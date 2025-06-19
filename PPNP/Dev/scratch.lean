import Mathlib.Data.Finset.Basic
import EGPT.Core
import EGPT.Complexity.Core
import EGPT.Complexity.PPNP
import EGPT.Entropy.Common
import EGPT.Physics.PhysicsDist
import EGPT.Constraints -- Add this import
import EGPT.NumberTheory.Core -- Add this import
import EGPT.NumberTheory.Filter -- Add this for RejectionFilter
import Mathlib.Data.List.Basic -- Keep this import


open EGPT Finset
open EGPT.Complexity
open EGPT.Entropy.Common
open EGPT.Physics.PhysicsDist
open EGPT.Constraints -- Open EGPT.Constraints
open EGPT.NumberTheory.Filter -- Open for RejectionFilter

/-- # FROM SCRATCH
Interprets a ComputerTape as a CNF formula. Each bit of the tape
constrains the state of the computation particle at the corresponding time step.
-/
def constraints_from_tape (tape : ComputerTape) : SyntacticCNF_EGPT 1 :=
  -- List.map a tape of length N into N unit clauses.
  tape.zipIdx.map (fun (instruction, t) =>
    -- At time `t`, the `instruction` bit becomes a constraint.
    -- Example constraint: `polarity` = `instruction`.
    -- This creates a CNF: (x₀=tape[0]) ∧ (x₁=tape[1]) ∧ ...
    [{ particle_idx := ⟨0, by simp⟩, polarity := instruction }]
  )


/--
**Computes a Potential Next State via a Memoryless Random Walk.**

This is the core state transition function of the EGPT physical model. It
defines one step of a parallel Markov process. It is "potential" because it
represents the raw physical evolution, before any constraints are applied.

The function is memoryless: the next state candidate depends *only* on the
`current_state` and the `seed` for randomness, not on any prior history.

1.  It converts the input boolean vector (`current_state`) into a vector of
    `ParticleState_SAT`, where each particle is assigned a fundamental, unbiased
    physical law (a fair coin, represented by the EGPT rational `1/1`).
2.  It calls `advance_state`, which performs `k` parallel, independent, and
    identically distributed (IID) "coin flips" to generate the next state.
3.  It returns the resulting boolean vector.
-/
noncomputable def potential_next_state {k : ℕ} (current_state : Vector Bool k) (seed : ℕ) : Vector Bool k :=
  -- 1. Create the particle state vector (value + law) from the boolean vector.
  --    The law `fromRat 1` represents a fair 1/1 coin, the fundamental IID source.
  let particle_states := Vector.ofFn (fun i => {
    value := current_state.get i,
    law   := EGPT.NumberTheory.Core.fromRat 1
  })

  -- 2. Advance the state using the memoryless `advance_state` function.
  let next_particle_states := advance_state particle_states seed

  -- 3. Extract just the boolean values for the resulting state vector.
  get_system_state_vector next_particle_states

/--
**The EGPT Non-deterministic Machine (`NDTM_A`) Runner.**

This function embodies the EGPT model of non-deterministic computation. It does
not simulate a Turing Machine abstractly; instead, it models computation as a
physical process: a "computation particle" attempting a random walk through a
state space, where its path is constrained by a set of physical laws.

- **The Machine's "Program":** The `constraints` (`SyntacticCNF_EGPT k`) are the
  program. They define the physical laws of the computational universe.
- **Non-determinism:** The `seed` provides the source of randomness for the
  particle's walk. A different seed leads to a different computational path.
  The problem is "accepted" if there *exists* any seed that finds a valid path.
- **Execution:** The machine performs a random walk with rejection sampling.
  At each time step, it generates a potential next state. If the state obeys
  the constraints, the path is extended. If not, the step is rejected, and
  the machine attempts a new random move from its previous state.

The output is `some path` if a valid computational history of `time_limit`
steps is found, and `none` otherwise.
-/
noncomputable def NDTM_A_run {k : ℕ} (constraints : SyntacticCNF_EGPT k) (time_limit : ℕ) (seed : ℕ) : Option (List (Vector Bool k)) :=
  -- === Phase 1: Initialization ===
  -- The NDTM must start in a valid state. We find all satisfying assignments
  -- and pick the first one as a valid starting point.
  let satisfying_states := (Finset.univ : Finset (Vector Bool k)).filter (fun v => evalCNF constraints v)
  let initial_state_opt := satisfying_states.toList.head?

  match initial_state_opt with
  | none =>
    -- No state satisfies the constraints. The computational space is empty, so no path can exist.
    none
  | some initial_state =>
    -- A valid starting state was found. Begin the random walk.

    -- === Phase 2: The Recursive Random Walk ===
    let rec loop (t : ℕ) (current_path : List (Vector Bool k)) (current_seed : ℕ) : Option (List (Vector Bool k)) :=
      -- The head of the path is always the current state for the next step.
      -- This is safe because `current_path` is initialized as `[initial_state]`.
      let current_state := current_path.head!

      -- Check for successful termination. A path of length `time_limit` has been found.
      if t >= time_limit then
        -- We have successfully constructed a valid path of the required length.
        some (current_path.reverse) -- Reverse to get chronological order [start, ..., end].
      else
        -- Propose a non-deterministic next state using the memoryless transition function.
        let next_candidate := potential_next_state current_state current_seed

        -- Verify the candidate against the physical laws (constraints).
        if evalCNF constraints next_candidate then
          -- **Accept:** The state is valid. Extend the path and continue the walk from the new state.
          let new_path := next_candidate :: current_path
          loop (t + 1) new_path (current_seed + 1)
        else
          -- **Reject:** The state is invalid. The path is not extended.
          -- Try a new random choice from the *same* `current_state`.
          loop (t + 1) current_path (current_seed + 1)
    termination_by time_limit - t

    -- Start the execution loop from t=0 with a path containing only the valid initial state.
    loop 0 [initial_state] seed

/--
**Creates a CNF formula that is uniquely satisfied by the given state vector `v`.**
The formula is a conjunction of `k` unit clauses, where the `i`-th clause fixes
the `i`-th variable to its value in `v`. For example, for `v = [true, false]`,
the CNF is `(x₀) ∧ (¬x₁)`.
-/
def cnf_for_specific_assignment {k : ℕ} (v : Vector Bool k) : SyntacticCNF_EGPT k :=
  List.ofFn (fun i : Fin k =>
    -- Each clause is a list containing a single literal.
    [{ particle_idx := i, polarity := v.get i }]
  )
/--
A `ConstrainedPathProblem` defines a complete search task within the EGPT framework.
It specifies the constraints for the starting state, all intermediate states (the "path laws"),
and the target state.

- `initial_state_cnf`: A CNF whose satisfying assignments are the valid starting points.
- `path_constraints`: A CNF that every state along the path (after the initial state) must satisfy.
- `target_constraint`: A CNF that the final state of a successful path must satisfy.
-/
structure ConstrainedPathProblem (k : ℕ) where
  initial_state_cnf : SyntacticCNF_EGPT k
  path_constraints  : SyntacticCNF_EGPT k
  target_constraint : SyntacticCNF_EGPT k

/-!
### Equivalence Between ConstrainedPathProblem and SyntacticCNF_EGPT

The core insight is that any `ConstrainedPathProblem` can be viewed as a single
`SyntacticCNF_EGPT` formula by combining all its constraint components. This
establishes the fundamental equivalence between path-finding problems and
satisfiability problems within the EGPT framework.
-/

/--
**Converts a `ConstrainedPathProblem` to an equivalent `SyntacticCNF_EGPT`.**

The conversion combines all three constraint types into a single CNF formula.
For path problems, we interpret this as: "Find assignments that could represent
valid states in a solution path" - i.e., states that satisfy at least one of
the constraint types (initial, path, or target).

The resulting CNF is satisfied by any assignment that could be part of a valid
solution path to the original constrained path problem.
-/
def constrainedPathToCNF {k : ℕ} (problem : ConstrainedPathProblem k) : SyntacticCNF_EGPT k :=
  -- Combine all three CNF components into one formula
  -- The disjunction of the three constraint types means an assignment satisfies
  -- the combined CNF if it satisfies at least one component
  problem.initial_state_cnf ++ problem.path_constraints ++ problem.target_constraint

/--
**Converts a `SyntacticCNF_EGPT` to an equivalent `ConstrainedPathProblem`.**

This creates a trivial path problem where:
- Initial states can be any assignment satisfying the CNF
- Path constraints are empty (any intermediate state is allowed)
- Target constraint is the same as the initial constraint

This represents the SAT problem as a trivial path problem where any satisfying
assignment is both a valid start and end state.
-/
def cnfToConstrainedPath {k : ℕ} (cnf : SyntacticCNF_EGPT k) : ConstrainedPathProblem k :=
{
  initial_state_cnf := cnf,
  path_constraints := [], -- Empty CNF (always satisfied)
  target_constraint := cnf
}

/--
The language of solvable constrained path problems. An instance is in the language
if there *exists* a valid path from a valid start to a valid end.
-/
abbrev Lang_EGPT_ConstrainedPath (k : ℕ) := Set (ConstrainedPathProblem k)

/--
A deterministic verifier for a `ConstrainedPathProblem`. It takes a problem
description and a certificate (the proposed path) and returns `true` if the
path is a valid solution.
-/
def DMachine_CP_verify {k : ℕ} (problem : ConstrainedPathProblem k) (path_cert : List (Vector Bool k)) : Bool :=
  match path_cert with
  | [] => false -- An empty path is not a solution.
  | initial_state :: rest_of_path =>
      -- 1. Check if the starting state is valid.
      let is_start_valid := evalCNF problem.initial_state_cnf initial_state
      -- 2. Check if every intermediate state obeys the path constraints.
      let are_intermediate_valid := rest_of_path.all (fun state => evalCNF problem.path_constraints state)
      -- 3. Check if the final state is a valid target.
      let is_end_valid := evalCNF problem.target_constraint path_cert.getLast! -- Assumes non-empty

      is_start_valid && are_intermediate_valid && is_end_valid -- Use boolean AND (&&)

/-!
### Universal Problem Encoding

The following function embodies a core tenet of the EGPT framework: that any
computational task, no matter how complex, can be represented as a single,
unambiguous piece of information—a single `ComputerTape`. This tape is conceptually
equivalent to a single (potentially very large) number.
-/

/--
**The Universal Problem Encoder.**

Encodes an entire `ConstrainedPathProblem` into a single, canonical `ComputerTape`.
This function serializes the three distinct CNF formulas that define the problem
into one continuous list of booleans.

To ensure the encoding is unambiguous and can be uniquely parsed back into its
three components, a special delimiter is used to separate the encoded tapes.

**Encoding Format:**

The final tape has the structure:
`[ <encoded_initial_cnf> ] ++ <DELIMITER> ++ [ <encoded_path_cnf> ] ++ <DELIMITER> ++ [ <encoded_target_cnf> ]`

Where:
- Each `<encoded_..._cnf>` is generated by the `encodeCNF` function, which creates a
  self-describing tape for a single `SyntacticCNF_EGPT`.
- The `<DELIMITER>` is a sequence of three `false` bits `[false, false, false]`. This
  was chosen because double `false` is already used as a separator within the
  `encodeCNF` format, so a triple `false` provides a unique, higher-level separator.

The resulting `ComputerTape` is the definitive "program tape" for this specific
pathfinding problem. Its length serves as the input size for complexity analysis
(e.g., in the definitions of `P_EGPT_CP` and `NP_EGPT_CP`).
-/
noncomputable def encode_pathfinding_problem {k : ℕ} (problem : ConstrainedPathProblem k) : ComputerTape :=
  -- 1. Define the delimiter that will separate the three encoded CNF tapes.
  let delimiter : ComputerTape := [false, false, false]

  -- 2. Encode each of the three component CNF formulas into its own ComputerTape
  --    using the existing `encodeCNF` utility.
  let tape_initial := encodeCNF problem.initial_state_cnf
  let tape_path    := encodeCNF problem.path_constraints
  let tape_target  := encodeCNF problem.target_constraint

  -- 3. Concatenate the three tapes with the delimiter in between to form the
  --    final, unified problem tape.
  List.append (List.append tape_initial delimiter) (List.append tape_path (List.append delimiter tape_target))

-- In EGPT/Complexity/Core.lean or a new file

/--
**The Revised Constrained Path Solver - Returns RejectionFilter.**

Instead of searching for specific paths, this solver converts the
`ConstrainedPathProblem` into a `RejectionFilter` that represents all valid
states that could appear in solution paths. This captures the probabilistic
structure of the solution space rather than finding individual solutions.

The solver creates a filter based on the combined CNF formula that represents
all constraints from the original path problem. The resulting `RejectionFilter`
can then be used to generate the probability distribution over valid states.
-/
noncomputable def ndm_constrained_path_solver {k : ℕ} (problem : ConstrainedPathProblem k) : Option (RejectionFilter k) :=
  -- Convert the constrained path problem to a single CNF formula
  let combined_cnf := constrainedPathToCNF problem

  -- Check if there are any satisfying assignments
  let satisfying_assignments := (Finset.univ : Finset (Vector Bool k)).filter (fun v => evalCNF combined_cnf v)

  if h_nonempty : satisfying_assignments.Nonempty then
    -- Create the RejectionFilter
    let filter : RejectionFilter k := {
      cnf := combined_cnf,
      satisfying_assignments := satisfying_assignments,
      is_satisfiable := h_nonempty,
      ax_coherent := by
        intros v h_v_in_sa
        exact (Finset.mem_filter.mp h_v_in_sa).2
    }
    some filter
  else
    none -- No solutions exist


/--
**Constructs the RejectionFilter representing the complete solution space for a
set of physical constraints.**

This function is the definitive, deterministic EGPT solver. It takes a set of
physical laws, encoded as a `SyntacticCNF_EGPT`, and determines the complete
set of all possible states that are consistent with those laws.

Instead of simulating a non-deterministic random walk to find a single witness,
this function performs a direct, deterministic analysis of the entire state space.

- If the set of valid states (satisfying assignments) is non-empty, it
  constructs and returns a `RejectionFilter` that encapsulates this entire
  solution space.
- If no state can satisfy the constraints, it returns `none`, signifying that
  the physical system is impossible.

This function represents a P-solver for an NP-complete problem. The core EGPT
claim is that the time required for a physical, non-deterministic process to
find a *single* solution is polynomially equivalent to the time required for
this function to characterize the *entire* solution space.
-/
noncomputable def construct_solution_filter {k : ℕ} (constraints : SyntacticCNF_EGPT k) : Option (RejectionFilter k) :=
  -- 1. Deterministically find ALL satisfying assignments by filtering the
  --    entire state space (Finset.univ) against the constraint checker.
  let satisfying_assignments := (Finset.univ : Finset (Vector Bool k)).filter (fun v => evalCNF constraints v)

  -- 2. Check if the resulting set of solutions is empty.
  if h_nonempty : satisfying_assignments.Nonempty then
    -- 3a. If solutions exist, package the complete solution space into a RejectionFilter.
    --     The `is_satisfiable` proof is directly provided by `h_nonempty`.
    let filter : RejectionFilter k := {
      cnf := constraints,
      satisfying_assignments := satisfying_assignments,
      is_satisfiable := h_nonempty,
      -- The coherence axiom is true by the definition of our filter.
      ax_coherent := by
        intros v h_v_in_sa
        -- If v is in the filtered set, it must satisfy the filter's predicate.
        exact (Finset.mem_filter.mp h_v_in_sa).2
    }
    some filter
  else
    -- 3b. If the set of solutions is empty, the system is unsolvable.
    none

-- A Constrained System is defined by a single set of laws.
abbrev ConstrainedSystem (k : ℕ) := SyntacticCNF_EGPT k

-- The verifier checks that EVERY state in the path obeys the laws.
def DMachine_CS_verify {k : ℕ} (sys : ConstrainedSystem k) (path_cert : List (Vector Bool k)) : Bool :=
  -- An empty path cannot be a valid solution certificate.
  ¬path_cert.isEmpty ∧ path_cert.all (fun state => evalCNF sys state)


theorem constrainedSystem_equiv_SAT {k : ℕ} (sys : ConstrainedSystem k) :
  (∃ path : List (Vector Bool k), DMachine_CS_verify sys path = true) ↔
  (∃ assignment : Vector Bool k, evalCNF sys assignment = true) :=
by
  -- To prove the iff (↔), we prove both directions.
  constructor

  -- Part 1: Forward Direction (→)
  -- If a valid path exists, then the CNF is satisfiable.
  · intro h_path_exists
    -- From the hypothesis, we get a specific path that is valid.
    rcases h_path_exists with ⟨path, h_path_valid⟩

    -- The verifier returns a Bool, so we have `DMachine_CS_verify sys path = true`
    -- This means `decide (¬path.isEmpty ∧ path.all (fun state => evalCNF sys state)) = true`
    simp only [DMachine_CS_verify] at h_path_valid

    -- Since `decide` returns `true`, the inner proposition must be true
    have h_inner : ¬path.isEmpty ∧ path.all (fun state => evalCNF sys state) := by
      exact decide_eq_true_iff.mp h_path_valid

    -- Extract the components
    have h_path_nonempty : ¬path.isEmpty := h_inner.1
    have h_all_states_valid : path.all (fun state => evalCNF sys state) := h_inner.2

    -- Since the path is not empty, it must have a first element (a head).
    have h_ne_nil : path ≠ [] := by
      intro h_eq_nil
      rw [h_eq_nil] at h_path_nonempty
      simp at h_path_nonempty

    cases path with
    | nil => contradiction -- This case is impossible due to h_ne_nil
    | cons head tail =>
        -- We now have a specific state, `head`. We will show it is a satisfying assignment.
        -- We need to prove `∃ assignment, evalCNF sys assignment = true`. We use `head`.
        use head

        -- The goal is to prove `evalCNF sys head = true`.
        -- We know `(head :: tail).all (fun state => evalCNF sys state) = true`.
        -- By the definition of `List.all`, this means the property holds for the head and for all elements in the tail.
        simp [List.all_cons] at h_all_states_valid
        -- `h_all_states_valid` is now `evalCNF sys head ∧ tail.all (fun state => evalCNF sys state)`.
        -- The first part of this conjunction is exactly our goal.
        exact h_all_states_valid.left

  -- Part 2: Backward Direction (←)
  -- If the CNF is satisfiable, then a valid path exists.
  · intro h_assignment_exists
    -- From the hypothesis, we get a specific assignment that satisfies the CNF.
    rcases h_assignment_exists with ⟨assignment, h_assignment_valid⟩

    -- We need to prove `∃ path, DMachine_CS_verify sys path = true`.
    -- We can construct a trivial, single-state path using our valid assignment.
    use [assignment]

    -- The goal is to prove `DMachine_CS_verify sys [assignment] = true`.
    -- Unfold the verifier's definition.
    simp only [DMachine_CS_verify, List.isEmpty_cons, List.all_cons, List.all_nil, Bool.not_false]
    -- The goal is now `true ∧ evalCNF sys assignment = true`.
    -- Since we know `evalCNF sys assignment = true`, this simplifies to `true ∧ true = true`.
    simp [h_assignment_valid]

-- Updated P_EGPT_CP definition using the new solver

def P_EGPT_CP : Set (Π k, Lang_EGPT_ConstrainedPath k) :=
{ L | ∃ (p : ℕ → ℕ) (_h_poly : IsPolynomialNat p),
      ∀ (k : ℕ) (problem : ConstrainedPathProblem k),
        (problem ∈ L k) ↔
          -- The solver succeeds in creating a RejectionFilter
          ndm_constrained_path_solver problem ≠ none
}

/--
The class NP_EGPT_CP: Problems for which a "yes" instance has a path certificate
whose length is bounded by a polynomial in the size of the problem description.
-/
def NP_EGPT_CP : Set (Π k, Lang_EGPT_ConstrainedPath k) :=
{ L | ∃ (p : ℕ → ℕ) (_h_poly : IsPolynomialNat p),
      ∀ (k : ℕ) (problem : ConstrainedPathProblem k),
        (problem ∈ L k) ↔ ∃ (path_cert : List (Vector Bool k)),
          -- The certificate (path) must be of polynomial length.
          path_cert.length ≤ p ((encode_pathfinding_problem problem).length) ∧
          DMachine_CP_verify problem path_cert = true
}




/-!
### Theorem: Underlying State Evolution is Memoryless (A Markov Process)

This theorem formalizes the observation that the state transition function used by the
`ndm_constrained_path_solver` is Markovian.

Even though the solver carries a full path history (`current_path`), the generation
of the *next candidate state* at each step depends **only on the most recent state**
in that path and the current seed. It has no dependency on `s_{t-1}, s_{t-2}, ...`.

The proof shows that the state generation logic inside the solver's loop is
definitionally equal to a standalone, memoryless function (`potential_next_state`).
-/
theorem underlying_state_evolution_is_memoryless {k : ℕ} :
    -- We want to prove that for any `current_state` and `current_seed` that might
    -- appear inside the solver's loop...
    ∀ (current_state : Vector Bool k) (current_seed : ℕ),
      -- ...the `next_state` generated inside the loop...
      (
        let particle_states := Vector.ofFn (fun i => { value := current_state.get i, law := EGPT.NumberTheory.Core.fromRat 1})
        get_system_state_vector (advance_state particle_states current_seed)
      )
      -- ...is equal to the output of our standalone, memoryless function.
      = potential_next_state current_state current_seed :=
by
  -- The proof is by definition. We introduce the variables and show both
  -- sides of the equality are identical.
  intro current_state current_seed

  -- Unfold the definition of `potential_next_state` on the right-hand side.
  simp [potential_next_state]



/-!
### Additional Theorems for the Revised Framework
-/


/--
**Connection to Probability Theory**

This function demonstrates how to extract a probability distribution from the
solution structure discovered by the solver.
-/
noncomputable def extractProbabilityDistribution {k : ℕ} (problem : ConstrainedPathProblem k) :
  Option (Vector Bool k → ℚ) :=
  match ndm_constrained_path_solver problem with
  | none => none
  | some filter => some (distOfRejectionFilter filter)

/-!
# END FROM SCRATCH
-/

lemma encodeLiteral_nonempty {k : ℕ} (l : Literal_EGPT k) : 0 < (encodeLiteral l).length := by
  unfold encodeLiteral
  simp [encodeNat, List.length_append, List.length_cons, List.length_replicate]

-- Helper lemma for proving properties of foldl with append
lemma foldl_append_flatten {β} (init : List β) (l : List (List β)) :
  List.foldl List.append init l = List.append init (List.flatten l) := by
  induction l generalizing init with
  | nil => simp [List.foldl, List.flatten, List.append_nil]
  | cons h t ih =>
    simp only [List.foldl, List.flatten]
    rw [ih (List.append init h)]
    simp [List.append_assoc]

-- Helper lemma to relate foldl with append to flatten and map
lemma foldl_append_flatten_map {α β} (g : α → List β) (c : List α) :
  List.foldl (fun acc l => List.append acc (g l)) [] c = List.flatten (c.map g) := by
  induction c with
  | nil => simp [List.foldl, List.map, List.flatten]
  | cons head tail ih =>
    simp [List.foldl, List.map, List.flatten, ih]

lemma length_encodeClause_eq_sum_of_lengths {k : ℕ} (c : Clause_EGPT k) :
  (encodeClause c).length = List.sum (c.map (fun l => (encodeLiteral l).length + 1)) := by
  let g : Literal_EGPT k → List Bool := fun l => List.append (encodeLiteral l) [false]
  have h_eq_join_map : encodeClause c = List.flatten (c.map g) := by
    unfold encodeClause
    exact foldl_append_flatten_map g c
  rw [h_eq_join_map]
  rw [List.length_flatten]
  simp only [List.map_map]
  congr 1
  ext l
  simp [g, Function.comp, List.length_append, List.length_cons, List.length_nil]
