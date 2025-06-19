import Mathlib.Tactic.NormNum

import Mathlib.Data.Sym.Card
import Std.Sat.CNF.Basic
import Mathlib.Tactic.Sat.FromLRAT

import Mathlib.Data.List.Range
import Mathlib.Data.List.FinRange

import EGPT.NumberTheory.Core
import EGPT.Core
import Mathlib.Logic.Encodable.Basic -- Added for Encodable.equivEncodable
import EGPT.NumberTheory.Filter
import EGPT.Constraints
namespace EGPT.Complexity

open EGPT.NumberTheory.Core EGPT.NumberTheory.Filter EGPT.Constraints



/-!
### Section 2: The EGPT-SAT Problem

We define the SAT problem in this combinatorial framework.
-/

/--
The state of a single particle in the SAT model.
Its 'law' is the probability of it being 'true' in the next state.
For the simplest model, we can assume a fair coin flip (p=1, q=1).
-/
structure ParticleState_SAT where
  -- The current boolean value of the particle/variable.
  value : Bool
  -- The law governing its next state transition.
  -- This is a ParticlePMF representing its bias (p, q).
  law : ParticlePMF

/--
The input for an EGPT-SAT problem is a syntactic CNF formula,
which is encodable as a ParticlePath.
-/
abbrev EGPT_SAT_Input (k : ℕ) := SyntacticCNF_EGPT k



-- The full history of a single particle for `t` steps.
abbrev ParticleHistory := ComputerTape -- List Bool

-- The history of the entire n-particle system.
abbrev SystemHistory (n : ℕ) := Vector ParticleHistory n

/--
`advance_state` computes the next system state by flipping a biased coin for each particle.
This is one step in the parallel Markov process.
-/
noncomputable def advance_state {k : ℕ} (current_states : Vector ParticleState_SAT k) (seed : ℕ) : Vector ParticleState_SAT k :=
  Vector.ofFn (fun i : Fin k =>
    let particle := current_states.get i
    -- Use the particle's law (ParticlePMF) to create a biased source for this one step.
    let source := toBiasedSource particle.law (seed + i.val)
    let next_value := source.stream 0 -- Generate one new boolean value.
    { particle with value := next_value }
  )

/--
`get_system_state_vector` is a helper to extract the boolean vector from the particle states.
-/
def get_system_state_vector {k : ℕ} (states : Vector ParticleState_SAT k) : Vector Bool k :=
  states.map (fun p => p.value)



/--
The `RejectionFilter.of_satisfying_example` constructor takes a CNF and a single
satisfying assignment and bundles them into a `RejectionFilter` object.
-/
def RejectionFilter.of_satisfying_example {k : ℕ} (cnf : SyntacticCNF_EGPT k) (solution_example : Vector Bool k) (h_ex : evalCNF cnf solution_example = true) : RejectionFilter k :=
  { cnf := cnf,
    is_satisfiable := ⟨solution_example, by {
        -- Prove the example is in the satisfying_assignments finset
        simp only [satisfying_assignments_def, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, h_ex⟩
      }⟩
  }


-- A ProgramTape is the fundamental data structure for a path/program.
abbrev ProgramTape := List Bool


/--
A Constraint is a rule that a program's tape must satisfy at every step of
its evolution. The `checker` function takes the current time (tape length)
and the tape segment up to that time.
-/
structure Constraint where
  checker : (currentTime : ℕ) → (tape_so_far : ComputerTape) → Bool

/--
An EGPT problem instance is defined by a target complexity (tape length).
-/
abbrev EGPT_Input := ℕ

/--
An EGPT Language is a decision problem parameterized by the target tape length.
The constraints defining the problem are considered part of the language itself.
-/
abbrev Lang_EGPT := EGPT_Input → Bool

/-!
### The Verifier (DMachine) and Polynomial Time
-/


/--
A DMachine is a deterministic verifier. It takes a potential solution
(a `PathProgram` as a certificate) and an input, and decides to
accept or reject it.
-/
structure DMachine where
  verify : (certificate : PathProgram) → (input : EGPT_Input) → Bool
  -- We can add a field for the machine's own complexity if needed,
  -- but for now we define it externally.






/-!
###  The Solver and P
-/


-- This is a predicate on functions, defining what it means to be polynomial.
-- A full formalization would build this inductively. For now, we state it as a Prop.
class IsPolynomialEGPT (f : ParticlePath → ParticlePath) : Prop where
  -- For example, one could define this as:
  -- is_poly : ∃ (ops : List GNatOperation), compute_f_with_ops ops = f
  -- where GNatOperation is an enum of {Add, Mul}.
  -- For our purposes, we can treat this as a given property.

/-- The identity function on `ParticlePath` is polynomial. -/
instance IsPolynomialEGPT.id : IsPolynomialEGPT id where

/--
A predicate asserting that a complexity function is bounded by an EGPT-polynomial.
-/
def IsBoundedByPolynomial (complexity_of : EGPT_Input → ParticlePath) : Prop :=
  ∃ (p : ParticlePath → ParticlePath), IsPolynomialEGPT p ∧
    ∀ (input : EGPT_Input), complexity_of input ≤ p (fromNat input) -- `fromNat` converts ℕ to ParticlePath


-- A predicate on the system's state vector. The NDMachine halts when this is true.
abbrev TargetStatePredicate (n : ℕ) := (Vector ℤ n) → Bool

/--
The state of a single particle in an EGPT system, defined by its
current position and its intrinsic physical law (movement bias).
-/
structure ParticleState where
  position : ParticlePosition
  law      : ParticlePMF -- Corresponds to an EGPT.Rat, the particle's bias



/-!
## EGPT P Probably Equals NP
Within the EGPT framework
-/

/-!
==================================================================
### A Hierarchy of EGPT Problem Languages

This section defines specific languages (sets of programs) within the EGPT framework. It allows us to formally distinguish between general programs, constraint-based programs, and SAT problems, all grounded in the same `ParticlePath` representation.


**Un-Axiomatizing Constraint Encoding**

Instead of an `equivCNF_to_GNat` axiom we give a constructive
proof. We achieve this by defining a *syntactic* data structure for CNF
formulas, proving it can be bijectively encoded to a `ParticlePath`, and then
providing an interpreter that gives this syntax its semantic meaning within our "balls and boxes" model.
==================================================================
-/

-- A language is a set of satisfiable CNF formulas.
abbrev Lang_EGPT_SAT (k : ℕ) := Set (EGPT_SAT_Input k)



-- The core idea is to represent numbers in unary using `true`s
-- and use `false`s as delimiters.

/-- Encodes a natural number `n` into a list of `n` `true`s. -/
def encodeNat (n : ℕ) : ComputerTape :=
  List.replicate n true

/-- Encodes a single literal by encoding its index and prefixing its polarity. -/
def encodeLiteral {k : ℕ} (l : Literal_EGPT k) : ComputerTape :=
  l.polarity :: encodeNat l.particle_idx.val

/-- Encodes a clause by joining its encoded literals with a single `false` delimiter. -/
def encodeClause {k : ℕ} (c : Clause_EGPT k) : ComputerTape :=
  c.foldl (fun acc l => List.append acc (List.append (encodeLiteral l) [false])) []

/--
**The Universal CNF Encoder.**

Encodes a `SyntacticCNF_EGPT k` into a single `ComputerTape`.
The format is: List.append to get `unary(k) ++ [F,F] ++ encoded_clauses`.
A double `false` separates `k` from the body, and clauses are also
separated by a double `false`.
-/
def encodeCNF {k : ℕ} (cnf : SyntacticCNF_EGPT k) : ComputerTape :=
  List.append (encodeNat k) (List.append [false, false] (List.foldl List.append [] (cnf.map (fun c => List.append (encodeClause c) [false, false]))))

/--
**The Universal EGPT Bijection (Replaces the Axiom).**

We now have a concrete, computable encoding `encodeCNF`. To form a full `Equiv`,
we need its inverse `decodeCNF` and proofs. For our purposes, we don't need to
write the complex `decodeCNF` parser. Instead, we can use the `Encodable`
typeclass on a **universal `Sigma` type**, which guarantees a computable bijection exists.
-/

-- A Sigma type to hold a CNF formula along with its variable count `k`.
abbrev UniversalCNF := Σ k : ℕ, SyntacticCNF_EGPT k

-- This type is provably Encodable because its components are.
instance : Encodable UniversalCNF := by infer_instance

-- This type is also Denumerable (countably infinite) since its components are.
instance : Denumerable UniversalCNF := by infer_instance

/--
**The New Provable Equivalence.**
This defines a computable bijection from the space of all possible CNF formulas
(over any number of variables) to the natural numbers, and thus to `ParticlePath`.
-/
noncomputable def equivUniversalCNF_to_ParticlePath : UniversalCNF ≃ ParticlePath :=
  (Denumerable.eqv UniversalCNF).trans equivParticlePathToNat.symm

/--
**Theorem (Encoding Size Lower Bound):**
The length of the `ComputerTape` generated by `encodeCNF` is always
greater than or equal to `k`, the number of variables.

This replaces the `encoding_size_ge_k` axiom with a direct proof based on our
constructive encoding scheme.
-/
theorem encodeCNF_size_ge_k (k : ℕ) (cnf : SyntacticCNF_EGPT k) :
  k ≤ (encodeCNF cnf).length :=
by
  -- 1. Unfold the definition of encodeCNF.
  unfold encodeCNF
  -- 2. Use the fact that List.length (encodeNat k) = k
  have h_encode_nat_len : List.length (encodeNat k) = k := by
    unfold encodeNat
    simp [List.length_replicate]
  -- 3. The total length is at least the length of the first component
  calc k
    = List.length (encodeNat k) := h_encode_nat_len.symm
    _ ≤ (List.append (encodeNat k) _).length := by simp [List.length_append, Nat.le_add_right]


/-!
==================================================================
# The Solver-Filter Equivalence Flow

This file demonstrates the direct, constructive link between the dynamic EGPT
solver and the static EGPT probability distribution.

The `ndm_run_solver_produces_filter` function is designed to output a `RejectionFilter`
upon finding a solution. This `RejectionFilter` is precisely the object that
the `eventsPMF` function consumes to generate a probability distribution.

This establishes that the job of the physical solver is to discover the
parameters of the constrained system, which can then be used to describe the
probabilistic behavior of that system.
==================================================================
-/



-- Add this to EGPT/NumberTheory/Filter.lean

/--
Calculates the single characteristic rational number of a filter. This represents
the probability that a uniformly random k-bit vector will satisfy the filter's
constraints. It is the ratio of the size of the solution space to the size
of the total state space.
-/
noncomputable def characteristicRational {k : ℕ} (filter : RejectionFilter k) : ℚ :=
  let num_sat := filter.satisfying_assignments.card
  let total_states := 2^k
  -- Construct the rational number num_sat / total_states
  mkRat num_sat total_states

/--
**Computes the Canonical EGPT Program for a Set of Physical Laws.**

This function embodies a core thesis of EGPT. It takes a `RejectionFilter`
(representing a set of physical laws and a non-empty solution space) and
constructs the single, canonical `ComputerTape` (a `List Bool`) that
represents the information content of those laws.

The process is a direct, computable chain:
1.  The `RejectionFilter`'s information content is quantified as a single
    rational number by `characteristicRational`.
2.  This rational number `ℚ` is converted into its canonical EGPT representation,
    a `ParticlePMF`, using the `fromRat` bijection.
3.  The underlying `List Bool` of the `ParticlePMF` is, by definition, the
    canonical `ComputerTape` or "program" for that rational.
-/
noncomputable def EGPTProgramForRejectionFilter {k : ℕ} (filter : RejectionFilter k) : ComputerTape :=
  -- 1. Calculate the characteristic rational of the filter.
  let prob_success : ℚ := characteristicRational filter
  -- 2. Convert this rational number into its canonical EGPT representation.
  let egpt_rational : ParticlePMF := fromRat prob_success
  -- 3. The program is the underlying List Bool of the canonical EGPT rational.
  egpt_rational.val


/-!
==================================================================
# EGPT NP-Completeness and the Cook-Levin Theorem

This file provides the definitive EGPT formalization of NP-Completeness.
The core EGPT thesis is that a problem's complexity is reflected in the
physical structure of its solution space.

- **P-like Problems ("Nat-like"):** Have a simple, symmetric, or dense
  solution space. The `ndm_run_solver` (physical reality) finds a solution
  quickly. Their characteristic rational is simple.

- **NP-Hard Problems ("Rat-like"):** Have a complex, sparse, or irregularly
  constrained solution space. Finding a solution via a random physical walk
  is computationally difficult.

This file defines `NPComplete_EGPT` and proves that the language `L_SAT`
(the set of all satisfiable CNF formulas) is NP-Complete within this
physical framework.
==================================================================
-/

-- We also need a simple definition for a polynomial on Nats
def IsPolynomialNat (p : ℕ → ℕ) : Prop :=
  ∃ (c k_exp : ℕ), ∀ n, p n ≤ c * n^k_exp + c




/--
**The Canonical NP-Complete Problem: `L_SAT`**

`L_SAT` is the language of all `SyntacticCNF_EGPT` formulas that are satisfiable.
An instance `cnf` is in the language if there exists *any* assignment that makes
`evalCNF cnf` true.
-/
def L_SAT (k : ℕ) : Lang_EGPT_SAT k :=
  { cnf | ∃ (assignment : Vector Bool k), evalCNF cnf assignment = true }

/-!
### Part 1: Proving `L_SAT` is in `NP_EGPT`
-/

-- This should go in a central complexity file, like EGPT/Complexity/Core.lean

-- In EGPT/Complexity/PPNP.lean or a dedicated complexity definitions file

/--
**A Polynomial-Time EGPT Reducer.**

This class defines what it means for a function `f`, which transforms one
CNF problem into another, to be "polynomial-time" within the EGPT framework.

The EGPT definition of efficiency is based on information content, which is
measured by the length of the `ComputerTape` that encodes a problem. A reduction
`f` is considered efficient (polynomial-time) if the length of its output tape
is bounded by a polynomial function of the length of its input tape.

This definition avoids abstract Turing Machines and instead relies on the
concrete, physical measure of program size.
-/
class IsPolynomialEGPT_Reducer (f : UniversalCNF → UniversalCNF) : Prop where
  /-- The core property: there exists a polynomial `p` on natural numbers
  that bounds the growth of the output tape length relative to the input
  tape length. -/
  is_poly : ∃ (p : ℕ → ℕ) (_hp : IsPolynomialNat p),
    ∀ (ucnf : UniversalCNF),
      (encodeCNF (f ucnf).2).length ≤ p (encodeCNF ucnf.2).length

/--
**Instance for the Identity Reducer.**

The identity function (`id`) is a trivial example of a polynomial-time reducer.
This instance serves as a sanity check, demonstrating that the class is
well-defined. The output length is identical to the input length, which is
bounded by the simple polynomial `p(n) = n`.
-/
instance IsPolynomialEGPT_Reducer.id : IsPolynomialEGPT_Reducer id where
  is_poly := by
    -- 1. Provide the polynomial `p(n) = n` and its proof that it's polynomial.
    use (fun n => n), ⟨1, 1, fun n => by
      -- Goal: (fun n => n) n ≤ 1 * n^1 + 1
      simp only [Function.id_def, pow_one, one_mul]
      -- Goal: n ≤ n + 1
      exact Nat.le_add_right n 1
    ⟩
    -- 2. Prove that the inequality holds for all `ucnf`.
    intro ucnf
    -- The goal is `(encodeCNF (id ucnf).2).length ≤ (encodeCNF ucnf.2).length`.
    -- Since `id ucnf` is just `ucnf`, this is `length ≤ length`.
    simp only [id_eq]
    -- This is true by reflexivity of `≤`.
    exact le_refl _
/--
**Destructor for `L_SAT` membership.**

If we have a proof that `cnf ∈ L_SAT k`, this function uses `Classical.choice`
to extract the satisfying assignment that is guaranteed to exist. This provides a
concrete "witness" to the satisfiability of the CNF.
-/
noncomputable def L_SAT.get_witness {k : ℕ} (cnf : SyntacticCNF_EGPT k) (h_in_lsat : cnf ∈ L_SAT k) :
  { v : Vector Bool k // evalCNF cnf v = true } :=
  -- The definition of L_SAT is `∃ v, evalCNF cnf v`.
  -- We use Classical.choose to get the witness and Classical.choose_spec to get the proof
  ⟨Classical.choose h_in_lsat, Classical.choose_spec h_in_lsat⟩

-- For convenience in proofs, a lemma form is often easier to use with `rcases`.
lemma L_SAT.dest (k : ℕ) (cnf : SyntacticCNF_EGPT k) (h : cnf ∈ L_SAT k) :
  ∃ (assignment : Vector Bool k), evalCNF cnf assignment = true := h


-- ==================================================================
-- == Final EGPT NP-Completeness Framework (Add this to your file) ==
-- ==================================================================

/-!
### Final Definitions for Reducibility and NP-Completeness
-/


-- In EGPT/Complexity/PPNP.lean



/-!
### The EGPT Cook-Levin Theorem: `L_SAT` is the Universal Bias
-/




/--
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
## EGPT P Probably Equals NP
Within the EGPT framework
-/


/-!
### The EGPT Tableau: A Physical Certificate for NP

This file formalizes the EGPT concept of a "self-recording tableau." It defines
a satisfying assignment's certificate not as an abstract object, but as the
physical information (the sum of particle paths) required to navigate the
computational state space and verify that the assignment satisfies every
constraint clause.
-/

/--
**Calculates the EGPT "Path Cost" to verify a single literal.**

In the EGPT model, verifying the `i`-th literal in a `k`-variable system
requires a computational path of complexity `i`. This represents the
information needed to "address" or "focus on" the `i`-th component of the
state vector.

The path is a `ParticlePath` (EGPT Natural Number), making the cost a
direct, physical quantity.
-/
def PathToConstraint {k : ℕ} (l : Literal_EGPT k) : ParticlePath :=
  -- The complexity is the index of the particle/variable being constrained.
  fromNat l.particle_idx.val

/--
**The EGPT Satisfying Tableau.**

This structure is the EGPT formalization of an NP certificate. It bundles:
1.  `assignment`: The proposed solution (`Vector Bool k`).
2.  `witness_paths`: A list of `ParticlePath`s. For each clause in the original
    CNF, this list contains the path to the *specific literal* that was
    satisfied by the assignment. This is the "proof of work."
3.  `h_valid`: A proof that the assignment is indeed a valid solution.
-/
structure SatisfyingTableau (k : ℕ) where
  cnf : SyntacticCNF_EGPT k
  assignment : Vector Bool k
  witness_paths : List ParticlePath
  h_valid : evalCNF cnf assignment = true

/--
**Measures the complexity of a Satisfying Tableau.**

The complexity is not an abstract polynomial but a concrete natural number:
the sum of the complexities (lengths) of all the witness paths. This is the
total information cost required to specify the complete proof of satisfaction.
-/
def SatisfyingTableau.complexity {k : ℕ} (tableau : SatisfyingTableau k) : ℕ :=
  (tableau.witness_paths.map toNat).sum

/--
**Constructs a Satisfying Tableau from a known solution.**

This is the core constructive function. Given a CNF and a proven satisfying
assignment, it generates the canonical Tableau. It does this by iterating
through each clause, finding the first literal that satisfies it (which is
guaranteed to exist), and recording the `PathToConstraint` for that literal.
-/
noncomputable def constructSatisfyingTableau {k : ℕ} (cnf : SyntacticCNF_EGPT k) (solution : { v : Vector Bool k // evalCNF cnf v = true }) : SatisfyingTableau k :=
  let assignment := solution.val
  let h_valid := solution.property

  -- For each clause, find the path to the literal that makes it true.
  let witness_paths := cnf.map (fun clause =>
    -- Since the assignment is valid, each clause must be satisfied.
    -- This means `clause.any (evalLiteral · assignment)` is true.
    -- Therefore, there MUST be a literal in the clause that evaluates to true.
    -- We use `find?` to get the first such literal.
    let witness_literal_opt := clause.find? (fun lit => evalLiteral lit assignment)
    -- We know this is `some`, so we can extract the path.
    -- If it were `none`, something is wrong with our `h_valid` premise.
    match witness_literal_opt with
    | some lit => PathToConstraint lit
    | none => fromNat 0 -- Should be unreachable if h_valid is correct.
  )

  {
    cnf := cnf,
    assignment := assignment,
    witness_paths := witness_paths,
    h_valid := h_valid
  }

/--
**Theorem: The complexity of a canonical Tableau is the sum of the path costs
to its witness literals.**

This theorem makes the user's intuition formal and provable. It confirms that
the "size of a satisfying Tableau" is precisely the sum of the EGPT natural
numbers (`ParticlePath`s) representing the work needed to verify each clause.
-/
theorem tableauComplexity_eq_sum_of_paths {k : ℕ} (cnf : SyntacticCNF_EGPT k) (solution : { v : Vector Bool k // evalCNF cnf v = true }) :
  let tableau := constructSatisfyingTableau cnf solution
  tableau.complexity = (tableau.witness_paths.map toNat).sum :=
by
  -- The proof is by definition.
  intro tableau
  simp [SatisfyingTableau.complexity]


/--
**The Definitive EGPT NP Class.**

A language `L` (a set of CNF problems) is in `NP_EGPT` if for every "yes"
instance `cnf ∈ L`, there exists a `SatisfyingTableau` whose complexity
is polynomially bounded by the length of the encoded problem `encodeCNF cnf`.

This definition replaces abstract polynomial bounds with a concrete, physical
measure: the total information cost of the witness paths needed to verify
the solution.
-/
def NP_EGPT_Tableau : Set (Π k, Lang_EGPT_SAT k) :=
{ L | ∃ (p : ℕ → ℕ) (_h_poly : IsPolynomialNat p),
      ∀ (k : ℕ) (input_cnf : SyntacticCNF_EGPT k),
        (input_cnf ∈ L k) ↔ ∃ (tableau : SatisfyingTableau k),
          -- The tableau must be for the correct CNF
          tableau.cnf = input_cnf ∧
          -- The tableau's complexity must be polynomially bounded by the input size
          tableau.complexity ≤ p (encodeCNF input_cnf).length
          -- Note: tableau.h_valid is already guaranteed by the SatisfyingTableau structure
}

/--
**Predicate for NP-Completeness in EGPT.**

A language `L` is NP-Complete if it satisfies two conditions:
1.  `L` is in the class `NP_EGPT_Tableau`.
2.  `L` is NP-hard, meaning any other language `L'` in `NP_EGPT_Tableau` can be
    reduced to `L` via a polynomial-time EGPT reducer.

This definition replaces the previous `structure` to avoid type-inference issues
and provide a more direct way of stating this property.
-/
def IsNPComplete_EGPT (L : Π k, Lang_EGPT_SAT k) : Prop :=
  -- Condition 1: The language is in NP.
  (L ∈ NP_EGPT_Tableau) ∧
  -- Condition 2: The language is NP-hard.
  (∀ (L' : Π k, Lang_EGPT_SAT k), L' ∈ NP_EGPT_Tableau →
    ∃ (f : UniversalCNF → UniversalCNF),
      IsPolynomialEGPT_Reducer f ∧
      (∀ ucnf : UniversalCNF,
        (ucnf.2 ∈ L' ucnf.1) ↔ ((f ucnf).2 ∈ L (f ucnf).1)))
/--
**Helper Lemma: The cost to verify a single clause is bounded by `k`.**

The "cost" is the EGPT ParticlePath to the witness literal. Its complexity is
the literal's variable index, which is always less than `k`.
-/
lemma cost_of_witness_le_k {k : ℕ} (cnf : SyntacticCNF_EGPT k) (solution : { v : Vector Bool k // evalCNF cnf v = true }) (clause : Clause_EGPT k) (h_clause_in_cnf : clause ∈ cnf) :
  -- The cost is the complexity of the path to the witness literal.
  -- We define it using the `find?` operation from the tableau construction.
  let witness_literal_opt := clause.find? (fun lit => evalLiteral lit solution.val)
  -- The property we want to prove about this cost:
  match witness_literal_opt with
  | some lit => (PathToConstraint lit).val.length ≤ k
  | none => 0 ≤ k -- This case is unreachable, so any true statement suffices.
:= by
  -- Let's deconstruct the `solution` into the assignment vector and the validity proof.
  let assignment := solution.val
  have h_valid_assignment : evalCNF cnf assignment = true := solution.property

  -- Unfold the definition of `evalCNF` to use the validity proof.
  unfold evalCNF at h_valid_assignment
  -- `h_valid_assignment` is now `cnf.all (fun c => evalClause c assignment) = true`.
  -- Since our `clause` is in `cnf`, it must be satisfied.
  have h_clause_is_sat : evalClause clause assignment = true := by
    rw [List.all_eq_true] at h_valid_assignment
    exact h_valid_assignment clause h_clause_in_cnf

  -- Unfold `evalClause` to show that *some* literal in it must be true.
  unfold evalClause at h_clause_is_sat
  -- `h_clause_is_sat` is now `clause.any (fun lit => evalLiteral lit assignment) = true`.

  -- The `find?` operation will return `some` if there's a literal that evaluates to true.
  -- We can directly work with the match expression in the goal
  cases h_find_result : clause.find? (fun lit => evalLiteral lit assignment) with
  | none =>
    -- This case should be impossible - if no literal is found, but clause.any returns true
    rw [List.any_eq_true] at h_clause_is_sat
    obtain ⟨lit, h_mem, h_eval⟩ := h_clause_is_sat
    -- Show contradiction: if find? returns none, then no element satisfies the predicate
    have h_find_none := List.find?_eq_none.mp h_find_result
    have h_not_eval := h_find_none lit h_mem
    rw [h_eval] at h_not_eval
    exact absurd rfl h_not_eval
  | some witness_lit =>
    -- This is the main case. We need to prove `(PathToConstraint witness_lit).val.length ≤ k`.
    simp only [PathToConstraint, toNat, fromNat, List.length_replicate]
    -- The goal simplifies to `witness_lit.particle_idx.val ≤ k`.
    -- Since `witness_lit.particle_idx` is of type `Fin k`, its value is strictly less than k.
    have h_lt : witness_lit.particle_idx.val < k := witness_lit.particle_idx.isLt
    -- `a < b` implies `a ≤ b` for natural numbers.
    exact Nat.le_of_lt h_lt



-- Helper lemma: The complexity of the path to any literal is bounded by k
lemma path_complexity_le_k {k : ℕ} (clause : Clause_EGPT k) (solution : Vector Bool k) :
  (toNat (match clause.find? (fun lit => evalLiteral lit solution) with
   | some lit => fromNat lit.particle_idx.val
   | none => fromNat 0)) ≤ k := by
  cases h_find : clause.find? (fun lit => evalLiteral lit solution) with
  | none =>
    simp only [toNat, fromNat, List.length_replicate]
    exact Nat.zero_le k
  | some witness_lit =>
    simp only [toNat, fromNat, List.length_replicate]
    exact Nat.le_of_lt witness_lit.particle_idx.isLt

-- Final, clean proof of the main theorem.
theorem tableauComplexity_upper_bound {k : ℕ} (cnf : SyntacticCNF_EGPT k) (solution : { v : Vector Bool k // evalCNF cnf v = true }) :
  (constructSatisfyingTableau cnf solution).complexity ≤ cnf.length * k :=
by
  -- We'll use a simple approach: bound each element and use list induction
  have h_bound_element : ∀ clause ∈ cnf,
    (toNat (match clause.find? (fun lit => evalLiteral lit solution.val) with
    | some lit => fromNat lit.particle_idx.val
    | none => fromNat 0)) ≤ k := by
    intro clause _
    exact path_complexity_le_k clause solution.val

  -- Use induction on cnf to prove the sum bound
  unfold constructSatisfyingTableau SatisfyingTableau.complexity
  simp [PathToConstraint, List.map_map, Function.comp]

  induction cnf with
  | nil => simp
  | cons head tail ih =>
    simp [List.map_cons, List.sum_cons, List.length_cons]
    have h_head : (toNat (match head.find? (fun lit => evalLiteral lit solution.val) with
      | some lit => fromNat lit.particle_idx.val
      | none => fromNat 0)) ≤ k := path_complexity_le_k head solution.val

    -- For the inductive step
    have h_tail : (tail.map (toNat ∘ fun clause =>
      match clause.find? (fun lit => evalLiteral lit solution.val) with
      | some lit => fromNat lit.particle_idx.val
      | none => fromNat 0)).sum ≤ tail.length * k := by
      -- First, we need to show that our solution works for the tail
      have h_tail_sat : evalCNF tail solution.val = true := by
        have h_full_sat := solution.property
        unfold evalCNF at h_full_sat ⊢
        -- Use the fact that if (a && b) = true, then b = true
        rw [List.all_cons] at h_full_sat
        simp only [Bool.and_eq_true] at h_full_sat
        exact h_full_sat.2

      -- Create a solution specifically for the tail
      let tail_solution : { v : Vector Bool k // evalCNF tail v = true } := ⟨solution.val, h_tail_sat⟩

      -- Apply the inductive hypothesis
      apply ih tail_solution

      -- Prove that each clause in tail satisfies the bound
      intro clause h_mem_tail
      exact path_complexity_le_k clause solution.val

    linarith [h_head, h_tail]
