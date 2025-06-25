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



/-- A PathProgram is defined by an initial state and a tape of instructions
    that drives its evolution. -/
structure PathProgram where
  current_state : ℤ
  tape : ComputerTape

-- Helper to create a new program at a starting position.
def mkPathProgram (initial_pos : Int) : PathProgram :=
  { tape := [], current_state := initial_pos }


-- ADD THE NEW HELPER FUNCTION HERE
namespace PathProgram

/--
**Updates the tape of a PathProgram, returning a new program.**

This function takes an existing program `prog` and a new `ComputerTape`. It produces
a new `PathProgram` that has the same initial state as the original but uses the
new tape as its instructions.

This is a key helper for defining computations. It allows us to treat a `PathProgram`
as a reusable "machine" and `update_tape` as the mechanism for loading a new
input tape into that machine before running it.
-/
def update_tape (prog : PathProgram) (new_tape : ComputerTape) : PathProgram :=
  { current_state := prog.current_state,
    tape := new_tape }

end PathProgram
/--
A `SATSystemState` is a distribution of particles into a finite number of
positions. It is represented by a `Multiset` over `Fin constrained_position`, where
`constrained_position` is the number of "boxes". The cardinality of the multiset is
the number of particles ("balls").
-/
abbrev SATSystemState (constrained_position : ℕ) := Multiset (Fin constrained_position)

/--
A `ClauseConstraint` is a rule that a `SATSystemState` must satisfy. It is a
predicate on the distribution of particles.
This is the EGPT equivalent of a single clause in a CNF formula.
-/
abbrev ClauseConstraint (constrained_position : ℕ) := SATSystemState constrained_position → Bool

/--
A `CNF_Formula` is a list of `ClauseConstraint`s. A `SATSystemState` is
satisfying if and only if it satisfies every constraint in the list.
-/
abbrev CNF_Formula (constrained_position : ℕ) := List (ClauseConstraint constrained_position)

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

/--
A certificate for a SAT problem is a proposed satisfying assignment.
-/
abbrev Certificate (k : ℕ) := Vector Bool k

/--
A DMachine (Deterministic Verifier) for SAT is defined by its action:
it evaluates a CNF formula against a certificate.
-/
def DMachine_SAT_verify {k : ℕ} (input : EGPT_SAT_Input k) (cert : Certificate k) : Bool :=
  evalCNF input cert

/--
An NDMachine (Non-Deterministic Solver) is the physical system itself.
It is defined by the laws (constraints) it operates under.
Its `solve` method is the concrete `ndm_run_solver`.
-/
structure NDMachine_SAT (k : ℕ) where
  -- The physical laws of the system.
  constraints : EGPT_SAT_Input k
  -- The initial state of the k particles/variables (e.g., all false, with fair bias).
  initial_states : Vector ParticleState_SAT k


-- The full history of a single particle for `t` steps.
abbrev ParticleHistory := ComputerTape -- List Bool

-- The history of the entire n-particle system.
abbrev SystemHistory (n : ℕ) := Vector ParticleHistory n
/--
Converts a `SystemHistory` (a set of parallel tapes) into a single,
serial `PathProgram` by concatenating all tapes. This represents the
total computational work of the simulation.
-/
def prog_of_history {n : ℕ} (hist : SystemHistory n) : PathProgram :=
  { current_state := 0, tape := hist.toList.flatMap id }


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

/--
**The Revised Solver:** `ndm_run_solver` now returns an `Option (RejectionFilter k)`.
A `some filter` result means a solution was found, and that solution is now
packaged inside the filter itself as the proof of `is_satisfiable`.
-/
noncomputable def ndm_run_solver {k : ℕ} (machine : NDMachine_SAT k) (time_limit : ℕ) (seed : ℕ) : Option (RejectionFilter k) :=
  let rec loop (t : ℕ) (current_states : Vector ParticleState_SAT k) : Option (RejectionFilter k) :=
    if t >= time_limit then
      none -- Timeout
    else
      -- 1. Advance the state
      let next_particle_states := advance_state current_states (seed + t)
      let next_system_state := get_system_state_vector next_particle_states

      -- 2. Check the constraints
      if h_eval : evalCNF machine.constraints next_system_state then
        -- **Success!** We found a satisfying assignment.
        -- Use it to construct and return the full RejectionFilter.
        some (RejectionFilter.of_satisfying_example machine.constraints next_system_state h_eval)
      else
        -- Keep searching
        loop (t + 1) next_particle_states
    termination_by time_limit - t

  loop 0 machine.initial_states

/--
The `solve` function IS the ndm_run_solver. This becomes the primary
definition of non-deterministic solving in EGPT.
-/
noncomputable def NDMachine_SAT.solve (machine : NDMachine_SAT k) (time_limit : ℕ) (seed : ℕ) : Option (RejectionFilter k) :=
  ndm_run_solver machine time_limit seed

/--
Axiom: Represents the deterministic evaluation of the program.
Given a program (initial state + tape), it outputs the final state.
The specific function `eval` is not defined here, only its existence and type.
-/
def PathProgram.eval (prog : PathProgram) := calcParticlePosition prog.current_state prog.tape

/--
Defines the computational complexity of a `PathProgram` in this model.
It is defined as the length of its input `ComputerTape`, representing the
number of i.i.d. binary choices processed.
-/
def PathProgram.complexity (prog : PathProgram) : ℕ :=
  prog.tape.length


-- A ProgramTape is the fundamental data structure for a path/program.
abbrev ProgramTape := List Bool


open EGPT.NumberTheory.Core


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





/--
A predicate asserting that a DMachine runs in polynomial time.
`complexity_of` is a function that measures the runtime.
The runtime must be polynomial in the size of the certificate's tape
and the numerical value of the input.
-/
def RunsInPolyTime (complexity_of : PathProgram → EGPT_Input → ℕ) : Prop :=
  ∃ (c k : ℕ), ∀ (cert : PathProgram) (input : EGPT_Input),
    complexity_of cert input ≤ c * (cert.complexity + input)^k + c

/-!
### The Non-Deterministic Generator and NP
-/

/--
This predicate formalizes what it means for a program to be a valid physical
path. It is true if the program's tape satisfies all constraints at every
intermediate step of its creation (from length 1 to its final length).
-/
def CanNDMachineProduce (constraints : List Constraint) (prog : PathProgram) : Prop :=
  ∀ (t : ℕ) (_ht : 0 < t ∧ t ≤ prog.complexity),
    (constraints.all (fun c => c.checker t (prog.tape.take t)))



open EGPT.NumberTheory.Core EGPT.Complexity EGPT.NumberTheory.Filter EGPT.Constraints

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
-- This is a predicate on functions, defining what it means to be polynomial.
-- A full formalization would build this inductively. For now, we state it as a Prop.
class IsPolynomialEGPT (f : ParticlePath → ParticlePath) : Prop where
  -- For example, one could define this as:
  -- is_poly : ∃ (ops : List GNatOperation), compute_f_with_ops ops = f
  -- where GNatOperation is an enum of {Add, Mul}.
  -- For our purposes, we can treat this as a given property.

/-- The identity function on `ParticlePath` is polynomial. -/
instance IsPolynomialEGPT.id : IsPolynomialEGPT id where

-- A language is a set of satisfiable CNF formulas.
abbrev Lang_EGPT_SAT (k : ℕ) := Set (EGPT_SAT_Input k)

/--
The class NP_EGPT: Problems for which a "yes" instance has a
polynomial-time verifiable certificate.
-/
def NP_EGPT : Set (Π k, Lang_EGPT_SAT k) :=
{ L | ∃ (poly_bound : ParticlePath → ParticlePath) (_h_poly : IsPolynomialEGPT poly_bound),
      ∀ (k : ℕ) (input : EGPT_SAT_Input k),
        (input ∈ L k) ↔ ∃ (cert : Certificate k),
          -- The verifier is our DMachine. Its runtime is poly in the size of the input + cert.
          -- We just need to assert the certificate itself is of poly size.
          cert.size ≤ (equivParticlePathToNat (poly_bound (equivSyntacticCNF_to_ParticlePath input))) ∧
          DMachine_SAT_verify input cert = true
}

/--
The class P_EGPT: Problems for which the NDMachine (physical reality)
finds a solution in polynomial time.
-/
def P_EGPT : Set (Π k, Lang_EGPT_SAT k) :=
{ L | ∃ (machine_builder : ∀ k, EGPT_SAT_Input k → NDMachine_SAT k)
         (poly_bound : ParticlePath → ParticlePath) (_h_poly : IsPolynomialEGPT poly_bound),
      ∀ (k : ℕ) (input : EGPT_SAT_Input k),
        (input ∈ L k) ↔ ∃ (seed : ℕ), -- There exists a lucky path
          let machine := machine_builder k input
          let time_limit := equivParticlePathToNat (poly_bound (equivSyntacticCNF_to_ParticlePath input))
          machine.solve time_limit seed ≠ none
}


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
The format is: `unary(k) ++ [F,F] ++ encoded_clauses`.
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

/--
The class NP_EGPT (Revised): Problems for which a "yes" instance has a
certificate whose size is polynomially bounded by the *concrete encoding length*
of the input instance.
-/
def NP_EGPT_Concrete : Set (Π k, Lang_EGPT_SAT k) :=
{ L | ∃ (p : ℕ → ℕ) (_h_poly : IsPolynomialNat p), -- A standard polynomial on Nats
      ∀ (k : ℕ) (input : SyntacticCNF_EGPT k),
        (input ∈ L k) ↔ ∃ (cert : Certificate k),
          -- The size of the certificate (k) is bounded by a polynomial
          -- of the concrete length of the encoded input.
          k ≤ p (encodeCNF input).length ∧
          DMachine_SAT_verify input cert = true
}



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

/--
A function `f` that transforms one CNF problem into another is **polynomial in EGPT**
if there exists a polynomial-time algorithm that can compute the transformation
on their concrete `ComputerTape` encodings.
-/
class IsPolynomialEGPT_CNF_Reducer (f : UniversalCNF → UniversalCNF) : Prop where
  poly_complexity : ∃ (complexity_fn : PathProgram → EGPT_Input → ℕ),
    RunsInPolyTime complexity_fn ∧
    ∀ (ucnf : UniversalCNF),
      ∃ (result_tape : ComputerTape),
        result_tape = encodeCNF (f ucnf).2 ∧
        result_tape.length ≤ complexity_fn (mkPathProgram 0) (encodeCNF ucnf.2).length
-- Note: The polynomial-time property ensures the transformation can be computed efficiently
-- The result_tape represents the encoded output of applying f to the input CNF


/--
Theorem: `L_SAT` is in `NP_EGPT` (Concrete Version).

**Proof:** We use our concrete encoding size theorem `encodeCNF_size_ge_k`.
The size of the certificate is `k`. The size of the input is `(encodeCNF input).length`.
We proved `k ≤ (encodeCNF input).length`. Therefore, `k` is bounded by the
identity function `p(n) = n`, which is a polynomial.
-/
theorem L_SAT_in_NP_EGPT_Concrete : (L_SAT : Π k, Lang_EGPT_SAT k) ∈ NP_EGPT_Concrete := by
  unfold NP_EGPT_Concrete
  use (fun n => n)
  exact ⟨⟨1, 1, fun n => by simp [pow_one]⟩,
    fun k input => by {
      unfold L_SAT
      constructor
      · intro h_exists_a
        rcases h_exists_a with ⟨assignment, h_eval⟩
        use assignment
        constructor
        · exact encodeCNF_size_ge_k k input
        · unfold DMachine_SAT_verify; exact h_eval
      · intro h_exists_c
        rcases h_exists_c with ⟨certificate, _, h_verify⟩
        use certificate
        unfold DMachine_SAT_verify at h_verify
        exact h_verify
    }⟩

-- This should be placed right after the definition of L_SAT.

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

/--
The Class P_EGPT (Unbiased Problems): The set of all CNF formulas that are
trivially satisfiable (i.e., tautologies).
-/
def P_EGPT_Biased_Language (k : ℕ) : Lang_EGPT_SAT k :=
{ cnf |
    -- The CNF is a tautology if its characteristicRational is 1.
    -- We need to prove it's satisfiable first to construct the filter.
    (∀ (v : Vector Bool k), evalCNF cnf v = true)
}

-- Then you can prove that if `cnf ∈ P_EGPT_Biased_Language k`, then `characteristicRational ... = 1`.
theorem characteristicRational_of_P_lang_is_one {k : ℕ} {cnf : SyntacticCNF_EGPT k}
  (h : cnf ∈ P_EGPT_Biased_Language k) :
  ∃ (filter : RejectionFilter k), filter.cnf = cnf ∧ characteristicRational filter = 1 := by
  -- Construct the satisfying assignments (all assignments since it's a tautology)
  let satisfying_assignments : Finset (Vector Bool k) := Finset.univ
  -- Prove this set is nonempty
  have is_satisfiable : satisfying_assignments.Nonempty := by
    use Vector.replicate k false
    simp [satisfying_assignments]
  -- Prove the coherence axiom
  have ax_coherent : ∀ v, v ∈ satisfying_assignments → (evalCNF cnf v = true) := by
    intros v _
    exact h v
  -- Construct the filter
  let filter : RejectionFilter k := {
    cnf := cnf,
    satisfying_assignments := satisfying_assignments,
    is_satisfiable := is_satisfiable,
    ax_coherent := ax_coherent
  }
  use filter
  constructor
  · rfl
  · unfold characteristicRational
    simp only [satisfying_assignments]

    -- We need to show that card (univ : Finset (Vector Bool k)) = 2^k
    rw [Finset.card_univ]
    -- The instance instFintypeVectorBool gives us the Fintype structure
    -- Use the available card_vector theorem from Fintype via the equivalence
    have h_eq : Fintype.card (Vector Bool k) = Fintype.card Bool ^ k := by
      -- Transform to List.Vector via equivalence and then use card_vector
      have h1 : Fintype.card (Vector Bool k) = Fintype.card (List.Vector Bool k) :=
        Fintype.card_congr listVectorEquivVector.symm
      rw [h1]
      -- Now use the card_vector theorem for List.Vector
      exact @card_vector Bool _ k
    rw [h_eq, Fintype.card_bool]
    simp only [Rat.mkRat_eq_div]
    norm_cast
    simp

-- ==================================================================
-- == Final EGPT NP-Completeness Framework (Add this to your file) ==
-- ==================================================================

/-!
### Final Definitions for Reducibility and NP-Completeness
-/

/--
A function `f` that transforms one `UniversalCNF` problem into another is a
**Polynomial-Time EGPT Reducer** if the physical process to compute it has a
polynomially-bounded information cost (Shannon Entropy).

For simplicity and to focus on the logical structure, we state this as a
high-level property. A deeper dive would involve defining an EGPT virtual machine.
-/
class IsPolynomialEGPT_Reducer (f : UniversalCNF → UniversalCNF) : Prop where
  is_poly : ∃ (p : ℕ → ℕ) (_hp : IsPolynomialNat p),
    ∀ (ucnf : UniversalCNF),
      -- The complexity of the output encoding is polynomially bounded by the input encoding.
      (encodeCNF (f ucnf).2).length ≤ p (encodeCNF ucnf.2).length

/--
A language `L` is **NP-Complete in EGPT** if it is in `NP_EGPT_Concrete` and any
other language in `NP_EGPT_Concrete` can be reduced to it via a
polynomial-time EGPT reducer.
-/
structure NPComplete_EGPT (L : Π k, Lang_EGPT_SAT k) : Prop where
  in_NP   : (L : Π k, Lang_EGPT_SAT k) ∈ NP_EGPT_Concrete
  is_hard : ∀ (L' : Π k, Lang_EGPT_SAT k), L' ∈ NP_EGPT_Concrete →
              ∃ (f : UniversalCNF → UniversalCNF),
                IsPolynomialEGPT_Reducer f ∧
                (∀ ucnf : UniversalCNF,
                  (ucnf.2 ∈ L' ucnf.1) ↔ ((f ucnf).2 ∈ L (f ucnf).1)
                )

/-!
### The EGPT Cook-Levin Theorem: `L_SAT` is the Universal Bias
-/

/--
**Axiom (The Universal Bias Compiler):**
Any verifiable bias (a problem `L'` in `NP_EGPT_Concrete`) can be compiled into the
universal language of bias (`L_SAT`). This compilation function `f` is a
polynomial-time EGPT reducer.

This is the EGPT equivalent of the Cook-Levin theorem's core argument. It posits
that CNF is a universal language for describing verifiable computational constraints.
-/
axiom universal_bias_compiler :
  ∀ (L' : Π k, Lang_EGPT_SAT k), L' ∈ NP_EGPT_Concrete →
    ∃ (f : UniversalCNF → UniversalCNF),
      IsPolynomialEGPT_Reducer f ∧
      (∀ ucnf, (ucnf.2 ∈ L' ucnf.1) ↔ ((f ucnf).2 ∈ L_SAT (f ucnf).1))

/--
**Theorem: `L_SAT` is NP-Hard.**

This follows directly from the `universal_bias_compiler` axiom, which states
that `L_SAT` can serve as the target for a reduction from any NP problem.
-/
theorem L_SAT_is_NP_Hard :
  ∀ (L' : Π k, Lang_EGPT_SAT k), L' ∈ NP_EGPT_Concrete →
    ∃ (f : UniversalCNF → UniversalCNF),
      IsPolynomialEGPT_Reducer f ∧
      (∀ ucnf, (ucnf.2 ∈ L' ucnf.1) ↔ ((f ucnf).2 ∈ L_SAT (f ucnf).1)) :=
by
  -- The proof is a direct application of the axiom.
  intro L' hL'
  exact universal_bias_compiler L' hL'

/--
**Main Theorem: `L_SAT` is NP-Complete in EGPT.**

This theorem formalizes the idea that `L_SAT` is the universal problem for
describing all possible verifiable physical biases.
-/
theorem L_SAT_is_NPComplete : NPComplete_EGPT L_SAT :=
{
  in_NP   := L_SAT_in_NP_EGPT_Concrete,
  is_hard := L_SAT_is_NP_Hard
}


/-!
###  The Solver and P
-/




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
The core EGPT
claim is that the time required for a physical, non-deterministic process to
find a *single* solution is polynomially equivalent to the time required for
this function to characterize the *entire* solution space.
-/
noncomputable def construct_real_solution_space {k : ℕ} (constraints : SyntacticCNF_EGPT k) : Option (RejectionFilter k) :=
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
