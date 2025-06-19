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
