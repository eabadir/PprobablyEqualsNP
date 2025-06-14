import Mathlib.Tactic.NormNum

import Mathlib.Data.Sym.Card
import Std.Sat.CNF.Basic
import Mathlib.Tactic.Sat.FromLRAT

import Mathlib.Data.List.Range
import Mathlib.Data.List.FinRange

import EGPT.NumberTheory.Core
import EGPT.Core
import EGPT.Complexity.Core
import EGPT.NumberTheory.Filter
namespace EGPT.Complexity

open EGPT.NumberTheory.Core EGPT.Complexity EGPT.NumberTheory.Filter

/-!
## EGPT COMPLEXITY CLASSES
This section defines P and NP based on the concrete computational
model established in Phase 1.
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
An NDMachine for SAT is a system of k particles, each with its own
state and law, evolving under a global set of constraints (the CNF).
-/
structure NDMachine_SAT (k : ℕ) where
  -- The initial state of all k particles.
  initial_states : Vector ParticleState_SAT k
  -- The global constraints on the system's state vector.
  constraints : SyntacticCNF_EGPT k

/--
Converts a `SystemHistory` (a set of parallel tapes) into a single,
serial `PathProgram` by concatenating all tapes. This represents the
total computational work of the simulation.
-/
def prog_of_history {n : ℕ} (hist : SystemHistory n) : PathProgram :=
  { current_state := 0, tape := hist.toList.flatMap id }

-- Implementation of the universal solve function
noncomputable def ndm_run_solverold {n : ℕ}
    (initial_states : Vector ParticleState n)
    (target : TargetStatePredicate n)
    (time_limit : ℕ)
    (seed : ℕ)
    : Option (Vector PathProgram n) :=
  -- Start with fresh programs at their initial positions.
  let progs_t0 := initial_states.map (fun s => mkPathProgram s.position)

  -- Loop for `time_limit` steps.
  let rec loop (t : ℕ) (current_progs : Vector PathProgram n) : Option (Vector PathProgram n) :=
    if h_lt : t < time_limit then
      -- We are still within the time limit; keep simulating.
      let current_positions := current_progs.map (fun p => p.current_state)
      if target current_positions then
        some current_progs -- Solution found!
      else
        -- Run one more step of the simulation.
        let next_progs := Vector.ofFn (fun i : Fin n =>
          let prog := current_progs.get i
          let law := (initial_states.get i).law
          let source := toBiasedSource law (seed + i.val * time_limit + t)
          let choice := source.stream 0
          { tape := prog.tape.append [choice],
            current_state :=  prog.current_state + (if choice then 1 else -1)  }
        )
        loop (t + 1) next_progs
    else
      none -- Reached or exceeded the time limit
    termination_by
      time_limit - t
    decreasing_by
      simpa using Nat.sub_succ_lt_self time_limit t h_lt

  loop 0 progs_t0

-- In EGPT/Complexity/Core.lean (Revised)

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
The true EGPT solver. It simulates the system forward, checking constraints at each step.
It returns the first valid state it encounters.
This is a non-deterministic search for a satisfying assignment.
-/
noncomputable def ndm_run_solver {k : ℕ} (machine : NDMachine_SAT k) (time_limit : ℕ) (seed : ℕ) : Option (Vector Bool k) :=
  let rec loop (t : ℕ) (current_states : Vector ParticleState_SAT k) : Option (Vector Bool k) :=
    if t >= time_limit then
      none -- Timeout
    else
      -- 1. Advance all particles by one step according to their individual laws.
      let next_particle_states := advance_state current_states (seed + t)
      let next_system_state := get_system_state_vector next_particle_states

      -- 2. Apply the filter: check if the new system state is valid.
      if evalCNF machine.constraints next_system_state then
        -- This state is a valid solution. Halt and return it.
        some next_system_state
      else
        -- The state is invalid. Continue the search from this new (but invalid) state.
        -- A different model could be to "reject" the step and retry from `current_states`.
        -- Let's stick with the simpler "keep walking" model.
        loop (t + 1) next_particle_states
    termination_by time_limit - t

  loop 0 machine.initial_states
/-!
# OLD DEPRECATED SECTION - THE FOLLOWING DEFINITIONS ARE NOW OBSOLETE AND NEED TO BE REPLACED WITH THE NEW ONES BASED ON THE NDMachine and PathProgram structures.
-/

/--
The polynomial time class P_EGPT, redefined using our number-theoretic concept of polynomial time.
-/
def P_EGPT_NT : Set Lang_EGPT :=
{ L | ∃ (solver : EGPT_Input → Bool)
         (complexity : EGPT_Input → ParticlePath),
       -- The solver must be bounded by an EGPT-polynomial function.
       IsBoundedByPolynomial complexity ∧
       -- The solver must correctly decide the language.
       (∀ input, L input = solver input)
}

/--
A `Lang_EGPT_SAT` is a decision problem on combinatorial systems.
-/
abbrev Lang_EGPT_SAT := EGPT_SAT_Input → Bool

/--
A `Certificate` for an EGPT-SAT problem is a vector of `PathProgram`s,
one for each particle. The certificate represents the full history (the paths)
that lead to a proposed final state.
-/
abbrev Certificate (n_particles : ℕ) := Vector PathProgram n_particles



/-!
###  Connecting Paths to States

This function is the crucial bridge between the dynamic particle paths
(the certificate) and the static, combinatorial `SATSystemState`.
-/

/--
Calculates the position of a single particle (as an Integer) given its path.
A simple definition is the number of `true`s minus the number of `false`s.
-/
def particlePosition (tape : ComputerTape) : ℤ :=
  (tape.filter (· == true)).length - (tape.filter (· == false)).length


/--
Generates a `SATSystemState` (a multiset of box occupancies) from a
`Certificate` (a vector of particle programs) at a specific time `t`.

- `progs`: The certificate containing the path for each particle.
- `t`: The time at which to take the snapshot of the system.
- `pos_to_box`: A function mapping a particle's integer position to a specific
  "box" index (`Fin k_positions`). This mapping is part of the problem setup
  and defines how the continuous space of positions is discretized.
-/
def generateSystemState {n_particles k_positions : ℕ}
    (progs : Certificate n_particles) (t : ℕ)
    (pos_to_box : ℤ → Fin k_positions) : SATSystemState k_positions :=
  progs.toList.map (fun prog => pos_to_box (particlePosition (prog.tape.take t))) |> Multiset.ofList

/-!
### EGPT Complexity & Canonical SAT Systems

With the path-to-state bridge in place, we can now formally define the
complexity classes for our combinatorial EGPT-SAT problems.
-/

/--
A verifier for EGPT-SAT problems. It takes an EGPT_SAT_Input and a Certificate
(a vector of ComputerPrograms) and determines if the certificate is a valid,
satisfying solution. The `pos_to_box` mapping is part of the verifier's logic.
-/
structure SAT_Verifier where
  pos_to_box : ℤ → Fin k_positions -- The specific discretization for this verifier
  verify (input : EGPT_SAT_Input) (certificate : Certificate input.n_particles) : Bool :=
    let final_state := generateSystemState certificate input.n_particles pos_to_box
    -- A certificate is valid if:
    -- 1. It has the correct number of particles.
    -- 2. It satisfies all CNF constraints.
    final_state.card = input.n_particles ∧ input.cnf.all (fun c => c final_state)


/--
The class `NP_EGPT_SAT` contains combinatorial problems for which a "yes"
answer can be verified in EGPT-polynomial time.
-/
def NP_EGPT_SAT : Set Lang_EGPT_SAT :=
{ L | ∃ (sv : SAT_Verifier) (poly_bound : ParticlePath → ParticlePath) (_h_poly : IsPolynomialEGPT poly_bound),
      ∀ (input : EGPT_SAT_Input),
        L input ↔ ∃ (cert : Certificate input.n_particles),
          -- The complexity of each program in the certificate must be polynomially bounded.
          (cert.toList.all (fun prog => prog.complexity ≤ equivParticlePathToNat.toFun (poly_bound (fromNat input.n_particles)))) ∧
          -- The SAT_Verifier must accept the certificate for the given input.
          sv.verify input cert
}

/--
The class `P_EGPT_SAT` contains combinatorial problems that can be solved
directly by a deterministic algorithm in EGPT-polynomial time.
-/
def P_EGPT_SAT : Set Lang_EGPT_SAT :=
{ L | ∃ (solver : EGPT_SAT_Input → Bool)
         (complexity_bound : ParticlePath → ParticlePath) (_h_poly : IsPolynomialEGPT complexity_bound),
      -- The solver must be bounded by an EGPT-polynomial function of its input size.
      -- The solver must correctly decide the language.
      (∀ input, L input = solver input)
}

/-!
### NP-Completeness in the EGPT Framework

To define NP-completeness, we must first formalize what it means for one
combinatorial problem to be "at least as hard as" another. This is done
through the concept of a polynomial-time reduction.
-/

/--
A function to measure the size of an EGPT-SAT problem instance.
This is used to bound the complexity of a reduction function.
-/
def EGPT_SAT_Input.sizeOf (input : EGPT_SAT_Input) : ℕ :=
  input.n_particles + input.k_positions + input.cnf.length

/--
A `PolyTimeReducer_EGPT_SAT` encapsulates a function that transforms problem
instances, along with a proof that this transformation is finitely countable (i.e. solution -> Nat in Lean which implies ParticlePath in the EGPT sense
-/
structure PolyTimeReducer_EGPT_SAT where
  transform : EGPT_SAT_Input → EGPT_SAT_Input
  complexity_bound : ParticlePath → ParticlePath
  h_poly : IsPolynomialEGPT complexity_bound


/--
Defines polynomial-time reducibility between two EGPT-SAT languages.
`L' <=p L` means that any instance of `L'` can be efficiently transformed
into an equivalent instance of `L`.
-/
def PolyTimeReducible_EGPT_SAT (L' L : Lang_EGPT_SAT) : Prop :=
  ∃ (f : PolyTimeReducer_EGPT_SAT),
    ∀ (input : EGPT_SAT_Input), L' input ↔ L (f.transform input)

-- Define an infix operator for convenience.
infix:50 " <=p " => PolyTimeReducible_EGPT_SAT

/--
A language `L` is **EGPT-NP-complete** if it is in `NP_EGPT_SAT` and
is "at least as hard" as every other problem in `NP_EGPT_SAT`.
-/
def EGPT_NPComplete (L : Lang_EGPT_SAT) : Prop :=
  -- Condition 1: The problem is in our NP class.
  (L ∈ NP_EGPT_SAT) ∧
  -- Condition 2: The problem is NP-hard within our class.
  (∀ (L' : Lang_EGPT_SAT) (_hL' : L' ∈ NP_EGPT_SAT), L' <=p L)
