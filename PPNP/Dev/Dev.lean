import Mathlib.Tactic.NormNum

import Mathlib.Data.Sym.Card
import Std.Sat.CNF.Basic
import Mathlib.Tactic.Sat.FromLRAT

import Mathlib.Data.List.Range
import Mathlib.Data.List.FinRange

import PPNP.NumberTheory.Core
import PPNP.Common.Basic
import PPNP.Entropy.Common

namespace PPNP.Complexity.Program

/-- A single instruction/choice, represented by a Bool.
    Corresponds to one "bit" of choice from an i.i.d. source
    or one step in a binary decision tree. -/
def ComputerInstruction := Bool

/-- A sequence of choices/instructions forming the "program" or "path description".
    This is conceptually the Turing Machine's input tape. -/
def ComputerTape := List ComputerInstruction

/-- Represents the abstract state of a single particle or a simple system.
    The specific structure of SystemState is not crucial for the complexity definition
    focused on tape length, but it's part of the program definition. -/
structure SystemState where -- Example placeholder definition
  val : ℕ --Noting ℕ is List Bool is GNat but Lean's simp will handle Nat better

/-- A ComputerProgram is defined by an initial state and a tape of instructions
    that drives its evolution. -/
structure ComputerProgram where
  initial_state : SystemState
  tape : ComputerTape



/--
A `SystemState` is a distribution of particles into a finite number of
positions. It is represented by a `Multiset` over `Fin k_positions`, where
`k_positions` is the number of "boxes". The cardinality of the multiset is
the number of particles ("balls").
-/
abbrev SATSystemState (k_positions : ℕ) := Multiset (Fin k_positions)

/--
A `ClauseConstraint` is a rule that a `SATSystemState` must satisfy. It is a
predicate on the distribution of particles.
This is the EGPT equivalent of a single clause in a CNF formula.
-/
abbrev ClauseConstraint (k_positions : ℕ) := SATSystemState k_positions → Bool

/--
A `CNF_Formula` is a list of `ClauseConstraint`s. A `SATSystemState` is
satisfying if and only if it satisfies every constraint in the list.
-/
abbrev CNF_Formula (k_positions : ℕ) := List (ClauseConstraint k_positions)

/-!
### Section 2: The EGPT-SAT Problem

We define the SAT problem in this combinatorial framework.
-/

/--
The input for an EGPT-SAT problem, defined by the number of particles,
the number of possible positions, and the set of combinatorial constraints.
-/
structure EGPT_SAT_Input where
  n_particles : ℕ
  k_positions : ℕ
  cnf : CNF_Formula k_positions
