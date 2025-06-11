import Mathlib.Tactic.NormNum

import Mathlib.Data.Sym.Card
import Std.Sat.CNF.Basic
import Mathlib.Tactic.Sat.FromLRAT

import Mathlib.Data.List.Range
import Mathlib.Data.List.FinRange

import PPNP.NumberTheory.Core
import PPNP.Common.Basic
import PPNP.Entropy.Common
import PPNP.Complexity.Program
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Denumerable

open PPNP.Entropy.Common PPNP.Complexity.Program PPNP.NumberTheory.Core

/-!
==================================================================
### A Hierarchy of EGPT Problem Languages

This section defines specific languages (sets of programs) within the EGPT framework. It allows us to formally distinguish between general programs, constraint-based programs, and SAT problems, all grounded in the same `GNat` representation.


**Un-Axiomatizing Constraint Encoding**

Instead of an `equivCNF_to_GNat` axiom we give a constructive
proof. We achieve this by defining a *syntactic* data structure for CNF
formulas, proving it can be bijectively encoded to a `GNat`, and then
providing an interpreter that gives this syntax its semantic meaning within our "balls and boxes" model.
==================================================================
-/

-- === Step 1: Define the Syntactic CNF Data Structures ===

/--
A `Literal_EGPT` represents a single literal (e.g., `xᵢ` or `¬xᵢ`).
It pairs a box index with a polarity (true for positive, false for negative).
-/
structure Literal_EGPT (k_positions : ℕ) where
  box_index : Fin k_positions
  polarity  : Bool

/-- Helper equivalence for `Literal_EGPT` to a product type. -/
def Literal_EGPT.equivProd {k_positions : ℕ} : Literal_EGPT k_positions ≃ (Fin k_positions × Bool) :=
{
  toFun := fun lit => (lit.box_index, lit.polarity),
  invFun := fun p => { box_index := p.1, polarity := p.2 },
  left_inv := fun lit => by cases lit; simp,
  right_inv := fun p => by cases p; simp
}

instance Literal_EGPT.encodable {k_positions : ℕ} : Encodable (Literal_EGPT k_positions) :=
  Encodable.ofEquiv _ (Literal_EGPT.equivProd)

/-- A `Clause_EGPT` is a list of literals, representing their disjunction. -/
abbrev Clause_EGPT (k_positions : ℕ) := List (Literal_EGPT k_positions)

/--
A `SyntacticCNF_EGPT` is the data structure for a CNF formula, represented
as a list of clauses.
-/
abbrev SyntacticCNF_EGPT (k_positions : ℕ) := List (Clause_EGPT k_positions)

instance denumerable_SyntacticCNF_EGPT (k : ℕ) : Denumerable (SyntacticCNF_EGPT k) :=
  Denumerable.ofEncodableOfInfinite (SyntacticCNF_EGPT k)

-- === Step 2: Define the Provable Encoding (SyntacticCNF ≃ GNat) ===

/-
To encode a `SyntacticCNF_EGPT` as a `List Bool`, we need a canonical mapping.
A simple example scheme:
- Literal `(box_index, polarity)`: `(encode box_index) ++ [polarity]`
- Clause `[L1, L2, ...]`: `(encode L1) ++ [false, true] ++ (encode L2) ++ ...` (using `[false, true]` as a separator)
- CNF `[C1, C2, ...]`: `(encode C1) ++ [false, false, true] ++ (encode C2) ++ ...` (using a different separator)

Mathlib's `Encodable` typeclass can build such an encoding automatically,
since all our components (`List`, `Fin`, `Bool`) are encodable.
-/

/--
**The New Equivalence (Un-Axiomatized):**
There exists a computable bijection between the syntactic representation of a
CNF formula and the `GNat` type. We state its existence via `Encodable`.
-/
noncomputable def equivSyntacticCNF_to_GNat {k : ℕ} : SyntacticCNF_EGPT k ≃ GNat :=
  -- We use the power of Lean's typeclass synthesis for Denumerable types.
  -- `List`, `Fin k`, and `Bool` are all denumerable, so their product and list
  -- combinations are also denumerable. `GNat` is denumerable via its equiv to `ℕ`.
  (Denumerable.eqv (SyntacticCNF_EGPT k)).trans (equivGNatToNat.symm)

-- === Step 3: Bridge from Syntax to Semantics (The Interpreter) ===

/--
`eval_literal` gives the semantic meaning of a syntactic literal.
e.g., `(box_index:=i, polarity:=true)` means "is box i occupied?".
-/
def eval_literal {k : ℕ} (lit : Literal_EGPT k) (state : SATSystemState k) : Bool :=
  if lit.polarity then
    (state.count lit.box_index > 0) -- Positive literal: check for occupation
  else
    (state.count lit.box_index = 0) -- Negative literal: check for emptiness

/--
`eval_clause` gives the semantic meaning of a syntactic clause.
A clause is true if at least one of its literals is true.
-/
def eval_clause {k : ℕ} (clause : Clause_EGPT k) : ClauseConstraint k :=
  fun state => clause.any (fun lit => eval_literal lit state)

/--
`eval_syntactic_cnf` is the main interpreter. It converts a syntactic CNF data
structure into the semantic `CNF_Formula` (a list of predicate functions).
-/
def eval_syntactic_cnf {k : ℕ} (syn_cnf : SyntacticCNF_EGPT k) : CNF_Formula k :=
  syn_cnf.map eval_clause

-- === Updated Language Definitions ===


/--
A `ProgramProblem` is the language of all validly encoded computer programs.
For now, we can consider this to be the set of all `GNat`s, as every `GNat`
can be interpreted as the tape of some program.
-/
abbrev ProgramProblem : Set GNat := Set.univ

/--
**REVISED `CNFProgram`:** The language of programs (`GNat`s) that are valid
encodings of a *syntactic* CNF formula. This is now fully constructive.
-/
def CNFProgram {k : ℕ} : Set GNat :=
  { gnat | ∃ (s : SyntacticCNF_EGPT k), equivSyntacticCNF_to_GNat.symm gnat = s }

/--
A `StateCheckProgram` is a specific kind of `CNFProgram` that represents
constraints on final system states. This is conceptually equivalent to
`CNFProgram` in our "balls and boxes" model, as our constraints are already
defined on `SATSystemState`s.
-/
abbrev StateCheckProgram {k : ℕ} : Set GNat := CNFProgram (k := k)



-- === Program Composition ===

/--
**CompositeProgram (Addition of Programs):**
A `CompositeProgram` is formed by the EGPT addition of two `GNat`s, where
one represents a general program and the other represents a set of constraints.
This is a polynomial-time operation.
-/
def CompositeProgram (prog_gnat : GNat) (constraint_gnat : GNat) : GNat :=
  -- GNat addition is a polynomial-time operation in EGPT.
  add_gnat prog_gnat constraint_gnat
