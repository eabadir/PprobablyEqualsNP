import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Denumerable
import EGPT.NumberTheory.Core -- For ParticlePath and its equivalences
-- -- import Mathlib.Logic.Denumerable
namespace EGPT.Constraints

/-!
==================================================================
# EGPT Constraint Syntax

This file defines the canonical, syntactic data structures for representing
physical constraints in the EGPT framework. These constraints are expressed
as Boolean formulas in Conjunctive Normal Form (CNF).

This file is the single source of truth for these definitions and is
intended to be imported by both the NumberTheory and Complexity modules.
==================================================================
-/

/--
A `Literal_EGPT` represents a single literal (e.g., `xᵢ` or `¬xᵢ`).
It pairs a particle/variable index with a polarity.
-/
structure Literal_EGPT (k : ℕ) where
  particle_idx : Fin k
  polarity     : Bool

/-- Helper equivalence for `Literal_EGPT` to a product type. -/
def Literal_EGPT.equivProd {constrained_position : ℕ} : Literal_EGPT constrained_position ≃ (Fin constrained_position × Bool) :=
{
  toFun := fun lit => (lit.particle_idx, lit.polarity),
  invFun := fun p => { particle_idx := p.1, polarity := p.2 },
  left_inv := fun lit => by cases lit; simp,
  right_inv := fun p => by cases p; simp
}

/-- A `Clause_EGPT` is a list of literals, representing their disjunction. -/
abbrev Clause_EGPT (k : ℕ) := List (Literal_EGPT k)

/--
A `SyntacticCNF_EGPT` is the data structure for a CNF formula, represented
as a list of clauses. This is the concrete representation of a physical law.
-/
abbrev SyntacticCNF_EGPT (k : ℕ) := List (Clause_EGPT k)

-- === Syntactic Interpreter ===

/--
`evalLiteral` evaluates a single syntactic literal against a variable assignment vector.
-/
def evalLiteral {k : ℕ} (lit : Literal_EGPT k) (assignment : Vector Bool k) : Bool :=
  -- `xor` with `¬lit.polarity` implements the conditional negation:
  -- - If polarity is true, ¬polarity is false. `v xor false = v`.
  -- - If polarity is false, ¬polarity is true. `v xor true = ¬v`.
  xor (assignment.get lit.particle_idx) (not lit.polarity)

/--
`evalClause` evaluates a syntactic clause. A clause is satisfied if any of its literals are true.
-/
def evalClause {k : ℕ} (clause : Clause_EGPT k) (assignment : Vector Bool k) : Bool :=
  clause.any (fun lit => evalLiteral lit assignment)

/--
`evalCNF` evaluates a syntactic CNF formula. A formula is satisfied if all of its clauses are true.
This function is the semantic interpreter for our constraints.
-/
def evalCNF {k : ℕ} (cnf : SyntacticCNF_EGPT k) (assignment : Vector Bool k) : Bool :=
  cnf.all (fun clause => evalClause clause assignment)

-- === Encodability and Equivalence to ParticlePath ===

instance Literal_EGPT.encodable {k : ℕ} : Encodable (Literal_EGPT k) :=
  Encodable.ofEquiv _ (Literal_EGPT.equivProd)


instance Clause_EGPT.encodable {k : ℕ} : Encodable (Clause_EGPT k) :=
    List.encodable -- Explicitly use List.encodable

instance SyntacticCNF_EGPT.encodable {k : ℕ} : Encodable (SyntacticCNF_EGPT k) :=
    List.encodable -- Explicitly use List.encodable

open Function

/-- A dummy literal needed to build an injection `ℕ → List (Literal_EGPT k)`.
    We package the “`k ≠ 0`” assumption as a `Fact` so it can be found by
    type-class resolution. -/
instance {k : ℕ} [hk : Fact (0 < k)] : Inhabited (Literal_EGPT k) where
  default := { particle_idx := ⟨0, hk.out⟩, polarity := false }

/-- Lists of literals are infinite whenever `k ≠ 0`. -/
instance Clause_EGPT.infinite {k : ℕ} [Fact (0 < k)] :
    Infinite (Clause_EGPT k) := by
  classical
  let lit : Literal_EGPT k := default
  have inj : Injective (fun n : ℕ ↦ List.replicate n lit) := by
    intro m n hmn
    simpa [List.length_replicate] using congrArg List.length hmn
  exact Infinite.of_injective _ inj

/-- `Clause_EGPT` is denumerable (countably infinite) as soon as it is infinite. -/
instance Clause_EGPT.denumerable {k : ℕ} [Fact (0 < k)] :
    Denumerable (Clause_EGPT k) :=
  Denumerable.ofEncodableOfInfinite (Clause_EGPT k)

/-- `SyntacticCNF_EGPT` inherits `Infinite` and `Denumerable` in the same way. -/
instance SyntacticCNF_EGPT.infinite {k : ℕ} : -- Removed [Fact (0 < k)]
    Infinite (SyntacticCNF_EGPT k) :=
  -- SyntacticCNF_EGPT k is List (Clause_EGPT k).
  -- Clause_EGPT k is List (Literal_EGPT k).
  -- List (Literal_EGPT k) is Nonempty (it contains []). (via List.instNonempty)
  -- Therefore, by instInfiniteListOfNonempty, List (Clause_EGPT k) is Infinite.
  -- This should be found by typeclass inference.
  inferInstance

instance SyntacticCNF_EGPT.denumerable {k : ℕ} : -- Removed [Fact (0 < k)]
    Denumerable (SyntacticCNF_EGPT k) :=
  Denumerable.ofEncodableOfInfinite (SyntacticCNF_EGPT k)

/--
**The New Equivalence (Un-Axiomatized):**
There exists a computable bijection between the syntactic representation of a
CNF formula and the `ParticlePath` type. We state its existence via `Encodable`.
-/
noncomputable def equivSyntacticCNF_to_ParticlePath {k : ℕ} : SyntacticCNF_EGPT k ≃ EGPT.ParticlePath :=
  -- We use the power of Lean's typeclass synthesis for Denumerable types.
  -- `List`, `Fin k`, and `Bool` are all denumerable, so their product and list
  -- combinations are also denumerable. `ParticlePath` is denumerable via its equiv to `ℕ`.
  (Denumerable.eqv (SyntacticCNF_EGPT k)).trans (EGPT.NumberTheory.Core.equivParticlePathToNat.symm)

noncomputable def cnfToParticlePMF (full_cnf : Σ k, SyntacticCNF_EGPT k) : EGPT.NumberTheory.Core.ParticlePMF :=
  -- 1. Encode the entire CNF structure (including k) into a single natural number.
  let n := Encodable.encode full_cnf

  -- 2. Convert the natural number to a rational using a simple construction
  -- We can use the fact that every natural number corresponds to a rational
  let q : ℚ := n

  -- 3. Convert this rational number into its canonical EGPT representation (a ParticlePMF).
  EGPT.NumberTheory.Core.fromRat q

noncomputable def particlePMFToCnf (pmf : EGPT.NumberTheory.Core.ParticlePMF) : Σ k, SyntacticCNF_EGPT k :=
  -- 1. Convert the ParticlePMF into its mathlib rational value.
  let q := EGPT.NumberTheory.Core.toRat pmf

  -- 2. Convert the rational back to a natural number (inverse of the injection we used)
  -- Since we used simple coercion ℕ → ℚ, we can extract the numerator if denominator is 1
  let n := q.num.natAbs -- This works for rationals that came from naturals

  -- 3. Decode this natural number back into the full CNF structure.
  -- The output is an Option; we can get the value because the encoding is total.
  match Encodable.decode n with
  | some cnf => cnf
  | none => ⟨0, []⟩ -- Default empty CNF in case of decode failure
