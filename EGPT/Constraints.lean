import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Denumerable
import EGPT.Core
import EGPT.NumberTheory.Core -- For ParticlePath and its equivalences
-- -- import Mathlib.Logic.Denumerable
namespace EGPT.Constraints

open EGPT NumberTheory.Core



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

noncomputable def cnfToParticleHistoryPMF (full_cnf : Σ k, SyntacticCNF_EGPT k) : EGPT.NumberTheory.Core.ParticleHistoryPMF :=
  -- 1. Encode the entire CNF structure (including k) into a single natural number.
  let n := Encodable.encode full_cnf

  -- 2. Convert the natural number to a rational using a simple construction
  -- We can use the fact that every natural number corresponds to a rational
  let q : ℚ := n

  -- 3. Convert this rational number into its canonical EGPT representation (a ParticleHistoryPMF).
  EGPT.NumberTheory.Core.fromRat q

noncomputable def ParticleHistoryPMFToCnf (pmf : EGPT.NumberTheory.Core.ParticleHistoryPMF) : Σ k, SyntacticCNF_EGPT k :=
  -- 1. Convert the ParticleHistoryPMF into its mathlib rational value.
  let q := EGPT.NumberTheory.Core.toRat pmf

  -- 2. Convert the rational back to a natural number (inverse of the injection we used)
  -- Since we used simple coercion ℕ → ℚ, we can extract the numerator if denominator is 1
  let n := q.num.natAbs -- This works for rationals that came from naturals

  -- 3. Decode this natural number back into the full CNF structure.
  -- The output is an Option; we can get the value because the encoding is total.
  match Encodable.decode n with
  | some cnf => cnf
  | none => ⟨0, []⟩ -- Default empty CNF in case of decode failure



/-!
### Canonical CNF and Unified Complexity

This file formalizes the user's intuition that the "search cost" and "address
cost" of verifying a solution should be the same. It does so by defining a
**Canonical Form** for CNF formulas, where literals within each clause are
sorted by their variable index. This makes the search order deterministic and
directly related to the variable addresses.
-/

/--
**Defines a canonical ordering for literals based on their variable index.**
`l₁ ≤ l₂` if the index of `l₁` is less than or equal to the index of `l₂`.
-/
def literal_le {k : ℕ} (l₁ l₂ : Literal_EGPT k) : Bool :=
  l₁.particle_idx.val ≤ l₂.particle_idx.val

/--
**Propositional version of literal ordering for use with List.Sorted.**
`l₁ ≤ l₂` if the index of `l₁` is less than or equal to the index of `l₂`.
-/
def literal_le_prop {k : ℕ} (l₁ l₂ : Literal_EGPT k) : Prop :=
  l₁.particle_idx.val ≤ l₂.particle_idx.val

/--
**Defines a canonical ordering for literals based on their variable index.**
`literal_le_bool l₁ l₂` is true if the index of `l₁` is less than or equal to
the index of `l₂`. We use a `Bool`-returning function as required by `mergeSort`.
-/
def literal_le_bool {k : ℕ} (l₁ l₂ : Literal_EGPT k) : Bool :=
  l₁.particle_idx.val ≤ l₂.particle_idx.val

-- Make literal_le_prop decidable
instance {k : ℕ} : DecidableRel (@literal_le_prop k) :=
  fun l₁ l₂ => by
    unfold literal_le_prop
    exact Nat.decLe l₁.particle_idx.val l₂.particle_idx.val


-- The core idea is to represent numbers in unary using `true`s
-- and use `false`s as delimiters.

/-- Encodes a natural number `n` into a list of `n` `true`s. -/
def encodeNat (n : ℕ) : ComputerTape :=
  List.replicate n true

/-- Encodes a single literal by encoding its index and prefixing its polarity. -/
def encodeLiteral {k : ℕ} (l : Literal_EGPT k) : ComputerTape :=
  l.polarity :: encodeNat l.particle_idx.val

/-- Encodes a clause by joining its encoded literals with a single `false` delimiter. -/
def encodeClause {k : ℕ} (c : Clause_EGPT k) : List Bool :=
  c.foldl (fun acc l => List.append acc (List.append (encodeLiteral l) [false])) []

/--
**A General-Purpose Lemma for Bounding the Sum of a Mapped List.**

This is a more powerful and reusable alternative to the missing `List.sum_le_sum_of_le`.
It proves that the sum of a function `f` mapped over a list `l` is bounded by
the length of the list times a uniform upper bound `M` on the value of `f`.

**Proof by Induction:**
- Base Case: For an empty list `[]`, the sum is 0 and the length is 0. `0 ≤ 0 * M` is true.
- Inductive Step: For a list `h :: t`, `sum(map f (h::t)) = f(h) + sum(map f t)`.
  By hypothesis, `f(h) ≤ M` and `sum(map f t) ≤ |t|*M`.
  Therefore, the total sum is `≤ M + |t|*M`, which equals `(|t|+1)*M`.
-/
lemma sum_map_le_length_mul_bound {α : Type} (l : List α) (f : α → ℕ) (M : ℕ)
  (h_bound : ∀ x ∈ l, f x ≤ M) : (l.map f).sum ≤ l.length * M :=
by
  induction l with
  | nil =>
    simp
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    -- The induction hypothesis `ih` applies to the tail of the list.
    -- We need to prove the bound `h_bound` holds for the tail.
    have h_bound_tail : ∀ x ∈ tail, f x ≤ M := by
      intro x h_mem_tail
      exact h_bound x (List.mem_cons_of_mem head h_mem_tail)
    -- Apply the induction hypothesis.
    specialize ih h_bound_tail
    -- The bound `h_bound` also holds for the head.
    have h_bound_head : f head ≤ M := h_bound head List.mem_cons_self
    -- The goal is `f head + (tail.map f).sum ≤ (tail.length + 1) * M`.
    -- We know `f head ≤ M` and `(tail.map f).sum ≤ tail.length * M`.
    -- Adding these two inequalities gives the result.
    calc
      f head + (tail.map f).sum ≤ M + tail.length * M := Nat.add_le_add h_bound_head ih
      _ = (1 + tail.length) * M := by ring
      _ = (tail.length + 1) * M := by rw [Nat.add_comm]


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
**The Universal CNF to ParticlePath EGPT Bijection .**

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


/--
**Predicate to check if a single clause is in canonical (sorted) form.**
A clause is canonical if it is sorted according to `literal_le_bool`.
This uses the `List.Pairwise` predicate, which checks that the relation holds
for all adjacent elements. For a sorted list, this is sufficient.
-/
def IsClauseCanonical {k : ℕ} (c : Clause_EGPT k) : Prop :=
  c.Pairwise (fun l₁ l₂ => literal_le_bool l₁ l₂)

/--
**Predicate to check if an entire CNF formula is in canonical form.**
A CNF is canonical if all of its clauses are canonical.
-/
def IsCNFCanonical {k : ℕ} (cnf : SyntacticCNF_EGPT k) : Prop :=
  ∀ c ∈ cnf, IsClauseCanonical c

/--
**A type for CNF formulas that are proven to be in Canonical Form.**
-/
abbrev CanonicalCNF (k : ℕ) := { cnf : SyntacticCNF_EGPT k // IsCNFCanonical cnf }
/--
**A "Compiler" that converts any CNF into its unique Canonical Form.**
This function sorts the literals within each clause using `mergeSort`,
making the problem representation unambiguous and aligning the search order
with the address order.
-/
def normalizeCNF {k : ℕ} (cnf : SyntacticCNF_EGPT k) : CanonicalCNF k :=
  -- Create the new, sorted CNF by mapping `mergeSort` over the clauses.
  let sorted_cnf := cnf.map (fun c => c.mergeSort literal_le_bool)
  -- Package it with the proof that it is now canonical.
  ⟨sorted_cnf, by
    -- Proof: We need to show that every clause in `sorted_cnf` is canonical.
    intro c h_c_mem
    rw [List.mem_map] at h_c_mem
    rcases h_c_mem with ⟨c_orig, _, h_c_eq⟩
    -- The goal is to prove `IsClauseCanonical c`.
    -- We know `c` is equal to `c_orig.mergeSort ...`, so we rewrite the goal.
    rw [← h_c_eq] -- CORRECTED: Rewrite in reverse.
    -- The goal is now `IsClauseCanonical (c_orig.mergeSort literal_le_bool)`.
    unfold IsClauseCanonical
    -- We must prove that `mergeSort` produces a `Pairwise` sorted list.
    -- This is exactly what `List.sorted_mergeSort` guarantees.
    apply List.sorted_mergeSort
    · -- Prove transitivity for `literal_le_bool`.
      intro l1 l2 l3 h1 h2
      -- Unfold the definition to expose the underlying `≤` on natural numbers.
      unfold literal_le_bool at *
      -- Convert boolean decisions to propositions
      have h1_prop : l1.particle_idx.val ≤ l2.particle_idx.val :=
        of_decide_eq_true h1
      have h2_prop : l2.particle_idx.val ≤ l3.particle_idx.val :=
        of_decide_eq_true h2
      -- Use transitivity and convert back to boolean
      have h_trans : l1.particle_idx.val ≤ l3.particle_idx.val :=
        Nat.le_trans h1_prop h2_prop
      exact decide_eq_true_iff.mpr h_trans
    · -- Prove totality for `literal_le_bool`.
      intro l1 l2
      unfold literal_le_bool
      -- The goal is `(decide (l1.idx ≤ l2.idx) || decide (l2.idx ≤ l1.idx)) = true`.
      -- This follows from the totality of `≤` on ℕ.
      have h_total := Nat.le_total l1.particle_idx.val l2.particle_idx.val
      cases h_total with
      | inl h =>
        simp [Bool.or_eq_true]
        left
        exact h
      | inr h =>
        simp [Bool.or_eq_true]
        right
        exact h
  ⟩


/--
**Helper Lemma: `List.any` is invariant under permutations.**

If two lists `l₁` and `l₂` are permutations of each other, then a predicate `p`
holds for any element in `l₁` if and only if it holds for any element in `l₂`.
-/
lemma List.Perm.any_iff {α : Type} {p : α → Bool} {l₁ l₂ : List α} (h_perm : l₁.Perm l₂) :
  l₁.any p = l₂.any p :=
by
  -- The proof is by induction on the permutation itself.
  induction h_perm with
  | nil => simp
  | cons x _ ih => simp [ih]
  | swap x y l =>
    -- Need to prove: (y :: x :: l).any p = (x :: y :: l).any p
    -- This expands to: (p y || (p x || l.any p)) = (p x || (p y || l.any p))
    simp only [List.any_cons]
    -- Use left commutativity of Bool.or: a || (b || c) = b || (a || c)
    rw [Bool.or_left_comm]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]



/--
**Equivalence of Evaluation:**
Normalizing a CNF via `mergeSort` does not change its logical meaning, because
`mergeSort` is a permutation of the original list, and `evalClause` (which uses
`List.any`) is invariant under permutations.
-/
theorem evalCNF_normalize_eq_evalCNF {k : ℕ} (cnf : SyntacticCNF_EGPT k) (assignment : Vector Bool k) :
  evalCNF (normalizeCNF cnf).val assignment = evalCNF cnf assignment :=
by
  -- Unfold the definitions to get to the core of the proof.
  unfold evalCNF normalizeCNF
  simp only [Subtype.coe_eta]
  -- The goal should now be about List.all over mapped list
  -- We'll use simp to simplify List.all_map and then show function equivalence
  simp only [List.all_map]
  -- Goal is now showing function equivalence
  congr 1
  ext c
  -- Goal is: `evalClause (c.mergeSort ...) = evalClause c`.
  unfold evalClause
  -- The goal is now: `(c.mergeSort ...).any ... = c.any ...`.
  -- We use the fact that `mergeSort` is a permutation (`List.mergeSort_perm`).
  have h_perm : (c.mergeSort literal_le_bool).Perm c := List.mergeSort_perm c _
  -- Now we apply our custom helper lemma.
  exact List.Perm.any_iff h_perm




/-- Helper Lemma: The encoding of a clause with its separator has length ≥ 1. -/
lemma encoded_clause_with_sep_len_ge_one {k : ℕ} (c : Clause_EGPT k) :
  1 ≤ (List.append (encodeClause c) [false, false]).length :=
by
  -- From the docs: `(as ++ bs).length = as.length + bs.length`
  -- And `List.append a b` is definitionally `a ++ b`.
  simp [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]


/--
**Helper Lemma:** Shows that `foldl (++) []` on a list of lists is equivalent
to flattening the list. This is the crucial algebraic bridge.
-/
lemma foldl_append_nil_eq_flatten (l : List (List α)) :
  List.foldl (· ++ ·) [] l = l.flatten :=
by
  induction l with
  | nil =>
    -- Base case: `foldl (++) [] []` is `[]`, and `[].flatten` is `[]`.
    simp
  | cons h t ih =>
    -- Inductive step:
    -- `foldl (++) [] (h::t) = foldl (++) (h) t`
    -- `(h::t).flatten = h ++ t.flatten`
    -- `foldl (++) h t = h ++ foldl (++) [] t` (This needs a small proof)
    have h_fold_append : ∀ (init : List α) (l' : List (List α)),
      List.foldl (· ++ ·) init l' = init ++ l'.flatten := by
        intro init l'
        induction l' generalizing init with
        | nil => simp
        | cons head tail ih_inner =>
          simp only [List.foldl_cons, List.flatten_cons]
          rw [ih_inner (init ++ head)]
          rw [List.append_assoc]
    rw [h_fold_append]
    -- [] ++ (h :: t).flatten = (h :: t).flatten
    simp

/--
**Helper Lemma:** Shows that `foldl List.append` is equivalent to `foldl (++)`.
This bridges the gap between different append representations.
-/
@[simp] lemma foldl_List_append_eq_foldl_append (l : List (List α)) :
  List.foldl List.append [] l = List.foldl (· ++ ·) [] l :=
by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp only [List.foldl_cons]
    -- We need to show that folding with List.append is the same as folding with ++
    have h_equiv : ∀ (acc : List α) (rest : List (List α)),
      List.foldl List.append acc rest = List.foldl (· ++ ·) acc rest := by
      intro acc rest
      induction rest generalizing acc with
      | nil => rfl
      | cons head tail ih_inner =>
        simp only [List.foldl_cons]
        -- Show that List.append = ++
        rw [← List.append_eq]
        rw [ih_inner]
    exact h_equiv h t

/--
**Helper Lemma:** Direct version using `List.append` instead of `++`.
-/
@[simp] lemma foldl_List_append_nil_eq_flatten (l : List (List α)) :
  List.foldl List.append [] l = l.flatten :=
by
  rw [foldl_List_append_eq_foldl_append, foldl_append_nil_eq_flatten]





/-!
### Final, Robust Proof for `encodeCNF_length_ge_num_clauses`

This proof uses a clean, algebraic approach, leveraging a key identity between
`foldl` and `flatten` to avoid the type-inference and tactical issues
encountered in previous attempts.
-/



/--
**Theorem: The length of an encoded CNF is at least the number of its clauses.**
theorem encodeCNF_length_ge_num_clauses {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
  cnf.length ≤ (encodeCNF cnf).length :=
-/
theorem encodeCNF_length_ge_num_clauses {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
  cnf.length ≤ (encodeCNF cnf).length :=
by
  induction cnf with
  | nil =>
    simp [encodeCNF, encodeNat]
  | cons head tail ih =>
    calc
      (head :: tail).length = tail.length + 1 := by simp [List.length]
      _ ≤ (encodeCNF tail).length + 1 := Nat.add_le_add_right ih 1
      _ ≤ (encodeCNF (head :: tail)).length := by
        unfold encodeCNF
        simp only [List.length_append, List.map_cons, List.foldl_cons]
        -- Apply the same transformation to both sides
        rw [foldl_List_append_nil_eq_flatten (List.map (fun c => (encodeClause c).append [false, false]) tail)]
        -- Apply the general foldl transformation
        have h_foldl_with_init : ∀ (init : List Bool) (l : List (List Bool)),
          List.foldl List.append init l = init ++ l.flatten := by
          intro init l
          induction l generalizing init with
          | nil => simp only [List.foldl_nil, List.flatten_nil, List.append_nil]
          | cons h t ih =>
            simp only [List.foldl_cons, List.flatten_cons]
            rw [ih (List.append init  h)]
            simp [List.append_assoc]
        -- Apply to the right side
        rw [h_foldl_with_init]
        -- Simplify the append operations
        simp [List.append_nil, List.length_append, List.flatten_cons]
        -- The goal is now arithmetic: prove that adding the head clause increases length by at least 1
        have h_head_nonempty : 1 ≤ ((encodeClause head).append [false, false]).length := by
          simp [List.length_append]
        linarith

-- In EGPT/Constraints.lean




/--
**Helper Lemma:** An algebraic identity for the length of `encodeCNF`.
Proves that `|encodeCNF (h::t)| = |encodeCNF t| + |encoded component for h|`.
This clean identity makes the main inductive proof trivial.
-/
lemma encodeCNF_cons_length_identity {k : ℕ} (h : Clause_EGPT k) (t : SyntacticCNF_EGPT k) :
  (encodeCNF (h :: t)).length = (encodeCNF t).length + (List.append (encodeClause h) [false, false]).length :=
by
  unfold encodeCNF
  simp only [List.map_cons, List.foldl_cons, List.length_append, List.nil_append]
  -- Use the existing helper lemma for the RHS first
  rw [foldl_List_append_nil_eq_flatten (List.map (fun c => List.append (encodeClause c) [false, false]) t)]
  -- Apply the general foldl transformation that's already proven in this file
  have h_foldl_with_init : ∀ (init : List Bool) (l : List (List Bool)),
    List.foldl List.append init l = init ++ l.flatten := by
      intro init l
      induction l generalizing init with
      | nil => simp only [List.foldl_nil, List.flatten_nil, List.append_nil]
      | cons h t ih =>
        simp only [List.foldl_cons, List.flatten_cons]
        rw [ih (List.append init h)]
        simp [List.append_assoc]
  -- The LHS has: List.foldl List.append ([].append (encodeClause h ++ [false, false])) (...)
  -- We need to simplify [].append x = x first
  have h_nil_simp : List.append [] (List.append (encodeClause h) [false, false]) = List.append (encodeClause h) [false, false] := by simp [List.nil_append]
  rw [h_nil_simp]
  rw [h_foldl_with_init (List.append (encodeClause h) [false, false]) (List.map (fun c => List.append (encodeClause c) [false, false]) t)]
  simp  [List.length_append]
  ring


/--
**Theorem: The number of clauses in a CNF is less than or equal to the
length of its canonical EGPT encoding.**
-/
theorem cnf_length_le_encoded_length {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
  cnf.length ≤ (encodeCNF cnf).length :=
by
  -- We prove this by a clean induction on the list of clauses.
  induction cnf with
  | nil =>
    -- Base Case: cnf = []. `0 ≤ |encodeCNF []|` is true.
    simp [encodeCNF]
  | cons head tail ih =>
    -- Inductive Step: Assume `|tail| ≤ |encodeCNF tail|` (this is `ih`).
    -- Prove it for `head :: tail`.
    -- Start with the length of the new list.
    calc
      (head :: tail).length
        = tail.length + 1 := by simp [List.length_cons]
    -- Apply the induction hypothesis.
      _ ≤ (encodeCNF tail).length + 1 := Nat.add_le_add_right ih 1
    -- Use our algebraic identity and the fact that each clause adds at least 1 to the length.
      _ ≤ (encodeCNF (head :: tail)).length := by
          rw [encodeCNF_cons_length_identity]
          apply Nat.add_le_add_left
          exact encoded_clause_with_sep_len_ge_one head


/-!
### Constructive Bridge Between Tableau and Canonical Form
-/
lemma length_foldl_mul
  (ys : List α) (xs : List β) :
  xs.foldl (fun acc _ => acc + ys.length) 0 = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl_cons, ih, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [Nat.mul_comm]


/--
**Helper: Length computation for single literal encoding**
-/
lemma encodeLiteral_append_false_length {k : ℕ} (l : Literal_EGPT k) :
  (List.append (encodeLiteral l) [false]).length = (encodeLiteral l).length + 1 := by
  simp [List.length_append, List.length_singleton]

/--
**Helper: foldl append distributes over length**
-/
lemma foldl_append_distributes_length {k : ℕ} (acc : List Bool) (l : Literal_EGPT k) :
  (acc.append (List.append (encodeLiteral l) [false])).length =
  acc.length + (encodeLiteral l).length + 1 := by
  simp [List.length_append, List.length_singleton]
  ring

/--
**General Helper: The length of folding our clause-encoding operation.**

This lemma is the core of the proof, proven by induction. It shows that for
any accumulator `acc` and any list of literals `c`, the length of the final
encoded list is the length of the accumulator plus the sum of the lengths of
the encodings of each literal in `c`.
-/
lemma foldl_encodeClause_op_length (acc : List Bool) (c : List (Literal_EGPT k)) :
  (c.foldl (fun acc l => acc.append ((encodeLiteral l).append [false])) acc).length
  = acc.length + (c.map (fun l => (encodeLiteral l).length + 1)).sum :=
by
  -- We prove this by induction on the list of literals `c`.
  induction c generalizing acc with
  | nil =>
    -- Base case: for an empty list, foldl returns the accumulator.
    -- The goal becomes `acc.length = acc.length + 0`.
    simp
  | cons head tail ih =>
    -- Inductive step: assume the property holds for the `tail` with any accumulator.
    -- Unfold the `foldl` for `head :: tail`.
    simp only [List.foldl_cons]
    -- Apply the induction hypothesis `ih` with the new accumulator.
    rw [ih]
    -- Unfold the map and sum on the RHS.
    simp only [List.map_cons, List.sum_cons]
    -- The goal is now an equation of sums of lengths.
    -- Use the `foldl_append_distributes_length` helper you already created
    -- (or just `List.length_append` twice).
    simp [List.length_append]
    -- The goal is now pure arithmetic, which `ring` can solve.
    ring

/--
**Key Helper: Express encodeClause length as sum**
-/
lemma encodeClause_length_as_sum {k : ℕ} (c : List (Literal_EGPT k)) :
  (encodeClause c).length = (c.map (fun l => (encodeLiteral l).length + 1)).sum :=
by
  -- Unfold the definition of encodeClause to expose the foldl.
  unfold encodeClause
  -- The main proof is now a direct application of our general helper lemma,
  -- starting with an empty accumulator `[]`.
  rw [foldl_encodeClause_op_length [] c]
  -- The goal simplifies to `0 + ... = ...`, which is true.
  simp

/--
**Lemma: The length of an encoded clause is invariant under permutations.**

This proves that `|encodeClause c|` depends only on the *set* of literals in `c`,
not their order. This is because `encodeClause`'s length is just a sum of the
lengths of the encoded literals (plus delimiters), and summation is commutative.
-/
theorem encodeClause_length_is_perm_invariant {k : ℕ} (c : Clause_EGPT k) :
  ∀ (c' : Clause_EGPT k), c.Perm c' → (encodeClause c).length = (encodeClause c').length :=
by
  intro c' h_perm
  -- Express both lengths as sums using our helper lemma
  rw [encodeClause_length_as_sum c, encodeClause_length_as_sum c']

  -- Now we have sums of mapped lists
  -- Since c and c' are permutations, their mapped versions are also permutations
  have h_map_perm : (c.map (fun l => (encodeLiteral l).length + 1)).Perm
                    (c'.map (fun l => (encodeLiteral l).length + 1)) := by
    exact List.Perm.map _ h_perm

  -- Permutations preserve sums
  exact List.Perm.sum_eq h_map_perm

-- In a new helper file or at the top of Constraints.lean

/--
**The Key Lemma to Break the Cycle**

If a function `f` "absorbs" a permutation `g` (i.e., `f x (g y) = f x y`),
then folding `f` over a list where `g` has been mapped is the same as
folding `f` over the original list.
-/
lemma foldl_of_invariant_function {α β : Type} (f : β → α → β) (g : α → α)
  (l : List α) (init : β) (h_inv : ∀ (acc : β) (y : α), f acc (g y) = f acc y) :
  (l.map g).foldl f init = l.foldl f init :=
by
  induction l generalizing init with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.foldl_cons]
    -- Apply the invariance property to the head element
    rw [h_inv]
    -- Apply the induction hypothesis to the tail with the new accumulator
    exact ih (f init head)


/--
**The Correct Key Lemma: Length invariance for foldl**

If the length of the result of a folding function `f` is the same for `y` and
for a transformed `g y` (regardless of the accumulator), then folding over
the original list `l` or the mapped list `l.map g` results in a list of
the same final length.
-/
@[simp] lemma foldl_length_eq_of_invariant_length {α γ : Type}
  (f : List γ → α → List γ) (g : α → α) (l : List α) (init : List γ)
  (h_len_inv : ∀ (acc : List γ) (y : α), (f acc (g y)).length = (f acc y).length)
  (h_f_len_ext : ∀ (acc1 acc2 : List γ) (y : α), acc1.length = acc2.length → (f acc1 y).length = (f acc2 y).length) :
  ((l.map g).foldl f init).length = (l.foldl f init).length :=
by
  -- We prove this by induction on the list `l`, generalizing the accumulator.
  induction l generalizing init with
  | nil =>
    -- Base Case: `init.length = init.length`.
    simp
  | cons head tail ih =>
    -- Inductive Step: Assume the property holds for `tail`.
    -- Unfold `foldl` on both sides of the goal.
    simp only [List.map_cons, List.foldl_cons]

    -- Goal: `(tail.map g |>.foldl f (f init (g head))).length = (tail.foldl f (f init head)).length`

    -- Step 1: Apply the induction hypothesis `ih` to the LHS of the goal.
    -- The accumulator for this recursive call is `f init (g head)`.
    rw [ih (f init (g head))]

    -- New Goal: `(tail.foldl f (f init (g head))).length = (tail.foldl f (f init head)).length`

    -- Step 2: Now we have two `foldl` expressions over the same list (`tail`).
    -- The only difference is their initial accumulators.
    -- We will prove that these two `foldl` expressions result in lists of the same
    -- length by proving that their *initial accumulators* have the same length,
    -- and that the length change from `f` is independent of the accumulator's content.

    -- First, prove the initial accumulators have the same length using our hypothesis `h_len_inv`.
    have h_acc_len_eq : (f init (g head)).length = (f init head).length := by
      exact h_len_inv init head

    -- Now, we need a general lemma about how `foldl` with our *specific* type of
    -- append function propagates length equality.
    have h_len_prop : ∀ (l' : List α) (acc1 acc2 : List γ),
        acc1.length = acc2.length →
        (l'.foldl f acc1).length = (l'.foldl f acc2).length := by
      intro l' acc1 acc2 h_acc_eq
      induction l' generalizing acc1 acc2 with
      | nil => exact h_acc_eq
      | cons h t ih_inner =>
        simp only [List.foldl_cons]
        -- The inner induction hypothesis applies to the new accumulators.
        apply ih_inner (f acc1 h) (f acc2 h)
        -- We just need to prove these new accumulators have the same length.
        exact h_f_len_ext acc1 acc2 h h_acc_eq

    -- Apply this general property to our goal.
    apply h_len_prop
    -- The proof obligation is to show our initial accumulators have the same length.
    exact h_acc_len_eq

-- In Constraints.lean or your main proof file



-- In Constraints.lean or your main proof file

-- This should go in a helper file, or at the top of Constraints.lean.

/--
**The Algebraic Bridge Lemma: `foldl List.append` length as a sum.**

This lemma provides the crucial, provable identity that transforms the length
of a `foldl` with `List.append` into a `sum` of `map`ped lengths.
-/
theorem foldl_append_length_as_sum (xss : List (List α)) :
  (xss.foldl List.append []).length = (xss.map List.length).sum :=
by
  -- We first prove a more general helper lemma
  have general : ∀ (init : List α) (xs : List (List α)),
    (xs.foldl List.append init).length = init.length + (xs.map List.length).sum := by
    intro init xs
    induction xs generalizing init with
    | nil => simp
    | cons head tail ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      -- Apply induction hypothesis to the new initial value
      have h := ih (init.append head)
      rw [h]
      -- Simplify the goal using simp which should handle List.append.length
      simp  [List.length_append]
      ring
  -- Now apply the general case with init = []
  have h := general [] xss
  rw [h]
  simp

-- Helper lemma to bridge the gap between lambda append and List.append
lemma foldl_lambda_append_eq_foldl_append (l : List (List α)) :
  List.foldl (fun x1 x2 => x1 ++ x2) [] l = List.foldl List.append [] l :=
by
  -- The functions are definitionally equal
  rfl

-- Derived lemma for lambda append to flatten
lemma foldl_lambda_append_nil_eq_flatten (l : List (List α)) :
  List.foldl (fun x1 x2 => x1 ++ x2) [] l = l.flatten :=
by
  rw [foldl_lambda_append_eq_foldl_append, foldl_List_append_nil_eq_flatten]

/--
**Theorem: Normalizing a CNF does not change its encoded length.**

This is the core efficiency proof for our `normalizeCNF` reducer. This final
version uses a clean, algebraic approach that correctly handles the data
structures to avoid the tactical errors of previous attempts.
-/
theorem encodeCNF_normalize_length_eq {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
  (encodeCNF (normalizeCNF cnf).val).length = (encodeCNF cnf).length :=
by
  -- 1. Unfold definitions to expose the core structure. A targeted `simp`
  --    handles the `normalizeCNF` subtype and `let` binding cleanly.
  simp [encodeCNF, normalizeCNF]

  -- 2. The goal is now a direct equality of two expressions containing `foldl`.
  --    Apply our key bridge lemma to transform `foldl` into `flatten` on both sides.
  rw [foldl_lambda_append_nil_eq_flatten, foldl_lambda_append_nil_eq_flatten]

  -- 3. Now the goal is about `flatten.length`. Use the fact that `flatten.length = sum (map length)`.
  rw [List.length_flatten, List.length_flatten]

  -- 5. The goal is now an equality of two sums of mapped lists.
  --    Use `List.map_map` to simplify the nested maps on the LHS.
  simp_rw [List.map_map]

  -- 6. Prove the sums are equal by proving the lists being summed are identical.
  apply congr_arg List.sum

  -- 7. Prove the lists are equal element-wise using function extensionality.
  congr 1
  ext c
  -- Now we need to prove the functions are equal for each element
  -- The current goal should be about the composed functions being equal on each element
  -- Goal: (List.length ∘ (fun c => encodeClause c ++ [false, false]) ∘ fun c => List.mergeSort c literal_le_bool) c =
  --       (List.length ∘ fun c => encodeClause c ++ [false, false]) c
  simp only [Function.comp_apply]
  -- This should give us: List.length (encodeClause (List.mergeSort c literal_le_bool) ++ [false, false]) =
  --                      List.length (encodeClause c ++ [false, false])
  rw [List.length_append, List.length_append]
  -- This reduces to: List.length (encodeClause (List.mergeSort c literal_le_bool)) + 2 =
  --                  List.length (encodeClause c) + 2
  congr 1
  -- Now the goal is: List.length (encodeClause (List.mergeSort c literal_le_bool)) = List.length (encodeClause c)
  apply encodeClause_length_is_perm_invariant
  exact List.mergeSort_perm c _
