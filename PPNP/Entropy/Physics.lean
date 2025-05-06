import Mathlib.Data.Fin.Basic -- Basic Fin definitions and lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Fintype.Card -- Fintype.card, Fintype.ofEquiv, Fintype.card_congr
import Mathlib.Data.Sym.Card -- Sym.card_sym_eq_multichoose
import Mathlib.Data.Nat.Choose.Basic -- Nat.choose, Nat.multichoose_eq, Nat.choose_pos
import Mathlib.Data.NNReal.Basic -- For NNReal
import Mathlib.Logic.Equiv.Fintype -- Fintype.equivFin
import Mathlib.Data.Fintype.Basic -- Fintype instances
import Mathlib.Data.Finset.Basic -- Finset.univ, Finset.mem_univ
import Mathlib.Data.Multiset.Fintype -- Fintype instance for Sym (Fin N) M
import Mathlib.Tactic.Positivity -- positivity tactic
import Mathlib.Algebra.Group.Defs -- nsmul_eq_mul (implicitly used or needed)
import Mathlib.Analysis.SpecialFunctions.Log.Basic -- Real.log for final entropy calculation
namespace PPNP.Entropy.Physics

open BigOperators Multiset Finset

-- Define the type for Macrostates (occupancy vectors summing to M)
-- Needed for both MB and BE state space definitions
def MBMacrostate (N M : ℕ) := { q : Fin N → ℕ // ∑ i, q i = M }


/-- `Multiset.count` distributes over a `Finset` sum of multisets. -/
@[simp] lemma Multiset.count_finset_sum
    {α β : Type*} [DecidableEq α] {s : Finset β} (f : β → Multiset α) (a : α) :
    Multiset.count a (∑ i in s, f i) = ∑ i in s, Multiset.count a (f i) := by
  classical
  -- We proceed by induction on the structure of `s`.
  refine Finset.induction ?base ?step s
  · -- base case: `s = ∅`
    simp
  · -- inductive step: `s = insert b s'` with `b ∉ s'`
    intro b s' hb_not_mem ih
    simp [Finset.sum_insert hb_not_mem, Multiset.count_add, ih]

-- BE state space is mathematically equivalent to MB macrostates
@[reducible] def OmegaBE (N M : ℕ) := MBMacrostate N M

-- Map a BE state (occupancy vector) to the corresponding multiset of occupied states
-- Example: N=3, M=4, q = (i=0 ↦ 2, i=1 ↦ 1, i=2 ↦ 1) -> {0, 0, 1, 2}
def beStateToMultiset {N M : ℕ} (q : OmegaBE N M) : Multiset (Fin N) :=
  Finset.univ.sum (fun i => replicate (q.val i) i)

-- First provable lemma: The card of the generated multiset is M
lemma card_beStateToMultiset {N M : ℕ} (q : OmegaBE N M) :
    Multiset.card (beStateToMultiset q) = M := by
  -- Unfold the definition of the map
  simp only [beStateToMultiset]
  -- Use the property that card distributes over sum of multisets
  rw [Multiset.card_sum]
  -- Use the property that card of (replicate k a) is k
  simp_rw [Multiset.card_replicate]
  -- The remaining goal is ∑ i in Finset.univ, q.val i = M,
  -- which is exactly the property bundled in the OmegaBE subtype.
  exact q.property

-- Define the map from a multiset of states to an occupancy vector function
-- Example: {0, 0, 1, 2} -> (i=0 ↦ 2, i=1 ↦ 1, i=2 ↦ 1)
def multisetToBEState {N : ℕ} (s : Multiset (Fin N)) : Fin N → ℕ :=
  fun i => Multiset.count i s

lemma sum_count_eq_card {N : ℕ} (s : Multiset (Fin N)) :
    ∑ i : Fin N, Multiset.count i s = Multiset.card s := by
  -- instantiate the library lemma with `s = Finset.univ`
  have hms : ∀ a ∈ s, (a : Fin N) ∈ (Finset.univ : Finset (Fin N)) := by
    intro a ha
    exact Finset.mem_univ _
  -- The goal is definitionally equal to the statement of Multiset.sum_count_eq_card
  exact (Multiset.sum_count_eq_card (s := (Finset.univ : Finset (Fin N))) (m := s) hms)

-- Define the type for multisets of size M over Fin N
-- This uses the standard Mathlib definition `Sym α n := {s : Multiset α // card s = n}`
@[reducible] def SymFin (N M : ℕ) := Sym (Fin N) M


/-!
Helper lemma for `left_inv_beState_multiset`.
Shows that counting element `i` in a multiset created by replicating element `j`
yields zero if `i` and `j` are different.
-/
lemma count_replicate_term_zero {N : ℕ} {q : Fin N → ℕ} (i j : Fin N) (hij : i ≠ j) :
    Multiset.count i (Multiset.replicate (q j) j) = 0 := by
  -- Apply the general lemma for counting in a replicated multiset and simplify using hij
  -- We use Ne.symm hij to match the condition `j = i` in `Multiset.count_replicate`.
  simp [Multiset.count_replicate, Ne.symm hij]

/-!
Helper lemma for `left_inv_beState_multiset`.
Shows that counting element `i` in a multiset created by replicating `i` itself
yields the number of replications.
-/
lemma count_replicate_term_eq {N : ℕ} {q : Fin N → ℕ} (i : Fin N) :
    Multiset.count i (Multiset.replicate (q i) i) = q i := by
  -- Apply the specific Mathlib lemma for counting the replicated element itself
  rw [Multiset.count_replicate_self]

/-!
Helper lemma for `left_inv_beState_multiset`.
Shows that the sum of counts over all `j` simplifies to the single term where `j = i`.
-/
lemma sum_count_replicate_eq_single_term {N : ℕ} {q : Fin N → ℕ} (i : Fin N) :
    ∑ j in Finset.univ, Multiset.count i (Multiset.replicate (q j) j) = q i := by
  -- Use Finset.sum_eq_single to isolate the term where j = i
  -- We need to provide:
  -- 1. The index `a` we want to single out (which is `i`).
  -- 2. Proof that for all other indices `b` in the set (`j ∈ Finset.univ`), if `b ≠ a` (`j ≠ i`), the term `f b` is zero.
  -- 3. Proof that if `a` is *not* in the set, then `f a` is zero (this is usually handled by `simp` or trivial for `Finset.univ`).
  rw [Finset.sum_eq_single i]
  -- Prove the main goal after simplification: f i = q i
  · -- The term f i is `Multiset.count i (Multiset.replicate (q i) i)`
    -- Use the previous lemma `count_replicate_term_eq`
    exact count_replicate_term_eq i
  -- Prove side condition 1: ∀ j ∈ Finset.univ, j ≠ i → f j = 0
  · intro j _ hij_ne -- Assume j ∈ Finset.univ and j ≠ i
    -- The term f j is `Multiset.count i (Multiset.replicate (q j) j)`
    -- Use the first lemma `count_replicate_term_zero` with the hypothesis hij_ne
    -- We need Ne.symm because count_replicate_term_zero expects i ≠ j, but hij_ne is j ≠ i.
    exact count_replicate_term_zero i j (Ne.symm hij_ne)
  -- Prove side condition 2: i ∉ Finset.univ → f i = 0
  · intro h_not_mem -- Assume i is not in Finset.univ
    -- This case is impossible for `Fin N` as `i` is always in `Finset.univ`.
    -- `simp` should resolve this, as `i ∈ Finset.univ` is true.
    simp only [Finset.mem_univ, not_true_eq_false] at h_not_mem
    -- Alternatively, directly use the fact that i is always in univ.
    --have : i ∈ Finset.univ := Finset.mem_univ i
    --contradiction -- The assumption h_not_mem contradicts this fact.

-- Make sure this or an equivalent Mathlib lemma is available/imported
-- @[simp] lemma Multiset.count_finset_sum ... (from previous interaction)

/-!
Helper lemma for `left_inv_beState_multiset`.
Applies the distributivity of `Multiset.count` over `Finset.sum`
to the definition of `beStateToMultiset`.
-/
lemma count_beStateToMultiset_eq_sum_count_replicate {N M : ℕ} (q : OmegaBE N M) (i : Fin N) :
    Multiset.count i (beStateToMultiset q) =
      ∑ j in Finset.univ, Multiset.count i (Multiset.replicate (q.val j) j) := by
  -- Unfold the definition of beStateToMultiset
  simp only [beStateToMultiset]
  -- Goal: count i (∑ j in Finset.univ, Multiset.replicate (q.val j) j) = ...
  -- Apply the lemma that distributes count over finset sum
  -- (Assuming the lemma Multiset.count_finset_sum provided earlier or similar exists)
  rw [Multiset.count_finset_sum]
  -- The goal should now be definitionally equal, so rfl or simp closes it.

end PPNP.Entropy.Physics
