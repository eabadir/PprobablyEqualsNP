import Mathlib.Data.Fin.Basic -- Basic Fin definitions and lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Multiset.Defs

namespace PPNP.Entropy.Physics

open BigOperators Multiset Finset

-- Define the type for Macrostates (occupancy vectors summing to M)
-- Needed for both MB and BE state space definitions
def MBMacrostate (N M : ℕ) := { q : Fin N → ℕ // ∑ i, q i = M }

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

-- Define the map from a multiset known to have card M back to a BE state
-- This bundles the function `multisetToBEState` with the proof that its components sum to M
def multisetToBEStateSubtype {N M : ℕ} (s : SymFin N M) : OmegaBE N M :=
  ⟨ multisetToBEState s.val , -- The function (Fin N → ℕ)
    by
      -- Proof that the sum is M:
      have h_sum := sum_count_eq_card s.val -- ∑ (count i s.val) = card s.val
      simp only [multisetToBEState] -- Unfold definition in the goal
      -- Goal is now ∑ i, count i ↑s = M
      rw [h_sum] -- Rewrite using the sum_count_eq_card lemma result
      -- Goal is now card s.val = M
      exact s.property -- The property bundled with s is card s.val = M
  ⟩

-- Lemma: `beStateToMultiset` and `multisetToBEStateSubtype` are inverses (left inverse)
lemma left_inv_beState_multiset {N M : ℕ} (q : OmegaBE N M) :
    multisetToBEStateSubtype ⟨beStateToMultiset q, card_beStateToMultiset q⟩ = q := by
  -- To prove equality of subtypes, prove equality of their value parts
  apply Subtype.eq
  -- Goal: (multisetToBEStateSubtype ⟨...⟩).val = q.val
  -- Unfold the value part of multisetToBEStateSubtype
  simp only [multisetToBEStateSubtype]
  -- Goal: multisetToBEState (Subtype.val ⟨...⟩) = q.val
  -- Simplify the Subtype.val call
  simp only [Subtype.val_eq_coe]
  -- Goal: multisetToBEState (beStateToMultiset q) = q.val
  -- Now unfold multisetToBEState pointwise
  funext i -- Prove for arbitrary i: Fin N
  -- Goal: multisetToBEState (beStateToMultiset q) i = q.val i
  simp only [multisetToBEState]
  -- Goal: Multiset.count i (beStateToMultiset q) = q.val i
  -- Unfold beStateToMultiset (use simp, not rw)
  simp only [beStateToMultiset] -- Goal: count i (Finset.univ.sum (fun j => replicate ...)) = q.val i
  -- Use Multiset.count_sum to distribute count over the sum
  rw [Multiset.count_sum] -- Goal: ∑ j in Finset.univ, count i (replicate (q.val j) j) = q.val i
  -- Simplify the sum using the property of count_replicate
  -- count i (replicate k a) = k if i = a, else 0
  rw [Finset.sum_eq_single i] -- Reduce sum to the term where j = i
  · -- Prove the term is correct: count i (replicate (q.val i) i) = q.val i
    rw [Multiset.count_replicate_self]
  · -- Prove other terms are zero: ∀ j ≠ i, count i (replicate (q.val j) j) = 0
    intro j _ hj_ne_i -- hj_ne_i : j ≠ i
    rw [Multiset.count_replicate] -- Goal is now: ite (i = j) (q.val j) 0 = 0
    -- Use if_neg to simplify the ite, requires ¬(i = j)
    apply if_neg
    -- Prove ¬(i = j) from j ≠ i
    symm -- Change goal to ¬(j = i)
    exact Ne.symm hj_ne_i -- Use the hypothesis j ≠ i
  · -- Prove i is always in Finset.univ
    intro _hia -- Case where i is not in univ (impossible for Fin N)
    exact Finset.mem_univ i

end PPNP.Entropy.Physics
