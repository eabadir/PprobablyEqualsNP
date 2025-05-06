import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog -- For negMulLog, Real.log
import Mathlib.Data.NNReal.Basic -- For NNReal
import Mathlib.Topology.Basic -- For ContinuousOn (placeholder)
import Mathlib.Order.Monotone.Basic -- For Monotone
import Mathlib.Algebra.BigOperators.Fin -- For sum over Fin n
import Mathlib.Data.Fin.Basic -- Basic Fin definitions and lemmas
import Mathlib.Data.Fintype.Fin -- Instances for Fin n
import Mathlib.Algebra.Order.Field.Basic -- For inv_one etc.
import Mathlib.Algebra.GroupWithZero.Units.Basic -- Provides mul_inv_cancel₀
import Mathlib.Analysis.SpecialFunctions.Log.Base -- Real.logb
import Mathlib.Analysis.SpecialFunctions.Pow.Real -- Real.rpow
import Mathlib.Data.Complex.Basic -- For Complex.exp_re if needed
import Mathlib.Analysis.SpecificLimits.Basic -- tendsto_one_div_atTop_zero
import Mathlib.Data.Real.Basic -- Basic Real properties
import Mathlib.Order.Filter.Basic -- Filter bases etc.
import Mathlib.Topology.Order.Basic -- OrderTopology
import Mathlib.Data.Nat.Basic -- Basic Nat properties
import Mathlib.Data.Nat.Log -- Nat.log
import Mathlib.Algebra.Order.Floor.Defs -- Floor definitions
import Mathlib.Tactic.Linarith -- Inequality solver
import Mathlib.Algebra.Ring.Nat -- For Nat.cast_pow
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.GroupTheory.Congruence.Basic

import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- Import previous definitions and theorems
import PPNP.Util.Basic
import PPNP.Entropy.RET
import PPNP.Entropy.Physics

namespace PPNP.Entropy

open BigOperators Fin Real Topology NNReal Filter Nat Set

open PPNP.Util
open PPNP.Entropy.RET
open PPNP.Entropy.Physics

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

-- Make sure the above lemma (or its equivalent) is available before the proof below.

/-!
Helper lemma for `right_inv_beState_multiset`.
Shows that if element `i` is not in multiset `s`, replicating `i` by its count in `s` (which is 0)
results in the empty multiset `0`.
-/
lemma replicate_count_zero_of_not_mem {α : Type*} [DecidableEq α] {s : Multiset α} {i : α} (hi_not_mem : i ∉ s) :
    Multiset.replicate (Multiset.count i s) i = 0 := by
  -- Use the property that `i ∉ s` is equivalent to `count i s = 0`
  have h_count_eq_zero : Multiset.count i s = 0 := Multiset.count_eq_zero.mpr hi_not_mem
  -- Rewrite the count in the goal using this fact
  rw [h_count_eq_zero]
  -- Apply the definition of replicate with count 0
  rw [Multiset.replicate_zero]

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


/-!
Lemma: `beStateToMultiset` and `multisetToBEStateSubtype` are inverses (left inverse).
This proof uses the previously defined micro-lemmas.
-/
lemma left_inv_beState_multiset {N M : ℕ} (q : OmegaBE N M) :
    multisetToBEStateSubtype ⟨beStateToMultiset q, card_beStateToMultiset q⟩ = q := by
  apply Subtype.ext
  -- Instead of using `simp only [multisetToBEStateSubtype, Subtype.mk_val]`,
  -- we use dsimp to reveal the underlying definition.
  dsimp [multisetToBEStateSubtype]
  -- Now the goal is: multisetToBEState (beStateToMultiset q) = q.val
  funext i
  simp only [multisetToBEState]
  rw [count_beStateToMultiset_eq_sum_count_replicate]
  rw [sum_count_replicate_eq_single_term]
  -- Goal: q.val i = q.val i, which holds.


/-!
Helper lemma for `right_inv_beState_multiset`.
Shows that summing the `replicate (count i s) i` terms over `univ`
equals the sum over just the elements present in the multiset `s` (`s.toFinset`),
because terms for elements not in `s` are the empty multiset (zero).
Uses Finset.sum_subset focusing on the required zero condition.
-/

lemma sum_replicate_count_univ_eq_sum_toFinset {α : Type*} [DecidableEq α] (s : Multiset α) (univ : Finset α) (h_univ : ∀ x : α, x ∈ univ) :
    ∑ i in univ, Multiset.replicate (Multiset.count i s) i = ∑ i in s.toFinset, Multiset.replicate (Multiset.count i s) i := by
  -- Use symmetry to match the structure of Finset.sum_subset conclusion: ∑ s = ∑ t
  apply Eq.symm
  -- Goal: ∑ i in s.toFinset, replicate... = ∑ i in univ, replicate...

  -- Apply Finset.sum_subset {s t} (h_sub : s ⊆ t) (h_zero : ∀ x ∈ t, x ∉ s → f x = 0) : ∑ x in s, f x = ∑ x in t, f x
  apply Finset.sum_subset
  · -- Goal 1: Prove s ⊆ t, i.e., s.toFinset ⊆ univ
    intro x _hx_mem_toFinset -- Assume x ∈ s.toFinset
    -- Prove x ∈ univ using the hypothesis h_univ
    exact h_univ x
  · -- Goal 2: Prove ∀ x ∈ t, x ∉ s → f x = 0
    -- i.e., ∀ x ∈ univ, x ∉ s.toFinset → replicate (count x s) x = 0
    intro x _hx_in_univ hx_not_in_s_toFinset -- Assume x ∈ univ and x ∉ s.toFinset

    -- Derive `x ∉ s` from `x ∉ s.toFinset` explicitly
    have hx_not_mem_s : x ∉ s := by
      -- Multiset.mem_toFinset is an iff `a ∈ s.toFinset ↔ a ∈ s`
      -- We can use its negation. `mt` (modus tollens) might work, or prove by contradiction.
      contrapose! hx_not_in_s_toFinset -- Changes goal to proving `x ∈ s.toFinset` from `x ∈ s`
      rwa [Multiset.mem_toFinset] -- Apply the iff lemma

    -- Apply the lemma showing replicate count is zero when element is not present, using the derived `x ∉ s`
    exact replicate_count_zero_of_not_mem hx_not_mem_s

@[simp] lemma toFinset_cons
    {α} [DecidableEq α] (a : α) (s : Multiset α) :
  (a ::ₘ s).toFinset = insert a s.toFinset := by
  -- `rw [Multiset.toFinset_cons]` is a simp lemma  :contentReference[oaicite:8]{index=8}
  simp

@[simp] lemma count_cons_self
    {α} [DecidableEq α] (a : α) (s : Multiset α) :
  Multiset.count a (a ::ₘ s) = Multiset.count a s + 1 := by
  exact Multiset.count_cons_self a s

lemma count_cons_ne
    {α} [DecidableEq α] {a i : α} (h : i ≠ a) (s : Multiset α) :
  Multiset.count i (a ::ₘ s) = Multiset.count i s := by
  exact Multiset.count_cons_of_ne h s  -- Directly apply the lemma

lemma replicate_split {α} (n : ℕ) (a : α) :
    Multiset.replicate (n + 1) a =
      Multiset.replicate 1 a + Multiset.replicate n a := by
  rw [Nat.add_comm] -- Goal: replicate (1 + n) a = replicate 1 a + replicate n a
  exact Multiset.replicate_add 1 n a -- Apply the standard lemma
  -- `replicate_add`

lemma sum_congr_count
    {β} [AddCommMonoid β] {α} [DecidableEq α]
    {s : Finset α} {f g : α → β}
    (hfg : ∀ i ∈ s, f i = g i) :
  (∑ i in s, f i) = ∑ i in s, g i :=
by
  -- zipper lemma  `Finset.sum_congr`  :contentReference[oaicite:13]{index=13}
  simpa using Finset.sum_congr rfl hfg

@[simp] lemma sum_replicate_count_nil
    {α} [DecidableEq α] :
  (∑ i : α in (0 : Multiset α).toFinset,
      Multiset.replicate (Multiset.count i (0 : Multiset α)) i) = (0 : Multiset α) :=
by simp

/-! ## Micro–micro lemmas for the “`a ∈ s`” branch -/

/-- 2.6 (a).  Split the sum over `insert a t` into the
    part without `a` plus the `i = a` summand. -/
lemma sum_insert_split
    {α β} [DecidableEq α] [AddCommMonoid β]
    {a : α} {t : Finset α} (f : α → β) (ha : a ∈ insert a t) :
  (∑ i in insert a t, f i)
    = (∑ i in (insert a t).erase a, f i) + f a :=
by
  -- Apply the lemma that splits the sum
  rw [Finset.sum_eq_sum_diff_singleton_add ha f]
  -- The goal might now be `∑ i in insert a t \ {a}, f i + f a = ∑ i in (insert a t).erase a, f i + f a`
  -- We need to show `insert a t \ {a}` is the same as `(insert a t).erase a`
  -- This should hold definitionally or via a simp lemma like Finset.sdiff_singleton_eq_erase
  -- Let's try simp first, as it might handle this.
  simp only [Finset.sdiff_singleton_eq_erase]
  -- If simp worked, the goal is now trivial (α = α).

/-- 2.6 (b).  `count` for every *other* element is unchanged
    after consing `a`. -/
lemma count_cons_ne'
    {α} [DecidableEq α] {a i : α} (h : i ≠ a) {s : Multiset α} :
  Multiset.count i (a ::ₘ s) = Multiset.count i s :=
by
  --simpa [h] using Multiset.count_cons_of_ne h _   -- already proven in § 2.3
  exact count_cons_ne h s

/-- 2.6 (c).  `replicate` respects (b). -/
lemma replicate_cons_ne'
    {α} [DecidableEq α] {a i : α} (h : i ≠ a) {s : Multiset α} :
  Multiset.replicate (Multiset.count i (a ::ₘ s)) i =
    Multiset.replicate (Multiset.count i s) i :=
by
  simp [count_cons_ne' h]

/-- 2.6 (d).  Rewrite the *tail* of the split sum
    using (c).  -/
lemma tail_sum_cons
    {α} [DecidableEq α] {a : α} {s : Multiset α} :
  (∑ i in (insert a s.toFinset).erase a,
      Multiset.replicate (Multiset.count i (a ::ₘ s)) i)
    =
  (∑ i in s.toFinset.erase a,
      Multiset.replicate (Multiset.count i s) i) :=
by
  -- First, show the summation domains are equal
  rw [Finset.erase_insert_eq_erase]
  -- Now the goal is:
  -- ∑ i in s.toFinset.erase a, Multiset.replicate (Multiset.count i (a ::ₘ s)) i =
  --   ∑ i in s.toFinset.erase a, Multiset.replicate (Multiset.count i s) i
  -- Apply the sum congruence lemma (using Finset.sum_congr directly is often clearer)
  apply Finset.sum_congr rfl -- The domains now match (rfl), need to prove equality of terms
  intro i hi
  -- `i ∈ s.toFinset.erase a` implies `i ≠ a` and `i ∈ s.toFinset`
  simp only [Finset.mem_erase] at hi
  -- hi is now a pair: ⟨i ≠ a, i ∈ s.toFinset⟩
  have hia : i ≠ a := hi.1 -- Corrected: Use hi.1 for the inequality
  -- Use replicate_cons_ne' which requires i ≠ a
  simp [replicate_cons_ne' hia]

/-- 2.6 (e).  The *head* replicate for `a`. -/
lemma head_replicate_cons
    {α} [DecidableEq α] {a : α} {s : Multiset α} :
  Multiset.replicate (Multiset.count a (a ::ₘ s)) a =
    Multiset.replicate 1 a + Multiset.replicate (Multiset.count a s) a :=
by
  simp [count_cons_self, replicate_split]

variable {α β : Type*} [DecidableEq α] [AddCommMonoid β]


lemma sum_eq_add_sum_erase {s : Finset α} {a : α} (f : α → β) (h : a ∈ s) :
  ∑ x in s, f x = f a + ∑ x in s.erase a, f x :=
by
   rw [←Finset.sum_insert (Finset.not_mem_erase a s)]
   congr
   exact Eq.symm (Finset.insert_erase h)


/-- Final streamlined version of the “`a ∈ s`” inductive step. -/
lemma step_mem
    {α} [DecidableEq α] {a : α} {s : Multiset α}
    (hmem : a ∈ s.toFinset)
    (IH : ∑ i ∈ s.toFinset, Multiset.replicate (Multiset.count i s) i = s) :
  ∑ i ∈ insert a s.toFinset, Multiset.replicate (Multiset.count i (a ::ₘ s)) i
      = a ::ₘ s := by
  -- 1.  Since `a ∈ s.toFinset`, `insert` does nothing.
  have h_insert : insert a s.toFinset = s.toFinset :=
    Finset.insert_eq_of_mem hmem
  simp [h_insert] at IH ⊢                           -- rewrites the goal & IH

-- 2.  Split the sum into the `i = a` part and the tail.
  have h_split :
      (∑ i ∈ s.toFinset, Multiset.replicate (Multiset.count i (a ::ₘ s)) i) =
        Multiset.replicate (Multiset.count a (a ::ₘ s)) a +
        ∑ i ∈ s.toFinset.erase a,
            Multiset.replicate (Multiset.count i (a ::ₘ s)) i := by
    -- Apply the lemma directly, providing the function first, then the membership proof
    exact sum_eq_add_sum_erase
            (fun i ↦ Multiset.replicate (Multiset.count i (a ::ₘ s)) i)
            hmem

  -- 3.  The tail counts are unchanged when `i ≠ a`.
  have h_tail :
      ∑ i ∈ s.toFinset.erase a,
          Multiset.replicate (Multiset.count i (a ::ₘ s)) i =
      ∑ i ∈ s.toFinset.erase a,
          Multiset.replicate (Multiset.count i s) i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_ne : i ≠ a := (Finset.mem_erase.1 hi).1
    simp [Multiset.count_cons_of_ne hi_ne]          -- counts coincide

  -- 4.  The head term adds exactly one copy of `a`.
  have h_head :
      Multiset.replicate (Multiset.count a (a ::ₘ s)) a =
        {a} + Multiset.replicate (Multiset.count a s) a := by
    simp [Multiset.count_cons_self, replicate_split]

-- 5.  Assemble:  `lhs = {a} + (∑ over s)` and use the induction hypothesis.
  calc
    (∑ i ∈ s.toFinset, Multiset.replicate (Multiset.count i (a ::ₘ s)) i)
        = {a} + ∑ i ∈ s.toFinset,
            Multiset.replicate (Multiset.count i s) i := by
          rw [h_split]
          rw [h_head]
          rw [h_tail]
          rw [Multiset.add_assoc]
          rw [←sum_eq_add_sum_erase (fun i ↦ Multiset.replicate (Multiset.count i s) i) hmem]
    _ = {a} + s := by
          simp only [IH] -- Changed simpa to simp only
    _ = a ::ₘ s := by
          simp only [Multiset.singleton_add] -- Changed simpa to simp only
