import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog -- For negMulLog, Real.log
import Mathlib.Algebra.BigOperators.Fin -- For sum over Fin n
import Mathlib.Data.Fin.Basic -- Basic Fin definitions and lemmas
import Mathlib.Data.Fintype.Fin -- Instances for Fin n
import Mathlib.Algebra.GroupWithZero.Units.Basic -- Provides mul_inv_cancel₀
import Mathlib.Data.Nat.Basic -- Basic Nat properties

import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PPNP.Common.Basic
import PPNP.Entropy.Physics.Common

namespace PPNP.Entropy.Physics.BE

open BigOperators Multiset Finset
open PPNP.Common
open PPNP.Entropy.Physics.Common

/-! # Formalizing Physics Distributions Starting with Bose-Einstein Statistics

## Three Disjoint Constraint Cases Describe All Physical Systems
Let (N) boxes (states) and (M) balls (particles). A microstate is a way of allocating the (M) balls among the (N) boxes. There are exactly three—and only three—constraint families on how balls may occupy boxes. As further explained in accompanying documentation: Maxwell-Boltzmann (MB) is the distinguishable balls case with no limit to box capacity, Fermi-Dirac (FD) is indistinguishable balls with at most one ball per box, and Bose-Einstein (BE) is indistinguishable balls with no limit to the balls per box.

This file aims to formally define the state space and probability distribution for Bose-Einstein (BE) statistics within the Lean 4 theorem prover, leveraging the Mathlib4 library. The ultimate goal is to apply the previously proven Rota's Entropy Theorem (RET) to this distribution.

Formalizing concepts from statistical mechanics requires careful handling of combinatorial structures, type theory, and proof details. To manage this complexity effectively and ensure correctness, we employ a **four-phased approach**:

1.  **Phase 1: Combinatorial Equivalence:** Establish the fundamental combinatorial structure. We define the BE state space (`OmegaBE`, based on occupancy numbers) and show it's mathematically equivalent (via a Lean `Equiv`) to a standard combinatorial object: multisets of a fixed size (`SymFin`). This grounds the specific physical concept in a well-understood mathematical structure within Mathlib.
2.  **Phase 2: Cardinality and Iteration:** Determine the size of the BE state space using the equivalence established in Phase 1 and known results for multisets (the "stars and bars" formula, yielding binomial coefficients). We also formally declare `OmegaBE` as a `Fintype`, enabling iteration and summation over all possible BE states, which is crucial for defining probabilities.
3.  **Phase 3: Probability Distribution:** Define the BE probability distribution (`p_BE`) assuming equiprobability of microstates (which corresponds to a uniform distribution over `OmegaBE`). Prove that this distribution is valid by showing the probabilities sum to 1 (normalization).
4.  **Phase 4: RET Application:** Connect the formalized BE distribution to the framework of Rota's Entropy Theorem. This involves potentially adapting the type of our distribution (`p_BE_fin`) and then applying the main theorem (`H_BE_eq_C_shannon`) to conclude that any valid entropy function `H` applied to `p_BE` is proportional to the standard Shannon entropy.
5. **Phase 5: Generalization:** Extend the results to other distributions (e.g., Maxwell-Boltzmann) and explore the implications of Rota's theorem in this context.

-/

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
    ∑ i ∈ univ, Multiset.replicate (Multiset.count i s) i = ∑ i ∈ s.toFinset, Multiset.replicate (Multiset.count i s) i := by
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

/-! ## Micro–micro lemmas for the “`a ∈ s`” branch -/

/-- 2.6 (a).  Split the sum over `insert a t` into the
    part without `a` plus the `i = a` summand. -/
lemma sum_insert_split
    {α β} [DecidableEq α] [AddCommMonoid β]
    {a : α} {t : Finset α} (f : α → β) (ha : a ∈ insert a t) :
  (∑ i ∈ insert a t, f i)
    = (∑ i ∈ (insert a t).erase a, f i) + f a :=
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
  (∑ i ∈ (insert a s.toFinset).erase a,
      Multiset.replicate (Multiset.count i (a ::ₘ s)) i)
    =
  (∑ i ∈ s.toFinset.erase a,
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
  simp [Multiset.count_cons_self, replicate_split]

variable {α β : Type*} [DecidableEq α] [AddCommMonoid β]


lemma sum_eq_add_sum_erase {s : Finset α} {a : α} (f : α → β) (h : a ∈ s) :
  ∑ x ∈ s, f x = f a + ∑ x ∈ s.erase a, f x :=
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

/-! ## Micro–micro lemmas for the “`a ∉ s`” branch -/

/-- 2.6 (g).  When `a ∉ s`, its count in `s` is zero. -/
lemma count_not_mem_zero
    {α} [DecidableEq α] {a : α} {s : Multiset α} (h_not_mem : a ∉ s) :
  Multiset.count a s = 0 :=
by
  -- Apply the relevant direction of the iff lemma `Multiset.count_eq_zero`
  exact Multiset.count_eq_zero.mpr h_not_mem

/-- 2.6 (h).  The head replicate collapses to `{a}` if `a ∉ s`. -/
lemma head_replicate_not_mem
    {α} [DecidableEq α] {a : α} {s : Multiset α} (h_not_mem : a ∉ s) :
  Multiset.replicate (Multiset.count a (a ::ₘ s)) a = {a} :=
by
  -- Use count_cons_self: count a (a ::ₘ s) = count a s + 1
  rw [Multiset.count_cons_self]
  -- Use count_not_mem_zero: count a s = 0 since a ∉ s
  rw [count_not_mem_zero h_not_mem]
  -- Simplify the expression: replicate (0 + 1) a = replicate 1 a
  simp only [Nat.zero_add]
  -- Use replicate_one: replicate 1 a = {a}
  rw [Multiset.replicate_one] -- Use the standard Mathlib lemma

/-- 2.6 (i).  Tail sum unchanged when `a ∉ s`. -/
lemma tail_sum_not_mem
    {α} [DecidableEq α] {a : α} {s : Multiset α} (h_not_mem : a ∉ s) :
  (∑ i ∈ s.toFinset,
      Multiset.replicate (Multiset.count i (a ::ₘ s)) i) =
  (∑ i ∈ s.toFinset,
      Multiset.replicate (Multiset.count i s) i) :=
by
  -- Apply sum congruence: need to show terms are equal for i ∈ s.toFinset
  apply Finset.sum_congr rfl -- Domains are the same (rfl)
  intro i hi_mem_finset -- Assume i ∈ s.toFinset (renamed for clarity)
  -- Need to show: replicate (count i (a ::ₘ s)) i = replicate (count i s) i
  -- This holds if i ≠ a. We need to prove i ≠ a from i ∈ s.toFinset and a ∉ s.
  have hi_ne_a : i ≠ a := by
    intro h_eq -- Assume i = a for contradiction
    subst h_eq -- Substitute a for i
    -- Now hi_mem_finset is a hypothesis: a ∈ s.toFinset
    -- We also have the main lemma hypothesis h_not_mem: a ∉ s
    -- Use Multiset.mem_toFinset to show a ∈ s.toFinset implies a ∈ s
    rw [Multiset.mem_toFinset] at hi_mem_finset -- Now hi_mem_finset is: a ∈ s
    -- This contradicts the hypothesis h_not_mem (a ∉ s).
    exact h_not_mem hi_mem_finset
  -- Now apply replicate_cons_ne' which requires i ≠ a
  rw [replicate_cons_ne' hi_ne_a] -- Uses lemma 2.6(c)


/-- 2.6 (j).  Assemble the pieces for `a ∉ s`. -/
lemma step_not_mem
    {α} [DecidableEq α] {a : α} {s : Multiset α}
    (h_not_mem_finset : a ∉ s.toFinset)
    (IH : ∑ i ∈ s.toFinset, Multiset.replicate (Multiset.count i s) i = s) :
  ∑ i ∈ insert a s.toFinset,
      Multiset.replicate (Multiset.count i (a ::ₘ s)) i = a ::ₘ s :=
by
  -- 1. Derive `a ∉ s` from `a ∉ s.toFinset`
  have h_not_mem : a ∉ s := by
    -- `a ∈ s.toFinset ↔ a ∈ s`. We prove the contrapositive.
    contrapose! h_not_mem_finset -- Goal: a ∈ s → a ∈ s.toFinset
    rwa [Multiset.mem_toFinset] -- Apply the iff lemma

  -- 2. Split the sum over `insert a s.toFinset` using `Finset.sum_insert`
  --    Requires `a ∉ s.toFinset`, which is given by `h_not_mem_finset`.
  rw [Finset.sum_insert h_not_mem_finset]
  -- Goal: f a + ∑ i ∈ s.toFinset, f i = a ::ₘ s
  -- where f i = Multiset.replicate (Multiset.count i (a ::ₘ s)) i

  -- 3. Rewrite the head term `f a` using `head_replicate_not_mem`
  --    Requires `a ∉ s`, which we proved as `h_not_mem`.
  rw [head_replicate_not_mem h_not_mem]
  -- Goal: {a} + ∑ i ∈ s.toFinset, f i = a ::ₘ s

  -- 4. Rewrite the sum term `∑ i ∈ s.toFinset, f i` using `tail_sum_not_mem`
  --    Requires `a ∉ s`, which we proved as `h_not_mem`.
  rw [tail_sum_not_mem h_not_mem]
  -- Goal: {a} + ∑ i ∈ s.toFinset, Multiset.replicate (Multiset.count i s) i = a ::ₘ s

  -- 5. Apply the induction hypothesis (IH)
  rw [IH]
  -- Goal: {a} + s = a ::ₘ s

  -- 6. Use the definition of cons `a ::ₘ s = {a} + s`
  rw [Multiset.singleton_add]
  -- Goal is now `a ::ₘ s = a ::ₘ s`, which is true by reflexivity.

@[simp]
theorem sum_replicate_count_toFinset_eq_self {α : Type*} [DecidableEq α] (s : Multiset α) :
    ∑ i ∈ s.toFinset, Multiset.replicate (Multiset.count i s) i = s := by
  -- Prove by induction on the multiset s
  induction s using Multiset.induction
  case empty =>
    -- Base case: s = 0
    simp -- Uses sum_replicate_count_nil or simplifies directly: toFinset 0 = ∅, sum over ∅ is 0. Goal 0 = 0.
  case cons a s ih =>
    -- Inductive step: Assume property holds for s, prove for a :: s
    -- Goal: ∑ i in (a :: s).toFinset, replicate (count i (a :: s)) i = a :: s
    rw [Multiset.toFinset_cons] -- (a :: s).toFinset = insert a s.toFinset
    -- Goal: ∑ i in insert a s.toFinset, replicate (count i (a :: s)) i = a :: s

    -- Split the proof based on whether 'a' was already in the finset 's.toFinset'
    by_cases ha_mem_finset : a ∈ s.toFinset
    · -- Case 1: a ∈ s.toFinset
      exact step_mem ha_mem_finset ih
    · -- Case 2: a ∉ s.toFinset
      exact step_not_mem ha_mem_finset ih

/-!
Lemma: `beStateToMultiset` and `multisetToBEStateSubtype` are inverses (right inverse).
Shows applying the conversion to multiset then back to state map yields the original multiset.
-/
lemma right_inv_beState_multiset {N M : ℕ} (s : SymFin N M) :
    beStateToMultiset (multisetToBEStateSubtype s) = s.val := by
  -- Unfold the definitions step-by-step
  -- 1. Unfold beStateToMultiset
  dsimp only [beStateToMultiset]
  -- Goal: ∑ i ∈ Finset.univ, replicate ((multisetToBEStateSubtype s).val i) i = s.val

  -- 2. Unfold the .val part of multisetToBEStateSubtype
  --    (multisetToBEStateSubtype s).val = multisetToBEState s.val
  simp only [multisetToBEStateSubtype] -- Use simp to handle the subtype projection
  -- Goal: ∑ i ∈ Finset.univ, replicate (multisetToBEState s.val i) i = s.val

  -- 3. Unfold multisetToBEState
  simp only [multisetToBEState]
  -- Goal: ∑ i ∈ Finset.univ, replicate (Multiset.count i s.val) i = s.val

  -- 4. Use the lemma linking sum over univ to sum over toFinset
  --    Need `Finset.univ` for Fin N and the proof `Finset.mem_univ`
  rw [sum_replicate_count_univ_eq_sum_toFinset s.val Finset.univ (Finset.mem_univ)]
  -- Goal: ∑ i ∈ s.val.toFinset, replicate (Multiset.count i s.val) i = s.val

  -- 5. Apply the key identity proven by induction
  rw [sum_replicate_count_toFinset_eq_self s.val]
  -- Goal is now s.val = s.val, which is true by reflexivity.
