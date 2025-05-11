--import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog -- For negMulLog, Real.log
--import Mathlib.Algebra.BigOperators.Fin -- For sum over Fin n
--import Mathlib.Data.Fin.Basic -- Basic Fin definitions and lemmas
--import Mathlib.Data.Fintype.Fin -- Instances for Fin n
--import Mathlib.Algebra.GroupWithZero.Units.Basic -- Provides mul_inv_cancel₀
--import Mathlib.Data.Nat.Basic -- Basic Nat properties
import Mathlib.Data.Sym.Card

--import Mathlib.Data.Multiset.Bind
--import Mathlib.Data.Multiset.Basic
--import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PPNP.Common.Basic
import PPNP.Entropy.Common
import PPNP.Entropy.Physics.Common
import PPNP.Entropy.RET

namespace PPNP.Entropy.Physics.BE

open PPNP.Entropy.RET

open Multiset NNReal
open PPNP.Common
open PPNP.Entropy.Common
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

/-!
## Phase 1: Combinatorial Equivalence (Completed)
We have established the maps and proven they are inverses. Now we bundle them into a formal `Equiv`.
-/

/--
Formal `Equiv` (bijection) between the `OmegaBE` representation (occupancy vectors)
and the `SymFin` representation (multisets of a fixed size).
This equivalence is crucial for transferring properties (like cardinality and `Fintype` instances)
from the well-understood `SymFin` type to `OmegaBE`.
-/
def beStateEquivMultiset (N M : ℕ) : OmegaBE N M ≃ SymFin N M where
  toFun q := ⟨beStateToMultiset q, card_beStateToMultiset q⟩
  invFun s := multisetToBEStateSubtype s
  left_inv q := left_inv_beState_multiset q
  right_inv s := by
    -- The goal is: toFun (invFun s) = s
    -- which expands to:
    -- ⟨beStateToMultiset (multisetToBEStateSubtype s), card_beStateToMultiset (multisetToBEStateSubtype s)⟩ = s
    -- For subtypes, equality `⟨v₁, p₁⟩ = ⟨v₂, p₂⟩` is equivalent to `v₁ = v₂` due to proof irrelevance for the property `p`.
    -- Here, `s.val` is the multiset part of `s : SymFin N M`, and `s.property` is the proof `card s.val = M`.
    -- The first component of `toFun (invFun s)` is `beStateToMultiset (multisetToBEStateSubtype s)`.
    -- So, we need to show `beStateToMultiset (multisetToBEStateSubtype s) = s.val`.
    -- This is precisely what `right_inv_beState_multiset s` states.
    apply Subtype.eq
    exact right_inv_beState_multiset s


/-!
## Phase 2: Cardinality and Iteration
With the equivalence established, we can now define a `Fintype` instance for `OmegaBE`.
-/

/--
`Fintype` instance for `OmegaBE N M`.
This instance is derived from the `Fintype` instance of `SymFin N M`
(which is `Sym (Fin N) M`) via the equivalence `beStateEquivMultiset`.
This allows us to treat `OmegaBE N M` as a finite type, enabling enumeration
and summation over all Bose-Einstein states, which is crucial for defining
probabilities and calculating entropy.
Mathlib provides `Sym.fintype` for `Sym α n` when `α` is a `Fintype` with `DecidableEq`.
`Fin N` meets these criteria.
-/
instance fintypeOmegaBE (N M : ℕ) : Fintype (OmegaBE N M) :=
  Fintype.ofEquiv (SymFin N M) (beStateEquivMultiset N M).symm

/--
Calculates the cardinality of the Bose-Einstein state space `OmegaBE N M`.
This is the number of ways to distribute `M` indistinguishable particles into `N`
distinguishable energy states, which is given by the multichoose function `Nat.multichoose N M`.
This corresponds to the "stars and bars" formula `(N + M - 1) choose M`.
The proof relies on the equivalence `beStateEquivMultiset` between `OmegaBE N M`
and `SymFin N M` (multisets of size `M` over `Fin N`), and the known cardinality
of `SymFin N M` from Mathlib (`Sym.card_fintype`).
-/
lemma card_omega_be (N M : ℕ) :
    Fintype.card (OmegaBE N M) = Nat.multichoose N M := by
  rw [Fintype.card_congr (beStateEquivMultiset N M)]
  -- Goal is now: Fintype.card (SymFin N M) = Nat.multichoose N M
  -- SymFin N M is defined as Sym (Fin N) M.
  -- Sym.card_fintype states: Fintype.card (Sym α k) = Nat.multichoose (Fintype.card α) k
  rw [Sym.card_sym_eq_multichoose (Fin N) M]
  -- Goal is now: Nat.multichoose (Fintype.card (Fin N)) M = Nat.multichoose N M
  rw [Fintype.card_fin N]
  -- Goal is now: Nat.multichoose N M = Nat.multichoose N M, which is true by reflexivity.

open BigOperators

/-- `Nat.multichoose` is positive exactly when we can really place
    `k` indistinguishable balls into `n` labelled boxes – i.e.
    either we have at least one box (`n ≠ 0`) or there is nothing
    to place (`k = 0`). -/
lemma multichoose_pos_iff (n k : ℕ) :
    0 < Nat.multichoose n k ↔ (n ≠ 0 ∨ k = 0) := by
  -- split on the trivial `k = 0` case
  by_cases hk : k = 0
  · subst hk
    simp [Nat.multichoose_zero_right]  -- `1 > 0`
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    -- now analyse `n`
    cases n with
    | zero =>
        -- `n = 0`, `k > 0`  ⇒  multichoose vanishes
        have h0 : Nat.multichoose 0 k = 0 := by
          -- stars‑&‑bars gives a too‑large binomial coefficient
          have hlt : k - 1 < k := Nat.pred_lt (Nat.ne_of_gt hkpos)
          rw [Nat.multichoose_eq]
          rw [Nat.zero_add]
          exact (Nat.choose_eq_zero_of_lt hlt)
        simp [h0, hk]
    | succ n' =>
        -- `n = n'.succ`, `k > 0`  ⇒  multichoose positive
        have hle : k ≤ n' + k := by
          simpa [add_comm] using Nat.le_add_left k n'
        have : 0 < (n' + k).choose k := Nat.choose_pos hle
        simpa [Nat.multichoose_eq, Nat.succ_eq_add_one,
               add_comm, add_left_comm, add_assoc, hk] using this

/-- Proves that the cardinality of the Bose-Einstein state space OmegaBE N M is positive
under the condition that either the number of states N is non-zero or the number of
particles M is zero. This condition is necessary and sufficient for Nat.multichoose N M
to be positive. This lemma is important for defining probabilities, as it ensures the
denominator (total number of states) is not zero. -/
lemma card_omega_be_pos (N M : ℕ) (h : N ≠ 0 ∨ M = 0) :
    0 < Fintype.card (OmegaBE N M) := by
  -- the heavy lifting is `multichoose_pos_iff`
  simpa [card_omega_be, multichoose_pos_iff] using h

/-!
## Phase 3: Probability Distribution
With cardinality established, we can define the Bose-Einstein probability distribution.
We assume equiprobability of all microstates (configurations).
-/

/--
Defines the Bose-Einstein probability distribution `p_BE` over the state space `OmegaBE N M`.
This is a uniform distribution, where each state `q : OmegaBE N M` has probability
`1 / Fintype.card (OmegaBE N M)`.
The probability is given as an `NNReal` (non-negative real number).
This definition relies on `uniformProb` from `PPNP.Entropy.Common`, which handles
the case where the number of outcomes might be zero (though `card_omega_be_pos`
ensures the cardinality is positive under typical physical conditions `N ≠ 0 ∨ M = 0`).
-/
noncomputable def p_BE (N M : ℕ) : OmegaBE N M → NNReal :=
  fun _q => uniformProb (Fintype.card (OmegaBE N M))


/--
Proves that the Bose-Einstein probability distribution `p_BE N M` sums to 1 over
all possible states in `OmegaBE N M`, provided the domain is valid
(i.e., `N ≠ 0 ∨ M = 0`, ensuring the cardinality of the state space is positive).
This confirms that `p_BE N M` is a valid (normalized) probability distribution.
-/
lemma p_BE_sums_to_one (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    ∑ q : OmegaBE N M, (p_BE N M q) = 1 := by
  let card_val := Fintype.card (OmegaBE N M)
  have h_card_pos : card_val > 0 := card_omega_be_pos N M h_domain_valid

  -- Substitute the definition of p_BE and simplify using h_card_pos
  -- p_BE N M q simplifies to uniformProb card_val,
  -- which simplifies to (card_val : NNReal)⁻¹ because card_val > 0.
  -- Step 1: Substitute the definition of p_BE
  simp_rw [p_BE]
  -- After this, p_BE N M q becomes uniformProb card_val q

  -- Step 2: Substitute the definition of uniformProb
  -- This will introduce an if-then-else expression:
  -- (if card_val > 0 then fun _ => (card_val : NNReal)⁻¹ else fun _ => 0) q
  -- which simplifies to: if card_val > 0 then (card_val : NNReal)⁻¹ else 0
  simp_rw [uniformProb]

  -- Step 3: Simplify the if-then-else expression using h_card_pos (which states card_val > 0)
  -- This should rewrite (if card_val > 0 then (card_val : NNReal)⁻¹ else 0) to (card_val : NNReal)⁻¹
  rw [dif_pos h_card_pos]

  -- The sum is now of a constant term (card_val : NNReal)⁻¹ over all elements in OmegaBE N M.
  -- Finset.sum_const: ∑ _x ∈ s, c = Finset.card s • c
  -- Finset.card_univ for a Fintype is Fintype.card
  rw [Finset.sum_const, Finset.card_univ]
  -- The sum is now (Fintype.card (OmegaBE N M)) • (card_val : NNReal)⁻¹
  -- which is card_val • (card_val : NNReal)⁻¹

  -- Convert nsmul (ℕ • NNReal) to multiplication (NNReal * NNReal)
  rw [nsmul_eq_mul]
  -- The sum is now (↑card_val : NNReal) * (↑card_val : NNReal)⁻¹

  -- To use mul_inv_cancel₀, we need to show (card_val : NNReal) ≠ 0.
  have h_card_nnreal_ne_zero : (card_val : NNReal) ≠ 0 := by
    -- For a natural number n, (n : NNReal) = 0 if and only if n = 0.
    -- So, (n : NNReal) ≠ 0 if and only if n ≠ 0.
    -- We have h_card_pos : card_val > 0, which implies card_val ≠ 0.

    -- Step 1: Use `norm_cast` to simplify the coercion.
    -- This tactic applies `@[norm_cast]` lemmas like `NNReal.coe_ne_zero {n : ℕ}`.
    -- It should change the goal from `(↑card_val : NNReal) ≠ 0` to `card_val ≠ 0`.
    norm_cast
    -- The previous `simp only [NNReal.coe_ne_zero]` might have issues if the
    -- wrong `coe_ne_zero` lemma was being considered or if matching failed.

    -- Step 2: Prove `card_val ≠ 0` using `h_card_pos`.
    -- `h_card_pos` states `card_val > 0` (which is `0 < card_val`).
    -- `Nat.pos_iff_ne_zero.mp` is the implication `(0 < n) → (n ≠ 0)`.
    -- Thus, `Nat.pos_iff_ne_zero.mp h_card_pos` is a proof of `card_val ≠ 0`.
    exact Nat.pos_iff_ne_zero.mp h_card_pos
    -- This replaces the previous two steps:
    -- rw [←Nat.pos_iff_ne_zero]
    -- assumption

  -- Apply mul_inv_cancel₀
  rw [mul_inv_cancel₀ h_card_nnreal_ne_zero]
  -- The goal is now 1 = 1, which is true by reflexivity.

noncomputable def p_BE_fin (N M : ℕ) : Fin (Fintype.card (OmegaBE N M)) → NNReal :=
  fun _i => uniformProb (Fintype.card (OmegaBE N M))


-- Helper lemma: the uniform distribution sums to 1
lemma sum_uniform_eq_one {n : ℕ} (hn : n > 0) :
  ∑ _i : Fin n, uniformProb n = 1 := by
  simp only [uniformProb, dif_pos hn]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [mul_inv_cancel₀]
  apply Nat.cast_ne_zero.mpr
  exact Nat.pos_iff_ne_zero.mp hn





-- /-- Product of two uniform distributions is uniform on the product space. -/
-- lemma uniformProb_product_uniformProb_is_uniformProb
--     {n m : ℕ} (hn : n > 0) (hm : m > 0) :
--     product_dist
--         (fun _ : Fin n     => uniformProb n)
--         (fun _ : Fin m     => uniformProb m)
--       = (fun _ : Fin (n*m) => uniformProb (n * m)) := by
--   -- point‑wise equality of functions on `Fin (n*m)`
--   funext k
--   /- 1 ▸ reduce to an identity in `NNReal` -/
--   simp [product_dist, uniformProb, mul_pos hn hm]  -- goal: ↑n⁻¹ * ↑m⁻¹ = ↑(n*m)⁻¹

--   /- 2 ▸ build the `≠ 0` hypotheses in `NNReal` via `exact_mod_cast` -/
--   have hn_ne_zero : n ≠ 0 := (Nat.pos_iff_ne_zero).1 hn
--   have hm_ne_zero : m ≠ 0 := (Nat.pos_iff_ne_zero).1 hm
--   have h_n : (n : NNReal) ≠ 0 := by exact_mod_cast hn_ne_zero  -- `norm_cast` trick :contentReference[oaicite:0]{index=0}
--   have h_m : (m : NNReal) ≠ 0 := by exact_mod_cast hm_ne_zero

--   /- 3 ▸ convert the product of inverses to the inverse of a product -/
--   -- The left factor is `↑m⁻¹ * ↑n⁻¹`, so we use the lemma with arguments in that order.
--   rw [nnreal_inv_mul_inv_eq_inv_mul h_m h_n]

--   /- 4 ▸ finish by rewriting inside the inverse and using commutativity -/
--   rw [mul_comm] --`mul_comm` is a lemma that rewrites `a * b = b * a`
--   simp [hn, hm, mul_comm, nnreal_coe_nat_mul n m]  -- evaluates the `if`s and rewrites `↑n * ↑m`

/--
Proves that the adapted Bose-Einstein probability distribution `p_BE_fin N M`
(which is uniform over `Fin (Fintype.card (OmegaBE N M))`) sums to 1.
This confirms it's a valid probability distribution.
Requires the domain to be valid (`N ≠ 0 ∨ M = 0`) to ensure positive cardinality.
-/
lemma p_BE_fin_sums_to_one (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    ∑ i : Fin (Fintype.card (OmegaBE N M)), (p_BE_fin N M i) = 1 := by
  let k := Fintype.card (OmegaBE N M)
  have hk_pos : k > 0 := card_omega_be_pos N M h_domain_valid

  -- By definition, p_BE_fin N M i is uniformProb k.
  -- So the sum becomes ∑ (i : Fin k), uniformProb k.
  -- This can be simplified by rewriting the summand using the definition of p_BE_fin.
  simp_rw [p_BE_fin]

  -- The goal is now ∑ (_ : Fin k), uniformProb k = 1.
  -- This is exactly the statement of `sum_uniform_eq_one` with k and hk_pos.
  exact sum_uniform_eq_one hk_pos



/--
Helper lemma to show that `p_BE_fin N M` (which is `uniformProb k_card` for each entry)
is pointwise equal to `uniformDist` on `Fin k_card`.
This version uses a micro-lemma `Fintype_card_fin_pos` for clarity in the positivity argument.
-/
lemma p_BE_fin_is_uniformDist (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    let k_card := Fintype.card (OmegaBE N M)
    have hk_card_pos : k_card > 0 := card_omega_be_pos N M h_domain_valid
    -- The RHS now uses the clean Fintype_card_fin_pos lemma for its argument
    p_BE_fin N M = uniformDist (Fintype_card_fin_pos hk_card_pos) := by
  let k_card := Fintype.card (OmegaBE N M)
  have hk_card_pos : k_card > 0 := card_omega_be_pos N M h_domain_valid

  -- Prove by functional extensionality: show they are equal for any input `i`.
  funext i

  -- LHS processing:
  -- Unfold p_BE_fin. The definition of p_BE_fin is:
  --   noncomputable def p_BE_fin (N M : ℕ) : Fin (Fintype.card (OmegaBE N M)) → NNReal :=
  --     fun _i => uniformProb (Fintype.card (OmegaBE N M))
  -- So, (p_BE_fin N M i) becomes (uniformProb k_card).
  -- Unfold uniformProb. The definition is:
  --   noncomputable def uniformProb (n : ℕ) : NNReal :=
  --     if _hn : n > 0 then (n⁻¹ : NNReal) else 0
  -- So, (uniformProb k_card) becomes (if _hn : k_card > 0 then (k_card⁻¹ : NNReal) else 0).
  -- Since we have `hk_card_pos : k_card > 0`, this simplifies to (k_card⁻¹ : NNReal).

  -- RHS processing:
  -- Unfold uniformDist. The definition is:
  --   noncomputable def uniformDist {α : Type*} [Fintype α]
  --       (_h_card_pos : 0 < Fintype.card α) : α → NNReal :=
  --   λ _ ↦ (Fintype.card α : NNReal)⁻¹
  -- Here, α is `Fin k_card`.
  -- The argument `_h_card_pos` is `Fintype_card_fin_pos hk_card_pos`.
  -- So, (uniformDist (Fintype_card_fin_pos hk_card_pos) i) becomes
  --   (Fintype.card (Fin k_card) : NNReal)⁻¹.
  -- Since `Fintype.card (Fin k_card)` is `k_card` (from `Fintype.card_fin`),
  -- this becomes `(k_card : NNReal)⁻¹`.

  -- The simp tactic should handle these unfoldings.
  -- The crucial part is that the `if` on the LHS (from uniformProb) needs to be resolved.
  simp only [p_BE_fin, uniformProb, uniformDist, Fintype.card_fin]
  -- After this, the goal becomes:
  -- `(if hk_card_pos' : k_card > 0 then (k_card : NNReal)⁻¹ else 0) = (k_card : NNReal)⁻¹`
  -- where `hk_card_pos'` is the `_hn` from `uniformProb`.
  -- We have `hk_card_pos : k_card > 0` in the context.
  -- We need to tell Lean that `hk_card_pos'` is true because of `hk_card_pos`.
  rw [dif_pos hk_card_pos]

/--
Helper lemma to show that applying an entropy function `H_func` to `p_BE_fin N M`
(coerced to `Real`) is equivalent to evaluating `f0 H_func k_card` (coerced to `Real`),
where `k_card` is the cardinality of the state space.
-/
lemma H_p_BE_fin_eq_f_H_card (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0)
    (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal)
    (hH_axioms : IsEntropyFunction H_func) :
    (H_func (p_BE_fin N M) : ℝ) = (f0 hH_axioms (Fintype.card (OmegaBE N M)) : ℝ) := by
  let k_card := Fintype.card (OmegaBE N M)
  have hk_card_pos : k_card > 0 := card_omega_be_pos N M h_domain_valid

  -- Step 1: Rewrite LHS using p_BE_fin_is_uniformDist
  -- This changes H_func(p_BE_fin N M) to H_func(uniformDist (Fintype_card_fin_pos hk_card_pos))
  rw [p_BE_fin_is_uniformDist N M h_domain_valid]

  -- Step 2: Simplify the RHS.
  -- We want to show: (f0 hH_axioms k_card : ℝ) = (H_func (uniformDist (Fintype_card_fin_pos hk_card_pos)) : ℝ)
  -- First, unfold f0.
  simp only [f0]
  -- The RHS's NNReal part is now `if _hn : k_card > 0 then f hH_axioms _hn else 0`.
  -- The coercion to Real distributes over the if: `if _hn : k_card > 0 then ↑(f hH_axioms _hn) else ↑0`.
  -- Now, simplify the if using hk_card_pos.
  rw [dif_pos hk_card_pos]
  -- Now RHS is `↑(f hH_axioms hk_card_pos)`.

  -- Step 3: Unfold f on the RHS.
  -- The term `f hH_axioms hk_card_pos` is defined as:
  -- `let α_k_card := Fin k_card;
  --  have h_card_pos_f_def : 0 < Fintype.card α_k_card := Fintype_card_fin_pos hk_card_pos;
  --  H_func (uniformDist h_card_pos_f_def)`
  -- This `uniformDist` uses `h_card_pos_f_def`, which is `Fintype_card_fin_pos hk_card_pos`.
  -- The `uniformDist` on the LHS also uses `Fintype_card_fin_pos hk_card_pos`.
  -- So, the arguments to H_func should be identical.
  simp only [f]
  -- After this, both sides should be `(H_func (uniformDist (Fintype_card_fin_pos hk_card_pos)) : ℝ)`.
  -- Therefore, reflexivity should close the goal.


theorem H_BE_eq_C_shannon (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    eval_H_phys_system_on_fin_dist_to_real (p_BE_fin N M) =
      C_constant_real PPNP.Entropy.Physics.Common.H_physical_system_is_IsEntropyFunction *
      stdShannonEntropyLn (p_BE_fin N M) := by
  let k_card := Fintype.card (OmegaBE N M)
  have hk_card_pos : k_card > 0 := card_omega_be_pos N M h_domain_valid

  let H_is_entropy_proof_fq := PPNP.Entropy.Physics.Common.H_physical_system_is_IsEntropyFunction

  have h1 : eval_H_phys_system_on_fin_dist_to_real (p_BE_fin N M) =
              (f0 H_is_entropy_proof_fq k_card : ℝ) := by
    simp only [eval_H_phys_system_on_fin_dist_to_real]
    exact H_p_BE_fin_eq_f_H_card N M h_domain_valid PPNP.Entropy.Physics.Common.H_physical_system H_is_entropy_proof_fq
  rw [h1]

  have h2_full := RotaUniformTheorem_formula_with_C_constant H_is_entropy_proof_fq
  have h2_transform_f0 : (f0 H_is_entropy_proof_fq k_card : ℝ) =
              C_constant_real H_is_entropy_proof_fq * Real.log k_card :=
    h2_full.right k_card hk_card_pos
  rw [h2_transform_f0]

  have h_p_BE_fin_is_unif : p_BE_fin N M =
      uniformDist (Fintype_card_fin_pos hk_card_pos) :=
    p_BE_fin_is_uniformDist N M h_domain_valid

  have h3_shannon_eq_log_k : stdShannonEntropyLn (p_BE_fin N M) = Real.log k_card := by
    rw [h_p_BE_fin_is_unif]
    -- LHS becomes: stdShannonEntropyLn (uniformDist (Fintype_card_fin_pos hk_card_pos))
    -- We know from stdShannonEntropyLn_uniform_eq_log_card:
    --   stdShannonEntropyLn (uniformDist (Fintype_card_fin_pos hk_card_pos)) = Real.log (Fintype.card (Fin k_card))
    -- Goal is: Real.log k_card
    -- So we need to show: Real.log (Fintype.card (Fin k_card)) = Real.log k_card
    -- This follows if Fintype.card (Fin k_card) = k_card.

    -- Apply stdShannonEntropyLn_uniform_eq_log_card first
    rw [stdShannonEntropyLn_uniform_eq_log_card (Fintype_card_fin_pos hk_card_pos)]
    -- Goal is now: Real.log (Fintype.card (Fin k_card)) = Real.log k_card

    -- Now use the helper to change the argument of Real.log
    rw [card_fin_eq_self k_card]
    -- Goal is now: Real.log k_card = Real.log k_card


  rw [h3_shannon_eq_log_k]
