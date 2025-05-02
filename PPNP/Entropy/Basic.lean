import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog -- For negMulLog, Real.log
import Mathlib.Data.NNReal.Basic -- For NNReal
import Mathlib.Topology.Basic -- For ContinuousOn (placeholder)
import Mathlib.Order.Monotone.Basic -- For Monotone
import Mathlib.Algebra.BigOperators.Fin -- For sum over Fin n
import Mathlib.Data.Fin.Basic -- Basic Fin definitions and lemmas
import Mathlib.Data.Fintype.Fin -- Instances for Fin n
import Mathlib.Algebra.Order.Field.Basic -- For inv_one etc.
import Mathlib.Algebra.GroupWithZero.Units.Basic -- Provides mul_inv_cancel₀

namespace PPNP.Entropy.Basic

open BigOperators Fin Real Topology NNReal Filter Nat

/-!
# Formalizing Rota's Uniqueness of Entropy Theorem - Chunk 1 Completed

**Goal:** Define `IsEntropyFunction` structure correctly, define `f n = H(uniform n)`,
prove `f 1 = 0`, and prove `f` is monotone.

**Correction:** Fixed all previous issues and added proof for `f0_mono`.
-/

-- Definitions and Lemmas from previous steps... (stdEntropy, helpers, IsEntropyFunction structure)

/-- Standard Shannon entropy of a probability distribution given as a function `Fin n → NNReal`.
    Uses natural logarithm (base e). -/
noncomputable def stdEntropy {n : ℕ} (p : Fin n → NNReal) : Real :=
  ∑ i : Fin n, negMulLog (p i : Real)

-- Helper: Show the extended distribution for prop2 sums to 1 - Reuse from previous
lemma sum_p_ext_eq_one {n : ℕ} {p : Fin n → NNReal} (hp_sum : ∑ i : Fin n, p i = 1) :
    let p_ext := (λ i : Fin (n + 1) => if h : i.val < n then p (Fin.castLT i h) else 0)
    (∑ i : Fin (n + 1), p_ext i) = 1 := by
  intro p_ext
  rw [Fin.sum_univ_castSucc]
  have last_term_is_zero : p_ext (Fin.last n) = 0 := by
    simp only [p_ext, Fin.val_last, lt_self_iff_false, dif_neg, not_false_iff]
  rw [last_term_is_zero, add_zero]
  have sum_eq : ∑ (i : Fin n), p_ext (Fin.castSucc i) = ∑ (i : Fin n), p i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [p_ext]
    have h_lt : (Fin.castSucc i).val < n := by exact i.is_lt
    rw [dif_pos h_lt, Fin.castLT_castSucc i h_lt]
  rw [sum_eq]
  exact hp_sum

-- stdEntropy lemma for extended distribution (used if we prove relation for stdEntropy)
lemma stdEntropy_p_ext_eq_stdEntropy {n : ℕ} (p : Fin n → NNReal) :
    let p_ext := (λ i : Fin (n + 1) => if h : i.val < n then p (Fin.castLT i h) else 0)
    stdEntropy p_ext = stdEntropy p := by
  intro p_ext
  simp_rw [stdEntropy]
  rw [Fin.sum_univ_castSucc]
  have last_term_val_is_zero : p_ext (Fin.last n) = 0 := by
    simp only [p_ext, Fin.val_last, lt_self_iff_false, dif_neg, not_false_iff]
  rw [last_term_val_is_zero, NNReal.coe_zero, negMulLog_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply congr_arg negMulLog
  apply NNReal.coe_inj.mpr
  simp only [p_ext]
  have h_lt : (Fin.castSucc i).val < n := by exact i.is_lt
  rw [dif_pos h_lt, Fin.castLT_castSucc i h_lt]


-- Structure: Axiomatic Entropy Function H
structure IsEntropyFunction (H : ∀ {n : ℕ}, (Fin n → NNReal) → Real) where
  (prop0_H1_eq_0 : H (λ _ : Fin 1 => 1) = 0)
  (prop2_zero_inv : ∀ {n : ℕ} (p : Fin n → NNReal) (_ : ∑ i : Fin n, p i = 1),
      let p_ext := (λ i : Fin (n + 1) => if h : i.val < n then p (Fin.castLT i h) else 0)
      H p_ext = H p)
  (prop3_continuity : Prop)
  (prop4_conditional : Prop)
  (prop5_max_uniform : ∀ {n : ℕ} (hn_pos : n > 0) (p : Fin n → NNReal) (hp_sum : ∑ i : Fin n, p i = 1),
      H p ≤ H (λ _ : Fin n => if hn' : n > 0 then (n⁻¹ : NNReal) else 0)) -- NOTE: hn' check is redundant due to hn_pos

-- Definition: f(n) = H(uniform distribution on n outcomes)

-- Helper function for the uniform distribution probability value
noncomputable def uniformProb (n : ℕ) : NNReal :=
  if hn : n > 0 then (n⁻¹ : NNReal) else 0

-- Helper lemma: the uniform distribution sums to 1
lemma sum_uniform_eq_one {n : ℕ} (hn : n > 0) :
  ∑ _i : Fin n, uniformProb n = 1 := by
  simp only [uniformProb, dif_pos hn]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [mul_inv_cancel₀]
  apply Nat.cast_ne_zero.mpr
  exact Nat.pos_iff_ne_zero.mp hn

/-- Define f(n) as the entropy H of the uniform distribution on n outcomes. Needs n > 0. -/
noncomputable def f {n : ℕ} (H : ∀ {m : ℕ}, (Fin m → NNReal) → Real) (hn : n > 0) : Real :=
  H (λ _ : Fin n => uniformProb n)

/-- Define f₀(n) extending f to n=0. -/
noncomputable def f₀ (H : ∀ {m : ℕ}, (Fin m → NNReal) → Real) (n : ℕ) : Real :=
  if hn : n > 0 then f H hn else 0

-- Assume H satisfies the properties for the rest of the proofs
variable {H : ∀ {n : ℕ}, (Fin n → NNReal) → Real} (hH : IsEntropyFunction H)

-- ##################################################
-- Basic Properties of f₀(n)
-- ##################################################

/-- Property: f₀(1) = 0 -/
theorem f0_1_eq_0 (hH : IsEntropyFunction H) : f₀ H 1 = 0 := by
  have h1 : 1 > 0 := Nat.one_pos
  simp only [f₀, dif_pos h1, f]
  have h_unif1_func : (λ _ : Fin 1 => uniformProb 1) = (λ _ : Fin 1 => 1) := by
    funext i
    simp only [uniformProb, dif_pos h1, Nat.cast_one, inv_one]
  rw [h_unif1_func]
  exact hH.prop0_H1_eq_0

/-- Property: f₀ is monotone non-decreasing -/
theorem f0_mono (hH : IsEntropyFunction H) : Monotone (f₀ H) := by
  -- Use monotone_nat_of_le_succ: prove f₀ n ≤ f₀ (n + 1) for all n
  apply monotone_nat_of_le_succ
  intro n
  -- Case split on n
  if hn_zero : n = 0 then
    -- Case n = 0: Need f₀ 0 ≤ f₀ 1
    rw [hn_zero]
    rw [f0_1_eq_0 hH] -- f₀ 1 = 0
    simp only [f₀, dif_neg (Nat.not_lt_zero 0)]
    exact le_refl 0 -- 0 ≤ 0
  else
    -- Case n ≥ 1: Need f₀ n ≤ f₀ (n + 1)
    -- Get proofs that n > 0 and n + 1 > 0
    have hn_pos : n > 0 := Nat.pos_of_ne_zero hn_zero
    have hn1_pos : n + 1 > 0 := Nat.succ_pos n

    -- Unfold f₀ for n and n + 1
    have f0_n_def : f₀ H n = f H hn_pos := dif_pos hn_pos
    have f0_n1_def : f₀ H (n + 1) = f H hn1_pos := dif_pos hn1_pos
    rw [f0_n_def, f0_n1_def] -- Now goal is f H hn_pos ≤ f H hn1_pos
    simp_rw [f] -- Unfold f: goal is H (uniform n) ≤ H (uniform (n+1))

    -- Define the uniform distribution on n outcomes
    let unif_n := (λ _ : Fin n => uniformProb n)
    -- Define the extended distribution p on n+1 outcomes
    let p := (λ i : Fin (n + 1) => if h : i.val < n then unif_n (Fin.castLT i h) else 0)

    -- Show p sums to 1
    have h_sum_n : ∑ i : Fin n, unif_n i = 1 := sum_uniform_eq_one hn_pos
    have h_sum_p : ∑ i : Fin (n + 1), p i = 1 := sum_p_ext_eq_one h_sum_n

    -- Relate H p to H (uniform n) using Property 2
    have h_p_eq_H_unif_n : H p = H unif_n := by
       -- Need to provide the explicit function H to prop2_zero_inv
       exact hH.prop2_zero_inv unif_n h_sum_n

    -- Relate H p to H (uniform n+1) using Property 5
    -- Direct application of prop5 and simplify uniformProb
    have h_p_le_H_unif_n1 : H p ≤ H (λ _ : Fin (n + 1) => uniformProb (n + 1)) := by
      have h5 := hH.prop5_max_uniform hn1_pos p h_sum_p
      simpa [uniformProb, hn1_pos] using h5

    -- Combine the results: H (uniform n) = H p ≤ H (uniform n+1)
    rw [← h_p_eq_H_unif_n] -- Replace H (uniform n) with H p
    exact h_p_le_H_unif_n1 -- The goal is now exactly this inequality

/-!
Chunk 1 Completed. Next Step: Chunk 2 - The Power Law `f₀(n^k) = k * f₀(n)`.
-/

end PPNP.Entropy.Basic

export PPNP.Entropy.Basic (
  stdEntropy
  IsEntropyFunction
  uniformProb
  sum_uniform_eq_one
  f
  f₀
  f0_1_eq_0
  f0_mono
)
