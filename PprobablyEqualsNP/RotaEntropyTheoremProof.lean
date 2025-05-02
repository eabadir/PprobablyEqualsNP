import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog -- For negMulLog, Real.log
import Mathlib.Data.NNReal.Basic -- For NNReal
import Mathlib.Topology.Basic -- For ContinuousOn (placeholder)
import Mathlib.Order.Monotone.Basic -- For Monotone
import Mathlib.Algebra.BigOperators.Fin -- For sum over Fin n
import Mathlib.Data.Fin.Basic -- Basic Fin definitions and lemmas
import Mathlib.Data.Fintype.Fin -- Instances for Fin n
import Mathlib.Algebra.Order.Field.Basic -- For inv_one etc.
import Mathlib.Algebra.GroupWithZero.Units.Basic -- Provides mul_inv_cancel₀ and related field/group lemmas

open BigOperators Fin Real Topology NNReal Filter Nat

/-!
# Formalizing Rota's Uniqueness of Entropy Theorem - Chunk 1 (Corrected Theorem f0_1_eq_0)

**Goal:** Define `IsEntropyFunction` structure correctly, define `f n = H(uniform n)`, and prove `f 1 = 0`.

**Correction:** Fixed proof of `sum_uniform_eq_one` and errors in `f0_1_eq_0`.
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

-- stdEntropy lemma should work with the same fix for arg_eq - Reuse from previous
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


-- Structure: Axiomatic Entropy Function H (Corrected)
structure IsEntropyFunction (H : ∀ {n : ℕ}, (Fin n → NNReal) → Real) where
  (prop0_H1_eq_0 : H (λ _ : Fin 1 => 1) = 0) -- Property 0: Certainty has zero entropy
  (prop2_zero_inv : ∀ {n : ℕ} (p : Fin n → NNReal) (_ : ∑ i : Fin n, p i = 1),
      let p_ext := (λ i : Fin (n + 1) => if h : i.val < n then p (Fin.castLT i h) else 0)
      H p_ext = H p) -- Property 2: Invariance to adding zero probability
  (prop3_continuity : Prop) -- Placeholder: Assume continuity holds (as Prop)
  (prop4_conditional : Prop) -- Placeholder: Assume conditional property holds (as Prop)
  (prop5_max_uniform : ∀ {n : ℕ} (_hn_pos : n > 0) (p : Fin n → NNReal) (_hp_sum : ∑ i : Fin n, p i = 1),
      H p ≤ H (λ _ : Fin n => if hn' : n > 0 then (n⁻¹ : NNReal) else 0)) -- Property 5: Max entropy for uniform

-- Definition: f(n) = H(uniform distribution on n outcomes)

-- Helper function for the uniform distribution probability value
noncomputable def uniformProb (n : ℕ) : NNReal :=
  if hn : n > 0 then (n⁻¹ : NNReal) else 0

-- Helper lemma: the uniform distribution sums to 1 (Corrected)
lemma sum_uniform_eq_one {n : ℕ} (hn : n > 0) :
  ∑ _i : Fin n, uniformProb n = 1 := by
  simp only [uniformProb, dif_pos hn]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  -- Use mul_inv_cancel₀ requires proving ↑n ≠ 0
  rw [mul_inv_cancel₀] -- Apply cancellation
  -- Prove the condition for cancellation: ↑n ≠ 0
  apply Nat.cast_ne_zero.mpr -- Use the correct direction helper
  exact Nat.pos_iff_ne_zero.mp hn -- Use hn > 0 to show n ≠ 0


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
  simp only [f₀, dif_pos h1, f] -- Use definition of f₀ and f for n=1
  -- Show that the uniform distribution function for n=1 is (λ _ : Fin 1 => 1)
  have h_unif1_func : (λ _ : Fin 1 => uniformProb 1) = (λ _ : Fin 1 => 1) := by
    funext i -- Use function extensionality
    simp only [uniformProb, dif_pos h1] -- Simplify uniformProb for n=1
    rw [Nat.cast_one, inv_one] -- Simplify (↑1)⁻¹ to 1
  rw [h_unif1_func]
  -- Use the assumed property prop0_H1_eq_0 from the explicitly passed hH instance
  exact hH.prop0_H1_eq_0

/-!
Next Step: Prove `f0_mono : Monotone (f₀ H)`.
-/
