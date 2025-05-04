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

namespace PPNP.Entropy.Basic

open BigOperators Fin Real Topology NNReal Filter Nat

/-!
# Formalizing Rota's Uniqueness of Entropy Theorem - Chunk 1 Completed

**Goal:** Define `IsEntropyFunction` structure correctly, define `f n = H(uniform n)`,
prove `f 1 = 0`, and prove `f` is monotone.

**Correction:** Fixed all previous issues and added proof for `f0_mono`.
-/

-- Definitions and Lemmas from previous steps... (stdShannonEntropyLn, helpers, IsEntropyFunction structure)

/-- Standard Shannon entropy of a probability distribution given as a function `Fin n → NNReal`.
    Uses natural logarithm (base e). -/
noncomputable def stdShannonEntropyLn {n : ℕ} (p : Fin n → NNReal) : Real :=
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

-- stdShannonEntropyLn lemma for extended distribution (used if we prove relation for stdShannonEntropyLn)
lemma stdShannonEntropyLn_p_ext_eq_stdShannonEntropyLn {n : ℕ} (p : Fin n → NNReal) :
    let p_ext := (λ i : Fin (n + 1) => if h : i.val < n then p (Fin.castLT i h) else 0)
    stdShannonEntropyLn p_ext = stdShannonEntropyLn p := by
  intro p_ext
  simp_rw [stdShannonEntropyLn]
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
  (prop5_max_uniform : ∀ {n : ℕ} (_hn_pos : n > 0) (p : Fin n → NNReal) (_hp_sum : ∑ i : Fin n, p i = 1),
      H p ≤ H (λ _ : Fin n => if _hn' : n > 0 then (n⁻¹ : NNReal) else 0)) -- NOTE: hn' check is redundant due to hn_pos

-- Definition: f(n) = H(uniform distribution on n outcomes)
noncomputable def uniformProb (n : ℕ) : NNReal :=
  if _hn : n > 0 then (n⁻¹ : NNReal) else 0

-- Helper lemma: the uniform distribution sums to 1
lemma sum_uniform_eq_one {n : ℕ} (hn : n > 0) :
  ∑ _i : Fin n, uniformProb n = 1 := by
  simp only [uniformProb, dif_pos hn]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [mul_inv_cancel₀]
  apply Nat.cast_ne_zero.mpr
  exact Nat.pos_iff_ne_zero.mp hn

/-- Define f(n) as the entropy H of the uniform distribution on n outcomes. Needs n > 0. -/
noncomputable def f {n : ℕ} (H : ∀ {m : ℕ}, (Fin m → NNReal) → Real) (_hn : n > 0) : Real :=
  H (λ _ : Fin n => uniformProb n)

/-- Define f₀(n) extending f to n=0. -/
noncomputable def f₀ (H : ∀ {m : ℕ}, (Fin m → NNReal) → Real) (n : ℕ) : Real :=
  if hn : n > 0 then f H hn else 0


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

/-!
### Chunk 2: The Power Law `f₀(n^k) = k * f₀(n)`

**Step 1: State the Assumed Lemma (Consequence of Prop 4)**
-/

/-- Assumed step relation derived from Property 4 (Conditional Entropy). -/
lemma uniformEntropy_product_recursion {n k : ℕ} (hn : n ≥ 1) (hk : k ≥ 1) :
    f₀ H (n ^ (k + 1)) = f₀ H (n ^ k) + f₀ H n := by
  sorry -- Assumed consequence of hH.prop4_conditional applied to specific partitions

/-!
**Step 2: Prove the Main Power Law `uniformEntropy_power_law`**

Use the assumed step relation and induction on `k` starting from 1,
breaking the proof into helper lemmas.
-/

/-- Cast a successor into a sum: `↑(m + 1) = ↑m + 1`. -/
lemma cast_add_one_real (m : ℕ) : ↑(m + 1) = ↑m + 1 :=
  Nat.cast_add_one m

lemma add_mul_right (m : ℕ) (c : ℝ) :
    ↑m * c + c = (m + 1 : ℝ) * c := by
  ring          -- ← one line, succeeds


/-- Power law for `f₀`: `f₀(n^k) = k * f₀(n)`. -/
theorem uniformEntropy_power_law
  (_hH : IsEntropyFunction H) {n k : ℕ} (hn : n ≥ 1) (hk : k ≥ 1) :
    f₀ H (n ^ k) = (k : ℝ) * f₀ H n := by
  -- predicate we will induct on
  let P : ℕ → Prop := fun m ↦ f₀ H (n ^ m) = (m : ℝ) * f₀ H n

  -- base : `k = 1`
  have base : P 1 := by
    simp [P, pow_one]

  -- step : `m ≥ 1 → P m → P (m+1)`
  have step : ∀ m, 1 ≤ m → P m → P (m + 1) := by
    intro m hm ih
    -- unfold the predicate
    simp [P] at ih ⊢
    -- entropy step (assumed consequence of conditional entropy)
    have hstep := uniformEntropy_product_recursion (H := H) hn hm
    -- rewrite with the step relation and IH
    simpa [ih, add_mul_right m (f₀ H n)] using hstep

  -- perform the induction starting at 1
  simpa [P] using
    Nat.le_induction (m := 1)
      base
      (fun m hm ih => step m hm ih)
      k
      hk

-- Code from Chunk 3.1 ... (C_const, log_b_pos, f0_nonneg, C_const_nonneg) ...
/- ### Chunk 3.3c: Breaking down uniformEntropy_pos_of_nontrivial -/


/-- Lemma: `f₀ H b ≥ 0` for `b ≥ 1`. -/
lemma f0_nonneg (hH : IsEntropyFunction H) {b : ℕ} (hb : b ≥ 1) : f₀ H b ≥ 0 := by
  have h_mono_prop : Monotone (f₀ H) := PPNP.Entropy.Basic.f0_mono hH
  have h_mono_ineq : f₀ H 1 ≤ f₀ H b := h_mono_prop hb
  have h_f0_1_zero : f₀ H 1 = 0 := PPNP.Entropy.Basic.f0_1_eq_0 hH
  rw [h_f0_1_zero] at h_mono_ineq
  exact h_mono_ineq

/-!
### Chunk 3.2: The Trapping Argument Setup
-/

/-- Helper lemma: `1 < b` for `b ≥ 2` -/
lemma one_lt_cast_of_ge_two {b : ℕ} (hb : b ≥ 2) : 1 < (b : ℝ) :=
  Nat.one_lt_cast.mpr (Nat.lt_of_succ_le hb)

/-- Helper lemma: `0 < b` for `b ≥ 2` -/
lemma cast_pos_of_ge_two {b : ℕ} (hb : b ≥ 2) : 0 < (b : ℝ) :=
  Nat.cast_pos.mpr (Nat.lt_of_succ_le (by linarith [hb] : 1 ≤ b))

/-- Lemma: floor of `Real.logb b x` is at most `Real.logb b x`. -/
lemma floor_logb_le {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
  (Nat.floor (Real.logb b x) : ℝ) ≤ Real.logb b x := -- Cast floor to Real
by
  have hb_gt_one_real : 1 < (b : ℝ) := one_lt_cast_of_ge_two hb
  exact Nat.floor_le (Real.logb_nonneg hb_gt_one_real hx)

/-- Lemma: `log b > 0` for `b ≥ 2`. -/
lemma log_b_pos {b : ℕ} (hb : b ≥ 2) : Real.log b > 0 := by
  apply Real.log_pos -- Changes goal to `↑b > 1`
  -- Explicitly show the cast is greater than 1
  have hb_gt_one_real : (b : ℝ) > 1 := by
    -- Convert Nat inequality `b ≥ 2` to Real inequality `↑b ≥ 2`
    have hb_ge_2_real : (b : ℝ) ≥ (2 : ℝ) := Nat.cast_le.mpr hb
    -- Use linarith: `↑b ≥ 2` implies `↑b > 1` because `2 > 1`
    linarith [hb_ge_2_real]
  exact hb_gt_one_real



/-- Lemma: `Real.logb b x * Real.log b = Real.log x`. Needs `b > 0`, `b ≠ 1`, `x > 0`. -/
lemma logb_mul_log_eq_log {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
  Real.logb b x * Real.log b = Real.log x :=
by
  -- Need b ≠ 1 for logb definition
  have b_ne_one : (b : ℝ) ≠ 1 := ne_of_gt (one_lt_cast_of_ge_two hb)
  -- Need b > 0 for logb definition
  have b_pos : 0 < (b : ℝ) := cast_pos_of_ge_two hb
  -- Need x > 0 for logb definition
  have x_pos : 0 < x := by linarith [hx]

  -- Use the definition: Real.logb b x = Real.log x / Real.log b
  rw [Real.logb] -- Unfolds the definition

  -- Simplify (log x / log b) * log b = log x
  -- Use div_mul_cancel₀ which requires log b ≠ 0
  rw [div_mul_cancel₀]
  -- Prove log b ≠ 0
  exact Real.log_ne_zero_of_pos_of_ne_one b_pos b_ne_one

/-- Intermediate Lemma: `k * log b ≤ log x` where `k = floor(logb b x)`. -/
lemma floor_logb_mul_log_le_log {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
  (Nat.floor (Real.logb b x) : ℝ) * Real.log b ≤ Real.log x :=
by
  have h_floor_le_logb_real : (Nat.floor (Real.logb b x) : ℝ) ≤ Real.logb b x :=
    floor_logb_le hb hx
  have h_log_b_nonneg : 0 ≤ Real.log b := le_of_lt (log_b_pos hb)
  have h_mul_log : (Nat.floor (Real.logb b x) : ℝ) * Real.log b ≤ Real.logb b x * Real.log b :=
    mul_le_mul_of_nonneg_right h_floor_le_logb_real h_log_b_nonneg
  rw [logb_mul_log_eq_log hb hx] at h_mul_log
  exact h_mul_log

/-- Intermediate Lemma: From `y * log b ≤ log x`, prove `b ^ y ≤ x`. Uses `rpow`. -/
lemma rpow_le_of_mul_log_le_log {b : ℕ} {x y : ℝ} (hb : b ≥ 2) (hx_pos : 0 < x)
    (h_mul_log : y * Real.log b ≤ Real.log x) :
    (b : ℝ) ^ y ≤ x :=
by
  have hb_pos_real : 0 < (b : ℝ) := cast_pos_of_ge_two hb
  -- Apply exp to both sides (exp is strictly monotone)
  have h_exp_le_exp : Real.exp (y * Real.log b) ≤ Real.exp (Real.log x) :=
    Real.exp_le_exp.mpr h_mul_log
  -- Simplify LHS using x ^ y = exp(y * log x)
  rw [mul_comm y (Real.log b)] at h_exp_le_exp -- Commute for rpow_def_of_pos
  rw [← Real.rpow_def_of_pos hb_pos_real] at h_exp_le_exp -- LHS is now (b : ℝ) ^ y
  -- Simplify RHS using exp(log x) = x
  rw [Real.exp_log hx_pos] at h_exp_le_exp -- RHS is now x
  exact h_exp_le_exp


/-- Lemma: `(b : ℝ) ^ (Nat.floor (Real.logb b x) : ℝ) ≤ x` for `b ≥ 2` and `x ≥ 1`. -/
lemma rpow_floor_logb_le_x {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
  (b : ℝ) ^ (Nat.floor (Real.logb b x) : ℝ) ≤ x := -- Exponent is Real cast
by
  have h_mul_log : (Nat.floor (Real.logb b x) : ℝ) * Real.log b ≤ Real.log x :=
    floor_logb_mul_log_le_log hb hx
  have hx_pos : 0 < x := by linarith [hx]
  exact rpow_le_of_mul_log_le_log hb hx_pos h_mul_log

/-- Helper Lemma: `(b : ℝ) ^ k ≤ x` where `k = Nat.floor (Real.logb b x)`. Uses Nat exponent. -/
lemma pow_nat_floor_logb_le_x {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
  (b : ℝ) ^ (Nat.floor (Real.logb b x)) ≤ x :=
by
  let k := Nat.floor (Real.logb b x)
  -- Get the inequality with Real exponent from the existing lemma
  have h_le_real_exp : (b : ℝ) ^ (k : ℝ) ≤ x := rpow_floor_logb_le_x hb hx
  -- Need b ≥ 0 to use rpow_natCast
  have hb_nonneg : 0 ≤ (b : ℝ) := le_of_lt (cast_pos_of_ge_two hb)
  -- Rewrite the inequality using rpow_natCast (forward direction) to match the goal (Nat exponent)
  rw [Real.rpow_natCast (b : ℝ) k] at h_le_real_exp
  -- The hypothesis now matches the goal
  exact h_le_real_exp

/-- Helper Lemma: `x < (b : ℝ) ^ (k + 1)` where `k = Nat.floor (Real.logb b x)`. Uses Nat exponent. -/
lemma x_lt_pow_succ_floor_logb {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
  x < (b : ℝ) ^ (Nat.floor (Real.logb b x) + 1) :=
by
  let k := Nat.floor (Real.logb b x)
  have hb_pos : 0 < (b : ℝ) := cast_pos_of_ge_two hb
  have hx_pos : 0 < x := by linarith [hx]
  have log_b_pos' : 0 < Real.log b := log_b_pos hb

  -- Start from Nat.lt_floor_add_one
  have lt_floor_add_one : Real.logb b x < (k : ℝ) + 1 :=
    Nat.lt_floor_add_one (Real.logb b x)

  -- Multiply by log b (positive)
  have h_mul_log_lt : Real.logb b x * Real.log b < ((k : ℝ) + 1) * Real.log b :=
    (mul_lt_mul_right log_b_pos').mpr lt_floor_add_one

  -- Substitute log x using logb_mul_log_eq_log
  rw [logb_mul_log_eq_log hb hx] at h_mul_log_lt -- log x < (k+1) * log b

  -- Apply exp (strictly monotone)
  have h_exp_lt : Real.exp (Real.log x) < Real.exp (((k : ℝ) + 1) * Real.log b) :=
    Real.exp_lt_exp.mpr h_mul_log_lt

  -- Simplify LHS using exp_log
  rw [Real.exp_log hx_pos] at h_exp_lt -- x < exp(...)

  -- Simplify RHS using rpow_def_of_pos (backwards)
  rw [mul_comm ((k : ℝ) + 1) (Real.log b), ← Real.rpow_def_of_pos hb_pos] at h_exp_lt -- Changed: Added ←
  -- Now have: x < (b : ℝ) ^ ((k : ℝ) + 1)

  -- Rewrite exponent using Nat.cast_add_one
  have exp_eq : (k : ℝ) + 1 = (↑(k + 1) : ℝ) := (Nat.cast_add_one k).symm
  rw [exp_eq] at h_exp_lt -- x < (b : ℝ) ^ (↑(k + 1) : ℝ)

  -- Rewrite the expression in the hypothesis using rpow_natCast (forward direction)
  have hb_nonneg : 0 ≤ (b : ℝ) := le_of_lt hb_pos -- Need b ≥ 0 for rpow_natCast
  rw [Real.rpow_natCast (b : ℝ) (k + 1)] at h_exp_lt -- x < (b : ℝ) ^ (k + 1) (Nat exponent)

  -- The inequality now matches the goal
  exact h_exp_lt

/-- Lemma: For any `x ≥ 1` and integer `b ≥ 2`, there exists an integer `k` such that `b^k ≤ x < b^(k+1)`. This `k` is `floor(log_b(x))`. Uses Nat exponent version. -/
lemma exists_nat_pow_bounds {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
  ∃ k : ℕ, (b : ℝ) ^ k ≤ x ∧ x < (b : ℝ) ^ (k + 1) := by
  -- Define k as the floor of log base b of x
  let k := Nat.floor (Real.logb b x)
  -- Claim existence of this k
  use k
  -- Prove the two inequalities using the helper lemmas with Nat exponents
  constructor
  · exact pow_nat_floor_logb_le_x hb hx
  · exact x_lt_pow_succ_floor_logb hb hx


lemma exists_k_log_bounds {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
  ∃ k : ℕ, (b : ℝ) ^ k ≤ x ∧ x < (b : ℝ) ^ (k + 1) := by
  -- Define k as the floor of log base b of x
  let k := Nat.floor (Real.logb b x)
  -- Claim existence of this k
  use k
  -- Prove the two inequalities
  constructor
  · -- Prove (b : ℝ) ^ k ≤ x
    exact pow_nat_floor_logb_le_x hb hx
  · -- Prove x < (b : ℝ) ^ (k + 1)
    exact x_lt_pow_succ_floor_logb hb hx

/-!
### Chunk 3.3: Inequalities from Trapping `f₀ H (n^m)`
Derive `(k/m) * f₀ H b ≤ f₀ H n ≤ ((k+1)/m) * f₀ H b` (or similar, being careful about division).
This is the core step relating `f₀ H n` and `f₀ H b` via the integer bounds.
-/

/-- Lemma: If `a ≤ b`, then `↑a ≤ ↑b` for `a, b : ℕ`. -/
lemma cast_le_cast {a b : ℕ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr h


/- Lemma: `f₀ H b > 0` if `H` is not identically zero and `b ≥ 2`.
### Chunk 3.3a: Breaking down uniformEntropy_pos_of_nontrivial
-/

/-- Lemma 1: If f₀ H b = 0 for some b ≥ 2, then f₀ H 2 = 0. -/
lemma f0_2_eq_zero_of_f0_b_eq_zero {b : ℕ} (hH : IsEntropyFunction H) (hb : b ≥ 2) (hf0b_eq_0 : f₀ H b = 0) :
    f₀ H 2 = 0 := by
  -- Get monotonicity and non-negativity properties using hH
  have h_mono := f0_mono hH
  have h_f0_2_ge_0 : f₀ H 2 ≥ 0 := f0_nonneg hH (by linarith : 2 ≥ 1)

  -- Apply monotonicity: f₀(2) ≤ f₀(b) since 2 ≤ b
  have h_f0_2_le_b : f₀ H 2 ≤ f₀ H b := h_mono hb

  -- Combine inequalities: 0 ≤ f₀ H 2 ≤ f₀ H b = 0
  -- Rewrite with the assumption f₀ H b = 0
  rw [hf0b_eq_0] at h_f0_2_le_b -- Now have f₀ H 2 ≤ 0

  -- Conclude f₀ H 2 = 0 using antisymmetry (or linarith)
  -- We have f₀ H 2 ≥ 0 and f₀ H 2 ≤ 0
  linarith [h_f0_2_ge_0, h_f0_2_le_b]

/-!
### Chunk 3.3b: Breaking down uniformEntropy_pos_of_nontrivial
-/

/-- Lemma 2: If f₀ H 2 = 0, then f₀ H (2^k) = 0 for all k ≥ 1. -/
lemma f0_pow2_eq_zero_of_f0_2_eq_zero {k : ℕ} (hH : IsEntropyFunction H) (hf0_2_eq_0 : f₀ H 2 = 0) (hk : k ≥ 1) :
    f₀ H (2 ^ k) = 0 := by
  -- Apply the power law f₀(n^k) = k * f₀(n) with n=2
  have h_pow_law := uniformEntropy_power_law hH (by norm_num : 2 ≥ 1) hk
  -- h_pow_law : f₀ H (2 ^ k) = ↑k * f₀ H 2

  -- Substitute the assumption f₀ H 2 = 0
  rw [hf0_2_eq_0] at h_pow_law
  -- h_pow_law : f₀ H (2 ^ k) = ↑k * 0

  -- Simplify
  rw [mul_zero] at h_pow_law
  exact h_pow_law


/-!
### Chunk 3.3d: Breaking down uniformEntropy_pos_of_nontrivial
-/

-- Re-include the custom exists_pow_ge lemma and its use in exists_pow2_bound
lemma exists_pow_ge {a n : ℕ} (ha : 1 < a) : ∃ k : ℕ, n ≤ a ^ k :=
by
  cases n with
  | zero =>
      use 0
      exact Nat.zero_le (a ^ 0)
  | succ m =>
      use (m + 1)
      have h_lt : m + 1 < a ^ (m + 1) := Nat.lt_pow_self ha
      exact Nat.le_of_lt h_lt

lemma exists_pow2_bound {n : ℕ} (_hn : n ≥ 1) : ∃ k ≥ 1, n ≤ 2 ^ k := by
  have h2_gt_1 : 1 < 2 := by norm_num
  have h_exists_k0 : ∃ k₀ : ℕ, n ≤ 2 ^ k₀ := exists_pow_ge h2_gt_1
  rcases h_exists_k0 with ⟨k₀, h_n_le_pow_k₀⟩
  let k := max 1 k₀
  use k
  have hk_ge_1 : k ≥ 1 := Nat.le_max_left 1 k₀
  have hk₀_le_k : k₀ ≤ k := Nat.le_max_right 1 k₀
  have h_pow_mono : 2 ^ k₀ ≤ 2 ^ k := Nat.pow_le_pow_right (Nat.le_of_lt h2_gt_1) hk₀_le_k
  have hn_le_pow_k : n ≤ 2 ^ k := le_trans h_n_le_pow_k₀ h_pow_mono
  exact ⟨hk_ge_1, hn_le_pow_k⟩

/-- Lemma 4: If f₀ H (2^k) = 0 for all k ≥ 1, then f₀ H n = 0 for all n ≥ 1. -/
lemma f0_n_eq_zero_of_f0_pow2_zero {n : ℕ} (hH : IsEntropyFunction H)
    (h_f0_pow2_zero : ∀ k ≥ 1, f₀ H (2 ^ k) = 0) (hn : n ≥ 1) :
    f₀ H n = 0 := by
  -- Find k ≥ 1 such that n ≤ 2^k
  rcases exists_pow2_bound hn with ⟨k, hk_ge1, hn_le_pow2⟩

  -- Apply monotonicity of f₀ H
  have h_mono := f0_mono hH
  have h_f0_n_le_pow2 : f₀ H n ≤ f₀ H (2 ^ k) := h_mono hn_le_pow2

  -- Use the assumption that f₀ H (2^k) = 0 for k ≥ 1
  have h_f0_pow2_is_zero : f₀ H (2 ^ k) = 0 := h_f0_pow2_zero k hk_ge1

  -- Combine: f₀ H n ≤ 0
  rw [h_f0_pow2_is_zero] at h_f0_n_le_pow2

  -- Apply non-negativity: f₀ H n ≥ 0
  have h_f0_n_ge_0 : f₀ H n ≥ 0 := f0_nonneg hH hn

  -- Conclude f₀ H n = 0 by antisymmetry (or linarith)
  linarith [h_f0_n_ge_0, h_f0_n_le_pow2]

/-!
### Chunk 3.3e: Breaking down uniformEntropy_pos_of_nontrivial
-/

/-- Lemma 5: If f₀ H b = 0 for some b ≥ 2, then f₀ H n = 0 for all n ≥ 1. -/
lemma f0_all_zero_of_f0_b_zero {b : ℕ} (hH : IsEntropyFunction H) (hb : b ≥ 2) (hf0b_eq_0 : f₀ H b = 0) :
    ∀ n ≥ 1, f₀ H n = 0 := by
  -- Introduce n and the assumption n ≥ 1
  intro n hn

  -- Step 1: Show f₀ H 2 = 0
  have hf0_2_eq_0 : f₀ H 2 = 0 := f0_2_eq_zero_of_f0_b_eq_zero hH hb hf0b_eq_0

  -- Step 2: Define the hypothesis needed for the next lemma
  -- We need to show that f₀ H (2^k) = 0 for all k ≥ 1
  have h_f0_pow2_zero : ∀ k ≥ 1, f₀ H (2 ^ k) = 0 := by
    intro k hk
    exact f0_pow2_eq_zero_of_f0_2_eq_zero hH hf0_2_eq_0 hk

  -- Step 3: Apply the lemma showing f₀ H n = 0
  exact f0_n_eq_zero_of_f0_pow2_zero hH h_f0_pow2_zero hn


/-!
### Chunk 3.3f: Final Lemma for Positive f₀(b)
-/

/-- Lemma 6 (Original Goal): `f₀ H b > 0` if `H` is not identically zero and `b ≥ 2`. -/
lemma uniformEntropy_pos_of_nontrivial (hH : IsEntropyFunction H) (hH_nonzero : ∃ n ≥ 1, f₀ H n ≠ 0) (hb : b ≥ 2) :
    f₀ H b > 0 := by
  -- Start proof by contradiction
  by_contra h_f0_b_not_pos
  -- `h_f0_b_not_pos : ¬(f₀ H b > 0)`

  -- We know f₀ H b ≥ 0 from f0_nonneg
  have h_f0_b_ge_0 : f₀ H b ≥ 0 := f0_nonneg hH (by linarith : b ≥ 1)

  -- If f₀ H b is not positive and is non-negative, it must be zero
  have hf0b_eq_0 : f₀ H b = 0 := by
    linarith [h_f0_b_ge_0, h_f0_b_not_pos]

  -- Use the lemma showing that if f₀ H b = 0, then f₀ H n = 0 for all n ≥ 1
  have h_all_zero : ∀ n ≥ 1, f₀ H n = 0 := f0_all_zero_of_f0_b_zero hH hb hf0b_eq_0

  -- Extract the witness n_nz from the assumption hH_nonzero
  rcases hH_nonzero with ⟨n_nz, hn_nz_ge1, h_f0_n_nz_neq_0⟩

  -- Apply the "all zero" result to n_nz
  have h_f0_n_nz_eq_0 : f₀ H n_nz = 0 := h_all_zero n_nz hn_nz_ge1

  -- This contradicts the hypothesis that f₀ H n_nz ≠ 0
  exact h_f0_n_nz_neq_0 h_f0_n_nz_eq_0

lemma nat_bounds_from_cast_pow_bounds {b k n m : ℕ}
    (h_le_cast : (b : ℝ) ^ k ≤ (n : ℝ) ^ m)
    (h_lt_cast : (n : ℝ) ^ m < (b : ℝ) ^ (k + 1)) :
    b ^ k ≤ n ^ m ∧ n ^ m < b ^ (k + 1) := by

  -- Rewrite the hypotheses using Nat.cast_pow forwards to get the form ↑(...) required by mp
  rw [← Nat.cast_pow b k] at h_le_cast      -- Goal: Transform (↑b)^k into ↑(b^k)
  rw [← Nat.cast_pow n m] at h_le_cast      -- Goal: Transform (↑n)^m into ↑(n^m)
                                            -- h_le_cast is now ↑(b^k) ≤ ↑(n^m)

  rw [← Nat.cast_pow n m] at h_lt_cast      -- Goal: Transform (↑n)^m into ↑(n^m)
  rw [← Nat.cast_pow b (k + 1)] at h_lt_cast -- Goal: Transform (↑b)^(k+1) into ↑(b^(k+1))
                                             -- h_lt_cast is now ↑(n^m) < ↑(b^(k+1))

  -- Convert the inequalities involving casts back to Nat inequalities using mp
  constructor
  · -- Prove b^k ≤ n^m
    exact Nat.cast_le.mp h_le_cast
  · -- Prove n^m < b^(k+1)
    exact Nat.cast_lt.mp h_lt_cast

/--
Lemma: Convert Nat bounds `Bk ≤ Nm < Bkp1` to Real bounds on `f₀ H`.
-/
lemma f0_bounds_from_nat_bounds (hH : IsEntropyFunction H)
    {Bk Nm Bkp1 : ℕ} (h_le : Bk ≤ Nm) (h_lt : Nm < Bkp1) :
    f₀ H Bk ≤ f₀ H Nm ∧ f₀ H Nm ≤ f₀ H Bkp1 := by
  -- Get the monotonicity property of f₀ H
  have h_mono := f0_mono hH

  -- Apply monotonicity to the first inequality Bk ≤ Nm
  have h_f0_le1 : f₀ H Bk ≤ f₀ H Nm := h_mono h_le

  -- Convert the strict inequality Nm < Bkp1 to non-strict Nm ≤ Bkp1
  have h_le_from_lt : Nm ≤ Bkp1 := Nat.le_of_lt h_lt
  -- Apply monotonicity to the second (non-strict) inequality Nm ≤ Bkp1
  have h_f0_le2 : f₀ H Nm ≤ f₀ H Bkp1 := h_mono h_le_from_lt

  -- Combine the two derived f₀ H inequalities using the constructor for ∧
  constructor
  · exact h_f0_le1
  · exact h_f0_le2


/-- Helper 4a: Apply power law to the middle term f₀ H (n^m). -/
lemma f0_pow_middle (hH : IsEntropyFunction H) {n m : ℕ} (hn : n ≥ 1) (hm : m ≥ 1) :
    f₀ H (n ^ m) = (m : ℝ) * f₀ H n := by
  exact uniformEntropy_power_law hH hn hm

/-- Helper 4b: Apply power law to the left term f₀ H (b^k) when k ≥ 1. -/
lemma f0_pow_left_k_ge_1 (hH : IsEntropyFunction H) {b k : ℕ} (hb_ge1 : b ≥ 1) (hk_ge1 : k ≥ 1) :
    f₀ H (b ^ k) = (k : ℝ) * f₀ H b := by
  exact uniformEntropy_power_law hH hb_ge1 hk_ge1

/-- Helper 4c: Apply power law to the right term f₀ H (b^(k+1)) when k ≥ 0. -/
lemma f0_pow_right (hH : IsEntropyFunction H) {b k : ℕ} (hb_ge1 : b ≥ 1) :
    f₀ H (b ^ (k + 1)) = ((k : ℝ) + 1) * f₀ H b := by
  have hkp1_ge1 : k + 1 ≥ 1 := Nat.succ_pos k
  have raw_pow_law := uniformEntropy_power_law hH hb_ge1 hkp1_ge1 -- Gives ↑(k+1) * f₀ H b
  rw [Nat.cast_add_one k] at raw_pow_law -- Rewrites ↑(k+1) to ↑k + 1
  exact raw_pow_law

/-- Helper 4d: Combine power laws for the k ≥ 1 case. -/
lemma apply_power_law_k_ge_1 (hH : IsEntropyFunction H)
    {n m b k : ℕ} (hn : n ≥ 1) (hm : m ≥ 1) (hb : b ≥ 2) (hk_ge1 : k ≥ 1)
    (h_f0_le1_orig : f₀ H (b ^ k) ≤ f₀ H (n ^ m))
    (h_f0_le2_orig : f₀ H (n ^ m) ≤ f₀ H (b ^ (k + 1))) :
    (k : ℝ) * f₀ H b ≤ (m : ℝ) * f₀ H n ∧ (m : ℝ) * f₀ H n ≤ ((k : ℝ) + 1) * f₀ H b := by
  have hb_ge1 : b ≥ 1 := by linarith [hb]
  -- Apply power laws using the helpers
  let h_mid := f0_pow_middle hH hn hm
  let h_left := f0_pow_left_k_ge_1 hH hb_ge1 hk_ge1
  let h_right := f0_pow_right hH (b := b) (k := k) hb_ge1 -- Explicitly provide b and k

  -- Rewrite the original inequalities
  rw [h_left, h_mid] at h_f0_le1_orig
  rw [h_mid, h_right] at h_f0_le2_orig

  exact ⟨h_f0_le1_orig, h_f0_le2_orig⟩

/-- Helper 4e: Handle the k = 0 case. -/
lemma apply_power_law_k_eq_0 (hH : IsEntropyFunction H)
    {n m b : ℕ} (hn : n ≥ 1) (hm : m ≥ 1) (_hb : b ≥ 2) -- hb needed for context but not directly used
    (h_f0_le1_orig : f₀ H (b ^ 0) ≤ f₀ H (n ^ m))
    (h_f0_le2_orig : f₀ H (n ^ m) ≤ f₀ H (b ^ (0 + 1))) :
    (0 : ℝ) * f₀ H b ≤ (m : ℝ) * f₀ H n ∧ (m : ℝ) * f₀ H n ≤ ((0 : ℝ) + 1) * f₀ H b := by
  -- Apply power law to middle term
  let h_mid := f0_pow_middle hH hn hm

  -- Simplify bounds involving k=0
  rw [pow_zero] at h_f0_le1_orig -- f₀ H 1 ≤ f₀ H (n^m)
  rw [zero_add, pow_one] at h_f0_le2_orig -- f₀ H (n^m) ≤ f₀ H b

  -- Use f₀ H 1 = 0
  rw [f0_1_eq_0 hH] at h_f0_le1_orig -- 0 ≤ f₀ H (n^m)

  -- Rewrite middle term
  rw [h_mid] at h_f0_le1_orig h_f0_le2_orig -- 0 ≤ ↑m * f₀ H n ∧ ↑m * f₀ H n ≤ f₀ H b

  -- Construct the target structure
  constructor
  · -- Left inequality: 0 * f₀ H b ≤ ↑m * f₀ H n
    rw [zero_mul] -- Goal: 0 ≤ ↑m * f₀ H n
    exact h_f0_le1_orig
  · -- Right inequality: ↑m * f₀ H n ≤ (0 + 1) * f₀ H b
    simp only [zero_add, one_mul] -- Goal: ↑m * f₀ H n ≤ f₀ H b
    exact h_f0_le2_orig

/--
Lemma (Final Assembly): Apply the power law `f₀(a^p) = p * f₀(a)` to the bounds
`f₀ H (b^k) ≤ f₀ H (n^m) ≤ f₀ H (b^(k+1))`.
Requires appropriate positivity conditions `n ≥ 1, m ≥ 1, b ≥ 2`.
Handles the case k=0 separately using helper lemmas.
-/
lemma f0_bounds_apply_power_law (hH : IsEntropyFunction H)
    {n m b k : ℕ} (hn : n ≥ 1) (hm : m ≥ 1) (hb : b ≥ 2)
    (h_f0_bounds : f₀ H (b ^ k) ≤ f₀ H (n ^ m) ∧ f₀ H (n ^ m) ≤ f₀ H (b ^ (k + 1))) :
    (k : ℝ) * f₀ H b ≤ (m : ℝ) * f₀ H n ∧ (m : ℝ) * f₀ H n ≤ ((k : ℝ) + 1) * f₀ H b := by

  -- Deconstruct the input bounds
  rcases h_f0_bounds with ⟨h_f0_le1_orig, h_f0_le2_orig⟩

  -- Case split on k
  if hk_zero : k = 0 then
    -- Case k = 0
    -- Rewrite the original bounds using k=0 *before* calling the helper
    rw [hk_zero] at h_f0_le1_orig h_f0_le2_orig
    -- Now h_f0_le1_orig : f₀ H (b ^ 0) ≤ f₀ H (n ^ m)
    -- And h_f0_le2_orig : f₀ H (n ^ m) ≤ f₀ H (b ^ (0 + 1))

    -- Use the k=0 helper lemma with the rewritten bounds
    have result_k0 := apply_power_law_k_eq_0 hH hn hm hb h_f0_le1_orig h_f0_le2_orig
    -- result_k0 : 0 * f₀ H b ≤ ↑m * f₀ H n ∧ ↑m * f₀ H n ≤ (0 + 1) * f₀ H b

    -- Rewrite the *goal* using k=0 to match the result
    rw [hk_zero] -- Goal: (0:ℝ)*f₀ H b ≤ ... ∧ ... ≤ ((0:ℝ)+1)*f₀ H b
    simp only [Nat.cast_zero] -- Goal: 0*f₀ H b ≤ ... ∧ ... ≤ (0+1)*f₀ H b

    -- Now the result_k0 should exactly match the goal
    exact result_k0
  else
    -- Case k ≠ 0, implies k ≥ 1
    have hk_ge1 : k ≥ 1 := Nat.pos_of_ne_zero hk_zero
    -- Use the k ≥ 1 helper lemma with the original bounds
    exact apply_power_law_k_ge_1 hH hn hm hb hk_ge1 h_f0_le1_orig h_f0_le2_orig

lemma div_bounds_from_mul_bounds {A B C D E : ℝ} (hC : C > 0) (hD : D > 0)
    (h_le1 : A * C ≤ B * D) (h_le2 : B * D ≤ E * C) :
    A / D ≤ B / C ∧ B / C ≤ E / D := by
  constructor
  · -- Prove A / D ≤ B / C
    -- Use div_le_div_iff which states (a / d ≤ b / c ↔ a * c ≤ b * d) given d > 0, c > 0
    rwa [div_le_div_iff₀ hD hC] -- Rewrites goal A / D ≤ B / C to A * C ≤ B * D and uses h_le1
  · -- Prove B / C ≤ E / D
    -- Use div_le_div_iff which states (b / c ≤ e / d ↔ b * d ≤ e * c) given c > 0, d > 0
    rwa [div_le_div_iff₀ hC hD] -- Rewrites goal B / C ≤ E / D to B * D ≤ E * C and uses h_le2
/-! ### Chunk 3.4 - Breakdown Step 3 -/


/-- Helper: Prove 1 ≤ (b:ℝ)^k by induction for b ≥ 1. -/
lemma one_le_pow_of_one_le_real {b : ℝ} (hb : 1 ≤ b) (k : ℕ) : 1 ≤ b ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, le_refl] -- 1 ≤ 1
  | succ k ih => -- ih: 1 ≤ b^k. Goal: 1 ≤ b^(k+1)
    rw [pow_succ] -- Goal: 1 ≤ b^k * b
    -- We know 1 ≤ b (hb)
    -- We know 1 ≤ b^k (ih)
    -- Since 1 ≤ b, we have 0 ≤ 1 ≤ b, so b is non-negative.
    have hb_nonneg : 0 ≤ b := le_trans zero_le_one hb
    -- Multiply the inequality ih (1 ≤ b^k) by b (non-negative) on the right:
    -- 1 * b ≤ b^k * b
    -- We need `mul_le_mul_of_nonneg_right` which holds in `LinearOrderedSemiring` like ℝ
    have h_mul_le : 1 * b ≤ b ^ k * b := by
      apply mul_le_mul_of_nonneg_right
      · exact ih -- The inequality 1 ≤ b^k
      · exact hb_nonneg -- Proof that the multiplier b is non-negative

    simp only [one_mul] at h_mul_le -- Simplify 1 * b to b. Now: b ≤ b^k * b
    -- We have 1 ≤ b (hb) and b ≤ b^k * b (h_mul_le)
    -- By transitivity of ≤ :
    exact le_trans hb h_mul_le

/-- Lemma: `1 ≤ (n : ℝ) ^ (m : ℝ)` given `n ≥ 1, m ≥ 1`. -/
lemma one_le_rpow_cast_pow {n m : ℕ} (hn : n ≥ 1) :
    1 ≤ (n : ℝ) ^ (m : ℝ) := by
  -- Cast n ≥ 1 to Real: ↑n ≥ 1
  have hn_real_ge_1 : (n : ℝ) ≥ 1 := Nat.one_le_cast.mpr hn
  -- Cast m ≥ 1 implies m ≥ 0 in Real: ↑m ≥ 0
  have hm_real_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m -- m ≥ 1 → m ≥ 0 holds for Nat

  -- Rewrite 1 as 1 ^ ↑m using Real.one_rpow
  rw [← Real.one_rpow (m : ℝ)] -- Goal: 1 ^ ↑m ≤ ↑n ^ ↑m

  -- Apply Real.rpow_le_rpow {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) {r : ℝ} (hr : 0 ≤ r) : x ^ r ≤ y ^ r
  -- Here x=1, y=↑n, r=↑m
  apply Real.rpow_le_rpow
  · -- Prove 0 ≤ 1
    exact zero_le_one
  · -- Prove 1 ≤ ↑n
    exact hn_real_ge_1
  · -- Prove 0 ≤ ↑m
    exact hm_real_nonneg

-- Helper lemma (should be placed earlier or imported)
lemma one_le_pow_cast {n m : ℕ} (hn : n ≥ 1) :
    1 ≤ (n : ℝ) ^ m := by
  have hn_real_ge_1 : (n : ℝ) ≥ 1 := Nat.one_le_cast.mpr hn
  -- Use library lemma for powers of reals ≥ 1
  exact one_le_pow_of_one_le_real hn_real_ge_1 m

/-! ## Chunk 3.3: THEOREM!!! Trapping Inequalities
Theorem: Establishes the core trapping inequalities relating the ratio `f₀ H n / f₀ H b`
to the ratio `k / m` derived from integer power bounds `b^k ≤ n^m < b^(k+1)`.
Requires H to be non-trivial (`hH_nonzero`).
-/
theorem uniformEntropy_ratio_bounds_by_rational (hH : IsEntropyFunction H) (hH_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0)
    {n m b : ℕ} (hn : n ≥ 1) (hm : m ≥ 1) (hb : b ≥ 2) :
    ∃ k : ℕ, (k : ℝ) / m ≤ f₀ H n / f₀ H b ∧ f₀ H n / f₀ H b ≤ (k + 1 : ℝ) / m := by

  -- Step 1 & 2: Define x = (n:ℝ)^m (Nat power) and prove x ≥ 1.
  let x : ℝ := (n : ℝ) ^ m
  have hx_ge_1 : x ≥ 1 := one_le_pow_cast hn -- Use Nat power version

  -- Step 3: Get k and power bounds b^k ≤ x < b^(k+1)
  -- exists_nat_pow_bounds expects (b:ℝ)^k and (b:ℝ)^(k+1) which are Nat powers.
  rcases exists_nat_pow_bounds hb hx_ge_1 with ⟨k, h_bk_le_x, h_x_lt_bkp1⟩
  -- h_bk_le_x : (b:ℝ)^k ≤ x = (n:ℝ)^m
  -- h_x_lt_bkp1 : x = (n:ℝ)^m < (b:ℝ)^(k+1)

  -- Step 4: Convert Real bounds (involving Nat powers of casts) to Nat bounds
  let Bk := b ^ k
  let Nm := n ^ m
  let Bkp1 := b ^ (k + 1)
  have h_nat_bounds : Bk ≤ Nm ∧ Nm < Bkp1 :=
    nat_bounds_from_cast_pow_bounds h_bk_le_x h_x_lt_bkp1

  -- Step 5: Get f₀ H bounds from Nat bounds
  have h_f0_bounds := f0_bounds_from_nat_bounds hH h_nat_bounds.1 h_nat_bounds.2

  -- Step 6: Apply power law to get multiplication bounds
  have h_mul_bounds := f0_bounds_apply_power_law hH hn hm hb h_f0_bounds
  rcases h_mul_bounds with ⟨h_mul_le1, h_mul_le2⟩
  -- h_mul_le1: ↑k * f₀ H b ≤ ↑m * f₀ H n
  -- h_mul_le2: ↑m * f₀ H n ≤ (↑k + 1) * f₀ H b

  -- Step 7: Prepare for division
  have hf0b_pos : f₀ H b > 0 := uniformEntropy_pos_of_nontrivial hH hH_nonzero hb
  have hm_pos_real : 0 < (m : ℝ) := Nat.cast_pos.mpr (by linarith [hm] : m > 0)

  -- Step 8: Apply division logic
  -- Use the k found in Step 3
  use k
  constructor
  · -- Prove k / m ≤ f₀ H n / f₀ H b
    -- Start from h_mul_le1: k * f₀ H b ≤ m * f₀ H n
    -- Rewrite using mul_comm to match div_le_div_iff more easily
    rw [mul_comm (m : ℝ) _] at h_mul_le1 -- k * f₀ H b ≤ (f₀ H n) * m
    -- Use (a / d ≤ b / c ↔ a * c ≤ b * d) with a=k, d=m, b=f₀ H n, c=f₀ H b
    -- Need k * f₀ H b ≤ f₀ H n * m
    rwa [div_le_div_iff₀ hm_pos_real hf0b_pos] -- Goal: k / m ≤ f₀ H n / f₀ H b
  · -- Prove f₀ H n / f₀ H b ≤ (k + 1) / m
    -- Start from h_mul_le2: m * f₀ H n ≤ (↑k + 1) * f₀ H b
    -- Rewrite using mul_comm
    rw [mul_comm (m : ℝ) _] at h_mul_le2 -- (f₀ H n) * m ≤ (↑k + 1) * f₀ H b
    -- Use (b / c ≤ e / d ↔ b * d ≤ e * c) with b=f₀ H n, c=f₀ H b, e=k+1, d=m
    -- Need (f₀ H n) * m ≤ (k + 1) * f₀ H b
    rwa [div_le_div_iff₀ hf0b_pos hm_pos_real] -- Goal: f₀ H n / f₀ H b ≤ (k + 1) / m


/-! ## Chunk 3.4: logb properties -/

lemma one_le_implies_pos {x : ℝ} (hx : x ≥ 1) : 0 < x := by linarith

/-- Lemma: `logb b` is monotone increasing for base `b ≥ 2` and arguments ≥ 1. -/
lemma logb_le_logb_of_le {b : ℕ} {y z : ℝ} (hb : b ≥ 2) (hy : y ≥ 1) (hz : z ≥ 1) (h_le : y ≤ z) :
    Real.logb b y ≤ Real.logb b z := by
  -- Preconditions for Real.logb
  have hb_pos : 0 < (b : ℝ) := cast_pos_of_ge_two hb
  have hb_ne_one : (b : ℝ) ≠ 1 := ne_of_gt (one_lt_cast_of_ge_two hb)
  have hy_pos : 0 < y := one_le_implies_pos hy
  have hz_pos : 0 < z := one_le_implies_pos hz

  -- Use Real.logb_le_logb which requires base > 1
  have hb_gt_one : (b : ℝ) > 1 := one_lt_cast_of_ge_two hb
  exact (Real.logb_le_logb hb_gt_one hy_pos hz_pos).mpr h_le

/-! ### Chunk 3.4c: logb of a power -/

/-- Lemma: `logb b (b^k) = k` for Nat exponent k. -/
lemma logb_pow_eq_self {b k : ℕ} (hb : b ≥ 2) :
    Real.logb b ((b : ℝ) ^ k) = (k : ℝ) := by
  -- Need base > 0 and base ≠ 1 for logb
  have hb_pos : 0 < (b : ℝ) := cast_pos_of_ge_two hb
  have hb_ne_one : (b : ℝ) ≠ 1 := ne_of_gt (one_lt_cast_of_ge_two hb)

  -- Use Real.logb_rpow after casting k to ℝ using Real.rpow_nat_cast
  -- Rewrite the Nat power to Real power (rpow) using conv
  conv =>
    lhs       -- Focus on the left-hand side: logb (↑b) (↑b ^ k)
    arg 2     -- Focus on the second argument: ↑b ^ k
    rw [← Real.rpow_natCast (b : ℝ) k] -- Rewrite ↑b ^ k to ↑b ^ (↑k : ℝ) using the theorem backwards
  -- Goal is now logb (↑b) (↑b ^ (↑k : ℝ)) = ↑k

  -- Apply Real.logb_rpow, providing the required proofs for the base b (which is ↑b here)
  rw [Real.logb_rpow hb_pos hb_ne_one] -- Goal: ↑k = ↑k
  -- The proof is complete as the goal becomes an identity.

/-! ### Chunk 3.4d: Lower bound on k using logb -/




/-- Lemma: `k ≤ logb b x` given `(b : ℝ) ^ k ≤ x`. -/
lemma k_le_logb_rpow {b k : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1)
    (hk_le_x_pow : (b : ℝ) ^ k ≤ x) :
    (k : ℝ) ≤ Real.logb b x := by
  -- Apply logb b to both sides of hk_le_x_pow using monotonicity
  have h_logb_le : Real.logb b ((b : ℝ) ^ k) ≤ Real.logb b x := by
    apply logb_le_logb_of_le hb
    · -- Prove 1 ≤ (b:ℝ)^k using the helper lemma
      apply one_le_pow_of_one_le_real
      · exact Nat.one_le_cast.mpr (Nat.le_of_lt hb) -- Need base ≥ 1
      -- k is the exponent argument
    · exact hx -- Given x ≥ 1
    · exact hk_le_x_pow

  -- Simplify the LHS using logb_pow_eq_self (ensure it's defined above)
  have h_lhs_eq_k : Real.logb b ((b : ℝ) ^ k) = (k : ℝ) := logb_pow_eq_self hb

  -- Rewrite the LHS in the inequality
  rw [h_lhs_eq_k] at h_logb_le
  exact h_logb_le

-- Define define the lemma logb_lt_logb_of_lt using Real.logb_lt_logb and place it before its usage.
-- This lemma states that if b ≥ 2 and x, y ≥ 1, then logb b x < logb b y if x < y.
lemma logb_lt_logb_of_lt {b : ℝ} (hb : b ≥ 2) {x y : ℝ} (hx : x ≥ 1) (hxy : x < y) :
    Real.logb b x < Real.logb b y := by
  -- Preconditions for Real.logb_lt_logb
  have hb_gt_one : 1 < b := by linarith -- b ≥ 2 implies b > 1
  have hx_pos : 0 < x := one_le_implies_pos hx -- x ≥ 1 implies x > 0
  -- hy_pos is not directly needed by Real.logb_lt_logb signature but good practice

  -- Apply the lemma from Real.logb with the correct arguments
  apply Real.logb_lt_logb hb_gt_one hx_pos hxy

/-- Lemma: `logb b x < k + 1` given `x < (b : ℝ) ^ (k + 1)`. -/
lemma logb_rpow_lt_k_plus_1 {b k : ℕ} {x : ℝ} (hb_nat : b ≥ 2) (hx : x ≥ 1)
    (hx_lt_kp1 : x < (b : ℝ) ^ (k + 1)) :
    Real.logb b x < (k + 1 : ℝ) := by
  -- Cast b to Real for logb operations
  let b_real := (b : ℝ)
  have hb : b_real ≥ 2 := by exact Nat.cast_le.mpr hb_nat

  -- Apply logb b to both sides of hx_lt_kp1 using strict monotonicity
  have h_logb_lt : Real.logb b_real x < Real.logb b_real (b_real ^ (k + 1)) := by
    -- Apply the lemma directly with the available hypotheses
    apply logb_lt_logb_of_lt hb hx hx_lt_kp1
    -- Removed the incorrect proof steps that followed the apply

  -- Simplify the RHS using logb_pow_eq_self
  have h_rhs_eq_kp1 : Real.logb b_real (b_real ^ (k + 1)) = (k + 1 : ℝ) := by
    -- Rewrite the RHS goal `(k + 1 : ℝ)` to `↑(k + 1)` using Nat.cast_add_one backwards
    rw [← Nat.cast_add_one]
    -- Now the goal is `logb b_real (b_real ^ (k + 1)) = ↑(k + 1)`
    -- Since b_real = ↑b, this matches the type of logb_pow_eq_self
    exact logb_pow_eq_self hb_nat-- Corrected line

  -- Rewrite the RHS in the inequality
  rw [h_rhs_eq_kp1] at h_logb_lt
  exact h_logb_lt

lemma logb_rpow_bounds_k {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
    ∃ k : ℕ, Real.logb b x - 1 < (k : ℝ) ∧ (k : ℝ) ≤ Real.logb b x := by
  -- Use exists_nat_pow_bounds to find k such that b^k ≤ x < b^(k+1)
  rcases exists_nat_pow_bounds hb hx with ⟨k, h_bk_le_x, h_x_lt_bkp1⟩

  -- Prove the two inequalities for this k
  use k
  constructor
  · -- Prove logb b x - 1 < k
    -- Start from x < b^(k+1)
    have h_logb_lt_kp1 : Real.logb b x < (k + 1 : ℝ) := by
      apply logb_rpow_lt_k_plus_1 hb hx h_x_lt_bkp1
    -- The rewrite is not needed as ↑(k + 1) is often automatically ↑k + 1
    -- Subtract 1 from both sides using linarith
    linarith [h_logb_lt_kp1]
  · -- Prove k ≤ logb b x
    -- Start from b^k ≤ x
    have h_k_le_logb : (k : ℝ) ≤ Real.logb b x := by
      apply k_le_logb_rpow hb hx h_bk_le_x
    exact h_k_le_logb

/-- Lemma: `logb b (n^m) = m * logb b n` for Real exponent m.
Requires `b > 0`, `b ≠ 1` (implicit in `Real.logb`), and `n ≥ 1`. -/
lemma logb_rpow_eq_mul_logb {b n : ℕ} {m : ℝ} (hn : n ≥ 1) :
    Real.logb b ((n : ℝ) ^ m) = m * Real.logb b n := by
  -- Precondition required explicitly by the lemma Real.logb_rpow_eq_mul_logb_of_pos
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by linarith [hn] : n > 0)
  -- (Implicit preconditions 0 < ↑b and ↑b ≠ 1 are handled by logb's definition)

  -- Apply the lemma, providing only the required explicit argument hn_pos
  exact Real.logb_rpow_eq_mul_logb_of_pos hn_pos
  -- Lean matches the implicit b in the lemma with ↑b from the goal,
  -- x with ↑n, and y with m.

/-! ### Chunk 3.4h: Logarithmic Trapping - Final Bound -/

-- Assume lemmas from LogF.lean (like logb_rpow_eq_mul_logb etc.) are available

/-- Lemma: `logb b (n^m) = m * logb b n` for Nat exponent m. -/
lemma logb_pow_eq_mul_logb_nat {b n m : ℕ} (_hb : b ≥ 2) (_hn : n ≥ 1) : -- hb, hn proofs not needed by logb_pow
    Real.logb b ((n : ℝ) ^ m) = (m : ℝ) * Real.logb b n := by
  -- The goal is logb (↑b) (↑n ^ m) = ↑m * logb ↑b ↑n
  -- The lemma statement is logb b' (x' ^ k') = ↑k' * logb b' x'
  -- Unifying: b' = ↑b, x' = ↑n, k' = m
  -- The instantiated lemma statement is identical to the goal.
  exact Real.logb_pow (b : ℝ) (n : ℝ) m


/-! Step 1: Prove logb b x = m * logb b n -/
lemma prove_logb_x_eq {n m b : ℕ} (hn : n ≥ 1) (hb : b ≥ 2) (x : ℝ) (hx_def : x = (n : ℝ) ^ m) :
    Real.logb b x = (m : ℝ) * Real.logb b n := by
  -- Substitute the definition of x into the goal
  rw [hx_def] -- Goal: logb ↑b (↑n ^ m) = ↑m * logb ↑b ↑n
  -- Apply the lemma for Nat exponents
  exact logb_pow_eq_mul_logb_nat hb hn

-- Retry Step 1 using the corrected lemma name for Nat powers
lemma prove_logb_x_eq_nat {n m b : ℕ} (hn : n ≥ 1) (hb : b ≥ 2) (x : ℝ) (hx_def : x = (n : ℝ) ^ m) :
    Real.logb b x = (m : ℝ) * Real.logb b n := by
  rw [hx_def] -- Goal: logb ↑b (↑n ^ m) = ↑m * logb ↑b ↑n
  exact logb_pow_eq_mul_logb_nat hb hn

/--
Lemma: Guarantees the existence of `k : ℕ` satisfying both the power bounds
`(b : ℝ) ^ k ≤ (n : ℝ) ^ m ∧ (n : ℝ) ^ m < (b : ℝ) ^ (k + 1)`
and the ratio bounds derived from `uniformEntropy_ratio_bounds_by_rational`.
This lemma essentially packages the result of `uniformEntropy_ratio_bounds_by_rational` along
with the power bounds used to derive it.
-/
lemma k_from_f0_trap_satisfies_pow_bounds (hH : IsEntropyFunction H) (hH_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0)
    {n m b : ℕ} (hn : n ≥ 1) (hm : m ≥ 1) (hb : b ≥ 2) :
    ∃ k : ℕ,
      -- Power bounds
      ((b : ℝ) ^ k ≤ (n : ℝ) ^ m ∧ (n : ℝ) ^ m < (b : ℝ) ^ (k + 1)) ∧
      -- Ratio bounds
      ((k : ℝ) / m ≤ f₀ H n / f₀ H b ∧ f₀ H n / f₀ H b ≤ (k + 1 : ℝ) / m) := by
  -- Step 1 & 2: Define x = (n:ℝ)^m (Nat power) and prove x ≥ 1.
  let x : ℝ := (n : ℝ) ^ m
  have hx_ge_1 : x ≥ 1 := one_le_pow_cast hn

  -- Step 3: Get k and power bounds b^k ≤ x < b^(k+1) using exists_nat_pow_bounds
  rcases exists_nat_pow_bounds hb hx_ge_1 with ⟨k, h_bk_le_x, h_x_lt_bkp1⟩
  -- h_bk_le_x : (b:ℝ)^k ≤ x = (n:ℝ)^m
  -- h_x_lt_bkp1 : x = (n:ℝ)^m < (b:ℝ)^(k+1)

  -- Claim existence of this specific k
  use k

  -- Prove the conjunction: (Power bounds) ∧ (Ratio bounds)
  constructor
  · -- Prove Power bounds: These are exactly h_bk_le_x and h_x_lt_bkp1
    exact ⟨h_bk_le_x, h_x_lt_bkp1⟩
  · -- Prove Ratio bounds: This follows the logic from uniformEntropy_ratio_bounds_by_rational proof for *this* k

    -- Step 4: Convert Real bounds (involving Nat powers of casts) to Nat bounds
    let Bk := b ^ k
    let Nm := n ^ m
    let Bkp1 := b ^ (k + 1)
    have h_nat_bounds : Bk ≤ Nm ∧ Nm < Bkp1 :=
      nat_bounds_from_cast_pow_bounds h_bk_le_x h_x_lt_bkp1

    -- Step 5: Get f₀ H bounds from Nat bounds
    have h_f0_bounds := f0_bounds_from_nat_bounds hH h_nat_bounds.1 h_nat_bounds.2

    -- Step 6: Apply power law to get multiplication bounds
    have h_mul_bounds := f0_bounds_apply_power_law hH hn hm hb h_f0_bounds
    rcases h_mul_bounds with ⟨h_mul_le1, h_mul_le2⟩
    -- h_mul_le1: ↑k * f₀ H b ≤ ↑m * f₀ H n
    -- h_mul_le2: ↑m * f₀ H n ≤ (↑k + 1) * f₀ H b

    -- Step 7: Prepare for division (need f₀ H b > 0 and m > 0)
    have hf0b_pos : f₀ H b > 0 := uniformEntropy_pos_of_nontrivial hH hH_nonzero hb
    have hm_pos_real : 0 < (m : ℝ) := Nat.cast_pos.mpr (by linarith [hm] : m > 0)

    -- Step 8: Apply division logic to get the ratio bounds
    constructor
    · -- Prove k / m ≤ f₀ H n / f₀ H b
      -- Start from h_mul_le1: k * f₀ H b ≤ m * f₀ H n
      rw [mul_comm (m : ℝ) _] at h_mul_le1 -- k * f₀ H b ≤ (f₀ H n) * m
      -- Use (a / d ≤ b / c ↔ a * c ≤ b * d) with a=k, d=m, b=f₀ H n, c=f₀ H b
      rwa [div_le_div_iff₀ hm_pos_real hf0b_pos] -- Goal: k / m ≤ f₀ H n / f₀ H b
    · -- Prove f₀ H n / f₀ H b ≤ (k + 1) / m
      -- Start from h_mul_le2: m * f₀ H n ≤ (↑k + 1) * f₀ H b
      rw [mul_comm (m : ℝ) _] at h_mul_le2 -- (f₀ H n) * m ≤ (↑k + 1) * f₀ H b
      -- Use (b / c ≤ e / d ↔ b * d ≤ e * c) with b=f₀ H n, c=f₀ H b, e=k+1, d=m
      rwa [div_le_div_iff₀ hf0b_pos hm_pos_real] -- Goal: f₀ H n / f₀ H b ≤ (k + 1) / m

/--
Lemma: If `k` satisfies the power bounds `(b : ℝ) ^ k ≤ x < (b : ℝ) ^ (k + 1)`,
then `k` also satisfies the logarithmic bounds `logb b x - 1 < k` and `k ≤ logb b x`.
-/
lemma logb_x_bounds_k {b k : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1)
    (h_pow_bounds : (b : ℝ) ^ k ≤ x ∧ x < (b : ℝ) ^ (k + 1)) :
    Real.logb b x - 1 < (k : ℝ) ∧ (k : ℝ) ≤ Real.logb b x := by
  -- Deconstruct the power bounds
  rcases h_pow_bounds with ⟨h_lower_pow, h_upper_pow⟩

  -- Prove the two required inequalities
  constructor
  · -- Prove logb b x - 1 < k
    -- Use the upper power bound: x < b^(k+1)
    have h_logb_lt_kp1 : Real.logb b x < (k + 1 : ℝ) := by
      apply logb_rpow_lt_k_plus_1 hb hx h_upper_pow
    -- Rearrange using linarith
    linarith [h_logb_lt_kp1]
  · -- Prove k ≤ logb b x
    -- Use the lower power bound: b^k ≤ x
    have h_k_le_logb : (k : ℝ) ≤ Real.logb b x := by
      apply k_le_logb_rpow hb hx h_lower_pow
    exact h_k_le_logb

/--
Lemma: Translates bounds on `logb b x` in terms of `k` to bounds on
`m * logb b n` using the identity `logb b x = m * logb b n` where `x = (n:ℝ)^m`.
-/
lemma logb_n_times_m_bounds_k {n m b k : ℕ} (hn : n ≥ 1) (hb : b ≥ 2)
    (x : ℝ) (hx_def : x = (n : ℝ) ^ m)
    (h_logb_x_bounds : Real.logb b x - 1 < (k : ℝ) ∧ (k : ℝ) ≤ Real.logb b x) :
    (m : ℝ) * Real.logb b n - 1 < (k : ℝ) ∧ (k : ℝ) ≤ (m : ℝ) * Real.logb b n := by
  -- Prove the identity logb b x = m * logb b n
  have h_logb_x_eq : Real.logb b x = (m : ℝ) * Real.logb b n := by
    apply prove_logb_x_eq_nat hn hb x hx_def

  -- Rewrite the logb expression in the hypothesis bounds using the identity
  rw [h_logb_x_eq] at h_logb_x_bounds

  -- The hypothesis now directly matches the goal
  exact h_logb_x_bounds

/--
Lemma: Converts bounds involving `m * logb b n` to bounds involving `logb b n`
by dividing by `m`. Requires `m ≥ 1`.
-/
lemma logb_n_bounds_k_div_m {n m b k : ℕ} (_hn : n ≥ 1) (_hb : b ≥ 2) (hm : m ≥ 1)
    (h_logb_nm_bounds : (m : ℝ) * Real.logb b n - 1 < (k : ℝ) ∧ (k : ℝ) ≤ (m : ℝ) * Real.logb b n) :
    Real.logb b n - 1 / (m : ℝ) < (k : ℝ) / (m : ℝ) ∧ (k : ℝ) / (m : ℝ) ≤ Real.logb b n := by
  -- Deconstruct the input hypothesis
  rcases h_logb_nm_bounds with ⟨h_lower_mul, h_upper_mul⟩

  -- Need m > 0 for division properties
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (by linarith [hm] : m > 0)

  constructor
  · -- Prove logb b n - 1 / m < k / m
    calc
      Real.logb b n - 1 / (m : ℝ) = ((m : ℝ) * Real.logb b n - 1) / m := by
        field_simp [hm_pos, mul_comm] -- Added mul_comm
      -- Use div_lt_div_iff_of_pos_right, which requires a < b to prove a / c < b / c
      _ < (k : ℝ) / m := by exact (div_lt_div_iff_of_pos_right hm_pos).mpr h_lower_mul

  · -- Prove k / m ≤ logb b n
    -- Use div_le_iff₀' which states (a / c ≤ b ↔ a ≤ c * b) for c > 0.
    -- Let a = k, c = m, b = logb b n.
    -- Goal is k / m ≤ logb b n. The lemma rewrites this to k ≤ m * logb b n.
    -- This is exactly h_upper_mul.
    exact (div_le_iff₀' hm_pos).mpr h_upper_mul



/-! ### Chunk 3.4 - Breakdown Step 5 - Helper 4: Real Arithmetic Equivalence -/
lemma lt_add_iff_sub_left_real (a b c : ℝ) : a < b + c ↔ a - c < b := by
  -- Prove forward direction: a < b + c → a - c < b
  apply Iff.intro
  · intro h
    calc
      a - c < b + c - c := by exact sub_lt_sub_right h c
      _ = b := by ring -- Simplifies b + c - c to b
  · -- Prove backward direction: a - c < b → a < b + c
    intro h
    calc
      a = a - c + c := by ring -- Rewrite a
      _ < b + c := by exact add_lt_add_right h c

/-! ### Chunk 3.4 - Breakdown Step 5 - Helper 5: Negation of Division -/
lemma helper_neg_div (a b : ℝ) : -(a / b) = -a / b := by
  field_simp -- Try field_simp first


lemma helper_neg_sub (a b : ℝ) : -(a - b) = b - a := by
  exact neg_sub a b

/--
Lemma: Proves the lower bound part of the absolute difference inequality.
Combines the lower bound on the f₀ ratio (`k/m ≤ f0_ratio`)
and the upper bound relating `logb` to `k/m` (`logb - 1/m < k/m`).
Uses helper lemmas for arithmetic and transitivity.
-/
lemma prove_diff_lower_bound {f0_ratio logb_val k_val m_val : ℝ}
    (h_f0_lower : k_val / m_val ≤ f0_ratio)
    (h_logb_upper_shifted : logb_val - 1 / m_val < k_val / m_val) :
    -1 / m_val < f0_ratio - logb_val := by
  -- 1. Combine the hypotheses using transitivity
  have h_trans : logb_val - 1 / m_val < f0_ratio :=
    lt_of_lt_of_le h_logb_upper_shifted h_f0_lower

  -- 2. Rearrange h_trans: logb_val - 1 / m_val < f0_ratio
  -- Use `sub_lt_iff_lt_add`: logb_val < f0_ratio + 1 / m_val
  have h_step2 : logb_val < f0_ratio + 1 / m_val := by
    exact (sub_lt_iff_lt_add).mp h_trans -- Changed to sub_lt_iff_lt_add (no prime)

  -- Rewrite h_step2 to match the expected form for lt_add_iff_sub_left_real
  rw [add_comm] at h_step2 -- Now h_step2 : logb_val < 1 / m_val + f0_ratio

  -- 3. Rearrange h_step2: logb_val < 1 / m_val + f0_ratio
  -- Use custom `lt_add_iff_sub_left_real`: logb_val - f0_ratio < 1 / m_val
  -- Lemma: a < b + c ↔ a - c < b. Here a=logb_val, b=1/m_val, c=f0_ratio
  have h_step3 : logb_val - f0_ratio < 1 / m_val := by
    exact (lt_add_iff_sub_left_real logb_val (1 / m_val) f0_ratio).mp h_step2 -- Use the rewritten h_step2

  -- 4. Rearrange h_step3: logb_val - f0_ratio < 1 / m_val
  -- Multiply by -1 and flip inequality
  have h_step4_raw : -(1 / m_val) < -(logb_val - f0_ratio) := by
    exact neg_lt_neg_iff.mpr h_step3

  -- 5. Simplify LHS using helper_neg_div
  have h_step5 : -1 / m_val < -(logb_val - f0_ratio) := by
    rw [helper_neg_div 1 m_val] at h_step4_raw
    exact h_step4_raw

  -- 6. Simplify RHS using helper_neg_sub
  have h_step6 : -1 / m_val < f0_ratio - logb_val := by
    rw [helper_neg_sub logb_val f0_ratio] at h_step5
    exact h_step5

  -- 7. Check goal
  exact h_step6

lemma le_add_iff_sub_left_real (a b c : ℝ) : a ≤ b + c ↔ a - b ≤ c := by
  apply Iff.intro
  · intro h -- a ≤ b + c
    calc
      a - b ≤ (b + c) - b := by exact sub_le_sub_right h b
      _ = c := by ring
  · intro h -- a - b ≤ c
    calc
      a = a - b + b := by ring
      _ ≤ c + b := by exact add_le_add_right h b
      _ = b + c := by rw [add_comm]

/--
Lemma: Proves the upper bound part of the absolute difference inequality.
Combines the upper bound on the f₀ ratio (`f0_ratio ≤ (k+1)/m`)
and the lower bound relating `logb` to `k/m` (`k/m ≤ logb`).
Uses helper lemmas for arithmetic and transitivity.
-/
lemma prove_diff_upper_bound {f0_ratio logb_val k_val m_val : ℝ}
    (h_f0_upper : f0_ratio ≤ (k_val + 1) / m_val)
    (h_km_le_logb : k_val / m_val ≤ logb_val) :
    f0_ratio - logb_val ≤ 1 / m_val := by

  -- 1. Rewrite the upper bound on f0_ratio to isolate k/m
  have h_f0_upper_rewritten : f0_ratio ≤ k_val / m_val + 1 / m_val := by
    rw [add_div] at h_f0_upper -- Rewrite (k+1)/m as k/m + 1/m
    exact h_f0_upper

  -- 2. Combine inequalities using transitivity
  -- We have f0_ratio ≤ k/m + 1/m and k/m ≤ logb_val
  have h_trans : f0_ratio ≤ logb_val + 1 / m_val := by
    calc
      f0_ratio ≤ k_val / m_val + 1 / m_val := h_f0_upper_rewritten
      -- Apply `add_le_add_right`: If k/m ≤ logb_val, then k/m + 1/m ≤ logb_val + 1/m
      _ ≤ logb_val + 1 / m_val := by exact add_le_add_right h_km_le_logb (1 / m_val)

  -- 3. Rearrange h_trans: f0_ratio ≤ logb_val + 1 / m_val
  -- Use helper `le_add_iff_sub_left_real`: a ≤ b + c ↔ a - b ≤ c
  -- Let a = f0_ratio, b = logb_val, c = 1 / m_val
  exact (le_add_iff_sub_left_real f0_ratio logb_val (1 / m_val)).mp h_trans


/--
Theorem: Establishes that the difference between the normalized `f₀ H n` ratio
and the logarithm `logb b n` is bounded by `1/m`. This is the key result
showing `f₀` behaves like `log`.
Requires H to be non-trivial (`hH_nonzero`).
-/
theorem logarithmic_trapping (hH : IsEntropyFunction H) (hH_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0)
    {n m b : ℕ} (hn : n ≥ 1) (hm : m ≥ 1) (hb : b ≥ 2) :
    |f₀ H n / f₀ H b - Real.logb b n| ≤ 1 / (m : ℝ) := by

  -- Steps 1-5: Obtain k and the bounds (as before)
  rcases k_from_f0_trap_satisfies_pow_bounds hH hH_nonzero hn hm hb with
    ⟨k, ⟨h_pow_bounds_le, h_pow_bounds_lt⟩, ⟨h_ratio_lower, h_ratio_upper⟩⟩
  let x : ℝ := (n : ℝ) ^ m
  have hx_ge_1 : x ≥ 1 := one_le_pow_cast hn
  have h_logb_x_bounds : Real.logb b x - 1 < (k : ℝ) ∧ (k : ℝ) ≤ Real.logb b x := by
    apply logb_x_bounds_k hb hx_ge_1; exact ⟨h_pow_bounds_le, h_pow_bounds_lt⟩
  have h_logb_nm_bounds : (m : ℝ) * Real.logb b n - 1 < (k : ℝ) ∧ (k : ℝ) ≤ (m : ℝ) * Real.logb b n := by
    apply logb_n_times_m_bounds_k hn hb x (Eq.refl x) h_logb_x_bounds
  have h_logb_n_div_bounds : Real.logb b n - 1 / (m : ℝ) < (k : ℝ) / (m : ℝ) ∧ (k : ℝ) / (m : ℝ) ≤ Real.logb b n := by
    apply logb_n_bounds_k_div_m hn hb hm h_logb_nm_bounds
  rcases h_logb_n_div_bounds with ⟨h_logb_upper_shifted, h_km_le_logb⟩

  -- Step 6 & 7: Prove the lower bound on the difference (as before)
  have h_diff_lower : -1 / (m : ℝ) < f₀ H n / f₀ H b - Real.logb b n := by
    apply prove_diff_lower_bound (f0_ratio := f₀ H n / f₀ H b) (logb_val := Real.logb b n) (k_val := k) (m_val := m)
    · exact h_ratio_lower
    · exact h_logb_upper_shifted

  -- Step 8: Prove the upper bound on the difference (as before)
  have h_diff_upper : f₀ H n / f₀ H b - Real.logb b n ≤ 1 / (m : ℝ) := by
    apply prove_diff_upper_bound (f0_ratio := f₀ H n / f₀ H b) (logb_val := Real.logb b n) (k_val := k) (m_val := m)
    · exact h_ratio_upper
    · exact h_km_le_logb

  -- Step 9: Combine bounds using abs_le.mpr
  -- Goal: |f₀ H n / f₀ H b - Real.logb b n| ≤ 1 / (m : ℝ)
  -- Use `abs_le.mpr : (-y ≤ x ∧ x ≤ y) → |x| ≤ y`
  apply abs_le.mpr
  -- Need to prove: - (1 / m) ≤ (f₀ H n / f₀ H b - Real.logb b n) ∧ (f₀ H n / f₀ H b - Real.logb b n) ≤ 1 / m
  constructor
  · -- Prove Left Goal: - (1 / m) ≤ (f₀ H n / f₀ H b - Real.logb b n)
    -- Rewrite the goal using neg_div to match h_diff_lower
    rw [← neg_div] -- Goal is now: -1 / m ≤ ...
    -- We have h_diff_lower : -1 / m < ...
    -- Use `le_of_lt`
    exact le_of_lt h_diff_lower
  · -- Prove Right Goal: (f₀ H n / f₀ H b - Real.logb b n) ≤ 1 / m
    -- This is exactly h_diff_upper
    exact h_diff_upper

/-! ### Chunk 3.5 - Limit Argument Helpers -/

/--
Lemma (Archimedean Helper): For any `ε > 0`, there exists a natural number `m ≥ 1`
such that `1 / (m : ℝ) ≤ ε`.
-/
lemma exists_one_le_nat_one_div_le {ε : ℝ} (hε : ε > 0) :
    ∃ m : ℕ, m ≥ 1 ∧ 1 / (m : ℝ) ≤ ε := by
  -- Use the Archimedean property to find a natural k such that 1 / (k + 1) < ε
  rcases exists_nat_one_div_lt hε with ⟨k, hk⟩
  -- Let m = k + 1
  let m := k + 1
  -- Claim existence of this m
  use m
  -- Prove the two required properties: m ≥ 1 and 1 / m ≤ ε
  constructor
  · -- Prove m ≥ 1
    exact Nat.succ_pos k -- k + 1 is always ≥ 1 for any Nat k
  · -- Prove 1 / m ≤ ε
    -- We have hk : 1 / (↑k + 1) < ε
    -- Substitute m = k + 1 into hk
    have h_one_div_m_lt_ε : 1 / (m : ℝ) < ε := by
      -- Simplify the goal using the definition of m
      simp only [m]
      -- Rewrite ↑(k + 1) using Nat.cast_add_one
      rw [Nat.cast_add_one k]
      -- Apply the hypothesis hk
      exact hk
    -- Use le_of_lt to convert the strict inequality to ≤
    exact le_of_lt h_one_div_m_lt_ε


/--
Lemma (Core Limit Argument): If the absolute difference between two real numbers `x` and `y`
is bounded by `1/m` for all natural numbers `m ≥ 1`, then `x` must equal `y`.
-/
lemma eq_of_abs_sub_le_inv_ge_one_nat {x y : ℝ} (h_bound : ∀ m : ℕ, m ≥ 1 → |x - y| ≤ 1 / (m : ℝ)) :
    x = y := by
  -- Use the metric space lemma eq_of_forall_dist_le
  -- The goal becomes: ∀ ε > 0, dist x y ≤ ε
  apply eq_of_forall_dist_le
  -- Introduce arbitrary ε > 0
  intro ε hε
  -- Show dist x y ≤ ε
  -- For Real numbers, dist x y = |x - y|
  simp_rw [dist_eq_norm_sub, Real.norm_eq_abs] -- Goal: |x - y| ≤ ε
  -- Use the Archimedean helper to find m ≥ 1 such that 1 / m ≤ ε
  rcases exists_one_le_nat_one_div_le hε with ⟨m, hm_ge_1, h_inv_m_le_ε⟩
  -- Use the hypothesis h_bound for this specific m
  have h_abs_le_inv_m : |x - y| ≤ 1 / (m : ℝ) := h_bound m hm_ge_1
  -- Combine the two inequalities using transitivity
  exact le_trans h_abs_le_inv_m h_inv_m_le_ε -- |x - y| ≤ 1 / m and 1 / m ≤ ε implies |x - y| ≤ ε


/--
Lemma (Apply Limit to Trapping): Shows that the ratio `f₀ H n / f₀ H b` is exactly
equal to `logb b n`. Assumes `H` is non-trivial.
-/
lemma uniformEntropy_ratio_eq_logb (hH : IsEntropyFunction H) (hH_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0)
    {n b : ℕ} (hn : n ≥ 1) (hb : b ≥ 2) :
    f₀ H n / f₀ H b = Real.logb b n := by
  -- Apply the limit lemma eq_of_abs_sub_le_inv_ge_one_nat
  -- Let x = f₀ H n / f₀ H b and y = Real.logb b n
  apply eq_of_abs_sub_le_inv_ge_one_nat
  -- The goal becomes: ∀ m : ℕ, m ≥ 1 → |f₀ H n / f₀ H b - Real.logb b n| ≤ 1 / (m : ℝ)
  -- This is precisely the statement provided by logarithmic_trapping for any m ≥ 1
  intro m hm
  exact logarithmic_trapping hH hH_nonzero hn hm hb


-- Replacements for Mathlib3 lemmas that are not in Mathlib4 yet
lemma pos_of_ge_one {x : ℝ} (h : 1 ≤ x) : 0 < x :=
  lt_of_lt_of_le zero_lt_one h

lemma pos_of_one_le {n : ℕ} (h : 1 ≤ n) : 0 < n :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one h

lemma logb_eq_log {b x : ℝ} :
    logb b x = log x / log b := by
  rw [logb]

-- Replacement for logb_eq_log_div_log
lemma f0_ratio_eq_log_ratio (hH : IsEntropyFunction H) (hH_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0)
    {n b : ℕ} (hn : n ≥ 1) (hb : b ≥ 2) :
    f₀ H n / f₀ H b = Real.log n / Real.log b := by
  -- Step 1: Get the previous equality involving logb
  have h_eq_logb : f₀ H n / f₀ H b = Real.logb b n := by
    exact uniformEntropy_ratio_eq_logb hH hH_nonzero hn hb

  -- Step 2: Establish preconditions for Real.logb_eq_log
  have hb_pos_real : 0 < (b : ℝ) := cast_pos_of_ge_two hb
  have hb_ne_one_real : (b : ℝ) ≠ 1 := ne_of_gt (one_lt_cast_of_ge_two hb)
  -- Correctly prove 0 < n (Nat) from hn : n ≥ 1 (Nat)
  have hn_pos_nat : 0 < n := pos_of_one_le hn
  -- Use Nat.cast_pos.mpr with the correct Nat proof
  have hn_pos_real : 0 < (n : ℝ) := Nat.cast_pos.mpr hn_pos_nat

  -- Step 3: Rewrite logb using Real.logb_eq_log
  have h_logb_rewrite : Real.logb b n = Real.log n / Real.log b := by
    exact logb_eq_log

  -- Step 4: Substitute the rewritten logb into the equality from Step 1
  rw [h_eq_logb, h_logb_rewrite]

/--
Definition: The constant `C` relating `f₀` to `log`.
It is defined as `f₀ H 2 / log 2` if the entropy function `H` is non-trivial
(meaning `f₀` is not identically zero for `n ≥ 1`), and `0` otherwise.
We use base `b=2` for the definition.
-/
noncomputable def C_constant (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ) : ℝ :=
  -- Explicitly use Classical.propDecidable for the condition so we don't have to Open Classical
  let _inst : Decidable (∃ n' ≥ 1, f₀ H n' ≠ 0) := Classical.propDecidable _
  if _h : ∃ n' ≥ 1, f₀ H n' ≠ 0 then
    f₀ H 2 / Real.log 2
  else
    0


/--
Lemma: The constant `C` relating `f₀` to `log` is non-negative.
-/
lemma C_constant_nonneg (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ) (hH : IsEntropyFunction H) :
    C_constant H ≥ 0 := by
  -- Unfold the definition of C_constant
  rw [C_constant]
  -- Split the proof based on the if condition
  split_ifs with h_nonzero
  · -- Case 1: H is non-trivial (h_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0)
    -- Goal is: f₀ H 2 / Real.log 2 ≥ 0
    -- Prove numerator is non-negative
    have h_num_nonneg : f₀ H 2 ≥ 0 := by
      apply f0_nonneg hH
      norm_num -- Proves 2 ≥ 1
    -- Prove denominator is positive (which implies non-negative)
    have h_den_pos : Real.log 2 > 0 := by
      -- Use Real.log_pos which requires 2 > 1
      apply Real.log_pos
      norm_num -- Proves (2 : ℝ) > 1
    -- Apply div_nonneg (requires numerator non-negative, denominator non-negative)
    apply div_nonneg h_num_nonneg (le_of_lt h_den_pos)
  · -- Case 2: H is trivial (h_not_nonzero : ¬(∃ n' ≥ 1, f₀ H n' ≠ 0))
    -- Goal is: 0 ≥ 0
    exact le_refl 0

/-- Helper: f₀ H 2 is non-zero if H is non-trivial. -/
lemma f0_2_ne_zero (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ) (hH : IsEntropyFunction H)
    (h_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0) :
    f₀ H 2 ≠ 0 := by
  have hb2 : 2 ≥ 2 := by norm_num
  have h_pos : f₀ H 2 > 0 := uniformEntropy_pos_of_nontrivial hH h_nonzero hb2
  exact ne_of_gt h_pos

/-- Helper: log 2 is non-zero. -/
lemma log_2_ne_zero : Real.log 2 ≠ 0 := by
  have hb2 : 2 ≥ 2 := by norm_num
  have h_pos : Real.log 2 > 0 := log_b_pos hb2
  exact ne_of_gt h_pos

/--
Helper: Rearranges the equality `a / b = c / d` to `a = (b / d) * c`,
given denominators are non-zero.
-/
lemma rearrange_ratio_equality {a b c d : ℝ} (hb : b ≠ 0) (_hd : d ≠ 0)
    (h_ratio : a / b = c / d) :
    a = (b / d) * c := by
  -- Start from a / b = c / d
  -- Multiply both sides by b
  rw [div_eq_iff hb] at h_ratio
  -- h_ratio: a = (c / d) * b
  -- Rearrange RHS: (c / d) * b = (c * b) / d
  rw [div_mul_eq_mul_div] at h_ratio
  -- h_ratio: a = (c * b) / d
  -- Commute multiplication in numerator: (c * b) / d = (b * c) / d
  rw [mul_comm c b] at h_ratio
  -- h_ratio: a = (b * c) / d
  -- Associate division differently: (b * c) / d = (b / d) * c using div_mul_eq_mul_div
  -- This step implicitly uses hd ≠ 0
  rw [← div_mul_eq_mul_div] at h_ratio
  -- h_ratio: a = (b / d) * c
  exact h_ratio


/--
Helper Lemma: Explicitly proves that C_constant H equals the 'then' branch
of its definition when H is non-trivial.
-/
lemma C_constant_eq_term_A_of_nonzero (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ)
    (h_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0) :
    C_constant H = f₀ H 2 / Real.log 2 := by
  -- Unfold the definition of C_constant
  unfold C_constant
  -- Use the provided hypothesis h_nonzero to simplify the if statement
  exact if_pos h_nonzero

/--
Lemma: If the entropy function `H` is non-trivial, then `f₀ H n` equals
`C * Real.log n`, where `C` is the defined constant `C_constant H hH`.
Uses helper lemmas for clarity.
-/
lemma f0_eq_C_log_of_nonzero (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ) (hH : IsEntropyFunction H)
    (h_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0) {n : ℕ} (hn : n ≥ 1) :
    f₀ H n = C_constant H * Real.log n := by

  -- Step 1: Get the core relationship derived from ratios
  have hb2 : 2 ≥ 2 := by norm_num
  have h_ratio_eq : f₀ H n / f₀ H 2 = Real.log n / Real.log 2 := by
    exact f0_ratio_eq_log_ratio hH h_nonzero hn hb2
  have hf0_2_ne_zero : f₀ H 2 ≠ 0 := f0_2_ne_zero H hH h_nonzero
  have hlog2_ne_zero : Real.log 2 ≠ 0 := log_2_ne_zero
  have h_core_relation : f₀ H n = (f₀ H 2 / Real.log 2) * Real.log n := by
    exact rearrange_ratio_equality hf0_2_ne_zero hlog2_ne_zero h_ratio_eq

  -- Step 2: Establish that C_constant H equals the 'then' branch value
  have h_C_eq_A : C_constant H = f₀ H 2 / Real.log 2 := by
    exact C_constant_eq_term_A_of_nonzero H h_nonzero

  -- Step 3: Rewrite the LHS of the goal using the core relationship
  rw [h_core_relation]
  -- Goal is now: (f₀ H 2 / Real.log 2) * Real.log n = C_constant H * Real.log n

  -- Step 4: Rewrite the RHS of the goal using the equality for C_constant
  rw [h_C_eq_A]
  -- Goal is now: (f₀ H 2 / Real.log 2) * Real.log n = (f₀ H 2 / Real.log 2) * Real.log n

  -- Step 5: Close the goal by reflexivity
  --rfl

/--
Helper Lemma: If H is the trivial entropy function (f₀ H n = 0 for all n ≥ 1),
then f₀ H n is indeed 0 for any specific n ≥ 1.
-/
lemma f0_eq_zero_of_not_nonzero (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ)
    (h_not_nonzero : ¬(∃ n' ≥ 1, f₀ H n' ≠ 0)) {n : ℕ} (_hn : n ≥ 1) :
    f₀ H n = 0 := by
  -- Proof by contradiction
  by_contra h_f0_n_ne_zero
  -- Assume f₀ H n ≠ 0.
  -- Since n ≥ 1 (from hn), this provides a witness for the existence claim.
  have h_exists : ∃ n' ≥ 1, f₀ H n' ≠ 0 := by
    use n -- Use the specific n we are considering
    -- Need to provide proof of n ≥ 1 and f₀ H n ≠ 0
  -- This contradicts the main hypothesis h_not_nonzero
  exact h_not_nonzero h_exists

/--
Helper Lemma: Explicitly proves that C_constant H equals the 'else' branch (0)
of its definition when H is trivial.
-/
lemma C_constant_eq_zero_of_not_nonzero (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ)
    (h_not_nonzero : ¬(∃ n' ≥ 1, f₀ H n' ≠ 0)) :
    C_constant H = 0 := by
  -- Unfold the definition of C_constant
  unfold C_constant
  -- Use the provided hypothesis h_not_nonzero to simplify the if statement
  exact if_neg h_not_nonzero

/--
Lemma: If the entropy function `H` is trivial (f₀ H n = 0 for all n ≥ 1),
then `f₀ H n` equals `C * Real.log n`, where `C` is the defined constant (which is 0).
-/
lemma f0_eq_C_log_of_zero (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ) (_hH : IsEntropyFunction H)
    (h_not_nonzero : ¬(∃ n' ≥ 1, f₀ H n' ≠ 0)) {n : ℕ} (hn : n ≥ 1) :
    f₀ H n = C_constant H * Real.log n := by

  -- Step 1: Establish f₀ H n = 0 using the first helper
  have h_f0_n_zero : f₀ H n = 0 := by
    exact f0_eq_zero_of_not_nonzero H h_not_nonzero hn

  -- Step 2: Establish C_constant H = 0 using the second helper
  have h_C_zero : C_constant H = 0 := by
    exact C_constant_eq_zero_of_not_nonzero H h_not_nonzero

  -- Step 3: Rewrite the goal using these two facts
  rw [h_f0_n_zero, h_C_zero]
  -- Goal is now: 0 = 0 * Real.log n

  -- Step 4: Prove the final equality using symmetry
  exact Eq.symm (zero_mul (Real.log n))

/--
Helper Lemma: Combines the results for the non-trivial and trivial cases
to show that `f₀ H n = C * Real.log n` holds for all n ≥ 1.
-/
lemma f0_eq_C_log_cases (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ) (hH : IsEntropyFunction H)
    {n : ℕ} (hn : n ≥ 1) :
    f₀ H n = C_constant H * Real.log n := by
  -- Use classical logic to split on whether H is non-trivial
  apply Classical.by_cases
  · -- Case 1: Assume H is non-trivial (h_nonzero : ∃ ...)
    intro h_nonzero
    exact f0_eq_C_log_of_nonzero H hH h_nonzero hn
  · -- Case 2: Assume H is trivial (h_not_nonzero : ¬(∃ ...))
    intro h_not_nonzero
    exact f0_eq_C_log_of_zero H hH h_not_nonzero hn

/--
Helper Lemma: Connects the original function `f` (defined for `n > 0`)
to the extended function `f₀` (defined for all `n`).
-/
lemma f_eq_f0_for_positive_n (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ)
    {n : ℕ} (hn_pos : n > 0) :
    f H hn_pos = f₀ H n := by
  -- Unfold the definition of f₀ on the RHS
  rw [f₀]
  -- Goal is now: f H hn_pos = (dite (n > 0) (fun hn => f H hn) (fun _ => 0))
  -- Use the hypothesis hn_pos to simplify the 'dite' to the 'then' branch
  -- dif_pos rewrites (dite c t e) to t(hc) given hc : c
  rw [dif_pos hn_pos]

/-!
### Chunk 3.4 - Breakdown Step 5 - Main Theorem: Existence of C and log formula
Theorem (Chunk 3 Goal): There exists a non-negative constant `C` such that
for all `n > 0`, the entropy of the uniform distribution `f H n` is equal
to `C * log n`.
-/
theorem isCShannonEntropy (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ) (hH : IsEntropyFunction H) :
    ∃ C ≥ 0, ∀ n (hn : n > 0), f H hn = C * Real.log n := by
  -- Step 1: Define the constant C using the existing definition
  let C := C_constant H
  -- Step 2: Claim existence of this C
  use C

  -- Step 3: Prove the two required properties: C ≥ 0 and the universal quantification
  constructor
  · -- Prove C ≥ 0 using the previously proven lemma
    exact C_constant_nonneg H hH
  · -- Prove ∀ n > 0, f H ... = C * Real.log n
    -- Introduce arbitrary n and the hypothesis n > 0
    intro n hn_pos
    -- Goal: f H hn_pos = C * Real.log n

    -- Step 4: Connect f to f₀ using the helper lemma
    rw [f_eq_f0_for_positive_n H hn_pos]
    -- Goal: f₀ H n = C * Real.log n

    -- Step 5: Prove n ≥ 1 (needed for the next lemma)
    have hn_ge_1 : n ≥ 1 := Nat.one_le_of_lt hn_pos

    -- Step 6: Apply the lemma that combines the zero/non-zero cases
    exact f0_eq_C_log_cases H hH hn_ge_1

end PPNP.Entropy.Basic

export PPNP.Entropy.Basic (
  stdShannonEntropyLn
  IsEntropyFunction
  uniformProb
  sum_uniform_eq_one
  f
  f₀
  f0_1_eq_0
  f0_mono
)
