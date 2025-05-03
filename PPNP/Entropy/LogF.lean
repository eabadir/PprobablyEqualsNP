import Mathlib.Analysis.SpecialFunctions.Log.Basic -- Real.log
import Mathlib.Analysis.SpecialFunctions.Log.Base -- Real.logb
import Mathlib.Analysis.SpecialFunctions.Pow.Real -- Real.rpow
import Mathlib.Data.Complex.Basic -- For Complex.exp_re if needed

import Mathlib.Analysis.SpecificLimits.Basic -- tendsto_one_div_atTop_zero
import Mathlib.Data.Real.Basic -- Basic Real properties
import Mathlib.Order.Filter.Basic -- Filter bases etc.
import Mathlib.Topology.Order.Basic -- OrderTopology
import Mathlib.Data.Nat.Basic -- Basic Nat properties
--import Mathlib.Data.Nat.Pow -- CAN NOT INCLUDE BECAUSE IT DOES NOT EXIST IN IN Lean 4.0
import Mathlib.Data.Nat.Log -- Nat.log
import Mathlib.Algebra.Order.Floor.Defs -- Floor definitions
-- Removed duplicate imports for Floor, Log.Base, Real.Basic, Linarith
import Mathlib.Tactic.Linarith -- Inequality solver
import Mathlib.Algebra.Ring.Nat -- For Nat.cast_pow
import Mathlib.Order.Monotone.Basic -- For Monotone definitions
import Mathlib.Algebra.Order.Field.Basic -- For div_le_div etc.

-- Import previous definitions and theorems
import PPNP.Entropy.Basic
import PPNP.Entropy.PowerLaw

open PPNP.Entropy.Basic PPNP.Entropy.PowerLaw

namespace PPNP.Entropy.LogF

open BigOperators Fin Real Topology NNReal Filter Nat Set

-- Assume H satisfies the properties for the rest of the proofs
variable {H : ∀ {n : ℕ}, (Fin n → NNReal) → Real} (hH : IsEntropyFunction H)

-- Code from Chunk 3.1 ... (C_const, log_b_pos, f0_nonneg, C_const_nonneg) ...
/- ### Chunk 3.3c: Breaking down f0_b_pos_of_non_zero -/


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
### Chunk 3.3a: Breaking down f0_b_pos_of_non_zero
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
### Chunk 3.3b: Breaking down f0_b_pos_of_non_zero
-/

/-- Lemma 2: If f₀ H 2 = 0, then f₀ H (2^k) = 0 for all k ≥ 1. -/
lemma f0_pow2_eq_zero_of_f0_2_eq_zero {k : ℕ} (hH : IsEntropyFunction H) (hf0_2_eq_0 : f₀ H 2 = 0) (hk : k ≥ 1) :
    f₀ H (2 ^ k) = 0 := by
  -- Apply the power law f₀(n^k) = k * f₀(n) with n=2
  have h_pow_law := f0_pow_eq_mul hH (by norm_num : 2 ≥ 1) hk
  -- h_pow_law : f₀ H (2 ^ k) = ↑k * f₀ H 2

  -- Substitute the assumption f₀ H 2 = 0
  rw [hf0_2_eq_0] at h_pow_law
  -- h_pow_law : f₀ H (2 ^ k) = ↑k * 0

  -- Simplify
  rw [mul_zero] at h_pow_law
  exact h_pow_law


/-!
### Chunk 3.3d: Breaking down f0_b_pos_of_non_zero
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
### Chunk 3.3e: Breaking down f0_b_pos_of_non_zero
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
lemma f0_b_pos_of_non_zero (hH : IsEntropyFunction H) (hH_nonzero : ∃ n ≥ 1, f₀ H n ≠ 0) (hb : b ≥ 2) :
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
  exact f0_pow_eq_mul hH hn hm

/-- Helper 4b: Apply power law to the left term f₀ H (b^k) when k ≥ 1. -/
lemma f0_pow_left_k_ge_1 (hH : IsEntropyFunction H) {b k : ℕ} (hb_ge1 : b ≥ 1) (hk_ge1 : k ≥ 1) :
    f₀ H (b ^ k) = (k : ℝ) * f₀ H b := by
  exact f0_pow_eq_mul hH hb_ge1 hk_ge1

/-- Helper 4c: Apply power law to the right term f₀ H (b^(k+1)) when k ≥ 0. -/
lemma f0_pow_right (hH : IsEntropyFunction H) {b k : ℕ} (hb_ge1 : b ≥ 1) :
    f₀ H (b ^ (k + 1)) = ((k : ℝ) + 1) * f₀ H b := by
  have hkp1_ge1 : k + 1 ≥ 1 := Nat.succ_pos k
  have raw_pow_law := f0_pow_eq_mul hH hb_ge1 hkp1_ge1 -- Gives ↑(k+1) * f₀ H b
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
theorem f0_trapping_inequalities (hH : IsEntropyFunction H) (hH_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0)
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
  have hf0b_pos : f₀ H b > 0 := f0_b_pos_of_non_zero hH hH_nonzero hb
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
and the ratio bounds derived from `f0_trapping_inequalities`.
This lemma essentially packages the result of `f0_trapping_inequalities` along
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
  · -- Prove Ratio bounds: This follows the logic from f0_trapping_inequalities proof for *this* k

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
    have hf0b_pos : f₀ H b > 0 := f0_b_pos_of_non_zero hH hH_nonzero hb
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


-- Assume lemmas from LogF.lean (like logb_rpow_eq_mul_logb etc.) are available
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
/-! ### Chunk 3.4 - Breakdown Step 5 - Helper 5: Negation of Division -/
lemma helper_neg_div (a b : ℝ) : -(a / b) = -a / b := by
  field_simp -- Try field_simp first

/-! ### Chunk 3.4 - Breakdown Step 5 - Helper 6: Negation of Subtraction -/
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
