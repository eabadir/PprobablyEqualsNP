import Mathlib.Analysis.SpecialFunctions.Log.Basic -- Real.log
import Mathlib.Data.Complex.Basic -- For Complex.exp_re if needed
import Mathlib.Analysis.SpecialFunctions.Pow.Real -- Real.rpow
import Mathlib.Analysis.SpecificLimits.Basic -- tendsto_one_div_atTop_zero
import Mathlib.Data.Real.Basic -- Basic Real properties
import Mathlib.Order.Filter.Basic -- Filter bases etc.
import Mathlib.Topology.Order.Basic -- OrderTopology
import Mathlib.Data.Nat.Log -- Nat.log
import Mathlib.Algebra.Order.Floor -- Nat.floor, Nat.lt_floor_add_one etc. (different from Defs/Ring/Semiring)
-- 'Mathlib.Algebra.Order.Floor' has been deprecated: please replace this import by

-- import Mathlib.Algebra.Order.Floor.Defs
-- import Mathlib.Algebra.Order.Floor.Ring
-- import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Base -- Real.logb
import Mathlib.Tactic.Linarith -- Inequality solver
import Mathlib.Analysis.SpecialFunctions.Log.Base -- Real.logb, Real.log
import Mathlib.Analysis.SpecialFunctions.Log.Basic -- Real.log properties
import Mathlib.Data.Real.Basic -- Basic Real properties
import Mathlib.Tactic.Linarith -- Inequality solver

-- Import previous definitions and theorems
import PPNP.Entropy.Basic
import PPNP.Entropy.PowerLaw

open PPNP.Entropy.Basic PPNP.Entropy.Pow

namespace PPNP.Entropy.LogF

open BigOperators Fin Real Topology NNReal Filter Nat Set

-- Assume H satisfies the properties for the rest of the proofs
variable {H : ∀ {n : ℕ}, (Fin n → NNReal) → Real} (hH : IsEntropyFunction H)

-- Code from Chunk 3.1 ... (C_const, log_b_pos, f0_nonneg, C_const_nonneg) ...

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
lemma rpow_nat_floor_logb_le_x {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
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
lemma x_lt_rpow_succ_floor_logb {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
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

/-- Lemma: For any `x ≥ 1` and integer `b ≥ 2`, there exists an integer `k` such that `b^k ≤ x < b^(k+1)`. This `k` is `floor(log_b(x))`. -/
lemma exists_k_log_bounds {b : ℕ} {x : ℝ} (hb : b ≥ 2) (hx : x ≥ 1) :
  ∃ k : ℕ, (b : ℝ) ^ k ≤ x ∧ x < (b : ℝ) ^ (k + 1) := by
  -- Define k as the floor of log base b of x
  let k := Nat.floor (Real.logb b x)
  -- Claim existence of this k
  use k
  -- Prove the two inequalities
  constructor
  · -- Prove (b : ℝ) ^ k ≤ x
    exact rpow_nat_floor_logb_le_x hb hx
  · -- Prove x < (b : ℝ) ^ (k + 1)
    exact x_lt_rpow_succ_floor_logb hb hx

/-!
Chunk 3.2 Completed. `exists_k_log_bounds` is proven using helper lemmas.
Next Step: Chunk 3.3 - Inequalities from Trapping
-/

end PPNP.Entropy.LogF
