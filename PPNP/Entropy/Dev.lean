import Mathlib.Analysis.SpecialFunctions.Log.Basic -- Real.log
import Mathlib.Analysis.SpecialFunctions.Log.Base -- Real.logb
import Mathlib.Analysis.SpecialFunctions.Pow.Real -- Real.rpow
--import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Data.Complex.Basic -- For Complex.exp_re if needed
import Mathlib.Algebra.Order.Ring.Defs -- For OrderedSemiring properties like one_le_mul

-- import Mathlib.Analysis.SpecificLimits.Basic -- tendsto_one_div_atTop_zero
-- import Mathlib.Data.Real.Basic -- Basic Real properties

-- import Mathlib.Order.Filter.Basic -- Filter bases etc.
-- import Mathlib.Topology.Order.Basic -- OrderTopology
-- import Mathlib.Data.Nat.Basic -- Basic Nat properties
-- --import Mathlib.Data.Nat.Pow -- CAN NOT INCLUDE BECAUSE IT DOES NOT EXIST IN IN Lean 4.0
-- import Mathlib.Data.Nat.Log -- Nat.log
-- import Mathlib.Algebra.Order.Floor.Defs -- Floor definitions
-- -- Removed duplicate imports for Floor, Log.Base, Real.Basic, Linarith
-- import Mathlib.Tactic.Linarith -- Inequality solver
-- import Mathlib.Algebra.Ring.Nat -- For Nat.cast_pow
-- import Mathlib.Order.Monotone.Basic -- For Monotone definitions
-- import Mathlib.Algebra.Order.Field.Basic -- For div_le_div etc.
-- import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
-- import Mathlib.Algebra.Order.Monoid.Unbundled.Pow -- For one_le_pow_of_le

-- import Mathlib.Algebra.Order.Field.Basic

-- import Mathlib.Data.Real.Archimedean -- For Archimedean property if needed later
-- import Mathlib.Order.Bounds.Basic -- For properties involving bounds
-- import Mathlib.Analysis.Convex.Basic -- May be needed for abs_le_of_between_neg_le if not in Order
-- import Mathlib.Data.Nat.Cast.Order.Basic -- Provides Nat.cast_le, Nat.cast_lt and their mp versions

-- import Mathlib.Data.Real.Archimedean -- For Archimedean property if needed later
-- import Mathlib.Order.Bounds.Basic -- For properties involving bounds
-- import Mathlib.Analysis.Convex.Basic -- May be needed for abs_le_of_between_neg_le if not in Order
-- import Mathlib.Order.Interval.Set.Basic -- Contains abs_le_of_between_neg_le

-- Import previous definitions and theorems
import PPNP.Entropy.Basic
import PPNP.Entropy.PowerLaw
import PPNP.Entropy.LogF

namespace PPNP.Entropy

open BigOperators Fin Real Topology NNReal Filter Nat Set
open PPNP.Entropy.LogF
open PPNP.Entropy.PowerLaw


/-! ### Chunk 3.4h: Logarithmic Trapping - Final Bound -/

/-! ### Chunk 3.4 - Breakdown Step 5 -/

/-! ### Chunk 3.4 - Breakdown Step 5 -/

/-! ### Chunk 3.4 - Breakdown Step 6 - Helper 1: Algebraic Equivalence -/
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


/-! ### Chunk 3.4 - Final Assembly: The Logarithmic Trapping Theorem -/

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
