-- import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog -- For negMulLog, Real.log
-- import Mathlib.Data.NNReal.Basic -- For NNReal
-- import Mathlib.Topology.Basic -- For ContinuousOn (placeholder)
-- import Mathlib.Order.Monotone.Basic -- For Monotone
-- import Mathlib.Algebra.BigOperators.Fin -- For sum over Fin n
-- import Mathlib.Data.Fin.Basic -- Basic Fin definitions and lemmas
-- import Mathlib.Data.Fintype.Fin -- Instances for Fin n
-- import Mathlib.Algebra.Order.Field.Basic -- For inv_one etc.
-- import Mathlib.Algebra.GroupWithZero.Units.Basic -- Provides mul_inv_cancel₀
-- import Mathlib.Analysis.SpecialFunctions.Log.Base -- Real.logb
-- import Mathlib.Analysis.SpecialFunctions.Pow.Real -- Real.rpow
-- import Mathlib.Data.Complex.Basic -- For Complex.exp_re if needed
-- import Mathlib.Analysis.SpecificLimits.Basic -- tendsto_one_div_atTop_zero
-- import Mathlib.Data.Real.Basic -- Basic Real properties
-- import Mathlib.Order.Filter.Basic -- Filter bases etc.
-- import Mathlib.Topology.Order.Basic -- OrderTopology
-- import Mathlib.Data.Nat.Basic -- Basic Nat properties
-- import Mathlib.Data.Nat.Log -- Nat.log
-- import Mathlib.Algebra.Order.Floor.Defs -- Floor definitions
-- import Mathlib.Tactic.Linarith -- Inequality solver
-- import Mathlib.Algebra.Ring.Nat -- For Nat.cast_pow
-- import Mathlib.Logic.Equiv.Fin.Basic
-- import Mathlib.Logic.Equiv.Defs
-- import Mathlib.GroupTheory.Congruence.Basic

-- import Mathlib.Data.Multiset.Bind
-- import Mathlib.Data.Multiset.Basic
-- import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- Import previous definitions and theorems
import PPNP.Common.Basic
import PPNP.Entropy.RET
import PPNP.Entropy.Physics.BoseEinstein

namespace PPNP.Entropy

open BigOperators Fin Real Topology NNReal Filter Nat Set Multiset

open PPNP.Common
open PPNP.Entropy.RET
open PPNP.Entropy.Physics.BE


lemma stdShannonEntropyLn_uniform_eq_log_k {k : ℕ} (hk_pos : k > 0) :
    stdShannonEntropyLn (fun _ : Fin k => uniformProb k) = Real.log k := by
  simp_rw [stdShannonEntropyLn, uniformProb, dif_pos hk_pos]
  -- Goal: ∑ _i : Fin k, negMulLog (↑↑k⁻¹ : ℝ) = Real.log k
  rw [Finset.sum_const]
  -- Goal: k * negMulLog (↑↑k⁻¹ : ℝ) = Real.log k
  simp_rw [negMulLog, mul_ite, mul_zero] -- Handle the if inside negMulLog
  -- Need (↑↑k⁻¹ : ℝ) > 0, which is true since k > 0
  have h_inv_pos : (↑(k : ℝ≥0)⁻¹ : ℝ) > 0 := by
    rw [NNReal.coe_pos, NNReal.inv_pos]
    exact Nat.cast_pos.mpr hk_pos
  rw [if_pos h_inv_pos]
  -- Goal: k * (- (↑↑k⁻¹ : ℝ) * Real.log (↑↑k⁻¹ : ℝ)) = Real.log k
  rw [NNReal.coe_nat_cast k, NNReal.coe_inv] -- ↑k * (- (↑k)⁻¹ * Real.log (↑k)⁻¹)
  rw [Real.log_inv (Nat.cast_ne_zero_iff_pos.mpr hk_pos)] -- log (1/k) = -log k
  -- Goal: k * (- (↑k)⁻¹ * (-Real.log k)) = Real.log k
  rw [mul_neg, mul_neg, neg_neg] -- k * (↑k)⁻¹ * Real.log k
  rw [← mul_assoc, mul_inv_cancel (Nat.cast_ne_zero_iff_pos.mpr hk_pos), one_mul]
  -- Goal: Real.log k = Real.log k
  rfl
