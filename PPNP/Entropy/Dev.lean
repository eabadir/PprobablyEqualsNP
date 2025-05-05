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

-- Import previous definitions and theorems
import PPNP.Entropy.Basic

namespace PPNP.Entropy

open BigOperators Fin Real Topology NNReal Filter Nat Set
open PPNP.Entropy.Basic

def probabilitySimplex {n : ℕ} : Set (Fin n → NNReal) :=
  { p | ∑ i, p i = 1 }

#check finProdFinEquiv

lemma uniformProb_product_uniformProb_is_uniformProb {n m : ℕ} (hn : n > 0) (hm : m > 0) :
    product_dist (fun _ => uniformProb n) (fun _ => uniformProb m) = (fun _ => uniformProb (n * m)) := by
  funext k
  simp only [product_dist, uniformProb, dif_pos hn, dif_pos hm, dif_pos (mul_pos hn hm)]
  -- Goal: (uniformProb n) * (uniformProb m) = uniformProb (n * m)
  -- Which simplifies to: (↑n)⁻¹ * (↑m)⁻¹ = (↑(n * m))⁻¹
  rw [NNReal.inv_mul_inv₀] -- Goal: (↑n * ↑m)⁻¹ = (↑(n * m))⁻¹
  · -- Prove the arguments inside the inverse are equal
    apply congr_arg (fun x => x⁻¹) -- Apply inverse to both sides of the equality we want to prove
    exact NNReal.coe_nat_cast_mul n m -- Prove ↑n * ↑m = ↑(n * m)
  · -- Prove ↑n ≠ 0 for NNReal.inv_mul_inv₀
    exact NNReal.coe_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  · -- Prove ↑m ≠ 0 for NNReal.inv_mul_inv₀
    exact NNReal.coe_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
