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
import Mathlib.GroupTheory.Congruence.Basic

import Mathlib.Data.Sym.Card

import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import PPNP.Common.Basic
import PPNP.Entropy.Common
import PPNP.Entropy.RET
import PPNP.Entropy.Physics.Common
import PPNP.Entropy.Physics.BoseEinstein

import Mathlib.Algebra.Ring.Defs
--import PPNP.Entropy.Physics.BoseEinstein

-- simp made no progressLean 4
-- 'simp only [mul_neg, neg_neg]' tactic does nothing
-- note: this linter can be disabled with `set_option linter.unusedTactic false`Lean 4
-- mul_neg.{u} {α : Type u} [Mul α] [HasDistribNeg α] (a b : α) : a * -b = -(a * b)
-- import Mathlib.Algebra.Ring.Defs

namespace PPNP.Dev

open BigOperators Fin Real Topology NNReal Filter Nat Set Multiset


-- open PPNP.Common
-- open PPNP.Entropy.Common
-- open PPNP.Entropy.RET
-- open PPNP.Entropy.Physics.BE


/- PPNP.Entropy.Common - Phase 0 Revised/New Objects -/

open PPNP.Common PPNP.Entropy.Common PPNP.Entropy.RET PPNP.Entropy.Physics.BE


/--
The canonical uniform distribution on `Fin k`.
Defined as `fun (_ : Fin k) => (k : NNReal)⁻¹`.
This is a specialization of `uniformDist` for clarity and specific use with `Fin k`.
-/
noncomputable def canonicalUniformDist (k : ℕ) (hk_pos : k > 0) : Fin k → NNReal :=
  uniformDist (Fintype_card_fin_pos hk_pos)

/--
Proof that `canonicalUniformDist k hk_pos` sums to 1.
This directly uses `sum_uniformDist` with the appropriate proof of positivity
for `Fintype.card (Fin k)`.
-/
lemma sum_canonicalUniformDist_eq_one (k : ℕ) (hk_pos : k > 0) :
    (∑ i, canonicalUniformDist k hk_pos i) = 1 := by
  simp only [canonicalUniformDist] -- Unfold to uniformDist (Fintype_card_fin_pos hk_pos)
  exact sum_uniformDist (Fintype_card_fin_pos hk_pos)

/--
Symmetry of `stdShannonEntropyLn`: `stdShannonEntropyLn (p ∘ e) = stdShannonEntropyLn p`
for an `Equiv e : α ≃ β` between two Fintypes `α` and `β`,
and a target distribution `p_target : β → NNReal`.
The sum `∑ x:α, negMulLog(p_target(e x))` is transformed to `∑ y:β, negMulLog(p_target y)`.
-/
theorem stdShannonEntropyLn_comp_equiv {α β : Type*} [Fintype α] [Fintype β]
    (p_target : β → NNReal) (e : α ≃ β) :
    stdShannonEntropyLn (p_target ∘ e) = stdShannonEntropyLn p_target := by
  -- Unfold stdShannonEntropyLn on both sides to expose the sums.
  unfold stdShannonEntropyLn
  -- LHS: ∑ (x : α), negMulLog ((p_target (e x)) : ℝ)
  -- RHS: ∑ (y : β), negMulLog ((p_target y) : ℝ)
  -- Apply Function.comp_apply to the term inside the sum on the LHS.
  simp_rw [Function.comp_apply]
  -- LHS is now: ∑ (x : α), negMulLog ((p_target (e x)) : ℝ)
  -- Let g(y) := negMulLog ((p_target y) : ℝ).
  -- LHS is ∑ (x : α), g (e x).
  -- Equiv.sum_comp states: (∑ x, g (e x)) = (∑ y, g y).
  exact Equiv.sum_comp e (fun (y : β) => negMulLog ((p_target y) : ℝ))

-- We'll continue with `stdShannonEntropyLn_canonicalUniform_eq_log_k` and the main theorem
-- `H_uniform_mapped_dist_eq_C_shannon` once this part is verified.
