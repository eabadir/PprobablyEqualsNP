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

import PPNP.Common.Basic

namespace PPNP.Entropy.Common

open BigOperators Fin Real Topology NNReal Filter Nat
open PPNP.Common

-- Definition: f(n) = H(uniform distribution on n outcomes)
noncomputable def uniformProb (n : ℕ) : NNReal :=
  if _hn : n > 0 then (n⁻¹ : NNReal) else 0

/-- Standard Shannon entropy of a probability distribution given as a function `Fin n → NNReal`.
    Uses natural logarithm (base e). -/
noncomputable def stdShannonEntropyLn {n : ℕ} (p : Fin n → NNReal) : Real :=
  ∑ i : Fin n, negMulLog (p i : Real)

def probabilitySimplex {n : ℕ} : Set (Fin n → NNReal) :=
  { p | ∑ i, p i = 1 }

noncomputable def product_dist {n m : ℕ} (p : Fin n → NNReal) (q : Fin m → NNReal) : Fin (n * m) → NNReal :=
  fun k =>
    -- Assuming finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)
    -- Use its inverse finProdFinEquiv.symm : Fin (m * n) ≃ Fin m × Fin n
    -- Cast k : Fin (n * m) to k' : Fin (m * n) using Nat.mul_comm
    let k' : Fin (m * n) := Equiv.cast (congrArg Fin (Nat.mul_comm n m)) k
    -- Apply inverse to get pair of type Fin m × Fin n
    let ji := finProdFinEquiv.symm k'
    -- ji.1 has type Fin m
    -- ji.2 has type Fin n
    -- Match types: p needs Fin n (ji.2), q needs Fin m (ji.1)
    p ji.2 * q ji.1



-- Structure: Axiomatic Entropy Function H
structure IsEntropyFunction (H : ∀ {n : ℕ}, (Fin n → NNReal) → Real) where
  (prop0_H1_eq_0 : H (λ _ : Fin 1 => 1) = 0)
  (prop2_zero_inv : ∀ {n : ℕ} (p : Fin n → NNReal) (_ : ∑ i : Fin n, p i = 1),
      let p_ext := (λ i : Fin (n + 1) => if h : i.val < n then p (Fin.castLT i h) else 0)
      H p_ext = H p)
  (prop3_continuity : ∀ n : ℕ, ContinuousOn H (probabilitySimplex (n := n)))
  (prop4_additivity_product : ∀ {n m : ℕ} (p : Fin n → NNReal) (q : Fin m → NNReal) (_hp : ∑ i, p i = 1) (_hq : ∑ j, q j = 1),
    H (product_dist p q) = H p + H q)
  (prop5_max_uniform : ∀ {n : ℕ} (_hn_pos : n > 0) (p : Fin n → NNReal) (_hp_sum : ∑ i : Fin n, p i = 1),
      H p ≤ H (λ _ : Fin n => if _hn' : n > 0 then (n⁻¹ : NNReal) else 0)) -- NOTE: hn' check is redundant due to hn_pos


-- Helper lemma: the uniform distribution sums to 1
lemma sum_uniform_eq_one {n : ℕ} (hn : n > 0) :
  ∑ _i : Fin n, uniformProb n = 1 := by
  simp only [uniformProb, dif_pos hn]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [mul_inv_cancel₀]
  apply Nat.cast_ne_zero.mpr
  exact Nat.pos_iff_ne_zero.mp hn





/-- Product of two uniform distributions is uniform on the product space. -/
lemma uniformProb_product_uniformProb_is_uniformProb
    {n m : ℕ} (hn : n > 0) (hm : m > 0) :
    product_dist
        (fun _ : Fin n     => uniformProb n)
        (fun _ : Fin m     => uniformProb m)
      = (fun _ : Fin (n*m) => uniformProb (n * m)) := by
  -- point‑wise equality of functions on `Fin (n*m)`
  funext k
  /- 1 ▸ reduce to an identity in `ℝ≥0` -/
  simp [product_dist, uniformProb, mul_pos hn hm]  -- goal: ↑n⁻¹ * ↑m⁻¹ = ↑(n*m)⁻¹

  /- 2 ▸ build the `≠ 0` hypotheses in `ℝ≥0` via `exact_mod_cast` -/
  have hn_ne_zero : n ≠ 0 := (Nat.pos_iff_ne_zero).1 hn
  have hm_ne_zero : m ≠ 0 := (Nat.pos_iff_ne_zero).1 hm
  have h_n : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn_ne_zero  -- `norm_cast` trick :contentReference[oaicite:0]{index=0}
  have h_m : (m : ℝ≥0) ≠ 0 := by exact_mod_cast hm_ne_zero

  /- 3 ▸ convert the product of inverses to the inverse of a product -/
  -- The left factor is `↑m⁻¹ * ↑n⁻¹`, so we use the lemma with arguments in that order.
  rw [nnreal_inv_mul_inv_eq_inv_mul h_m h_n]

  /- 4 ▸ finish by rewriting inside the inverse and using commutativity -/
  rw [mul_comm] --`mul_comm` is a lemma that rewrites `a * b = b * a`
  simp [hn, hm, mul_comm, nnreal_coe_nat_mul n m]  -- evaluates the `if`s and rewrites `↑n * ↑m`
