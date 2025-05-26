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

open BigOperators Fin Real Topology NNReal Filter Nat Function
open PPNP.Common

universe u

-- Definition: f(n) = H(uniform distribution on n outcomes)
noncomputable def uniformProb (n : ℕ) : NNReal :=
  if _hn : n > 0 then (n⁻¹ : NNReal) else 0

/-- *Uniform distribution on a finite non-empty type.*
    The proof `h_card_pos` guarantees the denominator is non-zero. -/
noncomputable def uniformDist {α : Type*} [Fintype α]
    (_h_card_pos : 0 < Fintype.card α) : α → NNReal :=
λ _ ↦ (Fintype.card α : NNReal)⁻¹


/-- The uniform distribution sums to 1. -/
lemma sum_uniformDist {α : Type*} [Fintype α]
    (h_card_pos : 0 < Fintype.card α) : (∑ x, uniformDist h_card_pos x) = 1 := by
  have h_card_nnreal_ne_zero : (Fintype.card α : NNReal) ≠ 0 := by
      have h_card_nat_ne_zero : (Fintype.card α : ℕ) ≠ 0 := Nat.ne_of_gt h_card_pos
      simpa using h_card_nat_ne_zero
  simp only [uniformDist, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_inv_cancel₀ h_card_nnreal_ne_zero]

/--
Helper lemma: If `k > 0`, then `0 < Fintype.card (Fin k)`.
This provides a clean proof term for the positivity argument required by `uniformDist`.
-/
lemma Fintype_card_fin_pos {k : ℕ} (hk_pos : k > 0) : 0 < Fintype.card (Fin k) := by
  simp only [Fintype.card_fin] -- Fintype.card (Fin k) is definitionally k
  exact hk_pos

/-- Standard Shannon entropy of `p : α → NNReal`. Uses natural logarithm. -/
noncomputable def stdShannonEntropyLn {α : Type*} [Fintype α] (p : α → NNReal) : Real :=
  ∑ i : α, negMulLog (p i : Real)



/-- The set of valid probability distributions over `Fin n`. -/
def probabilitySimplex {n : ℕ} : Set (Fin n → NNReal) :=
  { p | ∑ i, p i = 1 }

/-- Product distribution `P((i,j)) = p(i)q(j)` for independent `p` and `q`. -/
noncomputable def product_dist {n m : ℕ} (p : Fin n → NNReal) (q : Fin m → NNReal) : Fin (n * m) → NNReal :=
  fun k =>
    let k' : Fin (m * n) := Equiv.cast (congrArg Fin (Nat.mul_comm n m)) k
    let ji := finProdFinEquiv.symm k'
    p ji.2 * q ji.1


/-- Joint distribution `P(k) = prior(i) * P(j|i)` where `k` maps to `(i,j)`. -/
noncomputable def DependentPairDist
  {N M : ℕ} [NeZero N] [NeZero M]
  (prior : Fin N → NNReal)
  (P     : Fin N → Fin M → NNReal) :
  Fin (N * M) → NNReal :=
  fun k =>
    let k_equiv := Equiv.cast (congrArg Fin (Nat.mul_comm N M)) k
    let (i, j) := (finProdFinEquiv.symm k_equiv : Fin N × Fin M)
    prior i * P i j

/-- Coercion for `DependentPairDist`. -/
noncomputable instance {N M : ℕ} [NeZero N] [NeZero M] : Coe
  ((Fin N → NNReal) × (Fin N → Fin M → NNReal))
  (Fin (N * M) → NNReal) where
  coe := fun (⟨pr, P_cond⟩ : (Fin N → NNReal) × (Fin N → Fin M → NNReal)) => -- Renamed P to P_cond
    DependentPairDist pr P_cond

-- noncomputable instance {α β : Type*} :
--   CoeTC ((β → NNReal) × (α ≃ β)) (α → NNReal) where
--   coe := fun (⟨p, e⟩ : (β → NNReal) × (α ≃ β)) => p ∘ e

-- Component Structures for HasRotaEntropyProperties
-- H maps (α → NNReal) to NNReal.

structure IsEntropyNormalized
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) -- Renamed H to H_func
: Prop where
  normalized : ∀ (p : Fin 1 → NNReal), (∑ i, p i = 1) → H_func p = 0

structure IsEntropySymmetric
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) : Prop where
  symmetry :
    ∀ {α β : Type} [Fintype α] [Fintype β]
      (p_target : β → NNReal) (_hp : ∑ y, p_target y = 1)
      (e : α ≃ β),
      H_func (α := α) (fun x : α => p_target (e x)) =
      H_func (α := β) p_target

structure IsEntropyContinuous
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) -- Renamed H to H_func
: Prop where
  continuity : ∀ {α : Type} [Fintype α] (p_center : α → NNReal) (_hp_sum_1 : ∑ i, p_center i = 1)
                  (ε : ℝ), ε > 0 →
                ∃ δ > 0, ∀ (q : α → NNReal) (_hq_sum_1 : ∑ i, q i = 1),
                (∀ i, |(q i : ℝ) - (p_center i : ℝ)| < δ) → |((H_func q) : ℝ) - ((H_func p_center) : ℝ)| < ε
                -- Assuming H_func output is NNReal, so coercion to ℝ is needed for absolute difference.

structure IsEntropyCondAdd
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) -- Renamed H to H_func
: Prop where
  cond_add :
    ∀ {N M : ℕ} [NeZero N] [NeZero M]
      (prior   : Fin N → NNReal)
      (P_cond  : Fin N → Fin M → NNReal) -- Renamed P to P_cond
      (_hP_sum_1 : ∀ i, ∑ j, P_cond i j = 1)
      (_hprior_sum_1 : ∑ i, prior i = 1),
    H_func (DependentPairDist prior P_cond) = H_func prior + ∑ i, prior i * H_func (fun j => P_cond i j)
    -- Sum term: prior i is NNReal, H_func output is NNReal. Product is NNReal. Sum is NNReal.
    -- H_func prior is NNReal. So RHS is NNReal. LHS H_func output is NNReal. Consistent.

structure IsEntropyZeroInvariance
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) -- Renamed H to H_func
: Prop where
  zero_invariance :
    ∀ {n : ℕ} (p_orig : Fin n → NNReal) (_hp_sum_1 : ∑ i, p_orig i = 1),
      let p_ext := (fun (i : Fin (n + 1)) =>
                     if h_lt : i.val < n then p_orig (Fin.castLT i h_lt)
                     else 0)
    H_func p_ext = H_func p_orig


-- In PPNP.Entropy.Common.lean, add this structure:
structure IsEntropyZeroOnEmptyDomain
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) : Prop where
  apply_to_empty_domain : H_func Fin.elim0 = 0
  -- Fin.elim0 here denotes the unique function Fin 0 → NNReal.
  -- The specific instance H_func {α := Fin 0} [Fintype (Fin 0)] Fin.elim0 is used.



structure IsEntropyMaxUniform
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) : Prop where -- Renamed H to H_func
  max_uniform :
    ∀ {α : Type} [Fintype α] (h_card_pos : 0 < Fintype.card α)
      (p : α → NNReal) (_hp_sum_1 : (∑ x, p x) = 1),
      H_func p ≤ H_func (uniformDist h_card_pos)

/--
Generalized joint distribution (dependent pair distribution) over a sigma type.
`P(⟨i,j⟩) = prior(i) * P_cond(i)(j)`.
The type of `j` depends on `i` via `M_map i`.
Requires `Fintype` instances for `Fin N` and `Fin (M_map i)`.
Implicitly, `N > 0` if `prior` is on `Fin N` and non-trivial.
If `M_map i = 0`, then `Fin (M_map i)` is empty, and no `j` exists for such `i`.
The domain `(Σ i : Fin N, Fin (M_map i))` will not contain pairs `⟨i,j⟩` if `M_map i = 0`.
-/
noncomputable def DependentPairDistSigma {N : ℕ}
    (prior : Fin N → NNReal) (M_map : Fin N → ℕ)
    (P_cond : Π (i : Fin N), (Fin (M_map i) → NNReal)) :
    (Σ i : Fin N, Fin (M_map i)) → NNReal :=
  fun sigma_pair => -- sigma_pair is ⟨i, j⟩ where j : Fin (M_map i)
    let i := sigma_pair.fst
    let j := sigma_pair.snd
    prior i * P_cond i j

-- ... (IsEntropyNormalized, IsEntropySymmetric, IsEntropyContinuous)

-- REMOVE/REPLACE old IsEntropyCondAdd
-- structure IsEntropyCondAdd ...

/--
Axiom for conditional additivity of entropy, generalized for Sigma types.
`H(P_joint) = H(P_prior) + ∑_i P_prior(i) * H(P_conditional_i)`.
Preconditions:
- `prior` must sum to 1.
- For each `i` where `prior i > 0`:
    - `M_map i` must be greater than 0 (so `Fin (M_map i)` is non-empty and `P_cond i` is on a non-empty type).
    - `P_cond i` (the conditional distribution for that `i`) must sum to 1.
If `prior i = 0`, the term `prior i * H_func (P_cond i)` is zero, so the properties of `P_cond i`
(like summing to 1 or `M_map i > 0`) for that specific `i` do not affect the sum's value.
However, `H_func (P_cond i)` still needs to be well-defined. If `M_map i = 0`, then `P_cond i`
is a distribution on `Fin 0`. `H_func` applied to this should be `f0 H_func 0 = 0`.
The axiom states the equality assuming these conditions are met by the caller.
-/
structure IsEntropyCondAddSigma
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) : Prop where -- Changed Type u to Type
  cond_add_sigma :
    ∀ {N : ℕ} [NeZero N] -- Ensures Fin N is non-empty, prior is on a meaningful domain
      (prior   : Fin N → NNReal) (M_map : Fin N → ℕ)
      (P_cond  : Π (i : Fin N), (Fin (M_map i) → NNReal))
      (_hprior_sum_1    : ∑ i, prior i = 1)
      (_hP_cond_props : ∀ i : Fin N, prior i > 0 → (M_map i > 0 ∧ ∑ j, P_cond i j = 1))
      (_hH_P_cond_M_map_zero_is_zero : ∀ i : Fin N, M_map i = 0 →
        @H_func (Fin (M_map i)) (Fin.fintype (M_map i)) (P_cond i) = 0),
    H_func (DependentPairDistSigma prior M_map P_cond) =
      H_func prior + ∑ i, prior i * H_func (P_cond i)

/--
**Axiomatic Entropy Function.** (Updated to use IsEntropyCondAddSigma)
`HasRotaEntropyProperties H_func` means `H_func` assigns `NNReal` to finite probability distributions,
satisfying normalization, symmetry, continuity, conditional additivity (sigma version),
zero invariance, and maximality at uniform.
-/
structure HasRotaEntropyProperties -- This is the new definition
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) -- Changed Type u to Type
  : Prop
  extends IsEntropyZeroInvariance H_func,
          IsEntropyNormalized H_func,
          IsEntropySymmetric H_func,
          IsEntropyContinuous H_func,
          IsEntropyCondAddSigma H_func, -- UPDATED
          IsEntropyMaxUniform H_func,
          IsEntropyZeroOnEmptyDomain H_func



lemma product_coe_inv_coe_mul_log_eq_log {k : ℕ} (hk_pos_nat : k > 0) :
    ((k : ℝ) * (k : ℝ)⁻¹) * Real.log k = Real.log k := by
  have hk_real_ne_zero : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk_pos_nat)
  rw [mul_inv_cancel₀ hk_real_ne_zero, one_mul]

theorem stdShannonEntropyLn_uniform_eq_log_card {α : Type*} [Fintype α]
    (h_card_pos : 0 < Fintype.card α) :
  stdShannonEntropyLn (uniformDist h_card_pos) = Real.log (Fintype.card α) := by
  let k := Fintype.card α
  have hk_pos_nat : k > 0 := h_card_pos

  -- Unfold the definition of Shannon entropy, uniformDist, negMulLog, and the
  -- real/Nnreal coercions all at once:
  simp [stdShannonEntropyLn, uniformDist, negMulLog_def, NNReal.coe_inv, NNReal.coe_natCast]

  -- Now the goal is
  --   (k : ℝ) * ((k : ℝ)⁻¹ * Real.log k) = Real.log k

  -- Rearrange and finish
  rw [← mul_assoc]
  exact product_coe_inv_coe_mul_log_eq_log hk_pos_nat


-- Axiom for Shannon Coding Theorem
/--
Axiomatic statement of Shannon's Coding Theorem (SCT).
It asserts that for any probability distribution P over a finite alphabet α,
there exists an optimal average code length (in bits) for encoding symbols
drawn i.i.d. from P, and this length is approximately the Shannon entropy of P (base 2).
The "≈" would be formalized using limits for block codes in a full version.
-/
axiom shannon_coding_theorem_sct_axiom
    {α : Type u} [Fintype α] (P : α → NNReal) (hP_sums_to_1 : ∑ x, P x = 1) :
    ∃ (L_avg_bits : ℝ), L_avg_bits ≥ 0 ∧
      -- For simplicity, we state it as equality for the ideal optimal code.
      -- A more nuanced version would use inequalities or limits.
      L_avg_bits = (stdShannonEntropyLn P) / (Real.log 2) -- Shannon entropy in bits
      -- Status: Axiom (To be added, e.g. in PPNP.Entropy.SCT)
