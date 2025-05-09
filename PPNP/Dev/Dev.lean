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
import PPNP.Entropy.Physics.BoseEinstein



namespace PPNP.Dev

open BigOperators Fin Real Topology NNReal Filter Nat Set Multiset


-- open PPNP.Common
-- open PPNP.Entropy.Common
-- open PPNP.Entropy.RET
-- open PPNP.Entropy.Physics.BE


/- PPNP.Entropy.Common - Phase 0 Revised/New Objects -/

open BigOperators Fin Real Topology NNReal Filter Nat
open PPNP.Common -- Assuming PPNP.Common contains finProdFinEquiv


/-
  Defines the joint probability distribution for a two-stage experiment.
  Given `prior` as the distribution for the first stage (over `N` outcomes),
  and `P i` as the conditional distribution for the second stage (over `M` outcomes)
  given the `i`-th outcome of the first stage.
  The resulting distribution is over the `N*M` combined outcomes.
  P(i,j) = prior(i) * P(j|i)
-/
noncomputable def DependentPairDist
  {N M : ℕ} [NeZero N] [NeZero M] -- Ensure N, M > 0 for finProdFinEquiv
  (prior : Fin N → NNReal)
  (P     : Fin N → Fin M → NNReal) :
  Fin (N * M) → NNReal :=
  fun k =>
    -- finProdFinEquiv : Fin N × Fin M ≃ Fin (N * M)
    -- Need to handle N=0 or M=0 cases if H is defined there.
    -- The IsEntropyCondAdd has [NeZero N] [NeZero M] constraints, so this should be fine.
    let k_equiv := Equiv.cast (congrArg Fin (Nat.mul_comm N M)) k
    let (i, j) := (finProdFinEquiv.symm k_equiv : Fin N × Fin M)
    prior i * P i j

/-- *Uniform distribution on a finite non-empty type.*
    The proof `h` guarantees the denominator is non-zero, so the inverse
    lives comfortably in `ℝ≥0`. -/
noncomputable def uniformDist {α : Type*} [Fintype α]
    (_h : 0 < Fintype.card α) : α → ℝ≥0 :=
λ _ ↦ (Fintype.card α : ℝ≥0)⁻¹


/-- The uniform distribution really is a probability distribution. -/
lemma sum_uniformDist {α : Type*} [Fintype α]
    (h : 0 < Fintype.card α) : (∑ x, uniformDist h x) = 1 := by
  have : (Fintype.card α : ℝ≥0) ≠ 0 :=
    by
      have : (Fintype.card α : ℕ) ≠ 0 := by
        exact Nat.ne_of_gt h
      simpa using this
  simp [uniformDist, Finset.card_univ, this]   -- 1 = n * (1/n)

-- 1) Declare the coercion instance
noncomputable instance {N M : ℕ} [NeZero N] [NeZero M] : Coe
  ((Fin N → NNReal) × (Fin N → Fin M → NNReal))
  (Fin (N * M) → NNReal) where
  coe := fun (⟨pr, P⟩ : (Fin N → NNReal) × (Fin N → Fin M → NNReal)) =>
    DependentPairDist pr P

structure IsEntropyNormalized
  (H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0)
: Prop where
  normalized : ∀ (p : Fin 1 → ℝ≥0), (∑ i, p i = 1) → H p = 0

structure IsEntropySymmetric
  (H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0)
: Prop where
  symmetry   : ∀ {α : Type} [Fintype α] (p : α → ℝ≥0) (_hp : ∑ i, p i = 1)
                  (σ : Equiv.Perm α), H (p ∘ σ) = H p -- Or p ∘ σ.invFun depending on convention

structure IsEntropyContinuous
  (H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0)
: Prop where
  continuity : ∀ {α : Type} [Fintype α] (p_center : α → ℝ≥0) (_hp_sum_1 : ∑ i, p_center i = 1)
                  (ε : ℝ), ε > 0 →
                ∃ δ > 0, ∀ (q : α → ℝ≥0) (_hq_sum_1 : ∑ i, q i = 1),
                (∀ i, |(q i : ℝ) - (p_center i : ℝ)| < δ) → |(H q : ℝ) - (H p_center : ℝ)| < ε
                -- Or better: ContinuousOn H (probabilitySimplexGen α)
                -- where probabilitySimplexGen α := {p : α → NNReal | ∑ i, p i = 1}
                -- and an appropriate topology on (α → NNReal)

structure IsEntropyCondAdd
  (H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0)
: Prop where
  cond_add :
    ∀ {N M : ℕ} [NeZero N] [NeZero M]
      (prior   : Fin N → NNReal)
      (P       : Fin N → Fin M → NNReal)
      (_hP      : ∀ i, ∑ j, P i j = 1)
      (_hprior  : ∑ i, prior i = 1),
    H (DependentPairDist prior P) = H prior + ∑ i, prior i * H (fun j => P i j)

structure IsEntropyZeroInvariance
  (H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0)
: Prop where
  zero_invariance :
    ∀ {n : ℕ} (p_orig : Fin n → NNReal) (_hp_sum_1 : ∑ i, p_orig i = 1),
      let p_ext := (fun (i : Fin (n + 1)) =>
                     if h_lt : i.val < n then p_orig (Fin.castLT i h_lt)
                     else 0)
      -- Lemma sum_p_ext_eq_one (if proven) would show p_ext sums to 1.
      -- We state it as a direct equality on H.
    H p_ext = H p_orig


structure IsEntropyContinuous_Old
  (H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0)
: Prop where
  continuity : ∀ {α : Type} [Fintype α] (p_center : α → ℝ≥0) (_hp_sum_1 : ∑ i, p_center i = 1)
                  (ε : ℝ), ε > 0 →
                ∃ δ > 0, ∀ (q : α → ℝ≥0) (_hq_sum_1 : ∑ i, q i = 1),
                (∀ i, |(q i : ℝ) - (p_center i : ℝ)| < δ) → |(H q : ℝ) - (H p_center : ℝ)| < ε
                -- Or better: ContinuousOn H (probabilitySimplexGen α)
                -- where probabilitySimplexGen α := {p : α → NNReal | ∑ i, p i = 1}
                -- and an appropriate topology on (α → NNReal)

/-- **Maximum-at-uniform axiom (Lean 4 version).**
    Any finite probability vector has entropy ≤ entropy of the uniform vector. -/
structure IsEntropyMaxUniform
  (H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0) : Prop where
  (max_uniform :
    ∀ {α : Type} [Fintype α] (h : 0 < Fintype.card α)
      (p : α → ℝ≥0) (_hphp : (∑ x, p x) = 1),
      H p ≤ H (uniformDist h))

/-- **Axiomatic Entropy Function.**
`IsEntropyFunction_New H` means `H` assigns an entropy value (ℝ≥0) to any finite probability distribution
such that the usual Shannon entropy axioms hold: normalization, symmetry, continuity,
and conditional additivity (chain rule). -/
structure IsEntropyFunction
  (H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0)
  : Prop                                -- ① result type comes *before* `extends`
  extends IsEntropyZeroInvariance H,
          IsEntropyNormalized H,
          IsEntropySymmetric H,
          IsEntropyContinuous H,
          IsEntropyCondAdd H,
          IsEntropyMaxUniform H


/-! ### Phase 2: Properties of `f(n) = H(uniform_n)` -/

/--
Defines `f H n = H(uniform distribution on n outcomes)`.
`H` is an entropy function satisfying `IsEntropyFunction`.
Requires `n > 0`. Output is `ℝ≥0`.
-/
noncomputable def f {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (_hH_axioms : IsEntropyFunction H) {n : ℕ} (hn_pos : n > 0) : ℝ≥0 :=
  -- Create the specific Fintype instance for Fin n
  let α := Fin n
  -- Prove Fintype.card (Fin n) > 0 from hn_pos
  have h_card_pos : 0 < Fintype.card α := by
    rw [Fintype.card_fin]
    exact hn_pos
  H (uniformDist h_card_pos)


/--
Defines `f0 H n` which extends `f H n` to include `n=0` by setting `f0 H 0 = 0`.
Output is `ℝ≥0`.
-/
noncomputable def f0 {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) (n : ℕ) : ℝ≥0 :=
  if hn_pos : n > 0 then f hH_axioms hn_pos else 0

/--
Helper lemma: The uniform distribution on `Fin 1` is `λ _ => 1`.
-/
lemma uniformDist_fin_one_eq_dist_one :
    uniformDist (by {rw [Fintype.card_fin]; exact Nat.one_pos} : 0 < Fintype.card (Fin 1)) =
    (fun (_ : Fin 1) => 1) := by
  funext x -- Apply functional extensionality
  simp only [uniformDist, Fintype.card_fin, Nat.cast_one, inv_one]

/--
Helper lemma: The distribution `λ (_ : Fin 1) => 1` sums to 1.
-/
lemma sum_dist_one_fin_one_eq_1 :
    (∑ (_ : Fin 1), (1 : ℝ≥0)) = 1 := by
  simp [Finset.sum_const, Finset.card_fin, Nat.cast_one, nsmul_one]


/--
Property: `f0 H 1 = 0`.
This follows from the `normalized` axiom of `IsEntropyFunction`.
-/
theorem f0_1_eq_0_new {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) : f0 hH_axioms 1 = 0 := by
  have h1_pos : 1 > 0 := Nat.one_pos
  -- Unfold f0 using h1_pos
  simp only [f0, dif_pos h1_pos]
  -- Unfold f
  simp only [f]
  -- Rewrite the uniform distribution on Fin 1
  rw [uniformDist_fin_one_eq_dist_one]
  -- Apply the normalization axiom
  exact hH_axioms.normalized (fun (_ : Fin 1) => 1) sum_dist_one_fin_one_eq_1


/--
If `p_orig` sums to `1` on `Fin n`, the extension that appends a zero at
index `n` still sums to `1`.  This Lean 4 version uses
`Fin.sum_univ_castSucc` directly. -/
lemma sum_p_ext_eq_one_of_sum_p_orig_eq_one
    {n : ℕ} (p_orig : Fin n → ℝ≥0) (hp : ∑ i, p_orig i = 1) :
    (∑ i : Fin (n + 1),
        (if h : (i : ℕ) < n then p_orig (Fin.castLT i h) else 0)) = 1 := by
  -- Define the extended vector once so we can name it.
  set p_ext : Fin (n + 1) → ℝ≥0 :=
      fun i => if h : (i : ℕ) < n then p_orig (Fin.castLT i h) else 0

  -- Canonical split of the sum over `Fin (n+1)`.
  have h_split :
      (∑ i, p_ext i) =
        (∑ i : Fin n, p_ext i.castSucc) + p_ext (Fin.last n) := by
        rw [Fin.sum_univ_castSucc]

  -- The new last entry is zero.
  have h_last : p_ext (Fin.last n) = 0 := by
    simp [p_ext]

  -- The first summand coincides with the original sum.
  have h_cast :
      (∑ i : Fin n, p_ext i.castSucc) = ∑ i : Fin n, p_orig i := by
    apply Finset.sum_congr rfl
    intro i _
    have : ((i.castSucc : Fin (n + 1)) : ℕ) < n := by
      rw [Fin.castSucc] -- Goal becomes i.val < n
      exact i.is_lt         -- Proof of i.val < n
    simp [p_ext, this, Fin.castLT_castSucc]

  -- Put the pieces together.
  simp [h_split, h_last, h_cast, hp, p_ext]


/--
Property: `f0 H n` is monotone non-decreasing.
Uses `zero_invariance` and `max_uniform` axioms.
-/
theorem f0_mono_new {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) : Monotone (f0 hH_axioms) := by
  apply monotone_nat_of_le_succ
  intro n
  -- Case n = 0
  if hn_is_zero : n = 0 then
    rw [hn_is_zero] -- Goal: f0 hH_axioms 0 ≤ f0 hH_axioms (0 + 1)
    simp [Nat.add_zero] -- Goal: f0 hH_axioms 0 ≤ f0 hH_axioms 1

    -- Simplify RHS using f0_1_eq_0_new
    have h0_1_eq_0 : f0 hH_axioms 1 = 0 := f0_1_eq_0_new hH_axioms
    rw [h0_1_eq_0] -- Goal: f0 hH_axioms 0 ≤ 0

    -- Simplify LHS: f0 hH_axioms 0 is 0 by definition of f0
    simp [f0, Nat.not_lt_zero] -- Goal: 0 ≤ 0
  else
    -- Case n > 0
    have hn_pos : n > 0 := Nat.pos_of_ne_zero hn_is_zero
    have hn1_pos : n + 1 > 0 := Nat.succ_pos n

    -- Unfold f0 for n and n+1
    rw [f0, dif_pos hn_pos, f0, dif_pos hn1_pos]
    -- Goal: f hH_axioms hn_pos ≤ f hH_axioms hn1_pos
    -- This is H (uniformDist_on_Fin_n) ≤ H (uniformDist_on_Fin_{n+1})

    -- Let unif_n be the uniform distribution on Fin n
    let α_n := Fin n
    have h_card_n_pos : 0 < Fintype.card α_n := by
      unfold α_n
      simp only [Fintype.card_fin, hn_pos]
    let unif_n_dist := uniformDist h_card_n_pos

    -- Let p_ext be unif_n_dist extended with a zero to Fin (n+1)
    let p_ext : Fin (n+1) → NNReal :=
      fun (i : Fin (n+1)) => if h_lt : i.val < n then unif_n_dist (Fin.castLT i h_lt) else 0

    -- Show p_ext sums to 1
    have h_sum_unif_n_dist : (∑ i, unif_n_dist i) = 1 := sum_uniformDist h_card_n_pos
    have h_sum_p_ext_eq_1 : (∑ i, p_ext i) = 1 :=
      sum_p_ext_eq_one_of_sum_p_orig_eq_one unif_n_dist h_sum_unif_n_dist

    -- Relate H p_ext to H unif_n_dist using zero_invariance
    -- hH_axioms.zero_invariance requires p_orig (unif_n_dist) and its sum.
    have h_H_p_ext_eq_H_unif_n : H p_ext = H unif_n_dist := by
      -- The let binding in zero_invariance means we need to match the definition
      -- or prove our p_ext is equivalent to the one in the axiom.
      -- The axiom structure is:
      -- zero_invariance: ∀ {m : ℕ} (p_orig_ax : Fin m → NNReal) (_hp_sum_1_ax : ∑ i, p_orig_ax i = 1),
      --   let p_ext_ax := (fun (i : Fin (m + 1)) => ...); H p_ext_ax = H p_orig_ax
      -- Here, m = n, p_orig_ax = unif_n_dist.
      -- Our p_ext is definitionally the same as p_ext_ax.
      exact hH_axioms.zero_invariance unif_n_dist h_sum_unif_n_dist

    -- Relate H p_ext to H (uniformDist_on_Fin_{n+1}) using max_uniform
    let α_n1 := Fin (n+1)
    have h_card_n1_pos : 0 < Fintype.card α_n1 := by
      unfold α_n1
      simp only [Fintype.card_fin, hn1_pos]
    let unif_n1_dist := uniformDist h_card_n1_pos

    have h_H_p_ext_le_H_unif_n1 : H p_ext ≤ H unif_n1_dist := by
      -- max_uniform: ∀ {α} [Fintype α] (h_card_α_pos) (p_check) (h_sum_p_check), H p_check ≤ H (uniformDist h_card_α_pos)
      -- Here, α = Fin (n+1), p_check = p_ext.
      exact hH_axioms.max_uniform h_card_n1_pos p_ext h_sum_p_ext_eq_1

    -- Combine: H unif_n_dist = H p_ext ≤ H unif_n1_dist
    -- The goal is f hH_axioms hn_pos ≤ f hH_axioms hn1_pos.
    -- We show this is definitionally H unif_n_dist ≤ H unif_n1_dist.
    change H unif_n_dist ≤ H unif_n1_dist
    rw [← h_H_p_ext_eq_H_unif_n] -- Goal is now H p_ext ≤ H unif_n1_dist
    exact h_H_p_ext_le_H_unif_n1
