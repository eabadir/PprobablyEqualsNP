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


/-!
Helper function: Defines the product distribution P(i,j) = prior(i) * q_const(j)
using DependentPairDist where the conditional distribution P(j|i) is independent of i (i.e., P(j|i) = q_const(j)).
-/
noncomputable def dependentPairDist_of_independent
  {N M : ℕ} [hN : NeZero N] [hM : NeZero M]
  (prior : Fin N → NNReal) (q_const : Fin M → NNReal) :
  Fin (N * M) → NNReal :=
  @DependentPairDist N M hN hM prior (fun _i => q_const)


/--
If the weights `w` sum to `1`, the weighted sum `∑ w i * C`
collapses to the constant `C`.  (Lean-4 version, using
`Finset.sum_mul`.)
-/
lemma sum_weighted_constant {β : Type*} [Fintype β]
    {C : ℝ≥0} {w : β → ℝ≥0} (h : ∑ i, w i = 1) :
    (∑ i, w i * C) = C := by
  -- `Finset.sum_mul` gives  `(∑ i, w i) * C = ∑ i, w i * C`.
  -- We use it with `s = Finset.univ`.
  have : (∑ i, w i * C) = (∑ i : β, w i) * C := by
    simpa using
      (Finset.sum_mul (s := (Finset.univ : Finset β)) (f := w) C).symm
        -- `.symm` flips the direction so the RHS matches our goal. [oai_citation:0‡Lean Community](https://leanprover-community.github.io/mathlib_docs/algebra/big_operators/ring.html?utm_source=chatgpt.com) [oai_citation:1‡Hugging Face](https://huggingface.co/datasets/kfdong/STP_Lean_0320)
  -- Now `h : (∑ i, w i) = 1` finishes the job.
  simpa [h, one_mul] using this           -- closes the goal

/--
If the conditional distributions P(j|i) are all identical (i.e., P(j|i) = q_const(j) for all i),
then the conditional additivity axiom simplifies to H(joint) = H(prior) + H(q_const).
-/
lemma cond_add_for_independent_distributions
    {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H)
    {N M : ℕ} [NeZero N] [NeZero M]
    (prior : Fin N → NNReal) (q_const : Fin M → NNReal)
    (hprior_sum_1 : ∑ i, prior i = 1) (hq_const_sum_1 : ∑ j, q_const j = 1) :
    H (dependentPairDist_of_independent prior q_const)
      = H prior + H (α := Fin M) q_const := by   -- ← ① give `α` explicitly
  -- Unfold the joint distribution
  simp only [dependentPairDist_of_independent]

  -- Apply the chain-rule axiom
  rw [hH_axioms.cond_add
        prior (fun _ => q_const)
        (fun _ => hq_const_sum_1) hprior_sum_1]

  -- We now have:  `H prior + ∑ i, prior i * H (α := Fin M) q_const`
  --                = `H prior + H (α := Fin M) q_const`

  -- Cancel `H prior` on both sides and collapse the weighted sum
  have h_sum :
      (∑ i, prior i * H (α := Fin M) q_const) =
        H (α := Fin M) q_const :=
    sum_weighted_constant (β := Fin N) (C := H (α := Fin M) q_const)
                          (w := prior) hprior_sum_1
  have h_eta :
      H (fun j => q_const j) = H (α := Fin M) q_const := by
    rfl

  simp [h_sum, h_eta]     -- goal reduces to `rfl` and solves the proof

/-!
Constructs the joint probability distribution for two independent random variables,
where each variable follows a uniform distribution on `Fin N` and `Fin M` respectively.
The construction uses `dependentPairDist_of_independent`, with the prior being
`uniformDist` on `Fin N` and the constant conditional distribution being `uniformDist` on `Fin M`.
This helper function allows inspection of the resulting joint distribution.
-/
noncomputable def DependentPairDist_of_independent_helper
  {N M : ℕ} (hN_pos : N > 0) (hM_pos : M > 0) :
  Fin (N * M) → NNReal :=
  -- Ensure NeZero instances are available, derived from positivity hypotheses
  haveI : NeZero N := NeZero.of_pos hN_pos
  haveI : NeZero M := NeZero.of_pos hM_pos
  -- Define the prior distribution (uniform on Fin N)
  let prior_dist : Fin N → NNReal :=
    uniformDist (by {rw [Fintype.card_fin]; exact hN_pos} : 0 < Fintype.card (Fin N))
  -- Define the constant conditional distribution (uniform on Fin M)
  let q_const_dist : Fin M → NNReal :=
    uniformDist (by {rw [Fintype.card_fin]; exact hM_pos} : 0 < Fintype.card (Fin M))
  -- Compute the joint distribution P(i,j) = prior(i) * q_const(j)
  dependentPairDist_of_independent prior_dist q_const_dist

/--
The product of two uniform distributions (on Fin N and Fin M respectively)
is the uniform distribution on Fin (N*M).
This uses the `dependentPairDist_of_independent` to represent the product.
-/
lemma uniformDist_prod_uniformDist_is_uniformDist_prod
    {N M : ℕ} (hN_pos : N > 0) (hM_pos : M > 0) :
    DependentPairDist_of_independent_helper hN_pos hM_pos
    =
    uniformDist (by {simp only [Fintype.card_prod, Fintype.card_fin]; exact Nat.mul_pos hN_pos hM_pos} : 0 < Fintype.card (Fin N × Fin M)) ∘
      (finProdFinEquiv : Fin N × Fin M ≃ Fin (N*M)).symm := by
  -- Need to show equality of functions on Fin (N*M)
  funext k
  -- Definitions
  simp only [DependentPairDist_of_independent_helper, dependentPairDist_of_independent, DependentPairDist, uniformDist, Function.comp_apply]
  -- Let (idx_N, idx_M) be the pair corresponding to k
  -- LHS: ((Fintype.card (Fin N))⁻¹ : NNReal) * ((Fintype.card (Fin M))⁻¹ : NNReal)
  -- RHS: ((Fintype.card (Fin N × Fin M))⁻¹ : NNReal)
  -- where finProdFinEquiv.symm k is the argument to RHS's function (which is const, so ignored)

  simp only [Fintype.card_fin, Fintype.card_prod] -- Simplifies card terms

  simp [Nat.cast_mul, mul_comm]

/--
Helper Lemma: The joint distribution of two independent uniform random variables
(on Fin N and Fin M) is equivalent to a uniform distribution on Fin (N*M).
The result of `dependentPairDist_of_independent (uniformDist_N) (uniformDist_M)`
is pointwise equal to `uniformDist_NM`.
-/
lemma joint_uniform_is_flat_uniform
    {N M : ℕ} (hN_pos : N > 0) (hM_pos : M > 0) :
    -- Local NeZero instances for the definition
    haveI : NeZero N := NeZero.of_pos hN_pos
    haveI : NeZero M := NeZero.of_pos hM_pos
    let unif_N_dist := uniformDist (by simp only [Fintype.card_fin]; exact hN_pos : 0 < Fintype.card (Fin N))
    let unif_M_dist := uniformDist (by simp only [Fintype.card_fin]; exact hM_pos : 0 < Fintype.card (Fin M))
    let joint_dist := dependentPairDist_of_independent unif_N_dist unif_M_dist
    let flat_uniform_dist := uniformDist (by simp only [Fintype.card_fin]; exact Nat.mul_pos hN_pos hM_pos : 0 < Fintype.card (Fin (N * M)))
    joint_dist = flat_uniform_dist := by
  -- Functional extensionality
  funext k

  -- Unfold all relevant definitions.
  -- `simp` will unfold `joint_dist`, `unif_N_dist`, `unif_M_dist`, `flat_uniform_dist`
  -- as they are let-expressions in the goal.
  simp only [dependentPairDist_of_independent, DependentPairDist, uniformDist]

  -- At this point, the goal should be:
  -- (Fintype.card (Fin N))⁻¹ * (Fintype.card (Fin M))⁻¹ = (Fintype.card (Fin (N * M)))⁻¹

  -- Simplify Fintype.card values
  simp only [Fintype.card_fin]
  -- Goal: (↑N)⁻¹ * (↑M)⁻¹ = (↑(N * M))⁻¹

  -- Use NNReal properties for inverses and Nat.cast properties
  simp [Nat.cast_mul, mul_comm] -- Changes LHS to (↑N * ↑M)⁻¹


/--
Property: `f0 H (n*m) = f0 H n + f0 H m` for `n, m > 0`.
This is derived from the conditional additivity axiom for independent distributions.
Output is `ℝ≥0`.
-/
theorem f0_mul_eq_add_f0_new {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) {n m : ℕ} (hn_pos : n > 0) (hm_pos : m > 0) :
    f0 hH_axioms (n * m) = f0 hH_axioms n + f0 hH_axioms m := by
  -- Step 1: Handle positivity and unfold f0
  have hnm_pos : n * m > 0 := Nat.mul_pos hn_pos hm_pos
  simp only [f0, dif_pos hn_pos, dif_pos hm_pos, dif_pos hnm_pos]
  -- Goal: f hH_axioms hnm_pos = f hH_axioms hn_pos + f hH_axioms hm_pos

  -- Step 2: Define the uniform distributions involved
  -- For f hH_axioms hn_pos (uniform on Fin n)
  let card_n_pos_proof : 0 < Fintype.card (Fin n) := by simp [hn_pos]
  let unif_n_dist := uniformDist card_n_pos_proof

  -- For f hH_axioms hm_pos (uniform on Fin m)
  let card_m_pos_proof : 0 < Fintype.card (Fin m) := by simp [hm_pos]
  let unif_m_dist := uniformDist card_m_pos_proof

  -- For f hH_axioms hnm_pos (uniform on Fin (n*m))
  let card_nm_pos_proof : 0 < Fintype.card (Fin (n*m)) := by simp [hnm_pos]
  let unif_nm_dist := uniformDist card_nm_pos_proof

  -- Step 3: Rewrite the goal in terms of H applied to these distributions
  -- LHS: H (α := Fin (n*m)) unif_nm_dist
  -- RHS: H (α := Fin n) unif_n_dist + H (α := Fin m) unif_m_dist
  change H (α := Fin (n*m)) unif_nm_dist = H (α := Fin n) unif_n_dist + H (α := Fin m) unif_m_dist

  -- Step 4: Apply conditional additivity for independent distributions
  -- Need sum = 1 proofs for unif_n_dist and unif_m_dist
  have h_sum_unif_n : (∑ i, unif_n_dist i) = 1 := sum_uniformDist card_n_pos_proof
  have h_sum_unif_m : (∑ i, unif_m_dist i) = 1 := sum_uniformDist card_m_pos_proof

  -- Create local NeZero instances required by cond_add_for_independent_distributions
  haveI : NeZero n := NeZero.of_pos hn_pos
  haveI : NeZero m := NeZero.of_pos hm_pos

  have h_add_indep :
      H (dependentPairDist_of_independent unif_n_dist unif_m_dist) =
        H (α := Fin n) unif_n_dist + H (α := Fin m) unif_m_dist :=
    cond_add_for_independent_distributions hH_axioms unif_n_dist unif_m_dist h_sum_unif_n h_sum_unif_m

  -- Step 5: Rewrite the RHS of the main goal using h_add_indep
  rw [← h_add_indep]
  -- Goal: H (α := Fin (n*m)) unif_nm_dist = H (dependentPairDist_of_independent unif_n_dist unif_m_dist)

  -- Step 6: Prove that unif_nm_dist is the same as the joint distribution
  -- This uses the helper lemma joint_uniform_is_flat_uniform
  have h_dist_eq : dependentPairDist_of_independent unif_n_dist unif_m_dist = unif_nm_dist := by
    -- We need to match the statement of joint_uniform_is_flat_uniform
    -- joint_uniform_is_flat_uniform states:
    --   (dependentPairDist_of_independent unif_N unif_M) = unif_NM
    -- Here, our unif_n_dist and unif_m_dist are already defined correctly.
    -- The equality is direct from the lemma.
    exact joint_uniform_is_flat_uniform hn_pos hm_pos

  -- Step 7: Apply the distribution equality to the goal
  rw [h_dist_eq]
  -- Goal: H (α := Fin (n*m)) unif_nm_dist = H (α := Fin (n*m)) unif_nm_dist (by rfl)


/-!
Helper lemma for the inductive step of `uniformEntropy_power_law_new`.
Shows `f0 H (n^(m+1)) = f0 H (n^m) + f0 H n`.
-/
lemma f0_pow_succ_step {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) {n m : ℕ} (hn_pos : n > 0) (_hm_pos : m > 0) :
    f0 hH_axioms (n ^ (m + 1)) = f0 hH_axioms (n ^ m) + f0 hH_axioms n := by
  -- Assuming pow_succ' n m results in n * n^m based on the error message.
  -- If it results in n^m * n, the original argument order for f0_mul_eq_add_f0_new was correct,
  -- and the issue might be more subtle or the error message slightly misleading.
  -- Proceeding based on the error message's "with" clause indicating goal has n * n^m.
  rw [pow_succ' n m] -- This should be n * n^m if the error message is precise about the goal state

  -- Apply f0_mul_eq_add_f0_new. Need hypotheses for it:
  -- 1. n^m > 0
  have h_pow_nm_pos : n ^ m > 0 := by
    exact Nat.pow_pos hn_pos -- The exponent m is implicit here
  -- 2. n > 0 (given by hn_pos)

  -- Apply the multiplicative property.
  -- The factors in the goal's LHS (n * n^m) are n and n^m.
  -- Their positivity proofs are hn_pos and h_pow_nm_pos respectively.
  rw [f0_mul_eq_add_f0_new hH_axioms hn_pos h_pow_nm_pos]
  -- The goal is now:
  -- f0 hH_axioms n + f0 hH_axioms (n ^ m) = f0 hH_axioms (n ^ m) + f0 hH_axioms n
  rw [add_comm (f0 hH_axioms n) (f0 hH_axioms (n ^ m))]

/--/
The proof is by induction on `k`, using the “multiplicativity ⇒
additivity” lemma `f0_pow_succ_step` and the distributive identity
`add_mul`.  All algebra is carried out in `ℝ≥0`, so no special coercions
are needed.
-/
theorem uniformEntropy_power_law_new
    {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H)
    {n k : ℕ} (hn_pos : n > 0) (hk_pos : k > 0) :
    f0 hH_axioms (n ^ k) = (k : ℝ≥0) * f0 hH_axioms n := by
  ------------------------------------------------------------------
  --  Step 0  ·  Rephrase the goal as a proposition `P k`.
  ------------------------------------------------------------------
  let P : ℕ → Prop :=
    fun k' ↦ f0 hH_axioms (n ^ k') = (k' : ℝ≥0) * f0 hH_axioms n

  ------------------------------------------------------------------
  --  Step 1  ·  Establish the base case  k = 1.
  ------------------------------------------------------------------
  have base : P 1 := by
    simp [P, pow_one, Nat.cast_one, one_mul]

  ------------------------------------------------------------------
  --  Step 2  ·  Prove the inductive step  P m → P (m+1)  for m ≥ 1.
  ------------------------------------------------------------------
  have step : ∀ m, m ≥ 1 → P m → P (m + 1) := by
    intro m hm_ge1 hPm       -- inductive hypothesis `hPm`
    -- positivity of `m`
    have hm_pos : m > 0 := hm_ge1

    -- use the additive recursion lemma
    have h_rec := f0_pow_succ_step hH_axioms hn_pos hm_pos
        -- `h_rec : f0 … (n^(m+1)) = f0 … (n^m) + f0 … n`

    -- rewrite the right-hand `f0 n^m` via the I.H.
    have h_rw : f0 hH_axioms (n ^ (m + 1)) =
                (m : ℝ≥0) * f0 hH_axioms n + f0 hH_axioms n := by
      rw [h_rec] -- Goal: f0 hH_axioms (n^m) + f0 hH_axioms n = (↑m) * f0 hH_axioms n + f0 hH_axioms n
      rw [hPm]   -- Goal: (↑m) * f0 hH_axioms n + f0 hH_axioms n = (↑m) * f0 hH_axioms n + f0 hH_axioms n
                 -- This is true by reflexivity.

    -- Factor the common `f0 hH_axioms n` using `add_mul`.
    -- (↑m + 1) * C   =   ↑m * C + 1 * C
    have h_factor :
        (m : ℝ≥0) * f0 hH_axioms n + f0 hH_axioms n =
        ((m + 1 : ℕ) : ℝ≥0) * f0 hH_axioms n := by
      -- turn the lone `f0` into `1 * f0`, then apply `add_mul`
      simpa [one_mul, add_mul, Nat.cast_add, Nat.cast_one] using
        congrArg (fun x => x) (rfl :
          (m : ℝ≥0) * f0 hH_axioms n + 1 * f0 hH_axioms n =
          ((m : ℝ≥0) + 1) * f0 hH_axioms n)

    -- Combine the two equalities
    simpa [P] using h_rw.trans h_factor

  ------------------------------------------------------------------
  --  Step 3  ·  Apply `Nat.le_induction` starting from k = 1.
  ------------------------------------------------------------------
  have hk_ge1 : k ≥ 1 := Nat.one_le_of_lt hk_pos
  have : P k := Nat.le_induction base step k hk_ge1
  simpa [P] using this


/-- If `f0 H b = 0` for some `b ≥ 2`, then `f0 H 2 = 0`. (Output `ℝ≥0`) -/
lemma f0_2_eq_zero_of_f0_b_eq_zero_new {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) {b : ℕ} (hb_ge2 : b ≥ 2) (hf0b_eq_0 : f0 hH_axioms b = 0) :
    f0 hH_axioms 2 = 0 := by
  have h_mono := f0_mono_new hH_axioms
  have h_f0_2_ge_0 : f0 hH_axioms 2 ≥ 0 := by apply @_root_.zero_le -- Output is NNReal
  have h2_le_b : 2 ≤ b := by linarith
  have h_f0_2_le_b : f0 hH_axioms 2 ≤ f0 hH_axioms b := h_mono h2_le_b
  rw [hf0b_eq_0] at h_f0_2_le_b -- Now f0 hH_axioms 2 ≤ 0
  exact le_antisymm h_f0_2_le_b h_f0_2_ge_0





/-- If `f0 H 2 = 0`, then `f0 H (2^k) = 0` for `k ≥ 1`. (Output `ℝ≥0`) -/
lemma f0_pow2_eq_zero_of_f0_2_eq_zero_new {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) {k : ℕ} (hf0_2_eq_0 : f0 hH_axioms 2 = 0) (hk_ge1 : k ≥ 1) :
    f0 hH_axioms (2 ^ k) = 0 := by
  have h2_pos : 2 > 0 := by norm_num
  have hk_pos : k > 0 := pos_of_one_le hk_ge1
  have h_pow_law := uniformEntropy_power_law_new hH_axioms h2_pos hk_pos
  -- h_pow_law: f0 hH_axioms (2^k) = (k : ℝ≥0) * f0 hH_axioms 2
  rw [hf0_2_eq_0, mul_zero] at h_pow_law
  exact h_pow_law


/-- If `f0 H (2^k) = 0` for all `k ≥ 1`, then `f0 H n = 0` for all `n ≥ 1`. (Output `ℝ≥0`) -/
lemma f0_n_eq_zero_of_f0_pow2_zero_new {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H)
    (h_all_f0_pow2_zero : ∀ k ≥ 1, f0 hH_axioms (2 ^ k) = 0)
    {n : ℕ} (hn_ge1 : n ≥ 1) :
    f0 hH_axioms n = 0 := by
  have hn_pos : n > 0 := pos_of_one_le hn_ge1
  rcases @exists_pow_ge 2 n (by norm_num : 1 < 2) with ⟨k, h_n_le_2k⟩
  -- Need k ≥ 1 for h_all_f0_pow2_zero.
  -- If 2^k ≥ n ≥ 1, then k cannot be 0 unless n=1.
  if hn_eq_1 : n = 1 then
    rw [hn_eq_1]
    exact f0_1_eq_0_new hH_axioms
  else
    have k_ge_1 : k ≥ 1 := by
      contrapose! hn_eq_1 -- if k=0, then n=1. After contrapose, hn_eq_1 : k < 1, goal is n = 1
      have k_eq_zero : k = 0 := (Nat.lt_one_iff.mp hn_eq_1)
      rw [k_eq_zero, pow_zero] at h_n_le_2k
      exact Nat.le_antisymm h_n_le_2k hn_ge1

    have h_f0_n_le_f0_2k : f0 hH_axioms n ≤ f0 hH_axioms (2^k) :=
      (f0_mono_new hH_axioms) h_n_le_2k
    rw [h_all_f0_pow2_zero k k_ge_1] at h_f0_n_le_f0_2k -- f0 H n ≤ 0
    exact le_antisymm h_f0_n_le_f0_2k (by apply @_root_.zero_le : f0 hH_axioms n ≥ 0)


/-- `f0 H b > 0` (as NNReal, so `f0 H b ≠ 0`) if `H` is non-trivial and `b ≥ 2`. -/
lemma uniformEntropy_pos_of_nontrivial_new {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) (hH_nontrivial : ∃ n' ≥ 1, f0 hH_axioms n' ≠ 0)
    {b : ℕ} (hb_ge2 : b ≥ 2) :
    f0 hH_axioms b ≠ 0 := by
  by_contra hf0b_eq_0
  -- hf0b_eq_0 : f0 hH_axioms b = 0
  have hf0_2_eq_0 : f0 hH_axioms 2 = 0 :=
    f0_2_eq_zero_of_f0_b_eq_zero_new hH_axioms hb_ge2 hf0b_eq_0
  have h_all_f0_pow2_zero : ∀ k ≥ 1, f0 hH_axioms (2^k) = 0 :=
    fun k hk_ge1 => f0_pow2_eq_zero_of_f0_2_eq_zero_new hH_axioms hf0_2_eq_0 hk_ge1

  rcases hH_nontrivial with ⟨n', hn'_ge1, h_f0_n'_neq_0⟩
  have h_f0_n'_eq_0 : f0 hH_axioms n' = 0 :=
    f0_n_eq_zero_of_f0_pow2_zero_new hH_axioms h_all_f0_pow2_zero hn'_ge1
  exact h_f0_n'_neq_0 h_f0_n'_eq_0


/-- `f0 H b > 0` (as NNReal) if `H` is non-trivial and `b ≥ 2`.
    This is a version of `uniformEntropy_pos_of_nontrivial_new` that directly gives `0 < f0 ...`. -/
lemma f0_pos_of_nontrivial_nnreal_version {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) (hH_nontrivial : ∃ n' ≥ 1, f0 hH_axioms n' ≠ 0)
    {b : ℕ} (hb_ge2 : b ≥ 2) :
    0 < f0 hH_axioms b := by
  have h_ne_zero : f0 hH_axioms b ≠ 0 :=
    uniformEntropy_pos_of_nontrivial_new hH_axioms hH_nontrivial hb_ge2
  exact (@_root_.pos_iff_ne_zero _).mpr h_ne_zero

-- The trapping argument will now mostly deal with `Real` numbers due to division and logarithms.
-- `f0 H n` will be coerced to `Real` using `(f0 H n : Real)`.

/-- `k_from_f0_trap_satisfies_pow_bounds` but with `f0` outputting `ℝ≥0` and coercing.
    The inequalities for `f0` ratios will be in `Real`.
    `k_val / m_val ≤ (f0 H n : ℝ) / (f0 H b : ℝ)`
-/
lemma k_from_f0_trap_satisfies_pow_bounds_real {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) (hH_nontrivial : ∃ n' ≥ 1, f0 hH_axioms n' ≠ 0)
    {n m b : ℕ} (hn_pos : n > 0) (hm_pos : m > 0) (hb_ge2 : b ≥ 2) :
    ∃ k : ℕ,
      -- Power bounds (Real numbers, Nat powers)
      ((b : ℝ) ^ k ≤ (n : ℝ) ^ m ∧ (n : ℝ) ^ m < (b : ℝ) ^ (k + 1)) ∧
      -- Ratio bounds (Real numbers)
      (((k : ℝ) / (m : ℝ) ≤ (f0 hH_axioms n : ℝ) / (f0 hH_axioms b : ℝ)) ∧
       ((f0 hH_axioms n : ℝ) / (f0 hH_axioms b : ℝ) ≤ ((k : ℝ) + 1) / (m : ℝ))) := by
  let x_real : ℝ := (n : ℝ) ^ m
  have hx_real_ge_1 : x_real ≥ 1 := by
    exact one_le_pow_cast (Nat.one_le_of_lt hn_pos)
  have hb_real_gt_1 : (b : ℝ) > 1 := Nat.one_lt_cast.mpr (by linarith : b > 1)

  rcases exists_nat_pow_bounds hb_ge2 hx_real_ge_1 with ⟨k, h_bk_le_x, h_x_lt_bkp1⟩
  -- h_bk_le_x : (b:ℝ)^k ≤ x_real
  -- h_x_lt_bkp1 : x_real < (b:ℝ)^(k+1)

  use k
  constructor
  · exact ⟨h_bk_le_x, h_x_lt_bkp1⟩
  · -- Prove Ratio bounds using f0 (NNReal) properties, then coerce and divide in Real
    let f0n_nnreal := f0 hH_axioms n
    let f0b_nnreal := f0 hH_axioms b
    let f0_nm_pow_nnreal := f0 hH_axioms (n ^ m)
    let f0_bk_pow_nnreal := f0 hH_axioms (b ^ k)
    let f0_bkp1_pow_nnreal := f0 hH_axioms (b ^ (k+1))

    have h_nm_pow_pos : n^m > 0 := Nat.pow_pos hn_pos
    have h_bk_pow_pos : b^k > 0 := Nat.pow_pos (by linarith : b > 0)
    have h_bkp1_pow_pos : b^(k+1) > 0 := Nat.pow_pos (by linarith : b > 0)
    have m_pos_real : (m:ℝ) > 0 := Nat.cast_pos.mpr hm_pos

    -- Nat bounds from Real bounds on powers: b^k ≤ n^m < b^(k+1)
    have h_nat_bounds : b^k ≤ n^m ∧ n^m < b^(k+1) :=
      nat_bounds_from_cast_pow_bounds h_bk_le_x h_x_lt_bkp1
    have h_nat_le := h_nat_bounds.left
    have h_nat_lt := h_nat_bounds.right

    -- Monotonicity of f0 for these Nat bounds
    have h_f0_mono1 : f0_bk_pow_nnreal ≤ f0_nm_pow_nnreal := (f0_mono_new hH_axioms) h_nat_le
    have h_f0_mono2 : f0_nm_pow_nnreal ≤ f0_bkp1_pow_nnreal := (f0_mono_new hH_axioms) (Nat.le_of_lt h_nat_lt)

    -- Apply power law (outputs NNReal)
    -- f0 H (n^m) = m * f0 H n
    have pl_nm : f0_nm_pow_nnreal = (m : ℝ≥0) * f0n_nnreal :=
      uniformEntropy_power_law_new hH_axioms hn_pos hm_pos
    -- f0 H (b^k) = k * f0 H b (if k>0, else f0 H 1 = 0)
    have pl_bk : f0_bk_pow_nnreal = (if k_is_0 : k = 0 then 0 else (k : ℝ≥0) * f0b_nnreal) := by
      split_ifs with hk_cond
      · -- Case k = 0. Goal is f0_bk_pow_nnreal = 0.
        -- hk_cond : k = 0
        change f0 hH_axioms (b ^ k) = 0 -- Unfold f0_bk_pow_nnreal
        rw [hk_cond, pow_zero]          -- Goal: f0 hH_axioms 1 = 0
        exact f0_1_eq_0_new hH_axioms
      · -- Case k ≠ 0. Goal is f0_bk_pow_nnreal = (k : ℝ≥0) * f0b_nnreal.
        -- hk_cond : k ≠ 0
        change f0 hH_axioms (b ^ k) = (k : ℝ≥0) * f0b_nnreal -- Unfold f0_bk_pow_nnreal
        exact uniformEntropy_power_law_new hH_axioms (by linarith) (Nat.pos_of_ne_zero hk_cond)
    -- f0 H (b^(k+1)) = (k+1) * f0 H b
    have pl_bkp1 : f0_bkp1_pow_nnreal = ((k+1 : ℕ) : ℝ≥0) * f0b_nnreal :=
      uniformEntropy_power_law_new hH_axioms (by linarith) (Nat.succ_pos k)

    -- Substitute power laws into mono inequalities (still in NNReal)
    rw [pl_bk, pl_nm] at h_f0_mono1
    rw [pl_nm, pl_bkp1] at h_f0_mono2

    -- Coerce to Real and divide
    have h_f0b_real_pos : (f0b_nnreal : ℝ) > 0 := by
      simp only [coe_pos] -- coe_pos is NNReal.coe_pos, needs f0b_nnreal > 0 (as NNReal)
      exact f0_pos_of_nontrivial_nnreal_version hH_axioms hH_nontrivial hb_ge2

    constructor
    · -- Left inequality: k/m ≤ (f0n)/(f0b)
      -- from: (if k=0 then 0 else k*f0b) ≤ m*f0n
      by_cases hk0_case : k = 0
      · -- Case k = 0
        -- First, simplify h_f0_mono1 using k=0, though it's not directly used for this goal.
        rw [hk0_case] at h_f0_mono1; simp only [if_pos] at h_f0_mono1
        -- h_f0_mono1 is now `0 ≤ (m : ℝ≥0) * f0n_nnreal`

        -- Now, simplify the goal using k=0.
        -- Goal was: (k:ℝ)/(m:ℝ) ≤ (f0n_nnreal:ℝ)/(f0b_nnreal:ℝ)
        simp only [hk0_case, Nat.cast_zero, zero_div]
        -- Goal is now: 0 ≤ (f0n_nnreal:ℝ)/(f0b_nnreal:ℝ)
        -- This simp uses m_pos_real (↑m > 0) to simplify 0/(m:ℝ) to 0.

        -- Prove 0 ≤ (f0n_nnreal:ℝ)/(f0b_nnreal:ℝ)
        apply div_nonneg
        · -- Numerator f0n_nnreal ≥ 0
          exact NNReal.coe_nonneg f0n_nnreal
        · -- Denominator f0b_nnreal > 0, so f0b_nnreal ≥ 0
          exact le_of_lt h_f0b_real_pos
      · -- k > 0 case
        -- h_f0_mono1 was: (if k_is_0 : k = 0 then 0 else (k:ℝ≥0)*f0b_nnreal) ≤ (m:ℝ≥0)*f0n_nnreal
        -- hk0_case : ¬(k = 0)
        -- We want to simplify h_f0_mono1 using hk0_case.
        simp [hk0_case] at h_f0_mono1
        -- h_f0_mono1 is now: (k:ℝ≥0)*f0b_nnreal ≤ (m:ℝ≥0)*f0n_nnreal
        -- Goal: (k:ℝ)/(m:ℝ) ≤ (f0n_nnreal:ℝ)/(f0b_nnreal:ℝ)
        -- Rewrite as k * f0b ≤ m * f0n using mul_le_mul_iff_of_pos (for Real)
        rw [div_le_div_iff₀ m_pos_real h_f0b_real_pos]
        -- Goal is now (k:ℝ)*(f0b_nnreal:ℝ) ≤ (f0n_nnreal:ℝ)*(m:ℝ) due to div_le_div_iff₀ structure
        -- Transform goal to match NNReal.coe_le_coe structure
        rw [← NNReal.coe_natCast k, ← NNReal.coe_natCast m] -- Converts (k:ℝ) to ↑(k:ℝ≥0) etc.
                                                        -- Goal: ↑k * ↑f0b ≤ ↑f0n * ↑m (all terms now coe from NNReal)
        rw [← NNReal.coe_mul, ← NNReal.coe_mul] -- Converts ↑X * ↑Y to ↑(X * Y)
                                            -- Goal: ↑(k*f0b) ≤ ↑(f0n*m) (ops inside coe are NNReal)
        rw [NNReal.coe_le_coe] -- Applies ↑A ≤ ↑B ↔ A ≤ B
                                -- Goal: (k:ℝ≥0)*f0b_nnreal ≤ (f0n_nnreal:ℝ≥0)*(m:ℝ≥0)
        conv_rhs => rw [mul_comm] -- Goal: (k:ℝ≥0)*f0b_nnreal ≤ (m:ℝ≥0)*(f0n_nnreal:ℝ≥0)
        exact h_f0_mono1
    · -- Right inequality: (f0n)/(f0b) ≤ (k+1)/m
      -- from: m*f0n ≤ (k+1)*f0b
      -- h_f0_mono2: (m:ℝ≥0)*f0n_nnreal ≤ ((k+1):ℝ≥0)*f0b_nnreal
      rw [div_le_div_iff₀ h_f0b_real_pos m_pos_real]
      -- Goal: (f0n_nnreal:ℝ)*(m:ℝ) ≤ (((k+1):ℕ):ℝ)*(f0b_nnreal:ℝ)
      rw [mul_comm (f0n_nnreal:ℝ) _] -- match order for next steps
      -- Goal: (m:ℝ)*(f0n_nnreal:ℝ) ≤ (((k+1):ℕ):ℝ)*(f0b_nnreal:ℝ)
      -- Note: by Nat.cast_add_one, the term (((k+1):ℕ):ℝ) is (↑k + 1) in Real.

      -- Transform goal to match NNReal.coe_le_coe structure
      rw [← NNReal.coe_natCast m] -- Handles LHS factor (m:ℝ) becoming ↑(↑m:ℝ≥0)
      -- At this point, the RHS factor involving k is (↑k + 1):ℝ
      rw [← Nat.cast_add_one k]   -- Changes (↑k + 1) on RHS to ↑(k+1:ℕ)
      rw [← NNReal.coe_natCast (k+1)] -- Changes ↑(k+1:ℕ) on RHS to ↑(↑(k+1:ℕ):ℝ≥0)

      -- Goal should now be:
      -- ↑(↑m:ℝ≥0) * ↑f0n_nnreal ≤ ↑(↑(k+1:ℕ):ℝ≥0) * ↑f0b_nnreal
      rw [← NNReal.coe_mul, ← NNReal.coe_mul]
      rw [NNReal.coe_le_coe]
      -- Goal: (m:ℝ≥0)*f0n_nnreal ≤ ((k+1):ℝ≥0)*f0b_nnreal
      exact h_f0_mono2
