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

import PPNP.Common.Basic
import PPNP.Entropy.Common


namespace PPNP.Entropy.RET

open BigOperators Fin Real Topology NNReal Filter Nat
open PPNP.Common
open PPNP.Entropy.Common


/-! ### Phase 2: Properties of `f(n) = H(uniform_n)` -/

-- Replaced: old `f` definition
/--
Defines `f H n = H(uniform distribution on n outcomes)`.
`H` is an entropy function satisfying `IsEntropyFunction`.
Requires `n > 0`. Output is `ℝ≥0`.
-/
noncomputable def f {H_func : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0} -- Renamed H to H_func for clarity
    (hH_axioms : IsEntropyFunction H_func) {n : ℕ} (hn_pos : n > 0) : ℝ≥0 :=
  let α_n := Fin n
  have h_card_pos : 0 < Fintype.card α_n := by
    rw [Fintype.card_fin]
    exact hn_pos
  H_func (uniformDist h_card_pos)

-- Replaced: old `f0` definition
/--
Defines `f0 H n` which extends `f H n` to include `n=0` by setting `f0 H 0 = 0`.
Output is `ℝ≥0`.
-/
noncomputable def f0 {H_func : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0} -- Renamed H to H_func
    (hH_axioms : IsEntropyFunction H_func) (n : ℕ) : ℝ≥0 :=
  if hn_pos : n > 0 then f hH_axioms hn_pos else 0

-- New helper
/--
Helper lemma: The uniform distribution on `Fin 1` is `λ _ => 1`.
-/
lemma uniformDist_fin_one_eq_dist_one :
    uniformDist (by {rw [Fintype.card_fin]; exact Nat.one_pos} : 0 < Fintype.card (Fin 1)) =
    (fun (_ : Fin 1) => 1) := by
  funext x
  simp only [uniformDist, Fintype.card_fin, Nat.cast_one, inv_one]

-- New helper
/--
Helper lemma: The distribution `λ (_ : Fin 1) => 1` sums to 1.
-/
lemma sum_dist_one_fin_one_eq_1 :
    (∑ (_ : Fin 1), (1 : ℝ≥0)) = 1 := by
  simp [Finset.sum_const, Finset.card_fin, nsmul_one]



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
Property: `f0 H 1 = 0`.
This follows from the `normalized` axiom of `IsEntropyFunction`.
-/
theorem f0_1_eq_0 {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
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
Property: `f0 H n` is monotone non-decreasing.
Uses `zero_invariance` and `max_uniform` axioms.
-/
theorem f0_mono {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) : Monotone (f0 hH_axioms) := by
  apply monotone_nat_of_le_succ
  intro n
  -- Case n = 0
  if hn_is_zero : n = 0 then
    rw [hn_is_zero] -- Goal: f0 hH_axioms 0 ≤ f0 hH_axioms (0 + 1)
    simp [Nat.add_zero] -- Goal: f0 hH_axioms 0 ≤ f0 hH_axioms 1

    -- Simplify RHS using f0_1_eq_0
    have h0_1_eq_0 : f0 hH_axioms 1 = 0 := f0_1_eq_0 hH_axioms
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

-- New helper
/--
Helper function: Defines P(i,j) = prior(i) * q_const(j) using DependentPairDist.
-/
noncomputable def dependentPairDist_of_independent
  {N M : ℕ} [hN : NeZero N] [hM : NeZero M]
  (prior : Fin N → NNReal) (q_const : Fin M → NNReal) :
  Fin (N * M) → NNReal :=
  @DependentPairDist N M hN hM prior (fun _i => q_const)

-- New helper
/--
If weights `w` sum to `1`, then `∑ w i * C = C`.
-/
lemma sum_weighted_constant {β : Type*} [Fintype β]
    {C_val : ℝ≥0} {w : β → ℝ≥0} (h_w_sum_1 : ∑ i, w i = 1) : -- Renamed C to C_val
    (∑ i, w i * C_val) = C_val := by
  rw [← Finset.sum_mul, h_w_sum_1, one_mul]

-- New derivation (replaces logic of old prop4_additivity_product)
/--
If P(j|i) = q_const(j), then H(joint) = H(prior) + H(q_const).
-/
lemma cond_add_for_independent_distributions
    {H_func : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0} -- Renamed H to H_func
    (hH_axioms : IsEntropyFunction H_func)
    {N M : ℕ} [NeZero N] [NeZero M]
    (prior : Fin N → NNReal) (q_const : Fin M → NNReal)
    (hprior_sum_1 : ∑ i, prior i = 1) (hq_const_sum_1 : ∑ j, q_const j = 1) :
    H_func (dependentPairDist_of_independent prior q_const)
      = H_func prior + H_func (α := Fin M) q_const := by
  simp only [dependentPairDist_of_independent]
  rw [hH_axioms.cond_add prior (fun _ => q_const) (fun _ => hq_const_sum_1) hprior_sum_1]
  rw [sum_weighted_constant hprior_sum_1]


-- This helper can be local to f0_mul_eq_add_f0 proof or kept if generally useful
-- noncomputable def DependentPairDist_of_independent_helper -- From Phase 2, might not be needed if  is direct.
--   {N M : ℕ} (hN_pos : N > 0) (hM_pos : M > 0) :
--   Fin (N * M) → NNReal :=
--   haveI : NeZero N := NeZero.of_pos hN_pos
--   haveI : NeZero M := NeZero.of_pos hM_pos
--   let prior_dist := uniformDist (by {rw [Fintype.card_fin]; exact hN_pos})
--   let q_const_dist := uniformDist (by {rw [Fintype.card_fin]; exact hM_pos})
--   dependentPairDist_of_independent prior_dist q_const_dist

-- Replaced: old `uniformProb_product_uniformProb_is_uniformProb`
-- This version is more direct for the proof of f0_mul_eq_add_f0.

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
theorem f0_mul_eq_add_f0 {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
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
  rw [f0_mul_eq_add_f0 hH_axioms hn_pos h_pow_nm_pos]
  -- The goal is now:
  -- f0 hH_axioms n + f0 hH_axioms (n ^ m) = f0 hH_axioms (n ^ m) + f0 hH_axioms n
  rw [add_comm (f0 hH_axioms n) (f0 hH_axioms (n ^ m))]




/-
The proof is by induction on `k`, using the “multiplicativity ⇒
additivity” lemma `f0_pow_succ_step` and the distributive identity
`add_mul`.  All algebra is carried out in `ℝ≥0`, so no special coercions
are needed.
-/
theorem uniformEntropy_power_law
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


-- Replaced: old `f0_nonneg`
/-- Property: `f0 H n ≥ 0` for `n ≥ 1`. (Trivial since `f0` outputs `ℝ≥0`). -/
lemma f0_nonneg {H_func : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0} -- Renamed H to H_func
    (hH_axioms : IsEntropyFunction H_func) {n : ℕ} (_hn_ge1 : n ≥ 1) :
    ((f0 hH_axioms n) : ℝ) ≥ 0 := -- Coerced to Real for comparison with old version.
  NNReal.coe_nonneg _

-- Replaced: old `f0_2_eq_zero_of_f0_b_eq_zero`
/-- If `f0 H b = 0` for `b ≥ 2`, then `f0 H 2 = 0`. Output `ℝ≥0`. -/
lemma f0_2_eq_zero_of_f0_b_eq_zero {H_func : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0} -- Renamed H to H_func
    (hH_axioms : IsEntropyFunction H_func) {b : ℕ} (hb_ge2 : b ≥ 2) (hf0b_eq_0 : f0 hH_axioms b = 0) :
    f0 hH_axioms 2 = 0 := by
  have h_mono := f0_mono hH_axioms
  have h_f0_2_ge_0 : f0 hH_axioms 2 ≥ 0 := zero_le (f0 hH_axioms 2)
  have h2_le_b : 2 ≤ b := by linarith
  have h_f0_2_le_b : f0 hH_axioms 2 ≤ f0 hH_axioms b := h_mono h2_le_b
  rw [hf0b_eq_0] at h_f0_2_le_b
  exact le_antisymm h_f0_2_le_b h_f0_2_ge_0

/-- If `f0 H 2 = 0`, then `f0 H (2^k) = 0` for `k ≥ 1`. (Output `ℝ≥0`) -/
lemma f0_pow2_eq_zero_of_f0_2_eq_zero {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) {k : ℕ} (hf0_2_eq_0 : f0 hH_axioms 2 = 0) (hk_ge1 : k ≥ 1) :
    f0 hH_axioms (2 ^ k) = 0 := by
  have h2_pos : 2 > 0 := by norm_num
  have hk_pos : k > 0 := pos_of_one_le hk_ge1
  have h_pow_law := uniformEntropy_power_law hH_axioms h2_pos hk_pos
  -- h_pow_law: f0 hH_axioms (2^k) = (k : ℝ≥0) * f0 hH_axioms 2
  rw [hf0_2_eq_0, mul_zero] at h_pow_law
  exact h_pow_law



/-- If `f0 H (2^k) = 0` for all `k ≥ 1`, then `f0 H n = 0` for all `n ≥ 1`. (Output `ℝ≥0`) -/
lemma f0_n_eq_zero_of_f0_pow2_zero {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
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
    exact f0_1_eq_0 hH_axioms
  else
    have k_ge_1 : k ≥ 1 := by
      contrapose! hn_eq_1 -- if k=0, then n=1. After contrapose, hn_eq_1 : k < 1, goal is n = 1
      have k_eq_zero : k = 0 := (Nat.lt_one_iff.mp hn_eq_1)
      rw [k_eq_zero, pow_zero] at h_n_le_2k
      exact Nat.le_antisymm h_n_le_2k hn_ge1

    have h_f0_n_le_f0_2k : f0 hH_axioms n ≤ f0 hH_axioms (2^k) :=
      (f0_mono hH_axioms) h_n_le_2k
    rw [h_all_f0_pow2_zero k k_ge_1] at h_f0_n_le_f0_2k -- f0 H n ≤ 0
    exact le_antisymm h_f0_n_le_f0_2k (by apply @_root_.zero_le : f0 hH_axioms n ≥ 0)



/-- `f0 H b > 0` (as NNReal, so `f0 H b ≠ 0`) if `H` is non-trivial and `b ≥ 2`. -/
lemma uniformEntropy_pos_of_nontrivial {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) (hH_nontrivial : ∃ n' ≥ 1, f0 hH_axioms n' ≠ 0)
    {b : ℕ} (hb_ge2 : b ≥ 2) :
    f0 hH_axioms b ≠ 0 := by
  by_contra hf0b_eq_0
  -- hf0b_eq_0 : f0 hH_axioms b = 0
  have hf0_2_eq_0 : f0 hH_axioms 2 = 0 :=
    f0_2_eq_zero_of_f0_b_eq_zero hH_axioms hb_ge2 hf0b_eq_0
  have h_all_f0_pow2_zero : ∀ k ≥ 1, f0 hH_axioms (2^k) = 0 :=
    fun k hk_ge1 => f0_pow2_eq_zero_of_f0_2_eq_zero hH_axioms hf0_2_eq_0 hk_ge1

  rcases hH_nontrivial with ⟨n', hn'_ge1, h_f0_n'_neq_0⟩
  have h_f0_n'_eq_0 : f0 hH_axioms n' = 0 :=
    f0_n_eq_zero_of_f0_pow2_zero hH_axioms h_all_f0_pow2_zero hn'_ge1
  exact h_f0_n'_neq_0 h_f0_n'_eq_0



-- New helper
/-- If `f0 H n ≠ 0` for `n > 0`, then `H` is non-trivial. -/
lemma hf0n_ne_0_implies_nontrivial
    {H_func : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0} -- Renamed H to H_func
    (hH_axioms : IsEntropyFunction H_func)
    {n : ℕ} (hf0n_ne_0 : f0 hH_axioms n ≠ 0) (hn_pos : n > 0) :
    ∃ n' ≥ 1, f0 hH_axioms n' ≠ 0 := by
  use n; exact ⟨Nat.one_le_of_lt hn_pos, hf0n_ne_0⟩

/-- `f0 H b > 0` (as NNReal) if `H` is non-trivial and `b ≥ 2`.
    This is a version of `uniformEntropy_pos_of_nontrivial` that directly gives `0 < f0 ...`. -/
lemma f0_pos_of_nontrivial_nnreal_version {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) (hH_nontrivial : ∃ n' ≥ 1, f0 hH_axioms n' ≠ 0)
    {b : ℕ} (hb_ge2 : b ≥ 2) :
    0 < f0 hH_axioms b := by
  have h_ne_zero : f0 hH_axioms b ≠ 0 :=
    uniformEntropy_pos_of_nontrivial hH_axioms hH_nontrivial hb_ge2
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
    have h_f0_mono1 : f0_bk_pow_nnreal ≤ f0_nm_pow_nnreal := (f0_mono hH_axioms) h_nat_le
    have h_f0_mono2 : f0_nm_pow_nnreal ≤ f0_bkp1_pow_nnreal := (f0_mono hH_axioms) (Nat.le_of_lt h_nat_lt)

    -- Apply power law (outputs NNReal)
    -- f0 H (n^m) = m * f0 H n
    have pl_nm : f0_nm_pow_nnreal = (m : ℝ≥0) * f0n_nnreal :=
      uniformEntropy_power_law hH_axioms hn_pos hm_pos
    -- f0 H (b^k) = k * f0 H b (if k>0, else f0 H 1 = 0)
    have pl_bk : f0_bk_pow_nnreal = (if k_is_0 : k = 0 then 0 else (k : ℝ≥0) * f0b_nnreal) := by
      split_ifs with hk_cond
      · -- Case k = 0. Goal is f0_bk_pow_nnreal = 0.
        -- hk_cond : k = 0
        change f0 hH_axioms (b ^ k) = 0 -- Unfold f0_bk_pow_nnreal
        rw [hk_cond, pow_zero]          -- Goal: f0 hH_axioms 1 = 0
        exact f0_1_eq_0 hH_axioms
      · -- Case k ≠ 0. Goal is f0_bk_pow_nnreal = (k : ℝ≥0) * f0b_nnreal.
        -- hk_cond : k ≠ 0
        change f0 hH_axioms (b ^ k) = (k : ℝ≥0) * f0b_nnreal -- Unfold f0_bk_pow_nnreal
        exact uniformEntropy_power_law hH_axioms (by linarith) (Nat.pos_of_ne_zero hk_cond)
    -- f0 H (b^(k+1)) = (k+1) * f0 H b
    have pl_bkp1 : f0_bkp1_pow_nnreal = ((k+1 : ℕ) : ℝ≥0) * f0b_nnreal :=
      uniformEntropy_power_law hH_axioms (by linarith) (Nat.succ_pos k)

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


-- Replaced: old `le_logb_rpow_self_of_le`
/-- `k ≤ logb b X` given `b > 1, X > 0, b^k ≤ X`. -/
lemma le_logb_rpow_self_of_le {b k X : ℝ} (hb_gt_1 : b > 1) (hX_pos : 0 < X) (hkX : b^k ≤ X) :
    k ≤ Real.logb b X := by
  have b_pos : 0 < b := lt_trans zero_lt_one hb_gt_1
  have b_ne_one : b ≠ 1 := ne_of_gt hb_gt_1
  rw [← Real.logb_rpow b_pos b_ne_one (x := k)]
  apply (Real.logb_le_logb hb_gt_1 (Real.rpow_pos_of_pos b_pos k) hX_pos).mpr
  exact hkX

-- Replaced: old `logb_rpow_self_lt_of_lt`
/-- `logb b X < k_plus_1` given `b > 1, X > 0, X < b^(k_plus_1)`. -/
lemma logb_rpow_self_lt_of_lt {b X k_plus_1 : ℝ} (hb_gt_1 : b > 1) (hX_pos : 0 < X) (hXlt : X < b^k_plus_1) :
    Real.logb b X < k_plus_1 := by
  have b_pos : 0 < b := lt_trans zero_lt_one hb_gt_1
  have b_ne_one : b ≠ 1 := ne_of_gt hb_gt_1
  rw [← Real.logb_rpow b_pos b_ne_one (x := k_plus_1)]
  apply Real.logb_lt_logb hb_gt_1 hX_pos hXlt

/-!  Helper for `abs_sub_le_iff`  -/
structure AbsPair (a b r : ℝ) : Prop where
  left  : a - b ≤ r       -- 1ˢᵗ inequality
  right : b - a ≤ r       -- 2ⁿᵈ inequality

instance {a b r : ℝ} : Coe (AbsPair a b r)
    (a - b ≤ r ∧ b - a ≤ r) where
  coe := fun h => ⟨h.left, h.right⟩


/--
Logarithmic trapping: `| (f0 H n : ℝ) / (f0 H b : ℝ) - logb b n | ≤ 1 / (m : ℝ)`.
This uses the Real‐valued bounds from `k_from_f0_trap_satisfies_pow_bounds_real`.
-/
theorem logarithmic_trapping
  {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
  (hH_axioms     : IsEntropyFunction H)
  (hH_nontrivial : ∃ n' ≥ 1, f0 hH_axioms n' ≠ 0)
  {n m b : ℕ} (hn_pos  : n > 0) (hm_pos  : m > 0) (hb_ge2 : b ≥ 2) :
  |(f0 hH_axioms n : ℝ) / (f0 hH_axioms b : ℝ) - Real.logb b n| ≤ 1 / (m : ℝ) :=
by
  -- Unpack the “k from f0” bounds:
  rcases k_from_f0_trap_satisfies_pow_bounds_real
    hH_axioms hH_nontrivial hn_pos hm_pos hb_ge2
    with ⟨k, ⟨h_pow_le_nm,   h_nm_lt_pow_kp1⟩,
              ⟨h_f0_ratio_lower_bound, h_f0_ratio_upper_bound⟩⟩

  let f0_ratio  := (f0 hH_axioms n : ℝ) / (f0 hH_axioms b : ℝ)
  let logb_n_val := Real.logb b n
  let k_real    := (k : ℝ)
  let m_real    := (m : ℝ)

  -- Basic casts and positivity facts
  have hb_real_gt_1 : (b : ℝ) > 1 := Nat.one_lt_cast.mpr (by linarith : b > 1)
  have hn_real_pos : (n : ℝ) > 0 := Nat.cast_pos.mpr hn_pos
  have hm_real_pos : m_real > 0   := Nat.cast_pos.mpr hm_pos

  -- Derive     k_real ≤ m_real * logb_n_val   <   k_real + 1
  have h_k_le_m_logbn : k_real ≤ m_real * logb_n_val := by
    -- rewrite m * logb b n as logb b ((n^m : ℝ))
    rw [← Real.logb_rpow_eq_mul_logb_of_pos hn_real_pos (y := m_real)]
    -- reduce to proving (b^k : ℝ) ≤ (n^m : ℝ)
    have : (b : ℝ)^k_real ≤ (n : ℝ)^m_real := by
      simp_rw [k_real, m_real]
      rw [Real.rpow_natCast, Real.rpow_natCast]
      exact h_pow_le_nm
    apply le_logb_rpow_self_of_le hb_real_gt_1 (Real.rpow_pos_of_pos hn_real_pos m_real) this

  have h_m_logbn_lt_kp1 : m_real * logb_n_val < k_real + 1 := by
    rw [← Real.logb_rpow_eq_mul_logb_of_pos hn_real_pos (y := m_real)]
    have : (n : ℝ)^m_real < (b : ℝ)^(k_real + 1) := by
      simp_rw [m_real, k_real]
      rw [Real.rpow_natCast, ← Nat.cast_add_one, Real.rpow_natCast] -- Corrected order
      exact h_nm_lt_pow_kp1
    apply logb_rpow_self_lt_of_lt hb_real_gt_1 (Real.rpow_pos_of_pos hn_real_pos m_real) this

  -- Convert to the two sided‐inequalities on logb_n_val
  have h_logb_lt_kp1_m : logb_n_val < (k_real + 1) / m_real := by
    rw [lt_div_iff₀ hm_real_pos, mul_comm]
    exact h_m_logbn_lt_kp1

  have h_km_le_logb : k_real / m_real ≤ logb_n_val := by
    rw [div_le_iff₀ hm_real_pos, mul_comm]
    exact h_k_le_m_logbn

  have h_logb_minus_1m_lt_km : logb_n_val - 1 / m_real < k_real / m_real := by
    rw [sub_lt_iff_lt_add, div_add_div_same]
    exact h_logb_lt_kp1_m

  ----------------------------------------------------------------
  --  NEW: prove the two sides in the correct orientations:
  ----------------------------------------------------------------
  -- (1) logb_n_val - f0_ratio ≤ 1 / m_real
  have h_right : logb_n_val - f0_ratio ≤ 1 / m_real := by
    have : logb_n_val - f0_ratio < 1 / m_real := by
      -- f0_ratio ≥ k/m and logb_n_val - 1/m < k/m
      linarith [h_logb_minus_1m_lt_km, h_f0_ratio_lower_bound]
    exact le_of_lt this

  -- (2)  –(1/m_real) ≤  logb_n_val - f0_ratio
  --     ↔  f0_ratio - logb_n_val ≤ 1/m_real
  have h_left : f0_ratio - logb_n_val ≤ 1 / m_real := by
    -- first prove  f0_ratio ≤ logb_n_val + 1/m_real
    have h_aux : f0_ratio ≤ logb_n_val + 1 / m_real := by
      have h2 : f0_ratio ≤ (k_real + 1) / m_real := h_f0_ratio_upper_bound
      have h3 : (k_real + 1) / m_real ≤ logb_n_val + 1 / m_real := by
        have h_base : k_real + 1 ≤ m_real * logb_n_val + 1 := by
          exact add_le_add_right h_k_le_m_logbn 1
        -- rewrite logb_n_val + 1/m_real as (m_real * logb_n_val + 1)/m_real
        rw [show logb_n_val + 1 / m_real = (m_real * logb_n_val + 1) / m_real by
              field_simp [mul_comm, ne_of_gt hm_real_pos]]
        exact (div_le_div_iff_of_pos_right hm_real_pos).mpr h_base
      exact h2.trans h3
    -- now sub_le_iff_le_add turns `f0_ratio ≤ logb_n_val + 1/m` into the goal
    -- The simplified goal becomes `f0_ratio ≤ 1 / m_real + logb_n_val` (due to simpa's canonicalization).
    -- h_aux is `f0_ratio ≤ logb_n_val + 1 / m_real`.
    -- Adding `add_comm` allows simpa to match these.
    simpa [sub_le_iff_le_add, add_comm] using h_aux

  -- Assemble and finish
  rw [abs_sub_comm f0_ratio logb_n_val]
  have h_bounds : AbsPair logb_n_val f0_ratio (1 / m_real) := ⟨h_right, h_left⟩
  exact abs_sub_le_iff.mpr h_bounds


/--
The ratio `(f0 H n : ℝ) / (f0 H b : ℝ)` is exactly `logb b n`.
Requires `H` to be non-trivial.
-/
theorem uniformEntropy_ratio_eq_logb {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) (hH_nontrivial : ∃ n' ≥ 1, f0 hH_axioms n' ≠ 0)
    {n b : ℕ} (hn_pos : n > 0) (hb_ge2 : b ≥ 2) :
    (f0 hH_axioms n : ℝ) / (f0 hH_axioms b : ℝ) = Real.logb b n := by
  apply eq_of_abs_sub_le_inv_ge_one_nat
  intro m hm_ge1
  exact logarithmic_trapping hH_axioms hH_nontrivial hn_pos (pos_of_one_le hm_ge1) hb_ge2

/--
The constant `C_H` relating `f0 H n` to `Real.log n`.
Defined as `(f0 H 2 : ℝ) / Real.log 2` if H is non-trivial, else 0.
This constant is `Real`-valued.
-/
noncomputable def C_constant_real {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) : Real :=
  by classical -- Use classical logic to ensure the condition is decidable
  exact if h_nontrivial : (∃ n' ≥ 1, f0 hH_axioms n' ≠ 0) then
    (f0 hH_axioms 2 : ℝ) / Real.log 2
  else
    0

/-- `C_constant_real` is non-negative. -/
lemma C_constant_real_nonneg {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) : C_constant_real hH_axioms ≥ 0 := by
  rw [C_constant_real]
  split_ifs with h_nontrivial
  · -- Case: H non-trivial
    have hf02_real_nonneg : (f0 hH_axioms 2 : ℝ) ≥ 0 := NNReal.coe_nonneg _
    have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num : (2:ℝ) > 1)
    exact div_nonneg hf02_real_nonneg (le_of_lt hlog2_pos)
  · -- Case: H trivial
    exact le_refl 0


/--
Rota's Uniform Theorem (final part of Phase 2):
`f0 H n` (coerced to Real) is `C * Real.log n`.
-/
theorem RotaUniformTheorem_formula_with_C_constant {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) :
    let C_val := C_constant_real hH_axioms
    (C_val ≥ 0 ∧
     ∀ (n : ℕ) (_hn_pos : n > 0), (f0 hH_axioms n : ℝ) = C_val * Real.log n) := by
  let C_val := C_constant_real hH_axioms
  constructor
  · exact C_constant_real_nonneg hH_axioms
  · intro n hn_pos
    -- Goal: (f0 hH_axioms n : ℝ) = C_val * Real.log n
    simp_rw [C_constant_real] -- Unfold C_val definition in the goal
    split_ifs with h_nontrivial
    · -- Case: H non-trivial. C_val_expanded = (f0 hH_axioms 2 : ℝ) / Real.log 2
      -- Goal: (f0 hH_axioms n : ℝ) = ((f0 hH_axioms 2 : ℝ) / Real.log 2) * Real.log n
      let F0N := (f0 hH_axioms n : ℝ)
      let F02 := (f0 hH_axioms 2 : ℝ)
      let LOGN := Real.log n
      let LOG2 := Real.log 2
      change F0N = (F02 / LOG2) * LOGN -- Makes the goal structure explicit with local names

      have h_ratio_eq_logb : F0N / F02 = Real.logb 2 n :=
        uniformEntropy_ratio_eq_logb hH_axioms h_nontrivial hn_pos (by norm_num : 2 ≥ 2)

      have hf02_ne_zero : F02 ≠ 0 := by
        exact coe_ne_zero.mpr (uniformEntropy_pos_of_nontrivial hH_axioms h_nontrivial (by norm_num))
      have hlog2_ne_zero : LOG2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (2:ℝ) > 1))
      have hn_real_pos : (n:ℝ) > 0 := Nat.cast_pos.mpr hn_pos
      have h2_real_pos : (2:ℝ) > 0 := by norm_num

      -- Rewrite logb using log: F0N / F02 = LOGN / LOG2
      rw [Real.logb] at h_ratio_eq_logb
      -- Note: Real.logb_def is logb b x = log x / log b.
      -- This changes h_ratio_eq_logb to: F0N / F02 = LOGN / LOG2

      -- Now we have F0N / F02 = LOGN / LOG2
      -- Goal is F0N = (F02 / LOG2) * LOGN
      rw [div_eq_iff hf02_ne_zero] at h_ratio_eq_logb
      -- h_ratio_eq_logb is now: F0N = (LOGN / LOG2) * F02
      -- Goal is:                F0N = (F02 / LOG2) * LOGN
      rw [h_ratio_eq_logb]
      -- Goal: (LOGN / LOG2) * F02 = (F02 / LOG2) * LOGN
      -- This can be rearranged using field properties
      -- field_simp [hlog2_ne_zero] -- Should simplify both sides to (LOGN * F02) / LOG2
      -- The goal is (Real.log ↑n / Real.log 2) * F02 = F02 / Real.log 2 * Real.log ↑n
      -- which simplifies to (Real.log n * F02) / Real.log 2 = (F02 * Real.log n) / Real.log 2.
      -- This is true by commutativity of multiplication. `ring` handles this.
      ring

    · -- Case: H trivial (¬h_nontrivial). C_val_expanded = 0
      -- Goal: (f0 hH_axioms n : ℝ) = 0 * Real.log n
      have hf0n_eq_0_nnreal : f0 hH_axioms n = 0 := by
        by_contra hf0n_ne_0_hyp
        -- Use the externalized lemma:
        -- hf0n_ne_0_implies_nontrivial takes (f0 H n ≠ 0) and (n > 0)
        -- and returns (∃ n' ≥ 1, f0 H n' ≠ 0)
        -- This contradicts h_nontrivial (which is ¬(∃ n' ≥ 1, f0 H n' ≠ 0))
        exact h_nontrivial (hf0n_ne_0_implies_nontrivial hH_axioms hf0n_ne_0_hyp hn_pos)
      simp only [hf0n_eq_0_nnreal, NNReal.coe_zero, zero_mul]

theorem RotaUniformTheorem {H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0}
    (hH_axioms : IsEntropyFunction H) :
    ∃ C ≥ 0, ∀ (n : ℕ) (_hn_pos : n > 0), (f0 hH_axioms n : ℝ) = C * Real.log n := by
  use C_constant_real hH_axioms
  exact RotaUniformTheorem_formula_with_C_constant hH_axioms
