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

import PPNP.Util.Basic

namespace PPNP.Entropy

open BigOperators Fin Real Topology NNReal Filter Nat
open PPNP.Util.Basic

/-!
# Formalizing Rota's Uniqueness of Entropy Theorem
**Goal:** Define `IsEntropyFunction` structure correctly, define `f n = H(uniform n)`,
prove `f 1 = 0`, and prove `f` is monotone.

**Correction:** Fixed all previous issues and added proof for `f0_mono`.
-/


/-- Define f(n) as the entropy H of the uniform distribution on n outcomes. Needs n > 0. -/
noncomputable def f {n : ℕ} (H : ∀ {m : ℕ}, (Fin m → NNReal) → Real) (_hn : n > 0) : Real :=
  H (λ _ : Fin n => uniformProb n)

/-- Define f₀(n) extending f to n=0. -/
noncomputable def f₀ (H : ∀ {m : ℕ}, (Fin m → NNReal) → Real) (n : ℕ) : Real :=
  if hn : n > 0 then f H hn else 0


/--
Definition: The constant `C` relating `f₀` to `log`.
It is defined as `f₀ H 2 / log 2` if the entropy function `H` is non-trivial
(meaning `f₀` is not identically zero for `n ≥ 1`), and `0` otherwise.
We use base `b=2` for the definition.
-/
noncomputable def C_constant (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ) : ℝ :=
  -- Explicitly use Classical.propDecidable for the condition so we don't have to Open Classical
  let _inst : Decidable (∃ n' ≥ 1, f₀ H n' ≠ 0) := Classical.propDecidable _
  if _h : ∃ n' ≥ 1, f₀ H n' ≠ 0 then
    f₀ H 2 / Real.log 2
  else
    0

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



/-- Core additivity property: `f₀(nm) = f₀(n) + f₀(m)`. -/
theorem f0_mul_eq_add_f0 (hH : IsEntropyFunction H) {n m : ℕ} (hn : n ≥ 1) (hm : m ≥ 1) :
    f₀ H (n * m) = f₀ H n + f₀ H m := by
  -- 1. Derive positivity from hypotheses n ≥ 1, m ≥ 1
  have hn_pos : n > 0 := one_le_iff_pos.mp hn
  have hm_pos : m > 0 := one_le_iff_pos.mp hm
  have hnm_pos : n * m > 0 := Nat.mul_pos hn_pos hm_pos

  -- 2. Define the uniform distributions involved
  let unif_n := fun (_ : Fin n) => uniformProb n
  let unif_m := fun (_ : Fin m) => uniformProb m
  let unif_nm := fun (_ : Fin (n * m)) => uniformProb (n * m)

  -- 3. Verify the sum = 1 hypotheses for the component distributions
  have h_sum_n : ∑ i, unif_n i = 1 := sum_uniform_eq_one hn_pos
  have h_sum_m : ∑ i, unif_m i = 1 := sum_uniform_eq_one hm_pos

  -- 4. Apply Axiom 4 (prop4_additivity_product)
  have H_prod_eq_sum_H : H (product_dist unif_n unif_m) = H unif_n + H unif_m :=
    hH.prop4_additivity_product unif_n unif_m h_sum_n h_sum_m

  -- 5. Substitute the result that the product of uniforms is uniform
  have prod_is_uniform : product_dist unif_n unif_m = unif_nm :=
    uniformProb_product_uniformProb_is_uniformProb hn_pos hm_pos
  rw [prod_is_uniform] at H_prod_eq_sum_H
  -- Equation is now: H unif_nm = H unif_n + H unif_m

  -- 6. Translate from H(uniform) to f₀ using definitions of f₀ and f
  -- Goal: f₀ H (n * m) = f₀ H n + f₀ H m
  -- LHS: f₀ H (n * m) = f H hnm_pos = H unif_nm (using dif_pos hnm_pos, and def of f)
  -- RHS: f₀ H n + f₀ H m = f H hn_pos + f H hm_pos = H unif_n + H unif_m
  -- So the goal becomes H unif_nm = H unif_n + H unif_m
  -- We use simp_rw to apply these definitions and positivity proofs
  simp_rw [f₀, dif_pos hn_pos, dif_pos hm_pos, dif_pos hnm_pos, f]
  -- The goal now directly matches the derived equation H_prod_eq_sum_H
  exact H_prod_eq_sum_H

-- Helper: Show the extended distribution for prop2 sums to 1 - Reuse from previous
lemma sum_p_ext_eq_one {n : ℕ} {p : Fin n → NNReal} (hp_sum : ∑ i : Fin n, p i = 1) :
    let p_ext := (λ i : Fin (n + 1) => if h : i.val < n then p (Fin.castLT i h) else 0)
    (∑ i : Fin (n + 1), p_ext i) = 1 := by
  intro p_ext
  rw [Fin.sum_univ_castSucc]
  have last_term_is_zero : p_ext (Fin.last n) = 0 := by
    simp only [p_ext, Fin.val_last, lt_self_iff_false, dif_neg, not_false_iff]
  rw [last_term_is_zero, add_zero]
  have sum_eq : ∑ (i : Fin n), p_ext (Fin.castSucc i) = ∑ (i : Fin n), p i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [p_ext]
    have h_lt : (Fin.castSucc i).val < n := by exact i.is_lt
    rw [dif_pos h_lt, Fin.castLT_castSucc i h_lt]
  rw [sum_eq]
  exact hp_sum

-- stdShannonEntropyLn lemma for extended distribution (used if we prove relation for stdShannonEntropyLn)
lemma stdShannonEntropyLn_p_ext_eq_stdShannonEntropyLn {n : ℕ} (p : Fin n → NNReal) :
    let p_ext := (λ i : Fin (n + 1) => if h : i.val < n then p (Fin.castLT i h) else 0)
    stdShannonEntropyLn p_ext = stdShannonEntropyLn p := by
  intro p_ext
  simp_rw [stdShannonEntropyLn]
  rw [Fin.sum_univ_castSucc]
  have last_term_val_is_zero : p_ext (Fin.last n) = 0 := by
    simp only [p_ext, Fin.val_last, lt_self_iff_false, dif_neg, not_false_iff]
  rw [last_term_val_is_zero, NNReal.coe_zero, negMulLog_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply congr_arg negMulLog
  apply NNReal.coe_inj.mpr
  simp only [p_ext]
  have h_lt : (Fin.castSucc i).val < n := by exact i.is_lt
  rw [dif_pos h_lt, Fin.castLT_castSucc i h_lt]




-- ##################################################
-- Basic Properties of f₀(n)
-- ##################################################

/-- Property: f₀(1) = 0 -/
theorem f0_1_eq_0 (hH : IsEntropyFunction H) : f₀ H 1 = 0 := by
  have h1 : 1 > 0 := Nat.one_pos
  simp only [f₀, dif_pos h1, f]
  have h_unif1_func : (λ _ : Fin 1 => uniformProb 1) = (λ _ : Fin 1 => 1) := by
    funext i
    simp only [uniformProb, dif_pos h1, Nat.cast_one, inv_one]
  rw [h_unif1_func]
  exact hH.prop0_H1_eq_0

/-- Property: f₀ is monotone non-decreasing -/
theorem f0_mono (hH : IsEntropyFunction H) : Monotone (f₀ H) := by
  -- Use monotone_nat_of_le_succ: prove f₀ n ≤ f₀ (n + 1) for all n
  apply monotone_nat_of_le_succ
  intro n
  -- Case split on n
  if hn_zero : n = 0 then
    -- Case n = 0: Need f₀ 0 ≤ f₀ 1
    rw [hn_zero]
    rw [f0_1_eq_0 hH] -- f₀ 1 = 0
    simp only [f₀, dif_neg (Nat.not_lt_zero 0)]
    exact le_refl 0 -- 0 ≤ 0
  else
    -- Case n ≥ 1: Need f₀ n ≤ f₀ (n + 1)
    -- Get proofs that n > 0 and n + 1 > 0
    have hn_pos : n > 0 := Nat.pos_of_ne_zero hn_zero
    have hn1_pos : n + 1 > 0 := Nat.succ_pos n

    -- Unfold f₀ for n and n + 1
    have f0_n_def : f₀ H n = f H hn_pos := dif_pos hn_pos
    have f0_n1_def : f₀ H (n + 1) = f H hn1_pos := dif_pos hn1_pos
    rw [f0_n_def, f0_n1_def] -- Now goal is f H hn_pos ≤ f H hn1_pos
    simp_rw [f] -- Unfold f: goal is H (uniform n) ≤ H (uniform (n+1))

    -- Define the uniform distribution on n outcomes
    let unif_n := (λ _ : Fin n => uniformProb n)
    -- Define the extended distribution p on n+1 outcomes
    let p := (λ i : Fin (n + 1) => if h : i.val < n then unif_n (Fin.castLT i h) else 0)

    -- Show p sums to 1
    have h_sum_n : ∑ i : Fin n, unif_n i = 1 := sum_uniform_eq_one hn_pos
    have h_sum_p : ∑ i : Fin (n + 1), p i = 1 := sum_p_ext_eq_one h_sum_n

    -- Relate H p to H (uniform n) using Property 2
    have h_p_eq_H_unif_n : H p = H unif_n := by
       -- Need to provide the explicit function H to prop2_zero_inv
       exact hH.prop2_zero_inv unif_n h_sum_n

    -- Relate H p to H (uniform n+1) using Property 5
    -- Direct application of prop5 and simplify uniformProb
    have h_p_le_H_unif_n1 : H p ≤ H (λ _ : Fin (n + 1) => uniformProb (n + 1)) := by
      have h5 := hH.prop5_max_uniform hn1_pos p h_sum_p
      simpa [uniformProb, hn1_pos] using h5

    -- Combine the results: H (uniform n) = H p ≤ H (uniform n+1)
    rw [← h_p_eq_H_unif_n] -- Replace H (uniform n) with H p
    exact h_p_le_H_unif_n1 -- The goal is now exactly this inequality

/-!
Chunk 1 Completed. Next Step: Chunk 2 - The Power Law `f₀(n^k) = k * f₀(n)`.
-/

/-!
### Chunk 2: The Power Law `f₀(n^k) = k * f₀(n)`

**Step 1: State the Assumed Lemma (Consequence of Prop 4)**
**Step 2: Prove the Main Power Law `uniformEntropy_power_law`**
 Assumed step relation derived from Property 4 (Conditional Entropy). -/

lemma uniformEntropy_product_recursion {n k : ℕ} (hH : IsEntropyFunction H) (hn : n ≥ 1) (_hk : k ≥ 1) : -- hk is not used here but kept for consistency
    f₀ H (n ^ (k + 1)) = f₀ H (n ^ k) + f₀ H n := by
  -- Rewrite n^(k+1) as n * n^k to match f0_mul_eq_add_f0's a * b form
  rw [pow_succ'] -- n^(k+1) = n * n^k

  -- Prove the hypothesis n^k ≥ 1 needed for f0_mul_eq_add_f0
  have hnk_ge1 : n ^ k ≥ 1 := by
    -- Use the provided Nat.one_le_pow lemma
    exact Nat.one_le_pow k n hn

  -- Apply the core additivity theorem f0_mul_eq_add_f0 H n (n^k)
  -- Need arguments H, n, n^k and hypotheses n ≥ 1 (hn) and n^k ≥ 1 (hnk_ge1)
  have h_add := f0_mul_eq_add_f0 hH hn hnk_ge1
  -- h_add: f₀ H (n * n ^ k) = f₀ H n + f₀ H (n ^ k)

  -- Rewrite the goal using h_add and commutativity of addition
  rw [h_add, add_comm] -- Goal: f₀ H n + f₀ H (n ^ k) = f₀ H (n ^ k) + f₀ H n
  -- The goal is now identical.

/-- Power law for `f₀`: `f₀(n^k) = k * f₀(n)`. -/
theorem uniformEntropy_power_law
  (_hH : IsEntropyFunction H) {n k : ℕ} (hn : n ≥ 1) (hk : k ≥ 1) :
    f₀ H (n ^ k) = (k : ℝ) * f₀ H n := by
  -- predicate we will induct on
  let P : ℕ → Prop := fun m ↦ f₀ H (n ^ m) = (m : ℝ) * f₀ H n

  -- base : `k = 1`
  have base : P 1 := by
    simp [P, pow_one]

  -- step : `m ≥ 1 → P m → P (m + 1)`
  have step : ∀ m, 1 ≤ m → P m → P (m + 1) := by
    intro m hm ih
    -- unfold the predicate
    simp [P] at ih ⊢
    -- entropy step (using the proven recursion)
    -- Correctly pass the IsEntropyFunction instance _hH first
    have hstep := uniformEntropy_product_recursion _hH hn hm -- Corrected line
    -- hstep: f₀ H (n ^ (m + 1)) = f₀ H (n ^ m) + f₀ H n

    -- rewrite with the step relation and IH
    rw [hstep, ih] -- Goal: ↑m * f₀ H n + f₀ H n = ↑(m + 1) * f₀ H n
    -- Simplify using ring tactic or explicit algebra
    ring -- Applies distributive law

  -- perform the induction starting at 1
  simpa [P] using
    Nat.le_induction (m := 1)
      base
      (fun m hm ih => step m hm ih)
      k
      hk



/-- Lemma: `f₀ H b ≥ 0` for `b ≥ 1`. -/
lemma f0_nonneg (hH : IsEntropyFunction H) {b : ℕ} (hb : b ≥ 1) : f₀ H b ≥ 0 := by
  have h_mono_prop : Monotone (f₀ H) := PPNP.Entropy.f0_mono hH
  have h_mono_ineq : f₀ H 1 ≤ f₀ H b := h_mono_prop hb
  have h_f0_1_zero : f₀ H 1 = 0 := PPNP.Entropy.f0_1_eq_0 hH
  rw [h_f0_1_zero] at h_mono_ineq
  exact h_mono_ineq

/-!
### The Trapping Argument Setup
-/


/-!
### Chunk 3.3: Inequalities from Trapping `f₀ H (n^m)`
Derive `(k/m) * f₀ H b ≤ f₀ H n ≤ ((k+1)/m) * f₀ H b` (or similar, being careful about division).
This is the core step relating `f₀ H n` and `f₀ H b` via the integer bounds.
-/

/-- Lemma: If `a ≤ b`, then `↑a ≤ ↑b` for `a, b : ℕ`. -/
lemma cast_le_cast {a b : ℕ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr h


/- Lemma: `f₀ H b > 0` if `H` is not identically zero and `b ≥ 2`.
### Chunk 3.3a: Breaking down uniformEntropy_pos_of_nontrivial
-/

/-- Lemma 1: If f₀ H b = 0 for some b ≥ 2, then f₀ H 2 = 0. -/
lemma f0_2_eq_zero_of_f0_b_eq_zero {b : ℕ} (hH : IsEntropyFunction H) (hb : b ≥ 2) (hf0b_eq_0 : f₀ H b = 0) :
    f₀ H 2 = 0 := by
  -- Get monotonicity and non-negativity properties using hH
  have h_mono := f0_mono hH
  have h_f0_2_ge_0 : f₀ H 2 ≥ 0 := f0_nonneg hH (by linarith : 2 ≥ 1)

  -- Apply monotonicity: f₀(2) ≤ f₀(b) since 2 ≤ b
  have h_f0_2_le_b : f₀ H 2 ≤ f₀ H b := h_mono hb

  -- Combine inequalities: 0 ≤ f₀ H 2 ≤ f₀ H b = 0
  -- Rewrite with the assumption f₀ H b = 0
  rw [hf0b_eq_0] at h_f0_2_le_b -- Now have f₀ H 2 ≤ 0

  -- Conclude f₀ H 2 = 0 using antisymmetry (or linarith)
  -- We have f₀ H 2 ≥ 0 and f₀ H 2 ≤ 0
  linarith [h_f0_2_ge_0, h_f0_2_le_b]

/-!
### Chunk 3.3b: Breaking down uniformEntropy_pos_of_nontrivial
-/

/-- Lemma 2: If f₀ H 2 = 0, then f₀ H (2^k) = 0 for all k ≥ 1. -/
lemma f0_pow2_eq_zero_of_f0_2_eq_zero {k : ℕ} (hH : IsEntropyFunction H) (hf0_2_eq_0 : f₀ H 2 = 0) (hk : k ≥ 1) :
    f₀ H (2 ^ k) = 0 := by
  -- Apply the power law f₀(n^k) = k * f₀(n) with n=2
  have h_pow_law := uniformEntropy_power_law hH (by norm_num : 2 ≥ 1) hk
  -- h_pow_law : f₀ H (2 ^ k) = ↑k * f₀ H 2

  -- Substitute the assumption f₀ H 2 = 0
  rw [hf0_2_eq_0] at h_pow_law
  -- h_pow_law : f₀ H (2 ^ k) = ↑k * 0

  -- Simplify
  rw [mul_zero] at h_pow_law
  exact h_pow_law


/-!
### Chunk 3.3d: Breaking down uniformEntropy_pos_of_nontrivial
-/

-- Re-include the custom exists_pow_ge lemma and its use in exists_pow2_bound
lemma exists_pow_ge {a n : ℕ} (ha : 1 < a) : ∃ k : ℕ, n ≤ a ^ k :=
by
  cases n with
  | zero =>
      use 0
      exact Nat.zero_le (a ^ 0)
  | succ m =>
      use (m + 1)
      have h_lt : m + 1 < a ^ (m + 1) := Nat.lt_pow_self ha
      exact Nat.le_of_lt h_lt

lemma exists_pow2_bound {n : ℕ} (_hn : n ≥ 1) : ∃ k ≥ 1, n ≤ 2 ^ k := by
  have h2_gt_1 : 1 < 2 := by norm_num
  have h_exists_k0 : ∃ k₀ : ℕ, n ≤ 2 ^ k₀ := exists_pow_ge h2_gt_1
  rcases h_exists_k0 with ⟨k₀, h_n_le_pow_k₀⟩
  let k := max 1 k₀
  use k
  have hk_ge_1 : k ≥ 1 := Nat.le_max_left 1 k₀
  have hk₀_le_k : k₀ ≤ k := Nat.le_max_right 1 k₀
  have h_pow_mono : 2 ^ k₀ ≤ 2 ^ k := Nat.pow_le_pow_right (Nat.le_of_lt h2_gt_1) hk₀_le_k
  have hn_le_pow_k : n ≤ 2 ^ k := le_trans h_n_le_pow_k₀ h_pow_mono
  exact ⟨hk_ge_1, hn_le_pow_k⟩

/-- Lemma 4: If f₀ H (2^k) = 0 for all k ≥ 1, then f₀ H n = 0 for all n ≥ 1. -/
lemma f0_n_eq_zero_of_f0_pow2_zero {n : ℕ} (hH : IsEntropyFunction H)
    (h_f0_pow2_zero : ∀ k ≥ 1, f₀ H (2 ^ k) = 0) (hn : n ≥ 1) :
    f₀ H n = 0 := by
  -- Find k ≥ 1 such that n ≤ 2^k
  rcases exists_pow2_bound hn with ⟨k, hk_ge1, hn_le_pow2⟩

  -- Apply monotonicity of f₀ H
  have h_mono := f0_mono hH
  have h_f0_n_le_pow2 : f₀ H n ≤ f₀ H (2 ^ k) := h_mono hn_le_pow2

  -- Use the assumption that f₀ H (2^k) = 0 for k ≥ 1
  have h_f0_pow2_is_zero : f₀ H (2 ^ k) = 0 := h_f0_pow2_zero k hk_ge1

  -- Combine: f₀ H n ≤ 0
  rw [h_f0_pow2_is_zero] at h_f0_n_le_pow2

  -- Apply non-negativity: f₀ H n ≥ 0
  have h_f0_n_ge_0 : f₀ H n ≥ 0 := f0_nonneg hH hn

  -- Conclude f₀ H n = 0 by antisymmetry (or linarith)
  linarith [h_f0_n_ge_0, h_f0_n_le_pow2]

/-!
### Chunk 3.3e: Breaking down uniformEntropy_pos_of_nontrivial
-/

/-- Lemma 5: If f₀ H b = 0 for some b ≥ 2, then f₀ H n = 0 for all n ≥ 1. -/
lemma f0_all_zero_of_f0_b_zero {b : ℕ} (hH : IsEntropyFunction H) (hb : b ≥ 2) (hf0b_eq_0 : f₀ H b = 0) :
    ∀ n ≥ 1, f₀ H n = 0 := by
  -- Introduce n and the assumption n ≥ 1
  intro n hn

  -- Step 1: Show f₀ H 2 = 0
  have hf0_2_eq_0 : f₀ H 2 = 0 := f0_2_eq_zero_of_f0_b_eq_zero hH hb hf0b_eq_0

  -- Step 2: Define the hypothesis needed for the next lemma
  -- We need to show that f₀ H (2^k) = 0 for all k ≥ 1
  have h_f0_pow2_zero : ∀ k ≥ 1, f₀ H (2 ^ k) = 0 := by
    intro k hk
    exact f0_pow2_eq_zero_of_f0_2_eq_zero hH hf0_2_eq_0 hk

  -- Step 3: Apply the lemma showing f₀ H n = 0
  exact f0_n_eq_zero_of_f0_pow2_zero hH h_f0_pow2_zero hn


/-!
### Chunk 3.3f: Final Lemma for Positive f₀(b)
-/

/-- Lemma 6 (Original Goal): `f₀ H b > 0` if `H` is not identically zero and `b ≥ 2`. -/
lemma uniformEntropy_pos_of_nontrivial (hH : IsEntropyFunction H) (hH_nonzero : ∃ n ≥ 1, f₀ H n ≠ 0) (hb : b ≥ 2) :
    f₀ H b > 0 := by
  -- Start proof by contradiction
  by_contra h_f0_b_not_pos
  -- `h_f0_b_not_pos : ¬(f₀ H b > 0)`

  -- We know f₀ H b ≥ 0 from f0_nonneg
  have h_f0_b_ge_0 : f₀ H b ≥ 0 := f0_nonneg hH (by linarith : b ≥ 1)

  -- If f₀ H b is not positive and is non-negative, it must be zero
  have hf0b_eq_0 : f₀ H b = 0 := by
    linarith [h_f0_b_ge_0, h_f0_b_not_pos]

  -- Use the lemma showing that if f₀ H b = 0, then f₀ H n = 0 for all n ≥ 1
  have h_all_zero : ∀ n ≥ 1, f₀ H n = 0 := f0_all_zero_of_f0_b_zero hH hb hf0b_eq_0

  -- Extract the witness n_nz from the assumption hH_nonzero
  rcases hH_nonzero with ⟨n_nz, hn_nz_ge1, h_f0_n_nz_neq_0⟩

  -- Apply the "all zero" result to n_nz
  have h_f0_n_nz_eq_0 : f₀ H n_nz = 0 := h_all_zero n_nz hn_nz_ge1

  -- This contradicts the hypothesis that f₀ H n_nz ≠ 0
  exact h_f0_n_nz_neq_0 h_f0_n_nz_eq_0

lemma nat_bounds_from_cast_pow_bounds {b k n m : ℕ}
    (h_le_cast : (b : ℝ) ^ k ≤ (n : ℝ) ^ m)
    (h_lt_cast : (n : ℝ) ^ m < (b : ℝ) ^ (k + 1)) :
    b ^ k ≤ n ^ m ∧ n ^ m < b ^ (k + 1) := by

  -- Rewrite the hypotheses using Nat.cast_pow forwards to get the form ↑(...) required by mp
  rw [← Nat.cast_pow b k] at h_le_cast      -- Goal: Transform (↑b)^k into ↑(b^k)
  rw [← Nat.cast_pow n m] at h_le_cast      -- Goal: Transform (↑n)^m into ↑(n^m)
                                            -- h_le_cast is now ↑(b^k) ≤ ↑(n^m)

  rw [← Nat.cast_pow n m] at h_lt_cast      -- Goal: Transform (↑n)^m into ↑(n^m)
  rw [← Nat.cast_pow b (k + 1)] at h_lt_cast -- Goal: Transform (↑b)^(k+1) into ↑(b^(k+1))
                                             -- h_lt_cast is now ↑(n^m) < ↑(b^(k+1))

  -- Convert the inequalities involving casts back to Nat inequalities using mp
  constructor
  · -- Prove b^k ≤ n^m
    exact Nat.cast_le.mp h_le_cast
  · -- Prove n^m < b^(k+1)
    exact Nat.cast_lt.mp h_lt_cast

/--
Lemma: Convert Nat bounds `Bk ≤ Nm < Bkp1` to Real bounds on `f₀ H`.
-/
lemma f0_bounds_from_nat_bounds (hH : IsEntropyFunction H)
    {Bk Nm Bkp1 : ℕ} (h_le : Bk ≤ Nm) (h_lt : Nm < Bkp1) :
    f₀ H Bk ≤ f₀ H Nm ∧ f₀ H Nm ≤ f₀ H Bkp1 := by
  -- Get the monotonicity property of f₀ H
  have h_mono := f0_mono hH

  -- Apply monotonicity to the first inequality Bk ≤ Nm
  have h_f0_le1 : f₀ H Bk ≤ f₀ H Nm := h_mono h_le

  -- Convert the strict inequality Nm < Bkp1 to non-strict Nm ≤ Bkp1
  have h_le_from_lt : Nm ≤ Bkp1 := Nat.le_of_lt h_lt
  -- Apply monotonicity to the second (non-strict) inequality Nm ≤ Bkp1
  have h_f0_le2 : f₀ H Nm ≤ f₀ H Bkp1 := h_mono h_le_from_lt

  -- Combine the two derived f₀ H inequalities using the constructor for ∧
  constructor
  · exact h_f0_le1
  · exact h_f0_le2


/-- Helper 4a: Apply power law to the middle term f₀ H (n^m). -/
lemma f0_pow_middle (hH : IsEntropyFunction H) {n m : ℕ} (hn : n ≥ 1) (hm : m ≥ 1) :
    f₀ H (n ^ m) = (m : ℝ) * f₀ H n := by
  exact uniformEntropy_power_law hH hn hm

/-- Helper 4b: Apply power law to the left term f₀ H (b^k) when k ≥ 1. -/
lemma f0_pow_left_k_ge_1 (hH : IsEntropyFunction H) {b k : ℕ} (hb_ge1 : b ≥ 1) (hk_ge1 : k ≥ 1) :
    f₀ H (b ^ k) = (k : ℝ) * f₀ H b := by
  exact uniformEntropy_power_law hH hb_ge1 hk_ge1

/-- Helper 4c: Apply power law to the right term f₀ H (b^(k+1)) when k ≥ 0. -/
lemma f0_pow_right (hH : IsEntropyFunction H) {b k : ℕ} (hb_ge1 : b ≥ 1) :
    f₀ H (b ^ (k + 1)) = ((k : ℝ) + 1) * f₀ H b := by
  have hkp1_ge1 : k + 1 ≥ 1 := Nat.succ_pos k
  have raw_pow_law := uniformEntropy_power_law hH hb_ge1 hkp1_ge1 -- Gives ↑(k+1) * f₀ H b
  rw [Nat.cast_add_one k] at raw_pow_law -- Rewrites ↑(k+1) to ↑k + 1
  exact raw_pow_law

/-- Helper 4d: Combine power laws for the k ≥ 1 case. -/
lemma apply_power_law_k_ge_1 (hH : IsEntropyFunction H)
    {n m b k : ℕ} (hn : n ≥ 1) (hm : m ≥ 1) (hb : b ≥ 2) (hk_ge1 : k ≥ 1)
    (h_f0_le1_orig : f₀ H (b ^ k) ≤ f₀ H (n ^ m))
    (h_f0_le2_orig : f₀ H (n ^ m) ≤ f₀ H (b ^ (k + 1))) :
    (k : ℝ) * f₀ H b ≤ (m : ℝ) * f₀ H n ∧ (m : ℝ) * f₀ H n ≤ ((k : ℝ) + 1) * f₀ H b := by
  have hb_ge1 : b ≥ 1 := by linarith [hb]
  -- Apply power laws using the helpers
  let h_mid := f0_pow_middle hH hn hm
  let h_left := f0_pow_left_k_ge_1 hH hb_ge1 hk_ge1
  let h_right := f0_pow_right hH (b := b) (k := k) hb_ge1 -- Explicitly provide b and k

  -- Rewrite the original inequalities
  rw [h_left, h_mid] at h_f0_le1_orig
  rw [h_mid, h_right] at h_f0_le2_orig

  exact ⟨h_f0_le1_orig, h_f0_le2_orig⟩

/-- Helper 4e: Handle the k = 0 case. -/
lemma apply_power_law_k_eq_0 (hH : IsEntropyFunction H)
    {n m b : ℕ} (hn : n ≥ 1) (hm : m ≥ 1) (_hb : b ≥ 2) -- hb needed for context but not directly used
    (h_f0_le1_orig : f₀ H (b ^ 0) ≤ f₀ H (n ^ m))
    (h_f0_le2_orig : f₀ H (n ^ m) ≤ f₀ H (b ^ (0 + 1))) :
    (0 : ℝ) * f₀ H b ≤ (m : ℝ) * f₀ H n ∧ (m : ℝ) * f₀ H n ≤ ((0 : ℝ) + 1) * f₀ H b := by
  -- Apply power law to middle term
  let h_mid := f0_pow_middle hH hn hm

  -- Simplify bounds involving k=0
  rw [pow_zero] at h_f0_le1_orig -- f₀ H 1 ≤ f₀ H (n^m)
  rw [zero_add, pow_one] at h_f0_le2_orig -- f₀ H (n^m) ≤ f₀ H b

  -- Use f₀ H 1 = 0
  rw [f0_1_eq_0 hH] at h_f0_le1_orig -- 0 ≤ f₀ H (n^m)

  -- Rewrite middle term
  rw [h_mid] at h_f0_le1_orig h_f0_le2_orig -- 0 ≤ ↑m * f₀ H n ∧ ↑m * f₀ H n ≤ f₀ H b

  -- Construct the target structure
  constructor
  · -- Left inequality: 0 * f₀ H b ≤ ↑m * f₀ H n
    rw [zero_mul] -- Goal: 0 ≤ ↑m * f₀ H n
    exact h_f0_le1_orig
  · -- Right inequality: ↑m * f₀ H n ≤ (0 + 1) * f₀ H b
    simp only [zero_add, one_mul] -- Goal: ↑m * f₀ H n ≤ f₀ H b
    exact h_f0_le2_orig

/--
Lemma (Final Assembly): Apply the power law `f₀(a^p) = p * f₀(a)` to the bounds
`f₀ H (b^k) ≤ f₀ H (n^m) ≤ f₀ H (b^(k+1))`.
Requires appropriate positivity conditions `n ≥ 1, m ≥ 1, b ≥ 2`.
Handles the case k=0 separately using helper lemmas.
-/
lemma f0_bounds_apply_power_law (hH : IsEntropyFunction H)
    {n m b k : ℕ} (hn : n ≥ 1) (hm : m ≥ 1) (hb : b ≥ 2)
    (h_f0_bounds : f₀ H (b ^ k) ≤ f₀ H (n ^ m) ∧ f₀ H (n ^ m) ≤ f₀ H (b ^ (k + 1))) :
    (k : ℝ) * f₀ H b ≤ (m : ℝ) * f₀ H n ∧ (m : ℝ) * f₀ H n ≤ ((k : ℝ) + 1) * f₀ H b := by

  -- Deconstruct the input bounds
  rcases h_f0_bounds with ⟨h_f0_le1_orig, h_f0_le2_orig⟩

  -- Case split on k
  if hk_zero : k = 0 then
    -- Case k = 0
    -- Rewrite the original bounds using k=0 *before* calling the helper
    rw [hk_zero] at h_f0_le1_orig h_f0_le2_orig
    -- Now h_f0_le1_orig : f₀ H (b ^ 0) ≤ f₀ H (n ^ m)
    -- And h_f0_le2_orig : f₀ H (n ^ m) ≤ f₀ H (b ^ (0 + 1))

    -- Use the k=0 helper lemma with the rewritten bounds
    have result_k0 := apply_power_law_k_eq_0 hH hn hm hb h_f0_le1_orig h_f0_le2_orig
    -- result_k0 : 0 * f₀ H b ≤ ↑m * f₀ H n ∧ ↑m * f₀ H n ≤ (0 + 1) * f₀ H b

    -- Rewrite the *goal* using k=0 to match the result
    rw [hk_zero] -- Goal: (0:ℝ)*f₀ H b ≤ ... ∧ ... ≤ ((0:ℝ)+1)*f₀ H b
    simp only [Nat.cast_zero] -- Goal: 0*f₀ H b ≤ ... ∧ ... ≤ (0+1)*f₀ H b

    -- Now the result_k0 should exactly match the goal
    exact result_k0
  else
    -- Case k ≠ 0, implies k ≥ 1
    have hk_ge1 : k ≥ 1 := Nat.pos_of_ne_zero hk_zero
    -- Use the k ≥ 1 helper lemma with the original bounds
    exact apply_power_law_k_ge_1 hH hn hm hb hk_ge1 h_f0_le1_orig h_f0_le2_orig

lemma div_bounds_from_mul_bounds {A B C D E : ℝ} (hC : C > 0) (hD : D > 0)
    (h_le1 : A * C ≤ B * D) (h_le2 : B * D ≤ E * C) :
    A / D ≤ B / C ∧ B / C ≤ E / D := by
  constructor
  · -- Prove A / D ≤ B / C
    -- Use div_le_div_iff which states (a / d ≤ b / c ↔ a * c ≤ b * d) given d > 0, c > 0
    rwa [div_le_div_iff₀ hD hC] -- Rewrites goal A / D ≤ B / C to A * C ≤ B * D and uses h_le1
  · -- Prove B / C ≤ E / D
    -- Use div_le_div_iff which states (b / c ≤ e / d ↔ b * d ≤ e * c) given c > 0, d > 0
    rwa [div_le_div_iff₀ hC hD] -- Rewrites goal B / C ≤ E / D to B * D ≤ E * C and uses h_le2
/-! ### Chunk 3.4 - Breakdown Step 3 -/


/-! ## Chunk 3.3: THEOREM!!! Trapping Inequalities
Theorem: Establishes the core trapping inequalities relating the ratio `f₀ H n / f₀ H b`
to the ratio `k / m` derived from integer power bounds `b^k ≤ n^m < b^(k+1)`.
Requires H to be non-trivial (`hH_nonzero`).
-/
theorem uniformEntropy_ratio_bounds_by_rational (hH : IsEntropyFunction H) (hH_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0)
    {n m b : ℕ} (hn : n ≥ 1) (hm : m ≥ 1) (hb : b ≥ 2) :
    ∃ k : ℕ, (k : ℝ) / m ≤ f₀ H n / f₀ H b ∧ f₀ H n / f₀ H b ≤ (k + 1 : ℝ) / m := by

  -- Step 1 & 2: Define x = (n:ℝ)^m (Nat power) and prove x ≥ 1.
  let x : ℝ := (n : ℝ) ^ m
  have hx_ge_1 : x ≥ 1 := one_le_pow_cast hn -- Use Nat power version

  -- Step 3: Get k and power bounds b^k ≤ x < b^(k+1)
  -- exists_nat_pow_bounds expects (b:ℝ)^k and (b:ℝ)^(k+1) which are Nat powers.
  rcases exists_nat_pow_bounds hb hx_ge_1 with ⟨k, h_bk_le_x, h_x_lt_bkp1⟩
  -- h_bk_le_x : (b:ℝ)^k ≤ x = (n:ℝ)^m
  -- h_x_lt_bkp1 : x = (n:ℝ)^m < (b:ℝ)^(k+1)

  -- Step 4: Convert Real bounds (involving Nat powers of casts) to Nat bounds
  let Bk := b ^ k
  let Nm := n ^ m
  let Bkp1 := b ^ (k + 1)
  have h_nat_bounds : Bk ≤ Nm ∧ Nm < Bkp1 :=
    nat_bounds_from_cast_pow_bounds h_bk_le_x h_x_lt_bkp1

  -- Step 5: Get f₀ H bounds from Nat bounds
  have h_f0_bounds := f0_bounds_from_nat_bounds hH h_nat_bounds.1 h_nat_bounds.2

  -- Step 6: Apply power law to get multiplication bounds
  have h_mul_bounds := f0_bounds_apply_power_law hH hn hm hb h_f0_bounds
  rcases h_mul_bounds with ⟨h_mul_le1, h_mul_le2⟩
  -- h_mul_le1: ↑k * f₀ H b ≤ ↑m * f₀ H n
  -- h_mul_le2: ↑m * f₀ H n ≤ (↑k + 1) * f₀ H b

  -- Step 7: Prepare for division
  have hf0b_pos : f₀ H b > 0 := uniformEntropy_pos_of_nontrivial hH hH_nonzero hb
  have hm_pos_real : 0 < (m : ℝ) := Nat.cast_pos.mpr (by linarith [hm] : m > 0)

  -- Step 8: Apply division logic
  -- Use the k found in Step 3
  use k
  constructor
  · -- Prove k / m ≤ f₀ H n / f₀ H b
    -- Start from h_mul_le1: k * f₀ H b ≤ m * f₀ H n
    -- Rewrite using mul_comm to match div_le_div_iff more easily
    rw [mul_comm (m : ℝ) _] at h_mul_le1 -- k * f₀ H b ≤ (f₀ H n) * m
    -- Use (a / d ≤ b / c ↔ a * c ≤ b * d) with a=k, d=m, b=f₀ H n, c=f₀ H b
    -- Need k * f₀ H b ≤ f₀ H n * m
    rwa [div_le_div_iff₀ hm_pos_real hf0b_pos] -- Goal: k / m ≤ f₀ H n / f₀ H b
  · -- Prove f₀ H n / f₀ H b ≤ (k + 1) / m
    -- Start from h_mul_le2: m * f₀ H n ≤ (↑k + 1) * f₀ H b
    -- Rewrite using mul_comm
    rw [mul_comm (m : ℝ) _] at h_mul_le2 -- (f₀ H n) * m ≤ (↑k + 1) * f₀ H b
    -- Use (b / c ≤ e / d ↔ b * d ≤ e * c) with b=f₀ H n, c=f₀ H b, e=k+1, d=m
    -- Need (f₀ H n) * m ≤ (k + 1) * f₀ H b
    rwa [div_le_div_iff₀ hf0b_pos hm_pos_real] -- Goal: f₀ H n / f₀ H b ≤ (k + 1) / m


/-! ## Chunk 3.4: logb properties -/


/--
Lemma: Guarantees the existence of `k : ℕ` satisfying both the power bounds
`(b : ℝ) ^ k ≤ (n : ℝ) ^ m ∧ (n : ℝ) ^ m < (b : ℝ) ^ (k + 1)`
and the ratio bounds derived from `uniformEntropy_ratio_bounds_by_rational`.
This lemma essentially packages the result of `uniformEntropy_ratio_bounds_by_rational` along
with the power bounds used to derive it.
-/
lemma k_from_f0_trap_satisfies_pow_bounds (hH : IsEntropyFunction H) (hH_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0)
    {n m b : ℕ} (hn : n ≥ 1) (hm : m ≥ 1) (hb : b ≥ 2) :
    ∃ k : ℕ,
      -- Power bounds
      ((b : ℝ) ^ k ≤ (n : ℝ) ^ m ∧ (n : ℝ) ^ m < (b : ℝ) ^ (k + 1)) ∧
      -- Ratio bounds
      ((k : ℝ) / m ≤ f₀ H n / f₀ H b ∧ f₀ H n / f₀ H b ≤ (k + 1 : ℝ) / m) := by
  -- Step 1 & 2: Define x = (n:ℝ)^m (Nat power) and prove x ≥ 1.
  let x : ℝ := (n : ℝ) ^ m
  have hx_ge_1 : x ≥ 1 := one_le_pow_cast hn

  -- Step 3: Get k and power bounds b^k ≤ x < b^(k+1) using exists_nat_pow_bounds
  rcases exists_nat_pow_bounds hb hx_ge_1 with ⟨k, h_bk_le_x, h_x_lt_bkp1⟩
  -- h_bk_le_x : (b:ℝ)^k ≤ x = (n:ℝ)^m
  -- h_x_lt_bkp1 : x = (n:ℝ)^m < (b:ℝ)^(k+1)

  -- Claim existence of this specific k
  use k

  -- Prove the conjunction: (Power bounds) ∧ (Ratio bounds)
  constructor
  · -- Prove Power bounds: These are exactly h_bk_le_x and h_x_lt_bkp1
    exact ⟨h_bk_le_x, h_x_lt_bkp1⟩
  · -- Prove Ratio bounds: This follows the logic from uniformEntropy_ratio_bounds_by_rational proof for *this* k

    -- Step 4: Convert Real bounds (involving Nat powers of casts) to Nat bounds
    let Bk := b ^ k
    let Nm := n ^ m
    let Bkp1 := b ^ (k + 1)
    have h_nat_bounds : Bk ≤ Nm ∧ Nm < Bkp1 :=
      nat_bounds_from_cast_pow_bounds h_bk_le_x h_x_lt_bkp1

    -- Step 5: Get f₀ H bounds from Nat bounds
    have h_f0_bounds := f0_bounds_from_nat_bounds hH h_nat_bounds.1 h_nat_bounds.2

    -- Step 6: Apply power law to get multiplication bounds
    have h_mul_bounds := f0_bounds_apply_power_law hH hn hm hb h_f0_bounds
    rcases h_mul_bounds with ⟨h_mul_le1, h_mul_le2⟩
    -- h_mul_le1: ↑k * f₀ H b ≤ ↑m * f₀ H n
    -- h_mul_le2: ↑m * f₀ H n ≤ (↑k + 1) * f₀ H b

    -- Step 7: Prepare for division (need f₀ H b > 0 and m > 0)
    have hf0b_pos : f₀ H b > 0 := uniformEntropy_pos_of_nontrivial hH hH_nonzero hb
    have hm_pos_real : 0 < (m : ℝ) := Nat.cast_pos.mpr (by linarith [hm] : m > 0)

    -- Step 8: Apply division logic to get the ratio bounds
    constructor
    · -- Prove k / m ≤ f₀ H n / f₀ H b
      -- Start from h_mul_le1: k * f₀ H b ≤ m * f₀ H n
      rw [mul_comm (m : ℝ) _] at h_mul_le1 -- k * f₀ H b ≤ (f₀ H n) * m
      -- Use (a / d ≤ b / c ↔ a * c ≤ b * d) with a=k, d=m, b=f₀ H n, c=f₀ H b
      rwa [div_le_div_iff₀ hm_pos_real hf0b_pos] -- Goal: k / m ≤ f₀ H n / f₀ H b
    · -- Prove f₀ H n / f₀ H b ≤ (k + 1) / m
      -- Start from h_mul_le2: m * f₀ H n ≤ (↑k + 1) * f₀ H b
      rw [mul_comm (m : ℝ) _] at h_mul_le2 -- (f₀ H n) * m ≤ (↑k + 1) * f₀ H b
      -- Use (b / c ≤ e / d ↔ b * d ≤ e * c) with b=f₀ H n, c=f₀ H b, e=k+1, d=m
      rwa [div_le_div_iff₀ hf0b_pos hm_pos_real] -- Goal: f₀ H n / f₀ H b ≤ (k + 1) / m



/-! ### Chunk 3.4 - Breakdown Step 5 - Helper 4: Real Arithmetic Equivalence -/


/--
Lemma: Proves the lower bound part of the absolute difference inequality.
Combines the lower bound on the f₀ ratio (`k/m ≤ f0_ratio`)
and the upper bound relating `logb` to `k/m` (`logb - 1/m < k/m`).
Uses helper lemmas for arithmetic and transitivity.
-/
lemma prove_diff_lower_bound {f0_ratio logb_val k_val m_val : ℝ}
    (h_f0_lower : k_val / m_val ≤ f0_ratio)
    (h_logb_upper_shifted : logb_val - 1 / m_val < k_val / m_val) :
    -1 / m_val < f0_ratio - logb_val := by
  -- 1. Combine the hypotheses using transitivity
  have h_trans : logb_val - 1 / m_val < f0_ratio :=
    lt_of_lt_of_le h_logb_upper_shifted h_f0_lower

  -- 2. Rearrange h_trans: logb_val - 1 / m_val < f0_ratio
  -- Use `sub_lt_iff_lt_add`: logb_val < f0_ratio + 1 / m_val
  have h_step2 : logb_val < f0_ratio + 1 / m_val := by
    exact (sub_lt_iff_lt_add).mp h_trans -- Changed to sub_lt_iff_lt_add (no prime)

  -- Rewrite h_step2 to match the expected form for lt_add_iff_sub_left_real
  rw [add_comm] at h_step2 -- Now h_step2 : logb_val < 1 / m_val + f0_ratio

  -- 3. Rearrange h_step2: logb_val < 1 / m_val + f0_ratio
  -- Use custom `lt_add_iff_sub_left_real`: logb_val - f0_ratio < 1 / m_val
  -- Lemma: a < b + c ↔ a - c < b. Here a=logb_val, b=1/m_val, c=f0_ratio
  have h_step3 : logb_val - f0_ratio < 1 / m_val := by
    exact (lt_add_iff_sub_left_real logb_val (1 / m_val) f0_ratio).mp h_step2 -- Use the rewritten h_step2

  -- 4. Rearrange h_step3: logb_val - f0_ratio < 1 / m_val
  -- Multiply by -1 and flip inequality
  have h_step4_raw : -(1 / m_val) < -(logb_val - f0_ratio) := by
    exact neg_lt_neg_iff.mpr h_step3

  -- 5. Simplify LHS using helper_neg_div
  have h_step5 : -1 / m_val < -(logb_val - f0_ratio) := by
    rw [helper_neg_div 1 m_val] at h_step4_raw
    exact h_step4_raw

  -- 6. Simplify RHS using helper_neg_sub
  have h_step6 : -1 / m_val < f0_ratio - logb_val := by
    rw [helper_neg_sub logb_val f0_ratio] at h_step5
    exact h_step5

  -- 7. Check goal
  exact h_step6



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


/--
Lemma (Core Limit Argument): If the absolute difference between two real numbers `x` and `y`
is bounded by `1/m` for all natural numbers `m ≥ 1`, then `x` must equal `y`.
-/
lemma eq_of_abs_sub_le_inv_ge_one_nat {x y : ℝ} (h_bound : ∀ m : ℕ, m ≥ 1 → |x - y| ≤ 1 / (m : ℝ)) :
    x = y := by
  -- Use the metric space lemma eq_of_forall_dist_le
  -- The goal becomes: ∀ ε > 0, dist x y ≤ ε
  apply eq_of_forall_dist_le
  -- Introduce arbitrary ε > 0
  intro ε hε
  -- Show dist x y ≤ ε
  -- For Real numbers, dist x y = |x - y|
  simp_rw [dist_eq_norm_sub, Real.norm_eq_abs] -- Goal: |x - y| ≤ ε
  -- Use the Archimedean helper to find m ≥ 1 such that 1 / m ≤ ε
  rcases exists_one_le_nat_one_div_le hε with ⟨m, hm_ge_1, h_inv_m_le_ε⟩
  -- Use the hypothesis h_bound for this specific m
  have h_abs_le_inv_m : |x - y| ≤ 1 / (m : ℝ) := h_bound m hm_ge_1
  -- Combine the two inequalities using transitivity
  exact le_trans h_abs_le_inv_m h_inv_m_le_ε -- |x - y| ≤ 1 / m and 1 / m ≤ ε implies |x - y| ≤ ε


/--
Lemma (Apply Limit to Trapping): Shows that the ratio `f₀ H n / f₀ H b` is exactly
equal to `logb b n`. Assumes `H` is non-trivial.
-/
lemma uniformEntropy_ratio_eq_logb (hH : IsEntropyFunction H) (hH_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0)
    {n b : ℕ} (hn : n ≥ 1) (hb : b ≥ 2) :
    f₀ H n / f₀ H b = Real.logb b n := by
  -- Apply the limit lemma eq_of_abs_sub_le_inv_ge_one_nat
  -- Let x = f₀ H n / f₀ H b and y = Real.logb b n
  apply eq_of_abs_sub_le_inv_ge_one_nat
  -- The goal becomes: ∀ m : ℕ, m ≥ 1 → |f₀ H n / f₀ H b - Real.logb b n| ≤ 1 / (m : ℝ)
  -- This is precisely the statement provided by logarithmic_trapping for any m ≥ 1
  intro m hm
  exact logarithmic_trapping hH hH_nonzero hn hm hb



-- Replacement for logb_eq_log_div_log
lemma f0_ratio_eq_log_ratio (hH : IsEntropyFunction H) (hH_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0)
    {n b : ℕ} (hn : n ≥ 1) (hb : b ≥ 2) :
    f₀ H n / f₀ H b = Real.log n / Real.log b := by
  -- Step 1: Get the previous equality involving logb
  have h_eq_logb : f₀ H n / f₀ H b = Real.logb b n := by
    exact uniformEntropy_ratio_eq_logb hH hH_nonzero hn hb

  -- Step 2: Establish preconditions for Real.logb_eq_log
  have hb_pos_real : 0 < (b : ℝ) := cast_pos_of_ge_two hb
  have hb_ne_one_real : (b : ℝ) ≠ 1 := ne_of_gt (one_lt_cast_of_ge_two hb)
  -- Correctly prove 0 < n (Nat) from hn : n ≥ 1 (Nat)
  have hn_pos_nat : 0 < n := pos_of_one_le hn
  -- Use Nat.cast_pos.mpr with the correct Nat proof
  have hn_pos_real : 0 < (n : ℝ) := Nat.cast_pos.mpr hn_pos_nat

  -- Step 3: Rewrite logb using Real.logb_eq_log
  have h_logb_rewrite : Real.logb b n = Real.log n / Real.log b := by
    exact logb_eq_log

  -- Step 4: Substitute the rewritten logb into the equality from Step 1
  rw [h_eq_logb, h_logb_rewrite]



/--
Lemma: The constant `C` relating `f₀` to `log` is non-negative.
-/
lemma C_constant_nonneg (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ) (hH : IsEntropyFunction H) :
    C_constant H ≥ 0 := by
  -- Unfold the definition of C_constant
  rw [C_constant]
  -- Split the proof based on the if condition
  split_ifs with h_nonzero
  · -- Case 1: H is non-trivial (h_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0)
    -- Goal is: f₀ H 2 / Real.log 2 ≥ 0
    -- Prove numerator is non-negative
    have h_num_nonneg : f₀ H 2 ≥ 0 := by
      apply f0_nonneg hH
      norm_num -- Proves 2 ≥ 1
    -- Prove denominator is positive (which implies non-negative)
    have h_den_pos : Real.log 2 > 0 := by
      -- Use Real.log_pos which requires 2 > 1
      apply Real.log_pos
      norm_num -- Proves (2 : ℝ) > 1
    -- Apply div_nonneg (requires numerator non-negative, denominator non-negative)
    apply div_nonneg h_num_nonneg (le_of_lt h_den_pos)
  · -- Case 2: H is trivial (h_not_nonzero : ¬(∃ n' ≥ 1, f₀ H n' ≠ 0))
    -- Goal is: 0 ≥ 0
    exact le_refl 0

/-- Helper: f₀ H 2 is non-zero if H is non-trivial. -/
lemma f0_2_ne_zero (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ) (hH : IsEntropyFunction H)
    (h_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0) :
    f₀ H 2 ≠ 0 := by
  have hb2 : 2 ≥ 2 := by norm_num
  have h_pos : f₀ H 2 > 0 := uniformEntropy_pos_of_nontrivial hH h_nonzero hb2
  exact ne_of_gt h_pos

/-- Helper: log 2 is non-zero. -/
lemma log_2_ne_zero : Real.log 2 ≠ 0 := by
  have hb2 : 2 ≥ 2 := by norm_num
  have h_pos : Real.log 2 > 0 := log_b_pos hb2
  exact ne_of_gt h_pos

/--
Helper: Rearranges the equality `a / b = c / d` to `a = (b / d) * c`,
given denominators are non-zero.
-/
lemma rearrange_ratio_equality {a b c d : ℝ} (hb : b ≠ 0) (_hd : d ≠ 0)
    (h_ratio : a / b = c / d) :
    a = (b / d) * c := by
  -- Start from a / b = c / d
  -- Multiply both sides by b
  rw [div_eq_iff hb] at h_ratio
  -- h_ratio: a = (c / d) * b
  -- Rearrange RHS: (c / d) * b = (c * b) / d
  rw [div_mul_eq_mul_div] at h_ratio
  -- h_ratio: a = (c * b) / d
  -- Commute multiplication in numerator: (c * b) / d = (b * c) / d
  rw [mul_comm c b] at h_ratio
  -- h_ratio: a = (b * c) / d
  -- Associate division differently: (b * c) / d = (b / d) * c using div_mul_eq_mul_div
  -- This step implicitly uses hd ≠ 0
  rw [← div_mul_eq_mul_div] at h_ratio
  -- h_ratio: a = (b / d) * c
  exact h_ratio


/--
Helper Lemma: Explicitly proves that C_constant H equals the 'then' branch
of its definition when H is non-trivial.
-/
lemma C_constant_eq_term_A_of_nonzero (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ)
    (h_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0) :
    C_constant H = f₀ H 2 / Real.log 2 := by
  -- Unfold the definition of C_constant
  unfold C_constant
  -- Use the provided hypothesis h_nonzero to simplify the if statement
  exact if_pos h_nonzero

/--
Lemma: If the entropy function `H` is non-trivial, then `f₀ H n` equals
`C * Real.log n`, where `C` is the defined constant `C_constant H hH`.
Uses helper lemmas for clarity.
-/
lemma f0_eq_C_log_of_nonzero (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ) (hH : IsEntropyFunction H)
    (h_nonzero : ∃ n' ≥ 1, f₀ H n' ≠ 0) {n : ℕ} (hn : n ≥ 1) :
    f₀ H n = C_constant H * Real.log n := by

  -- Step 1: Get the core relationship derived from ratios
  have hb2 : 2 ≥ 2 := by norm_num
  have h_ratio_eq : f₀ H n / f₀ H 2 = Real.log n / Real.log 2 := by
    exact f0_ratio_eq_log_ratio hH h_nonzero hn hb2
  have hf0_2_ne_zero : f₀ H 2 ≠ 0 := f0_2_ne_zero H hH h_nonzero
  have hlog2_ne_zero : Real.log 2 ≠ 0 := log_2_ne_zero
  have h_core_relation : f₀ H n = (f₀ H 2 / Real.log 2) * Real.log n := by
    exact rearrange_ratio_equality hf0_2_ne_zero hlog2_ne_zero h_ratio_eq

  -- Step 2: Establish that C_constant H equals the 'then' branch value
  have h_C_eq_A : C_constant H = f₀ H 2 / Real.log 2 := by
    exact C_constant_eq_term_A_of_nonzero H h_nonzero

  -- Step 3: Rewrite the LHS of the goal using the core relationship
  rw [h_core_relation]
  -- Goal is now: (f₀ H 2 / Real.log 2) * Real.log n = C_constant H * Real.log n

  -- Step 4: Rewrite the RHS of the goal using the equality for C_constant
  rw [h_C_eq_A]
  -- Goal is now: (f₀ H 2 / Real.log 2) * Real.log n = (f₀ H 2 / Real.log 2) * Real.log n

  -- Step 5: Close the goal by reflexivity
  --rfl

/--
Helper Lemma: If H is the trivial entropy function (f₀ H n = 0 for all n ≥ 1),
then f₀ H n is indeed 0 for any specific n ≥ 1.
-/
lemma f0_eq_zero_of_not_nonzero (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ)
    (h_not_nonzero : ¬(∃ n' ≥ 1, f₀ H n' ≠ 0)) {n : ℕ} (_hn : n ≥ 1) :
    f₀ H n = 0 := by
  -- Proof by contradiction
  by_contra h_f0_n_ne_zero
  -- Assume f₀ H n ≠ 0.
  -- Since n ≥ 1 (from hn), this provides a witness for the existence claim.
  have h_exists : ∃ n' ≥ 1, f₀ H n' ≠ 0 := by
    use n -- Use the specific n we are considering
    -- Need to provide proof of n ≥ 1 and f₀ H n ≠ 0
  -- This contradicts the main hypothesis h_not_nonzero
  exact h_not_nonzero h_exists

/--
Helper Lemma: Explicitly proves that C_constant H equals the 'else' branch (0)
of its definition when H is trivial.
-/
lemma C_constant_eq_zero_of_not_nonzero (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ)
    (h_not_nonzero : ¬(∃ n' ≥ 1, f₀ H n' ≠ 0)) :
    C_constant H = 0 := by
  -- Unfold the definition of C_constant
  unfold C_constant
  -- Use the provided hypothesis h_not_nonzero to simplify the if statement
  exact if_neg h_not_nonzero

/--
Lemma: If the entropy function `H` is trivial (f₀ H n = 0 for all n ≥ 1),
then `f₀ H n` equals `C * Real.log n`, where `C` is the defined constant (which is 0).
-/
lemma f0_eq_C_log_of_zero (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ) (_hH : IsEntropyFunction H)
    (h_not_nonzero : ¬(∃ n' ≥ 1, f₀ H n' ≠ 0)) {n : ℕ} (hn : n ≥ 1) :
    f₀ H n = C_constant H * Real.log n := by

  -- Step 1: Establish f₀ H n = 0 using the first helper
  have h_f0_n_zero : f₀ H n = 0 := by
    exact f0_eq_zero_of_not_nonzero H h_not_nonzero hn

  -- Step 2: Establish C_constant H = 0 using the second helper
  have h_C_zero : C_constant H = 0 := by
    exact C_constant_eq_zero_of_not_nonzero H h_not_nonzero

  -- Step 3: Rewrite the goal using these two facts
  rw [h_f0_n_zero, h_C_zero]
  -- Goal is now: 0 = 0 * Real.log n

  -- Step 4: Prove the final equality using symmetry
  exact Eq.symm (zero_mul (Real.log n))

/--
Helper Lemma: Combines the results for the non-trivial and trivial cases
to show that `f₀ H n = C * Real.log n` holds for all n ≥ 1.
-/
lemma f0_eq_C_log_cases (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ) (hH : IsEntropyFunction H)
    {n : ℕ} (hn : n ≥ 1) :
    f₀ H n = C_constant H * Real.log n := by
  -- Use classical logic to split on whether H is non-trivial
  apply Classical.by_cases
  · -- Case 1: Assume H is non-trivial (h_nonzero : ∃ ...)
    intro h_nonzero
    exact f0_eq_C_log_of_nonzero H hH h_nonzero hn
  · -- Case 2: Assume H is trivial (h_not_nonzero : ¬(∃ ...))
    intro h_not_nonzero
    exact f0_eq_C_log_of_zero H hH h_not_nonzero hn

/--
Helper Lemma: Connects the original function `f` (defined for `n > 0`)
to the extended function `f₀` (defined for all `n`).
-/
lemma f_eq_f0_for_positive_n (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ)
    {n : ℕ} (hn_pos : n > 0) :
    f H hn_pos = f₀ H n := by
  -- Unfold the definition of f₀ on the RHS
  rw [f₀]
  -- Goal is now: f H hn_pos = (dite (n > 0) (fun hn => f H hn) (fun _ => 0))
  -- Use the hypothesis hn_pos to simplify the 'dite' to the 'then' branch
  -- dif_pos rewrites (dite c t e) to t(hc) given hc : c
  rw [dif_pos hn_pos]

/-!
### Chunk 3.4 - Breakdown Step 5 - Main Theorem: Existence of C and log formula
Theorem (Chunk 3 Goal): There exists a non-negative constant `C` such that
for all `n > 0`, the entropy of the uniform distribution `f H n` is equal
to `C * log n`.
-/
theorem RotaEntropyTheorem (H : ∀ {n : ℕ}, (Fin n → NNReal) → ℝ) (hH : IsEntropyFunction H) :
    ∃ C ≥ 0, ∀ n (hn : n > 0), f H hn = C * Real.log n := by
  -- Step 1: Define the constant C using the existing definition
  let C := C_constant H
  -- Step 2: Claim existence of this C
  use C

  -- Step 3: Prove the two required properties: C ≥ 0 and the universal quantification
  constructor
  · -- Prove C ≥ 0 using the previously proven lemma
    exact C_constant_nonneg H hH
  · -- Prove ∀ n > 0, f H ... = C * Real.log n
    -- Introduce arbitrary n and the hypothesis n > 0
    intro n hn_pos
    -- Goal: f H hn_pos = C * Real.log n

    -- Step 4: Connect f to f₀ using the helper lemma
    rw [f_eq_f0_for_positive_n H hn_pos]
    -- Goal: f₀ H n = C * Real.log n

    -- Step 5: Prove n ≥ 1 (needed for the next lemma)
    have hn_ge_1 : n ≥ 1 := Nat.one_le_of_lt hn_pos

    -- Step 6: Apply the lemma that combines the zero/non-zero cases
    exact f0_eq_C_log_cases H hH hn_ge_1

end PPNP.Entropy
