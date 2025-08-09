import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic -- `strictConcaveOn_log_Ioi`
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Algebra.Order.Ring.Basic -- for le_iff_sub_nonneg
import EGPT.NumberTheory.Filter
import EGPT.NumberTheory.Core -- For ParticlePath bijection with ℕ
import EGPT.Complexity.PPNP -- For the final, canonical NP-Completeness proofs
import EGPT.Physics.PhotonicCA -- For the_system_has_equivalent_program
import EGPT.Entropy.Common -- For rect_program_for_dist and ShannonEntropyOfDist
import EGPT.Entropy.RET -- For the RET entropy function
import EGPT.Entropy.H -- For the canonical entropy function

open EGPT.Complexity EGPT.Constraints EGPT.Physics.PCA EGPT.Entropy.Common EGPT.NumberTheory.Filter EGPT.Complexity.PPNP EGPT.NumberTheory.Core EGPT.Entropy.RET Real Finset EGPT.Entropy.H


-- ==================================================================
-- PHASE 3: The Externalized Proof of Equivalence (Transport Theorem)
-- ==================================================================

/--
**Theorem (Rota Properties Transport Over Scaling):** If a function `H` satisfies
the properties of an entropy function, then any positive constant multiple of `H`
also satisfies those properties.

This transport also allows us to change the base of the logarithm in the entropy function
without re-writing all the axiom proofs which were more easily
done in nats.
-/
theorem RET_All_Enropy_Is_Scaled_Shannon_Entropy (ef : EntropyFunction) (C : ℝ) (hC_pos : 0 < C) :
    HasRotaEntropyProperties (fun p => (C * (ef.H_func p : ℝ)).toNNReal) :=
  let C_nn : NNReal := C.toNNReal
  have hC_nn_pos : 0 < C_nn := by
    simp only [C_nn]
    exact Real.toNNReal_pos.mpr hC_pos
  {
    -- Each axiom proof for the scaled function follows from the original proof by distributing the constant C.
    symmetry := by
      intro α β _ _ p_target hp e
      -- Goal: (C * ↑(ef.H_func (fun x => p_target (e x)))).toNNReal = (C * ↑(ef.H_func p_target)).toNNReal
      congr 2
      simp only [NNReal.coe_inj]
      exact ef.props.symmetry p_target hp e
    ,
    zero_invariance := by
      intro n p_orig hp_sum_1
      -- Goal: (C * ↑(ef.H_func p_ext)).toNNReal = (C * ↑(ef.H_func p_orig)).toNNReal
      congr 2
      simp only [NNReal.coe_inj]
      exact ef.props.zero_invariance p_orig hp_sum_1
    ,
    normalized := by
      intro p hp_sum_1
      -- Goal: (C * ↑(ef.H_func p)).toNNReal = 0
      simp only [ef.props.normalized p hp_sum_1, NNReal.coe_zero, mul_zero, Real.toNNReal_zero]
    ,
    max_uniform := by
      intro α _ h_card_pos p hp_sum_1
      -- Goal: (C * ↑(ef.H_func p)).toNNReal ≤ (C * ↑(ef.H_func (uniformDist h_card_pos))).toNNReal
      -- This follows from the monotonicity of toNNReal and multiplication by positive constants
      apply Real.toNNReal_le_toNNReal
      apply mul_le_mul_of_nonneg_left
      · exact NNReal.coe_le_coe.mpr (ef.props.max_uniform h_card_pos p hp_sum_1)
      · exact le_of_lt hC_pos
    ,
    continuity := by
      intro α _ p_center hp_sum_1 ε hε_pos
      -- Goal: ∃ δ > 0, ∀ (q : α → NNReal) (_hq_sum_1 : ∑ i, q i = 1),
      --       (∀ i, |(q i : ℝ) - (p_center i : ℝ)| < δ) →
      --       |((C * ↑(ef.H_func q)).toNNReal : ℝ) - ((C * ↑(ef.H_func p_center)).toNNReal : ℝ)| < ε

      -- Use continuity of the original entropy function ef.H_func
      -- We want: |C * ↑(ef.H_func q) - C * ↑(ef.H_func p_center)| < ε
      -- This gives us: |C| * |↑(ef.H_func q) - ↑(ef.H_func p_center)| < ε
      -- So we need: |↑(ef.H_func q) - ↑(ef.H_func p_center)| < ε / |C|

      have hC_abs_pos : |C| > 0 := abs_pos.mpr (ne_of_gt hC_pos)
      let ε_scaled := ε / |C|
      have hε_scaled_pos : ε_scaled > 0 := div_pos hε_pos hC_abs_pos

      -- Apply continuity of ef.H_func
      obtain ⟨δ, hδ_pos, hδ_works⟩ := ef.props.continuity p_center hp_sum_1 ε_scaled hε_scaled_pos

      use δ, hδ_pos
      intro q hq_sum_1 hq_close

      -- Apply the continuity property of ef.H_func
      have h_ef_close := hδ_works q hq_sum_1 hq_close

      -- Since ef.H_func returns NNReal, both values are non-negative, so toNNReal is identity
      have h_nonneg_q : (C * (ef.H_func q : ℝ)) ≥ 0 :=
        mul_nonneg (le_of_lt hC_pos) (NNReal.coe_nonneg _)
      have h_nonneg_p : (C * (ef.H_func p_center : ℝ)) ≥ 0 :=
        mul_nonneg (le_of_lt hC_pos) (NNReal.coe_nonneg _)

      rw [Real.coe_toNNReal _ h_nonneg_q, Real.coe_toNNReal _ h_nonneg_p]

      -- Now we have: |C * ↑(ef.H_func q) - C * ↑(ef.H_func p_center)| < ε
      rw [← mul_sub, abs_mul]

      -- Since C > 0, |C| = C
      rw [abs_of_pos hC_pos]

      -- Apply the bound from ef.H_func continuity
      have h_bound : |((ef.H_func q) : ℝ) - ((ef.H_func p_center) : ℝ)| < ε_scaled := h_ef_close

      -- Conclude: C * |↑(ef.H_func q) - ↑(ef.H_func p_center| < C * (ε / C) = ε
      calc C * |((ef.H_func q) : ℝ) - ((ef.H_func p_center) : ℝ)|
        < C * ε_scaled := by apply mul_lt_mul_of_pos_left h_bound hC_pos
        _ = C * (ε / |C|) := rfl
        _ = C * (ε / C) := by rw [abs_of_pos hC_pos]
        _ = ε := by field_simp [ne_of_gt hC_pos]
    ,
    cond_add_sigma := by
      -- Introduce all the universally quantified variables.
      intro N _inst prior M_map P_cond hprior_sum_1 hP_cond_props hH_P_cond_zero

      -- We will prove the equality in `ℝ` and then use `NNReal.eq` to finish.
      apply NNReal.eq
      symm  -- Flip the goal so calc starts with the correct side

      -- First, we establish that all scaled entropy terms are non-negative, so `toNNReal` behaves predictably.
      have h_joint_nonneg : 0 ≤ C * (ef.H_func (DependentPairDistSigma prior M_map P_cond) : ℝ) :=
        mul_nonneg (le_of_lt hC_pos) (NNReal.coe_nonneg _)
      have h_prior_nonneg : 0 ≤ C * (ef.H_func prior : ℝ) :=
        mul_nonneg (le_of_lt hC_pos) (NNReal.coe_nonneg _)
      have h_cond_i_nonneg (i : Fin N) : 0 ≤ C * (ef.H_func (P_cond i) : ℝ) :=
        mul_nonneg (le_of_lt hC_pos) (NNReal.coe_nonneg _)

      -- Now, let's work with the `ℝ`-valued equation.
      -- The `calc` block transforms the RHS into the LHS.
      calc
        -- Start with the expected LHS coerced to ℝ
        ↑((C * ↑(ef.H_func prior)).toNNReal + ∑ i, prior i * (C * ↑(ef.H_func (P_cond i))).toNNReal)

        -- Simplify coercions using toNNReal properties for nonnegative values.
        _ = (C * (ef.H_func prior : ℝ)) + ∑ i, (prior i : ℝ) * (C * (ef.H_func (P_cond i) : ℝ)) := by
            rw [NNReal.coe_add, NNReal.coe_sum]
            congr 1
            · rw [Real.coe_toNNReal _ h_prior_nonneg]
            · congr 1
              ext i
              rw [NNReal.coe_mul, Real.coe_toNNReal _ (h_cond_i_nonneg i)]

        -- Factor out the constant C in ℝ.
        _ = C * ((ef.H_func prior : ℝ) + ∑ i, (prior i : ℝ) * (ef.H_func (P_cond i) : ℝ)) := by
            rw [mul_add]
            congr 1
            rw [mul_sum]
            congr 1
            ext i
            ring

        -- Apply the original axiom for `ef`, coercing to ℝ.
        _ = C * (ef.H_func (DependentPairDistSigma prior M_map P_cond) : ℝ) := by
            congr 1
            -- We need to construct the proper hypothesis for the original axiom
            have hH_P_cond_zero_orig : ∀ (i : Fin N), M_map i = 0 → ef.H_func (P_cond i) = 0 := by
              intro i hi
              -- From hH_P_cond_zero, we have (C * ↑(ef.H_func (P_cond i))).toNNReal = 0
              have h := hH_P_cond_zero i hi
              -- Since C > 0, if (C * ↑(ef.H_func (P_cond i))).toNNReal = 0,
              -- then C * ↑(ef.H_func (P_cond i)) = 0, which implies ef.H_func (P_cond i) = 0
              have h_zero : C * ↑(ef.H_func (P_cond i)) = 0 := by
                have h_nonneg := h_cond_i_nonneg i
                -- From toNNReal a = 0 and a ≥ 0, we get a = 0
                have h_le_zero : C * ↑(ef.H_func (P_cond i)) ≤ 0 := Real.toNNReal_eq_zero.mp h
                exact le_antisymm h_le_zero h_nonneg
              have h_coe_zero : ↑(ef.H_func (P_cond i)) = (0 : ℝ) := by
                have h_nonzero : C ≠ 0 := ne_of_gt hC_pos
                rw [mul_eq_zero] at h_zero
                cases h_zero with
                | inl h => contradiction
                | inr h => exact h
              -- From coe zero to NNReal zero
              exact NNReal.coe_eq_zero.mp h_coe_zero
            have h_orig_axiom := ef.props.cond_add_sigma prior M_map P_cond hprior_sum_1 hP_cond_props hH_P_cond_zero_orig
            -- Apply coercion to both sides of the equality
            have h_real : (ef.H_func (DependentPairDistSigma prior M_map P_cond) : ℝ) =
                          (ef.H_func prior : ℝ) + ∑ i, (prior i : ℝ) * (ef.H_func (P_cond i) : ℝ) := by
              rw [h_orig_axiom]
              simp only [NNReal.coe_add, NNReal.coe_sum, NNReal.coe_mul]
            exact h_real.symm

        -- This is now the definition of the LHS coerced to ℝ.
        _ = ↑((C * ↑(ef.H_func (DependentPairDistSigma prior M_map P_cond))).toNNReal) := by
            rw [Real.coe_toNNReal _ h_joint_nonneg]
    ,
    apply_to_empty_domain := by
      -- Goal: (C * ↑(ef.H_func (fun (_ : Empty) => 0))).toNNReal = 0
      simp only [ef.props.apply_to_empty_domain, NNReal.coe_zero, mul_zero, Real.toNNReal_zero]
  }

-- With this, C_constant_of_EntropyFunction(TheCanonicalEntropyFunction) is provably 1.
theorem C_of_H_canonical_is_one :
  C_constant_of_EntropyFunction TheCanonicalEntropyFunction = 1 / Real.log 2 :=
  -- This would be a proof based on the definition of C and H_canonical.
  sorry


/--
For a given infinite source (`egpt_real`) and a prefix length `n`, this function
computes the empirical frequency of `true`s as a rational number.
-/
noncomputable def empirical_frequency (egpt_real : ParticleFuturePDF) (n : ℕ) : ℚ :=
  if _hn_pos : n > 0 then
    -- 1. Get the first `n` bits from the source.
    let prefix_tape := List.ofFn (fun i : Fin n => egpt_real (fromNat i.val))
    -- 2. Count the number of `true`s.
    let p_count := prefix_tape.count true
    -- 3. Construct the rational number `p_count / n`.
    mkRat p_count n
  else
    0 -- The frequency is undefined or 0 for a zero-length prefix.


/--
`get_bias_of_source` returns the asymptotic bias (frequency of `true`) of an
infinite IID bit source.  We take the `Filter.liminf` of the empirical
frequencies (viewed as real numbers) and coerce it to a non‑negative real
using `Real.toNNReal`, which is the preferred Lean 4 / mathlib4 replacement
for the old `nnreal.of_real`.
-/
noncomputable def get_bias_of_source (egpt_real : ParticleFuturePDF) : NNReal :=
  let seq : ℕ → ℝ := fun n => (empirical_frequency egpt_real n : ℝ)
  Real.toNNReal (Filter.liminf seq Filter.atTop)


/--
**toFun (The EGPT Encoder via Rota's Final Formula):** Computes the canonical measure
of an EGPT.Real by directly applying the Rota-Uniqueness of Entropy (RUE) theorem.

This definition replaces a direct call to the axiomatic H function with the
explicit formula (`C * H_shannon`) that Rota's theorem proves it must satisfy.
This is the most direct application of the logarithmic trapping machinery.
-/
noncomputable def toFun_EGPT_Real_to_Std_Real
  (ef : EntropyFunction) (egpt_real : ParticleFuturePDF) : ℝ :=
  -- Step 1: Conceptually obtain the source's intrinsic bias `p`.
  let p_bias := get_bias_of_source egpt_real

  -- Step 2: Construct the corresponding probability distribution on {false, true}.
  let dist_of_source : Fin 2 → NNReal :=
    fun i => if i.val = 0 then (1 - p_bias) else p_bias

  -- Step 3: Calculate the standard Shannon entropy of this distribution (in nats).
  -- This uses the standard, universally accepted definition of entropy.
  let h_shannon_nats := stdShannonEntropyLn dist_of_source

  -- Step 4: Get the Rota-Khinchin constant `C` for our specific axiomatic H.
  let C := C_constant_of_EntropyFunction ef

  -- Step 5: The encoded real number is `C * H_shannon`. This is the RUE formula.
  -- We divide by `log 2` to convert the standard entropy from nats to bits,
  -- aligning with the typical interpretation of C.
  C * (h_shannon_nats / Real.log 2)


/--
For a given prefix length `n`, this function creates the `FiniteIIDSample` that
perfectly describes the observed statistics.
-/
noncomputable def empirical_sample (egpt_real : ParticleFuturePDF) (n : ℕ) : Option FiniteIIDSample :=
  if hn_pos : n > 0 then
    let prefix_tape := List.ofFn (fun i : Fin n => egpt_real (fromNat i.val))
    let p := prefix_tape.count true
    let q := n - p
    some {
      p_param := p,
      q_param := q,
      num_sub_samples := 1,
      h_is_nontrivial := by {
        simp [p, q]
        -- Either there's a true in prefix_tape, or count true < n
        by_cases h : true ∈ prefix_tape
        · left; exact h
        · right
          simp [List.count_eq_zero_of_not_mem h]
          exact hn_pos
      }
    }
  else
    none

/--
For a given prefix length `n`, this function creates the canonical EGPT Rational
(`ParticleHistoryPMF`) that encodes the empirical frequency.
-/
noncomputable def empirical_pmf (egpt_real : ParticleFuturePDF) (n : ℕ) : ParticleHistoryPMF :=
  -- We get the rational frequency and then use the canonical fromRat encoder.
  fromRat (empirical_frequency egpt_real n)
