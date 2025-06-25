import Mathlib.Analysis.SpecificLimits.Basic -- for tendsto
import Mathlib.Order.Filter.Basic -- for atTop
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Order.Basic
import EGPT.NumberTheory.Core
import EGPT.Constraints
import EGPT.NumberTheory.Filter
import EGPT.Entropy.Common
import EGPT.Entropy.RET

import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Basic
--import Mathlib.Topology.Instances.Real

namespace EGPT.NumberTheory.Analysis


open EGPT.NumberTheory.Core EGPT.Constraints EGPT.NumberTheory.Filter EGPT.Entropy.Common EGPT.Entropy.RET Filter



/--
For a given infinite source (`egpt_real`) and a prefix length `n`, this function
computes the empirical frequency of `true`s as a rational number.
-/
noncomputable def empirical_frequency (egpt_real : ParticleSystemPDF) (n : ℕ) : ℚ :=
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
noncomputable def get_bias_of_source (egpt_real : ParticleSystemPDF) : NNReal :=
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
  (ef : EntropyFunction) (egpt_real : ParticleSystemPDF) : ℝ :=
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
noncomputable def empirical_sample (egpt_real : ParticleSystemPDF) (n : ℕ) : Option FiniteIIDSample :=
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
(`ParticlePMF`) that encodes the empirical frequency.
-/
noncomputable def empirical_pmf (egpt_real : ParticleSystemPDF) (n : ℕ) : ParticlePMF :=
  -- We get the rational frequency and then use the canonical fromRat encoder.
  fromRat (empirical_frequency egpt_real n)
