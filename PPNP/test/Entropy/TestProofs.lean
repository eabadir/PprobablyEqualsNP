import PPNP.Entropy.Basic
import PPNP.Entropy.PowerLaw
import PPNP.Entropy.LogF
import PPNP.Entropy.PartitionTheory
import Mathlib.Tactic.NormNum -- For evaluating numerals

open PPNP.Entropy.Basic PPNP.Entropy.Pow PPNP.Entropy.LogF Real Nat

-- Assume the existence of an entropy function H satisfying the properties
variable {H : ∀ {n : ℕ}, (Fin n → NNReal) → Real} (hH : IsEntropyFunction H)

-- Test lemma for f₀(1) = 0 from Basic.lean
example : f₀ H 1 = 0 :=
  f0_1_eq_0 hH

-- Test lemma for f₀ monotonicity from Basic.lean
example : f₀ H 2 ≤ f₀ H 3 := by
  have h_mono := f0_mono hH
  apply h_mono
  norm_num -- Proves 2 ≤ 3

-- Test lemma for the power law from PowerLaw.lean
example : f₀ H (2 ^ 3) = (3 : ℝ) * f₀ H 2 := by
  have h_pow := f0_pow_eq_mul hH (by norm_num : 2 ≥ 1) (by norm_num : 3 ≥ 1)
  -- The goal directly matches the theorem statement after substituting values
  exact h_pow

-- Test lemma for the existence of k for log bounds from LogF.lean
example : ∃ k : ℕ, (2 : ℝ) ^ k ≤ (10 : ℝ) ∧ (10 : ℝ) < (2 : ℝ) ^ (k + 1) := by
  -- Corrected the proof term for hx to use Real 10
  have h_exists := exists_k_log_bounds (b := 2) (x := 10) (by norm_num : 2 ≥ 2) (by norm_num : (10 : ℝ) ≥ 1)
  exact h_exists

-- Example showing f₀ is non-negative (from LogF.lean, originally in Chunk 3.1)
example : f₀ H 5 ≥ 0 :=
  f0_nonneg hH (by norm_num : 5 ≥ 1)
