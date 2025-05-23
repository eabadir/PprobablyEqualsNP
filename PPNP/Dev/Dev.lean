import Mathlib.Data.Sym.Card
import Std.Sat.CNF.Basic
import Mathlib.Tactic.Sat.FromLRAT
--import Std.Data.List.Lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic -- For Fintype (Fin n) if needed, though usually direct
import Mathlib.Logic.Equiv.Defs -- For Equiv

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic -- For Real.log, Real.log_pow, Real.log_ne_zero_of_pos_of_ne_one
--import Mathlib.Data.Nat.Order.Basic -- For Nat.pos_of_ne_zero, Nat.lt_irrefl
--import Mathlib.Algebra.Ring.NatCast -- For Nat.cast_pow (implicitly used by (↑(2^m_bits) : ℝ))
--                                      and Nat.cast_zero, Nat.cast_id
import Mathlib.Data.List.Basic -- For List.replicate, List.length_replicate (from Std, re-exported)

import PPNP.Common.Basic
import PPNP.Entropy.Common
import PPNP.Entropy.Physics.Common
import PPNP.Entropy.RET
import PPNP.Entropy.Physics.UniformSystems
import PPNP.Complexity.Program
import PPNP.Entropy.Physics.PhysicsDist
import PPNP.Entropy.Physics.BoseEinstein
import PPNP.Entropy.Physics.PhotonicCA

open Multiset NNReal Finset Function Real -- Added Function for comp_apply

open Multiset NNReal
open PPNP.Common
open PPNP.Complexity.Program
open PPNP.Entropy.Common
open PPNP.Entropy.Physics.Common
open PPNP.Entropy.Physics.UniformSystems
open PPNP.Entropy.Physics.PhysicsDist
open PPNP.Entropy.Physics.BE
open PPNP.Entropy.Physics.PCA
open PPNP.Entropy.RET

-- In PPNP.Entropy.RET.lean

open PPNP.Entropy.Common

-- In PPNP.Entropy.Physics.Common.lean or in RET.lean if it's general enough



noncomputable def f0_of_concrete_H (H_conc : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal)
    (n : ℕ) : NNReal :=
  if hn_pos : n > 0 then
    let α_n := Fin n
    have h_card_pos : 0 < Fintype.card α_n := by simp [α_n, hn_pos]
    H_conc (uniformDist h_card_pos) -- uniformDist requires proof of sum to 1 for its input,
                                    -- but it's about the output of uniformDist itself.
  else
    0

-- Alias for convenience
noncomputable def f0_H_physical_concrete (n : ℕ) : NNReal :=
  f0_of_concrete_H H_physical_system n


/--
Helper lemma to replace the deprecated `Fintype.card_fin_pos`.
Given `n > 0`, proves `0 < Fintype.card (Fin n)`.
-/
theorem f0_H_physical_concrete_is_C_log_n (n : ℕ) (hn_ge1 : n ≥ 1) :
    (f0_H_physical_concrete n : ℝ) = (C_physical_NNReal : ℝ) * Real.log (n : ℝ) := by
  have hn_pos : n > 0 := one_le_iff_pos.mp hn_ge1
  simp only [f0_H_physical_concrete, f0_of_concrete_H, dif_pos hn_pos, H_physical_system]
  -- H_physical_system's first if: k=Fintype.card (Fin n) = n. This is not 0.
  simp only [Fintype.card_fin, dif_neg (Nat.ne_of_gt hn_pos)]
  -- H_physical_system's second if: p = uniformDist (Fintype.card_fin_pos hn_pos)
  -- The input `p` *is* `uniformDist (by simp; exact hn_pos)`. So the `if` is true.
  -- Need to show `uniformDist (Fintype.card_fin_pos hn_pos)` is equal to `uniformDist (by simp; exact hn_pos)`
  -- This holds by proof irrelevance for the positivity argument.
  -- More directly, `H_physical_system` receives `uniformDist (...)` as `p`.
  simp [dif_pos rfl] -- p is indeed the uniformDist it's compared against
  -- Now we are in the H_physical_system_uniform_only_calc branch
  simp only [H_physical_system_uniform_only_calc]
  if hn_eq_1 : n = 1 then
    simp [hn_eq_1, Real.log_one, mul_zero, NNReal.coe_zero]
  else
    have hn_ne_1_proof : n ≠ 1 := hn_eq_1
    simp [hn_ne_1_proof, RealLogNatToNNReal, NNReal.coe_mul, Real.log_nonneg (Nat.one_le_cast.mpr hn_ge1)]
    -- Goal is (C_physical_NNReal : ℝ) * Real.log (n:ℝ) = (C_physical_NNReal : ℝ) * Real.log (n:ℝ)

-- Ensure PPNP.Entropy.Common contains the original Fintype_card_fin_pos:
-- lemma Fintype_card_fin_pos {k : ℕ} (hk_pos : k > 0) : 0 < Fintype.card (Fin k) := by
--   simp only [Fintype.card_fin]; exact hk_pos

-- In PPNP.Entropy.Physics.Common.lean or your proof file:
-- In PPNP.Entropy.Common.lean or similar
-- In PPNP.Entropy.Common.lean (or ensure accessible)
noncomputable def uniformDistOnFin (k : ℕ) (hk_pos : k > 0) : Fin k → NNReal :=
  uniformDist (α := Fin k) (by simp only [Fintype.card_fin]; exact hk_pos)



lemma p_BE_fin_is_uniformDist_precise (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
  let k_card_val := Fintype.card (OmegaUD N M)
  have hk_card_val_pos_direct : k_card_val > 0 := card_omega_BE_pos N M h_domain_valid
  let P_target : 0 < Fintype.card (Fin k_card_val) := by {
    simp only [Fintype.card_fin]
    exact hk_card_val_pos_direct
  }
  p_UD_fin N M = uniformDist (α := Fin k_card_val) P_target := by
    let k_card_val_in_proof := Fintype.card (OmegaUD N M)
    have hk_card_val_pos_direct_in_proof : k_card_val_in_proof > 0 := card_omega_BE_pos N M h_domain_valid
    funext i
    -- Unfold LHS to expose the 'if' from uniformProb
    unfold p_UD_fin uniformProb
    -- LHS: if _hn : Fintype.card (OmegaUD N M) > 0 then (↑(Fintype.card (OmegaUD N M)))⁻¹ else 0
    -- which is: if _hn : k_card_val_in_proof > 0 then (↑k_card_val_in_proof)⁻¹ else 0

    -- Simplify the 'if' using the known positivity
    rw [dif_pos hk_card_val_pos_direct_in_proof]
    -- LHS is now: (↑k_card_val_in_proof)⁻¹

    -- Unfold RHS
    unfold uniformDist
    -- RHS: (λ (_x : Fin k_card_val) => (↑(Fintype.card (Fin k_card_val)))⁻¹) i
    -- which simplifies to (↑(Fintype.card (Fin k_card_val)))⁻¹
    -- where k_card_val is from the outer scope (definitionally k_card_val_in_proof)

    -- Simplify Fintype.card (Fin k_card_val) to k_card_val
    simp only [Fintype.card_fin]
    -- RHS is now: (↑k_card_val)⁻¹
    -- Goal: (↑k_card_val_in_proof)⁻¹ = (↑k_card_val)⁻¹
    -- Since k_card_val_in_proof is definitionally equal to k_card_val (from outer scope)

-- Place this lemma preferably near p_BE_fin_is_uniformDist_precise or in a common helper file for BE.
lemma p_BE_fin_is_H_physical_system_uniform_input (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    -- The let bindings for k_card_, hk_card_pos_, and H_sys_internal_pos_proof are moved into the proof block.
    -- The lemma statement now directly uses their definitions.
    p_UD_fin N M = uniformDist (α := Fin (Fintype.card (OmegaUD N M))) (by {
      simp only [Fintype.card_fin]
      exact card_omega_BE_pos N M h_domain_valid -- This was the definition of hk_card_pos_
    }) := by
  let k_card_ := Fintype.card (OmegaUD N M)
  have hk_card_pos_ : k_card_ > 0 := card_omega_BE_pos N M h_domain_valid
  funext i
  simp [p_UD_fin, uniformProb, uniformDist, Fintype.card_fin, k_card_, if_pos hk_card_pos_]

-- Place this before H_physical_system_is_rota_uniform
-- It might go into PPNP.Entropy.Physics.BE or a common file that BE and Common use.
lemma eval_H_physical_system_on_p_UD_fin (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    H_physical_system (p_UD_fin N M) =
      H_physical_system_uniform_only_calc
        (Fintype.card (OmegaUD N M))
        (Nat.one_le_of_lt (card_omega_BE_pos N M h_domain_valid)) := by
  let k_card_ := Fintype.card (OmegaUD N M)
  have hk_card_pos_ : k_card_ > 0 := card_omega_BE_pos N M h_domain_valid
  -- have _hk_card_ge1_ : k_card_ ≥ 1 := Nat.one_le_of_lt hk_card_pos_ -- For the target RHS

  -- Unfold H_physical_system and simplify Fintype.card (Fin n) to n generally.
  simp only [H_physical_system, Fintype.card_fin]

  -- First `if` condition in H_physical_system: k_alpha = 0 (which became k_card_ = 0 after Fintype.card_fin)
  -- We use hk_card_pos_ (0 < k_card_) to show k_card_ ≠ 0.
  rw [dif_neg (Nat.ne_of_gt hk_card_pos_)]

  -- Now in the 'else' branch of the first 'if'.
  -- The expression involves a second 'if' checking if p_UD_fin is the uniformDist.
  -- Use p_BE_fin_is_H_physical_system_uniform_input to resolve this.
  -- This lemma states: p_UD_fin N M = uniformDist (α := Fin k_card_) (proof of 0 < k_card_)
  -- The simp will substitute p_UD_fin N M and simplify the equality condition of the if.
  -- The proofs of 0 < k_card_ will be definitionally equal due to proof irrelevance.
  simp only [p_BE_fin_is_H_physical_system_uniform_input N M h_domain_valid]

  -- The expression should now be:
  -- H_physical_system_uniform_only_calc k_card_ (Nat.one_le_of_lt P_internal) = H_physical_system_uniform_only_calc k_card_ (Nat.one_le_of_lt hk_card_pos_)
  -- This holds by definitional equality because `P_internal` (which is `Nat.pos_of_ne_zero (Nat.ne_of_gt hk_card_pos_)`) is definitionally equal to `hk_card_pos_`.
  -- `simp only []` or `rfl` should close this. Using `simp only []` for robustness.
  rfl

-- Helper lemma (can go near other BE related lemmas or in a common place)
lemma stdShannon_of_p_UD_fin_when_k_is_1 (N M : ℕ) (h_k_is_1 : Fintype.card (OmegaUD N M) = 1) :
    stdShannonEntropyLn (p_UD_fin N M) = 0 := by
  -- Let k_card_ be Fintype.card (OmegaUD N M). We know k_card_ = 1 by h_k_is_1.
  -- The type of p_UD_fin N M is Fin k_card_ → NNReal.
  -- We want to show that for any x in its domain, (p_UD_fin N M x) is 1.
  -- Since k_card_ = 1, the domain Fin k_card_ is Fin 1.
  -- There's only one element in Fin 1, let's call it ` एकमात्र_el : Fin k_card_` (the unique element).
  -- (More formally, ` एकमात्र_el := (0 : Fin 1).cast (by rw ←h_k_is_1)` or similar if needed)

  -- Unfold stdShannonEntropyLn
  unfold stdShannonEntropyLn
  -- Goal: ∑ (x : Fin (Fintype.card (OmegaUD N M))), negMulLog ((p_UD_fin N M x) : ℝ) = 0

  -- Since Fintype.card (OmegaUD N M) = 1, the sum is over a singleton set (Fin 1).
  -- Use Finset.sum_eq_single_of_mem or rewrite the sum over Fin 1 directly.
  -- Fintype.card (Fin 1) = 1. Finset.univ for Fin 1 is {(0 : Fin 1)}.
  conv_lhs =>
    arg 1 -- The sum itself
    simp [h_k_is_1] -- Replace Fintype.card (OmegaUD N M) with 1 in the type
    -- Now summation is over Finset.univ (α := Fin 1)

  -- Goal is now: negMulLog ((p_UD_fin N M (0 : Fin 1)) : ℝ) = 0
  -- (The (0 : Fin 1) is the default element picked by Finset.sum_singleton if not specified)
  -- We need to evaluate p_UD_fin N M (0 : Fin 1)
  -- p_UD_fin N M is (fun _ => uniformProb (Fintype.card (OmegaUD N M)))
  -- Substitute h_k_is_1 for Fintype.card (OmegaUD N M)
  simp [p_UD_fin, h_k_is_1, uniformProb, inv_one, NNReal.coe_one, negMulLog_one]
  -- uniformProb 1 simplifies to 1.
  -- Then negMulLog ((1 : NNReal) : ℝ) is negMulLog 1.0 which is 0.

theorem H_physical_system_is_rota_uniform (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    (H_physical_system (p_UD_fin N M) : ℝ) =
      (C_physical_NNReal : ℝ) * stdShannonEntropyLn (p_UD_fin N M) := by
  let k_card_ := Fintype.card (OmegaUD N M)
  have hk_card_ge1_ : k_card_ ≥ 1 := Nat.one_le_of_lt (card_omega_BE_pos N M h_domain_valid)

  rw [eval_H_physical_system_on_p_UD_fin N M h_domain_valid]
  rw [H_physical_system_uniform_only_calc]

  if hk_eq_1 : k_card_ = 1 then
    rw [dif_pos hk_eq_1]
    simp only [NNReal.coe_zero] -- LHS is (0 : ℝ)
    -- Use the new helper lemma for the RHS
    rw [stdShannon_of_p_UD_fin_when_k_is_1 N M hk_eq_1]
    simp only [mul_zero]
  else
    rw [dif_neg hk_eq_1]
    simp only [PPNP.Common.RealLogNatToNNReal, NNReal.coe_mul, (Real.log_nonneg (Nat.one_le_cast.mpr hk_card_ge1_))]
    have h_shannon_eq_log_k : stdShannonEntropyLn (p_UD_fin N M) = Real.log (k_card_ : ℝ) := by
      rw [p_BE_fin_is_H_physical_system_uniform_input N M h_domain_valid]
      rw [stdShannonEntropyLn_uniform_eq_log_card]
      simp only [Fintype.card_fin]
      rfl
    rw [h_shannon_eq_log_k]
    rfl
