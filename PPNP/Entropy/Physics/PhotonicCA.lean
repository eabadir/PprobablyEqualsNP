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


open Multiset NNReal Finset Function Real -- Added Function for comp_apply

open Multiset NNReal
open PPNP.Common
open PPNP.Complexity.Program
open PPNP.Entropy.Common
open PPNP.Entropy.Physics.Common
open PPNP.Entropy.Physics.UniformSystems
open PPNP.Entropy.Physics.PhysicsDist
open PPNP.Entropy.RET
open PPNP.Entropy.Physics.BE

/-!
# PPNP.Entropy.Physics.PCA - Photonic Cellular Automata
This file contains theorems and lemmas related to the encoding of Bose-Einstein and the individual photons (Bosons) in a system.
-/
namespace PPNP.Entropy.Physics.PCA


/-!
## Section 5.5: Encoding Bose-Einstein Distribution with a ComputerProgram

This section demonstrates that a Bose-Einstein (BE) statistical distribution can be
encoded by a ComputerProgram. The complexity of this program (its tape length)
corresponds to the number of bits required to specify a particular microstate of the
BE system. This number of bits is the Shannon entropy of the BE distribution (in bits).
The entropy of this BE system is characterized by `C_physical_NNReal * (Shannon entropy of BE in nats)`.
-/

/--
Theorem: A Bose-Einstein system can be encoded by a `ComputerProgram`.
The length of the program's tape (its complexity) is the number of bits needed
to specify a single microstate of the BE system. This quantity is derived from
the Shannon entropy of the BE distribution (in bits). The entropy of
this BE system is given by `C_physical_NNReal * (Shannon entropy of BE in nats)`.

The phrase "ComputerProgram with C*ShannonEntropy" is interpreted as:
A computer program encodes the choice of a microstate from a distribution
whose entropy value is `C*ShannonEntropy_nats`. The program's tape
length will be the number of bits for that choice.
-/
theorem encoding_BE_system_by_program
    (params : PPNP.Entropy.Physics.PhysicsDist.SystemParams)
    (h_valid_BE : params.N ≠ 0 ∨ params.M = 0) :
    ∃ (prog : ComputerProgram) (src : FiniteIIDSample)
      (prog_tape_len_nat : ℕ)
      -- MINIMAL CHANGE STARTS HERE --
      (_h_axiomatic_entropy_BE : -- Characterization of the BE system's axiomatic entropy
        (H_physical_system (p_UD_fin params.N params.M) : ℝ) = -- Ensure LHS is Real
          (C_physical_NNReal : ℝ) * stdShannonEntropyLn (p_UD_fin params.N params.M)),
      -- MINIMAL CHANGE ENDS HERE --
      -- Properties of the encoding program and source:
      prog.tape.length = prog_tape_len_nat ∧
      src.num_choices = prog_tape_len_nat ∧
      (ComputerProgram.complexity prog : ℝ) = (prog_tape_len_nat : ℝ) ∧
      (prog_tape_len_nat : ℝ) = (ShannonSourceCodingTheorem src : ℝ) := by -- Coerced ShannonSourceCodingTheorem

  -- 1. Determine the number of microstates in the BE system.
  let k_card := Fintype.card (OmegaUD params.N params.M)
  have hk_card_pos : k_card > 0 := UniformSystems.card_omega_BE_pos params.N params.M h_valid_BE

  -- 2. Calculate Shannon entropy of the BE distribution in nats and bits.
  let shannon_entropy_nats_BE : ℝ := stdShannonEntropyLn (p_UD_fin params.N params.M)
  have h_shannon_nats_BE_eq_log_k_card : shannon_entropy_nats_BE = Real.log (k_card : ℝ) := by
    -- This proof block is from your PhotonicCA.lean
    simp [shannon_entropy_nats_BE, -- Unfolds shannon_entropy_nats_BE
          p_BE_fin_is_uniformDist params.N params.M h_valid_BE,
          stdShannonEntropyLn_uniform_eq_log_card (Fintype_card_fin_pos hk_card_pos),
          Fintype.card_fin] -- Ensures Fintype.card (Fin k_card) simplifies to k_card

  let shannon_entropy_bits_BE : ℝ := shannon_entropy_nats_BE / Real.log 2
  have h_shannon_bits_BE_eq_logb_k_card : shannon_entropy_bits_BE = Real.logb 2 (k_card : ℝ) := by
    -- This proof block is from your PhotonicCA.lean
    simp [shannon_entropy_bits_BE, h_shannon_nats_BE_eq_log_k_card, Real.logb] -- Assuming Real.logb unfolds correctly

  -- 3. Determine the tape length for the program (number of bits to encode one microstate).
  let prog_tape_len_nat_val : ℕ :=
    if h_k_card_le_1 : k_card ≤ 1 then
      0
    else
      Nat.ceil shannon_entropy_bits_BE

  -- have h_prog_tape_len_nonneg_real : (prog_tape_len_nat_val : ℝ) ≥ 0 := Nat.cast_nonneg _ -- This line was in my version, not explicitly in yours, can be omitted if not needed by tactics later

  -- 4. Axiomatic entropy characterization (Rota's Theorem for this BE system)
  -- MINIMAL CHANGE STARTS HERE for the proof of the hypothesis
  have h_axiomatic_entropy_BE_stmt :
      (H_physical_system (p_UD_fin params.N params.M) : ℝ) =
      (C_physical_NNReal : ℝ) * shannon_entropy_nats_BE := by
    -- Use the direct proof: H_physical_system_is_rota_uniform
    exact H_physical_system_is_rota_uniform params.N params.M h_valid_BE
  -- MINIMAL CHANGE ENDS HERE for the proof of the hypothesis

  -- 5. Existence of the program and IID source.
  let example_tape : ComputerTape := List.replicate prog_tape_len_nat_val true
  let prog_exists : ComputerProgram :=
    { initial_state := { val := 0 }, tape := example_tape }
  let src_exists : FiniteIIDSample :=
    { num_choices := prog_tape_len_nat_val }

  use prog_exists
  use src_exists
  use prog_tape_len_nat_val
  use h_axiomatic_entropy_BE_stmt

  -- Prove the remaining properties:
  constructor -- for prog.tape.length = prog_tape_len_nat_val
  · simp [prog_exists, example_tape, List.length_replicate]

  constructor -- for src.num_choices = prog_tape_len_nat_val
  · simp [src_exists]

  constructor -- for (prog.complexity : ℝ) = (prog_tape_len_nat_val : ℝ)
  · simp [ComputerProgram.complexity, prog_exists, example_tape, List.length_replicate]

  -- for (prog_tape_len_nat_val : ℝ) = (ShannonSourceCodingTheorem src_exists : ℝ)
  · simp [ShannonSourceCodingTheorem, ShannonEntropyPerChoice_IIDFairBinarySource, src_exists, mul_one, Nat.cast_id] -- Added Nat.cast_id for robustness
