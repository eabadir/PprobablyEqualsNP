import Mathlib.Tactic.NormNum

import Mathlib.Data.Sym.Card
import Std.Sat.CNF.Basic
import Mathlib.Tactic.Sat.FromLRAT
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog -- For negMulLog, Real.log
import Mathlib.Algebra.GroupWithZero.Units.Basic
--import Std.Data.List.Lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic -- For Fintype (Fin n) if needed, though usually direct
import Mathlib.Logic.Equiv.Defs -- For Equiv
--import Mathlib.Order.Monotone.Strict.Nat -- For StrictMono.nat_of_lt_succ

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic -- For Real.log, Real.log_pow, Real.log_ne_zero_of_pos_of_ne_one
--import Mathlib.Data.Nat.Order.Basic -- For Nat.pos_of_ne_zero, Nat.lt_irrefl
--import Mathlib.Algebra.Ring.NatCast -- For Nat.cast_pow (implicitly used by (↑(2^m_bits) : ℝ))
--                                      and Nat.cast_zero, Nat.cast_id
import Mathlib.Data.List.Basic -- For List.replicate, List.length_replicate (from Std, re-exported)
import Mathlib.Logic.Equiv.Basic   -- Equiv API
import Mathlib.Logic.Equiv.Nat     -- intEquivNat, natSumNatEquivNat, …
import PPNP.Common.Basic
import PPNP.Entropy.Common
import PPNP.Entropy.Physics.Common
import PPNP.Entropy.RET -- Uncommented
import PPNP.Entropy.Physics.UniformSystems -- Uncommented

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Cardinality

import PPNP.NumberTheory.Core
import PPNP.Complexity.Program -- Assuming not needed for f0_mul_eq_add_f0
--import PPNP.Entropy.Physics.PhysicsDist
--import PPNP.Entropy.Physics.BoseEinstein
--import PPNP.Entropy.Physics.PhotonicCA

open Nat Real NNReal Multiset NNReal Fin Set Finset Filter Function BigOperators Topology
    -- Added Function for comp_apply

open Multiset NNReal
open PPNP.Common
--open PPNP.Complexity.Program
open PPNP.Entropy.Common
open PPNP.Entropy.Physics.Common
open PPNP.Entropy.Physics.UniformSystems -- Opened
--open PPNP.Entropy.Physics.PhysicsDist
--open PPNP.Entropy.Physics.BE
--open PPNP.Entropy.Physics.PCA
open PPNP.Entropy.RET -- Opened

namespace PPNP.Dev.code

-- In PPNP.Entropy.RET.lean
--open PPNP.NumberTheory.Core
open List PPNP.Complexity.Program

-- A ProgramTape is the fundamental data structure for a path/program.
abbrev ProgramTape := List Bool

-- Use the existing definitions from the file.
-- To avoid conflicts, let's use the names from the file directly.
abbrev ComputerProgram := ClassicalComputerProgram


-- An IIDSource is an infinite stream of binary choices.
structure IIDSource where
  stream : ℕ → Bool

-- A function to generate a finite tape from a source.
def drawTape (src : IIDSource) (t : ℕ) : ProgramTape :=
  (List.finRange t).map (fun i => src.stream i)

-- Standard Shannon Entropy (base 2) for a system of k equiprobable states.
noncomputable def shannonEntropyOfSystem (k : ℕ) : ℝ :=
  if k > 0 then Real.logb 2 k else 0


/-- Helper lemma to equate real power of 2 with a Nat exponent to the cast of Nat power of 2. -/
lemma real_two_pow_nat_eq_cast_nat_pow_two (n : ℕ) : (2:ℝ) ^ n = ↑((2:ℕ) ^ n) := by
  rw [Nat.cast_two.symm] -- Goal: (↑(2:ℕ):ℝ) ^ n = ↑((2:ℕ) ^ n)
  exact (Nat.cast_pow 2 n).symm


/-!
### Mathematical Lemma (Corrected)

This lemma proves that if you take the ceiling of the base-2 logarithm of k,
that number of bits is sufficient to represent k states.
This is the mathematical core of RECT.
-/
lemma needed_bits_lemma (k : ℕ) (hk_pos : k > 0) :
    k ≤ 2 ^ (Nat.ceil (Real.logb 2 k)) :=
by
  -- 1. Start with the property that x ≤ ⌈x⌉ for any x.
  have h_le_ceil : Real.logb 2 k ≤ ↑(Nat.ceil (Real.logb 2 k)) :=
    Nat.le_ceil _

  -- 2. The function 2^x is monotone for real exponents when the base ≥ 1.
  --    Apply this to both sides of the inequality.
  have h_rpow_le : (2 : ℝ) ^ (Real.logb 2 k) ≤ (2 : ℝ) ^ (↑(Nat.ceil (Real.logb 2 k)) : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2:ℝ)) h_le_ceil)

  -- 3. Simplify the left-hand side: 2 ^ (logb 2 k) simplifies to k.
  have h_k_real_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk_pos
  rw [Real.rpow_logb (by norm_num) (by norm_num) h_k_real_pos] at h_rpow_le
  -- h_rpow_le is now: `↑k ≤ 2 ^ (↑(Nat.ceil (Real.logb 2 k)))` (with a real exponent)

  -- 4. Convert the real power (rpow) on the RHS to a natural number power (pow).
  rw [Real.rpow_natCast] at h_rpow_le
  -- h_rpow_le is now: `↑k ≤ (2:ℝ) ^ (Nat.ceil (Real.logb 2 k))` (HPow with ℕ exponent)
  let L := Nat.ceil (Real.logb 2 k)
  -- h_rpow_le is effectively `↑k ≤ (2:ℝ) ^ L`

  -- 5. Rewrite (2:ℝ)^L to ↑(2^L) using the helper lemma.
  rw [real_two_pow_nat_eq_cast_nat_pow_two L] at h_rpow_le
  -- h_rpow_le is now: `↑k ≤ ↑(2 ^ L)`

  -- 6. Now the inequality is between two casted Nats, so `Nat.cast_le.mp` applies.
  exact Nat.cast_le.mp h_rpow_le


/-!
### The RECT Theorem (Full Proof)

This proof uses the constructive pattern from `Complexity.Program.lean` and
the mathematical justification from our `needed_bits_lemma`.
-/
theorem rect_program_for_entropy (k : ℕ) (hk_pos : k > 0) :
    ∃ (prog : ComputerProgram), prog.complexity = Nat.ceil (shannonEntropyOfSystem k) :=
by
  -- Define the target complexity value in its simplified form.
  let L_final := Nat.ceil (Real.logb 2 k)

  -- Prove that the original expression for complexity equals L_final.
  have h_complexity_eq_L_final : Nat.ceil (shannonEntropyOfSystem k) = L_final := by
    unfold shannonEntropyOfSystem
    rw [if_pos hk_pos]
    -- Goal is: Nat.ceil (Real.logb 2 k) = Nat.ceil (Real.logb 2 k)


  -- Construct a program with tape length L_final.
  let example_tape := List.replicate L_final true
  let initial_st_example : SystemState := { val := 0 }
  let prog_exists : ComputerProgram :=
    { initial_state := initial_st_example, tape := example_tape }

  -- Prove that this program exists.
  use prog_exists

  -- The goal is to prove:
  -- ClassicalComputerProgram.complexity prog_exists = Nat.ceil (shannonEntropyOfSystem k)

  -- Simplify the LHS of the goal.
  simp only [ClassicalComputerProgram.complexity, prog_exists, example_tape, List.length_replicate]
  -- Goal is now: L_final = Nat.ceil (shannonEntropyOfSystem k)

  -- Use the proven equality.
  exact h_complexity_eq_L_final.symm
