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

import PPNP.Complexity.Program
import PPNP.Common.Basic
import PPNP.Entropy.Common
import PPNP.Entropy.Physics.Common
import PPNP.Entropy.RET
import PPNP.Entropy.Physics.UniformSystems



open Multiset NNReal Finset Function Real -- Added Function for comp_apply

open Multiset NNReal
open PPNP.Common
open PPNP.Complexity.Program
open PPNP.Entropy.Common
open PPNP.Entropy.Physics.Common
open PPNP.Entropy.Physics.UniformSystems
open PPNP.Entropy.RET



/-!
## Section 5.1: Simple Computational Model for i.i.d. Binary Processes (Definitions)

This section provides the foundational definitions for a simple computational model
based on i.i.d. binary choices, which forms the basis for RECT.
-/

/-- A single instruction/choice, represented by a Bool.
    Corresponds to one "bit" of choice from an i.i.d. source
    or one step in a binary decision tree. -/
def ComputerInstruction := Bool

/-- A sequence of choices/instructions forming the "program" or "path description".
    This is conceptually the Turing Machine's input tape. -/
def ComputerTape := List ComputerInstruction

/-- Represents the abstract state of a single particle or a simple system.
    The specific structure of SystemState is not crucial for the complexity definition
    focused on tape length, but it's part of the program definition. -/
structure SystemState where -- Example placeholder definition
  val : Nat

/-- A ClassicalComputerProgram is defined by an initial state and a tape of instructions
    that drives its evolution. -/
structure ClassicalComputerProgram where
  initial_state : SystemState
  tape : ComputerTape

/--
Axiom: Represents the deterministic evaluation of the program.
Given a program (initial state + tape), it outputs the final state.
The specific function `eval` is not defined here, only its existence and type.
-/
axiom ClassicalComputerProgram.eval (prog : ClassicalComputerProgram) : SystemState

/--
Defines the computational complexity of a `ClassicalComputerProgram` in this model.
It is defined as the length of its input `ComputerTape`, representing the
number of i.i.d. binary choices processed.
-/
def ClassicalComputerProgram.complexity (prog : ClassicalComputerProgram) : ℕ :=
  prog.tape.length


/-!
## Section 5.2: Shannon Entropy of a Specific Binary Tape Choice

This section defines the Shannon entropy associated with selecting one specific
m-bit tape from all 2^m equiprobable possibilities.
-/

/--
Calculates the Shannon entropy (using natural logarithm, in nats) associated with
the event of observing one specific `m_bits`-length binary tape, assuming all
$2^{m_{bits}}$ such tapes are equiprobable.
The probability of one specific tape is $1 / 2^{m_{bits}} = 2^{-m_{bits}}$.
Shannon entropy for one outcome is $-P \ln P = -(2^{-m_{bits}}) \ln(2^{-m_{bits}})$.
However, we are interested in the entropy of the *uniform distribution over all possible tapes*.
This distribution has $2^{m_{bits}}$ outcomes, each with probability $2^{-m_{bits}}$.
The Shannon entropy of this uniform distribution is $\ln(\text{Number of outcomes}) = \ln(2^{m_{bits}})$.

Note: `(2^m_bits : ℝ)` is `Nat.cast (Nat.pow 2 m_bits)`.
-/
noncomputable def ShannonEntropyOfTapeChoice (m_bits : ℕ) : ℝ :=
  if _hm_pos : m_bits > 0 then Real.log (2^m_bits : ℝ) else 0 * Real.log 2



/--
Helper lemma: Equivalent to a potentially missing `Real.log_nat_cast_pow_of_pos`.
Proves that `log (↑(x^n)) = n • log (↑x)` for natural numbers `x, n` where `x > 0`.
-/
lemma log_nat_cast_pow_of_pos (x n : ℕ) [_h : NeZero x] :
  Real.log (↑x ^ n) = n • Real.log (↑x) := by
  let x_real : ℝ := ↑x
  let n_real : ℝ := ↑n
  let real_pow_x_n : ℝ := (x ^ n : ℝ)
  simp [x_real, n_real, real_pow_x_n]


lemma shannon_entropy_of_tape_choice_eq_m_log2 (m_bits : ℕ) (hm_pos : m_bits > 0) :
    ShannonEntropyOfTapeChoice m_bits = ↑(m_bits : ℝ) * Real.log 2 := by
  simp [ShannonEntropyOfTapeChoice, dif_pos hm_pos, log_nat_cast_pow_of_pos]

lemma shannon_entropy_of_tape_choice_zero_div_log_two_eq_zero :
    ShannonEntropyOfTapeChoice 0 / Real.log 2 = 0 := by
  have h_cond_false : ¬ (0 > 0) := Nat.lt_irrefl 0
  simp [ShannonEntropyOfTapeChoice, dif_neg h_cond_false, zero_mul, zero_div]

/-
## Existence and Complexity of a Program for i.i.d. Binary Source
**Theorem Statement (RECT Part 1):** For any number of i.i.d. binary choices $m_{bits}$, there exists a `ClassicalComputerProgram` (whose tape is an $m_{bits}$-length sequence of these choices) such that its `ComputationalComplexity` (tape length) is equal to the Shannon Entropy (in bits) of selecting that specific $m_{bits}$-length tape.
-/
theorem existence_and_complexity_of_program_for_iid_binary_source (m_bits : ℕ) :
    ∃ (prog : ClassicalComputerProgram) (_hm_tape_len_eq_m_bits : prog.tape.length = m_bits),
      (ClassicalComputerProgram.complexity prog : ℝ) =
        (ShannonEntropyOfTapeChoice m_bits) / Real.log 2 := by
  let initial_st_example : SystemState := { val := 0 }
  let example_tape : ComputerTape := List.replicate m_bits true -- Content of tape does not matter for length
  have h_example_tape_len : example_tape.length = m_bits := by
    simp [example_tape] -- Unfolds example_tape and uses List.length_replicate

  let prog_exists : ClassicalComputerProgram :=
    { initial_state := initial_st_example, tape := example_tape }
  use prog_exists

  -- The goal for the second existential is `prog_exists.tape.length = m_bits`.
  -- `h_example_tape_len` is `example_tape.length = m_bits`.
  -- Since `prog_exists.tape` is definitionally `example_tape` (due to the definition of prog_exists),
  -- `prog_exists.tape.length` is definitionally equal to `example_tape.length`.
  -- Thus, `h_example_tape_len` serves as a proof for `prog_exists.tape.length = m_bits`.
  use h_example_tape_len
  -- Using `h_example_tape_len` here introduces a hypothesis, named `_hm_tape_len_eq_m_bits`
  -- (from the existential binder), into the context for the main goal.
  -- This hypothesis is `_hm_tape_len_eq_m_bits : prog_exists.tape.length = m_bits`.

  -- Main goal: (ClassicalComputerProgram.complexity prog_exists : ℝ) = (ShannonEntropyOfTapeChoice m_bits) / Real.log 2
  -- 1. Unfold ClassicalComputerProgram.complexity
  simp only [ClassicalComputerProgram.complexity]
  -- Goal is now: (prog_exists.tape.length : ℝ) = (ShannonEntropyOfTapeChoice m_bits) / Real.log 2
  -- 2. Rewrite prog_exists.tape.length to m_bits using h_example_tape_len.
  -- It seems the hypothesis introduced by `use h_example_tape_len` might be referenced via
  -- h_example_tape_len itself, rather than the binder name _hm_tape_len_eq_m_bits.
  rw [h_example_tape_len]
  -- Goal is now: (↑m_bits : ℝ) = ShannonEntropyOfTapeChoice m_bits / Real.log 2

  by_cases hm_eq_zero : m_bits = 0
  · -- Case: m_bits = 0
    rw [hm_eq_zero]
    -- Goal: (↑0 : ℝ) = ShannonEntropyOfTapeChoice 0 / Real.log 2
    rw [shannon_entropy_of_tape_choice_zero_div_log_two_eq_zero]
    -- Goal: (↑0 : ℝ) = 0
    simp only [Nat.cast_zero]
  · -- Case: m_bits ≠ 0
    have hm_pos : m_bits > 0 := Nat.pos_of_ne_zero hm_eq_zero
    rw [shannon_entropy_of_tape_choice_eq_m_log2 m_bits hm_pos] -- Apply the previously proven lemma
    -- Goal: (↑m_bits : ℝ) = ( (↑m_bits : ℝ) * Real.log 2 ) / Real.log 2
    have h_log_two_ne_zero : Real.log 2 ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one
      · norm_num -- Proves 0 < (2 : ℝ)
      · norm_num -- Proves (2 : ℝ) ≠ 1
    rw [mul_div_cancel_right₀ _ h_log_two_ne_zero] -- Cancels (Real.log 2)
    -- Goal: (↑m_bits : ℝ) = (↑m_bits : ℝ)
