import Mathlib.Data.Sym.Card
import Std.Sat.CNF.Basic
--import Std.Data.List.Lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic -- For Fintype (Fin n) if needed, though usually direct
import Mathlib.Logic.Equiv.Defs -- For Equiv
import PPNP.Common.Basic

namespace PPNP.Complexity.Program

open Multiset NNReal Finset Function -- Added Function for comp_apply

open Multiset NNReal
open PPNP.Common



/-!
# A Detailed Plan for a Lean 4 Existential Proof of CNF Representation for the Stars and Bars Problem

This file implements the plan outlined in "CNF And Stars And Bars In Lean 4" (Plan 2).

## Structure of the Report (and this file)
Section 2: Formal Lean 4 Representation of the Stars and Bars Problem (SB_Instance)
Section 3: Boolean Encoding of Stars and Bars Solutions: The ComputerProgram Type
Section 4: Existence of a Conjunctive Normal Form (CNF) Representation for Stars and Bars
Section 5: Defining SBProgram and its Equivalence to NPCProgram
Section 6: Integration and Broader Implications (Discussion, not code)
-/

open Std.Sat -- For CNF, Literal, Clause, etc.
open Finset

universe u

/-!
## Section 2: Formal Lean 4 Representation of the Stars and Bars Problem
-/

/--
Represents an instance of the Stars and Bars problem.
N_balls: Number of indistinguishable items (stars).
M_boxes: Number of distinguishable containers (boxes).
-/
structure SB_Instance where
  (N_balls : ℕ)
  (M_boxes : ℕ)

-- For context, as discussed in Plan 2, Sec 2.3 (not directly used by the boolean verifier)
-- def UDMacrostate (N M : ℕ) := { q : Fin N → ℕ // ∑ i, q i = M }
-- def SymFin (M_boxes N_balls : ℕ) := Sym (Fin M_boxes) N_balls


/-!
## Section 3: Boolean Encoding of Stars and Bars Solutions: The ComputerProgram Type
The "Stars and Bars" string visualization: N_problem stars, M_problem-1 bars.
Total positions L = N_problem + (M_problem-1).
Boolean variables b_j: b_j=true if position j has a bar.
Constraint: Exactly M_problem-1 variables are true.
-/

/--
A ComputerProgram takes an assignment of truth values to its `num_vars` variables
and returns true if the input is "accepted", false otherwise.
-/
def ComputerProgram (num_vars : ℕ) := (Fin num_vars → Bool) → Bool

/--
Calculates the number of variables for the "bar position" encoding.
L = N_balls + M_boxes - 1.
This is only well-defined for the encoding if M_boxes >= 1.
If M_boxes = 0, the interpretation of "M_boxes - 1" bars is problematic.
We handle M_boxes = 0 as a special case in SB_Verifier.
-/
def num_encoding_vars_for_sb (inst : SB_Instance) : ℕ :=
  if inst.M_boxes = 0 then
    0 -- No bars to place, no "positions" in the same sense. Verifier will be const.
  else
    inst.N_balls + inst.M_boxes - 1

/--
Calculates the number of bars to be placed (number of variables that must be true).
K = M_boxes - 1.
-/
def num_bars_to_place (inst : SB_Instance) : ℕ :=
  if inst.M_boxes = 0 then
    0 -- Consistent with num_encoding_vars_for_sb = 0 for this case.
  else
    inst.M_boxes - 1

/--
The SB_Verifier for a Stars and Bars instance.
It takes a boolean assignment representing bar positions and checks the cardinality constraint.
-/
def SB_Verifier (inst : SB_Instance) : ComputerProgram (num_encoding_vars_for_sb inst) :=
  if h_M_boxes_zero : inst.M_boxes = 0 then
    -- Special case: 0 boxes.
    -- Here, num_encoding_vars_for_sb inst simplifies to 0.
    -- The verifier function for 0 variables is (fun (_ : Fin 0 → Bool) ↦ inst.N_balls == 0),
    -- which has type ComputerProgram 0.
    -- We need to show this is equivalent to ComputerProgram (num_encoding_vars_for_sb inst).
    -- We use h_M_boxes_zero to prove 0 = num_encoding_vars_for_sb inst, then use eq_rec (▸).
    have h_vars_type_eq : 0 = num_encoding_vars_for_sb inst := by
      simp [num_encoding_vars_for_sb, h_M_boxes_zero]
    h_vars_type_eq ▸ (fun (_ : Fin 0 → Bool) ↦ inst.N_balls == 0)
  else
    -- General case: M_boxes > 0
    -- num_vars = N_balls + M_boxes - 1
    -- num_true_needed = M_boxes - 1
    let num_vars := inst.N_balls + inst.M_boxes - 1
    let num_true_needed := inst.M_boxes - 1
    -- Proof that num_encoding_vars_for_sb inst = num_vars under this condition
    have h_num_vars_eq : num_encoding_vars_for_sb inst = num_vars := by
      simp [num_encoding_vars_for_sb, h_M_boxes_zero]; rfl
    -- Proof that num_bars_to_place inst = num_true_needed under this condition
    have h_num_true_eq : num_bars_to_place inst = num_true_needed := by
      simp [num_bars_to_place, h_M_boxes_zero]; rfl

    -- The verifier function, need to rewrite with the casts for num_vars
    fun (assignment : Fin (num_encoding_vars_for_sb inst) → Bool) ↦
      -- Card constraint: exactly K variables are true among N
      let assignment_casted : Fin num_vars → Bool := fun i => assignment (cast (by rw [←h_num_vars_eq]) i)
      (Fintype.card { j : Fin num_vars // assignment_casted j = true } = num_true_needed)

/-!
## Section 4: Existence of a Conjunctive Normal Form (CNF) Representation
-/

/--
A predicate asserting that a ComputerProgram `prog` has an equivalent CNF representation `C`.
-/
def HasCNFCertificate {num_vars : ℕ} (prog : ComputerProgram num_vars) : Prop :=
  ∃ (C : CNF (Fin num_vars)),
    ∀ (assignment_func : Fin num_vars → Bool),
      prog assignment_func ↔ C.eval assignment_func

-- Section 4.2.5: General CNF Existence (Refinement from user prompt)
/-
REMARK: General CNF Existence.
The `SB_Verifier` defined in Section 3.5 is a Boolean function
`(Fin n → Bool) → Bool`. By fundamental principles of Boolean logic, any such
function with a finite domain (here `2^n` possible assignments) has an
equivalent CNF representation. For example, one can construct the canonical CNF
by forming a conjunction of maxterms, where each maxterm rules out one specific
input assignment for which the function should be false. (This is true because
for any `φ : (Fin n → Bool) → Bool`, `φ` is equivalent to
`⋀_{τ | ¬φ τ} (¬ ⋀_{i | τ i} xᵢ ∧ ⋀_{i | ¬τ i} ¬xᵢ)`, which is CNF after distribution).
While this general existence is assured, for the particular cardinality
constraint embodied by `SB_Verifier` (when `M_boxes > 0`), a more direct and
standard CNF construction is known, which provides a clearer path for our
existential proof.
-/

variable {V : Type u} [Fintype V] [DecidableEq V]


noncomputable def at_most_k_CNF_def (k : ℕ) : Std.Sat.CNF V :=
  if _h_card_V_le_k : Fintype.card V ≤ k then
    []
  else
    let subsets_k_plus_1 := univ (α := V).powerset.filter (fun s => s.card = k + 1)
    subsets_k_plus_1.toList.map (fun s => s.toList.map (fun v => (v, false))) -- (v, false) is the negative literal ¬v

-- Assuming Std.Sat.Literal α is α × Bool (true for positive polarity)
-- and Std.Sat.Literal.negate l is (l.1, !l.2)

-- -- Local definition for Literal.eval for clarity in proofs.
-- -- If Std.Sat.Literal has its own `eval` with this meaning, this can be replaced.
-- @[local simp]
-- def LocalLiteralEval (l : Std.Sat.Literal V) (assignment : V → Bool) : Bool :=
--   assignment l.1 = l.2

-- -- Lemmata for direction -> (CNF eval true => card_true <= k)
-- section ImpliesLe

-- variable (k : ℕ) (assignment : V → Bool)
-- variable (h_k_lt_card_V : k < Fintype.card V) -- k < |V|
-- variable (h_card_true_gt_k : Fintype.card { v : V // assignment v = true } > k)
-- variable [Fintype α] [DecidablePred p]



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
