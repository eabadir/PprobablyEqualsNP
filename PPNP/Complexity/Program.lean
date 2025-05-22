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





/-!
## Section 5.3: IID Binary Source and its Relation to ComputerProgram Complexity

This section defines an IID Binary Source that produces a sequence of fair, independent
binary choices, and relates its information content (via SCT) to the complexity
(tape length) of a ClassicalComputerProgram that represents one specific output sequence
from such a source. The length also corresponds to the Shannon entropy (in bits)
of a uniform distribution over all possible output sequences of that length.
-/

/--
Represents an IID (Independent and Identically Distributed) Fair Binary Source.
Such a source produces a sequence of bits, where each bit is 'true' with probability 0.5
and 'false' with probability 0.5, independently of other bits.
The 'num_choices' parameter indicates the length of the binary sequence produced.
-/
structure IIDFairBinarySource where
  num_choices : ℕ

/--
The Shannon entropy (in bits) of a single choice from an IIDFairBinarySource.
For a fair binary choice (p=0.5), H_bits(choice) = 1 bit.
Formally: - (0.5 * Real.logb 2 0.5 + (1-0.5) * Real.logb 2 (1-0.5)) = 1.
-/
noncomputable def ShannonEntropyPerChoice_IIDFairBinarySource (_source : IIDFairBinarySource) : ℕ  :=
  1

/--
According to Shannon's Source Coding Theorem, the minimum average number of bits
required to encode `s.num_choices` symbols from an IIDFairBinarySource is
`s.num_choices * ShannonEntropyPerChoice_IIDFairBinarySource s`.
This defines the "SCT optimal tape length".
-/
noncomputable def SCTOptimalTapeLength (s : IIDFairBinarySource) : ℕ  :=
  (s.num_choices : ℕ ) * ShannonEntropyPerChoice_IIDFairBinarySource s

/--
Theorem: For an IIDFairBinarySource producing `m_bits` choices, there exists
a ClassicalComputerProgram whose tape represents one specific outcome of these choices.
The complexity (tape length) of this program is equal to the SCTOptimalTapeLength
for encoding that sequence.
-/
theorem iid_source_tape_length_eq_sct_length (m_bits : ℕ) :
    ∃ (src : IIDFairBinarySource) (prog : ClassicalComputerProgram)
      (_h_src_choices : src.num_choices = m_bits)
      (_h_prog_tape_len : prog.tape.length = src.num_choices),
        (ClassicalComputerProgram.complexity prog : ℝ) = SCTOptimalTapeLength src := by
  -- 1. Define the IIDFairBinarySource
  let source_model : IIDFairBinarySource := { num_choices := m_bits }
  use source_model

  -- 2. Define the ClassicalComputerProgram (using a specific tape of the correct length)
  let initial_st_example : SystemState := { val := 0 }
  let example_tape : ComputerTape := List.replicate m_bits true -- Content doesn't matter for length
  let existing_prog : ClassicalComputerProgram :=
    { initial_state := initial_st_example, tape := example_tape }
  use existing_prog

  -- 3. Prove the hypothesis linking source choices to m_bits
  have h_src_choices_eq_m_bits : source_model.num_choices = m_bits := by simp [source_model]
  use h_src_choices_eq_m_bits

  -- 4. Prove the hypothesis linking program tape length to source choices
  have h_prog_tape_len_eq_src_choices : existing_prog.tape.length = source_model.num_choices := by
    exact by
      -- Goal: existing_prog.tape.length = source_model.num_choices
      -- Goal: (List.replicate m_bits true).length = m_bits
      rw [List.length_replicate]
      -- Goal: m_bits = m_bits

  use h_prog_tape_len_eq_src_choices

  -- 5. Main Goal: (ClassicalComputerProgram.complexity existing_prog : ℝ) = SCTOptimalTapeLength source_model
  simp only [ClassicalComputerProgram.complexity, SCTOptimalTapeLength, ShannonEntropyPerChoice_IIDFairBinarySource]
  -- Goal is now: (existing_prog.tape.length : ℝ) = (source_model.num_choices : ℝ) * 1.0
  rw [mul_one]
  -- Goal is now: (existing_prog.tape.length : ℝ) = (source_model.num_choices : ℝ)
  rw [h_prog_tape_len_eq_src_choices]
  -- Goal is now: (source_model.num_choices : ℝ) = (source_model.num_choices : ℝ)


/--
Theorem: The SCTOptimalTapeLength for an IIDFairBinarySource producing `num_choices` bits
is equal to the Shannon entropy (in bits) of a uniform distribution over all $2^{num_choices}$
possible tapes of that length. This connects the SCT-based length to the notion of
the tape representing one "microstate" from an ensemble of equiprobable microstates (tapes).
-/
theorem sct_optimal_tape_length_eq_entropy_of_uniform_tape_dist (src : IIDFairBinarySource) :
    SCTOptimalTapeLength src = (ShannonEntropyOfTapeChoice src.num_choices) / Real.log 2 := by
  simp only [SCTOptimalTapeLength, ShannonEntropyPerChoice_IIDFairBinarySource, mul_one]
  -- Goal: (src.num_choices : ℝ) = ShannonEntropyOfTapeChoice src.num_choices / Real.log 2

  -- This was proven implicitly by `existence_and_complexity_of_program_for_iid_binary_source` logic.
  -- We re-prove it here for clarity with the current goal structure.
  by_cases hm_eq_zero : src.num_choices = 0
  · -- Case: src.num_choices = 0
    rw [hm_eq_zero]
    rw [shannon_entropy_of_tape_choice_zero_div_log_two_eq_zero] -- Handles the 0 case for tape choice entropy
    simp only [Nat.cast_zero] -- (↑0 : ℝ) = 0
  · -- Case: src.num_choices > 0
    have hm_pos : src.num_choices > 0 := Nat.pos_of_ne_zero hm_eq_zero
    rw [shannon_entropy_of_tape_choice_eq_m_log2 src.num_choices hm_pos] -- Substitute definition of tape choice entropy
    -- Goal: (src.num_choices : ℝ) = (↑(src.num_choices : ℝ) * Real.log 2) / Real.log 2
    have h_log_two_ne_zero : Real.log 2 ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one
      · norm_num -- Proves 0 < (2 : ℝ)
      · norm_num -- Proves (2 : ℝ) ≠ 1
    rw [mul_div_cancel_right₀ _ h_log_two_ne_zero] -- Cancels (Real.log 2)
    -- Goal: (src.num_choices : ℝ) = (src.num_choices : ℝ)

/-!
## Section 5.4: Modeling Any ComputerProgram with an IID Binary Source

This section establishes that any ClassicalComputerProgram, characterized by its tape,
can be considered as a specific output from an IIDFairBinarySource. The number of
choices made by the source corresponds to the program's tape length (complexity),
and this complexity aligns with the SCTOptimalTapeLength for such a source.
-/

/--
Theorem: Any `ClassicalComputerProgram` can be modeled by an `IIDFairBinarySource`.
This means that for any given program, we can define an IID fair binary source
whose number of choices matches the program's tape length. The program's complexity
(tape length) is then equal to the SCTOptimalTapeLength for that source.
This also means the program's complexity is equivalent to the Shannon entropy (in bits)
of a uniform distribution over all possible tapes of that length.
-/
theorem program_modeled_by_iid_source (prog : ClassicalComputerProgram) :
    ∃ (src : IIDFairBinarySource),
      src.num_choices = prog.tape.length ∧
      (ClassicalComputerProgram.complexity prog : ℝ) = SCTOptimalTapeLength src ∧
      SCTOptimalTapeLength src = (ShannonEntropyOfTapeChoice src.num_choices) / Real.log 2 := by
  -- 1. Let L be the length of the program's tape.
  let L := prog.tape.length

  -- 2. Define an IIDFairBinarySource with num_choices = L.
  let source_model : IIDFairBinarySource := { num_choices := L }
  use source_model

  -- 3. Prove the first part of the conjunction: src.num_choices = prog.tape.length
  have h_choices_eq_tape_length : source_model.num_choices = prog.tape.length := by
    simp [source_model, L]

  -- 4. Prove the second part: (prog.complexity : ℝ) = SCTOptimalTapeLength src
  have h_complexity_eq_sct_length : (ClassicalComputerProgram.complexity prog : ℝ) = SCTOptimalTapeLength source_model := by
    simp only [ClassicalComputerProgram.complexity, SCTOptimalTapeLength, ShannonEntropyPerChoice_IIDFairBinarySource, mul_one]
    -- Goal: (prog.tape.length : ℝ) = (source_model.num_choices : ℝ)
    rw [h_choices_eq_tape_length] -- Substitute source_model.num_choices with prog.tape.length
    -- Goal: (prog.tape.length : ℝ) = (prog.tape.length : ℝ)


  -- 5. Prove the third part: SCTOptimalTapeLength src = (ShannonEntropyOfTapeChoice src.num_choices) / Real.log 2
  -- This is the statement of `sct_optimal_tape_length_eq_entropy_of_uniform_tape_dist`
  have h_sct_eq_entropy_choice : SCTOptimalTapeLength source_model = (ShannonEntropyOfTapeChoice source_model.num_choices) / Real.log 2 := by
    exact sct_optimal_tape_length_eq_entropy_of_uniform_tape_dist source_model

  -- 6. Combine the proofs for the conjunction
  exact ⟨h_choices_eq_tape_length, h_complexity_eq_sct_length, h_sct_eq_entropy_choice⟩


/-!
## Section 5.6: Random Walks, CAPrograms, System Evolution, and BE Snapshots

This section defines programs for individual random walks (CAProgram) and
for a system of multiple random walks (SystemEvolutionProgram).
It then connects snapshots of the system's evolution to the Bose-Einstein
encoding program previously defined.
-/

/-- State of a single 1D random walk: current position and time.
    Position can be Integer to allow negative values.
    Alternatively, if only counting 'up' steps, position can be Nat.
    For simplicity here, let's track number of 'up' steps (heads). -/
structure PathRandomWalkState where
  time : ℕ
  up_steps : ℕ -- Number of heads/up-steps
  -- invariant: up_steps ≤ time

/-- A sequence of states representing the path of a random walk. -/
def RandomWalkPath := List PathRandomWalkState

/--
A CAProgram models the evolution of a single 1D random walk for `T_steps`.
Its tape consists of `T_steps` binary choices (e.g., head/tail).
-/
structure CAProgram where
  T_steps : ℕ
  tape : ComputerTape -- Expected length T_steps
  -- invariant: tape.length = T_steps (can be enforced in constructor or checked)

/--
Axiom: Evaluates a CAProgram to produce the path of a single random walk.
The initial state is assumed to be (time=0, up_steps=0).
-/
axiom CAProgram.eval (prog : CAProgram) (_h_tape_len : prog.tape.length = prog.T_steps) : RandomWalkPath

def CAProgram.complexity (prog : CAProgram) : ℕ := prog.tape.length

/--
The SystemEvolutionProgram models the evolution of `num_walks` independent
1D random walks, each for `T_steps_per_walk`.
Its tape consists of `num_walks * T_steps_per_walk` binary choices.
-/
structure SystemEvolutionProgram where
  num_walks : ℕ
  T_steps_per_walk : ℕ
  system_tape : ComputerTape -- Expected length num_walks * T_steps_per_walk

/--
Axiom: Evaluates a SystemEvolutionProgram to produce a list of paths,
one for each of the `num_walks` random walks.
Assumes tapes are ordered/demuxed correctly.
-/
axiom SystemEvolutionProgram.eval (prog : SystemEvolutionProgram)
  (_h_tape_len : prog.system_tape.length = prog.num_walks * prog.T_steps_per_walk)
  : List RandomWalkPath -- List of n paths, each path is a List PathRandomWalkState

def SystemEvolutionProgram.complexity (prog : SystemEvolutionProgram) : ℕ := prog.system_tape.length

/--
Theorem: For any number of steps `T`, there exists a `CAProgram`
to model a random walk of that length.
Its complexity is `T`, and it can be modeled by an IID source of `T` choices.
-/
theorem existence_of_CAProgram (T_val : ℕ) :
    ∃ (ca_prog : CAProgram) (src : IIDFairBinarySource),
      ca_prog.T_steps = T_val ∧
      ca_prog.tape.length = T_val ∧
      CAProgram.complexity ca_prog = T_val ∧
      src.num_choices = T_val ∧
      (CAProgram.complexity ca_prog : ℝ) = SCTOptimalTapeLength src := by
  let example_tape_ca := List.replicate T_val true
  let prog : CAProgram := { T_steps := T_val, tape := example_tape_ca }
  let iid_src : IIDFairBinarySource := { num_choices := T_val }
  use prog
  use iid_src
  simp [example_tape_ca, prog, iid_src, CAProgram.complexity, List.length_replicate, SCTOptimalTapeLength, ShannonEntropyPerChoice_IIDFairBinarySource, mul_one]



/--
Theorem: For `n` walks each of `T` steps, there exists a `SystemEvolutionProgram`.
Its complexity is `n*T`, and it can be modeled by an IID source of `n*T` choices.
-/
theorem existence_of_SystemEvolutionProgram (n_walks_val : ℕ) (T_steps_val : ℕ) :
    ∃ (sys_prog : SystemEvolutionProgram) (src : IIDFairBinarySource),
      sys_prog.num_walks = n_walks_val ∧
      sys_prog.T_steps_per_walk = T_steps_val ∧
      sys_prog.system_tape.length = n_walks_val * T_steps_val ∧
      SystemEvolutionProgram.complexity sys_prog = n_walks_val * T_steps_val ∧
      src.num_choices = n_walks_val * T_steps_val ∧
      (SystemEvolutionProgram.complexity sys_prog : ℝ) = SCTOptimalTapeLength src := by
  let total_tape_len := n_walks_val * T_steps_val
  let example_tape_sys := List.replicate total_tape_len true
  let prog : SystemEvolutionProgram :=
    { num_walks := n_walks_val, T_steps_per_walk := T_steps_val, system_tape := example_tape_sys }
  let iid_src : IIDFairBinarySource := { num_choices := total_tape_len }
  use prog
  use iid_src
  simp [total_tape_len, example_tape_sys, prog, iid_src, SystemEvolutionProgram.complexity, List.length_replicate, SCTOptimalTapeLength, ShannonEntropyPerChoice_IIDFairBinarySource, mul_one]


/-!
Helper function to extract the total number of up-steps from a list of paths
at a specific snapshot time. Returns 0 if time is out of bounds for any path or paths are empty.
(A more robust implementation would handle errors or use Options).
-/
noncomputable def getTotalUpStepsAtSnapshot (paths : List RandomWalkPath) (snapshot_time : ℕ) : ℕ :=
  paths.foldl (fun acc path =>
    match List.get? path snapshot_time with -- Changed from path[snapshot_time]?
    | some (state : PathRandomWalkState) => acc + state.up_steps
    | none => acc -- Or handle error: for simplicity, just adds 0 if time is invalid for a path
  ) 0
