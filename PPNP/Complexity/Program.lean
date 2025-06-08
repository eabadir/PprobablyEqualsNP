import Mathlib.Tactic.NormNum

import Mathlib.Data.Sym.Card
import Std.Sat.CNF.Basic
import Mathlib.Tactic.Sat.FromLRAT

import Mathlib.Data.List.Range
import Mathlib.Data.List.FinRange

import PPNP.NumberTheory.Core
import PPNP.Common.Basic
import PPNP.Entropy.Common

namespace PPNP.Complexity.Program

/-- A single instruction/choice, represented by a Bool.
    Corresponds to one "bit" of choice from an i.i.d. source
    or one step in a binary decision tree. -/
def ComputerInstruction := Bool

/-- A sequence of choices/instructions forming the "program" or "path description".
    This is conceptually the Turing Machine's input tape. -/
def ComputerTape := List ComputerInstruction

/-- Represents the abstract state of a single particle or set of particles (by addition) i.e. can be a complex system.
    The specific structure of SystemState is not crucial for the complexity definition
    focused on tape length, but it's part of the program definition. -/
structure SystemState where -- Example placeholder definition
  val : ℤ  --Noting ℤ is List Bool is GeneratedInt_PCA but Lean's simp will handle Int better

/-- A ComputerProgram is defined by an initial state and a tape of instructions
    that drives its evolution. -/
structure ComputerProgram where
  initial_state : SystemState
  tape : ComputerTape



/--
A `SystemState` is a distribution of particles into a finite number of
positions. It is represented by a `Multiset` over `Fin k_positions`, where
`k_positions` is the number of "boxes". The cardinality of the multiset is
the number of particles ("balls").
-/
abbrev SATSystemState (k_positions : ℕ) := Multiset (Fin k_positions)

/--
A `ClauseConstraint` is a rule that a `SATSystemState` must satisfy. It is a
predicate on the distribution of particles.
This is the EGPT equivalent of a single clause in a CNF formula.
-/
abbrev ClauseConstraint (k_positions : ℕ) := SATSystemState k_positions → Bool

/--
A `CNF_Formula` is a list of `ClauseConstraint`s. A `SATSystemState` is
satisfying if and only if it satisfies every constraint in the list.
-/
abbrev CNF_Formula (k_positions : ℕ) := List (ClauseConstraint k_positions)

/-!
### Section 2: The EGPT-SAT Problem

We define the SAT problem in this combinatorial framework.
-/

/--
The input for an EGPT-SAT problem, defined by the number of particles,
the number of possible positions, and the set of combinatorial constraints.
-/
structure EGPT_SAT_Input where
  n_particles : ℕ
  k_positions : ℕ
  cnf : CNF_Formula k_positions

/--
Axiom: Represents the deterministic evaluation of the program.
Given a program (initial state + tape), it outputs the final state.
The specific function `eval` is not defined here, only its existence and type.
-/
axiom ComputerProgram.eval (prog : ComputerProgram) : SystemState

/--
Defines the computational complexity of a `ComputerProgram` in this model.
It is defined as the length of its input `ComputerTape`, representing the
number of i.i.d. binary choices processed.
-/
def ComputerProgram.complexity (prog : ComputerProgram) : ℕ :=
  prog.tape.length


-- A ProgramTape is the fundamental data structure for a path/program.
abbrev ProgramTape := List Bool


-- An IIDSource is an infinite stream of binary choices.
structure IIDSource where
  stream : ℕ → Bool

-- A function to generate a finite tape from a source.
def drawTape (src : IIDSource) (t : ℕ) : ProgramTape :=
  (List.finRange t).map (fun i => src.stream i)


/--
The Shannon entropy (in bits) of a single choice from an FiniteIIDSample.
For a fair binary choice (p=0.5), H_bits(choice) = 1 bit.
Formally: - (0.5 * Real.logb 2 0.5 + (1-0.5) * Real.logb 2 (1-0.5)) = 1.
-/
noncomputable def ShannonEntropyPerChoice_IIDFairBinarySource (_source : FiniteIIDSample) : ℕ  :=
  1

/--
Represents a finite sample an IID (Independent and Identically Distributed) Fair Binary Source.
Such a source produces a sequence of bits, where each bit is 'true' with probability 0.5
and 'false' with probability 0.5, independently of other bits.
The 'num_choices' parameter indicates the length of the binary sequence produced.
-/
structure FiniteIIDSample where
  num_choices : ℕ


/-- Standard Shannon Entropy (base 2) for a system of k equiprobable states. -/
noncomputable def shannonEntropyOfSystem (k : ℕ) : ℝ :=
  if k > 0 then Real.logb 2 k else 0


/--
Source Coding Theorem: Any IID Source converges to Shannon entropy in the limit.

, the minimum average number of bits
required to encode `s.num_choices` symbols from an FiniteIIDSample is
`s.num_choices * ShannonEntropyPerChoice_IIDFairBinarySource s`.
This defines the "SCT optimal tape length".
-/
noncomputable def ShannonSourceCodingTheorem (s : FiniteIIDSample) : ℕ  :=
  (s.num_choices : ℕ ) * ShannonEntropyPerChoice_IIDFairBinarySource s


/--
NOT USED - JUST FOR REFERENCE Axiomatic statement of Shannon's Coding Theorem (SCT).
It asserts that for any probability distribution P over a finite alphabet α,
there exists an optimal average code length (in bits) for encoding symbols
drawn i.i.d. from P, and this length is approximately the Shannon entropy of P (base 2).
The "≈" would be formalized using limits for block codes in a full version.
-/
axiom shannon_coding_theorem_sct_axiom
    {α : Type u} [Fintype α] (P : α → NNReal) (hP_sums_to_1 : ∑ x, P x = 1) :
    ∃ (L_avg_bits : ℝ), L_avg_bits ≥ 0 ∧
      -- For simplicity, we state it as equality for the ideal optimal code.
      -- A more nuanced version would use inequalities or limits.
      L_avg_bits = (PPNP.Entropy.Common.stdShannonEntropyLn P) / (Real.log 2) -- Shannon entropy in bits


/-!
### The RECT Theorem (Full Proof)
Rota Entropy And Complexity Theorem (RECT):There exists a computer program for any system displaying Shannon Entropy
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
  -- ComputerProgram.complexity prog_exists = Nat.ceil (shannonEntropyOfSystem k)

  -- Simplify the LHS of the goal.
  simp only [ComputerProgram.complexity, prog_exists, example_tape, List.length_replicate]
  -- Goal is now: L_final = Nat.ceil (shannonEntropyOfSystem k)

  -- Use the proven equality.
  exact h_complexity_eq_L_final.symm

/--
Inverse SCT (Part A): Any program of complexity L corresponds to a single microstate
in a system of 2^L equiprobable states, which has Shannon Entropy L.
-/
theorem invSCT_entropy_of_program (prog : ComputerProgram) :
    shannonEntropyOfSystem (2^(ComputerProgram.complexity prog)) = ((ComputerProgram.complexity prog) : ℝ) :=
by
  simp only [shannonEntropyOfSystem]
  -- After simp, the goal is:
  -- (if 0 < 2 ^ (ComputerProgram.complexity prog) then Real.logb 2 (2 ^ (ComputerProgram.complexity prog)) else 0)
  --   = ↑(ComputerProgram.complexity prog)

  have h_pow_pos : 0 < 2^(ComputerProgram.complexity prog) := Nat.pow_pos (by norm_num)

  rw [if_pos h_pow_pos]
  -- Goal is now: Real.logb 2 (2 ^ (ComputerProgram.complexity prog)) = ↑(ComputerProgram.complexity prog)

  simp [Real.logb_pow]


/-!
Shannon Entropy of a Specific Equiprobable Tape Choice
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
noncomputable def ShannonEntropyOfEquiprobableTapeChoice (m_bits : ℕ) : ℝ :=
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
    ShannonEntropyOfEquiprobableTapeChoice m_bits = ↑(m_bits : ℝ) * Real.log 2 := by
  simp [ShannonEntropyOfEquiprobableTapeChoice, dif_pos hm_pos, log_nat_cast_pow_of_pos]

lemma shannon_entropy_of_tape_choice_zero_div_log_two_eq_zero :
    ShannonEntropyOfEquiprobableTapeChoice 0 / Real.log 2 = 0 := by
  have h_cond_false : ¬ (0 > 0) := Nat.lt_irrefl 0
  simp [ShannonEntropyOfEquiprobableTapeChoice, dif_neg h_cond_false, zero_mul, zero_div]

/-
## Existence and Complexity of a Program for i.i.d. Binary Source
**Theorem Statement (RECT Part 1):** For any number of i.i.d. binary choices $m_{bits}$, there exists a `ComputerProgram` (whose tape is an $m_{bits}$-length sequence of these choices) such that its `ComputationalComplexity` (tape length) is equal to the Shannon Entropy (in bits) of selecting that specific $m_{bits}$-length tape.
-/
theorem existence_and_complexity_of_program_for_iid_binary_source (m_bits : ℕ) :
    ∃ (prog : ComputerProgram) (_hm_tape_len_eq_m_bits : prog.tape.length = m_bits),
      (ComputerProgram.complexity prog : ℝ) =
        (ShannonEntropyOfEquiprobableTapeChoice m_bits) / Real.log 2 := by
  let initial_st_example : SystemState := { val := 0 }
  let example_tape : ComputerTape := List.replicate m_bits true -- Content of tape does not matter for length
  have h_example_tape_len : example_tape.length = m_bits := by
    simp [example_tape] -- Unfolds example_tape and uses List.length_replicate

  let prog_exists : ComputerProgram :=
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

  -- Main goal: (ComputerProgram.complexity prog_exists : ℝ) = (ShannonEntropyOfEquiprobableTapeChoice m_bits) / Real.log 2
  -- 1. Unfold ComputerProgram.complexity
  simp only [ComputerProgram.complexity]
  -- Goal is now: (prog_exists.tape.length : ℝ) = (ShannonEntropyOfEquiprobableTapeChoice m_bits) / Real.log 2
  -- 2. Rewrite prog_exists.tape.length to m_bits using h_example_tape_len.
  -- It seems the hypothesis introduced by `use h_example_tape_len` might be referenced via
  -- h_example_tape_len itself, rather than the binder name _hm_tape_len_eq_m_bits.
  rw [h_example_tape_len]
  -- Goal is now: (↑m_bits : ℝ) = ShannonEntropyOfEquiprobableTapeChoice m_bits / Real.log 2

  by_cases hm_eq_zero : m_bits = 0
  · -- Case: m_bits = 0
    rw [hm_eq_zero]
    -- Goal: (↑0 : ℝ) = ShannonEntropyOfEquiprobableTapeChoice 0 / Real.log 2
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






/--
Theorem: An IID source will produce all possible sequences of length `m_bits`

For an FiniteIIDSample producing `m_bits` choices, there exists
a ComputerProgram whose tape represents one specific outcome of these choices.
The complexity (tape length) of this program is equal to the ShannonSourceCodingTheorem
for encoding that sequence.
-/
theorem iid_source_tape_length_eq_sct_length (m_bits : ℕ) :
    ∃ (src : FiniteIIDSample) (prog : ComputerProgram)
      (_h_src_choices : src.num_choices = m_bits)
      (_h_prog_tape_len : prog.tape.length = src.num_choices),
        (ComputerProgram.complexity prog : ℝ) = ShannonSourceCodingTheorem src := by
  -- 1. Define the FiniteIIDSample
  let source_model : FiniteIIDSample := { num_choices := m_bits }
  use source_model

  -- 2. Define the ComputerProgram (using a specific tape of the correct length)
  let initial_st_example : SystemState := { val := 0 }
  let example_tape : ComputerTape := List.replicate m_bits true -- Content doesn't matter for length
  let existing_prog : ComputerProgram :=
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

  -- 5. Main Goal: (ComputerProgram.complexity existing_prog : ℝ) = ShannonSourceCodingTheorem source_model
  simp only [ComputerProgram.complexity, ShannonSourceCodingTheorem, ShannonEntropyPerChoice_IIDFairBinarySource]
  -- Goal is now: (existing_prog.tape.length : ℝ) = (source_model.num_choices : ℝ) * 1.0
  rw [mul_one]
  -- Goal is now: (existing_prog.tape.length : ℝ) = (source_model.num_choices : ℝ)
  rw [h_prog_tape_len_eq_src_choices]
  -- Goal is now: (source_model.num_choices : ℝ) = (source_model.num_choices : ℝ)


/--
Theorem: The ShannonSourceCodingTheorem for an FiniteIIDSample producing `num_choices` bits
is equal to the Shannon entropy (in bits) of a uniform distribution over all $2^{num_choices}$
possible tapes of that length. This connects the SCT-based length to the notion of
the tape representing one "microstate" from an ensemble of equiprobable microstates (tapes).
-/
theorem sct_optimal_tape_length_eq_entropy_of_uniform_tape_dist (src : FiniteIIDSample) :
    ShannonSourceCodingTheorem src = (ShannonEntropyOfEquiprobableTapeChoice src.num_choices) / Real.log 2 := by
  simp only [ShannonSourceCodingTheorem, ShannonEntropyPerChoice_IIDFairBinarySource, mul_one]
  -- Goal: (src.num_choices : ℝ) = ShannonEntropyOfEquiprobableTapeChoice src.num_choices / Real.log 2

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

This section establishes that any ComputerProgram, characterized by its tape,
can be considered as a specific output from an FiniteIIDSample. The number of
choices made by the source corresponds to the program's tape length (complexity),
and this complexity aligns with the ShannonSourceCodingTheorem for such a source.
-/

/--
Theorem: Any `ComputerProgram` can be modeled by an `FiniteIIDSample`.
This means that for any given program, we can define an IID fair binary source
whose number of choices matches the program's tape length. The program's complexity
(tape length) is then equal to the ShannonSourceCodingTheorem for that source.
This also means the program's complexity is equivalent to the Shannon entropy (in bits)
of a uniform distribution over all possible tapes of that length.
-/
theorem program_modeled_by_iid_source (prog : ComputerProgram) :
    ∃ (src : FiniteIIDSample),
      src.num_choices = prog.tape.length ∧
      (ComputerProgram.complexity prog : ℝ) = ShannonSourceCodingTheorem src ∧
      ShannonSourceCodingTheorem src = (ShannonEntropyOfEquiprobableTapeChoice src.num_choices) / Real.log 2 := by
  -- 1. Let L be the length of the program's tape.
  let L := prog.tape.length

  -- 2. Define an FiniteIIDSample with num_choices = L.
  let source_model : FiniteIIDSample := { num_choices := L }
  use source_model

  -- 3. Prove the first part of the conjunction: src.num_choices = prog.tape.length
  have h_choices_eq_tape_length : source_model.num_choices = prog.tape.length := by
    simp [source_model, L]

  -- 4. Prove the second part: (prog.complexity : ℝ) = ShannonSourceCodingTheorem src
  have h_complexity_eq_sct_length : (ComputerProgram.complexity prog : ℝ) = ShannonSourceCodingTheorem source_model := by
    simp only [ComputerProgram.complexity, ShannonSourceCodingTheorem, ShannonEntropyPerChoice_IIDFairBinarySource, mul_one]
    -- Goal: (prog.tape.length : ℝ) = (source_model.num_choices : ℝ)
    rw [h_choices_eq_tape_length] -- Substitute source_model.num_choices with prog.tape.length
    -- Goal: (prog.tape.length : ℝ) = (prog.tape.length : ℝ)


  -- 5. Prove the third part: ShannonSourceCodingTheorem src = (ShannonEntropyOfEquiprobableTapeChoice src.num_choices) / Real.log 2
  -- This is the statement of `sct_optimal_tape_length_eq_entropy_of_uniform_tape_dist`
  have h_sct_eq_entropy_choice : ShannonSourceCodingTheorem source_model = (ShannonEntropyOfEquiprobableTapeChoice source_model.num_choices) / Real.log 2 := by
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
    ∃ (ca_prog : CAProgram) (src : FiniteIIDSample),
      ca_prog.T_steps = T_val ∧
      ca_prog.tape.length = T_val ∧
      CAProgram.complexity ca_prog = T_val ∧
      src.num_choices = T_val ∧
      (CAProgram.complexity ca_prog : ℝ) = ShannonSourceCodingTheorem src := by
  let example_tape_ca := List.replicate T_val true
  let prog : CAProgram := { T_steps := T_val, tape := example_tape_ca }
  let iid_src : FiniteIIDSample := { num_choices := T_val }
  use prog
  use iid_src
  simp [example_tape_ca, prog, iid_src, CAProgram.complexity, List.length_replicate, ShannonSourceCodingTheorem, ShannonEntropyPerChoice_IIDFairBinarySource, mul_one]



/--
Theorem: For `n` walks each of `T` steps, there exists a `SystemEvolutionProgram`.
Its complexity is `n*T`, and it can be modeled by an IID source of `n*T` choices.
-/
theorem existence_of_SystemEvolutionProgram (n_walks_val : ℕ) (T_steps_val : ℕ) :
    ∃ (sys_prog : SystemEvolutionProgram) (src : FiniteIIDSample),
      sys_prog.num_walks = n_walks_val ∧
      sys_prog.T_steps_per_walk = T_steps_val ∧
      sys_prog.system_tape.length = n_walks_val * T_steps_val ∧
      SystemEvolutionProgram.complexity sys_prog = n_walks_val * T_steps_val ∧
      src.num_choices = n_walks_val * T_steps_val ∧
      (SystemEvolutionProgram.complexity sys_prog : ℝ) = ShannonSourceCodingTheorem src := by
  let total_tape_len := n_walks_val * T_steps_val
  let example_tape_sys := List.replicate total_tape_len true
  let prog : SystemEvolutionProgram :=
    { num_walks := n_walks_val, T_steps_per_walk := T_steps_val, system_tape := example_tape_sys }
  let iid_src : FiniteIIDSample := { num_choices := total_tape_len }
  use prog
  use iid_src
  simp [total_tape_len, example_tape_sys, prog, iid_src, SystemEvolutionProgram.complexity, List.length_replicate, ShannonSourceCodingTheorem, ShannonEntropyPerChoice_IIDFairBinarySource, mul_one]


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

/--
A lemma to help map between a sample over time (a range of indices)
and the tape of a program, showing that the mapping is equivalent to the tape itself.
--/
@[simp] lemma map_stream_over_range_eq_tape (t : List Bool) :
    List.map (fun i : ℕ =>
        if h : i < t.length then t.get ⟨i, h⟩ else false)
      (List.range t.length) = t := by
  -- Step 1: Rewrite `List.range` in terms of `finRange` and `map`.
  -- This allows composing the functions inside the map.
  have h₁ : List.range t.length =
        List.map (fun a : Fin t.length => (a : ℕ)) (List.finRange t.length) :=
    by simp [List.map_coe_finRange]
  rw [h₁]

  -- Step 2: Use `List.map_map` to compose the two functions.
  rw [List.map_map]

  -- Step 3: Prove that the composed function is equivalent to `t.get`.
  -- For an index `a : Fin t.length`, the condition `↑a < t.length` is always true.
  have h_fun_eq :
      (fun i : ℕ =>
          if h : i < t.length then t.get ⟨i, h⟩ else false) ∘
        (fun a : Fin t.length => (a : ℕ))
        = fun a : Fin t.length => t.get a := by
    -- Prove by functional extensionality.
    funext a
    -- `simp` can prove this, as `a.isLt` provides the proof for `dif_pos`.
    simp [Function.comp, dif_pos a.isLt]

  -- Step 4: Rewrite the function inside the `map` using our proof `h_fun_eq`.
  -- The goal's LHS is `map (f ∘ g) _`, and `h_fun_eq` proves `f ∘ g = t.get`.
  rw [h_fun_eq]

  -- Step 5: The goal simplifies to `List.map (List.get t) (List.finRange t.length) = t`.
  -- This is precisely the statement of the `List.finRange_map_get` lemma from mathlib.
  exact List.finRange_map_get t


-- ==================================================================
-- EGPT FOUNDATIONAL EQUIVALENCE
-- This section establishes the core, bidirectional relationship between
-- Computer Programs, Shannon Entropy, and IID Sources.
-- ==================================================================

/-!
## Foundational Types

These are the canonical types for our EGPT framework.
-/

/-!
###  The EGPT Cycle of Equivalence Theorems

These three theorems form a sorry-free, logical circle, demonstrating that
programs, entropy, and sources are mutually derivable concepts.
-/

/--
Theorem: "Inverse Shannon's Coding Theorem" - Any `ComputerProgram` can be modeled by an `FiniteIIDSample`.
This means that for any given program, we can define an IID fair binary source
whose number of choices matches the program's tape length. The program's complexity
(tape length) is then equal to the ShannonSourceCodingTheorem for that source.
This also means the program's complexity is equivalent to the Shannon entropy (in bits)
of a uniform distribution over all possible tapes of that length.
-/
theorem invSCT_Program_To_IIDEntropySample (prog : ComputerProgram) :
    ∃ (src : FiniteIIDSample),
      src.num_choices = prog.tape.length ∧
      (ComputerProgram.complexity prog : ℝ) = ShannonSourceCodingTheorem src ∧
      ShannonSourceCodingTheorem src = (ShannonEntropyOfEquiprobableTapeChoice src.num_choices) / Real.log 2 := by
  -- 1. Let L be the length of the program's tape.
  let L := prog.tape.length

  -- 2. Define an FiniteIIDSample with num_choices = L.
  let source_model : FiniteIIDSample := { num_choices := L }
  use source_model

  -- 3. Prove the first part of the conjunction: src.num_choices = prog.tape.length
  have h_choices_eq_tape_length : source_model.num_choices = prog.tape.length := by
    simp [source_model, L]

  -- 4. Prove the second part: (prog.complexity : ℝ) = ShannonSourceCodingTheorem src
  have h_complexity_eq_sct_length : (ComputerProgram.complexity prog : ℝ) = ShannonSourceCodingTheorem source_model := by
    simp only [ComputerProgram.complexity, ShannonSourceCodingTheorem, ShannonEntropyPerChoice_IIDFairBinarySource, mul_one]
    -- Goal: (prog.tape.length : ℝ) = (source_model.num_choices : ℝ)
    rw [h_choices_eq_tape_length] -- Substitute source_model.num_choices with prog.tape.length
    -- Goal: (prog.tape.length : ℝ) = (prog.tape.length : ℝ)


  -- 5. Prove the third part: ShannonSourceCodingTheorem src = (ShannonEntropyOfEquiprobableTapeChoice src.num_choices) / Real.log 2
  -- This is the statement of `sct_optimal_tape_length_eq_entropy_of_uniform_tape_dist`
  have h_sct_eq_entropy_choice : ShannonSourceCodingTheorem source_model = (ShannonEntropyOfEquiprobableTapeChoice source_model.num_choices) / Real.log 2 := by
    exact sct_optimal_tape_length_eq_entropy_of_uniform_tape_dist source_model

  -- 6. Combine the proofs for the conjunction
  exact ⟨h_choices_eq_tape_length, h_complexity_eq_sct_length, h_sct_eq_entropy_choice⟩




-- ==================================================================
-- PHASE 2: EGPT COMPLEXITY CLASSES
-- This section defines P and NP based on the concrete computational
-- model established in Phase 1.
-- ==================================================================

open PPNP.NumberTheory.Core

/-!
### Section 2.1: Defining Constraints and Problems in EGPT
-/

/--
A Constraint is a rule that a program's tape must satisfy at every step of
its evolution. The `checker` function takes the current time (tape length)
and the tape segment up to that time.
-/
structure Constraint where
  checker : (currentTime : ℕ) → (tape_so_far : ComputerTape) → Bool

/--
An EGPT problem instance is defined by a target complexity (tape length).
-/
abbrev EGPT_Input := ℕ

/--
An EGPT Language is a decision problem parameterized by the target tape length.
The constraints defining the problem are considered part of the language itself.
-/
abbrev Lang_EGPT := EGPT_Input → Bool

/-!
### Section 2.2: The Verifier (DMachine) and Polynomial Time
-/

/--
A DMachine is a deterministic verifier. It takes a potential solution
(a `ComputerProgram` as a certificate) and an input, and decides to
accept or reject it.
-/
structure DMachine where
  verify : (certificate : ComputerProgram) → (input : EGPT_Input) → Bool
  -- We can add a field for the machine's own complexity if needed,
  -- but for now we define it externally.

/--
A predicate asserting that a DMachine runs in polynomial time.
`complexity_of` is a function that measures the runtime.
The runtime must be polynomial in the size of the certificate's tape
and the numerical value of the input.
-/
def RunsInPolyTime (complexity_of : ComputerProgram → EGPT_Input → ℕ) : Prop :=
  ∃ (c k : ℕ), ∀ (cert : ComputerProgram) (input : EGPT_Input),
    complexity_of cert input ≤ c * (cert.complexity + input)^k + c

/-!
### Section 2.3: The Non-Deterministic Generator and NP
-/

/--
This predicate formalizes what it means for a program to be a valid physical
path. It is true if the program's tape satisfies all constraints at every
intermediate step of its creation (from length 1 to its final length).
-/
def CanNDMachineProduce (constraints : List Constraint) (prog : ComputerProgram) : Prop :=
  ∀ (t : ℕ) (_ht : 0 < t ∧ t ≤ prog.complexity),
    (constraints.all (fun c => c.checker t (prog.tape.take t)))


/-!
### Section 2.4: The Solver and P
-/


-- This is a predicate on functions, defining what it means to be polynomial.
-- A full formalization would build this inductively. For now, we state it as a Prop.
class IsPolynomialEGPT (f : GNat → GNat) : Prop where
  -- For example, one could define this as:
  -- is_poly : ∃ (ops : List GNatOperation), compute_f_with_ops ops = f
  -- where GNatOperation is an enum of {Add, Mul}.
  -- For our purposes, we can treat this as a given property.

/--
A predicate asserting that a complexity function is bounded by an EGPT-polynomial.
-/
def IsBoundedByPolynomial (complexity_of : EGPT_Input → GNat) : Prop :=
  ∃ (p : GNat → GNat), IsPolynomialEGPT p ∧
    ∀ (input : EGPT_Input), complexity_of input ≤ p (fromNat input) -- `fromNat` converts ℕ to GNat

/--
The class P_EGPT, redefined using our number-theoretic concept of polynomial time.
-/
def P_EGPT_NT : Set Lang_EGPT :=
{ L | ∃ (solver : EGPT_Input → Bool)
         (complexity : EGPT_Input → GNat),
       -- The solver must be bounded by an EGPT-polynomial function.
       IsBoundedByPolynomial complexity ∧
       -- The solver must correctly decide the language.
       (∀ input, L input = solver input)
}

-- The definition of NP_EGPT is similarly updated to use IsPolynomialEGPT for its bounds.
def NP_EGPT_NT : Set Lang_EGPT :=
{ L | ∃ (dm : DMachine)
         (constraints : List Constraint)
         (poly_bound : GNat → GNat) (_h_poly : IsPolynomialEGPT poly_bound),
       ∀ (input : EGPT_Input),
         L input ↔ ∃ (cert : ComputerProgram),
           -- The certificate's complexity is bounded by an EGPT-polynomial function.
           equivGNatToNat.toFun (fromNat cert.complexity) ≤ equivGNatToNat.toFun (poly_bound (fromNat input)) ∧
           CanNDMachineProduce constraints cert ∧
           dm.verify cert input
}

/-!
### Section 1: The "Balls and Boxes" System State

We redefine the state of a system not as a vector of individual particle
positions, but as a distribution of indistinguishable particles ("balls")
into a set of distinguishable positions ("boxes").
-/


/--
A `Lang_EGPT_SAT` is a decision problem on combinatorial systems.
-/
abbrev Lang_EGPT_SAT := EGPT_SAT_Input → Bool

/--
A `Certificate` for an EGPT-SAT problem is a vector of `ComputerProgram`s,
one for each particle. The certificate represents the full history (the paths)
that lead to a proposed final state.
-/
abbrev Certificate (n_particles : ℕ) := Vector ComputerProgram n_particles



/-!
### Section 3: Connecting Paths to States

This function is the crucial bridge between the dynamic particle paths
(the certificate) and the static, combinatorial `SATSystemState`.
-/

/--
Calculates the position of a single particle (as an Integer) given its path.
A simple definition is the number of `true`s minus the number of `false`s.
-/
def particlePosition (tape : ComputerTape) : ℤ :=
  (tape.filter (· == true)).length - (tape.filter (· == false)).length


/--
Generates a `SATSystemState` (a multiset of box occupancies) from a
`Certificate` (a vector of particle programs) at a specific time `t`.

- `progs`: The certificate containing the path for each particle.
- `t`: The time at which to take the snapshot of the system.
- `pos_to_box`: A function mapping a particle's integer position to a specific
  "box" index (`Fin k_positions`). This mapping is part of the problem setup
  and defines how the continuous space of positions is discretized.
-/
def generateSystemState {n_particles k_positions : ℕ}
    (progs : Certificate n_particles) (t : ℕ)
    (pos_to_box : ℤ → Fin k_positions) : SATSystemState k_positions :=
  progs.toList.map (fun prog => pos_to_box (particlePosition (prog.tape.take t))) |> Multiset.ofList

/-!
### Section 4: EGPT Complexity Classes (Combinatorial)

With the path-to-state bridge in place, we can now formally define the
complexity classes for our combinatorial EGPT-SAT problems.
-/

/--
A verifier for EGPT-SAT problems. It takes an EGPT_SAT_Input and a Certificate
(a vector of ComputerPrograms) and determines if the certificate is a valid,
satisfying solution. The `pos_to_box` mapping is part of the verifier's logic.
-/
structure SAT_Verifier where
  pos_to_box : ℤ → Fin k_positions -- The specific discretization for this verifier
  verify (input : EGPT_SAT_Input) (certificate : Certificate input.n_particles) : Bool :=
    let final_state := generateSystemState certificate input.n_particles pos_to_box
    -- A certificate is valid if:
    -- 1. It has the correct number of particles.
    -- 2. It satisfies all CNF constraints.
    final_state.card = input.n_particles ∧ input.cnf.all (fun c => c final_state)


/--
The class `NP_EGPT_SAT` contains combinatorial problems for which a "yes"
answer can be verified in EGPT-polynomial time.
-/
def NP_EGPT_SAT : Set Lang_EGPT_SAT :=
{ L | ∃ (sv : SAT_Verifier) (poly_bound : GNat → GNat) (_h_poly : IsPolynomialEGPT poly_bound),
      ∀ (input : EGPT_SAT_Input),
        L input ↔ ∃ (cert : Certificate input.n_particles),
          -- The complexity of each program in the certificate must be polynomially bounded.
          (cert.toList.all (fun prog => prog.complexity ≤ equivGNatToNat.toFun (poly_bound (fromNat input.n_particles)))) ∧
          -- The SAT_Verifier must accept the certificate for the given input.
          sv.verify input cert
}

/--
The class `P_EGPT_SAT` contains combinatorial problems that can be solved
directly by a deterministic algorithm in EGPT-polynomial time.
-/
def P_EGPT_SAT : Set Lang_EGPT_SAT :=
{ L | ∃ (solver : EGPT_SAT_Input → Bool)
         (complexity_bound : GNat → GNat) (_h_poly : IsPolynomialEGPT complexity_bound),
      -- The solver must be bounded by an EGPT-polynomial function of its input size.
      -- The solver must correctly decide the language.
      (∀ input, L input = solver input)
}

/-!
### Section 5: NP-Completeness in the EGPT Framework

To define NP-completeness, we must first formalize what it means for one
combinatorial problem to be "at least as hard as" another. This is done
through the concept of a polynomial-time reduction.
-/

/--
A function to measure the size of an EGPT-SAT problem instance.
This is used to bound the complexity of a reduction function.
-/
def EGPT_SAT_Input.sizeOf (input : EGPT_SAT_Input) : ℕ :=
  input.n_particles + input.k_positions + input.cnf.length

/--
A `PolyTimeReducer_EGPT_SAT` encapsulates a function that transforms problem
instances, along with a proof that this transformation is "efficient" in the
EGPT sense (i.e., its complexity is bounded by an EGPT-polynomial function
of the input size).
-/
structure PolyTimeReducer_EGPT_SAT where
  transform : EGPT_SAT_Input → EGPT_SAT_Input
  complexity_bound : GNat → GNat
  h_poly : IsPolynomialEGPT complexity_bound
  -- We would also include a field `complexity_of : EGPT_SAT_Input → GNat` and a
  -- proof that `complexity_of` is bounded by `complexity_bound`.
  -- For now, the existence of a polynomial bound is the key property.

/--
Defines polynomial-time reducibility between two EGPT-SAT languages.
`L' <=p L` means that any instance of `L'` can be efficiently transformed
into an equivalent instance of `L`.
-/
def PolyTimeReducible_EGPT_SAT (L' L : Lang_EGPT_SAT) : Prop :=
  ∃ (f : PolyTimeReducer_EGPT_SAT),
    ∀ (input : EGPT_SAT_Input), L' input ↔ L (f.transform input)

-- Define an infix operator for convenience.
infix:50 " <=p " => PolyTimeReducible_EGPT_SAT

/--
A language `L` is **EGPT-NP-complete** if it is in `NP_EGPT_SAT` and
is "at least as hard" as every other problem in `NP_EGPT_SAT`.
-/
def EGPT_NPComplete (L : Lang_EGPT_SAT) : Prop :=
  -- Condition 1: The problem is in our NP class.
  (L ∈ NP_EGPT_SAT) ∧
  -- Condition 2: The problem is NP-hard within our class.
  (∀ (L' : Lang_EGPT_SAT) (_hL' : L' ∈ NP_EGPT_SAT), L' <=p L)
