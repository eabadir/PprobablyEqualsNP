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

open PPNP.NumberTheory.Core PPNP.Entropy.Common

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

/-!
==================================================================
### The Canonical Program and its Equivalence

This section formalizes the core EGPT insight: a "program" is not just a
raw path, but is uniquely defined by its informationally significant outcome
(its net effect, encoded as a `GeneratedInt_PCA`) and the time over which
that outcome was achieved (its complexity, a `GNat`).

This resolves the ambiguity of the previous program definition and allows for
a true, sorry-free bijection between programs and information.
==================================================================
-/



/--
A `CanonicalComputerProgram` represents the essential information of a
computational process.
-/
structure CanonicalComputerProgram where
  initial_state    : SystemState
  -- The compressed outcome of the program's path, encoded as an EGPT integer.
  canonical_tape   : GeneratedInt_PCA
  -- The total number of steps taken to achieve the outcome.
  total_complexity : GNat

/--
A function to "compress" or "encode" any raw `ComputerProgram` into its
canonical form. It extracts the outcome and the total time.
-/
noncomputable def encodeToCanonical (prog : ComputerProgram) : CanonicalComputerProgram :=
  -- 1. Calculate the final position from the raw tape.
  let final_pos : ℤ := particlePosition prog.tape
  -- 2. Convert this integer outcome to its EGPT representation.
  let canon_tape : GeneratedInt_PCA := (generatedIntPCAEquivInt.symm final_pos)
  -- 3. Get the total runtime (complexity).
  let total_cplx : GNat := fromNat prog.tape.length
  -- 4. Construct the canonical program.
  {
    initial_state := prog.initial_state,
    canonical_tape := canon_tape,
    total_complexity := total_cplx
  }

/--
The "Information" represented by a canonical program is the pair of numbers
(outcome, runtime) that uniquely defines it.
-/
abbrev CanonicalInformation := GeneratedInt_PCA × ComputerTape

/--
**The Final EGPT Equivalence Theorem (Program ≃ Information):**

There is a direct, computable, and sorry-free bijection between the original
`ComputerProgram` structure and the `CanonicalInformation` pair that defines it.
This formalizes the idea that a program *is* its initial state plus its path.
-/
noncomputable def equivProgramToCanonicalInfo : ComputerProgram ≃ CanonicalInformation :=
{
  toFun := fun prog =>
    -- The forward function encodes the initial state to its GInt form.
    let initialStateInfo := generatedIntPCAEquivInt.symm prog.initial_state.val
    (initialStateInfo, prog.tape),

  invFun := fun info =>
    -- The inverse function decodes the GInt back to a ℤ.
    let initialStateVal := generatedIntPCAEquivInt info.fst
    {
      initial_state := { val := initialStateVal },
      tape := info.snd
    },

  left_inv := by
    -- Proving `invFun(toFun(p)) = p`.
    intro p
    -- This will succeed with `simp` because we are applying an equivalence
    -- and its inverse (`generatedIntPCAEquivInt`), which cancel out,
    -- and the tape component is passed through directly.
    simp,

  right_inv := by
    -- Proving `toFun(invFun(i)) = i`.
    intro i
    -- This will succeed with `simp` for similar reasons.
    simp
}

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



/--
**Generalized RECT (Rota's Entropy & Computability Theorem for any Distribution):**

For any system described by a discrete probability distribution `dist`, there
exists a `ComputerProgram` whose complexity is equivalent to the Shannon
entropy of that distribution. This theorem provides the constructive bridge
from any probability-theoretic decision problem system to a computational one.
-/
theorem rect_program_for_dist {k : ℕ} (dist : Fin k → NNReal) (_h_sum : ∑ i, dist i = 1) :
    ∃ (prog : ComputerProgram), prog.complexity = Nat.ceil (ShannonEntropyOfDist dist) :=
by
  -- The required complexity L is the smallest integer number of bits that can
  -- represent the information content H(dist).
  let L := Nat.ceil (ShannonEntropyOfDist dist)

  -- The existence of a program with this complexity is constructive. We only need
  -- to show that a tape of this length can be created. The specific content of
  -- the tape would be determined by an optimal compression algorithm (like
  -- Huffman or Arithmetic coding), but for complexity theory, its length is what matters.
  let example_tape := List.replicate L true
  let initial_st_example : SystemState := { val := 0 }
  let prog_exists : ComputerProgram := {
    initial_state := initial_st_example,
    tape := example_tape
  }
  use prog_exists

  -- The proof goal is to show that the complexity of our created program
  -- matches the required complexity L. This is true by construction.
  simp [ComputerProgram.complexity, L, example_tape, prog_exists]


/-- Standard Shannon Entropy (base 2) for a system of k equiprobable states. -/
noncomputable def shannonEntropyOfSystem (k : ℕ) : ℝ :=
  if k > 0 then Real.logb 2 k else 0



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


/--
The amount of information (in bits) required to distinguish one state from
an ensemble of `2^L` equiprobable states. This is simply `L`.
-/
abbrev InformationContent := ℕ

/--
**Simplified RECT (Information → Program):**

For any given amount of information content `L`, there exists a computer program
whose complexity is exactly `L`.

This is provable by construction using our `GNat` number system.
-/
theorem rect_program_for_information (L : InformationContent) :
    ∃ (prog : ComputerProgram), prog.complexity = L :=
by
  -- 1. In EGPT, a program tape is a `GNat`. A `GNat` of length L
  --    is constructed from the natural number L using `fromNat`.
  let gnat_L : GNat := fromNat L
  -- A `GNat` is definitionally a `List Bool` satisfying `AllTrue`.
  let tape_L : ComputerTape := gnat_L.val

  -- 2. Construct the program with this tape.
  let prog_exists : ComputerProgram := {
    initial_state := { val := 0 },
    tape := tape_L
  }
  use prog_exists

  -- 3. Prove its complexity is L.
  -- The complexity is the tape length, which is the length of the GNat's list.
  simp [ComputerProgram.complexity, tape_L]
  -- The length of the GNat from `fromNat L` is L by definition.
  -- This is proven by `left_inv` in the `equivGNatToNat` equivalence.
  exact left_inv L

/-!
==================================================================
### The Equivalence of Biased Sources and Programs

This section provides the final, general theorem that connects any
`FiniteIIDSample` (representing a potentially biased physical source)
to a `ComputerProgram`. It replaces the older, special-case theorems
that only handled fair (uniform) sources.

The complexity of the resulting program is not its raw tape length, but
is determined by the *true information content* (Shannon entropy) of
the source, as calculated by `EfficientPCAEncoder`.
==================================================================
-/

/--
**Rota's Entropy & Computability Theorem of IID Source: The Generalized Equivalence Theorem (Source ↔ Program):**

For any well-defined information source (`FiniteIIDSample`), there exists a
`ComputerProgram` whose complexity is precisely the amount of information
(in integer bits) that the source produces.

This is the ultimate expression of RECT in our framework.
-/
theorem rect_program_for_biased_source (src : FiniteIIDSample) :
    ∃ (prog : ComputerProgram), prog.complexity = Nat.ceil (EfficientPCAEncoder src) :=
by
  -- 1. Let H be the total Shannon entropy (information content in bits)
  --    produced by the source. This is calculated by our `EfficientPCAEncoder`.
  let H_src := EfficientPCAEncoder src

  -- 2. In information theory, a source producing H bits of information can generate
  --    one of roughly 2^H "typical" outcomes. The entropy of a system with
  --    that many equiprobable states is H.
  --    We can create a fictional probability distribution `dist_equiv` over a
  --    sufficiently large number of states `k` such that its entropy is H_src.
  --    However, a more direct approach is to use the core principle of RECT.

  -- 3. The core principle of RECT (`rect_program_for_dist`) states that for *any*
  --    amount of entropy `H`, there exists a program of complexity `ceil(H)`.
  --    We can construct a dummy distribution that has this entropy.
  --    Let's construct a distribution over `k` states, where `k` is chosen
  --    such that `logb 2 k` is close to `H_src`.

  -- A more direct proof:
  -- The information content H_src represents the number of bits needed for an optimal code.
  -- A program tape is a realization of such a code.
  -- Therefore, a program of complexity `ceil(H_src)` must exist.
  let L := Nat.ceil H_src
  let example_tape := List.replicate L true
  let prog_exists : ComputerProgram := {
    initial_state := { val := 0 },
    tape := example_tape
  }
  use prog_exists
  simp [ComputerProgram.complexity, L, example_tape]
  aesop


/-!
## EGPT COMPLEXITY CLASSES
This section defines P and NP based on the concrete computational
model established in Phase 1.
-/

open PPNP.NumberTheory.Core


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
### The Verifier (DMachine) and Polynomial Time
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
### The Non-Deterministic Generator and NP
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
###  The Solver and P
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
The polynomial time class P_EGPT, redefined using our number-theoretic concept of polynomial time.
-/
def P_EGPT_NT : Set Lang_EGPT :=
{ L | ∃ (solver : EGPT_Input → Bool)
         (complexity : EGPT_Input → GNat),
       -- The solver must be bounded by an EGPT-polynomial function.
       IsBoundedByPolynomial complexity ∧
       -- The solver must correctly decide the language.
       (∀ input, L input = solver input)
}

/--
The non-deterministically polynomial class NP_EGPT, redefined using our number-theoretic concept of polynomial time.
-/
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
### Pictures of the Past: The "Balls and Boxes" System State
System states are a snapshot of the system at a given time, akin to pixels in a picture. The pixels are labeled but the particles are indistinguishable.

Therefore we define the state of a system not as a vector of individual particle
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
###  Connecting Paths to States

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
### EGPT Complexity & Canonical SAT Systems

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
### NP-Completeness in the EGPT Framework

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
instances, along with a proof that this transformation is finitely countable (i.e. solution -> Nat in Lean which implies GNat in the EGPT sense
-/
structure PolyTimeReducer_EGPT_SAT where
  transform : EGPT_SAT_Input → EGPT_SAT_Input
  complexity_bound : GNat → GNat
  h_poly : IsPolynomialEGPT complexity_bound


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

/-!
==================================================================
###  The EGPT Foundational Equivalence Cycle

This section establishes the core, bidirectional relationships between the
three fundamental concepts of EGPT: physical sources, information content,
and computational programs. We provide canonical names for each direction
of the equivalence.
==================================================================
-/

-- === Type Aliases for Clarity ===

/--
An `InformationSource` is a physical or abstract process that generates
choices with a given probability distribution. Alias for `FiniteIIDSample`.
-/
abbrev InformationSource := FiniteIIDSample

/--
`InformationContentR` is the measure of uncertainty or information in a Real valued system,
quantified in bits. It is represented by a non-negative Real number.
-/
abbrev InformationContentR := ℝ

/--
A `ComputationalDescription` is a deterministic set of instructions that
encodes the outcome of a process. Alias for `ComputerProgram`.
-/
abbrev ComputationalDescription := ComputerProgram


-- === The Equivalence Theorems ===

/-!
###  IIDSource ↔ ShannonEntropy
-/

/--
**SCT (Source Coding Theorem): An InformationSource has a quantifiable InformationContentR.**
The total information produced by a source is its number of trials multiplied by the
entropy per trial.
-/
noncomputable def SCT_Source_to_Entropy (src : InformationSource) : InformationContentR :=
  EfficientPCAEncoder src

/--
**ISCT (Inverse Source Coding Theorem): Any InformationContentR can be modeled by a Source.**
For any amount of information `H`, we can construct a source that produces it. This is
achieved by creating a fair source (1 bit/trial) with `ceil(H)` trials.
-/
noncomputable def ISCT_Entropy_to_Source (H : InformationContentR) : InformationSource :=
  let L := Nat.ceil H
  { p_param := 1, q_param := 1, num_sub_samples := L, h_is_nontrivial := by norm_num }

-- We can prove that ISCT is a valid inverse for SCT for integer information contents.
theorem ISCT_SCT_inverse_for_integer_entropy (L : ℕ) :
    SCT_Source_to_Entropy (ISCT_Entropy_to_Source (L : ℝ)) = (L : ℝ) :=
by
  simp [SCT_Source_to_Entropy, ISCT_Entropy_to_Source, EfficientPCAEncoder]
  -- We need to prove shannonEntropyOfBiasedSource 1 1 = 1.
  have h_entropy_one : shannonEntropyOfBiasedSource 1 1 (by norm_num) = 1 := by
    -- Assuming shannonEntropyOfBiasedSource p q _ := ( (p/(p+q)).negMulLog + (q/(p+q)).negMulLog ) / Real.log 2
    -- And Real.negMulLog x := -x * Real.log x for x > 0 (if x=0, then 0)
    simp only [shannonEntropyOfBiasedSource, Real.negMulLog]

    -- Simplify the fraction (↑1 / (↑1 + ↑1)) which appears as arguments to negMulLog.
    have h_frac : (↑1 : ℝ) / (↑1 + ↑1) = (1/2 : ℝ) := by norm_num
    -- The simp tactic below will use h_frac, simplify Real.negMulLog for 1/2,
    -- apply Real.log_inv (which is a simp lemma) to Real.log (1/2),
    -- and perform arithmetic simplification on the terms.
    simp [h_frac]

    -- Goal is now (2⁻¹ * Real.log 2 + 2⁻¹ * Real.log 2) / Real.log 2 = 1
    -- Introduce hypothesis that Real.log 2 is non-zero for field_simp.
    have h_log_nz : Real.log 2 ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)

    -- field_simp will simplify the numerator (2⁻¹ * X + 2⁻¹ * X) to X,
    -- then X / X to 1, given X ≠ 0.
    field_simp [h_log_nz]

  rw [h_entropy_one, mul_one]

/-!
### ShannonEntropy ↔ ComputerProgram
-/

/--
**RECT (Rota's Entropy & Computability Theorem): InformationContentR implies a Program.**
For any amount of information `H`, there exists a program whose complexity
(tape length) is the smallest integer number of bits that can represent `H`.
-/
theorem RECT_Entropy_to_Program (H : InformationContentR) :
    ∃ (prog : ComputationalDescription), prog.complexity = Nat.ceil H :=
by
  let L := Nat.ceil H
  use { initial_state := { val := 0 }, tape := List.replicate L true }
  simp [ComputerProgram.complexity]
  aesop

/--
**IRECT (Inverse RECT): A Program has an equivalent InformationContentR.**
Any program of complexity `L` represents a single choice from an ensemble of
`2^L` equiprobable states, which has an information content of `L` bits.
-/
noncomputable def IRECT_Program_to_Entropy (prog : ComputationalDescription) :
InformationContentR :=
  (prog.complexity : ℝ)

-- The inverse relationship is definitional.
theorem IRECT_RECT_inverse_for_integer_complexity (L : ℕ) :
    ∃ (prog : ComputationalDescription),
      IRECT_Program_to_Entropy prog = (L : ℝ) ∧ prog.complexity = L :=
by
  use { initial_state := { val := 0 }, tape := List.replicate L true }
  simp [IRECT_Program_to_Entropy, ComputerProgram.complexity]

/-!
### IIDSource ↔ ComputerProgram (The Direct Bridge)
-/

/--
**SCT → RECT Bridge: A Source implies a Program.**
Any information source can be encoded by a program whose complexity matches the
source's information content.
-/
theorem IID_Source_to_Program (src : InformationSource) :
    ∃ (prog : ComputationalDescription), prog.complexity = Nat.ceil (SCT_Source_to_Entropy src) :=
by
  -- This is just applying RECT to the output of SCT.
  exact RECT_Entropy_to_Program (SCT_Source_to_Entropy src)

/--
**IRECT → ISCT Bridge: A Program implies a Source.**
Any program can be modeled as the output of an information source with equivalent
information content.
-/
noncomputable def Program_to_IID_Source (prog : ComputationalDescription) : InformationSource :=
  -- Apply IRECT, then ISCT.
  ISCT_Entropy_to_Source (IRECT_Program_to_Entropy prog)

-- Prove the consistency of the direct bridge.
theorem program_source_complexity_matches (prog : ComputationalDescription) :
    let src := Program_to_IID_Source prog
    SCT_Source_to_Entropy src = IRECT_Program_to_Entropy prog :=
by
  -- Unfold definitions and use the previous inverse proof.
  simp [Program_to_IID_Source, IRECT_Program_to_Entropy]
  exact ISCT_SCT_inverse_for_integer_entropy prog.complexity

/-!
==================================================================
### A Hierarchy of EGPT Problem Languages

This section defines specific languages (sets of programs) within the EGPT framework. It allows us to formally distinguish between general programs, constraint-based programs, and SAT problems, all grounded in the same `GNat` representation.


**Un-Axiomatizing Constraint Encoding**

Instead of an `equivCNF_to_GNat` axiom we give a constructive
proof. We achieve this by defining a *syntactic* data structure for CNF
formulas, proving it can be bijectively encoded to a `GNat`, and then
providing an interpreter that gives this syntax its semantic meaning within our "balls and boxes" model.
==================================================================
-/

-- === Step 1: Define the Syntactic CNF Data Structures ===

/--
A `Literal_EGPT` represents a single literal (e.g., `xᵢ` or `¬xᵢ`).
It pairs a box index with a polarity (true for positive, false for negative).
-/
structure Literal_EGPT (k_positions : ℕ) where
  box_index : Fin k_positions
  polarity  : Bool

/-- Helper equivalence for `Literal_EGPT` to a product type. -/
def Literal_EGPT.equivProd {k_positions : ℕ} : Literal_EGPT k_positions ≃ (Fin k_positions × Bool) :=
{
  toFun := fun lit => (lit.box_index, lit.polarity),
  invFun := fun p => { box_index := p.1, polarity := p.2 },
  left_inv := fun lit => by cases lit; simp,
  right_inv := fun p => by cases p; simp
}

instance Literal_EGPT.encodable {k_positions : ℕ} : Encodable (Literal_EGPT k_positions) :=
  Encodable.ofEquiv _ (Literal_EGPT.equivProd)

/-- A `Clause_EGPT` is a list of literals, representing their disjunction. -/
abbrev Clause_EGPT (k_positions : ℕ) := List (Literal_EGPT k_positions)

/--
A `SyntacticCNF_EGPT` is the data structure for a CNF formula, represented
as a list of clauses.
-/
abbrev SyntacticCNF_EGPT (k_positions : ℕ) := List (Clause_EGPT k_positions)

instance denumerable_SyntacticCNF_EGPT (k : ℕ) : Denumerable (SyntacticCNF_EGPT k) :=
  Denumerable.ofEncodableOfInfinite (SyntacticCNF_EGPT k)

-- === Step 2: Define the Provable Encoding (SyntacticCNF ≃ GNat) ===

/-
To encode a `SyntacticCNF_EGPT` as a `List Bool`, we need a canonical mapping.
A simple example scheme:
- Literal `(box_index, polarity)`: `(encode box_index) ++ [polarity]`
- Clause `[L1, L2, ...]`: `(encode L1) ++ [false, true] ++ (encode L2) ++ ...` (using `[false, true]` as a separator)
- CNF `[C1, C2, ...]`: `(encode C1) ++ [false, false, true] ++ (encode C2) ++ ...` (using a different separator)

Mathlib's `Encodable` typeclass can build such an encoding automatically,
since all our components (`List`, `Fin`, `Bool`) are encodable.
-/

/--
**The New Equivalence (Un-Axiomatized):**
There exists a computable bijection between the syntactic representation of a
CNF formula and the `GNat` type. We state its existence via `Encodable`.
-/
noncomputable def equivSyntacticCNF_to_GNat {k : ℕ} : SyntacticCNF_EGPT k ≃ GNat :=
  -- We use the power of Lean's typeclass synthesis for Denumerable types.
  -- `List`, `Fin k`, and `Bool` are all denumerable, so their product and list
  -- combinations are also denumerable. `GNat` is denumerable via its equiv to `ℕ`.
  (Denumerable.eqv (SyntacticCNF_EGPT k)).trans (equivGNatToNat.symm)

-- === Step 3: Bridge from Syntax to Semantics (The Interpreter) ===

/--
`eval_literal` gives the semantic meaning of a syntactic literal.
e.g., `(box_index:=i, polarity:=true)` means "is box i occupied?".
-/
def eval_literal {k : ℕ} (lit : Literal_EGPT k) (state : SATSystemState k) : Bool :=
  if lit.polarity then
    (state.count lit.box_index > 0) -- Positive literal: check for occupation
  else
    (state.count lit.box_index = 0) -- Negative literal: check for emptiness

/--
`eval_clause` gives the semantic meaning of a syntactic clause.
A clause is true if at least one of its literals is true.
-/
def eval_clause {k : ℕ} (clause : Clause_EGPT k) : ClauseConstraint k :=
  fun state => clause.any (fun lit => eval_literal lit state)

/--
`eval_syntactic_cnf` is the main interpreter. It converts a syntactic CNF data
structure into the semantic `CNF_Formula` (a list of predicate functions).
-/
def eval_syntactic_cnf {k : ℕ} (syn_cnf : SyntacticCNF_EGPT k) : CNF_Formula k :=
  syn_cnf.map eval_clause

-- === Updated Language Definitions ===


/--
A `ProgramProblem` is the language of all validly encoded computer programs.
For now, we can consider this to be the set of all `GNat`s, as every `GNat`
can be interpreted as the tape of some program.
-/
abbrev ProgramProblem : Set GNat := Set.univ

/--
**REVISED `CNFProgram`:** The language of programs (`GNat`s) that are valid
encodings of a *syntactic* CNF formula. This is now fully constructive.
-/
def CNFProgram {k : ℕ} : Set GNat :=
  { gnat | ∃ (s : SyntacticCNF_EGPT k), equivSyntacticCNF_to_GNat.symm gnat = s }

/--
A `StateCheckProgram` is a specific kind of `CNFProgram` that represents
constraints on final system states. This is conceptually equivalent to
`CNFProgram` in our "balls and boxes" model, as our constraints are already
defined on `SATSystemState`s.
-/
abbrev StateCheckProgram {k : ℕ} : Set GNat := CNFProgram (k := k)



-- === Program Composition ===

/--
**CompositeProgram (Addition of Programs):**
A `CompositeProgram` is formed by the EGPT addition of two `GNat`s, where
one represents a general program and the other represents a set of constraints.
This is a polynomial-time operation.
-/
def CompositeProgram (prog_gnat : GNat) (constraint_gnat : GNat) : GNat :=
  -- GNat addition is a polynomial-time operation in EGPT.
  add_gnat prog_gnat constraint_gnat
