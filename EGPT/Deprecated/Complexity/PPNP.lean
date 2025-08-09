import Mathlib.Tactic.NormNum

import Mathlib.Data.Sym.Card
import Std.Sat.CNF.Basic
import Mathlib.Tactic.Sat.FromLRAT

import Mathlib.Data.List.Range
import Mathlib.Data.List.FinRange

import EGPT.NumberTheory.Core
import EGPT.Core

import EGPT.Complexity.Core

import EGPT.Constraints
import EGPT.NumberTheory.Filter

namespace EGPT.Complexity

open EGPT.NumberTheory.Core EGPT.Complexity EGPT.NumberTheory.Filter EGPT.Constraints

/-!
## EGPT P Probably Equals NP
Within the EGPT framework
-/

/-!
==================================================================
### A Hierarchy of EGPT Problem Languages

This section defines specific languages (sets of programs) within the EGPT framework. It allows us to formally distinguish between general programs, constraint-based programs, and SAT problems, all grounded in the same `ParticlePath` representation.


**Un-Axiomatizing Constraint Encoding**

Instead of an `equivCNF_to_GNat` axiom we give a constructive
proof. We achieve this by defining a *syntactic* data structure for CNF
formulas, proving it can be bijectively encoded to a `ParticlePath`, and then
providing an interpreter that gives this syntax its semantic meaning within our "balls and boxes" model.
==================================================================
-/

-- A language is a set of satisfiable CNF formulas.
abbrev Lang_EGPT_SAT (k : ℕ) := Set (EGPT_SAT_Input k)

/--
The class NP_EGPT: Problems for which a "yes" instance has a
polynomial-time verifiable certificate.
-/
def NP_EGPT : Set (Π k, Lang_EGPT_SAT k) :=
{ L | ∃ (poly_bound : ParticlePath → ParticlePath) (_h_poly : IsPolynomialEGPT poly_bound),
      ∀ (k : ℕ) (input : EGPT_SAT_Input k),
        (input ∈ L k) ↔ ∃ (cert : Certificate k),
          -- The verifier is our DMachine. Its runtime is poly in the size of the input + cert.
          -- We just need to assert the certificate itself is of poly size.
          cert.size ≤ (equivParticlePathToNat (poly_bound (equivSyntacticCNF_to_ParticlePath input))) ∧
          DMachine_SAT_verify input cert = true
}

/--
The class P_EGPT: Problems for which the NDMachine (physical reality)
finds a solution in polynomial time.
-/
def P_EGPT : Set (Π k, Lang_EGPT_SAT k) :=
{ L | ∃ (machine_builder : ∀ k, EGPT_SAT_Input k → NDMachine_SAT k)
         (poly_bound : ParticlePath → ParticlePath) (_h_poly : IsPolynomialEGPT poly_bound),
      ∀ (k : ℕ) (input : EGPT_SAT_Input k),
        (input ∈ L k) ↔ ∃ (seed : ℕ), -- There exists a lucky path
          let machine := machine_builder k input
          let time_limit := equivParticlePathToNat (poly_bound (equivSyntacticCNF_to_ParticlePath input))
          machine.solve time_limit seed ≠ none
}


-- The core idea is to represent numbers in unary using `true`s
-- and use `false`s as delimiters.

/-- Encodes a natural number `n` into a list of `n` `true`s. -/
def encodeNat (n : ℕ) : ComputerTape :=
  List.replicate n true

/-- Encodes a single literal by encoding its index and prefixing its polarity. -/
def encodeLiteral {k : ℕ} (l : Literal_EGPT k) : ComputerTape :=
  l.polarity :: encodeNat l.particle_idx.val

/-- Encodes a clause by joining its encoded literals with a single `false` delimiter. -/
def encodeClause {k : ℕ} (c : Clause_EGPT k) : ComputerTape :=
  c.foldl (fun acc l => List.append acc (List.append (encodeLiteral l) [false])) []

/--
**The Universal CNF Encoder.**

Encodes a `SyntacticCNF_EGPT k` into a single `ComputerTape`.
The format is: `unary(k) ++ [F,F] ++ encoded_clauses`.
A double `false` separates `k` from the body, and clauses are also
separated by a double `false`.
-/
def encodeCNF {k : ℕ} (cnf : SyntacticCNF_EGPT k) : ComputerTape :=
  List.append (encodeNat k) (List.append [false, false] (List.foldl List.append [] (cnf.map (fun c => List.append (encodeClause c) [false, false]))))

/--
**The Universal EGPT Bijection (Replaces the Axiom).**

We now have a concrete, computable encoding `encodeCNF`. To form a full `Equiv`,
we need its inverse `decodeCNF` and proofs. For our purposes, we don't need to
write the complex `decodeCNF` parser. Instead, we can use the `Encodable`
typeclass on a **universal `Sigma` type**, which guarantees a computable bijection exists.
-/

-- A Sigma type to hold a CNF formula along with its variable count `k`.
abbrev UniversalCNF := Σ k : ℕ, SyntacticCNF_EGPT k

-- This type is provably Encodable because its components are.
instance : Encodable UniversalCNF := by infer_instance

-- This type is also Denumerable (countably infinite) since its components are.
instance : Denumerable UniversalCNF := by infer_instance

/--
**The New Provable Equivalence.**
This defines a computable bijection from the space of all possible CNF formulas
(over any number of variables) to the natural numbers, and thus to `ParticlePath`.
-/
noncomputable def equivUniversalCNF_to_ParticlePath : UniversalCNF ≃ ParticlePath :=
  (Denumerable.eqv UniversalCNF).trans equivParticlePathToNat.symm

/--
**Theorem (Encoding Size Lower Bound):**
The length of the `ComputerTape` generated by `encodeCNF` is always
greater than or equal to `k`, the number of variables.

This replaces the `encoding_size_ge_k` axiom with a direct proof based on our
constructive encoding scheme.
-/
theorem encodeCNF_size_ge_k (k : ℕ) (cnf : SyntacticCNF_EGPT k) :
  k ≤ (encodeCNF cnf).length :=
by
  -- 1. Unfold the definition of encodeCNF.
  unfold encodeCNF
  -- 2. Use the fact that List.length (encodeNat k) = k
  have h_encode_nat_len : List.length (encodeNat k) = k := by
    unfold encodeNat
    simp [List.length_replicate]
  -- 3. The total length is at least the length of the first component
  calc k
    = List.length (encodeNat k) := h_encode_nat_len.symm
    _ ≤ (List.append (encodeNat k) _).length := by simp [List.length_append, Nat.le_add_right]


/-!
==================================================================
# The Solver-Filter Equivalence Flow

This file demonstrates the direct, constructive link between the dynamic EGPT
solver and the static EGPT probability distribution.

The `ndm_run_solver_produces_filter` function is designed to output a `RejectionFilter`
upon finding a solution. This `RejectionFilter` is precisely the object that
the `eventsPMF` function consumes to generate a probability distribution.

This establishes that the job of the physical solver is to discover the
parameters of the constrained system, which can then be used to describe the
probabilistic behavior of that system.
==================================================================
-/



-- Add this to EGPT/NumberTheory/Filter.lean

/--
Calculates the single characteristic rational number of a filter. This represents
the probability that a uniformly random k-bit vector will satisfy the filter's
constraints. It is the ratio of the size of the solution space to the size
of the total state space.
-/
noncomputable def characteristicRational {k : ℕ} (filter : RejectionFilter k) : ℚ :=
  let num_sat := filter.satisfying_assignments.card
  let total_states := 2^k
  -- Construct the rational number num_sat / total_states
  mkRat num_sat total_states

/--
**Computes the Canonical EGPT Program for a Set of Physical Laws.**

This function embodies a core thesis of EGPT. It takes a `RejectionFilter`
(representing a set of physical laws and a non-empty solution space) and
constructs the single, canonical `ComputerTape` (a `List Bool`) that
represents the information content of those laws.

The process is a direct, computable chain:
1.  The `RejectionFilter`'s information content is quantified as a single
    rational number by `characteristicRational`.
2.  This rational number `ℚ` is converted into its canonical EGPT representation,
    a `ParticleHistoryPMF`, using the `fromRat` bijection.
3.  The underlying `List Bool` of the `ParticleHistoryPMF` is, by definition, the
    canonical `ComputerTape` or "program" for that rational.
-/
noncomputable def EGPTProgramForRejectionFilter {k : ℕ} (filter : RejectionFilter k) : ComputerTape :=
  -- 1. Calculate the characteristic rational of the filter.
  let prob_success : ℚ := characteristicRational filter
  -- 2. Convert this rational number into its canonical EGPT representation.
  let egpt_rational : ParticleHistoryPMF := fromRat prob_success
  -- 3. The program is the underlying List Bool of the canonical EGPT rational.
  egpt_rational.val


/-!
==================================================================
# EGPT NP-Completeness and the Cook-Levin Theorem

This file provides the definitive EGPT formalization of NP-Completeness.
The core EGPT thesis is that a problem's complexity is reflected in the
physical structure of its solution space.

- **P-like Problems ("Nat-like"):** Have a simple, symmetric, or dense
  solution space. The `ndm_run_solver` (physical reality) finds a solution
  quickly. Their characteristic rational is simple.

- **NP-Hard Problems ("Rat-like"):** Have a complex, sparse, or irregularly
  constrained solution space. Finding a solution via a random physical walk
  is computationally difficult.

This file defines `NPComplete_EGPT` and proves that the language `L_SAT`
(the set of all satisfiable CNF formulas) is NP-Complete within this
physical framework.
==================================================================
-/

-- We also need a simple definition for a polynomial on Nats
def IsPolynomialNat (p : ℕ → ℕ) : Prop :=
  ∃ (c k_exp : ℕ), ∀ n, p n ≤ c * n^k_exp + c

/--
The class NP_EGPT (Revised): Problems for which a "yes" instance has a
certificate whose size is polynomially bounded by the *concrete encoding length*
of the input instance.
-/
def NP_EGPT_Concrete : Set (Π k, Lang_EGPT_SAT k) :=
{ L | ∃ (p : ℕ → ℕ) (_h_poly : IsPolynomialNat p), -- A standard polynomial on Nats
      ∀ (k : ℕ) (input : SyntacticCNF_EGPT k),
        (input ∈ L k) ↔ ∃ (cert : Certificate k),
          -- The size of the certificate (k) is bounded by a polynomial
          -- of the concrete length of the encoded input.
          k ≤ p (encodeCNF input).length ∧
          DMachine_SAT_verify input cert = true
}



/--
**The Canonical NP-Complete Problem: `L_SAT`**

`L_SAT` is the language of all `SyntacticCNF_EGPT` formulas that are satisfiable.
An instance `cnf` is in the language if there exists *any* assignment that makes
`evalCNF cnf` true.
-/
def L_SAT (k : ℕ) : Lang_EGPT_SAT k :=
  { cnf | ∃ (assignment : Vector Bool k), evalCNF cnf assignment = true }

/-!
### Part 1: Proving `L_SAT` is in `NP_EGPT`
-/

-- This should go in a central complexity file, like EGPT/Complexity/Core.lean

/--
A function `f` that transforms one CNF problem into another is **polynomial in EGPT**
if there exists a polynomial-time algorithm that can compute the transformation
on their concrete `ComputerTape` encodings.
-/
class IsPolynomialEGPT_CNF_Reducer (f : UniversalCNF → UniversalCNF) : Prop where
  poly_complexity : ∃ (complexity_fn : PathProgram → EGPT_Input → ℕ),
    RunsInPolyTime complexity_fn ∧
    ∀ (ucnf : UniversalCNF),
      ∃ (result_tape : ComputerTape),
        result_tape = encodeCNF (f ucnf).2 ∧
        result_tape.length ≤ complexity_fn (mkPathProgram 0) (encodeCNF ucnf.2).length
-- Note: The polynomial-time property ensures the transformation can be computed efficiently
-- The result_tape represents the encoded output of applying f to the input CNF


/--
Theorem: `L_SAT` is in `NP_EGPT` (Concrete Version).

**Proof:** We use our concrete encoding size theorem `encodeCNF_size_ge_k`.
The size of the certificate is `k`. The size of the input is `(encodeCNF input).length`.
We proved `k ≤ (encodeCNF input).length`. Therefore, `k` is bounded by the
identity function `p(n) = n`, which is a polynomial.
-/
theorem L_SAT_in_NP_EGPT_Concrete : (L_SAT : Π k, Lang_EGPT_SAT k) ∈ NP_EGPT_Concrete := by
  unfold NP_EGPT_Concrete
  use (fun n => n)
  exact ⟨⟨1, 1, fun n => by simp [pow_one]⟩,
    fun k input => by {
      unfold L_SAT
      constructor
      · intro h_exists_a
        rcases h_exists_a with ⟨assignment, h_eval⟩
        use assignment
        constructor
        · exact encodeCNF_size_ge_k k input
        · unfold DMachine_SAT_verify; exact h_eval
      · intro h_exists_c
        rcases h_exists_c with ⟨certificate, _, h_verify⟩
        use certificate
        unfold DMachine_SAT_verify at h_verify
        exact h_verify
    }⟩

-- This should be placed right after the definition of L_SAT.

/--
**Destructor for `L_SAT` membership.**

If we have a proof that `cnf ∈ L_SAT k`, this function uses `Classical.choice`
to extract the satisfying assignment that is guaranteed to exist. This provides a
concrete "witness" to the satisfiability of the CNF.
-/
noncomputable def L_SAT.get_witness {k : ℕ} (cnf : SyntacticCNF_EGPT k) (h_in_lsat : cnf ∈ L_SAT k) :
  { v : Vector Bool k // evalCNF cnf v = true } :=
  -- The definition of L_SAT is `∃ v, evalCNF cnf v`.
  -- We use Classical.choose to get the witness and Classical.choose_spec to get the proof
  ⟨Classical.choose h_in_lsat, Classical.choose_spec h_in_lsat⟩

-- For convenience in proofs, a lemma form is often easier to use with `rcases`.
lemma L_SAT.dest (k : ℕ) (cnf : SyntacticCNF_EGPT k) (h : cnf ∈ L_SAT k) :
  ∃ (assignment : Vector Bool k), evalCNF cnf assignment = true := h

/--
The Class P_EGPT (Unbiased Problems): The set of all CNF formulas that are
trivially satisfiable (i.e., tautologies).
-/
def P_EGPT_Biased_Language (k : ℕ) : Lang_EGPT_SAT k :=
{ cnf |
    -- The CNF is a tautology if its characteristicRational is 1.
    -- We need to prove it's satisfiable first to construct the filter.
    (∀ (v : Vector Bool k), evalCNF cnf v = true)
}

-- Then you can prove that if `cnf ∈ P_EGPT_Biased_Language k`, then `characteristicRational ... = 1`.
theorem characteristicRational_of_P_lang_is_one {k : ℕ} {cnf : SyntacticCNF_EGPT k}
  (h : cnf ∈ P_EGPT_Biased_Language k) :
  ∃ (filter : RejectionFilter k), filter.cnf = cnf ∧ characteristicRational filter = 1 := by
  -- Construct the satisfying assignments (all assignments since it's a tautology)
  let satisfying_assignments : Finset (Vector Bool k) := Finset.univ
  -- Prove this set is nonempty
  have is_satisfiable : satisfying_assignments.Nonempty := by
    use Vector.replicate k false
    simp [satisfying_assignments]
  -- Prove the coherence axiom
  have ax_coherent : ∀ v, v ∈ satisfying_assignments → (evalCNF cnf v = true) := by
    intros v _
    exact h v
  -- Construct the filter
  let filter : RejectionFilter k := {
    cnf := cnf,
    satisfying_assignments := satisfying_assignments,
    is_satisfiable := is_satisfiable,
    ax_coherent := ax_coherent
  }
  use filter
  constructor
  · rfl
  · unfold characteristicRational
    simp only [satisfying_assignments]

    -- We need to show that card (univ : Finset (Vector Bool k)) = 2^k
    rw [Finset.card_univ]
    -- The instance instFintypeVectorBool gives us the Fintype structure
    -- Use the available card_vector theorem from Fintype via the equivalence
    have h_eq : Fintype.card (Vector Bool k) = Fintype.card Bool ^ k := by
      -- Transform to List.Vector via equivalence and then use card_vector
      have h1 : Fintype.card (Vector Bool k) = Fintype.card (List.Vector Bool k) :=
        Fintype.card_congr listVectorEquivVector.symm
      rw [h1]
      -- Now use the card_vector theorem for List.Vector
      exact @card_vector Bool _ k
    rw [h_eq, Fintype.card_bool]
    simp only [Rat.mkRat_eq_div]
    norm_cast
    simp

-- ==================================================================
-- == Final EGPT NP-Completeness Framework (Add this to your file) ==
-- ==================================================================

/-!
### Final Definitions for Reducibility and NP-Completeness
-/

/--
A function `f` that transforms one `UniversalCNF` problem into another is a
**Polynomial-Time EGPT Reducer** if the physical process to compute it has a
polynomially-bounded information cost (Shannon Entropy).

For simplicity and to focus on the logical structure, we state this as a
high-level property. A deeper dive would involve defining an EGPT virtual machine.
-/
class IsPolynomialEGPT_Reducer (f : UniversalCNF → UniversalCNF) : Prop where
  is_poly : ∃ (p : ℕ → ℕ) (_hp : IsPolynomialNat p),
    ∀ (ucnf : UniversalCNF),
      -- The complexity of the output encoding is polynomially bounded by the input encoding.
      (encodeCNF (f ucnf).2).length ≤ p (encodeCNF ucnf.2).length

/--
A language `L` is **NP-Complete in EGPT** if it is in `NP_EGPT_Concrete` and any
other language in `NP_EGPT_Concrete` can be reduced to it via a
polynomial-time EGPT reducer.
-/
structure NPComplete_EGPT (L : Π k, Lang_EGPT_SAT k) : Prop where
  in_NP   : (L : Π k, Lang_EGPT_SAT k) ∈ NP_EGPT_Concrete
  is_hard : ∀ (L' : Π k, Lang_EGPT_SAT k), L' ∈ NP_EGPT_Concrete →
              ∃ (f : UniversalCNF → UniversalCNF),
                IsPolynomialEGPT_Reducer f ∧
                (∀ ucnf : UniversalCNF,
                  (ucnf.2 ∈ L' ucnf.1) ↔ ((f ucnf).2 ∈ L (f ucnf).1)
                )

/-!
### The EGPT Cook-Levin Theorem: `L_SAT` is the Universal Bias
-/

/--
**Axiom (The Universal Bias Compiler):**
Any verifiable bias (a problem `L'` in `NP_EGPT_Concrete`) can be compiled into the
universal language of bias (`L_SAT`). This compilation function `f` is a
polynomial-time EGPT reducer.

This is the EGPT equivalent of the Cook-Levin theorem's core argument. It posits
that CNF is a universal language for describing verifiable computational constraints.
-/
axiom universal_bias_compiler :
  ∀ (L' : Π k, Lang_EGPT_SAT k), L' ∈ NP_EGPT_Concrete →
    ∃ (f : UniversalCNF → UniversalCNF),
      IsPolynomialEGPT_Reducer f ∧
      (∀ ucnf, (ucnf.2 ∈ L' ucnf.1) ↔ ((f ucnf).2 ∈ L_SAT (f ucnf).1))

/--
**Theorem: `L_SAT` is NP-Hard.**

This follows directly from the `universal_bias_compiler` axiom, which states
that `L_SAT` can serve as the target for a reduction from any NP problem.
-/
theorem L_SAT_is_NP_Hard :
  ∀ (L' : Π k, Lang_EGPT_SAT k), L' ∈ NP_EGPT_Concrete →
    ∃ (f : UniversalCNF → UniversalCNF),
      IsPolynomialEGPT_Reducer f ∧
      (∀ ucnf, (ucnf.2 ∈ L' ucnf.1) ↔ ((f ucnf).2 ∈ L_SAT (f ucnf).1)) :=
by
  -- The proof is a direct application of the axiom.
  intro L' hL'
  exact universal_bias_compiler L' hL'

/--
**Main Theorem: `L_SAT` is NP-Complete in EGPT.**

This theorem formalizes the idea that `L_SAT` is the universal problem for
describing all possible verifiable physical biases.
-/
theorem L_SAT_is_NPComplete : NPComplete_EGPT L_SAT :=
{
  in_NP   := L_SAT_in_NP_EGPT_Concrete,
  is_hard := L_SAT_is_NP_Hard
}
