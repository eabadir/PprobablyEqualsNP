import EGPT.NumberTheory.Core
import EGPT.NumberTheory.Filter
import EGPT.Complexity.Core
import EGPT.Constraints
import EGPT.Complexity.PPNP
import Mathlib.Probability.Distributions.Uniform
namespace EGPT.Analysis

open EGPT.Constraints  EGPT.NumberTheory.Core EGPT.NumberTheory.Filter EGPT.Complexity
open PMF Finset


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
  List.concat (c.map (fun l => encodeLiteral l ++ [false]))

/--
**The Universal CNF Encoder.**

Encodes a `SyntacticCNF_EGPT k` into a single `ComputerTape`.
The format is: `unary(k) ++ [F,F] ++ encoded_clauses`.
A double `false` separates `k` from the body, and clauses are also
separated by a double `false`.
-/
def encodeCNF {k : ℕ} (cnf : SyntacticCNF_EGPT k) : ComputerTape :=
  encodeNat k ++ [false, false] ++ List.concat (cnf.map (fun c => encodeClause c ++ [false, false]))

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

/--
**The New Provable Equivalence.**
This defines a computable bijection from the space of all possible CNF formulas
(over any number of variables) to the natural numbers, and thus to `ParticlePath`.
-/
noncomputable def equivUniversalCNF_to_ParticlePath : UniversalCNF ≃ ParticlePath :=
  (Encodable.equivEncodable _).trans (equivParticlePathToNat.symm)

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


/--
A function `f` from `SyntacticCNF_EGPT k` to `SyntacticCNF_EGPT k` is **polynomial in EGPT**
if the equivalent function on `ParticlePath` (obtained by encoding the input and decoding the output)
is polynomial according to `IsPolynomialEGPT`.
-/
class IsPolynomialEGPT_on_SyntacticCNF {k : ℕ} (f : SyntacticCNF_EGPT k → SyntacticCNF_EGPT k) : Prop :=
  poly : IsPolynomialEGPT (equivSyntacticCNF_to_ParticlePath ∘ f ∘ equivSyntacticCNF_to_ParticlePath.symm)


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
    a `ParticlePMF`, using the `fromRat` bijection.
3.  The underlying `List Bool` of the `ParticlePMF` is, by definition, the
    canonical `ComputerTape` or "program" for that rational.
-/
noncomputable def EGPTProgramForRejectionFilter {k : ℕ} (filter : RejectionFilter k) : ComputerTape :=
  -- 1. Calculate the characteristic rational of the filter.
  let prob_success : ℚ := characteristicRational filter
  -- 2. Convert this rational number into its canonical EGPT representation.
  let egpt_rational : ParticlePMF := fromRat prob_success
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



variable {k : ℕ}

/--
A language `L` is **NP-Complete in EGPT** if it is in `NP_EGPT` and every
other language in `NP_EGPT` can be reduced to it in polynomial time.
-/
structure NPComplete_EGPT (L : Π k, Lang_EGPT_SAT k) : Prop where
  /-- The language must have a polynomial-time verifier. -/
  in_NP : L ∈ NP_EGPT
  /-- Every other NP language must be polynomially reducible to this language. -/
  is_hard : ∀ (L' : Π k, Lang_EGPT_SAT k), L' ∈ NP_EGPT → ∃ (f : SyntacticCNF_EGPT k → SyntacticCNF_EGPT k) (_h_poly_f : IsPolynomialEGPT_on_SyntacticCNF f), -- Use the new typeclass
    (∀ (cnf : SyntacticCNF_EGPT k), (cnf ∈ L' k) ↔ (f cnf ∈ L k))

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

/--
Theorem: `L_SAT` is in `NP_EGPT`.

**Proof:** We must show there is a deterministic, polynomial-time verifier for `L_SAT`.
The verifier is `DMachine_SAT_verify` (which is just `evalCNF`). The certificate is
the satisfying assignment itself. The runtime of `evalCNF` is polynomial in the
size of the CNF formula.
-/
theorem L_SAT_in_NP_EGPT : (L_SAT : Π k, Lang_EGPT_SAT k) ∈ NP_EGPT := by
  -- 1. Unfold the definition of `NP_EGPT`.
  unfold NP_EGPT Lang_EGPT_SAT
  -- 2. We need to provide a polynomial bound for the certificate size.
  --    The certificate is a `Vector Bool k`. Its size is `k`.
  --    The input is a `SyntacticCNF_EGPT k`.
  --    We need a polynomial `p` such that `(encode (cert : Vector Bool k)).size ≤ (p (encode (input : SyntacticCNF_EGPT k))).size`.
  --    The size of `encode (Vector Bool k)` is `k`.
  --    The size of `encode (input : SyntacticCNF_EGPT k)` is the size of the encoded CNF.
  --    We need to show that `k` is polynomially bounded by the size of the encoded CNF.
  --    This requires a specific encoding scheme where the number of variables `k` is part of the input size.
  --    Assuming such an encoding, the identity function `id` on `ParticlePath` might work as the polynomial bound `p`.
  --    Let's use `id` for now, but the `sorry` for the size bound needs to be addressed properly later based on the encoding.
  use (fun (p : ParticlePath) => p) -- The identity function as the polynomial bound p
  constructor
  · -- Proof of the core equivalence: input ∈ L_SAT k ↔ ∃ cert, (encode cert).size ≤ (p (encode input)).size ∧ DMachine_SAT_verify input cert = true
    intro k input
    unfold L_SAT
    -- Goal: `(∃ a : Vector Bool k, evalCNF input a = true) ↔ (∃ c : Certificate k, (encode c).size ≤ (encode input).size ∧ DMachine_SAT_verify input c = true)`
    -- Note: `Certificate k` is `Vector Bool k`. `DMachine_SAT_verify input c` is `evalCNF input c`.
    -- Goal: `(∃ a : Vector Bool k, evalCNF input a = true) ↔ (∃ c : Vector Bool k, (encode c).size ≤ (encode input).size ∧ evalCNF input c = true)`
    apply Iff.intro
    · -- Forward direction: (∃ a, evalCNF input a) → (∃ c, ...)
      intro h_exists_a
      rcases h_exists_a with ⟨assignment, h_eval⟩
      use assignment -- The certificate is the assignment.
      constructor
      · -- Prove the size bound: (encode assignment).size ≤ (encode input).size
        -- (encode (Vector Bool k)).size is k.
        -- We need to show k ≤ (encode input).size. This depends on the encoding of SyntacticCNF_EGPT k.
        -- A typical encoding includes the number of variables k.
        -- Use the axiom `encoding_size_ge_k`.
        simp only [Vector.size, encode] -- `(encode (Vector Bool k)).size` simplifies to `k`
        exact encoding_size_ge_k k input
      · -- Prove the verifier accepts: evalCNF input assignment = true
        exact h_eval
    · -- Backward direction: (∃ c, ...) → (∃ a, evalCNF input a)
      intro h_exists_c
      rcases h_exists_c with ⟨certificate, _, h_verify⟩
      -- We don't need the size bound `_` here for the existence part.
      use certificate
      exact h_verify
  · -- Proof that the chosen polynomial bound `p` (which is `id`) is polynomial.
    exact IsPolynomialEGPT.id

/-!
### Part 2: Proving `L_SAT` is NP-Hard (The EGPT Cook-Levin Theorem)
-/

/--
**Axiom (The EGPT Compiler Postulate):**
Any EGPT verifier program `V` (a `DMachine`) can be compiled in polynomial time
into an equivalent `SyntacticCNF_EGPT`.

This axiom captures the standard result from computer science that any
polynomial-time computation can be "unrolled" into a polynomial-size Boolean
circuit, which can then be converted to a CNF formula.

The compiler takes the verifier function and the polynomial certificate size bound
from the definition of an NP language, and produces a polynomial-time computable
function `compiler_func` that maps inputs to the verifier into equivalent CNF formulas.
The resulting CNF is satisfiable if and only if the original verifier accepts
the input for some certificate *within the specified polynomial size bound*.
-/
axiom verifier_to_cnf_compiler (k : ℕ)
  (verifier_prog : Certificate k → EGPT_SAT_Input k → Bool)
  (poly_bound : ParticlePath → ParticlePath) : -- The polynomial bound on certificate size
  ∃ (compiler_func : EGPT_SAT_Input k → SyntacticCNF_EGPT k),
    (_h_poly_compiler : IsPolynomialEGPT_on_SyntacticCNF compiler_func) ∧ -- The compiler function is polynomial
    (∀ (input : EGPT_SAT_Input k), -- The core equivalence for the reduction
      ((∃ c : Certificate k, (encode c).size ≤ (poly_bound (encode input)).size ∧ verifier_prog c input = true) ↔
       (∃ a : Certificate k, evalCNF (compiler_func input) a = true))) -- Satisfiability of the output CNF

/--
**Theorem (The EGPT Cook-Levin Theorem): `L_SAT` is NP-Hard.**

**Proof:** We must show that any language `L' ∈ NP_EGPT` can be reduced to `L_SAT`.
The reduction function `f` is the `compiler_func` provided by the `verifier_to_cnf_compiler` axiom.
-/
theorem L_SAT_is_NP_Hard_EGPT :
  ∀ (L' : Π k, Lang_EGPT_SAT k), L' ∈ NP_EGPT → ∃ (f : SyntacticCNF_EGPT k → SyntacticCNF_EGPT k) (_h_poly_f : IsPolynomialEGPT_on_SyntacticCNF f), -- Use the new typeclass
    (∀ (cnf : SyntacticCNF_EGPT k), (cnf ∈ L' k) ↔ (f cnf ∈ L_SAT k)) :=
by
  -- 1. Let L' be any language in NP_EGPT.
  intro L' h_L'_in_NP
  -- 2. By definition of NP_EGPT, there exists a polynomial-time verifier for L'
  --    and a polynomial bound on the certificate size.
  rcases h_L'_in_NP with ⟨poly_bound, h_poly_bound, h_verify_equiv⟩

  -- 3. We now use our compiler axiom. The verifier for L' is `fun cert input => DMachine_SAT_verify input cert`.
  --    Apply the compiler axiom to this verifier and the polynomial bound from L'.
  let verifier_for_L' := fun (cert : Certificate k) (input : EGPT_SAT_Input k) => DMachine_SAT_verify input cert
  specialize (verifier_to_cnf_compiler k verifier_for_L' poly_bound)
  rcases (verifier_to_cnf_compiler k verifier_for L' poly_bound) with ⟨compiler_func, h_poly_compiler, h_equiv_compiler⟩

  -- 4. Let f be the compiler function. This is our reduction function.
  let f := compiler_func
  use f

  -- 5. Prove that this function f is polynomial on SyntacticCNF_EGPT k.
  --    This comes directly from the compiler axiom.
  use h_poly_compiler

  -- 6. Prove the core reduction equivalence: `cnf ∈ L' k ↔ f cnf ∈ L_SAT k`.
  intro cnf
  -- Unfold L_SAT for the right side of the equivalence.
  unfold L_SAT

  -- The goal is now:
  -- `(cnf ∈ L' k) ↔ (∃ a, evalCNF (f cnf) a = true)`

  -- From the definition of L' ∈ NP_EGPT (h_verify_equiv):
  -- `cnf ∈ L' k` is equivalent to `(∃ c : Certificate k, (encode c).size ≤ (poly_bound (encode cnf)).size ∧ DMachine_SAT_verify cnf c = true)`
  specialize h_verify_equiv k cnf

  -- From the compiler axiom (h_equiv_compiler):
  -- `(∃ c : Certificate k, (encode c).size ≤ (poly_bound (encode cnf)).size ∧ DMachine_SAT_verify cnf c = true)` is equivalent to `(∃ a : Certificate k, evalCNF (f cnf) a = true)`
  specialize h_equiv_compiler cnf

  -- Combine the two equivalences.
  exact Iff.trans h_verify_equiv h_equiv_compiler

/--
**Main Theorem: `L_SAT` is NP-Complete in EGPT.**
-/
theorem L_SAT_is_NPComplete_EGPT : NPComplete_EGPT L_SAT :=
{
  in_NP := L_SAT_in_NP_EGPT,
  is_hard := L_SAT_is_NP_Hard_EGPT
}
