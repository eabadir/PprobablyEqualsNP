import Mathlib.Tactic.NormNum

import Mathlib.Data.Sym.Card
import Std.Sat.CNF.Basic
import Mathlib.Tactic.Sat.FromLRAT

import Mathlib.Data.List.Range
import Mathlib.Data.List.FinRange

import EGPT.NumberTheory.Core
import EGPT.Core
import EGPT.Complexity.Core
import EGPT.NumberTheory.Filter
namespace EGPT.Complexity

open EGPT.NumberTheory.Core EGPT.Complexity EGPT.NumberTheory.Filter

/-!
## EGPT COMPLEXITY CLASSES
This section defines P and NP based on the concrete computational
model established in Phase 1.
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
