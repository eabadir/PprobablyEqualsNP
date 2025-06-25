
import EGPT.Core
import EGPT.Complexity.Core
import EGPT.Entropy.Common
import EGPT.Physics.PhysicsDist
import EGPT.NumberTheory.Core -- For ParticlePath, fromNat, toNat
import EGPT.Complexity.Tableau -- For SatisfyingTableau, constructSatisfyingTableau
open EGPT EGPT.Complexity EGPT.NumberTheory.Core EGPT.Constraints EGPT.NumberTheory.Filter

namespace EGPT.Complexity.PPNP
/--
**The EGPT Universal Turing Machine (UTM) as a Universal Certifier.**

This function takes a problem description (`input_problem`) and transforms it
into a certified result. The "computation" it performs is the construction of a
`SatisfyingTableau` for one of the problem's valid solutions.

The function is `noncomputable` because it uses `Classical.choice` to select an
arbitrary solution from the non-empty set of satisfying assignments. This mirrors
the non-deterministic nature of finding a specific solution in a physical system.
-/
noncomputable def UniversalTuringMachine_EGPT {k : ℕ} (input_problem : RejectionFilter k) : RejectionFilter k :=
  -- 1. **Select a Witness:** From the input problem's proof that a solution
  --    exists (`is_satisfiable`), non-deterministically select one concrete
  --    satisfying assignment.
  let solution_witness := input_problem.is_satisfiable.choose
  have h_solution_in_set : solution_witness ∈ input_problem.satisfying_assignments :=
    input_problem.is_satisfiable.choose_spec

  -- 2. **Verify the Witness:** Use the input problem's coherence axiom to get a
  --    direct proof that this chosen witness satisfies the CNF constraints.
  have h_eval_true : evalCNF input_problem.cnf solution_witness = true :=
    input_problem.ax_coherent solution_witness h_solution_in_set

  -- 3. **Construct the Certificate:** Run the constructive `constructSatisfyingTableau`
  --    algorithm to generate the canonical EGPT certificate (the "proof of work")
  --    for this specific solution.
  let certified_solution := constructSatisfyingTableau input_problem.cnf ⟨solution_witness, h_eval_true⟩

  -- 4. **Construct the Certified Output:** Create and return a *new* `RejectionFilter`.
  --    This new filter represents the same problem (same `cnf` and same total set
  --    of `satisfying_assignments`), but its proof of existence is now explicitly
  --    and concretely tied to the certificate we just constructed.
  {
    cnf := input_problem.cnf,
    satisfying_assignments := input_problem.satisfying_assignments,

    -- The NEW proof of `is_satisfiable`:
    -- The witness for non-emptiness is now the assignment from our tableau.
    is_satisfiable := by
      use certified_solution.assignment
      -- We must prove this assignment is in the set of satisfying assignments.
      -- First, note that the assignment in the tableau is identical to the
      -- original `solution_witness` we started with.
      have h_assignment_is_witness : certified_solution.assignment = solution_witness := by
        rfl
      -- Now, substitute this back into the goal.
      rw [h_assignment_is_witness]
      -- The goal is now to prove `solution_witness ∈ satisfying_assignments`,
      -- which we already have as a hypothesis from step 1.
      exact h_solution_in_set,

    -- The coherence axiom remains the same, as the underlying sets have not changed.
    ax_coherent := input_problem.ax_coherent
  }
