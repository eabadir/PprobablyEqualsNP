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

import PPNP.Common.Basic
import PPNP.Entropy.Common
import PPNP.Entropy.Physics.Common
import PPNP.Entropy.RET
import PPNP.Entropy.Physics.UniformSystems
import PPNP.Complexity.Program
import PPNP.Entropy.Physics.PhysicsDist
import PPNP.Entropy.Physics.BoseEinstein
import PPNP.Entropy.Physics.PhotonicCA

open Multiset NNReal Finset Function Real -- Added Function for comp_apply

open Multiset NNReal
open PPNP.Common
open PPNP.Complexity.Program
open PPNP.Entropy.Common
open PPNP.Entropy.Physics.Common
open PPNP.Entropy.Physics.UniformSystems
open PPNP.Entropy.Physics.PhysicsDist
open PPNP.Entropy.RET
open PPNP.Entropy.Physics.BE
open PPNP.Entropy.Physics.PCA



/-!
##  Random Walks, CAPrograms, System Evolution, and BE Snapshots

This proof sketch lays out that every time t, there is a computer program which exists which gives the exact state (position, etc.) of the photons, since, at every time t that state is characterised by the BoseEinstein distribution. The proof leverages programs for individual random walks (CAProgram) and
for a system of multiple random walks (SystemEvolutionProgram).
It then connects snapshots of the system's evolution to the Bose-Einstein
encoding program previously defined.
-/

/--
Theorem: A snapshot of an evolving system of `n` random walks at time `t_snapshot`
can be characterized by a Bose-Einstein distribution, which in turn can be
encoded by a `ClassicalComputerProgram` (prog_snapshot_BE). In computational terms, this is our "verifier" or "witness" program.

The `SystemEvolutionProgram` (tape `n*T`) determines the state of all walks.
A snapshot of this state (e.g., number of heads per walk `(h_1, ..., h_n)`)
can be viewed as a BE microstate.
`encoding_BE_system_by_program` shows that *this specific BE microstate* can be
encoded by a program `prog_snapshot_BE` whose tape length is `ceil(log2(num_BE_microstates))`.
The length of `prog_snapshot_BE.tape` is generally different from `SystemEvolutionProgram.tape.length`.
-/
theorem system_snapshot_encodable_by_BE_program
    (sys_prog_eval_output : List RandomWalkPath) -- Output from SystemEvolutionProgram.eval
    (n_walks : ℕ) (t_snapshot : ℕ)
    (_h_paths_len : sys_prog_eval_output.length = n_walks)
    (_h_paths_non_empty_and_time_valid : n_walks > 0 → -- Avoids BE with N=0 if n_walks is 0
      ∀ path ∈ sys_prog_eval_output, t_snapshot < path.length) :
    -- Define N_BE and M_BE for the BE system at t_snapshot
    let N_BE := n_walks
    let M_BE := getTotalUpStepsAtSnapshot sys_prog_eval_output t_snapshot
    -- Condition for BE system to be valid (N_BE > 0 or M_BE = 0)
    if _h_N_BE_pos_or_M_BE_zero : N_BE > 0 ∨ M_BE = 0 then
        ∃ (prog_snapshot_BE : ClassicalComputerProgram) (src_BE : IIDFairBinarySource)
          (prog_BE_tape_len_nat : ℕ)
          (be_params : PPNP.Entropy.Physics.PhysicsDist.SystemParams)
          (_h_be_params_match : be_params.N = N_BE ∧ be_params.M = M_BE)
          (_h_axiomatic_entropy_BE :
            H_physical_system (p_UD_fin be_params.N be_params.M) =
              C_constant_real H_physical_system_has_Rota_entropy_properties * stdShannonEntropyLn (p_UD_fin be_params.N be_params.M)),
          prog_snapshot_BE.tape.length = prog_BE_tape_len_nat ∧
          src_BE.num_choices = prog_BE_tape_len_nat ∧
          (ClassicalComputerProgram.complexity prog_snapshot_BE : ℝ) = (prog_BE_tape_len_nat : ℝ) ∧
          (prog_BE_tape_len_nat : ℝ) = SCTOptimalTapeLength src_BE
    else
        True -- If BE parameters are not valid (e.g. N_BE=0 and M_BE > 0), the BE encoding doesn't apply in this form.
        := by
  let N_BE_val := n_walks
  let M_BE_val := getTotalUpStepsAtSnapshot sys_prog_eval_output t_snapshot

  -- If the condition for BE validity is met, proceed with the encoding proof
  by_cases h_N_BE_pos_or_M_BE_zero_cond : N_BE_val > 0 ∨ M_BE_val = 0
  · -- The BE system is valid, apply the existing theorem
    rw [dif_pos h_N_BE_pos_or_M_BE_zero_cond]
    let be_sys_params : PPNP.Entropy.Physics.PhysicsDist.SystemParams := { N := N_BE_val, M := M_BE_val }

    -- Create a hypothesis with the exact type expected by encoding_BE_system_by_program
    have h_valid_for_call : be_sys_params.N ≠ 0 ∨ be_sys_params.M = 0 := by
      -- Given: h_N_BE_pos_or_M_BE_zero_cond : N_BE_val > 0 ∨ M_BE_val = 0
      -- Given: be_sys_params.N is N_BE_val and be_sys_params.M is M_BE_val
      -- Goal: N_BE_val ≠ 0 ∨ M_BE_val = 0
      cases h_N_BE_pos_or_M_BE_zero_cond with
      | inl hN_pos => -- Case: N_BE_val > 0
        exact Or.inl (Nat.ne_of_gt hN_pos) -- Nat.ne_of_gt converts N_BE_val > 0 to N_BE_val ≠ 0
      | inr hM_zero => -- Case: M_BE_val = 0
        exact Or.inr hM_zero

    -- Now call the existing `encoding_BE_system_by_program` theorem
    -- It provides: ∃ (prog : ClassicalComputerProgram) (src : IIDFairBinarySource)
    --                (prog_tape_len_nat : ℕ)
    --                (_h_axiomatic_entropy_BE : H_phys ... = C * stdShannon...),
    --                prog.tape.length = prog_tape_len_nat ∧ ...
    rcases encoding_BE_system_by_program be_sys_params h_valid_for_call with
      ⟨prog_be, src_be, tape_len_be, h_ax_ent_be, h_tape_eq, h_src_eq, h_compl_eq, h_len_eq_sct⟩

    use prog_be
    use src_be
    use tape_len_be
    use be_sys_params
    --use by { constructor; exact rfl; exact rfl; } -- Proof for _h_be_params_match
    --use h_ax_ent_be
    -- The rest of the goals match the output of encoding_BE_system_by_program
    --exact ⟨h_tape_eq, h_src_eq, h_compl_eq, h_len_eq_sct⟩

  · -- The BE system is not valid (e.g. N_BE_val=0 and M_BE_val > 0), the `if` condition is false.
    -- The goal is `True` in this branch.
    rw [dif_neg h_N_BE_pos_or_M_BE_zero_cond]
    trivial
