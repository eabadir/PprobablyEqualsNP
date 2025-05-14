import Mathlib.Data.Sym.Card
import Std.Sat.CNF.Basic
import Mathlib.Tactic.Sat.FromLRAT
--import Std.Data.List.Lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic -- For Fintype (Fin n) if needed, though usually direct
import Mathlib.Logic.Equiv.Defs -- For Equiv

import PPNP.Complexity.Program
import PPNP.Common.Basic
-- import PPNP.Entropy.Common
-- import PPNP.Entropy.Physics.Common
-- import PPNP.Entropy.RET
-- import PPNP.Entropy.Physics.UniformSystems

namespace PPNP.Entropy.Physics.PhysicsDist

open Multiset NNReal Finset Function -- Added Function for comp_apply

open Multiset NNReal
open PPNP.Common
open PPNP.Complexity.Program
-- open PPNP.Entropy.Common
-- open PPNP.Entropy.Physics.Common
-- open PPNP.Entropy.Physics.UniformSystems
-- open PPNP.Entropy.RET


open Std.Sat -- For CNF, Literal, Clause, etc.
open Sat
open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem card_subtype_eq_card_filter : Fintype.card {x : α // p x} = (univ.filter p).card :=
  Fintype.card_of_subtype (univ.filter p) (by simp)

-- Assuming Std.Sat.Literal α is α × Bool (true for positive polarity)
-- and Std.Sat.Literal.negate l is (l.1, !l.2)

-- Local definition for Literal.eval if not provided by Std.Sat or if its definition is opaque.
-- This definition aligns with the common interpretation.
@[local simp]
def LocalLiteralEval (l : Std.Sat.Literal V) (assignment : V → Bool) : Bool :=
  assignment l.1 = l.2

def Clause (V : Type u) := List (Std.Sat.Literal V)
-- Local definition for Clause.eval if not provided by Std.Sat or if its definition is opaque.

def LocalClauseEval (cl : Clause V) (assignment : V → Bool) : Bool :=
  List.any cl (fun l => LocalLiteralEval l assignment)

-- Local definition for CNF.eval if not provided by Std.Sat or if its definition is opaque.
def LocalCNFEval (cnf : Std.Sat.CNF V) (assignment : V → Bool) : Bool :=
  List.all cnf (fun cl => LocalClauseEval cl assignment)

-- We will use these local definitions for now. If Std.Sat provides them with the same semantics,
-- these local versions can be removed and Std.Sat's versions used directly.
-- The proofs below will rely on these specific semantics (e.g., List.any/all).
-- Definition of at_most_k_CNF using Std.Sat.Literal
noncomputable def at_most_k_CNF_def (k : ℕ) : CNF V :=
  if _h_card_V_le_k : Fintype.card V ≤ k then
    []
  else
    let subsets_k_plus_1 := univ (α := V).powerset.filter (fun s => s.card = k + 1)
    subsets_k_plus_1.toList.map (fun s => s.toList.map (fun v => (v, false))) -- (v, false) is the negative literal ¬v

-- Helper: Clause.eval is true iff there exists a literal in it that evaluates to true.
lemma local_clause_eval_iff_exists_literal_eval_true (cl : Clause V) (assignment : V → Bool) :
    LocalClauseEval cl assignment ↔ ∃ l ∈ cl, LocalLiteralEval l assignment := by
  simp [LocalClauseEval, List.any_eq_true]

-- -- Helper: CNF.eval is true iff all its clauses evaluate to true.
-- lemma local_cnf_eval_iff_forall_clauses_eval_true (cnf : CNF V) (assignment : V → Bool) :
--     LocalCNFEval cnf assignment ↔ ∀ cl ∈ cnf, LocalClauseEval cl assignment := by
--   simp [LocalCNFEval, List.all_iff_forall]




-- Lemmata for direction -> (CNF eval true => card_true <= k)
section ImpliesLe

variable (k : ℕ) (assignment : V → Bool)
variable (h_k_lt_card_V : k < Fintype.card V) -- k < |V|
variable (h_card_true_gt_k : Fintype.card { v : V // assignment v = true } > k)

lemma exists_k_plus_1_subset_of_true_vars :
    ∃ (s : Finset V), s.card = k + 1 ∧ ∀ v ∈ s, assignment v = true := by
  let S_true_finset := univ.filter (fun v => assignment v = true)
  have h_S_true_card : S_true_finset.card = Fintype.card { v : V // assignment v = true } :=
    (Fintype.card_subtype_eq_card_filter univ (fun v => assignment v = true)).symm
  rw [h_S_true_card] at h_card_true_gt_k
  have h_k_plus_1_le_S_true_card : k + 1 ≤ S_true_finset.card := Nat.succ_le_of_lt h_card_true_gt_k
  obtain ⟨s, hs_subset_S_true, hs_card⟩ :=
    Finset.exists_subset_card_eq h_k_plus_1_le_S_true_card -- s is a subset of S_true_finset
  use s
  constructor
  · exact hs_card
  · intro v hv_in_s
    exact (mem_filter.mp (hs_subset_S_true hv_in_s)).2

lemma k_plus_1_set_forms_clause_in_at_most_k_CNF (s : Finset V) (hs_card : s.card = k + 1) :
    (s.toList.map (fun v => (v, false))) ∈ (at_most_k_CNF_def k : CNF V) := by
  simp only [at_most_k_CNF_def, h_k_lt_card_V, dite_false] -- Use `dite_false` as h_k_lt_card_V means ¬(Fintype.card V ≤ k)
  apply List.mem_map_of_mem
  · simp only [mem_toList, mem_filter, univ_powerset_self, Finset.mem_univ, true_and]
    exact hs_card

lemma clause_from_k_plus_1_true_vars_evals_false (s : Finset V) -- (hs_card : s.card = k + 1) -- Not strictly needed for this lemma if s is just a set of vars
    (h_all_vars_true : ∀ v ∈ s, assignment v = true) :
    ¬ LocalClauseEval (s.toList.map (fun v => (v, false))) assignment := by
  rw [local_clause_eval_iff_exists_literal_eval_true]
  push_neg -- After push_neg, goal is: ∀ l ∈ (s.toList.map (fun v => (v,false))), ¬LocalLiteralEval l assignment
  intro l hl_in_clause_list
  simp only [LocalLiteralEval] -- Unfold local eval
  -- l is of the form (v, false) where v ∈ s.toList
  rw [List.mem_map] at hl_in_clause_list
  obtain ⟨v_orig, hv_orig_in_s_toList, heq_l⟩ := hl_in_clause_list
  rw [←heq_l] -- l is now (v_orig, false)
  -- Goal: ¬ (assignment v_orig = false)
  rw [Bool.eq_false_iff_not] -- Goal: ¬ ¬ (assignment v_orig)  which is (assignment v_orig)
  have hv_orig_in_s : v_orig ∈ s := List.mem_toFinset.mp hv_orig_in_s_toList
  exact h_all_vars_true v_orig hv_orig_in_s

end ImpliesLe


-- Lemmata for direction <- (card_true <= k => CNF eval true)
section LeImplies

variable (k : ℕ) (assignment : V → Bool)
variable (h_k_lt_card_V : k < Fintype.card V)
variable (h_card_true_le_k : Fintype.card { v : V // assignment v = true } ≤ k)

lemma at_least_one_var_false_in_k_plus_1_set (s : Finset V) (hs_card : s.card = k + 1) :
    ∃ v ∈ s, ¬(assignment v) := by
  by_contra h_all_true_in_s_contra
  push_neg at h_all_true_in_s_contra -- h_all_true_in_s_contra : ∀ v ∈ s, assignment v = true
  let S_true_finset := univ.filter (fun v => assignment v = true)
  have h_S_true_card : S_true_finset.card = Fintype.card { v : V // assignment v = true } :=
    (Fintype.card_subtype_eq_card_filter univ (fun v => assignment v = true)).symm

  have h_s_subset_S_true : s ⊆ S_true_finset := by
    intro v hv_in_s
    simp only [mem_filter, mem_univ, true_and, h_all_true_in_s_contra v hv_in_s]
  have card_s_le_card_S_true := Finset.card_le_of_subset h_s_subset_S_true
  rw [hs_card, h_S_true_card] at card_s_le_card_S_true
  -- card_s_le_card_S_true is k+1 <= Fintype.card { v // assignment v = true }
  linarith -- {h_card_true_le_k, card_s_le_card_S_true} should be a contradiction (k+1 <= X and X <= k)

lemma clause_from_k_plus_1_set_evals_true_if_one_var_false (s_finset : Finset V) -- Finset for clarity
    (h_exists_false_in_finset : ∃ v ∈ s_finset, ¬(assignment v)) :
    LocalClauseEval (s_finset.toList.map (fun v => (v, false))) assignment := by
  rw [local_clause_eval_iff_exists_literal_eval_true]
  obtain ⟨v_false, hv_false_mem_s_finset, h_assign_v_false_is_not_true⟩ := h_exists_false_in_finset
  -- We need to show ∃ l ∈ s_finset.toList.map (fun v => (v,false)), LocalLiteralEval l assignment
  -- Our target literal l is (v_false, false)
  use (v_false, false)
  constructor
  · apply List.mem_map_of_mem -- Show (v_false, false) is in the list of literals
    exact List.mem_toFinset.mpr hv_false_mem_s_finset -- v_false is in s_finset.toList
  · simp [LocalLiteralEval, Bool.eq_false_iff_not]
    exact h_assign_v_false_is_not_true

end LeImplies

-- Reassembling the main proof for at_most_k_CNF
lemma eval_at_most_k_CNF_def_iff (k : ℕ) (assignment : V → Bool) :
    LocalCNFEval (at_most_k_CNF_def k : CNF V) assignment ↔ Fintype.card { v // assignment v = true } ≤ k := by
  simp only [at_most_k_CNF_def]
  by_cases h_card_V_le_k : Fintype.card V ≤ k
  · -- Case 1: Fintype.card V ≤ k. CNF is [], which is true.
    -- And Fintype.card { v // assignment v = true } ≤ Fintype.card V ≤ k is true.
    simp only [h_card_V_le_k, dite_true, local_cnf_eval_iff_forall_clauses_eval_true]
    rw [List.forall_mem_nil] -- forall P x, x ∈ [] → P x is true
    exact le_trans (Fintype.card_subtype_le _) h_card_V_le_k
  · -- Case 2: k < Fintype.card V.
    simp only [h_card_V_le_k, dite_false, local_cnf_eval_iff_forall_clauses_eval_true]
    have h_k_lt_card_V : k < Fintype.card V := Nat.lt_of_not_le h_card_V_le_k

    apply Iff.intro
    · -- Direction -> (CNF eval true => card_true <= k)
      intro h_all_clauses_eval_true
      by_contra h_card_true_gt_k_local
      -- h_card_true_gt_k_local is Fintype.card {v // assignment v = true} > k
      push_neg at h_card_true_gt_k_local -- if it was a negation

      obtain ⟨s_true_subset, hs_card, hs_all_true⟩ :=
        exists_k_plus_1_subset_of_true_vars k assignment h_k_lt_card_V h_card_true_gt_k_local
      let clause_of_s := s_true_subset.toList.map (fun v => (v, false))

      have h_clause_s_in_CNF_list : clause_of_s ∈
        (((univ (α := V)).powerset.filter (fun s_iter => s_iter.card = k + 1)).toList.map
          (fun s_iter => s_iter.toList.map (fun v => (v, false)))) :=
        k_plus_1_set_forms_clause_in_at_most_k_CNF k h_k_lt_card_V s_true_subset hs_card

      have h_clause_s_should_eval_true : LocalClauseEval clause_of_s assignment :=
         h_all_clauses_eval_true clause_of_s h_clause_s_in_CNF_list

      have h_clause_s_actually_evals_false : ¬ LocalClauseEval clause_of_s assignment :=
        clause_from_k_plus_1_true_vars_evals_false k assignment s_true_subset hs_all_true
      exact h_clause_s_actually_evals_false h_clause_s_should_eval_true

    · -- Direction <- (card_true <= k => CNF eval true)
      intro h_card_true_le_k_local
      intro clause_C h_C_in_generated_list_of_clauses
      -- clause_C is of the form s.toList.map (fun v => (v, false)) where s.card = k+1
      obtain ⟨s_finset_source, hs_filter_props, hs_C_eq_representation⟩ :=
        List.mem_map.mp h_C_in_generated_list_of_clauses
      rw [←hs_C_eq_representation] -- Now clause_C is s_finset_source.toList.map (fun v => (v, false))

      simp only [mem_filter, univ_powerset_self, mem_univ, true_and] at hs_filter_props
      have hs_card : s_finset_source.card = k + 1 := hs_filter_props.2

      obtain ⟨v_false, hv_false_in_s_finset, h_assign_v_false_is_not_true⟩ :=
        at_least_one_var_false_in_k_plus_1_set k assignment h_k_lt_card_V h_card_true_le_k_local s_finset_source hs_card

      apply clause_from_k_plus_1_set_evals_true_if_one_var_false (s_finset_source)
      use v_false; constructor
      · exact hv_false_in_s_finset
      · exact h_assign_v_false_is_not_true
