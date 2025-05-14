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


noncomputable def at_most_k_CNF_def (k : ℕ) : Std.Sat.CNF V :=
  if _h_card_V_le_k : Fintype.card V ≤ k then
    []
  else
    let subsets_k_plus_1 := univ (α := V).powerset.filter (fun s => s.card = k + 1)
    subsets_k_plus_1.toList.map (fun s => s.toList.map (fun v => (v, false))) -- (v, false) is the negative literal ¬v

-- Assuming Std.Sat.Literal α is α × Bool (true for positive polarity)
-- and Std.Sat.Literal.negate l is (l.1, !l.2)

-- Local definition for Literal.eval for clarity in proofs.
-- If Std.Sat.Literal has its own `eval` with this meaning, this can be replaced.
@[local simp]
def LocalLiteralEval (l : Std.Sat.Literal V) (assignment : V → Bool) : Bool :=
  assignment l.1 = l.2

-- Lemmata for direction -> (CNF eval true => card_true <= k)
section ImpliesLe

variable (k : ℕ) (assignment : V → Bool)
variable (h_k_lt_card_V : k < Fintype.card V) -- k < |V|
variable (h_card_true_gt_k : Fintype.card { v : V // assignment v = true } > k)
variable [Fintype α] [DecidablePred p]


lemma exists_k_plus_1_subset_of_true_vars :
    ∃ (s : Finset V), s.card = k + 1 ∧ ∀ v ∈ s, assignment v = true := by
  let S_true_finset := Finset.univ.filter (fun v => assignment v = true)
  have h_k_plus_1_le_S_true_card : k + 1 ≤ S_true_finset.card := by
    rw [Fintype.card_subtype (fun v => assignment v = true)] at h_card_true_gt_k
    exact Nat.succ_le_of_lt h_card_true_gt_k
  obtain ⟨s, hs_subset_S_true, hs_card⟩ :=
    Finset.exists_subset_card_eq h_k_plus_1_le_S_true_card -- s is a subset of S_true_finset
  use s
  constructor
  · exact hs_card
  · intro v hv_in_s
    exact (mem_filter.mp (hs_subset_S_true hv_in_s)).2

lemma k_plus_1_set_forms_clause_in_at_most_k_CNF (s : Finset V) (hs_card : s.card = k + 1) :
    (s.toList.map (fun v => (v, false))) ∈ (at_most_k_CNF_def k : Std.Sat.CNF V) := by
  simp only [at_most_k_CNF_def, h_k_lt_card_V, dite_false]
  apply List.mem_map_of_mem
  · simp only [mem_toList, mem_filter, univ_powerset_self, Finset.mem_univ, true_and]
    exact hs_card

end ImpliesLe
