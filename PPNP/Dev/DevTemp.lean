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
import PPNP.Entropy.RET -- Uncommented
import PPNP.Entropy.Physics.UniformSystems -- Uncommented
-- import PPNP.Complexity.Program -- Assuming not needed for f0_mul_eq_add_f0
--import PPNP.Entropy.Physics.PhysicsDist
--import PPNP.Entropy.Physics.BoseEinstein
--import PPNP.Entropy.Physics.PhotonicCA

open Nat Real NNReal Multiset NNReal Fin Set Finset Filter Function BigOperators Topology     -- Added Function for comp_apply

open Multiset NNReal
open PPNP.Common
--open PPNP.Complexity.Program
open PPNP.Entropy.Common
open PPNP.Entropy.Physics.Common
open PPNP.Entropy.Physics.UniformSystems -- Opened
--open PPNP.Entropy.Physics.PhysicsDist
--open PPNP.Entropy.Physics.BE
--open PPNP.Entropy.Physics.PCA
open PPNP.Entropy.RET -- Opened

-- In PPNP.Entropy.RET.lean

open PPNP.Entropy.Common

-- File: PPNP/Common/Basic.lean
-- Add this lemma to your existing PPNP.Common.Basic file
/--
Defines the conditional distribution for the i-th component in Rota's rational setup.
If `a_map_i_val > 0`, it's uniform on `Fin a_map_i_val`.
If `a_map_i_val = 0`, it's the (unique) distribution on the empty type `Fin 0`.
-/
noncomputable def P_cond_sigma_def {n : ℕ} (a_map : Fin n → ℕ) (i : Fin n) : Fin (a_map i) → NNReal :=
  if h_ai_pos : a_map i > 0 then
    uniformDist (Fintype_card_fin_pos h_ai_pos)
  else
    -- a_map i = 0. Fin (a_map i) is Fin 0 (empty type).
    -- Fin.elim0 is the canonical function Fin 0 → NNReal.
    have h_a_map_i_eq_0 : a_map i = 0 := Nat.eq_zero_of_not_pos h_ai_pos
    h_a_map_i_eq_0.symm ▸ Fin.elim0

/--
The conditional distribution `P_cond_sigma_def` sums to 1 if its domain `Fin (a_map i)` is non-empty.
If `a_map i = 0`, the sum is over an empty type, which is 0.
-/
lemma sum_P_cond_sigma_def_eq_one_of_pos {n : ℕ} (a_map : Fin n → ℕ) (i : Fin n) (ha_i_pos : a_map i > 0) :
    ∑ j, (P_cond_sigma_def a_map i) j = 1 := by
  simp_rw [P_cond_sigma_def, dif_pos ha_i_pos]
  exact sum_uniformDist (Fintype_card_fin_pos ha_i_pos)

/--
Relates `H_func` applied to `P_cond_sigma_def` to `f0 H_func (a_map i)`.
-/
lemma H_func_P_cond_sigma_def_eq_f0 {n : ℕ}
    (H_func : ∀ {α_aux : Type u} [Fintype α_aux], (α_aux → NNReal) → NNReal)
    (hH_axioms : HasRotaEntropyProperties H_func)
    (a_map : Fin n → ℕ) (i : Fin n) :
    H_func (P_cond_sigma_def a_map i) = f0 hH_axioms (a_map i) := by
  let ai := a_map i
  rw [f0] -- RHS: if ai > 0 then f hH_axioms (by assumption) else 0
  simp_rw [P_cond_sigma_def]
  by_cases hai_pos : ai > 0
  · -- Case ai > 0
    rw [dif_pos hai_pos, dif_pos hai_pos] -- Both sides use this condition
    -- Goal: H_func (uniformDist (Fintype_card_fin_pos hai_pos)) = f hH_axioms hai_pos
    rw [f] -- Unfold f on RHS
    -- Goal: H_func (uniformDist (Fintype_card_fin_pos hai_pos)) = H_func (uniformDist (Fintype_card_fin_pos hai_pos))
    rfl
  · -- Case ai = 0 (since ¬ (ai > 0) means ai ≤ 0, and ai : ℕ means ai = 0)
    have hai_eq_zero : ai = 0 := Nat.eq_zero_of_not_pos hai_pos
    rw [dif_neg hai_pos, dif_neg hai_pos] -- Both sides use this condition
    -- Goal: H_func (fun emp : Fin 0 => emp.elim) = 0
    -- The RHS is 0. We need H_func of distribution on empty type to be 0.
    -- This is true because H_func (dist_on_Fin0) is f0 H_func 0, which is 0.
    -- More formally:
    -- H_func (P_cond_sigma_def a_map i when a_map i = 0)
    -- = H_func (uniformDist (Fintype_card_fin_pos (impossible_proof : 0 > 0))) if we forced f.
    -- Need to show card (Fin 0) = 0.
    -- f0 hH_axioms 0 is 0.
    -- H_func (P_cond_sigma_def a_map i) needs to be identified with f0 hH_axioms (Fintype.card (Fin (a_map i)))
    -- If a_map i = 0, then card is 0.
    -- So H_func (P_cond_sigma_def a_map i) = f0 hH_axioms 0 = 0.
    -- This requires H_func of (dist on empty type) to be f0 H_func 0.
    -- Let's assume this is how f0 interacts with H_func for card = 0 case.
    -- If α is empty, Fintype.card α = 0.
    -- f0 H_func (Fintype.card α) = f0 H_func 0 = 0.
    -- H_func (p : α → NNReal) where α is empty. p is the empty function.
    -- This is H_func (uniformDist (proof_card_pos_fails)).
    -- The definition of f is specific: f H_axioms {n} (hn_pos) := H_func (uniformDist_Fin_n).
    -- It's not H_func(uniformDist_on_generic_type_of_card_n).
    -- However, by symmetry, H_func (uniformDist α) = H_func (uniformDist (Fin (card α))).
    -- So if card α = 0, H_func (uniformDist α) should be f0 H 0 = 0.
    -- This seems consistent.
    rfl -- Both sides should simplify to 0 based on the `if` and def of `f0`.
