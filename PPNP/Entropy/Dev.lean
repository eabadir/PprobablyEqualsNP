import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog -- For negMulLog, Real.log
import Mathlib.Data.NNReal.Basic -- For NNReal
import Mathlib.Topology.Basic -- For ContinuousOn (placeholder)
import Mathlib.Order.Monotone.Basic -- For Monotone
import Mathlib.Algebra.BigOperators.Fin -- For sum over Fin n
import Mathlib.Data.Fin.Basic -- Basic Fin definitions and lemmas
import Mathlib.Data.Fintype.Fin -- Instances for Fin n
import Mathlib.Algebra.Order.Field.Basic -- For inv_one etc.
import Mathlib.Algebra.GroupWithZero.Units.Basic -- Provides mul_inv_cancel₀
import Mathlib.Analysis.SpecialFunctions.Log.Base -- Real.logb
import Mathlib.Analysis.SpecialFunctions.Pow.Real -- Real.rpow
import Mathlib.Data.Complex.Basic -- For Complex.exp_re if needed
import Mathlib.Analysis.SpecificLimits.Basic -- tendsto_one_div_atTop_zero
import Mathlib.Data.Real.Basic -- Basic Real properties
import Mathlib.Order.Filter.Basic -- Filter bases etc.
import Mathlib.Topology.Order.Basic -- OrderTopology
import Mathlib.Data.Nat.Basic -- Basic Nat properties
import Mathlib.Data.Nat.Log -- Nat.log
import Mathlib.Algebra.Order.Floor.Defs -- Floor definitions
import Mathlib.Tactic.Linarith -- Inequality solver
import Mathlib.Algebra.Ring.Nat -- For Nat.cast_pow
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.GroupTheory.Congruence.Basic

import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- Import previous definitions and theorems
import PPNP.Util.Basic
import PPNP.Entropy.RET
import PPNP.Entropy.Physics

namespace PPNP.Entropy

open BigOperators Fin Real Topology NNReal Filter Nat Set Multiset

open PPNP.Util
open PPNP.Entropy.RET
open PPNP.Entropy.Physics



@[simp]
theorem sum_replicate_count_toFinset_eq_self {α : Type*} [DecidableEq α] (s : Multiset α) :
    ∑ i ∈ s.toFinset, Multiset.replicate (Multiset.count i s) i = s := by
  -- Prove by induction on the multiset s
  induction s using Multiset.induction
  case empty =>
    -- Base case: s = 0
    simp -- Uses sum_replicate_count_nil or simplifies directly: toFinset 0 = ∅, sum over ∅ is 0. Goal 0 = 0.
  case cons a s ih =>
    -- Inductive step: Assume property holds for s, prove for a :: s
    -- Goal: ∑ i in (a :: s).toFinset, replicate (count i (a :: s)) i = a :: s
    rw [Multiset.toFinset_cons] -- (a :: s).toFinset = insert a s.toFinset
    -- Goal: ∑ i in insert a s.toFinset, replicate (count i (a :: s)) i = a :: s

    -- Split the proof based on whether 'a' was already in the finset 's.toFinset'
    by_cases ha_mem_finset : a ∈ s.toFinset
    · -- Case 1: a ∈ s.toFinset
      exact step_mem ha_mem_finset ih
    · -- Case 2: a ∉ s.toFinset
      exact step_not_mem ha_mem_finset ih

/-!
Lemma: `beStateToMultiset` and `multisetToBEStateSubtype` are inverses (right inverse).
Shows applying the conversion to multiset then back to state map yields the original multiset.
-/
lemma right_inv_beState_multiset {N M : ℕ} (s : SymFin N M) :
    beStateToMultiset (multisetToBEStateSubtype s) = s.val := by
  -- Unfold the definitions step-by-step
  -- 1. Unfold beStateToMultiset
  dsimp only [beStateToMultiset]
  -- Goal: ∑ i ∈ Finset.univ, replicate ((multisetToBEStateSubtype s).val i) i = s.val

  -- 2. Unfold the .val part of multisetToBEStateSubtype
  --    (multisetToBEStateSubtype s).val = multisetToBEState s.val
  simp only [multisetToBEStateSubtype] -- Use simp to handle the subtype projection
  -- Goal: ∑ i ∈ Finset.univ, replicate (multisetToBEState s.val i) i = s.val

  -- 3. Unfold multisetToBEState
  simp only [multisetToBEState]
  -- Goal: ∑ i ∈ Finset.univ, replicate (Multiset.count i s.val) i = s.val

  -- 4. Use the lemma linking sum over univ to sum over toFinset
  --    Need `Finset.univ` for Fin N and the proof `Finset.mem_univ`
  rw [sum_replicate_count_univ_eq_sum_toFinset s.val Finset.univ (Finset.mem_univ)]
  -- Goal: ∑ i ∈ s.val.toFinset, replicate (Multiset.count i s.val) i = s.val

  -- 5. Apply the key identity proven by induction
  rw [sum_replicate_count_toFinset_eq_self s.val]
  -- Goal is now s.val = s.val, which is true by reflexivity.
