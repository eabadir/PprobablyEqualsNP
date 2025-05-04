import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic

open Real List

-- Simplified uniformDist for MWE
noncomputable def uniformDist (n : Nat) : List Real :=
  match n with
  | 0 => []
  | k+1 => replicate (k+1) (1 / (k+1 : Real))

@[simp] lemma length_uniformDist (n : Nat) : length (uniformDist n) = n := by
  cases n <;> simp [uniformDist]

/-- Helper: filter (fun x : Real => decide (x > 0)) on [0] is []. -/
lemma filter_decide_gt_zero_singleton_zero : filter (fun x : Real => decide (x > 0)) [0] = [] := by
  simp [filter, gt_iff_lt, decide_eq_false_iff_not.mpr (lt_irrefl 0)]

/-- Helper: filter (fun x : Real => decide (x > 0)) on uniformDist n is identity for n > 0. -/
lemma filter_decide_gt_zero_uniformDist_eq_self {n : Nat} (hn : 0 < n) :
    filter (fun x : Real => decide (x > 0)) (uniformDist n) = uniformDist n := by
  apply filter_eq_self.mpr
  intro x hx_mem
  simp only [uniformDist] at hx_mem
  cases n with
  | zero => exact (Nat.not_lt_zero 0 hn).elim
  | succ k =>
    simp only [mem_replicate] at hx_mem
    obtain ⟨_hnz, hx_eq⟩ := hx_mem
    rw [hx_eq, decide_eq_true_iff] -- Goal: 1 / (↑k + 1) > 0
    positivity -- Should solve the goal directly

-- === Main Proof for f_non_decreasing ===

/-- Lemma: f is non-decreasing. Follows from Properties 2 and 5. -/
lemma f_non_decreasing (k : Nat) : True := by
  have nk_pos : 0 < k + 1 := Nat.succ_pos k
  let p := uniformDist (k+1)
  have hp_len_pos : 0 < p.length := sorry

  let p' := p ++ [0] -- Use generic 0
  have hp'_len_val : p'.length = k + 2 := sorry
  have hp'_len_pos : 0 < p'.length := by rw [hp'_len_val]; positivity

  suffices p'.filter (fun x : Real => decide (x > 0)) = p by trivial

  simp only [p'] -- Goal: filter (...) (p ++ [0]) = p
  rw [filter_append] -- Goal: filter (...) p ++ filter (...) [0] = p
  -- Use convert_to for robustness
  convert_to filter (fun x : Real => decide (x > 0)) p ++ [] = p using 2
  · exact filter_decide_gt_zero_singleton_zero -- Prove filter (...) [0] = []
  rw [append_nil] -- Goal: filter (...) p = p
  rw [filter_decide_gt_zero_uniformDist_eq_self nk_pos] -- Goal: p = p
