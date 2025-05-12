import Mathlib.Data.Sym.Card

import PPNP.Common.Basic
import PPNP.Entropy.Common
import PPNP.Entropy.Physics.Common
import PPNP.Entropy.RET

namespace PPNP.Entropy.Physics.PPNP.UniformSystems

open PPNP.Entropy.RET

open Multiset NNReal
open PPNP.Common
open PPNP.Entropy.Common
open PPNP.Entropy.Physics.Common



open Fin Real NNReal Nat Multiset


/--
The canonical uniform distribution on `Fin k`.
Defined as `fun (_ : Fin k) => (k : NNReal)⁻¹`.
This is a specialization of `uniformDist` for clarity and specific use with `Fin k`.
-/
noncomputable def canonicalUniformDist (k : ℕ) (hk_pos : k > 0) : Fin k → NNReal :=
  uniformDist (Fintype_card_fin_pos hk_pos)

/--
Proof that `canonicalUniformDist k hk_pos` sums to 1.
This directly uses `sum_uniformDist` with the appropriate proof of positivity
for `Fintype.card (Fin k)`.
-/
lemma sum_canonicalUniformDist_eq_one (k : ℕ) (hk_pos : k > 0) :
    (∑ i, canonicalUniformDist k hk_pos i) = 1 := by
  simp only [canonicalUniformDist] -- Unfold to uniformDist (Fintype_card_fin_pos hk_pos)
  exact sum_uniformDist (Fintype_card_fin_pos hk_pos)

/--
Symmetry of `stdShannonEntropyLn`: `stdShannonEntropyLn (p ∘ e) = stdShannonEntropyLn p`
for an `Equiv e : α ≃ β` between two Fintypes `α` and `β`,
and a target distribution `p_target : β → NNReal`.
The sum `∑ x:α, negMulLog(p_target(e x))` is transformed to `∑ y:β, negMulLog(p_target y)`.
-/
theorem stdShannonEntropyLn_comp_equiv {α β : Type*} [Fintype α] [Fintype β]
    (p_target : β → NNReal) (e : α ≃ β) :
    stdShannonEntropyLn (p_target ∘ e) = stdShannonEntropyLn p_target := by
  -- Unfold stdShannonEntropyLn on both sides to expose the sums.
  unfold stdShannonEntropyLn
  -- LHS: ∑ (x : α), negMulLog ((p_target (e x)) : ℝ)
  -- RHS: ∑ (y : β), negMulLog ((p_target y) : ℝ)
  -- Apply Function.comp_apply to the term inside the sum on the LHS.
  simp_rw [Function.comp_apply]
  -- LHS is now: ∑ (x : α), negMulLog ((p_target (e x)) : ℝ)
  -- Let g(y) := negMulLog ((p_target y) : ℝ).
  -- LHS is ∑ (x : α), g (e x).
  -- Equiv.sum_comp states: (∑ x, g (e x)) = (∑ y, g y).
  exact Equiv.sum_comp e (fun (y : β) => negMulLog ((p_target y) : ℝ))

-- We'll continue with `stdShannonEntropyLn_canonicalUniform_eq_log_k` and the main theorem
-- `H_uniform_mapped_dist_eq_C_shannon` once this part is verified.

lemma stdShannonEntropyLn_canonicalUniform_eq_log_k (k : ℕ) (hk_pos : k > 0) :
    stdShannonEntropyLn (canonicalUniformDist k hk_pos) = Real.log k := by
  simp only [canonicalUniformDist] -- Unfold to stdShannonEntropyLn (uniformDist (Fintype_card_fin_pos hk_pos))
  rw [stdShannonEntropyLn_uniform_eq_log_card (Fintype_card_fin_pos hk_pos)] -- from Entropy.Common
  -- Goal is Real.log (Fintype.card (Fin k)) = Real.log k
  rw [Fintype.card_fin k] -- from Mathlib

theorem H_canonical_uniform_eq_C_shannon
    (H_func : ∀ {α_aux : Type} [Fintype α_aux], (α_aux → NNReal) → NNReal)
    (hH_axioms : IsEntropyFunction H_func)
    (k : ℕ) (hk_pos : k > 0) :
    -- Removed 'let p_unif_k := canonicalUniformDist k hk_pos' from the statement
    (H_func (canonicalUniformDist k hk_pos) : ℝ) = (C_constant_real hH_axioms) * stdShannonEntropyLn (canonicalUniformDist k hk_pos) := by
  let p_unif_k := canonicalUniformDist k hk_pos

  -- Explicitly show that (H_func p_unif_k : ℝ) is equivalent to (f0 hH_axioms k : ℝ)
  have h_lhs_eq_f0_val : (H_func p_unif_k : ℝ) = (f0 hH_axioms k : ℝ) := by
    -- Unfold definitions to show both sides are definitionally equal to
    -- (H_func (uniformDist (Fintype_card_fin_pos hk_pos)) : ℝ)
    simp only [p_unif_k, canonicalUniformDist, uniformDist, Fintype_card_fin_pos,
               f0, f, dif_pos hk_pos]
    -- At this point, both sides should be identical after simp.

  -- Rewrite the LHS of the main goal using this equality
  rw [h_lhs_eq_f0_val]
  -- Now the goal is: (f0 hH_axioms k : ℝ) = (C_constant_real hH_axioms) * stdShannonEntropyLn p_unif_k

  -- Now use RotaUniformTheorem, which applies to (f0 hH_axioms k : ℝ)
  rw [(RotaUniformTheorem_formula_with_C_constant hH_axioms).right k hk_pos]
  -- Goal: C_constant_real hH_axioms * Real.log k = C_constant_real hH_axioms * stdShannonEntropyLn p_unif_k
  -- Need stdShannonEntropyLn p_unif_k = Real.log k
  rw [stdShannonEntropyLn_canonicalUniform_eq_log_k k hk_pos]
  -- Goal is now an identity: C * log k = C * log k

/--
Helper Lemma: Shows that a system distribution `p_sys`, if uniform on `Ω_sys` with cardinality `k`,
is equivalent to the canonical uniform distribution on `Fin k` composed with the equivalence
`e_sys_to_fin_k : Ω_sys ≃ Fin k`.
-/
lemma p_sys_eq_canonical_comp_equiv
    {Ω_sys : Type} [Fintype Ω_sys]
    (p_sys : Ω_sys → NNReal)
    (k : ℕ) (hk_pos : k > 0)
    (hp_sys_is_uniform : p_sys = fun (_ : Ω_sys) => (k : NNReal)⁻¹)
    (e_sys_to_fin_k : Ω_sys ≃ Fin k) :
    p_sys = (canonicalUniformDist k hk_pos) ∘ e_sys_to_fin_k := by
  let p_unif_k := canonicalUniformDist k hk_pos
  funext ω_sys
  rw [hp_sys_is_uniform] -- LHS is k⁻¹
  simp [p_unif_k, canonicalUniformDist, uniformDist, Function.comp_apply, Fintype_card_fin_pos, hk_pos] -- RHS is k⁻¹

lemma H_sys_eq_H_canonical_nnreal_of_comp
    {Ω_sys : Type} [Fintype Ω_sys]
    (H_func : ∀ {α_aux : Type} [Fintype α_aux], (α_aux → NNReal) → NNReal)
    (hH_axioms : IsEntropyFunction H_func)
    (p_sys_arg : Ω_sys → NNReal)
    (k : ℕ) (hk_pos : k > 0)
    (e_sys_to_fin_k : Ω_sys ≃ Fin k)
    (h_p_sys_is_comp : p_sys_arg = (canonicalUniformDist k hk_pos) ∘ e_sys_to_fin_k) :
    H_func p_sys_arg = H_func (canonicalUniformDist k hk_pos) := by
  let p_unif_k := canonicalUniformDist k hk_pos
  rw [h_p_sys_is_comp]
  -- Goal is now H_func (p_unif_k ∘ e_sys_to_fin_k) = H_func p_unif_k
  -- Axiom: symmetry {α} {β} (p_target : β → NNReal) (sum_proof) (e : α ≃ β) : H (p_target ∘ e) = H p_target
  -- Here: α is Ω_sys, β is Fin k, p_target is p_unif_k, e is e_sys_to_fin_k
  exact hH_axioms.symmetry p_unif_k (sum_canonicalUniformDist_eq_one k hk_pos) e_sys_to_fin_k

-- This should go into UniformSystems.lean (or wherever the other micro-lemmas are)
-- It depends on:
-- canonicalUniformDist (from UniformSystems.lean)
-- stdShannonEntropyLn_comp_equiv (from UniformSystems.lean or a common place for stdShannonEntropyLn properties)

/--
Helper Lemma: Shows that `stdShannonEntropyLn` of `p_sys`
is equal to `stdShannonEntropyLn` of `canonicalUniformDist k hk_pos`,
given that `p_sys` is the composition of `canonicalUniformDist` with the equivalence `e_sys_to_fin_k`.
-/
lemma stdShannon_sys_eq_stdShannon_canonical
    {Ω_sys : Type} [Fintype Ω_sys]
    (p_sys : Ω_sys → NNReal)
    (k : ℕ) (hk_pos : k > 0)
    (e_sys_to_fin_k : Ω_sys ≃ Fin k)
    (h_p_sys_is_comp : p_sys = (canonicalUniformDist k hk_pos) ∘ e_sys_to_fin_k) :
    stdShannonEntropyLn p_sys = stdShannonEntropyLn (canonicalUniformDist k hk_pos) := by
  let p_unif_k := canonicalUniformDist k hk_pos
  rw [h_p_sys_is_comp] -- LHS becomes stdShannonEntropyLn (p_unif_k ∘ e_sys_to_fin_k)
  -- Goal: stdShannonEntropyLn (p_unif_k ∘ e_sys_to_fin_k) = stdShannonEntropyLn p_unif_k
  -- This is precisely what stdShannonEntropyLn_comp_equiv states.
  -- stdShannonEntropyLn_comp_equiv arguments: p_target (p_unif_k), equiv (e_sys_to_fin_k)
  exact stdShannonEntropyLn_comp_equiv p_unif_k e_sys_to_fin_k

theorem H_physical_dist_eq_C_shannon_if_uniform_and_equiv
    {Ω_sys : Type} [Fintype Ω_sys]
    (H_func : ∀ {α_aux : Type} [Fintype α_aux], (α_aux → NNReal) → NNReal)
    (hH_axioms : IsEntropyFunction H_func)
    (p_sys : Ω_sys → NNReal)
    -- Condition 1: Ω_sys has a known cardinality k > 0
    (k : ℕ) (hk_pos : k > 0) (_h_card_Ω_eq_k : Fintype.card Ω_sys = k)
    -- Condition 2: p_sys is uniform on Ω_sys with this cardinality k
    (hp_sys_is_uniform : p_sys = fun (_ : Ω_sys) => (k : NNReal)⁻¹)
    -- Condition 3: Ω_sys is equivalent to Fin k
    (e_sys_to_fin_k : Ω_sys ≃ Fin k)
    :
    (H_func p_sys : ℝ) = (C_constant_real hH_axioms) * stdShannonEntropyLn p_sys := by

  let p_unif_k := canonicalUniformDist k hk_pos

  -- Prove p_sys is composition (Micro-lemma 1 application)
  have h_psys_is_comp_val : p_sys = p_unif_k ∘ e_sys_to_fin_k :=
    p_sys_eq_canonical_comp_equiv p_sys k hk_pos hp_sys_is_uniform e_sys_to_fin_k

  -- Step 1: Show (H_func p_sys : ℝ) = (H_func p_unif_k : ℝ)
  have h_H_sys_eq_H_unif_k_real : (H_func p_sys : ℝ) = (H_func p_unif_k : ℝ) := by
    have h_nnreal_eq : H_func p_sys = H_func p_unif_k :=
      H_sys_eq_H_canonical_nnreal_of_comp H_func hH_axioms p_sys k hk_pos e_sys_to_fin_k h_psys_is_comp_val
    rw [h_nnreal_eq]

  -- Step 2: Use H_canonical_uniform_eq_C_shannon
  rw [h_H_sys_eq_H_unif_k_real]
  -- Goal is now: (H_func p_unif_k : ℝ) = C_constant_real hH_axioms * stdShannonEntropyLn p_sys
  rw [H_canonical_uniform_eq_C_shannon H_func hH_axioms k hk_pos]
  -- Goal is now: C_constant_real hH_axioms * stdShannonEntropyLn p_unif_k = C_constant_real hH_axioms * stdShannonEntropyLn p_sys

  -- Step 3: Show stdShannonEntropyLn p_sys = stdShannonEntropyLn p_unif_k
  have h_shannon_sys_eq_canon : stdShannonEntropyLn p_sys = stdShannonEntropyLn p_unif_k :=
    stdShannon_sys_eq_stdShannon_canonical p_sys k hk_pos e_sys_to_fin_k h_psys_is_comp_val

  rw [h_shannon_sys_eq_canon] -- Rewrites RHS: C * stdShannon p_unif_k = C * stdShannon p_unif_k
  -- Goal should be reflexive.
