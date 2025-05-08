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

import Mathlib.Data.Sym.Card

import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import PPNP.Common.Basic
import PPNP.Entropy.Common
import PPNP.Entropy.RET
import PPNP.Entropy.Physics.BoseEinstein



namespace PPNP.Entropy

open BigOperators Fin Real Topology NNReal Filter Nat Set Multiset


-- open PPNP.Common
-- open PPNP.Entropy.Common
-- open PPNP.Entropy.RET
-- open PPNP.Entropy.Physics.BE


/- PPNP.Entropy.Common - Phase 0 Revised/New Objects -/

open BigOperators Fin Real Topology NNReal Filter Nat
open PPNP.Common -- Assuming PPNP.Common contains finProdFinEquiv


/--
Defines the joint probability distribution for a two-stage experiment.
Given `p` as the distribution for the first stage (over `N` outcomes),
and `q_cond i` as the conditional distribution for the second stage (over `M` outcomes)
given the `i`-th outcome of the first stage.
The resulting distribution is over the `N*M` combined outcomes.
P(i,j) = p(i) * q_cond(i,j)
-/
def DependentPairDist
  {N M : ℕ} (prior : Fin N → NNReal)
          (P     : Fin N → Fin M → NNReal) :
  Fin (N * M) → NNReal :=
  fun k =>
    let (i, j) := (finProdFinEquiv.symm k : Fin N × Fin M)
    prior i * P i j

-- 1) Declare the coercion instance
instance {N M : ℕ} : Coe
  ((Fin N → NNReal) × (Fin N → Fin M → NNReal))
  (Fin (N * M) → NNReal) where
  coe := fun (⟨pr, P⟩ : (Fin N → NNReal) × (Fin N → Fin M → NNReal)) =>
    DependentPairDist pr P

-- 2) Revised one‐field structure
structure IsEntropyCondAdd
  (H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0)
: Prop where
  cond_add :
    ∀ {N M : ℕ} [NeZero N] [NeZero M]
      (prior   : Fin N → NNReal)
      (P       : Fin N → Fin M → NNReal)
      (_hP      : ∀ i, ∑ j, P i j = 1)
      (_hprior  : ∑ i, prior i = 1),
    H (DependentPairDist prior P) = H prior + ∑ i, prior i * H (fun j => P i j)

structure IsEntropyNormalized
  (H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0)
: Prop where
  normalized : ∀ (p : Fin 1 → ℝ≥0), (∑ i, p i = 1) → H p = 0

structure IsEntropySymmetric
  (H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0)
: Prop where
  symmetry   : ∀ {n} (p : Fin n → ℝ≥0) (_hp : ∑ i, p i = 1)
                  (σ : Equiv.Perm (Fin n)), H (p ∘ σ) = H p

structure IsEntropyContinuous
  (H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0)
: Prop where
  continuity : ∀ {n} (p : Fin n → ℝ≥0) (_hp : ∑ i, p i = 1)
                  (ε : ℝ), ε > 0 →
                ∃ δ > 0, ∀ (q : Fin n → ℝ≥0), (∑ i, q i = 1) →
                (∀ i, |(q i : ℝ) - (p i : ℝ)| < δ) → |(H q : ℝ) - (H p : ℝ)| < ε

/-- **Axiomatic Entropy Function.**
`IsEntropyFunction_New H` means `H` assigns an entropy value (ℝ≥0) to any finite probability distribution
such that the usual Shannon entropy axioms hold: normalization, symmetry, continuity,
and conditional additivity (chain rule). -/
structure IsEntropyFunction
  (H : ∀ {α : Type} [Fintype α], (α → ℝ≥0) → ℝ≥0)
  : Prop                                -- ① result type comes *before* `extends`
  extends IsEntropyNormalized H,
          IsEntropySymmetric H,
          IsEntropyContinuous H,
          IsEntropyCondAdd H
