import Mathlib.Tactic.NormNum

import Mathlib.Data.Sym.Card
--import Std.Data.List.Lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic -- For Fintype (Fin n) if needed, though usually direct
import Mathlib.Logic.Equiv.Defs -- For Equiv
--import Mathlib.Order.Monotone.Strict.Nat -- For StrictMono.nat_of_lt_succ

import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic -- For List.replicate, List.length_replicate (from Std, re-exported)
import Mathlib.Logic.Equiv.Basic   -- Equiv API
import Mathlib.Logic.Equiv.Nat     -- intEquivNat, natSumNatEquivNat, …
import PPNP.Common.Basic


import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Cardinality


open Nat Real NNReal Multiset NNReal Fin Set Finset Filter Function BigOperators Topology
    -- Added Function for comp_apply

open Multiset NNReal
open PPNP.Common

namespace PPNP.NumberTheory.Core

-- In PPNP.Entropy.RET.lean
--open PPNP.NumberTheory.Core
open List

/-- The primordial source of infinite binary choices. -/
structure IIDParticleSource where
  stream : ℕ → Bool

/-- A particle path is a finite list of boolean outcomes. -/
abbrev ParticlePath := List Bool

/-- Draws the first `t` choices from an IIDParticleSource to form a ParticlePath. -/
def drawPath (src : IIDParticleSource) (t : ℕ) : ParticlePath :=
  (List.finRange t).map (fun i => src.stream i)

/-- Calculates the number of `true` choices (e.g., "up-steps") in a path. -/
def numOnes (p_path : ParticlePath) : ℕ :=
  p_path.count true -- as in your current code

/--
Calculates the "position" of a particle after `t` steps,
defined as (#trues - #falses).
-/
def particlePosition (p_path : ParticlePath) : ℤ :=
  let ones := numOnes p_path
  let path_len := p_path.length
  let zeros := path_len - ones
  (ones : ℤ) - (zeros : ℤ)

------------------------------------------------------------
-- 2.  Unary naturals = lists of all-true values
------------------------------------------------------------
def AllTrue (L : List Bool) : Prop := ∀ x ∈ L, x = true

-- NEW: make the predicate decidable so that the generic
--      `[Encodable {x // p x}]` instance can fire.
instance (L : List Bool) : Decidable (AllTrue L) := by
  unfold AllTrue
  exact List.decidableBAll (fun x => x = true) L

abbrev GeneratedNat_Unary := { L : List Bool // AllTrue L }

------------------------------------------------------------
-- 3.  Encodable instance now *does* synthesise
------------------------------------------------------------
example : Encodable GeneratedNat_Unary := inferInstance   -- compiles

------------------------------------------------------------
-- 4.  Bijection with ℕ
------------------------------------------------------------
def toNat   (u : GeneratedNat_Unary) : ℕ := u.val.length

def fromNat (n : ℕ) : GeneratedNat_Unary :=
  ⟨List.replicate n true, by
    intro x h_mem
    rw [List.mem_replicate] at h_mem
    exact h_mem.right⟩

lemma left_inv  (n : ℕ) : toNat (fromNat n) = n := by
  simp [toNat, fromNat]

lemma right_inv (u : GeneratedNat_Unary) : fromNat (toNat u) = u := by
  cases u with
  | mk L hL =>
      simp [toNat, fromNat, List.length_replicate, Subtype.ext]
      exact (List.eq_replicate_of_mem hL).symm

noncomputable def equivUnaryNat : GeneratedNat_Unary ≃ ℕ :=
{ toFun    := toNat,
  invFun   := fromNat,
  left_inv := right_inv,
  right_inv:= left_inv }


abbrev GNat := { L : List Bool // AllTrue L }
def equivGNatToNat : GNat ≃ ℕ :=
{ toFun    := toNat,
  invFun   := fromNat,
  left_inv := right_inv,
  right_inv:= left_inv }

/--
The type representing "emergent integers".
Pairs an element from `GNat` (representing magnitude)
with a `Bool` (representing sign: e.g., true for non-negative, false for negative).
This definition directly uses GNat.
-/
def GeneratedInt_PCA : Type := GNat × Bool

-- To establish GeneratedInt_PCA ≃ ℤ:
-- 1. We have `GNat ≃ ℕ` (via equivGNatToNat).
-- 2. We need an equivalence `ℕ × Bool ≃ ℤ`. Mathlib provides `Int.equivNatProdBool : ℤ ≃ ℕ × Bool`. [1]
--    Its inverse is `Int.equivNatProdBool.symm : ℕ × Bool ≃ ℤ`.
-- 3. We construct the equivalence:
--    `GeneratedInt_PCA = GNat × Bool`
--    `≃ ℕ × Bool` (using `Equiv.prodCongr equivGNatToNat (Equiv.refl Bool)`) [3]
--    `≃ ℤ` (using `Int.equivNatProdBool.symm`)

open Equiv

------------------------------------------------------------
-- Emergent integers
------------------------------------------------------------

noncomputable def intEquivNatProdBool : ℤ ≃ ℕ × Bool :=
  (Equiv.intEquivNat.trans (Equiv.boolProdNatEquivNat.symm)).trans (Equiv.prodComm ℕ Bool).symm   -- citations: ③,④,②

noncomputable def generatedIntPCAEquivInt : GeneratedInt_PCA ≃ ℤ :=
  (Equiv.prodCongr equivGNatToNat (Equiv.refl Bool)).trans intEquivNatProdBool.symm


/-! #############################################################
     Rationals as stars-and-bars encodings in `List Bool`
     ########################################################### -/


/-! #############################################################
     Reals as Boolean-valued functions on our emergent naturals
     ########################################################### -/

/-- Emergent reals: the power set of `GNat`, i.e. characteristic
    functions `GNat → Bool`. -/
abbrev GeneratedReal_PCA := GNat → Bool

namespace GeneratedReal_PCA

/-- Transport along `GNat ≃ ℕ`, giving `(GNat → Bool) ≃ (ℕ → Bool)`. -/
noncomputable def equivFunNat : GeneratedReal_PCA ≃ (ℕ → Bool) :=
  Equiv.arrowCongr equivGNatToNat (Equiv.refl Bool)


open Cardinal


/-- The cardinality of `GeneratedReal_PCA` (functions from GNat to Bool) is \(2^{\aleph_0}\). -/
lemma cardinal_eq_two_pow_aleph0 : Cardinal.mk GeneratedReal_PCA = 2 ^ Cardinal.aleph0 := by
  calc
    -- 1) By definition, GeneratedReal_PCA is GNat → Bool.
    --    Using the equivalence equivFunNat : (GNat → Bool) ≃ (ℕ → Bool),
    --    their cardinalities are equal.
    Cardinal.mk GeneratedReal_PCA
      = Cardinal.mk (ℕ → Bool)             := Cardinal.mk_congr equivFunNat
    -- 2) The cardinality of a function space #(A → B) is #B ^ #A.
    _ = Cardinal.mk Bool ^ Cardinal.mk ℕ   := by rw [Cardinal.power_def]
    -- 3) The cardinality of Bool is 2, and the cardinality of ℕ is ℵ₀.
    _ = 2 ^ Cardinal.aleph0                := by aesop
/-- The emergent reals have exactly the same cardinality as ℝ (the continuum). -/

noncomputable def equivGeneratedReal : GeneratedReal_PCA ≃ ℝ :=
  -- 1) combine your two cardinality proofs into `#G = #ℝ`
  have h : mk GeneratedReal_PCA = mk ℝ := by
    calc
      mk GeneratedReal_PCA = 2 ^ aleph0    := cardinal_eq_two_pow_aleph0
      _                 = #ℝ              := (Cardinal.mk_real).symm
  -- 2) use `Cardinal.eq` to get `Nonempty (G ≃ ℝ)`
  Classical.choice (Cardinal.eq.1 h)


end GeneratedReal_PCA
