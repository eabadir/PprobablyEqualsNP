import Mathlib.Logic.Equiv.Defs -- For Equiv
import Mathlib.Logic.Equiv.Basic   -- Equiv API
import Mathlib.Logic.Equiv.Nat     -- intEquivNat, natSumNatEquivNat, …
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Cardinality
import Mathlib.Control.Random
import Mathlib.Data.Fintype.Vector

namespace PPNP.NumberTheory.Core

open List

class IIDParticleSource (α : Type) where
  stream : ℕ → α

/-- The canonical representation of a particle path sampled from an IIDParticleSource is symmetric and sorted with 1s first. For example `[true, true, false, false]` is the canonical representation of the path `[true, false, true, false]`. This means that the order of choices does not matter, only the counts of `true` and `false` do. -/
def CannonicalSymmetricParticlePath := List Bool

/-- A non-canonical particle path is just the list of movements describing a random walk -/
abbrev RandomWalkPath := List Bool


instance mkPseudoRandomSource (seed : Nat) : IIDParticleSource Bool :=
{ stream := fun n =>
    let gen0 := mkStdGen seed
    let genN := (List.range n).foldl (fun g _ => (stdNext g).2) gen0
    (randBool genN).1 }

/-- A biased IID particle source that generates `true` with probability `p / (p + q)` and `false` with probability `q / (p + q)`. -/
instance mkBiasedIIDParticleSource (seed : Nat) (p : ℕ) (q: ℕ) (_h : p + q > 0) : IIDParticleSource Bool :=
{ stream := fun n =>
    let gen0 := mkStdGen seed
    let genN := (List.range n).foldl (fun g _ => (stdNext g).2) gen0
    (randBool genN).1 }


/-- Calculates the number of `true` choices (e.g., "up-steps") in a path. -/
def numOnes (p_path : RandomWalkPath) : ℕ :=
  p_path.count true

/--
Calculates the "position" of a particle after `t` steps,
defined as (#trues - #falses).
-/
def particlePosition (p_path : RandomWalkPath) : ℤ :=
  let ones := numOnes p_path
  let path_len := p_path.length
  let zeros := path_len - ones
  (ones : ℤ) - (zeros : ℤ)

------------------------------------------------------------
-- 2.  Unary naturals = lists of all-true values
------------------------------------------------------------
def GNatCompressPath_AllTrue (L : List Bool) : Prop := ∀ x ∈ L, x = true

-- NEW: make the predicate decidable so that the generic
--      `[Encodable {x // p x}]` instance can fire.
instance (L : List Bool) : Decidable (GNatCompressPath_AllTrue L) := by
  unfold GNatCompressPath_AllTrue
  exact List.decidableBAll (fun x => x = true) L

abbrev GeneratedNat_Unary := { L : List Bool // GNatCompressPath_AllTrue L }

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


abbrev GNat := { L : List Bool // GNatCompressPath_AllTrue L }
def equivGNatToNat : GNat ≃ ℕ :=
{ toFun    := toNat,
  invFun   := fromNat,
  left_inv := right_inv,
  right_inv:= left_inv }

/-- Adds two GNat numbers by converting them to ℕ, adding, and converting back. -/
def add_gnat (g1 g2 : GNat) : GNat :=
  equivGNatToNat.invFun (equivGNatToNat.toFun g1 + equivGNatToNat.toFun g2)

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
     Reals as Boolean-valued *functions* on our emergent naturals
     *Constructive Interpretation of functions* --
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
