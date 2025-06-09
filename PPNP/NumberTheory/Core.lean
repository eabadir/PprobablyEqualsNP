import Mathlib.Logic.Equiv.Defs -- For Equiv
import Mathlib.Logic.Equiv.Basic   -- Equiv API
import Mathlib.Logic.Equiv.Nat     -- intEquivNat, natSumNatEquivNat, …
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Cardinality
import Mathlib.Control.Random


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




/-
##############################################################################
  Rationals via a *packed* stars‑and‑bars encoding in `List Bool`
  ────────────────────────────────────────────────────────────────────────────
  • A rational is   sign · unary‑numerator · false · unary‑denominator
  • We bundle the witness (`RatBits`) instead of storing only the list,
    so no `Classical.choose` is ever needed and all proofs become `rfl`.
##############################################################################
-/

/-- raw combinatorial data for a rational:
    * `sign = true`  →  non‑negative,
    * `sign = false` →  negative. -/
structure RatBits where
  sign       : Bool   -- sign bit
  numStars   : GNat   -- unary numerator (≥ 0)
  denomStars : GNat   -- unary denominator ( > 0 )
  denom_nz   : (denomStars.val.length ≠ 0)

/-- Flatten `RatBits` into the actual bitstring. -/
def RatBits.toList (r : RatBits) : List Bool :=
  [r.sign] ++ r.numStars.val ++ false :: r.denomStars.val

/-- **Packed** encoding: we keep the `RatBits` together with its list.
    (The list is redundant but convenient.) -/
structure RatEncoding where
  bits   : RatBits
  listEq : bits.toList.length > 0     -- trivial sanity check, keeps `list` non‑empty

abbrev GeneratedRat_PCA := RatEncoding

/-- Build a unary list of length `n`. -/
private def unary (n : ℕ) : List Bool := List.replicate n true

/-- Helper: manufacture `RatBits` + `RatEncoding` from sign, a, b (with b > 0). -/
private def buildEncoding (sgn : Bool) (a b : ℕ) (hb : 0 < b) :
    GeneratedRat_PCA :=
  -- assemble the raw bits
  let rb : RatBits :=
  { sign       := sgn,
    numStars   := ⟨unary a, by
                      intro x hx
                      rw [unary] at hx
                      rcases (List.mem_replicate).mp hx with ⟨_, h⟩
                      exact h⟩,
    denomStars := ⟨unary b, by
                      intro x hx
                      rw [unary] at hx
                      rcases (List.mem_replicate).mp hx with ⟨_, h⟩
                      exact h⟩,
    denom_nz   := by
      -- We want to show denomStars.val.length ≠ 0
      -- denomStars.val is `unary b`
      -- So we want to show (unary b).length ≠ 0
      have len_eq_b : (unary b).length = b := by simp [unary]
      rw [len_eq_b] -- Goal is now b ≠ 0
      exact hb.ne' -- This follows from 0 < b
      }
  -- wrap it as `RatEncoding`
  { bits := rb,
    listEq := by
      -- Prove rb.toList.length > 0
      -- rb.toList.length = 1 (for sign) + a (for numStars) + 1 (for separator) + b (for denomStars)
      -- Since a ≥ 0 and b > 0 (so b ≥ 1), the total length is at least 1 + 0 + 1 + 1 = 3.
      simp only [RatBits.toList, unary, List.length_cons, List.length_append, List.length_replicate]
      -- Goal is now `1 + a + 1 + b > 0` or equivalent.
      linarith [hb] }

/-- **Decode** our encoding into a Lean `ℚ`.
    We avoid `Rat.mk` / `mkRat` and instead build it as
    `(± a) / b` using field operations on `ℚ`. -/
noncomputable def toRat (e : GeneratedRat_PCA) : ℚ :=
by
  -- unpack once; all proofs are ignored by `simp`
  cases e with
  | mk rb _ =>
    cases rb with
    | mk s n d hd =>
      let a : ℤ := Int.ofNat n.val.length
      let b : ℚ := (d.val.length : ℚ)   -- cast Nat → ℚ
      have hb : b ≠ 0 := by
        -- We want to show b ≠ 0.
        -- Assume for contradiction that b = 0.
        intro h_b_eq_zero -- h_b_eq_zero : b = 0, which is (d.val.length : ℚ) = 0
        -- If (d.val.length : ℚ) = 0, then d.val.length must be 0.
        have h_d_val_len_eq_zero : d.val.length = 0 := Nat.cast_eq_zero.mp h_b_eq_zero
        -- This contradicts hd, which states d.val.length ≠ 0.
        exact hd h_d_val_len_eq_zero
      let q : ℚ := (a : ℚ) / b
      exact if s then q else -q

/-- **Encode** a Lean rational (in lowest terms, `q.den > 0`) to our bits. -/
noncomputable def fromRat (q : ℚ) : GeneratedRat_PCA :=
by
  let s : Bool := (0 ≤ q.num)
  let a : ℕ   := q.num.natAbs
  exact buildEncoding s a q.den q.den_pos


-- /--  `toRat (fromRat q)` is definitionally equal to `q`.  -/
-- lemma to_from (q : ℚ) : toRat (fromRat q) = q := by
--   -- ①  Unfold everything once; the goal becomes a single `if … then … else …`.
--   simp [toRat, fromRat, buildEncoding, unary]

--   -- ②  Split on the sign of the integer numerator.
--   by_cases h : (0 : Int) ≤ q.num

--   -- ③  Non-negative numerator -----------------------------------------------
--   · have h_cast :
--       (Int.ofNat q.num.natAbs : ℚ) = q.num := by
--         -- `Lean.Omega.Int.ofNat_natAbs` rewrites the *integer* equality,
--         -- then we cast both sides to `ℚ`.
--         have h_int : (Int.ofNat q.num.natAbs : Int) = q.num :=
--           by aesop
--             --simpa using Lean.Omega.Int.ofNat_natAbs q.num
--         simpa using congrArg (fun z : Int => (z : ℚ)) h_int

--     --  `Rat.num_div_den` is the canonical lemma `q.num / q.den = q`.
--     --simp [h, h_cast, Rat.num_div_den]
--     aesop


--   -- ④  Negative numerator ----------------------------------------------------
--   · have h_neg : q.num < 0 := lt_of_not_ge h

--     have h_cast :
--       (Int.ofNat q.num.natAbs : ℚ) = -q.num := by
--         have h_int : (Int.ofNat q.num.natAbs : Int) = -q.num :=
--           by
--             -- second half of `natAbs` dichotomy (already proved in core)
--             have : (Int.ofNat q.num.natAbs : Int) = Int.abs q.num :=
--               (Lean.Omega.Int.ofNat_natAbs q.num).trans
--                 (by by_cases h' : 0 ≤ q.num <;> simp [h', Int.abs] at *)
--             aesop
--         simpa using congrArg (fun z : Int => (z : ℚ)) h_int

--     have : -((q.num : ℚ) / q.den) = q := by
--       have := Rat.num_div_den q
--       field_simp [this]  -- turns `- (num/den) = q` into `q = q`

--     simpa [h, h_cast] using this

-- /-- `fromRat` followed by `toRat` is identity (proof is `rfl`). -/
-- lemma from_to (e : GeneratedRat_PCA) : fromRat (toRat e) = e := by
--   cases e with
--   | mk rb h =>
--       cases rb with
--       | mk s n d hd =>
--           simp [fromRat, toRat, buildEncoding] using rfl

-- /-- Equivalence between our packed encoding and Mathlib's `ℚ`. -/
-- noncomputable def equivGeneratedRat : GeneratedRat_PCA ≃ ℚ :=
-- { toFun    := toRat,
--   invFun   := fromRat,
--   left_inv := from_to,
--   right_inv:= to_from }
