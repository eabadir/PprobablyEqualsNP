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

------------------------------------------------------------
-- helpers
------------------------------------------------------------
def isAllTrue (L : List Bool) : Prop := ∀ x ∈ L, x = true
instance (L) : Decidable (isAllTrue L) := by
  unfold isAllTrue; exact List.decidableBAll (fun x ↦ x = true) L



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


/--  `toRat (fromRat q)` is definitionally equal to `q`.  -/
lemma to_from (q : ℚ) : toRat (fromRat q) = q := by
  -- ①  Unfold everything once; the goal becomes a single `if … then … else …`.
  simp [toRat, fromRat, buildEncoding, unary]

  -- ②  Split on the sign of the integer numerator.
  by_cases h : (0 : Int) ≤ q.num

  -- ③  Non-negative numerator -----------------------------------------------
  · have h_cast :
      (Int.ofNat q.num.natAbs : ℚ) = q.num := by
        -- `Lean.Omega.Int.ofNat_natAbs` rewrites the *integer* equality,
        -- then we cast both sides to `ℚ`.
        have h_int : (Int.ofNat q.num.natAbs : Int) = q.num :=
          by aesop
            --simpa using Lean.Omega.Int.ofNat_natAbs q.num
        simpa using congrArg (fun z : Int => (z : ℚ)) h_int

    --  `Rat.num_div_den` is the canonical lemma `q.num / q.den = q`.
    simp [h, h_cast, Rat.num_div_den]


  -- ④  Negative numerator ----------------------------------------------------
  · have h_neg : q.num < 0 := lt_of_not_ge h

    have h_cast :
      (Int.ofNat q.num.natAbs : ℚ) = -q.num := by
        have h_int : (Int.ofNat q.num.natAbs : Int) = -q.num :=
          by
            -- second half of `natAbs` dichotomy (already proved in core)
            have : (Int.ofNat q.num.natAbs : Int) = Int.abs q.num :=
              (Lean.Omega.Int.ofNat_natAbs q.num).trans
                (by by_cases h' : 0 ≤ q.num <;> simp [h', Int.abs] at *)
            simpa [Int.abs_of_neg h_neg] using this
        simpa using congrArg (fun z : Int => (z : ℚ)) h_int

    have : -((q.num : ℚ) / q.den) = q := by
      have := Rat.num_div_den q
      field_simp [this]  -- turns `- (num/den) = q` into `q = q`

    simpa [h, h_cast] using this

/-- `fromRat` followed by `toRat` is identity (proof is `rfl`). -/
lemma from_to (e : GeneratedRat_PCA) : fromRat (toRat e) = e := by
  cases e with
  | mk rb h =>
      cases rb with
      | mk s n d hd =>
          simp [fromRat, toRat, buildEncoding] using rfl

/-- Equivalence between our packed encoding and Mathlib's `ℚ`. -/
noncomputable def equivGeneratedRat : GeneratedRat_PCA ≃ ℚ :=
{ toFun    := toRat,
  invFun   := fromRat,
  left_inv := from_to,
  right_inv:= to_from }
