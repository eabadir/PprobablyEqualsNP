import PPNP.NumberTheory.Core
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Countable.Basic -- For Encodable, Countable.equivNat
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Sigma.Basic -- For Equiv.sigmaEquivProdNat if needed for manual equiv

namespace PPNP.NumberTheory.Nat

open PPNP.NumberTheory.Core

/--
The type representing "emergent natural numbers".
An element `⟨t, k_fin⟩` signifies an outcome where a path of length `t`
resulted in `k_fin.val` ones. `k_fin` ranges from `0` to `t`.
-/
def GeneratedNat_PCA : Type := Σ (t : ℕ), Fin (t + 1)

-- Proof Sketch for GeneratedNat_PCA ≃ Nat:
-- 1. Show `GeneratedNat_PCA` is `Encodable`.
--    - `ℕ` is `Encodable`.
--    - For each `t : ℕ`, `Fin (t+1)` is `Encodable` (since it's `Fintype`).
--    - `Encodable.sigma` states that if `α` is encodable and `β : α → Type` is such that `β a` is encodable for all `a`, then `Σ a, β a` is encodable.
-- 2. Any `Encodable` `Countable` type that is also `Infinite` can be put into bijection with `ℕ`.
--    - Need to show `GeneratedNat_PCA` is infinite.
--      (e.g., for any `M : ℕ`, the element `⟨M, 0⟩` is in `GeneratedNat_PCA`).
-- 3. Use `Countable.equivNatOfEncodableInfinite` or `Encodable.equivNat GeneratedNat_PCA`.

@[simp] theorem fin_t_plus_1_encodable (t : ℕ) : Encodable (Fin (t+1)) := Fin.encodable _
instance : Encodable GeneratedNat_PCA := Encodable.sigma fin_t_plus_1_encodable

theorem infinite_GeneratedNat_PCA : Infinite GeneratedNat_PCA :=
  Infinite.of_injective (fun n ↦ ⟨n, 0⟩ : ℕ → GeneratedNat_PCA) (by {
    intro n m h; simp only [Sigma.mk.inj_iff] at h; exact h.1;
  })

/-- The equivalence between our combinatorially generated naturals and Mathlib's Nat. -/
noncomputable def generatedNatPCAEquivNat : GeneratedNat_PCA ≃ Nat :=
  Encodable.equivNat GeneratedNat_PCA

-- Cardinality Statement
theorem card_GeneratedNat_PCA_eq_aleph0 : Cardinal.mk GeneratedNat_PCA = Cardinal.aleph0 := by
  rw [Cardinal.mk_congr generatedNatPCAEquivNat, Cardinal.mk_nat]
