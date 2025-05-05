## TL;DR  
Lean 4 keeps the same dependent‑type theory as Lean 3, but the *surface* you program on is cleaner: one uniform language (no separate tactic DSL), a revamped macro engine, and a simpler, instance‑driven coercion system. The old “special‑purpose” cast functions—​such as `NNReal.coe_nat_cast`—​disappear; you now rely on the generic `Coe`/`CoeTC` instances and the `↑` notation, backed by standard lemmas like `Nat.cast_mul`. ([Lean 4 survival guide for Lean 3 users - GitHub](https://github.com/leanprover-community/mathlib4/wiki/Lean-4-survival-guide-for-Lean-3-users?utm_source=chatgpt.com), [Significant Changes from Lean 3 - Lean Documentation Overview](https://lean-lang.org/lean4/doc/lean3changes.html?utm_source=chatgpt.com))  

---

## Major Shifts at a Glance  

### 1 · Unified Syntax & Macro‑Based Tactics  
* **Single language** for terms *and* tactics—​both are Lean code expanded by macros rather than a hard‑wired tactic DSL. ([Review of Lean 4 : r/haskell - Reddit](https://www.reddit.com/r/haskell/comments/z55hha/review_of_lean_4/?utm_source=chatgpt.com), [Tactics - Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/tactics.html?utm_source=chatgpt.com))  
* Snake‑case keywords, new `by`/`exact?` sugar, and cleaned‑up binder syntax replace many Lean 3 idioms. ([Lean 4 survival guide for Lean 3 users - GitHub](https://github.com/leanprover-community/mathlib4/wiki/Lean-4-survival-guide-for-Lean-3-users?utm_source=chatgpt.com), [Topic: tactic naming convention - Zulip Chat Archive](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/tactic.20naming.20convention.html?utm_source=chatgpt.com))  

### 2 · Library & Namespacing Overhaul  
* `mathlib4` is a fresh port; many combinators were renamed or dropped to favour type‑class‑driven patterns. ([What will happen to mathlib when we transition to Lean 4?](https://proofassistants.stackexchange.com/questions/274/what-will-happen-to-mathlib-when-we-transition-to-lean-4?utm_source=chatgpt.com))  
* Numbers live in `Mathlib.Data.Nat.Cast.Basic`, `Mathlib.Data.Real.NNReal`, etc.; imports are more granular. ([Mathlib.Data.Nat.Cast.Basic - Lean community](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Cast/Basic.html?utm_source=chatgpt.com))  

### 3 · Coercion Paradigm  
| Lean 3 style | Lean 4 style | Why it changed |
|--------------|--------------|----------------|
| Explicit helpers (`nat_cast_le`, `NNReal.coe_nat_cast`, …) | Generic coercion via `↑` and `Coe` instances | Less surface API, uniform reasoning  ([How to perform type conversion/coercion in Lean 4?](https://proofassistants.stackexchange.com/questions/4113/how-to-perform-type-conversion-coercion-in-lean-4?utm_source=chatgpt.com), [Coercions - Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/type-classes/coercion.html?utm_source=chatgpt.com)) |
| Proofs relied on unfolding those helpers | Proofs use `simp`, `Nat.cast_*`, `Algebra.*` lemmas | Fewer rewrites; `simp` knows about `CoeTC`  ([Coercions - Lean](https://lean-lang.org/doc/reference/latest/Coercions/?utm_source=chatgpt.com), [12.2. Coercing Between Types - Lean](https://lean-lang.org/doc/reference/latest/Coercions/Coercing-Between-Types/?utm_source=chatgpt.com)) |

---

## Practical Guide: Working with Casts in Lean 4  

1. **Import the right files.**  
   ```lean
   import Mathlib.Data.Real.NNReal
   import Mathlib.Data.Nat.Cast.Basic
   ```  
   These bring in the `Coe` instances and `Nat.cast_*` lemmas you need. ([Mathlib.Data.Nat.Cast.Basic - Lean community](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Cast/Basic.html?utm_source=chatgpt.com))  

2. **Use `↑`.**  
   Writing `(n : ℝ≥0)` or simply `↑(n : ℝ≥0)` triggers the `CoeTC` machinery; no function call is required. ([How to perform type conversion/coercion in Lean 4?](https://proofassistants.stackexchange.com/questions/4113/how-to-perform-type-conversion-coercion-in-lean-4?utm_source=chatgpt.com), [Coercions - Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/type-classes/coercion.html?utm_source=chatgpt.com))  

3. **Lean inserts chains automatically.**  
   If there is `Nat → Int` and `Int → ℝ`, Lean can coerce `Nat` → `ℝ` by chaining. ([Coercions - Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/type-classes/coercion.html?utm_source=chatgpt.com), [Coercions - Functional Programming in Lean](https://docs.lean-lang.org/functional_programming_in_lean/type-classes/coercion.html?utm_source=chatgpt.com))  

4. **Lean knows arithmetic facts about casts.**  
   Lemmas like `Nat.cast_mul`, `Nat.cast_add`, `Nat.cast_pow` work for *any* semiring target, so `simp` can finish many goals. ([Mathlib.Data.Nat.Cast.Basic - Lean community](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Cast/Basic.html?utm_source=chatgpt.com))  

5. **Equality over `NNReal`** often reduces to equality over `ℝ` via `NNReal.eq` plus `simp` on `NNReal.coe_*` lemmas. ([Zulip Chat Archive - Lean community](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/coercion.20from.20Nat.20to.20ENat.html?utm_source=chatgpt.com))  

---

## Porting Checklist for Coercions  

* 🔍 **Search for old helpers** such as `nat_abs_cast`, `coe_nat`, `coe_nat_cast`, etc.  
* 🔄 **Replace** them with `↑n : target_type` and rely on `simp` lemmas.  
* 🧹 **Delete unwrap/rewrap code**; `simp [NNReal.coe_mul]` + `Nat.cast_*` normally suffices.  
* ✅ **Add `open scoped NNReal`** for notation like `((n : ℝ≥0) * m)`.  

---

## Worked Example (revisited)  

```lean
lemma nnreal_coe_nat_mul (n m : ℕ) :
    ((n : ℝ≥0) * m) = (n * m : ℝ≥0) := by
  apply NNReal.eq
  simp [NNReal.coe_mul, Nat.cast_mul]      -- ‹↑n * ↑m = ↑(n*m)›
```  

*No bespoke cast function, just coercions and two `simp` lemmas.*  

---

## Where to Learn More  

* Lean 4 survival guide for Lean 3 users – concise porting tips. ([Lean 4 survival guide for Lean 3 users - GitHub](https://github.com/leanprover-community/mathlib4/wiki/Lean-4-survival-guide-for-Lean-3-users?utm_source=chatgpt.com))  
* Lean manual §“Significant Changes from Lean 3”. ([Significant Changes from Lean 3 - Lean Documentation Overview](https://lean-lang.org/lean4/doc/lean3changes.html?utm_source=chatgpt.com))  
* Lean reference documentation on coercions and `Coe`/`CoeTC`. ([Coercions - Lean](https://lean-lang.org/doc/reference/latest/Coercions/?utm_source=chatgpt.com), [12.2. Coercing Between Types - Lean](https://lean-lang.org/doc/reference/latest/Coercions/Coercing-Between-Types/?utm_source=chatgpt.com))  
* ProofAssistants.SE thread on Lean 4 coercions – hands‑on examples. ([How to perform type conversion/coercion in Lean 4?](https://proofassistants.stackexchange.com/questions/4113/how-to-perform-type-conversion-coercion-in-lean-4?utm_source=chatgpt.com))  
* Zulip “coercion from Nat to ENat” discussion for troubleshooting edge cases. ([Zulip Chat Archive - Lean community](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/coercion.20from.20Nat.20to.20ENat.html?utm_source=chatgpt.com))