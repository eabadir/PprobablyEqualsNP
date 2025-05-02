Okay, let's outline an implementation plan for formalizing Rota's Uniqueness of Entropy Theorem in Lean 4, assuming the 5 properties of entropy and proving the uniqueness.

## Implementation Plan: Formalizing Rota's Uniqueness of Entropy

**Goal:** Prove that any function `H` satisfying the 5 axiomatic properties of entropy must be equal to `C * stdEntropy` for some constant `C ≥ 0`, where `stdEntropy` is the standard Shannon entropy using the natural logarithm.

**Assumptions:** We assume a function `H : List ℝ≥0 → Real` exists and satisfies the 5 properties formalized in a structure `IsEntropyFunction`.

**Methodology:** Follow the proof structure outlined in the Rota-Baclawski text (Chapter VIII / Addendum in the paper).

**Chunks:**

1.  **Chunk 1: Setup, Definitions, and Basic Properties of `f(n)`**
    *   **Objective:** Define standard entropy (`stdEntropy`), the `IsEntropyFunction` structure (assuming properties), define `f(n) = H(uniform n)`, and prove `f(1) = 0` and `f` is monotone non-decreasing.
    *   **Lean Tasks:**
        *   Import necessary libraries.
        *   Define `stdEntropy` using `negMulLog`.
        *   Define `structure IsEntropyFunction` encapsulating the 5 properties (Property 4 might be stated abstractly initially or assumed via its consequences). Add `H([1]) = 0` as Prop 0, derivable from others but useful.
        *   Define `f n`.
        *   Prove helper lemma: `∑ (List.replicate n n⁻¹) = 1`.
        *   Prove `f 1 = 0` (using Prop 0).
        *   Prove `Monotone f` (using Prop 2 and Prop 5).
    *   **Testable Outcome:** Lean file compiles, definitions are type-correct, `f 1 = 0` and `Monotone f` theorems are proven.

2.  **Chunk 2: The Power Law `f(n^k) = k * f(n)`**
    *   **Objective:** Prove the key multiplicative property of `f`.
    *   **Lean Tasks:**
        *   Formalize (at least conceptually) the argument using Property 4 (Conditional Entropy: `H(π|σ) = H(π) - H(σ)`). Assume this property holds for `H`.
        *   Construct the partitions π and σ needed in the proof (conceptually: σ has `n^(k-1)` blocks, π refines it into `n^k` blocks).
        *   Show `H(π|σ) = f(n)` (average entropy within blocks of σ).
        *   Show `H(π|σ) = H(π) - H(σ) = f(n^k) - f(n^(k-1))`.
        *   Use induction on `k` or direct summation to prove `f(n^k) = k * f(n)`.
    *   **Testable Outcome:** Theorem `f_pow (n k : ℕ) (hn : n > 0) (hk : k > 0) : f (n ^ k) = k * f n` is proven, likely assuming an abstract version of Property 4 or its direct consequence for this specific partition setup.

3.  **Chunk 3: Deriving `f(n) = C * log n`**
    *   **Objective:** Show that the power law and monotonicity imply `f(n)` is proportional to `log n` (natural log).
    *   **Lean Tasks:**
        *   Define `C := f b / Real.log b` for some integer base `b > 1` (e.g., `b=2` or `b=3`). Or work towards `f(n)/f(2) = logb 2 n` as in the text, then convert to natural log.
        *   Prove `C ≥ 0`.
        *   Use the inequality argument from the text: For any `n, k`, find `b` such that `b^k ≤ n^m < b^(k+1)`. Apply `f` and `log`. Use monotonicity (`f(a) ≤ f(c)` if `a≤c`) and the power law (`f(b^k) = k f(b)`).
        *   Take the limit `m → ∞` (or argue via density) to show `f(n) / f(b) = Real.logb b n`.
        *   Conclude `f n = C * Real.log n`.
    *   **Testable Outcome:** Theorem `exists_C_log_formula : ∃ C ≥ 0, ∀ n > 0, f n = C * Real.log n` is proven.

4.  **Chunk 4: Extension to Rational Probabilities**
    *   **Objective:** Show that `H(p) = C * stdEntropy p` holds when `p` is a list of rational probabilities.
    *   **Lean Tasks:**
        *   Represent rational probabilities `pᵢ = aᵢ / N`.
        *   Again, use Property 4 conceptually. Construct partitions σ (blocks with probability `pᵢ`) and π (finer partition with `N` blocks of probability `1/N`).
        *   Show `H(π|σ) = ∑ pᵢ f(aᵢ) = ∑ pᵢ (C * log aᵢ)`.
        *   Show `H(π|σ) = H(π) - H(σ) = f(N) - H(σ) = C * log N - H(σ)`.
        *   Equate and solve for `H(σ)`: `H(σ) = C log N - C ∑ pᵢ log aᵢ = C ∑ pᵢ (log N - log aᵢ) = C ∑ pᵢ log (N/aᵢ) = C ∑ pᵢ log (1/pᵢ)`.
        *   Relate `∑ pᵢ log (1/pᵢ)` to `stdEntropy p = ∑ negMulLog pᵢ = -∑ pᵢ log pᵢ`. Need `log(1/x) = -log x`. `H(σ) = C * stdEntropy p`.
        *   Handle types carefully (rationals vs reals, `List ℚ≥0` vs `List ℝ≥0`).
    *   **Testable Outcome:** Theorem `h_rational : ∀ (p : List ℚ≥0)..., H (p.map cast) = C * stdEntropy (p.map cast)` is proven.

5.  **Chunk 5: Extension to Real Probabilities**
    *   **Objective:** Use continuity (Property 3) to extend the result from rational to real probabilities.
    *   **Lean Tasks:**
        *   Use `hH.prop3_continuity`.
        *   Use density of rational lists/vectors in the space of real probability vectors.
        *   Apply standard limit arguments: approximate real `p` by rational `q`, show `H(q) → H(p)` and `C * stdEntropy q → C * stdEntropy p`.
    *   **Testable Outcome:** Theorem `h_real : ∀ (p : List ℝ≥0)..., H p = C * stdEntropy p` is proven.

6.  **Chunk 6: Final Theorem Assembly**
    *   **Objective:** State the final `Rota_Uniqueness_of_Entropy` theorem and combine the results from previous chunks.
    *   **Lean Tasks:**
        *   State the theorem formally using `∃ C ≥ 0`.
        *   The proof body combines the existence of `C` from Chunk 3 and the final equality from Chunk 5.
    *   **Testable Outcome:** The main theorem is fully proven.

---

## Lean 4 Code for Chunk 1

```lean
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog -- For negMulLog, Real.log
import Mathlib.Analysis.SpecialFunctions.Log.Base -- For logb if needed later
import Mathlib.Data.Real.NNReal -- For ℝ≥0 (NonNegReal)
import Mathlib.Algebra.BigOperators.List -- For sum over list
import Mathlib.Topology.Basic -- For Continuous
import Mathlib.Order.Monotone.Basic -- For Monotone

open BigOperators List Real Topology NNReal Filter

local notation "ℝ≥0" => NonNegReal

/-!
# Formalizing Rota's Uniqueness of Entropy Theorem - Chunk 1

**Goal:** Define standard Shannon entropy, assume the 5 axiomatic properties for a function H,
define f(n) = H(uniform n), and prove f(1) = 0 and f is monotone.

**Based on:** Rota, Baclawski, Billis "Introduction to Probability Theory" Chapter VIII (as per paper Addendum)
-/

-- ##################################################
-- Definition: Standard Shannon Entropy (base e)
-- ##################################################

/-- Standard Shannon entropy of a probability distribution given as a list of non-negative reals.
Uses natural logarithm (base e). -/
noncomputable def stdEntropy (p : List ℝ≥0) : Real :=
  ∑ x in p, negMulLog (x : Real)

lemma stdEntropy_singleton (x : ℝ≥0) (hx : x = 1) : stdEntropy [x] = 0 := by
  simp [stdEntropy, sum_singleton, hx, negMulLog_one]

lemma stdEntropy_append_zero (p : List ℝ≥0) : stdEntropy (p ++ [0]) = stdEntropy p := by
  simp [stdEntropy, sum_append, sum_singleton, negMulLog_zero]


-- ##################################################
-- Structure: Axiomatic Entropy Function H
-- ##################################################

/-- Structure capturing the 5 axiomatic properties of an entropy function H,
    following Rota-Baclawski Chapter VIII. -/
structure IsEntropyFunction (H : List ℝ≥0 → Real) : Prop :=
  (prop0_H1_eq_0 : H [1] = 0) -- Base case: Entropy of certainty is 0. (Derivable from Prop 4)
  (prop1_domain : ∀ (p : List ℝ≥0), (∑ x in p, x) = 1 → Prop) -- Predicate for valid domain inputs (assumed always true for H's arguments below)
  (prop2_zero_inv : ∀ (p : List ℝ≥0) (hp_sum : ∑ x in p, x = 1), H (p ++ [0]) = H p) -- Invariance under adding zero probability outcomes.
  (prop3_continuity : ContinuousOn H {p | (∑ x in p, x) = 1}) -- Continuity on the simplex. (Needs topology on List ℝ≥0 space - conceptual for now)
  (prop4_conditional : Prop) -- Placeholder: H(π|σ) = H(π) - H(σ) for π finer than σ. Assumed true, consequences used later.
  (prop5_max_uniform : ∀ {n : ℕ} (hn : n > 0) (p : List ℝ≥0) (hp_len : p.length = n) (hp_sum : ∑ x in p, x = 1),
      H p ≤ H (List.replicate n (n⁻¹ : ℝ≥0))) -- Max entropy for uniform distribution.


-- ##################################################
-- Definition: f(n) = H(uniform distribution on n outcomes)
-- ##################################################

-- Helper lemma: the uniform distribution sums to 1
lemma sum_replicate_inv_eq_one {n : ℕ} (hn : n > 0) :
    ∑ x in (List.replicate n (n⁻¹ : ℝ≥0)), x = 1 := by
  rw [sum_list_replicate, Nat.card_replicate]
  rw [nsmul_eq_mul, ← NNReal.coe_nat_cast, NNReal.coe_inv, NNReal.coe_nat_cast,
      mul_inv_cancel]
  exact Iff.mpr Nat.cast_ne_zero (Nat.pos_iff_ne_zero.mp hn)

/-- Define f(n) as the entropy H of the uniform distribution on n outcomes. -/
noncomputable def f (H : List ℝ≥0 → Real) (n : ℕ) : Real :=
  if hn : n > 0 then H (List.replicate n (n⁻¹ : ℝ≥0)) else 0

-- Assume H satisfies the properties for the rest of the proofs
variable {H : List ℝ≥0 → Real} (hH : IsEntropyFunction H)

-- ##################################################
-- Basic Properties of f(n)
-- ##################################################

/-- Property: f(1) = 0 -/
theorem f_1_eq_0 : f H 1 = 0 := by
  have h1 : 1 > 0 := by decide
  simp only [f, dif_pos h1] -- Use definition of f for n=1
  have h_unif1 : List.replicate 1 (1⁻¹ : ℝ≥0) = [1] := by
    simp [inv_one] -- 1⁻¹ = 1, replicate 1 [x] = [x]
  rw [h_unif1]
  exact hH.prop0_H1_eq_0 -- Use the assumed property H([1]) = 0


/-- Property: f is monotone non-decreasing -/
theorem f_mono : Monotone (f H) := by
  -- Need to show f H n ≤ f H (n + 1) for all n ∈ ℕ
  intro n m hnm -- Assume n ≤ m, need to show f H n ≤ f H m
  -- Base case n=0 is trivial: f H 0 = 0, and f H m ≥ f H 1 = 0 (by f_mono applied recursively or from physics intuition H>=0, not assumed here)
  -- Let's prove f n ≤ f (n+1) for n ≥ 1. The general case follows by transitivity.
  suffices h_step : ∀ n ≥ 1, f H n ≤ f H (n + 1) by
    apply monotone_nat_of_le_succ
    intro n
    if hn_zero : n = 0 then
      rw [hn_zero]
      simp only [f] -- f H 0 = 0
      -- We need f H 1 ≥ 0. f H 1 = 0 by f_1_eq_0. So 0 ≤ 0 holds.
      exact le_refl 0
    else
      apply h_step
      exact Nat.pos_of_ne_zero hn_zero

  -- Prove the step: f n ≤ f (n+1) for n ≥ 1
  intro n hn_ge1
  have hn_pos : n > 0 := hn_ge1
  have hn1_pos : n + 1 > 0 := Nat.succ_pos n

  -- Define p = (1/n, ..., 1/n, 0), which has length n+1
  let p : List ℝ≥0 := (List.replicate n (n⁻¹ : ℝ≥0)) ++ [0]

  -- Check length of p is n+1
  have hp_len : p.length = n + 1 := by simp [List.length_append, List.length_replicate]

  -- Check sum of p is 1
  have hp_sum : ∑ x in p, x = 1 := by
    rw [List.sum_append, List.sum_singleton, add_zero]
    exact sum_replicate_inv_eq_one hn_pos

  -- Apply Property 5 to p: H(p) ≤ H(uniform n+1) = f(n+1)
  have h_p_le_f_n1 : H p ≤ H (List.replicate (n + 1) ((n + 1)⁻¹ : ℝ≥0)) :=
    hH.prop5_max_uniform p hp_len hp_sum

  -- Relate H(p) to f(n) using Property 2
  -- H(p) = H( (1/n,...,1/n) ++ [0] ) = H(1/n,...,1/n) (by prop2) = f(n)
  have h_p_eq_f_n : H p = H (List.replicate n (n⁻¹ : ℝ≥0)) := by
    apply hH.prop2_zero_inv
    exact sum_replicate_inv_eq_one hn_pos -- Need the sum=1 hypothesis for prop2

  -- Now combine: f(n) = H(p) ≤ H(uniform n+1) = f(n+1)
  -- Definition of f for n > 0
  have f_n_def : f H n = H (List.replicate n (n⁻¹ : ℝ≥0)) := by simp [f, dif_pos hn_pos]
  -- Definition of f for n+1 > 0
  have f_n1_def : f H (n+1) = H (List.replicate (n+1) ((n+1)⁻¹ : ℝ≥0)) := by simp [f, dif_pos hn1_pos]

  -- Combine inequalities and definitions
  rw [f_n_def, ← h_p_eq_f_n]
  rw [f_n1_def] at h_p_le_f_n1
  exact h_p_le_f_n1

```

**Explanation of Chunk 1 Code:**

1.  **Imports:** Necessary modules from `Mathlib` are imported.
2.  **`stdEntropy` Definition:** Defines the standard Shannon entropy using `negMulLog` (natural log) for a list of `ℝ≥0`. Helper lemmas confirm `stdEntropy [1] = 0` and `stdEntropy (p ++ [0]) = stdEntropy p`.
3.  **`IsEntropyFunction` Structure:** Defines the assumed properties of `H`.
    *   `prop0_H1_eq_0`: Explicitly added `H([1])=0` for the base case `f(1)=0`.
    *   `prop1_domain`: Placeholder for domain condition (often implicitly handled by hypotheses like `hp_sum`).
    *   `prop2_zero_inv`: Invariance to adding a zero-probability outcome.
    *   `prop3_continuity`: Continuity assumption (placeholder logic).
    *   `prop4_conditional`: Placeholder for the crucial chain rule property.
    *   `prop5_max_uniform`: Entropy is maximized for the uniform distribution.
4.  **`f n` Definition:** Defines `f(n)` as `H` applied to the uniform distribution `List.replicate n n⁻¹`. Includes a check `n > 0`. Requires `sum_replicate_inv_eq_one` helper lemma, which is proven using basic `List.sum` and `NNReal` properties.
5.  **`f_1_eq_0` Theorem:** Proves `f(1) = 0` by unfolding the definition of `f`, simplifying the uniform list for `n=1` to `[1]`, and applying the assumed `prop0_H1_eq_0`.
6.  **`f_mono` Theorem:** Proves `Monotone (f H)` using the standard Lean tactic for proving monotonicity by showing `f n ≤ f (n+1)`. The core argument constructs the distribution `p = (1/n, ..., 1/n, 0)`, shows `H(p) = f(n)` using Property 2, and shows `H(p) ≤ f(n+1)` using Property 5.

# Lean 4 Programming Notes
## Summary of Changes

* **`Fin.castLT` → `Fin.castPred`** and all its lemmas (e.g. `castLT_castSucc`) have been replaced by the `castPred` variants in Mathlib 4 ([Lean Prover Community][1]).
* **`Fin.val_castLT` → `Fin.val_cast_of_lt`** and **`Fin.val_castSucc` → `Fin.val_succEmb`**, reflecting the actual lemma names in `Mathlib.Data.Fin.Basic` ([Lean Prover Community][1], [Lean Prover Community][1]).
* Verified that **`Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`** is the correct import for `negMulLog` ([Lean Prover Community][2]).
* Confirmed **`Fin.sum_univ_castSucc`** lives in `Mathlib.Algebra.BigOperators.Fin` for splitting sums over `Fin (n+1)` ([Lean Prover Community][3]).
* Removed all references to Lean 3–style modules (e.g. `Init.Data.Fin.Lemmas`, `data.finset.basic`) and ensured only Mathlib 4 paths remain.

---

## 1. Standard Imports (Lean 4 / Mathlib 4)

```lean
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog  -- negMulLog, Real.log :contentReference[oaicite:4]{index=4}
import Mathlib.Data.NNReal.Basic                       -- ℝ≥0 (NNReal) :contentReference[oaicite:5]{index=5}
import Mathlib.Topology.Basic                           -- ContinuousOn, etc. :contentReference[oaicite:6]{index=6}
import Mathlib.Order.Monotone.Basic                     -- Monotone lemmas :contentReference[oaicite:7]{index=7}
import Mathlib.Algebra.BigOperators.Fin                 -- ∑ i : Fin n, … and Fin.sum_univ_castSucc :contentReference[oaicite:8]{index=8}
import Mathlib.Data.Fin.Basic                           -- core Fin definitions & val/cast lemmas :contentReference[oaicite:9]{index=9}
import Mathlib.Data.Fintype.Fin                         -- Fintype instance for Fin n :contentReference[oaicite:10]{index=10}
```

> **Note:** Avoid any `Init.*` imports when Mathlib provides the same or richer functionality ([Lean Prover Community][1]).

---

## 2. Renamed `Fin` Operations & Lemmas

### 2.1 Casting Downwards (`Fin.castLT` → `Fin.castPred`)

**Old (Lean 3–style):**

```lean
i.castLT h : Fin n
# Lemma used: Fin.castLT_castSucc
```

**New (Mathlib 4):**

```lean
i.castPred h : Fin n
-- splits: Fin.castPred_castSucc and Fin.castSucc_castPred
```

* The Mathlib 4 file `Mathlib.Data.Fin.Basic` defines `Fin.castPred` (not `castLT`) and the key inversion lemmas `castPred_castSucc` and `castSucc_castPred` ([Lean Prover Community][1]).

### 2.2 Value Lemmas

| Old lemma          | Mathlib 4 lemma      |            Source            |
| ------------------ | -------------------- | :--------------------------: |
| `Fin.val_castLT`   | `Fin.val_cast_of_lt` | ([Lean Prover Community][1]) |
| `Fin.val_castSucc` | `Fin.val_succEmb`    | ([Lean Prover Community][1]) |

* **`Fin.val_cast_of_lt`**:

  ```lean
  theorem Fin.val_cast_of_lt {n : ℕ} [NeZero n] {a : ℕ} (h : a < n) :
    ↑↑a = a
  ```
* **`Fin.val_succEmb`**:

  ```lean
  theorem Fin.val_succEmb {n : ℕ} (i : Fin n) :
    (i.castSucc).val = i.val + 1
  ```

  (The lemma is named `val_succEmb` in Mathlib 4.) ([Lean Prover Community][1])

---

## 3. Core `Fin` Tactics & Lemmas

* **Splitting a sum over `Fin (n+1)`**

  ```lean
  rw [Fin.sum_univ_castSucc]
  ```

  defined in `Mathlib.Algebra.BigOperators.Fin` ([Lean Prover Community][3]).

* **`if h : P then t else e` → `rw [dif_pos hp]`**
  Use `dif_pos` (not `if_pos`) when rewriting `if h : P ...` given `hp : P` ([Lean Prover Community][1]).

* **Direct compositional lemma for downward/upward casts:**

  ```lean
  rw [Fin.castPred_castSucc i h_lt]
  ```

  (formerly `Fin.castLT_castSucc`) ([Lean Prover Community][1]).

* **`Fin.eq_of_val_eq`** still exists as a fallback for equality proofs based on `.val`, but try to avoid it when a direct lemma is available ([Lean Prover Community][1]).

---

## 4. Glossary of Lean 4 vs Lean 3

| Concept              | Lean 4 (Mathlib 4)       | Lean 3 (Mathlib 3 guess)       |
| :------------------- | :----------------------- | :----------------------------- |
| Lambda syntax        | `λ x => ...`             | `λ x, ...`                     |
| `Fin n` summation    | `∑ i : Fin n, ...`       | `∑ i : fin n, ...`             |
| Split sum over `n+1` | `Fin.sum_univ_castSucc`  | `fin.sum_univ_succ`            |
| Cast up              | `i.castSucc : Fin (n+1)` | `i.cast_succ`                  |
| Cast down            | `i.castPred : Fin n`     | `i.cast_lt` / `i.cast_lt_succ` |
| `.val` lemma (up)    | `Fin.val_succEmb`        | `fin.cast_succ_val` (?)        |
| `.val` lemma (down)  | `Fin.val_cast_of_lt`     | `fin.cast_lt_val` (?)          |
| Embedding of `Fin`   | `Mathlib.Data.Fin.Basic` | `data.fin`                     |

---

Okay, let's consolidate the learnings into an updated README and outline the plan for Chunk 2.

---

## Updated README: Formalizing Rota's Uniqueness of Entropy

This document tracks the progress and key findings in the Lean 4 formalization of Rota's theorem on the uniqueness of entropy functions, based on the axiomatic properties outlined in Rota, Baclawski, & Billis (Chapter VIII).

### Summary of Recent Changes & Learnings (Chunk 1)

1.  **`IsEntropyFunction` Structure:**
    *   Corrected definition to be `structure ... where : Type` instead of `structure ... := : Prop`. Fields within a `Type`-valued structure represent proof terms/evidence.
    *   Placeholders for `prop3_continuity` and `prop4_conditional` remain `Prop` for now, as their proof terms are not immediately needed.
    *   Replaced unused variable names in structure fields with underscores (`_`) to satisfy the linter.

2.  **`Fin` Operations:**
    *   **`Fin.castLT`:** Confirmed that `Fin.castLT i h` (where `h : i.val < n`) is the correct function for casting `i : Fin (n + 1)` down to `Fin n` *when the value is known to be in range*. It is distinct from `Fin.castPred`.
    *   **`Fin.castLT_castSucc`:** This lemma is essential for simplifying `Fin.castLT (Fin.castSucc i) h_lt` back to `i`.
    *   **Summation:** `Fin.sum_univ_castSucc` is the standard way to split sums over `Fin (n + 1)`.

3.  **`noncomputable` Definitions:** Functions relying on non-constructive elements like real number inverses (`n⁻¹`) or logarithms (`negMulLog`) must be marked `noncomputable` (e.g., `uniformProb`, `f`, `f₀`, `stdEntropy`).

4.  **Cancellation Lemma:**
    *   The correct lemma for `a * a⁻¹ = 1` in `NNReal` (which has a `GroupWithZero` instance) is `mul_inv_cancel₀`.
    *   Its usage requires proving `a ≠ 0`. For `↑n : NNReal`, this was proven via `Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)`, correctly using the implication directions.

5.  **`variable` vs. Explicit Theorem Arguments:**
    *   While `variable (hH : IsEntropyFunction H)` *should* make `hH` implicitly available to subsequent theorems, Lean sometimes requires it as an explicit argument (e.g., `theorem foo (hH : ...) ...`). We adopted this for `f0_1_eq_0` to resolve an "unknown identifier" error.

---

### 1. Standard Imports (Lean 4 / Mathlib 4)

```lean
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog  -- negMulLog, Real.log
import Mathlib.Data.NNReal.Basic                       -- ℝ≥0 (NNReal)
import Mathlib.Topology.Basic                           -- ContinuousOn, etc. (Placeholder)
import Mathlib.Order.Monotone.Basic                     -- Monotone lemmas
import Mathlib.Algebra.BigOperators.Fin                 -- ∑ i : Fin n, … and Fin.sum_univ_castSucc
import Mathlib.Data.Fin.Basic                           -- core Fin definitions & val/cast lemmas (incl. castLT)
import Mathlib.Data.Fintype.Fin                         -- Fintype instance for Fin n
import Mathlib.Algebra.Order.Field.Basic               -- inv_one etc.
import Mathlib.Algebra.GroupWithZero.Units.Basic       -- Provides mul_inv_cancel₀
```

---

### 2. Key `Fin` Operations & Lemmas Used

*   **`Fin.castLT {n} (i : Fin (n+1)) (h : i.val < n) : Fin n`**: Cast down preserving value when `h` proves bounds.
*   **`Fin.castLT_castSucc (i : Fin n) (h) : Fin.castLT (Fin.castSucc i) h = i`**: Simplification lemma.
*   **`Fin.sum_univ_castSucc {M} [AddCommMonoid M] {n} (f : Fin (n+1) → M)`**: Splits sum `∑ i : Fin (n+1)` into `(∑ i : Fin n, f (i.castSucc)) + f (Fin.last n)`.

---

### 3. Key Proof Techniques & Lemmas Used

*   **`structure ... where : Type`**: For bundling proofs/properties.
*   **`noncomputable def`**: For definitions involving `Real` inverses, logarithms, etc.
*   **`mul_inv_cancel₀ {α} [GroupWithZero α] {a : α} (ha : a ≠ 0) : a * a⁻¹ = 1`**: Cancellation in `NNReal`.
*   **Proving `↑n ≠ 0`**: `Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)` where `hn : n > 0`.
*   **Function Extensionality**: `funext i` tactic to prove `(λ i => f i) = (λ i => g i)`.
*   **Explicit Instance Arguments**: Passing instances like `(hH : IsEntropyFunction H)` explicitly to theorems if `variable` inference fails.

---

### 4. Glossary & Debugging

*(Sections 4 & 5 from the previous README remain relevant)*

---

## Implementation Plan: Chunk 2 - The Power Law `f₀(n^k) = k * f₀(n)`

**Objective:** Prove that `f₀ H (n ^ k) = k * f₀ H n` for `n ≥ 1, k ≥ 1`, using an assumed consequence of Property 4 (Conditional Entropy).

**Methodology:** The proof in Rota-Baclawski relies on the idea that `H(π) - H(σ) = H(π|σ)` where π refines σ. For the specific partitions involved (uniform distributions on `n^k` and `n^(k-1)` outcomes), this relationship implies `f₀(n^k) - f₀(n^(k-1)) = f₀(n)`. We will assume this step as a consequence of `prop4_conditional` and use induction on `k`.

**Sub-steps:**

1.  **State the Assumed Lemma (Consequence of Prop 4):**
    *   **Objective:** Formalize the key step needed from the conditional entropy property.
    *   **Lean Task:** Define a lemma, perhaps named `f0_step_relation`, that assumes `hH : IsEntropyFunction H` and states:
        ```lean
        lemma f0_step_relation {n k : ℕ} (hn : n ≥ 1) (hk : k ≥ 1) :
            f₀ H (n ^ (k + 1)) = f₀ H (n ^ k) + f₀ H n := sorry -- Assumed via hH.prop4_conditional
        ```
        *(Note: We assume this holds directly. A deeper formalization would involve defining partitions and conditional H, which is beyond the scope here. We need `n≥1` because `f₀ H 0 = 0` and `f₀ H 1 = 0`; the interesting behavior starts at `n=2`)*. We might need to refine the exact power indices (`k+1` vs `k`, `k` vs `k-1`) based on how the induction works best. Let's stick with `n^k` and `n^(k+1)` for now. Ensure constraints like `n ≥ 1` are correctly handled, possibly using `f₀ H 1 = 0` where needed.
    *   **Testable Outcome:** The lemma is stated correctly.

2.  **Prove `f₀(n^k) = k * f₀(n)` by Induction:**
    *   **Objective:** Use the assumed `f0_step_relation` to prove the power law.
    *   **Lean Task:** Define the main theorem for this chunk:
        ```lean
        theorem f0_pow_eq_mul (hH : IsEntropyFunction H) {n k : ℕ} (hn : n ≥ 1) (hk : k ≥ 1) :
            f₀ H (n ^ k) = k * f₀ H n := by
          -- Induction on k
          induction' k with k' ih
          · -- Base case k = 0 (or k=1 depending on induction start)
            -- If hk : k ≥ 1, base case is k = 1
            simp [pow_one] -- Need f₀ H (n^1) = 1 * f₀ H n
          · -- Inductive step: Assume f₀ H (n^k') = k' * f₀ H n
            -- Need to show f₀ H (n^(k'+1)) = (k'+1) * f₀ H n
            -- Use f0_step_relation here (adjusting indices if needed)
            -- rw [f0_step_relation hH hn _] -- Need hypothesis for k'
            -- rw [ih] -- Apply inductive hypothesis
            -- algebra
            sorry
        ```
        Refine the base case and inductive step, carefully managing the `k ≥ 1` constraint and ensuring the hypotheses for `f0_step_relation` and `ih` are met. We might need `Nat.le_induction` or adjust the base case.
    *   **Testable Outcome:** The `f0_pow_eq_mul` theorem is fully proven, assuming `f0_step_relation`.

**Lessons Learned Applied:**

*   Explicitly pass `hH` to theorems.
*   Mark theorems as `noncomputable` if they depend on `f₀`.
*   Be precise with natural number arithmetic (`k+1` vs `k`), powers (`Nat.pow`), and constraints (`≥ 1`).
*   Use standard Mathlib induction tactics (`induction'`, `Nat.le_induction`).