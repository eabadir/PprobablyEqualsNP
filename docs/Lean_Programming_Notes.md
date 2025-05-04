
# Lean 4 Programming Notes - IMPORTANT! 
This is a record of what we've been overcoming in the implementation of Rota's Entropy Theorem in Lean 4. **READ THIS SO WE DON'T REPATE THE SAME MISTAKES!**

Debugging Entropy.PowerLaw.lean — Post-mortem


Explanation of the Error

You’re seeing:

type mismatch
  h_pow_le
has type
  ↑b ^ ↑⌊logb (↑b) x⌋₊ ≤ x : Prop
but is expected to have type
  ↑b ^ ⌊logb (↑b) x⌋₊ ≤ x : Prop

Lean is telling you that the type of your hypothesis h_pow_le involves one more explicit coercion (the second ↑) than the goal expects. Even though mathematically
↑b ^ ↑\lfloor \log_b x\rfloor  \quad\text{and}\quad ↑b ^ \lfloor \log_b x\rfloor
are definitionally equal in ℝ, Lean’s kernel distinguishes between:
	•	↑(k : ℕ) — an explicit coercion from ℕ to ℝ
	•	an implicit coercion that Lean inserts automatically when needed

In your proof, you called the lemma

pow_le_of_floor_logb_mul_log_le_log
  (hb : b ≥ 2) (hx : x ≥ 1)
  (h_mul_log : (k : ℝ) * Real.log b ≤ Real.log x)

with k := Nat.floor (Real.logb b x). That lemma’s conclusion is

(b : ℝ) ^ (k : ℝ) ≤ x

where (k : ℝ) is used explicitly in the statement. Your hypothesis h_pow_le therefore has the form

(b : ℝ) ^ (k : ℝ) ≤ x

but in your goal you wrote

(b : ℝ) ^ k ≤ x

omitting the explicit cast on k. Lean parses ^ k in a context expecting a real exponent as meaning “coerce k : ℕ to ℝ implicitly, then use that as the real exponent.” Internally, this is still ↑b ^ ↑k, but Lean does not automatically treat that as definitionally equal to the version with two ↑ markers when unifying.

The Meaning of “↑”

In Lean:
	•	↑a is notation for coe a, i.e. the application of a Coe instance to convert a from one type to another (here ℕ → ℝ)  ￼.
	•	You can write (a : ℝ) or ↑a to explicitly coerce a : α to β when Lean cannot infer it implicitly.
	•	In many cases, Lean will insert that coercion automatically when the types don’t match, so you can write b : ℝ and b + 1 without writing ↑b + 1.

However, Lean’s definitional equality (what it uses for unification) does not always reduce away these explicit coercions if they’re inserted differently. Therefore, (↑b ^ ↑k) and (↑b ^ k) can fail to unify, even though they are provably equal.

How to Fix It

You have two main options:
	1.	Match your hypothesis to the goal exactly by inserting the explicit cast on k in your goal. For example:

have h_pow_le' : (b : ℝ) ^ (Nat.floor (Real.logb b x)) ≤ x := by
  exact h_pow_le  -- now matches exactly

Or by writing your goal as:

show (b : ℝ) ^ (Nat.floor (Real.logb b x) : ℝ) ≤ x


	2.	Erase the extra explicit coercions from your hypothesis before using it. You can use by rfl or a small lemma that ↑k = (k : ℝ) is definitionally true, or simply clear and reintroduce with an implicit cast:

have : (b : ℝ) ^ (Nat.floor (Real.logb b x) : ℝ) ≤ x := by
  simpa using h_pow_le



Either way, the key is to make the exact same coercions appear on both sides so that Lean’s definitional unifier can see them as equal.

⸻

References
	•	Coercion notation (↑a) in Lean 4: how it corresponds to Coe instances and implicit vs. explicit casts  ￼.
	•	Explanation of coercions in the Lean 4 manual: using ↑ to disambiguate and how implicit coercion works  ￼.
	•	Terry Tao’s blog on Lean 4: noting that uparrows are coercion symbols and can usually be ignored for simple arithmetic proofs  ￼.
⸻

1 · Initial pain-points

Problem	Symptom in Lean	Root cause
Pattern-matching failures	tactic 'rewrite' failed, did not find instance…	Rewrite attempts didn’t match because the goal contained extra casts (↑m) or the factor order differed (c * … vs … * c).
Obsolete recursor	Unknown constant Nat.induction_from_le	Mathlib 3 recursor removed; Lean 4 uses Nat.le_induction.
Ring equalities not closing	ring succeeds sometimes, but still produces unsolved goals or suggests ring_nf.	ring_nf normalises only; ring both normalises and solves commutative-ring equalities.
Elaborator confusion	“type mismatch”, “insufficient number of arguments”, or unused variables warnings.	Over-packed helper lemmas with implicit arguments Lean couldn’t infer; unused hH param triggered linter.



⸻

2 · Strategy: atomise the proof

We switched from a monolithic proof script to a layer of micro-lemmas:
	1.	Arithmetic identities (add_mul_right, cast_add_one_real) — one-line ring/rfl proofs.
	2.	Entropy step f0_step_relation kept as a single ‟axiom” (sorry) so the higher logic could compile.
	3.	Predicate P defined locally for clarity:
P m ≔ f₀ H (n ^ m) = m • f₀ H n.
	4.	Base case handled by simp [pow_one, one_mul].
	5.	Induction step split into:
	•	rewrite via f0_step_relation;
	•	replace f₀ H (n^m) using IH;
	•	finish with add_mul_right+ring.
	6.	Modern recursor: replaced Nat.induction_from_le with Nat.le_induction.

Breaking points fixed along the way:

Breakdown	Fix	Lesson
Algebraic RW mismatch (↑m * c + c vs c * ↑(1+m))	New lemma add_mul_right + ring; kept factor order consistent.	For pure ring goals, ring is the one-liner; ring_nf; rfl needs an extra commutativity step.
Missing arguments in Nat.le_induction	Supplying explicit starting point m := 1 and target k hk.	Modern recursors need the bound, the goal index, and the proof that bound ≤ index.
Unused variable warning	Renamed hH → _hH.	Use leading underscore for intentional dead params; keeps linter quiet.
Helper clutter	Deleting now-unused bulky lemmas.	Once micro-lemmas stabilise, prune to keep the file readable.



⸻

3 · Outcome
	•	Compiles cleanly: the final script uses only three tiny helper lemmas and one inductive block; no more pattern-matching surprises.
	•	Tactic clarity: simp, ring, and Nat.le_induction each used exactly where they shine.
	•	Maintainability: every proof obligation is isolated; future edits localise errors instead of cascading.

⸻

4 · Take-aways
	1.	Prefer one-purpose lemmas; keep them one-line if possible (ring, simp).
	2.	Distinguish ring vs ring_nf:
	•	ring → solve the whole equality.
	•	ring_nf → only normalise inside a bigger goal.
	3.	Update to Lean 4 idioms: Nat.le_induction, trailing _ in unused names, no legacy recursors.
	4.	Delete scaffolding early: removing obsolete helpers avoids ghost errors and keeps code approachable.

This incremental decomposition let us pinpoint each misunderstanding, correct it with a targeted lemma or clearer tactic, and converge to a short, robust proof.
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

** Additional Stumbling Blocks In Chunk 1:**
Here’s a concise recap of the stumbling‐blocks we ran into in Entropy.Basic.lean (specifically in the proof of f0_mono) and the steps we took to resolve each:
	1.	Missing lemma Nat.not_pos_zero
	•	Symptom: simp only […, dif_neg (Nat.not_pos_zero 0)] failed because Mathlib4/Lean 4 no longer defines Nat.not_pos_zero.
	•	Fix: Swapped in core lemmas such as Nat.not_lt_zero 0 (or Nat.lt_irrefl 0 / by decide) to discharge ¬0 < 0.
	2.	rewrite not finding f₀ 1 = 0
	•	Symptom: In the n = 0 branch, simp wiped out the f₀ 1 pattern before rw [f0_1_eq_0 hH] could fire, so the rewrite silently failed.
	•	Fix: Reordered the tactics: first rw [f0_1_eq_0 hH] (so f₀ 1 becomes 0), then simp only [f₀, dif_neg …].
	3.	Bad argument to prop2_zero_inv
	•	Symptom: We tried hH.prop2_zero_inv H unif_n h_sum_n, but prop2_zero_inv expects only the distribution and its sum proof, not an extra H.
	•	Fix: Dropped the spurious H argument:

exact hH.prop2_zero_inv unif_n h_sum_n


	4.	“Failed to infer binder type” on the λ for uniformProb (n+1)
	•	Symptom: Lean couldn’t infer the domain of the anonymous function in prop5_max_uniform.
	•	Fix: Annotated the binder explicitly:

H p ≤ H (λ _ : Fin (n + 1) => uniformProb (n + 1))

and also removed the extra H argument to prop5_max_uniform.

	5.	Type‐mismatch in the prop5_max_uniform inequality
	•	Symptom: We were manually rewriting the uniform distribution to match uniformProb and then calling prop5_max_uniform, but the intermediate lambda shape still didn’t line up.
	•	Fix: Simplified the whole step by calling prop5_max_uniform directly and then using simpa to fold in the uniformProb definition:

have h5 := hH.prop5_max_uniform hn1_pos p h_sum_p
simpa [uniformProb, hn1_pos] using h5



With these five adjustments—using the correct core lemmas, reordering rw/simp, dropping extra arguments, annotating binder types, and collapsing the uniform‐prob rewrite into a single simpa—the proof of f0_mono now checks smoothly under Lean 4 / Mathlib4.