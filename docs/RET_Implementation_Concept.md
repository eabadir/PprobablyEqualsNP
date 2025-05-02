# Implementation Plan: Formalizing Rota's Uniqueness of Entropy

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
