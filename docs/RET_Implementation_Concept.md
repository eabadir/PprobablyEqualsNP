# Implementation Plan: Formalizing Rota's Uniqueness of Entropy

**Goal:** Prove that any function `H` satisfying the 5 axiomatic properties of entropy must be equal to `C * stdShannonEntropyLn` for some constant `C ≥ 0`, where `stdShannonEntropyLn` is the standard Shannon entropy using the natural logarithm.

**Assumptions:** We assume a function `H : List ℝ≥0 → Real` exists and satisfies the 5 properties formalized in a structure `IsEntropyFunction`.

**Methodology:** Follow the proof structure outlined in the Rota-Baclawski text (Chapter VIII / Addendum in the paper).

**Chunks:**

1.  **Chunk 1: Setup, Definitions, and Basic Properties of `f(n)`COMPLETED**
    *   **Objective:** Define standard entropy (`stdShannonEntropyLn`), the `IsEntropyFunction` structure (assuming properties), define `f(n) = H(uniform n)`, and prove `f(1) = 0` and `f` is monotone non-decreasing.
    *   **Lean Tasks:**
        *   Import necessary libraries.
        *   Define `stdShannonEntropyLn` using `negMulLog`.
        *   Define `structure IsEntropyFunction` encapsulating the 5 properties (Property 4 might be stated abstractly initially or assumed via its consequences). Add `H([1]) = 0` as Prop 0, derivable from others but useful.
        *   Define `f n`.
        *   Prove helper lemma: `∑ (List.replicate n n⁻¹) = 1`.
        *   Prove `f 1 = 0` (using Prop 0).
        *   Prove `Monotone f` (using Prop 2 and Prop 5).
    *   **Testable Outcome:** Lean file compiles, definitions are type-correct, `f 1 = 0` and `Monotone f` theorems are proven.

2.  **Chunk 2: The Power Law `f(n^k) = k * f(n)` COMPLETED**
    *   **Objective:** Prove the key multiplicative property of `f`.
    *   **Lean Tasks:**
        *   Formalize (at least conceptually) the argument using Property 4 (Conditional Entropy: `H(π|σ) = H(π) - H(σ)`). Assume this property holds for `H`.
        *   Construct the partitions π and σ needed in the proof (conceptually: σ has `n^(k-1)` blocks, π refines it into `n^k` blocks).
        *   Show `H(π|σ) = f(n)` (average entropy within blocks of σ).
        *   Show `H(π|σ) = H(π) - H(σ) = f(n^k) - f(n^(k-1))`.
        *   Use induction on `k` or direct summation to prove `f(n^k) = k * f(n)`.
    *   **Testable Outcome:** Theorem `uniformEntropy_power_law (n k : ℕ) (hn : n > 0) (hk : k > 0) : f (n ^ k) = k * f n` is proven, likely assuming an abstract version of Property 4 or its direct consequence for this specific partition setup.

3.  **Chunk 3: Deriving `f(n) = C * log n` COMLETED**
    *   **Objective:** Show that the power law and monotonicity imply `f(n)` is proportional to `log n` (natural log).
    *   **Lean Tasks:**
        *   Define `C := f b / Real.log b` for some integer base `b > 1` (e.g., `b=2` or `b=3`). Or work towards `f(n)/f(2) = logb 2 n` as in the text, then convert to natural log.
        *   Prove `C ≥ 0`.
        *   Use the inequality argument from the text: For any `n, k`, find `b` such that `b^k ≤ n^m < b^(k+1)`. Apply `f` and `log`. Use monotonicity (`f(a) ≤ f(c)` if `a≤c`) and the power law (`f(b^k) = k f(b)`).
        *   Take the limit `m → ∞` (or argue via density) to show `f(n) / f(b) = Real.logb b n`.
        *   Conclude `f n = C * Real.log n`.
    *   **Testable Outcome:** Theorem `isCShannonEntropy : ∃ C ≥ 0, ∀ n > 0, f n = C * Real.log n` is proven.

4.  **Chunk 4: Extension to Rational Probabilities WIP**
    *   **Objective:** Show that `H(p) = C * stdShannonEntropyLn p` holds when `p` is a list of rational probabilities.
    *   **Lean Tasks:**
        *   Represent rational probabilities `pᵢ = aᵢ / N`.
        *   Again, use Property 4 conceptually. Construct partitions σ (blocks with probability `pᵢ`) and π (finer partition with `N` blocks of probability `1/N`).
        *   Show `H(π|σ) = ∑ pᵢ f(aᵢ) = ∑ pᵢ (C * log aᵢ)`.
        *   Show `H(π|σ) = H(π) - H(σ) = f(N) - H(σ) = C * log N - H(σ)`.
        *   Equate and solve for `H(σ)`: `H(σ) = C log N - C ∑ pᵢ log aᵢ = C ∑ pᵢ (log N - log aᵢ) = C ∑ pᵢ log (N/aᵢ) = C ∑ pᵢ log (1/pᵢ)`.
        *   Relate `∑ pᵢ log (1/pᵢ)` to `stdShannonEntropyLn p = ∑ negMulLog pᵢ = -∑ pᵢ log pᵢ`. Need `log(1/x) = -log x`. `H(σ) = C * stdShannonEntropyLn p`.
        *   Handle types carefully (rationals vs reals, `List ℚ≥0` vs `List ℝ≥0`).
    *   **Testable Outcome:** Theorem `h_rational : ∀ (p : List ℚ≥0)..., H (p.map cast) = C * stdShannonEntropyLn (p.map cast)` is proven.

5.  **Chunk 5: Extension to Real Probabilities**
    *   **Objective:** Use continuity (Property 3) to extend the result from rational to real probabilities.
    *   **Lean Tasks:**
        *   Use `hH.prop3_continuity`.
        *   Use density of rational lists/vectors in the space of real probability vectors.
        *   Apply standard limit arguments: approximate real `p` by rational `q`, show `H(q) → H(p)` and `C * stdShannonEntropyLn q → C * stdShannonEntropyLn p`.
    *   **Testable Outcome:** Theorem `h_real : ∀ (p : List ℝ≥0)..., H p = C * stdShannonEntropyLn p` is proven.

6.  **Chunk 6: Final Theorem Assembly**
    *   **Objective:** State the final `rota_uniqueness_of_entropy` theorem and combine the results from previous chunks.
    *   **Lean Tasks:**
        *   State the theorem formally using `∃ C ≥ 0`.
        *   The proof body combines the existence of `C` from Chunk 3 and the final equality from Chunk 5.
    *   **Testable Outcome:** The main theorem is fully proven.

---
# CURRENT IMPLEMENTATION PHASE

This provides the break down the plan for Chunk 4, aiming for a combinatorial approach rooted in Property 4.

**Chunk 4: Extension to Rational Probabilities**

**Goal:** Prove that for any probability distribution `p` with rational values, `H(p) = C * stdShannonEntropyLn(p)`, where `C = C_constant H` is the non-negative constant found in Chunk 3 (`uniformEntropy_eq_C_log`).

**Theorem Statement (Lean Target):**

```lean
theorem rational_entropy_eq_C_stdEntropyLn
    (hH : IsEntropyFunction H) (C : ℝ) (hC_def : C = C_constant H) (hC_prop : ∀ n ≥ 1, uniformEntropy_product_recursion H n = C * Real.log n)
    {n : ℕ} (p_rat : Fin n → ℚ) (hp_nn : ∀ i, 0 ≤ p_rat i) (hp_sum : ∑ i, p_rat i = 1) :
    let p_real := fun i => (p_rat i : ℝ)
    -- We need H to operate on distributions represented e.g., as Fin n → ℝ≥0
    -- Need to bridge from Fin n → ℚ≥0 to Fin n → ℝ≥0 satisfying sum = 1 for H's input
    -- Assume a helper function `H_real (p : Fin n → ℝ≥0) (h_sum : ∑ i, p i = 1)` that wraps H
    H_real p_nnreal hp_nnreal_sum = C * stdShannonEntropyLn p_nnreal := sorry -- Placeholder for body and precise H signature
```
*(Note: Handling the input type for H (`Fin n → NNReal`, `Fin n → Real`, `List Real`?) and the transition from `ℚ` needs care. We'll assume H operates on `Fin n → NNReal` where the sum is 1).*

**Implementation Steps:**

1.  **Preprocessing and Setup:**
    *   **Input:** `p_rat : Fin n → ℚ≥0` such that `∑ i, p_rat i = 1`.
    *   **Convert to Real:** Define `p_real : Fin n → ℝ≥0 := fun i => (p_rat i : ℝ≥0)`. Prove `∑ i, p_real i = 1`. This `p_real` is the distribution we want to evaluate `H` on.
    *   **Find Common Denominator:** Use lemmas from `Data.Rat.Denumerator` or similar (or prove manually) to find a natural number `N ≥ 1` and a function `a : Fin n → ℕ` such that for all `i`, `p_rat i = a i / N`.
        *   *Lemma Needed:* `exists_common_denominator {n} (p : Fin n → ℚ≥0) : ∃ (N : ℕ) (hN : N ≥ 1) (a : Fin n → ℕ), (∀ i, p i = (a i : ℚ) / (N : ℚ)) ∧ (∑ i, a i = N)`.
        *   We need $N \ge 1$. Since $\sum p_i = 1$ and $p_i \ge 0$, at least one $p_i > 0$, which means at least one $a_i > 0$, so $N = \sum a_i \ge 1$.
    *   **Define `C`:** Let `C := C_constant H`. We know `C ≥ 0` from `C_constant_nonneg`. We also have the result `uniformEntropy_eq_C_log`: `∀ k ≥ 1, f₀ H k = C * Real.log k`.

2.  **Define the Probability Space and Partitions (Conceptual):**
    *   **Space $\Omega$:** A set with $N$ equiprobable outcomes. Formalize using `Fin N`. The probability measure $P$ assigns $1/N$ to each singleton.
    *   **Fine Partition $\pi$:** The partition of $\Omega$ into $N$ singletons. The distribution on the blocks of $\pi$ is uniform: `uniform_N : Fin N → NNReal := fun _ => (N : NNReal)⁻¹`.
    *   **Coarse Partition $\sigma$:** Partition $\Omega$ into $n$ blocks $B_0, B_1, ..., B_{n-1}$ such that block $B_i$ contains $a_i$ elements from $\Omega$.
        *   Formally, define `B_i : Finset (Fin N)`. For example, using cumulative sums of `a`: `B_i := Finset.Ico (∑_{j=0}^{i-1} a j) (∑_{j=0}^{i} a j)`.
        *   Prove these sets form a partition of `Fin N`.
        *   Calculate the probability of each block: `P(B_i) = Finset.card B_i / N = a_i / N = (p_rat i : ℝ)`. Let `p_sigma : Fin n → NNReal` be this distribution. Show `p_sigma = p_real`.
    *   **Refinement:** Prove that $\pi$ is a refinement of $\sigma$ (trivial, as singletons are subsets of the blocks $B_i$).

3.  **Formalize and Apply Property 4 (Chain Rule):**
    *   **Assumption:** Property 4 needs to be formalized functionally within `IsEntropyFunction`. We assume `hH` provides:
        `prop4_chain_rule {N : ℕ} (π σ : Partition (Fin N)) (h_refine : IsRefinement π σ) : H(distr_of_partition π) = H(distr_of_partition σ) + H_conditional(H, π, σ)`
        *(Need precise definitions of `Partition`, `distr_of_partition`, `H_conditional`)*
    *   **Alternative (Direct Consequence):** We might assume a more direct consequence related to this specific construction, avoiding full partition theory formalization:
        `prop4_special_case {n N : ℕ} (a : Fin n → ℕ) (hN : N = ∑ i, a i) (hN_pos : N ≥ 1) : H(uniform N) = H(p_sigma) + ∑ i, p_sigma i * f₀ H (a i)`
        where `p_sigma i = a i / N`. This directly encodes the result of the conditional entropy calculation. Let's assume this `prop4_special_case`.

4.  **Calculate Terms using Chunk 3 Results:**
    *   **`H(uniform N)`:** Since $N \ge 1$, apply `uniformEntropy_eq_C_log`:
        `H(uniform N) = f₀ H N = C * Real.log N`.
    *   **`f₀ H (a i)`:** For each $i$, if $a_i \ge 1$, apply `uniformEntropy_eq_C_log`:
        `f₀ H (a i) = C * Real.log (a i)`.
        If $a_i = 0$, then $p_sigma i = 0$. We know `f₀ H 0 = 0`. The term `p_sigma i * f₀ H (a i)` becomes `0 * 0 = 0`.
        The formula `f₀ H k = C * Real.log k` technically requires $k \ge 1$. We need to handle the $a_i=0$ case carefully in the sum.

5.  **Apply Property 4 and Solve for `H(p_sigma)`:**
    *   Using `prop4_special_case`:
        `C * Real.log N = H(p_sigma) + ∑ i, (p_sigma i : ℝ) * f₀ H (a i)`
    *   Isolate `H(p_sigma)`:
        `H(p_sigma) = C * Real.log N - ∑ i, (p_sigma i : ℝ) * f₀ H (a i)`
    *   Substitute `f₀ H (a i) = C * Real.log (a i)` for $a_i \ge 1$. The terms where $a_i=0$ have $p_sigma i = 0$, so the corresponding term in the sum is `0 * f₀ H 0 = 0`. The substitution `f₀ H (a i) = C * Real.log (a i)` can be viewed as holding even for $a_i=0$ if we interpret $0 * \log 0 = 0$. However, `Real.log 0` is problematic.
    *   *Safer approach:* Split the sum over `i` where `a i > 0` and `a i = 0`.
        `H(p_sigma) = C * Real.log N - ∑_{i | a i > 0} (p_sigma i : ℝ) * (C * Real.log (a i))`
        `H(p_sigma) = C * [Real.log N - ∑_{i | a i > 0} (p_sigma i : ℝ) * Real.log (a i)]`
    *   Bring `Real.log N` inside the sum using `∑ p_sigma i = 1`:
        `Real.log N = (∑ i, p_sigma i) * Real.log N = (∑_{i | a i > 0} p_sigma i) * Real.log N` (since terms with $p_sigma i = 0$ vanish).
        `H(p_sigma) = C * [ (∑_{i | a i > 0} p_sigma i) * Real.log N - ∑_{i | a i > 0} p_sigma i * Real.log (a i) ]`
        `H(p_sigma) = C * ∑_{i | a i > 0} p_sigma i * (Real.log N - Real.log (a i))`
        `H(p_sigma) = C * ∑_{i | a i > 0} p_sigma i * Real.log (N / a i)`
    *   Since `p_sigma i = a i / N`, then `N / a i = 1 / p_sigma i` for $a_i > 0$.
        `H(p_sigma) = C * ∑_{i | a i > 0} p_sigma i * Real.log (1 / p_sigma i)`
        `H(p_sigma) = C * ∑_{i | a i > 0} p_sigma i * (- Real.log (p_sigma i))`
        `H(p_sigma) = C * (- ∑_{i | a i > 0} p_sigma i * Real.log (p_sigma i))`

6.  **Connect to `stdShannonEntropyLn`:**
    *   Recall `stdShannonEntropyLn p = ∑ i, negMulLog (p i) = - ∑_{i | p i > 0} p i * Real.log (p i)`. The definition using `negMulLog` correctly handles the $p_i=0$ terms.
    *   The sum we derived for `H(p_sigma)` is exactly `C * stdShannonEntropyLn(p_sigma)`.
    *   Since `p_sigma = p_real` (the distribution corresponding to the input rationals), we have:
        `H(p_real) = C * stdShannonEntropyLn(p_real)`

7.  **Address Formalization Details:**
    *   **Type of H:** Clarify if `H` takes `Fin n → NNReal`, `List NNReal`, `PMF (Fin n)`, etc. Ensure the input `p_real` matches.
    *   **Property 4 Formalization:** This is the main dependency. Assuming `prop4_special_case` makes this chunk feasible. Proving `prop4_special_case` from a more general `prop4_chain_rule` requires formalizing partitions and conditional entropy.
    *   **Logarithm Properties:** Need `Real.log_div`, `Real.log_inv`, relationship between `negMulLog` and `- x * log x`. These are available in Mathlib.
    *   **Summation Properties:** Manipulating sums, especially splitting based on conditions (`a i > 0`), requires standard `Finset.sum` lemmas.
    *   **Rational/Real/NNReal:** Careful casting and ensuring properties hold across types (e.g., `∑ (a i / N : ℝ) = 1`). Use `NNReal` (`ℝ≥0`) where possible for probabilities.

**Chunk 4 Summary:**

This chunk proves the main theorem for rational probabilities by:
1.  Representing the rational distribution `p` using a common denominator `N` and numerators `aᵢ`.
2.  Constructing a probability space with $N$ uniform outcomes and two partitions: $\pi$ (singletons) and $\sigma$ (blocks $B_i$ of size $a_i$).
3.  Applying Property 4 (likely a specialized version for this setup) relating `H(uniform N)`, `H(p)`, and the conditional term `∑ pᵢ f₀(aᵢ)`.
4.  Substituting the known formula `f₀(k) = C * log k` (from Chunk 3) into the Property 4 equation.
5.  Performing algebraic manipulations involving logarithms and sums, carefully handling $p_i=0$ cases, to show that `H(p) = C * (- ∑ pᵢ log pᵢ)`.
6.  Recognizing the final sum as `C * stdShannonEntropyLn(p)`.

This approach is combinatorial in spirit (using partitions derived from the rational structure) and directly relies on the key axiomatic property (Property 4) and the result established for uniform distributions.