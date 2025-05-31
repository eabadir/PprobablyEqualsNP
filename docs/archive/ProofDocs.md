
**Key Principles Of OurLemma Organization:**
Below is the list of lemmas and how they are currently Organized. 
1.  **Generality:** Most general lemmas (basic math, algebra, real analysis, Nat/Fin properties) go into `PPNP/Common/Basic.lean`.
2.  **Domain Specificity:**
    *   Definitions and lemmas core to complexity theory go to `PPNP/Complexity/Basic.lean`.
    *   General definitions/lemmas about entropy functions or probability distributions (not specific to one physical model or RET's `f₀`) go to `PPNP/Entropy/Common.lean`.
    *   Definitions/lemmas common to *multiple* physical statistical models (MB, FD, BE) go to `PPNP/Entropy/Physics/Common.lean`.
    *   Highly specific proofs and definitions stay within their current modules (e.g., Bose-Einstein specific combinatorics in `BoseEinstein.lean`, RET proof machinery in `RET.lean`).
3.  **Dependency:** If `A` depends on `B`, `B` should be in an equally or more general location.
4.  **Mathlib Alignment:** Some very general lemmas that used to exist in Lean 3 but did not get ported to Lean 4 have been replicated.
5.  **`Dev` folder:** Items in `Dev` are  experimental, duplicates, or candidates for integration into the main structure. 

Here's the table:

| Item                                                 | Short Description                                                                    | Current File                        |
| :--------------------------------------------------- | :----------------------------------------------------------------------------------- | :---------------------------------- |
|                                                      |                                                                                      |                                     |
| `nnreal_coe_nat_mul`                                 | `(↑n * m : ℝ≥0) = (↑(n * m) : ℝ≥0)`                                                  | PPNP/Common/Basic.lean (Keep)       |
| `nnreal_prod_inv_self_eq_one_prod`                   | `(a * a⁻¹) * (b * b⁻¹) = 1 * 1` for `a,b ≠ 0` in `ℝ≥0`                               | PPNP/Common/Basic.lean (Keep)       |
| `nnreal_mul_prod_inv_prod_rearrange`                 | `(a * b) * (a⁻¹ * b⁻¹) = (a * a⁻¹) * (b * b⁻¹)` in `ℝ≥0`                               | PPNP/Common/Basic.lean (Keep)       |
| `nnreal_inv_mul_inv_eq_inv_mul`                      | `a⁻¹ * b⁻¹ = (a * b)⁻¹` in `ℝ≥0` for `a,b ≠ 0`                                      | PPNP/Common/Basic.lean (Keep)       |
| `cast_add_one_real`                                  | `↑(m + 1) = ↑m + 1` for `m : ℕ` to `ℝ`                                               | PPNP/Common/Basic.lean (Keep)       |
| `add_mul_right`                                      | `↑m * c + c = (↑m + 1) * c` for `m : ℕ, c : ℝ`                                       | PPNP/Common/Basic.lean (Keep)       |
| `one_lt_cast_of_ge_two`                              | `b ≥ 2 → 1 < (b : ℝ)`                                                                | PPNP/Common/Basic.lean (Keep)       |
| `cast_pos_of_ge_two`                                 | `b ≥ 2 → 0 < (b : ℝ)`                                                                | PPNP/Common/Basic.lean (Keep)       |
| `floor_logb_le`                                      | `⌊logb b x⌋ ≤ logb b x`                                                              | PPNP/Common/Basic.lean (Keep)       |
| `log_b_pos`                                          | `log b > 0` for `b ≥ 2`                                                              | PPNP/Common/Basic.lean (Keep)       |
| `logb_mul_log_eq_log`                                | `logb b x * log b = log x`                                                           | PPNP/Common/Basic.lean (Keep)       |
| `floor_logb_mul_log_le_log`                          | `⌊logb b x⌋ * log b ≤ log x`                                                          | PPNP/Common/Basic.lean (Keep)       |
| `rpow_le_of_mul_log_le_log`                          | `y * log b ≤ log x → b ^ y ≤ x` (Real power)                                         | PPNP/Common/Basic.lean (Keep)       |
| `rpow_floor_logb_le_x`                               | `b ^ ⌊logb b x⌋ ≤ x` (Real power on cast floor)                                       | PPNP/Common/Basic.lean (Keep)       |
| `pow_nat_floor_logb_le_x`                            | `b ^ ⌊logb b x⌋ ≤ x` (Nat power)                                                      | PPNP/Common/Basic.lean (Keep)       |
| `x_lt_pow_succ_floor_logb`                           | `x < b ^ (⌊logb b x⌋ + 1)` (Nat power)                                                | PPNP/Common/Basic.lean (Keep)       |
| `exists_nat_pow_bounds`                              | `∃ k, b^k ≤ x < b^(k+1)` (Nat power)                                                 | PPNP/Common/Basic.lean (Keep)       |
| `exists_k_log_bounds`                                | (Duplicate of `exists_nat_pow_bounds`)                                               | PPNP/Common/Basic.lean (Remove)     |
| `one_le_pow_of_one_le_real`                          | `1 ≤ b → 1 ≤ b^k` for `b : ℝ, k : ℕ`                                                 | PPNP/Common/Basic.lean (Keep)       |
| `one_le_rpow_cast_pow`                               | `n ≥ 1 → 1 ≤ (n:ℝ)^(m:ℝ)`                                                            | PPNP/Common/Basic.lean (Keep)       |
| `one_le_pow_cast`                                    | `n ≥ 1 → 1 ≤ (n:ℝ)^m` (Nat power)                                                    | PPNP/Common/Basic.lean (Keep)       |
| `one_le_implies_pos`                                 | `x ≥ 1 → 0 < x` for `x : ℝ`                                                          | PPNP/Common/Basic.lean (Keep)       |
| `logb_le_logb_of_le`                                 | Monotonicity of `logb b x`                                                           | PPNP/Common/Basic.lean (Keep)       |
| `logb_pow_eq_self`                                   | `logb b (b^k) = k` (Nat exponent)                                                    | PPNP/Common/Basic.lean (Keep)       |
| `k_le_logb_rpow`                                     | `b^k ≤ x → k ≤ logb b x`                                                             | PPNP/Common/Basic.lean (Keep)       |
| `logb_lt_logb_of_lt`                                 | Strict monotonicity of `logb b x`                                                    | PPNP/Common/Basic.lean (Keep)       |
| `logb_rpow_lt_k_plus_1`                              | `x < b^(k+1) → logb b x < k+1`                                                       | PPNP/Common/Basic.lean (Keep)       |
| `logb_rpow_bounds_k`                                 | `∃ k, logb b x - 1 < k ∧ k ≤ logb b x`                                               | PPNP/Common/Basic.lean (Keep)       |
| `logb_rpow_eq_mul_logb`                              | `logb b (n^m) = m * logb b n` (Real exponent m)                                      | PPNP/Common/Basic.lean (Keep)       |
| `logb_pow_eq_mul_logb_nat`                           | `logb b (n^m) = m * logb b n` (Nat exponent m)                                       | PPNP/Common/Basic.lean (Keep)       |
| `prove_logb_x_eq`                                    | `x = n^m → logb b x = m * logb b n` (Real exp, using `logb_rpow_eq_mul_logb`)        | PPNP/Common/Basic.lean (Keep)       |
| `prove_logb_x_eq_nat`                                | `x = n^m → logb b x = m * logb b n` (Nat exp, using `logb_pow_eq_mul_logb_nat`)      | PPNP/Common/Basic.lean (Keep)       |
| `logb_x_bounds_k`                                    | `b^k ≤ x < b^(k+1) → logb b x - 1 < k ∧ k ≤ logb b x`                                | PPNP/Common/Basic.lean (Keep)       |
| `logb_n_times_m_bounds_k`                            | Translates `logb x` bounds to `m * logb n` bounds                                    | PPNP/Common/Basic.lean (Keep)       |
| `logb_n_bounds_k_div_m`                              | Converts `m * logb n` bounds to `logb n` bounds by division                          | PPNP/Common/Basic.lean (Keep)       |
| `lt_add_iff_sub_left_real`                           | `a < b + c ↔ a - c < b` for `a,b,c : ℝ`                                              | PPNP/Common/Basic.lean (Keep)       |
| `helper_neg_div`                                     | `-(a / b) = -a / b`                                                                  | PPNP/Common/Basic.lean (Keep)       |
| `helper_neg_sub`                                     | `-(a - b) = b - a`                                                                   | PPNP/Common/Basic.lean (Keep)       |
| `le_add_iff_sub_left_real`                           | `a ≤ b + c ↔ a - b ≤ c` for `a,b,c : ℝ`                                              | PPNP/Common/Basic.lean (Keep)       |
| `exists_one_le_nat_one_div_le`                       | Archimedean helper: `∀ ε > 0, ∃ m ≥ 1, 1/m ≤ ε`                                      | PPNP/Common/Basic.lean (Keep)       |
| `pos_of_ge_one`                                      | `1 ≤ x → 0 < x` for `x : ℝ`                                                          | PPNP/Common/Basic.lean (Keep)       |
| `pos_of_one_le`                                      | `1 ≤ n → 0 < n` for `n : ℕ`                                                          | PPNP/Common/Basic.lean (Keep)       |
| `logb_eq_log`                                        | `logb b x = log x / log b`                                                           | PPNP/Common/Basic.lean (Keep)       |
| `one_le_iff_pos`                                     | `1 ≤ n ↔ 0 < n` for `n : ℕ`                                                          | PPNP/Common/Basic.lean (Keep)       |
| `uniformProb`                                        | Uniform probability `1/n` as `NNReal`                                                | PPNP/Entropy/Common.lean            |
| `sum_uniform_eq_one`                                 | Sum of `uniformProb` over `Fin n` is 1                                               | PPNP/Entropy/Common.lean            |
|                                                      |                                                                                      |                                     |
| `Word`, `Machine`, `wordLength`, etc.                | Core computational primitives and complexity definitions (`P`, `NP`, `SAT_problem`)    | PPNP/Complexity/Basic.lean (Keep)   |
|                                                      |                                                                                      |                                     |
| `sum_replicate_count_toFinset_eq_self`               | `∑ replicate (count i s) i = s` (multiset sum) - (Duplicate of BE version)           | (Remove, use BE version or Common)  |
| `right_inv_beState_multiset`                         | `beStateToMultiset (multisetToBEStateSubtype s) = s.val` - (Duplicate of BE version) | (Remove, use BE version)            |
|                                                      |                                                                                      |                                     |
| `uniformDist` (List Real version)                    | Simplified `uniformDist` for MWE                                                     | (Experimental, likely remove/refactor) |
| `length_uniformDist`, `filter_decide_gt_zero_*` etc. | Helpers for local `uniformDist`                                                      | (Experimental, likely remove/refactor) |
|                                                      |                                                                                      |                                     |
| `IsProbDist`                                         | Predicate for `List Real` probability distribution                                   | PPNP/Entropy/Common.lean            |
| `uniformDist` (List Real version)                    | Uniform distribution as `List Real`                                                  | PPNP/Entropy/Common.lean            |
| `uniformDist_IsProbDist`                             | Proof that `uniformDist` (List Real) is `IsProbDist`                                 | PPNP/Entropy/Common.lean            |
| `EntropyFunction`                                    | Type alias `List Real → Real` for entropy functions                                  | PPNP/Entropy/Common.lean            |
| `ShannonEntropyFunc`                                 | Shannon Entropy for `List Real` using `logb 2`                                       | PPNP/Entropy/Common.lean            |
| `EntropyProperty0`, `EntropyProperty2`, `EntropyProperty5` | Axiomatic properties for `EntropyFunction` (List Real)                             | PPNP/Entropy/RET.lean (adapt/merge) |
| `IsContinuousEntropy`                                | Axiom for continuity of `EntropyFunction` (List Real)                                | PPNP/Entropy/RET.lean (adapt/merge) |
| `HasEntropyProperties`                               | Structure bundling properties for `EntropyFunction` (List Real)                      | PPNP/Entropy/RET.lean (adapt/merge) |
|                                                      |                                                                                      |                                     |
| `MBMacrostate`                                       | `{ q : Fin N → ℕ // ∑ i, q i = M }`                                                  | PPNP/Entropy/Physics/Common.lean    |
| `SymFin`                                             | `Sym (Fin N) M` (multisets of size M over Fin N)                                     | PPNP/Entropy/Physics/Common.lean    |
| `OmegaBE`                                            | `MBMacrostate N M` (alias for BE state space)                                        | PPNP/Entropy/Physics/BoseEinstein.lean (Keep) |
| `Multiset.count_finset_sum`                          | `count a (∑ f i) = ∑ (count a (f i))`                                                | PPNP/Common/Basic.lean              |
| `beStateToMultiset`                                  | Converts `OmegaBE` occupancy vector to `Multiset (Fin N)`                            | PPNP/Entropy/Physics/BoseEinstein.lean (Keep) |
| `card_beStateToMultiset`                             | `card (beStateToMultiset q) = M`                                                     | PPNP/Entropy/Physics/BoseEinstein.lean (Keep) |
| `multisetToBEState`                                  | Converts `Multiset (Fin N)` to occupancy function `Fin N → ℕ`                        | PPNP/Entropy/Physics/BoseEinstein.lean (Keep) |
| `sum_count_eq_card`                                  | `∑ (count i s) = card s` for multiset `s`                                            | PPNP/Common/Basic.lean              |
| `count_replicate_term_zero`                          | `i ≠ j → count i (replicate (q j) j) = 0`                                            | PPNP/Entropy/Physics/BoseEinstein.lean (Keep, helper) |
| `count_replicate_term_eq`                            | `count i (replicate (q i) i) = q i`                                                  | PPNP/Entropy/Physics/BoseEinstein.lean (Keep, helper) |
| `sum_count_replicate_eq_single_term`                 | `∑ j, count i (replicate (q j) j) = q i`                                             | PPNP/Entropy/Physics/BoseEinstein.lean (Keep, helper) |
| `count_beStateToMultiset_eq_sum_count_replicate`     | `count i (beStateToMultiset q) = ...` (distributes count)                            | PPNP/Entropy/Physics/BoseEinstein.lean (Keep, helper) |
| `replicate_count_zero_of_not_mem`                    | `i ∉ s → replicate (count i s) i = 0`                                                | PPNP/Common/Basic.lean              |
| `multisetToBEStateSubtype`                           | Bundles `multisetToBEState` with proof for `OmegaBE` type                            | PPNP/Entropy/Physics/BoseEinstein.lean (Keep) |
| `left_inv_beState_multiset`                          | Proves `multisetToBEStateSubtype (beStateToMultiset q) = q`                          | PPNP/Entropy/Physics/BoseEinstein.lean (Keep) |
| `sum_replicate_count_univ_eq_sum_toFinset`           | Sum over `univ` equals sum over `s.toFinset` for `replicate (count i s) i`          | PPNP/Entropy/Physics/BoseEinstein.lean (Keep, helper) |
| `toFinset_cons`                                      | `(a :: s).toFinset = insert a s.toFinset` (Likely in Mathlib)                        | PPNP/Common/Basic.lean (If not in Mathlib) |
| `count_cons_self`                                    | `count a (a :: s) = count a s + 1` (Likely in Mathlib)                               | PPNP/Common/Basic.lean (If not in Mathlib) |
| `count_cons_ne`                                      | `i ≠ a → count i (a :: s) = count i s` (Likely in Mathlib)                           | PPNP/Common/Basic.lean (If not in Mathlib) |
| `replicate_split`                                    | `replicate (n+1) a = replicate 1 a + replicate n a` (Likely `replicate_add` in Mathlib) | PPNP/Common/Basic.lean (If not in Mathlib) |
| `sum_congr_count`                                    | `(∀ i, f i = g i) → ∑ f i = ∑ g i` (Finset.sum_congr)                                | PPNP/Common/Basic.lean (If not in Mathlib) |
| `sum_replicate_count_nil`                            | Sum over empty toFinset is empty multiset                                            | PPNP/Common/Basic.lean              |
| `sum_insert_split`, `count_cons_ne'`, etc.          | Micro-helpers for `sum_replicate_count_toFinset_eq_self` proof                     | PPNP/Entropy/Physics/BoseEinstein.lean (Keep, helper) |
| `sum_replicate_count_toFinset_eq_self`               | `∑ i ∈ s.toFinset, replicate (count i s) i = s`                                      | PPNP/Entropy/Physics/BoseEinstein.lean (Keep) |
| `right_inv_beState_multiset`                         | Proves `beStateToMultiset (multisetToBEStateSubtype s) = s.val`                      | PPNP/Entropy/Physics/BoseEinstein.lean (Keep) |
|                                                      |                                                                                      |                                     |
| `f`, `f₀`                                            | `H(uniform n)` and its extension to `n=0`                                            | PPNP/Entropy/RET.lean (Keep)        |
| `C_constant`                                         | Constant `C` relating `f₀` to `log`                                                  | PPNP/Entropy/RET.lean (Keep)        |
| `stdShannonEntropyLn`                                | Shannon entropy for `Fin n → NNReal` using natural log                               | PPNP/Entropy/Common.lean            |
| `probabilitySimplex`                                 | Set `{p : Fin n → NNReal // ∑ p i = 1}`                                              | PPNP/Entropy/Common.lean            |
| `product_dist`                                       | Product distribution `(p q)_{ij} = p_i q_j` for `Fin n → NNReal`                     | PPNP/Entropy/Common.lean            |
| `uniformProb_product_uniformProb_is_uniformProb`     | Product of uniform `NNReal` distributions is uniform                                 | PPNP/Entropy/Common.lean            |
| `IsEntropyFunction`                                  | Structure for axiomatic entropy function (`Fin n → NNReal` version)                  | PPNP/Entropy/RET.lean (Keep)        |
| `sum_p_ext_eq_one`                                   | Helper for `prop2_zero_inv`: sum of extended dist is 1                               | PPNP/Entropy/RET.lean (Keep, helper)|
| `stdShannonEntropyLn_p_ext_eq_stdShannonEntropyLn`   | Helper for `prop2_zero_inv` if `H` is `stdShannonEntropyLn`                        | PPNP/Entropy/RET.lean (Keep, helper)|
| `f0_mul_eq_add_f0`, `f0_1_eq_0`, `f0_mono`, etc.     | All lemmas building up to `RotaEntropyTheorem` using `f₀`                            | PPNP/Entropy/RET.lean (Keep)        |
| `cast_le_cast`                                       | `a ≤ b → ↑a ≤ ↑b` for `ℕ` to `ℝ` (Duplicate)                                         | (Remove, use Common/Basic.lean)     |
| `exists_pow_ge`                                      | `1 < a → ∃ k, n ≤ a^k` (Duplicate)                                                   | (Remove, use Common/Basic.lean)     |
| `exists_pow2_bound`                                  | `n ≥ 1 → ∃ k ≥ 1, n ≤ 2^k` (Duplicate, uses `exists_pow_ge`)                         | (Remove, use Common/Basic.lean)     |
| `nat_bounds_from_cast_pow_bounds`                    | `(b:ℝ)^k ≤ (n:ℝ)^m → b^k ≤ n^m` etc. (Nat powers)                                   | PPNP/Common/Basic.lean              |
| `div_bounds_from_mul_bounds`                         | `A*C ≤ B*D ∧ B*D ≤ E*C → A/D ≤ B/C ∧ B/C ≤ E/D`                                      | PPNP/Common/Basic.lean              |
| `eq_of_abs_sub_le_inv_ge_one_nat`                    | `(∀ m ≥ 1, |x-y| ≤ 1/m) → x = y`                                                     | PPNP/Common/Basic.lean              |
| `rearrange_ratio_equality`                           | `a/b = c/d → a = (b/d)*c`                                                            | PPNP/Common/Basic.lean              |
| `RotaEntropyTheorem`                                 | Main theorem: `∃ C ≥ 0, f H n = C * log n`                                           | PPNP/Entropy/RET.lean (Keep)        |
|                                                      |                                                                                      |                                     |
| Axioms, Lemmas, and Theorem                          | All items are part of the final P=NP argument.                                       | PPNP/PequalsNP.lean (Keep)          |

**Summary of Target Files and Key Items to Move:**

*   **`PPNP/Common/Basic.lean`:**
    *   Many detailed `Real.logb`, `Nat.floor`, power, and casting interaction lemmas (currently there, confirm they are general enough or if some are too RET-specific).
    *   General `ℝ≥0` arithmetic.
    *   General `Real` arithmetic helpers (e.g., `lt_add_iff_sub_left_real`).
    *   Archimedean property helpers (e.g., `exists_one_le_nat_one_div_le`).
    *   Basic `Nat`/`Real` inequalities and equivalences.
    *   `Multiset.count_finset_sum`, `sum_count_eq_card` (from BE).
    *   `replicate_count_zero_of_not_mem`, `sum_replicate_count_nil` (from BE).
    *   `nat_bounds_from_cast_pow_bounds`, `div_bounds_from_mul_bounds`, `eq_of_abs_sub_le_inv_ge_one_nat`, `rearrange_ratio_equality` (from RET).
    *   Potentially some simple multiset helpers from BE if they are not in Mathlib (`toFinset_cons`, etc.).

*   **`PPNP/Entropy/Common.lean`:** (This file would be newly populated or expanded)
    *   `uniformProb` (from Common/Basic)
    *   `sum_uniform_eq_one` (from Common/Basic)
    *   `IsProbDist` (from Dev/RET_Sketch)
    *   `uniformDist` (List Real version from Dev/RET_Sketch, reconcile with `uniformProb`)
    *   `uniformDist_IsProbDist` (from Dev/RET_Sketch)
    *   `EntropyFunction` (type alias from Dev/RET_Sketch)
    *   `ShannonEntropyFunc` (from Dev/RET_Sketch)
    *   `stdShannonEntropyLn` (from RET)
    *   `probabilitySimplex` (from RET)
    *   `product_dist` (from RET)
    *   `uniformProb_product_uniformProb_is_uniformProb` (from RET)

*   **`PPNP/Entropy/Physics/Common.lean`:** (This file would be newly populated or expanded)
    *   `MBMacrostate` (from BoseEinstein)
    *   `SymFin` (from BoseEinstein)

**Notes on Duplicates and `Dev` folder:**

*   The `Dev` folder items are largely experimental or early versions. for our purpose, they can be ignored. 
This reorganization makes the project structure more logical and easier to navigate, with dependencies flowing from general utility modules to more specific application modules.