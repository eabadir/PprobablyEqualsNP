# Meticulous Comparison of Chunk 3 Completion Plan Against Lean 4 Construct Constraints

## 1. Introduction

This report presents a meticulous comparison of the proposed plan for completing Chunk 3 of the Lean 4 project against the specified constraint of utilizing only previously established Lean 4 constructs originating from the files `Entropy.Basic.lean`, `Entropy.PowerLaw.lean`, and the completed parts of `Entropy.LogFormula.lean`. 

The analysis involves a step-by-step examination of the intended Lean 4 lemmas and functions for various sub-sections within Chunk 3, namely 3.3, 3.4, and 3.6, as well as an investigation into the availability of a crucial lemma for the limit argument in Chunk 3.5. The primary objective is to verify the source of each planned construct and determine if it adheres to the project's strict import limitations.

## 2. Search for Limit Uniqueness Lemma (Instructions 1-3)

### 2.1 Search within `Data.Real.Basic`

The initial phase of the analysis focused on determining if the Lean 4 library `Data.Real.Basic` contains a lemma equivalent to `eq_of_abs_sub_le_all: ∀ {x y : ℝ}, (∀ ε > 0, |x - y| ≤ ε) → x = y` or `eq_of_forall_abs_lt_eps: ∀ {x y : ℝ}, (∀ ε > 0, |x - y| < ε) → x = y`. This type of lemma is fundamental for proving the uniqueness of limits, a likely requirement for Chunk 3.5. Documentation 1 describes `Data.Real.Basic` as defining the real numbers, denoted as ℝ, through the concept of equivalence classes of Cauchy sequences derived from rational numbers. The library's primary purpose is to establish the foundational algebraic structure of real numbers, demonstrating that they form a commutative ring. To maintain simplicity in imports, properties related to the order and completeness of real numbers, such as the Archimedean property and the conditional completeness as a linear order, are intentionally deferred to other files, specifically `Mathlib.Data.Real.Archimedean.lean`.1 Given this design, it is improbable that `Data.Real.Basic` would contain a lemma directly addressing the uniqueness of limits based on the absolute difference being arbitrarily small, as such a property is inherently linked to the order and metric completeness of the real number system, which are treated in separate modules.

### 2.2 Search within `Analysis.SpecificLimits.Basic`

The investigation then extended to the `Analysis.SpecificLimits.Basic` library, as this module is dedicated to specific computations involving limits. The rationale was that even if a general lemma for limit uniqueness was absent in `Data.Real.Basic`, a specialized version or a lemma that could be used to derive the required property might exist here. An examination of the contents of `Mathlib.Analysis.SpecificLimits.Basic` 4 reveals a comprehensive collection of theorems focused on the limits of particular sequences and functions. These include results concerning inverse and division by natural numbers, filter eventually equal theorems, `tendsto` (tends to) theorems involving division and infinity, the behavior of powers as the exponent goes to infinity, properties of geometric series, sequences with geometrically decaying distances in metric spaces, summability tests based on comparison with geometric series, positive sequences with small sums on countable types, the factorial function, and the ceil and floor functions. While this library offers a rich set of tools for working with limits, the detailed breakdown of its contents does not indicate the presence of a lemma directly equivalent to `eq_of_abs_sub_le_all` or `eq_of_forall_abs_lt_eps`. The focus of this module appears to be on applying fundamental limit properties to specific cases rather than providing the foundational properties themselves.

### 2.3 Investigation of Alternative Lemmas within Imported Libraries

Recognizing that the sought-after lemma might not reside in the initially targeted libraries, the inquiry broadened to encompass the set of currently imported libraries: `Real`, `NNReal`, `Fin`, `Nat`, `Log`, `Logb`, `Pow`, `rpow`, `Floor`, `BigOperators`, `Topology.Basic`, `Topology.Order.Basic`, `Analysis.SpecificLimits.Basic`, `Order.Monotone.Basic`, `Algebra.*`, `Tactic.*`. The uniqueness of limits is a concept intimately connected with the properties of topological spaces, particularly Hausdorff spaces, where distinct points possess disjoint neighborhoods. The real numbers, when equipped with their standard metric, form a Hausdorff space. The library `Topology.Basic` 5 lays the groundwork for topological spaces, defining key concepts such as neighborhoods and limits. The fact that the real numbers inherit a topology from their metric structure suggests that a lemma related to the uniqueness of limits might be found within this topological framework.8 While `Logic.Basic` 9 provides fundamental logical constructs and `Order.Basic` 10 deals with order relations, these are less likely to contain a real-number-specific lemma for limit uniqueness. Interestingly, a tutorial solution file, `tuto_lib.lean` 12, does contain the lemma `eq_of_abs_sub_le_all`, indicating its utility within the Lean 4 community. However, its presence in a tutorial rather than the core libraries suggests it might be located in a different module or require a specific import not yet considered.

A potential alternative approach to proving the limit argument in Chunk 3.5, specifically the step `(∀ m ≥ 1, |L - R| < 1 / m) → L = R`, involves leveraging the Archimedean property of real numbers. Although the formal definition of this property resides in `Mathlib.Data.Real.Archimedean.lean`, which is not among the initially specified allowed imports, it's possible that its consequences or related lemmas are accessible through the imported `Real` type or other transitive imports. The condition `|L - R| < 1/m` for all `m ≥ 1` implies that the non-negative value `|L - R|` is smaller than every positive number of the form `1/m`. The Archimedean property ensures that for any positive real number, there exists a natural number `m` such that `1/m` is smaller than it. This characteristic can be used to demonstrate that `|L - R|` must be equal to zero, thus proving `L = R`. Lemma `zero_via_1_over_n` from Lean 3 3 provides a precedent for this approach, establishing the equivalence between a similar condition and `x = 0`. Determining the availability of its Lean 4 equivalent or the necessary components to construct such a proof within the currently imported libraries is crucial.

## 3. Analysis of Chunk 3.3 Plan (Instructions 4-5)

### 3.1 Identify Planned Lemmas and Functions

The specific plan for Chunk 3.3 was not provided. The following analysis assumes the plan intends to utilize constructs commonly employed in basic algebraic manipulations involving natural and real numbers. Let's hypothesize the plan includes:
- `Nat.cast`: For converting natural numbers to real numbers.
- Basic arithmetic operations: addition (+), subtraction (-), multiplication (*).
- Potentially lemmas from `Algebra.Ring.Nat` related to ring properties of natural numbers.
- The explicitly allowed `f0_mono` and `f0_pow_eq_mul`.
- The explicitly allowed real division `/`.

### 3.2 Verify Origin of Identified Elements

The function `Nat.cast`, used to embed natural numbers into the real numbers, is likely permissible. Snippets 14 confirm that `Nat` is the standard type for natural numbers in Lean 4. Furthermore, the presence of the `NatCast ℝ` instance within `Data.Real.Basic`, as shown in 1, suggests that this functionality is likely accessible through the imported `Real` type or similar modules. The explicit allowance of `Data.Nat.Cast.Order` further supports the permissibility of operations involving casting natural numbers to ordered types. Basic arithmetic operations such as addition, subtraction, and multiplication on real numbers are fundamental to the structure of `Real` and are expected to be available within the imported environment. Snippet 1 explicitly lists instances for `Add`, `Neg`, `Mul`, and `Sub` in `Data.Real.Basic`, reinforcing their likely availability. The import `Algebra.Ring.Nat` is explicitly permitted by instruction (5), meaning any lemma directly originating from this file is compliant with the constraints. Finally, the functions `f0_mono` and `f0_pow_eq_mul`, along with real division `/`, are explicitly listed as allowed constructs in instruction (5).

### 3.3 Insights and Analysis for Chunk 3.3

Based on the assumption that the plan for Chunk 3.3 relies on constructs similar to those hypothesized, it appears that the plan is likely to adhere to the specified import constraints. The key is that basic operations involving natural numbers, their casting to reals, fundamental arithmetic on reals, and any lemmas directly from `Algebra.Ring.Nat`, along with the explicitly allowed elements, are all likely to be permissible. A definitive assessment, however, requires a detailed review of the specific lemmas and functions intended for use in the actual plan.

## 4. Analysis of Chunk 3.4 Plan (Instructions 6-7)

### 4.1 Identify Planned Lemmas and Functions

The specific plan for Chunk 3.4 was not provided. Let's assume the plan intends to utilize:
- `Nat.floor`: To compute the floor of a real number.
- `Real.logb_pow`: A lemma concerning the logarithm of a power with a specific base.
- Real division `/`.

### 4.2 Verify Origin of Identified Elements

The function `Nat.floor`, which returns the greatest integer less than or equal to a given real number, is likely to have its fundamental properties accessible. Snippet 4 mentions theorems in `Analysis.SpecificLimits.Basic` that utilize `Nat.floor`, such as `tendsto_nat_floor_div_atTop`, suggesting that the properties of `Nat.floor` are either defined within this module or in its imported dependencies, which could include `Data.Real.Basic`. Instruction (7) further indicates that these fundamental properties are likely to originate from `Data.Real.Basic`. Real division `/` is explicitly allowed as per instruction (7). However, instruction (7) clearly states that `Real.logb_pow`, a lemma likely concerning the property `log_b(x^y) = y * log_b(x)`, originates from `Analysis.SpecialFunctions.Log.Base`. This library is not included in the initial list of allowed imports for the entire chunk.

### 4.3 Insights and Analysis for Chunk 3.4

The most critical observation for Chunk 3.4 is the potential violation of the import constraints due to the planned use of `Real.logb_pow`. As per instruction (7), this lemma is sourced from `Analysis.SpecialFunctions.Log.Base`, a library that is not among the allowed imports for Chunk 3. If the plan for this sub-section indeed relies on `Real.logb_pow`, it will contravene the project's rules. The report will need to highlight this discrepancy and suggest exploring alternative approaches that do not depend on this specific lemma or involve proving the required logarithmic property using only allowed constructs.

## 5. Analysis of Chunk 3.6 Plan (Instruction 8)

### 5.1 Identify Planned Lemmas and Functions

The specific plan for Chunk 3.6 was not provided. Let's assume the plan intends to utilize:
- Division.
- The proven lemma `Real.log 2 > 0`.
- The proven lemma `f₀ H 2 ≥ 0`.
- `Real.logb_eq_log_div_log`: A lemma expressing the change of base formula for logarithms.
- Basic algebraic manipulations.

### 5.2 Verify Origin of Identified Elements

Division is explicitly allowed by instruction (8). The proven lemmas `Real.log 2 > 0` and `f₀ H 2 ≥ 0` are also permissible as they are established within the project's scope. However, instruction (8) explicitly states that `Real.logb_eq_log_div_log`, which likely expresses the identity `log_b(x) = log(x) / log(b)`, originates from `Analysis.SpecialFunctions.Log.Base`. Similar to the situation in Chunk 3.4, this library is not among the allowed imports for the entire chunk. Therefore, if the plan for Chunk 3.6 includes `Real.logb_eq_log_div_log`, it will constitute a violation of the project's constraints. While instruction (8) permits "basic algebraic manipulations," it is crucial to ensure that these manipulations do not implicitly rely on lemmas or tactics that originate from disallowed libraries. For instance, using powerful tactics like `ring` or `field_simp` might inadvertently invoke a broader set of algebraic identities than those directly available from the base algebraic structures within the allowed imports. Therefore, a careful and potentially more manual approach to algebraic manipulation might be necessary to guarantee compliance.

### 5.3 Insights and Analysis for Chunk 3.6

The primary concern for Chunk 3.6 is the potential violation arising from the planned use of `Real.logb_eq_log_div_log`, which, according to instruction (8), comes from a disallowed library. Additionally, while basic algebraic manipulations are allowed, the plan needs to be scrutinized to confirm that these operations are performed using only the fundamental algebraic properties likely available through the base structures provided by the allowed imports, without inadvertently relying on more advanced lemmas or tactics from restricted libraries.

## 6. Conclusion

The analysis of the proposed plan for completing Chunk 3 reveals potential challenges related to adherence to the specified constraints on allowed Lean 4 constructs.

### Recommendations:

- **Chunks 3.4 and 3.6:** Explore alternative methods for achieving the required logarithmic properties using only the allowed constructs. If no alternatives exist, consider re-evaluating the import restrictions.
- **Chunk 3.5:** Investigate proving the step `(∀ m ≥ 1, |L - R| < 1 / m) → L = R` using the Archimedean property or topological properties within the imported `Topology.Basic` library.
- **Chunk 3.3 and 3.6:** Finalize the specific plans and meticulously verify each intended lemma and function against the allowed origins.

By carefully considering these recommendations, the development team can ensure the project adheres to its constraints and progresses effectively.

## Works Cited

1. Mathlib.Data.Real.Basic - Lean community, accessed May 2, 2025, [link](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Real/Basic.html)
2. data.real.basic - mathlib3 docs - Lean community, accessed May 2, 2025, [link](https://leanprover-community.github.io/mathlib_docs/data/real/basic.html)
3. mathlib3/src/data/real/basic.lean at master - GitHub, accessed May 2, 2025, [link](https://github.com/leanprover-community/mathlib/blob/master/src/data/real/basic.lean)
4. Mathlib.Analysis.SpecificLimits.Normed - Lean community, accessed May 2, 2025, [link](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecificLimits/Normed.html)
5. mathlib4/Mathlib/Topology/Basic.lean at master - GitHub, accessed May 2, 2025, [link](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Basic.lean)
6. Maths in Lean: Topological, uniform and metric spaces, accessed May 2, 2025, [link](https://leanprover-community.github.io/theories/topology.html)
7. topology.basic - mathlib3 docs - Lean community, accessed May 2, 2025, [link](https://leanprover-community.github.io/mathlib_docs/topology/basic.html)
8. Mathematics in mathlib - Lean community, accessed May 2, 2025, [link](https://leanprover-community.github.io/mathlib-overview.html)
9. Mathlib.Logic.Basic - Lean community, accessed May 2, 2025, [link](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Basic.html)
10. Mathlib.Order.Basic - Lean community, accessed May 2, 2025, [link](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Basic.html)
11. order.basic - mathlib3 docs - Lean community, accessed May 2, 2025, [link](https://leanprover-community.github.io/mathlib_docs/order/basic.html)
12. tutorials/src/solutions/tuto_lib.lean at master - GitHub, accessed May 2, 2025, [link](https://github.com/leanprover-community/tutorials/blob/master/src/solutions/tuto_lib.lean)
13. Exploring Formalisation - Clara Löh - Universität Regensburg, accessed May 2, 2025, [link](https://loeh.app.uni-regensburg.de/mapa/main.pdf)
14. How does one import Natural numbers in Lean 4 -- unknown identifier 'ℕ'?, accessed May 2, 2025, [link](https://proofassistants.stackexchange.com/questions/3890/how-does-one-import-natural-numbers-in-lean-4-unknown-identifier-%E2%84%95)
