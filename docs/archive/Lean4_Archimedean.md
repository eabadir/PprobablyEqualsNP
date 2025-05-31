# Lean 4 Constructs Related to the Archimedean Property of Real Numbers

## 1. Introduction

The Archimedean property is a foundational concept in the study of real numbers. It essentially states that for any two positive real numbers, one can always find a multiple of the smaller number that exceeds the larger one. This seemingly simple idea has profound implications, serving as a cornerstone for many fundamental results in mathematical analysis, including the theory of limits, the completeness of the real number system, and the density of rational numbers within the reals. Understanding and formalizing this property is crucial for building a rigorous framework for real analysis in any formal system.

This report aims to identify and describe useful constructs available in the Lean 4 theorem prover's Mathlib library that are specifically related to the Archimedean property of real numbers. By examining relevant typeclasses and lemmas, we can gain insight into how this essential property is formalized and utilized within a powerful interactive theorem prover. The primary focus will be on constructs found within the `Mathlib.Algebra.Order.Archimedean.Basic` module, which is dedicated to defining and proving properties related to the Archimedean nature of ordered algebraic structures. Additionally, this report will explore relevant constructs from other modules within Mathlib, such as `Mathlib.Analysis.SpecificLimits.Basic` and `Mathlib.Data.Real.Basic`, to provide a comprehensive overview. The formalization of the Archimedean property in Lean 4 provides a robust foundation for verifying analytical results that rely on the interplay between discrete and continuous quantities.

## 2. Fundamental Archimedean Constructs

The core formalization of the Archimedean property in Lean 4 is achieved through the `Archimedean` typeclass, which is defined within the `Mathlib.Algebra.Order.Archimedean.Basic` module. This typeclass is designed to apply to ordered additive commutative monoids, providing a general framework for reasoning about this property across various algebraic structures. The definition of the `Archimedean` typeclass is expressed by the proposition:

```lean
arch (x : M) {y : M} : 0 < y → ∃ (n : ℕ), x ≤ n • y
```

This statement formally captures the essence of the Archimedean property: for any two elements `x` and `y` in the monoid `M`, if `y` is strictly greater than zero, then there exists a natural number `n` such that `x` is less than or equal to the result of adding `y` to itself `n` times (using the additive operation denoted by `•`).

Lean 4 recognizes that the real numbers (`ℝ`) satisfy this fundamental property and provides an instance of the `Archimedean` typeclass for `ℝ`. This declaration signifies that all the theorems and lemmas that are formulated based on the `Archimedean` typeclass are directly applicable to real numbers within the Lean 4 environment. Consequently, the `Archimedean.arch` lemma becomes a primary tool for directly invoking the Archimedean property when constructing proofs involving real numbers. While Mathlib also defines the `MulArchimedean` typeclass for ordered commutative monoids, which relates to the multiplicative version of the property, the primary focus for real numbers in analysis typically remains on the additive Archimedean property. The typeclass system in Lean 4 thus allows for a high level of abstraction and generality in formalizing mathematical concepts, ensuring that fundamental properties like the Archimedean one are both widely applicable and readily usable for specific mathematical objects like the real numbers.

## 3. Existence of Natural Number Bounds

Several lemmas within the `Mathlib.Algebra.Order.Archimedean.Basic` module explicitly address the existence of natural number bounds for elements residing in Archimedean ordered rings and fields. These lemmas are crucial for establishing that the set of natural numbers is unbounded above within the real number system. Among these:

```lean
exists_nat_ge {α : Type u_1} [ordered_ring α][archimedean α] (x : α) : ∃ (n : ℕ), x ≤ ↑n
```

This lemma asserts that for any element `x` in an Archimedean ordered ring `α`, one can always find a natural number `n` (which is explicitly coerced to the type `α` using the notation `↑n`) that is greater than or equal to `x`. A related lemma:

```lean
exists_nat_gt {α : Type u_1} [strict_ordered_ring α][archimedean α] (x : α) : ∃ (n : ℕ), x < ↑n
```

provides a similar result but with a strict inequality, applicable to Archimedean strict ordered rings.

These lemmas are fundamental when proving that for any given real number `r`, there exists a natural number `n` such that `n > r`. This can be achieved by directly applying the `exists_nat_gt` lemma with the real numbers as the underlying type (`α = ℝ`). The distinction in the preconditions of these lemmas, specifically between `ordered_ring` and `strict_ordered_ring`, highlights the precision of Lean 4's type system. It emphasizes that the exact algebraic structure plays a significant role when formalizing mathematical properties. Furthermore, the notation `↑n` is essential to understand, as it represents the explicit coercion of a natural number into the target type `α` (which in the context of real numbers, facilitates operations and comparisons between natural and real numbers). Lean's strong typing necessitates such explicit coercions when working across different number types. Similar lemmas also exist for integers, such as `exists_int_gt` and `exists_int_lt`, which can be valuable when dealing with bounds related to real numbers through the natural embedding of integers into the reals.

## 4. Convergence of 1/(n+1) to Zero

The property that for every positive real number `ε`, there exists a natural number `n` such that `1 / (n + 1) < ε` is a direct consequence of the Archimedean property and is frequently used in the foundations of real analysis. In Lean 4, the general concept of a sequence converging to a limit is formalized using the `Filter.Tendsto` construct. The relevant lemma that captures the behavior of the sequence `1/(n+1)` is found in `Mathlib.Analysis.SpecificLimits.Basic` and is stated as:

```lean
tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto (fun (n : ℕ) => 1 / (n + 1)) Filter.atTop (nhds 0)
```

This lemma formally expresses that the sequence defined by the function mapping a natural number `n` to the real number `1 / (n + 1)` converges to the limit `0` as `n` approaches infinity. The phrase "as `n` approaches infinity" is represented by the filter `Filter.atTop`, and the convergence to `0` is indicated by the filter of neighborhoods around `0`, denoted as `nhds 0`. The connection to the Archimedean property becomes clear when considering the epsilon-delta definition of a limit. Given any `ε > 0`, the Archimedean property guarantees the existence of a natural number `N` such that `1/ε < N + 1`. This inequality can be rearranged to `1/(N + 1) < ε`, thus demonstrating that for any chosen level of precision `ε`, we can find a point in the sequence (specifically, after the index `N`) where the terms are closer to `0` than `ε`. The `tendsto` lemma provides a more abstract and powerful way to express this idea of convergence within the framework of filters, which is a unifying concept in Mathlib for dealing with various types of limits. The lemma `tendsto_one_div_add_atTop_nhds_zero_nat` is a specific instance within the extensive collection of limit results provided by Mathlib, particularly within the `Analysis.SpecificLimits` hierarchy.

## 5. Lemma for Non-Negative Real Numbers Less Than 1/n

A fundamental consequence of the Archimedean property is that if a non-negative real number `x` is smaller than `1/n` for all positive natural numbers `n`, then `x` must be equal to zero. While Mathlib might not contain a single lemma with this exact phrasing, this property can be readily proven using existing constructs within the library. One common strategy involves proof by contradiction, leveraging the Archimedean property itself.

Assume, for the sake of contradiction, that `x > 0`. Since `x` is assumed to be positive, `1/x` is also a well-defined positive real number. By the Archimedean property, as formalized by lemmas like `exists_nat_gt`, there must exist a natural number `n` such that `n > 1/x`. Multiplying both sides of this inequality by the positive quantity `x/n`, we obtain `x > 1/n`. This result directly contradicts the initial hypothesis that `x < 1/n` for all positive natural numbers `n`. Therefore, our initial assumption that `x > 0` must be false, leading to the conclusion that `x = 0`. Snippet 8 from Lean 3 shows a related lemma `zero_via_1_over_n`, which establishes an equivalence between the convergence of `1/n` to zero and the fact that `0 < 1`, hinting at the foundational nature of this concept. Additionally, snippet 9 defines a lemma `eq_of_abs_sub_le_all`, which states that if the absolute difference between two real numbers is less than or equal to all positive epsilon, then they are equal. This principle can also be used to prove the desired property. If `0 ≤ x` and `∀ n > 0, x < 1/n`, then for any `ε > 0`, we can find an `n` such that `1/n < ε`, implying `0 ≤ x < ε`, and thus `x = 0`. The absence of a dedicated lemma for this specific statement might suggest that it is considered a straightforward consequence of more fundamental principles within Mathlib, encouraging users to either construct the short proof themselves or utilize closely related lemmas.

## 6. Density of Rational Numbers

The density of rational numbers within the real numbers is a crucial property stating that between any two distinct real numbers, there exists at least one rational number. This property has significant implications in real analysis and highlights the intricate relationship between the rational and real number systems. `Mathlib.Algebra.Order.Archimedean.Basic` provides the key lemma for formalizing this property in Lean 4:

```lean
exists_rat_btwn {α : Type u_1} [linear_ordered_field α][archimedean α] (x y : α) (hxlt : x < y) : ∃ (q : ℚ), x < ↑q ∧ ↑q < y
```

This lemma asserts that given two elements `x` and `y` from an Archimedean linear ordered field `α` (which includes the real numbers), if `x` is strictly less than `y`, then there exists a rational number `q` (coerced to the type `α` using `↑q`) that is strictly greater than `x` and strictly less than `y`. The proof of this lemma typically relies on the Archimedean property to establish the existence of a natural number `n` large enough such that the interval `(x, y)` has a width greater than `1/n`. By considering integer multiples of `1/n`, one can then locate a rational number within this interval. The presence of `exists_rat_btwn` within the Archimedean module emphasizes the strong connection between the Archimedean property and the density of rational numbers. The preconditions of the lemma, specifically `linear_ordered_field`, indicate that this property relies not only on the Archimedean nature of the reals but also on their field structure and total ordering. Lemmas such as `exists_rat_gt` and `exists_rat_lt`, which state that for any real number, there exists a rational number greater than it and another rational number less than it, respectively, further support reasoning about the relationship between these two number systems.

## 7. Conclusion

The Mathlib library in Lean 4 offers a comprehensive and well-structured formalization of the Archimedean property of real numbers. Through the `Archimedean` typeclass and a rich set of associated lemmas, Mathlib provides the necessary tools for rigorously verifying mathematical results that depend on this fundamental property. Key constructs identified in this report include the `Archimedean.arch` lemma, which directly embodies the definition of the property, and lemmas such as `exists_nat_ge` and `exists_int_lt` that establish the unboundedness of natural and integer numbers within the reals. Furthermore, the `tendsto_one_div_add_atTop_nhds_zero_nat` lemma formalizes the crucial consequence of the Archimedean property related to the convergence of the sequence `1/(n+1)` to zero. Finally, the `exists_rat_btwn` lemma explicitly captures the density of rational numbers within the reals, a property deeply intertwined with the Archimedean nature of the real number system. These constructs collectively demonstrate the power and expressiveness of Lean 4 for formalizing and reasoning about core concepts in real analysis.

## Tables

### Table 1: Key Lean 4 Constructs for the Archimedean Property

| Construct Name       | Type/Kind | Short Description                                                                 |
|----------------------|-----------|-----------------------------------------------------------------------------------|
| Archimedean          | Typeclass | Formalizes the Archimedean property for ordered additive commutative monoids.      |
| Archimedean.arch     | Lemma     | States that for positive y, there exists n : ℕ such that x ≤ n • y.                |
| MulArchimedean       | Typeclass | Formalizes the multiplicative Archimedean property.                                |

### Table 2: Lemmas for Natural and Integer Bounds

| Lemma Name     | Preconditions                          | Statement (Lean Syntax)                  |
|----------------|----------------------------------------|------------------------------------------|
| exists_nat_ge  | [ordered_ring α][archimedean α]        | ∃ (n : ℕ), x ≤ ↑n                        |
| exists_nat_gt  | [strict_ordered_ring α][archimedean α] | ∃ (n : ℕ), x < ↑n                        |
| exists_int_ge  | [ordered_ring α][archimedean α]        | ∃ (n : ℤ), x ≤ ↑n                        |
| exists_int_le  | [ordered_ring α][archimedean α]        | ∃ (n : ℤ), ↑n ≤ x                        |
| exists_int_gt  | [strict_ordered_ring α][archimedean α] | ∃ (n : ℤ), x < ↑n                        |
| exists_int_lt  | [strict_ordered_ring α][archimedean α] | ∃ (n : ℤ), ↑n < x                        |

### Table 3: Lemma for Convergence of 1/(n+1) to Zero

| Lemma Name                          | Statement (Lean Syntax)                                                |
|-------------------------------------|------------------------------------------------------------------------|
| tendsto_one_div_add_atTop_nhds_zero_nat | Filter.Tendsto (fun (n : ℕ) => 1 / (n + 1)) Filter.atTop (nhds 0) |

### Table 4: Lemmas for Density of Rational Numbers

| Lemma Name     | Statement (Lean Syntax)                                                                 |
|----------------|------------------------------------------------------------------------------------------|
| exists_rat_btwn| ∃ (q : ℚ), x < ↑q ∧ ↑q < y (preconditions: [linear_ordered_field α][archimedean α] (x y : α) (hxlt : x < y)) |
| exists_rat_gt  | ∃ (q : ℚ), x < ↑q (preconditions: [linear_ordered_field α][archimedean α] (x : α))       |
| exists_rat_lt  | ∃ (q : ℚ), ↑q < x (preconditions: [linear_ordered_field α][archimedean α] (x : α))       |

## Works cited

1. Mathlib.Algebra.Order.Archimedean.Basic - Lean community, accessed May 2, 2025, https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Archimedean/Basic.html
2. algebra.order.archimedean - mathlib3 docs - Lean community, accessed May 2, 2025, https://leanprover-community.github.io/mathlib_docs/algebra/order/archimedean.html
3. A slightly longer Lean 4 proof tour | What's new - Terence Tao, accessed May 2, 2025, https://terrytao.wordpress.com/2023/12/05/a-slightly-longer-lean-4-proof-tour/
4. Mathlib.Analysis.SpecificLimits.Normed - Lean community, accessed May 2, 2025, https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecificLimits/Normed.html
5. Formalising mathematics : workshop 3 — sequences and limits | Xena - WordPress.com, accessed May 2, 2025, https://xenaproject.wordpress.com/2021/02/04/formalising-mathematics-workshop-3/
6. Topology — Mathematics in Lean 0.1 documentation, accessed May 2, 2025, https://www.imo.universite-paris-saclay.fr/~patrick.massot/mil/07_Topology.html
7. Topology — Mathematics in Lean 0.1 documentation, accessed May 2, 2025, https://leanprover-community.github.io/mathematics_in_lean/C10_Topology.html
8. Exploring Formalisation - Clara Löh - Universität Regensburg, accessed May 2, 2025, https://loeh.app.uni-regensburg.de/mapa/main.pdf
9. tutorials/src/solutions/tuto_lib.lean at master - GitHub, accessed May 2, 2025, https://github.com/leanprover-community/tutorials/blob/master/src/solutions/tuto_lib.lean
