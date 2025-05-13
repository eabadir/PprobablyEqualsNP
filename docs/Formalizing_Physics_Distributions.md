# Rota’s Entropy Theorem & Physics Distributions: A Combinatorial Proof Approach


## 1. Statement of Rota’s Entropy Theorem (RET)

**Theorem (informal)** – *All fundamental “continuous” physics distributions – notably the Maxwell–Boltzmann (MB), Fermi–Dirac (FD), and Bose–Einstein (BE) statistics – can be expressed as scaled versions of the discrete Shannon entropy functional ([PprobablyEqualsNP_formal.pdf](file://file-6z3kcoJy9w5zq5vtSEwPv7#:~:text=Definition%203%20,measure%20under%20a%20constant%20factor)).  In other words, any probability distribution in physics that is described as having a continuous/thermal entropic form is isomorphic to a discrete Shannon entropy measure, up to a constant scaling factor.* ([PprobablyEqualsNP_formal.pdf](file://file-6z3kcoJy9w5zq5vtSEwPv7#:~:text=Rota%E2%80%99s%20Entropy%20Theo,work%20shows%20how%20these%20encodings)) ([PprobablyEqualsNP_formal.pdf](file://file-6z3kcoJy9w5zq5vtSEwPv7#:~:text=Statement%20,up%20to%20constant%20scaling%20factors))

In practical terms, RET asserts that for each of these statistical distributions, there exists some discrete probability distribution (a partition of a finite sample space with probabilities) such that the **Shannon entropy** of that partition, multiplied by an appropriate constant, reproduces the given physics distribution. Symbolically, the paper expresses this as: for every physical distribution $D$, there exists a set of probabilities $\{p_i\}$ and constant $C$ such that 

\[ D \;=\; C \cdot H(p_1,p_2,\dots,p_n)\,, \] 

where $H(p_1,\dots,p_n)=-\sum_{i=1}^n p_i \log_2 p_i$ is the Shannon entropy of the discrete distribution $\{p_i\}$ ([PprobablyEqualsNP_formal.pdf](file://file-6z3kcoJy9w5zq5vtSEwPv7#:~:text=Definition%202%20%28Shannon%20Entropy%20,the%20entropy%20is)) ([PprobablyEqualsNP_formal.pdf](file://file-6z3kcoJy9w5zq5vtSEwPv7#:~:text=Definition%203%20,measure%20under%20a%20constant%20factor)). This is exactly “Definition 3 (Rota’s Entropy Theorem)” in the paper ([PprobablyEqualsNP_formal.pdf](file://file-6z3kcoJy9w5zq5vtSEwPv7#:~:text=Definition%203%20,measure%20under%20a%20constant%20factor)). The constant $C$ accounts for units or physical constants (e.g. Boltzmann’s constant $k_B$ or other scaling in continuous formulas). RET thus bridges **continuous** equilibrium distributions in physics and **discrete** entropy: for each MB/FD/BE distribution, one can find an equivalent partition whose Shannon entropy (in bits or natural units) produces that distribution up to scale.

## 2. Rota’s Proof Sketch
Below is a purely combinatorial, “integer‐only” sketch—still faithful to Rota’s partition–entropy proof—that

1. **Organizes all finite “balls‑into‑boxes” models** (MB, FD, BE) as exactly three mutually exclusive constraint‐families on occupancy partitions;  
2. Derives in each case, via **partition refinements** and the **chain‐rule for conditional entropy**, that the total information (entropy) is the *sum* of contributions from each refinement step;  
3. Introduces a notion of **discrete continuity**—via the Law of Large Numbers on rational block‐counts—to extend from purely rational probabilities to arbitrary real limits without invoking metric topology or measure theory;  
4. Concludes that in *every* finite‐combinatorial occupancy scenario (no constraint, exclusion, or unlimited indistinguishability), the resulting entropy must be a constant multiple of Shannon’s discrete formula,
\[
H(p_1,\dots,p_n)\;=\;-\,\sum_{i=1}^n p_i\,\log_2 p_i.
\]

---

## 1. Three Disjoint Constraint Classes

Let \(N\) boxes (states) and \(M\) balls (particles).  A **microstate** is a way of allocating the \(M\) balls among the \(N\) boxes.  There are exactly three—and only three—constraint families on how balls may occupy boxes:

1. **Maxwell–Boltzmann (MB):**  
   • Balls **distinguishable** (labeled \(1,\dots,M\)), no limit on how many per box.  
   • Ω\(_{MB}\) has size \(N^M\) (each of the \(M\) labels chooses one of \(N\) boxes).  
   • *Macrostate* = occupancy vector \(\mathbf{q}=(q_1,\dots,q_N)\) with \(\sum_i q_i=M\).  
   • \(\#\{\text{microstates}\mid\mathbf{q}\}=\frac{M!}{q_1!\,\cdots\,q_N!}\).  

2. **Fermi–Dirac (FD):**  
   • Balls **indistinguishable**, *at most one* ball per box.  
   • Ω\(_{FD}\) has size \(\binom{N}{M}\) (choose which \(M\) of the \(N\) boxes are occupied).  
   • Macrostate ↔ subset \(S\subseteq\{1,\dots,N\}\), \(|S|=M\).  
   • \(\#\{\text{microstates}\mid S\} = 1\) (only one way to put one indistinguishable ball in each chosen box).  

3. **Bose–Einstein (BE):**  
   • Balls **indistinguishable**, *no limit* on occupancy per box.  
   • Ω\(_{BE}\) has size \(\binom{N+M-1}{M}\) (standard “stars and bars” count).  
   • Macrostate = occupancy \(\mathbf{q}=(q_1,\dots,q_N)\), \(\sum_i q_i=M\).  
   • \(\#\{\text{microstates}\mid\mathbf{q}\}=1\).  

These three cover **all** possible combinatorial constraints on indistinguishability and exclusion.  No other finite constraint phenomena exist (that is the classical “twelvefold way”).  

---

## 2. Partition Refinement & Chain‐Rule Additivity

### 2.1 Partitions and Refinements

-  A **partition** \(\sigma\) of the microstate set \(\Omega\) groups microstates into **macrostates**.  
-  A **refinement** \(\pi\) of \(\sigma\) splits each macrostate‐block of \(\sigma\) into smaller blocks (ultimately to singletons).  
-  Rota’s **chain rule** axiom says
\[
H(\pi)\;=\;H(\sigma)\;+\;H(\pi\mid\sigma)
\quad\Longleftrightarrow\quad
H(\pi\mid\sigma)=H(\pi)-H(\sigma)\,.
\]
and that if you refine block \(B\) into \(a\) equal‐probability subblocks, that refinement contributes exactly a constant \(f(a)\) to the conditional entropy.

### 2.2 Applying to MB/FD/BE

We start at the **coarsest** partition \(\hat1\) (one block = all microstates).  We then refine in two stages:

1. **Refinement I:** Group microstates by their **macrostate** under the given constraint family (MB, FD or BE).  
2. **Refinement II:** Within each macrostate block, split into individual microstates (singletons).

Write \(\sigma\) = “partition into macrostates” and \(\pi\) = “complete singleton partition.”  Then
\[
H(\pi)\;=\;H(\sigma)\;+\;H(\pi\mid\sigma).
\]
But \(\pi\) has exactly \(\lvert\Omega\rvert\) blocks of equal probability \(1/|\Omega|\), so
\[
H(\pi)=\log_2|\Omega|\quad\bigl(\text{since }H\text{ of a uniform }k\text{-block partition}=\log_2 k\bigr).
\]
On the other hand, by **summed block refinement**, each macrostate block \(B\) of size \(|B|\) splits into \(|B|\) singletons, contributing
\[
H(\pi\mid\sigma)
\;=\;\sum_{B\in\sigma}P(B)\,\log_2|B|
\;=\;\sum_{B\in\sigma}\frac{|B|}{|\Omega|}\,\log_2|B|.
\]
Equate:
\[
\log_2|\Omega|\;-\;\sum_{B}\frac{|B|}{|\Omega|}\,\log_2|B|
\;=\;H(\sigma).
\]
But \(\displaystyle p_B=\tfrac{|B|}{|\Omega|}\) is exactly the **macrostate probability**.  Therefore
\[
H(\sigma)
\;=\;\sum_{B}p_B\;\bigl(-\log_2 p_B\bigr)
\;=\;-\sum_{B}p_B\log_2p_B,
\]
the **Shannon formula**—and **nothing** about real‐valued logs or limits has entered.  Every step used only:

- integer counts \(\lvert\Omega\rvert\), \(\lvert B\rvert\),  
- rational probabilities \(p_B=\tfrac{|B|}{|\Omega|}\),  
- the chain rule for conditional entropy, and  
- \(\log_2\) on positive integers  

—all of which are purely combinatorial.

---

## 3. “Discrete Continuity” via the Law of Large Numbers

Rota needed continuity only to pass from *rational* \(p_B\) (ratios of integers) to **all** real \(p\).  We can avoid analytic topology by instead observing:

> **As \(M\to\infty\), for any fixed “target” real distribution \(\{p_i\}\), one can choose integers \(\{q_i\}\) with \(\sum q_i=M\) so that each \(\frac{q_i}{M}\) approximates \(p_i\) to within \(\epsilon\).  By the Law of Large Numbers, an i.i.d. sampling of microstates yields macro‐counts \(\{q_i\}\) with relative frequency nearly \(p_i\) with overwhelming combinatorial weight.**  

In other words, given any real tuple \((p_1,\dots,p_n)\), pick a huge \(M\) and let \(q_i=\lfloor Mp_i\rfloor\).  Form the partition \(\sigma_M\) of the microstate set \(\Omega_M\) by those counts.  The **combinatorial entropy** of \(\sigma_M\) is exactly
\[
H_M(\sigma_M)
\;=\;-\sum_i \frac{q_i}{|\Omega_M|}\,\log_2\!\frac{q_i}{|\Omega_M|}.
\]
As \(M\to\infty\), \(\frac{q_i}{|\Omega_M|}\to p_i\) and \(\frac{q_i}{M}\to p_i\), so the **discrete continuity** principle is:

> Whenever two partitions \(\sigma_M\) and \(\tilde\sigma_M\) have block‐fractions within \(\epsilon\), their entropies differ by at most \(O(\epsilon\log\epsilon^{-1})\).  

This bound follows from the fact that
\[
\bigl| -x\log x \;-\;-y\log y \bigr|
\;\le\; C\,|x-y|\bigl|\log|x-y|\bigr|
\]
on \([0,1]\), a purely combinatorial (integer‐based) estimate once \(x,y\) are rational.  One never needs to introduce limits in a metric space; the large‐\(M\) regime suffices to make the error “vanishingly small” in a *discrete* sense.  

---

## 4. Conclusion: Additivity Holds Under Any Constraint

Because **every** finite “balls‐into‐boxes” model is one of MB, FD or BE—or a mixture obtained by refining these partitions further—the same argument applies: at each stage of refinement the conditional contribution is \(f(a)=\log_2 a\) for splitting one block into \(a\) parts, and summing those yields the Shannon sum.  In particular:

- In **FD**, each box can be either empty or occupied, so each block splits into exactly two sub‑blocks (“occupied” vs “not”).  Each contributes \(\log_2 2=1\).  Summing gives
  \[
    H(\sigma)= -\sum p_i\log_2(p_i)\quad\text{with each }p_i=\frac1{\binom{N}{M}}
  \]
  in the uniform case, or more generally with the equilibrium occupancy probabilities in the grand‑canonical ensemble.

- In **BE**, each block splits into infinitely many sub‑blocks (one for each occupancy number), but **only finitely many** occur in a given finite \(M\) model.  The same \(\log_2 a\) law applies to those finite counts.

- Any **mixed** or nested constraints (e.g. partial exclusion or partial indistinguishability) also amount to refining a partition by subdividing each macrostate block into sub‐families of microstates; each subdivision carries a \(\log_2 a\) contribution.  

Thus **in every case** of a purely combinatorial occupancy model, the total information is
\[
  \sum_{\text{all refinements}} p_{\text{block}}\;\log_2(\text{#subblocks})
  = -\sum_B p_B\log_2 p_B,
\]
i.e. a constant multiple of the Shannon entropy.  No real‐analysis, no measure‐theory, no continuous topology—just **integer counts**, **rational approximations**, and the **Law of Large Numbers** to pass from rationals to all real distributions. 

---

### Key Takeaways

1. **Three constraint families** (MB, FD, BE) exhaust all finite partition‐theoretic occupancy models.  
2. **Chain‐rule additivity** under partition refinement forces a \(\log_2\) rule on splitting blocks.  
3. **Discrete continuity**, via large‐\(M\) sampling and rational approximations, extends the result from rational frequencies to *any* limiting real distribution.  
4. Therefore **EVERY** finite combinatorial occupancy scenario yields an entropy of the form
   \[
     H = -C\sum_i p_i\log_2 p_i,
   \]
   with \(C\) constant (determined by choice of base or units).  

This is exactly Rota’s Entropy Theorem—proved **entirely** within the realm of *integer combinatorics and partition refinements*, and ready for a fully formal Lean 4 development.

# Rota’s Entropy Theorem & Physics Distributions: A Combinatorial Proof Approach
# Formalizing Bose-Einstein Statistics in PPNP/Entropy/Physics.lean

## 1. Conceptual Overview: Phased Approach

This file aims to formally define the state space and probability distribution for Bose-Einstein (BE) statistics within the Lean 4 theorem prover, leveraging the Mathlib4 library. The ultimate goal is to apply the previously proven Rota's Entropy Theorem (RET) to this distribution.

Formalizing concepts from statistical mechanics requires careful handling of combinatorial structures, type theory, and proof details. To manage this complexity effectively and ensure correctness, we employ a **four-phased approach**:

1.  **Phase 1: Combinatorial Equivalence:** Establish the fundamental combinatorial structure. We define the BE state space (`OmegaBE`, based on occupancy numbers) and show it's mathematically equivalent (via a Lean `Equiv`) to a standard combinatorial object: multisets of a fixed size (`SymFin`). This grounds the specific physical concept in a well-understood mathematical structure within Mathlib.
2.  **Phase 2: Cardinality and Iteration:** Determine the size of the BE state space using the equivalence established in Phase 1 and known results for multisets (the "stars and bars" formula, yielding binomial coefficients). We also formally declare `OmegaBE` as a `Fintype`, enabling iteration and summation over all possible BE states, which is crucial for defining probabilities.
3.  **Phase 3: Probability Distribution:** Define the BE probability distribution (`p_BE`) assuming equiprobability of microstates (which corresponds to a uniform distribution over `OmegaBE`). Prove that this distribution is valid by showing the probabilities sum to 1 (normalization).
4.  **Phase 4: RET Application:** Connect the formalized BE distribution to the framework of Rota's Entropy Theorem. This involves potentially adapting the type of our distribution (`p_BE_fin`) and then applying the main theorem (`H_BE_eq_C_shannon`) to conclude that any valid entropy function `H` applied to `p_BE` is proportional to the standard Shannon entropy. We can then calculate this specific entropy value (`entropy_BE`).

**Why this approach?**

*   **Modularity:** Each phase addresses a distinct conceptual layer (combinatorics, counting, probability, entropy theory).
*   **Manageability:** It breaks a complex formalization task into smaller, more verifiable steps.
*   **Debugging:** Isolating proofs within phases makes identifying and fixing issues (like type mismatches or logical gaps) significantly easier.
*   **Micro-Lemma Strategy:** Within complex phases (especially Phase 1), we further decompose proofs into small, focused "micro-lemmas". Each micro-lemma proves a single, small step in the larger argument. This builds a robust, verifiable chain of reasoning, making the final proofs much clearer and less prone to subtle errors, as demonstrated during the proof of the `sum_replicate_count_toFinset_eq_self` identity.

## 2. Mapping Concepts to Code: Key Lemmas and Theorems

The conceptual phases described above map directly to specific definitions, lemmas, and theorems within the Lean code. The following table highlights the most important named items developed (or planned) and their role in the overall structure:

| Phase | Key Lemma/Definition                       | Role in Phase                                                                                    | Status      |
| :---- | :----------------------------------------- | :----------------------------------------------------------------------------------------------- | :---------- |
| 1     | `OmegaBE N M`                              | Defines the type for BE states (occupancy vectors summing to M).                                   | Done        |
| 1     | `SymFin N M`                               | Defines the equivalent type: Multisets of size M over `Fin N`.                                   | Done        |
| 1     | `beStateToMultiset`                        | Function mapping a BE state (`OmegaBE`) to its corresponding multiset (`Multiset (Fin N)`).       | Done        |
| 1     | `multisetToBEStateSubtype`                 | Function mapping a multiset (`SymFin`) back to a BE state (`OmegaBE`), including proof.        | Done        |
| 1     | `left_inv_beState_multiset`                | Proves `multisetToBEStateSubtype ∘ beStateToMultiset = id` (one direction of the equivalence).   | Done        |
| 1     | `right_inv_beState_multiset`               | Proves `beStateToMultiset ∘ multisetToBEStateSubtype = id` (other direction of the equivalence). | Done        |
| 1     | `sum_replicate_count_toFinset_eq_self`     | Core combinatorial identity needed for `right_inv` (proved via induction & micro-lemmas).        | Done        |
| 1     | `beStateEquivMultiset` (Planned)           | Formal `Equiv` bundling the maps and inverse proofs.                                             | **Next Step** |
| 2     | `fintypeOmegaBE` (Planned)                 | `Fintype` instance for `OmegaBE`, derived via the equivalence, enabling iteration/summation.   | Pending     |
| 2     | `card_omega_be` (Planned)                  | Calculates `Fintype.card (OmegaBE N M)` using the equivalence and stars-and-bars result.      | Pending     |
| 2     | `card_omega_be_pos` (Planned)              | Proves the cardinality is positive (needed for division in probability).                           | Pending     |
| 3     | `p_BE` (Planned)                           | Defines the uniform probability distribution `1 / |Ω_BE|` on `OmegaBE`.                           | Pending     |
| 3     | `p_BE_sums_to_one` (Planned)               | Proves `∑ p_BE(q) = 1` (normalization).                                                          | Pending     |
| 4     | `p_BE_fin` (Planned)                       | Adapts `p_BE` distribution to the canonical `Fin k → ℝ≥0` type expected by RET.                  | Pending     |
| 4     | `p_BE_fin_sums_to_one` (Planned)           | Proves normalization for the adapted `p_BE_fin`.                                                 | Pending     |
| 4     | `H_BE_eq_C_shannon` (Planned)              | Applies RET to `p_BE_fin`, showing `H(p) = C * stdShannonEntropyLn(p)`.                          | Pending     |
| 4     | `entropy_BE` (Planned)                     | Calculates the specific value `stdShannonEntropyLn(p_BE_fin) = log |Ω_BE|`.                     | Pending     |

This structure demonstrates how the foundational combinatorial work in Phase 1 directly enables the cardinality calculations in Phase 2, which are essential for defining the normalized probability distribution in Phase 3, ultimately allowing the application of Rota's Entropy Theorem in Phase 4. The micro-lemmas developed, particularly for the inverse proofs, exemplify the robust proof strategy employed.


# Implementation Plan
Formalizing Statistical Mechanics Distributions in Lean 4: A Mathlib4 Roadmap
1. Introduction
1.1. Objective
This report provides a detailed technical roadmap for the formalization of probability distributions central to Maxwell-Boltzmann (MB), Fermi-Dirac (FD), and Bose-Einstein (BE) statistical mechanics within the Lean 4 theorem prover, leveraging the capabilities of the Mathlib4 library. The primary aim is to identify the necessary definitions, lemmas, theorems, and tactics from Mathlib4 required to construct these distributions and verify their fundamental properties, paving the way for their use in subsequent theoretical developments.

1.2. Context and Motivation
The successful formalization and proof of Rota's Entropy Theorem (RET) within the PPNP project marks a significant milestone. RET establishes a fundamental uniqueness property for entropy functions satisfying a specific set of axioms (IsEntropyFunction). It guarantees that any such function H, when evaluated on a suitable probability distribution p, must take the form H(p)=C×stdShannonEntropyLn(p) for some constant C, where stdShannonEntropyLn(p)=−∑ 
i
​
 p 
i
​
 ln(p 
i
​
 ) is the standard Shannon entropy (using the natural logarithm).

This result provides crucial context for the current task. With RET proven, the focus shifts from deriving the specific mathematical form of entropy from combinatorial principles within Lean to applying the theorem to physically relevant systems. The immediate next step involves defining the probability distributions that characterize the macroscopic states of systems governed by MB, FD, and BE statistics. RET assures us that once these distributions are correctly formalized and shown to be valid probability measures (i.e., non-negative and summing to one), any entropy function conforming to the IsEntropyFunction axioms will automatically evaluate them proportionally to their standard Shannon entropy. This significantly streamlines the process, as a separate combinatorial derivation of the Shannon formula for each statistical ensemble within the formal system is rendered unnecessary for the primary goal of applying RET.

1.3. Report Structure and Scope
This report outlines the necessary steps and identifies the required Mathlib4 components for formalizing the MB, FD, and BE probability distributions in a new Lean file, proposed as PPNP/Entropy/Physics.lean. The structure is as follows:

Core Mathlib4 Imports and Foundational Concepts: Identifies essential library modules and defines core mathematical objects like Fintype, Fintype.card, and ℝ≥0 used throughout the formalization.
Formalizing Maxwell-Boltzmann (MB) Statistics: Details the definition of MB microstates and macrostates, the calculation of state space cardinalities, the definition of statistical weights (W_MB), the probability distribution (p_MB), and the strategy for proving normalization (∑p 
MB
​
 =1).
Formalizing Fermi-Dirac (FD) Statistics: Outlines the definition of the FD state space (subsets of states), cardinality calculation using binomial coefficients, the uniform probability distribution (p_FD), and the normalization proof.
Formalizing Bose-Einstein (BE) Statistics: Describes the BE state space (equivalent to MB macrostates), cardinality calculation using stars and bars (multiset combinations), the uniform probability distribution (p_BE), and the normalization proof.
Applying Rota's Entropy Theorem (RET): Explains how to map the defined distributions to the type required by the formalized RET and state the resulting theorems, including specific entropy calculations for FD and BE.
Potential Challenges and Recommendations: Discusses anticipated difficulties in the formalization process and suggests strategies using Mathlib4 tools.
Conclusion: Summarizes the plan and highlights the path forward for implementation.
The scope is focused on the definition and properties of the probability distributions themselves, emphasizing the identification of Mathlib4 dependencies and outlining proof strategies. It does not include the full Lean 4 code implementation but serves as a comprehensive blueprint for that task. The target audience is assumed to be proficient in Lean 4, Mathlib4, and the relevant mathematical and physical concepts.

2. Core Mathlib4 Imports and Foundational Concepts
The formalization of statistical mechanics distributions necessitates leveraging a significant portion of Mathlib4's combinatorics, algebra, and data structure libraries.

2.1. Essential Library Imports
The following imports are anticipated as necessary for the PPNP/Entropy/Physics.lean file:

import PPNP.Entropy.Basic: Provides access to the previously formalized RotaEntropyTheorem, the IsEntropyFunction typeclass, and potentially the stdShannonEntropyLn definition.
import Mathlib.Data.Fintype.Card: Essential for Fintype.card, cardinality computations, and related theorems like Fintype.card_congr.   
import Mathlib.Data.Fintype.Pi: Crucial for the Fintype instance and cardinality calculation (N ^ M) of function types (Fin M → Fin N), which represent MB microstates.   
import Mathlib.Data.Finset.Card: Defines Finset.card and basic properties needed for subset cardinalities and intermediate calculations.   
import Mathlib.Data.Finset.Basic: For fundamental Finset operations, definitions like Finset.univ, membership (∈), and subset relations (⊆).   
import Mathlib.Data.Finset.Subtype: Provides tools for working with subtypes defined by predicates on Finsets, relevant for FD states ({ s // s.card = M }).
import Mathlib.Data.Nat.Choose.Basic: Defines Nat.choose n k (( 
k
n
​
 )) and related properties, fundamental for FD and BE cardinalities.   
import Mathlib.Data.Nat.Choose.Multinomial: Defines Nat.multinomial, the multinomial coefficient, required for calculating MB weights (W_MB).   
import Mathlib.Data.Nat.Factorial.Basic: Provides Nat.factorial, a dependency for both Nat.choose and Nat.multinomial.
import Mathlib.Algebra.BigOperators.Finset.Basic: Defines Finset.sum and Finset.prod (big operators). Contains critical theorems like Finset.sum_pow (the Multinomial Theorem) needed for MB normalization and Finset.sum_const needed for FD and BE normalization.   
import Mathlib.Data.Real.NNReal: Defines the type ℝ≥0 (non-negative real numbers), its algebraic structure (e.g., LinearOrderedCommSemiring), order properties, and coercions, making it the appropriate type for probabilities.   
import Mathlib.Algebra.GroupPower.Order: May contain lemmas about powers, such as Nat.pow_pos, useful for proving positivity of cardinalities like N 
M
 .   
import Mathlib.Data.Sym.Card: Contains Sym.card_sym_eq_multichoose and related lemmas connecting multiset cardinality (Sym α k) to Nat.multichoose, which is essential for the BE cardinality proof via stars and bars.   
import Mathlib.Logic.Equiv.Fintype: Provides Fintype.equivFin, an equivalence between any Fintype and Fin k, potentially necessary for adapting the defined distributions to the type signature required by RotaEntropyTheorem.   
import Mathlib.Tactic.Positivity: Offers the positivity tactic for automatically discharging goals asserting that expressions are positive or non-negative, useful for conditions like N 
M
 >0 or ( 
M
N
​
 )>0.   
2.2. Foundational Types and Concepts
Fintype α: This Mathlib4 typeclass signifies that the type α is finite. It bundles a Finset α called elems containing all elements of α, along with a proof complete that every term x : α satisfies x ∈ elems. The existence of a Fintype instance is crucial for defining sums over all elements of a type, as required for probability normalization. Many standard types like Fin n, Bool, and products/sums/pi types (if components are Fintypes) automatically derive Fintype instances.   
Fintype.card α: For a type α with a Fintype instance, Fintype.card α is defined as Finset.univ.card, representing the number of elements in the type. Finset.univ refers to the elems finset provided by the Fintype instance. Cardinality calculations are central to statistical mechanics for determining the size of state spaces and normalization constants. Key properties include Fintype.card_congr which states that equivalent types have the same cardinality.   
ℝ≥0 (NNReal): This type represents non-negative real numbers, {x∈R∣x≥0}. It is equipped with a rich algebraic structure, including being a LinearOrderedCommSemiring. This means it supports addition, multiplication, zero, one, order relations (≤, <), and crucially, properties ensuring that sums and products of non-negative numbers remain non-negative. It also handles inversion for positive elements. These features make ℝ≥0 the ideal type for representing probabilities in Mathlib4. Coercions from ℕ and ℝ (via Real.toNNReal) are available.   
Probability Distributions: Within this context, a (discrete) probability distribution is a function p:α→R 
≥0
​
 , where α is a Fintype representing the sample space (e.g., microstates or macrostates), such that the probabilities sum to one: ∑ 
x:α
​
 p(x)=1. Formalizing this involves defining the function p and proving the normalization condition using Finset.sum over Finset.univ.
3. Formalizing Maxwell-Boltzmann (MB) Statistics
MB statistics describe systems of distinguishable particles that can occupy distinguishable energy states or positions, with no limit on the number of particles per state.

3.1. Microstate Space (Ω_MB)
Definition: The set of all possible configurations (microstates) for M distinguishable particles distributed among N distinguishable states is formally represented by the type of functions from the set of particles (indexed by Fin M) to the set of states (indexed by Fin N).
Lean

def OmegaMB (N M : ℕ) := Fin M → Fin N
Fintype Instance: Mathlib4 automatically infers a Fintype instance for function types when both the domain and codomain are Fintypes. Since Fin M and Fin N are Fintypes , OmegaMB N M is also a Fintype. This can be declared simply as:
Lean

instance : Fintype (OmegaMB N M) := by infer_instance
This relies on the infrastructure in Mathlib.Data.Fintype.Pi.   
Cardinality: The number of functions from a set of size M to a set of size N is N 
M
 . Mathlib's simp tactic can likely prove this automatically using lemmas associated with Fintype.card for Pi types.
Lean

lemma card_omega_mb (N M : ℕ) : Fintype.card (OmegaMB N M) = N ^ M := by simp
This simplification likely uses lemmas such as Fintype.card_pi internally.   
Positivity (N 
M
 >0): The definition of the MB probability distribution involves division by the total number of microstates, N 
M
 . This requires N 
M
  to be non-zero. In the context of ℝ≥0, the inverse (N 
M
 ) 
−1
  is defined only if N 
M
 >0. Since N,M are natural numbers, N 
M
  is also a natural number. N 
M
 =0 if and only if N=0 and M>0. Physical systems typically assume N≥1. If N>0 (i.e., N≥1), then N 
M
 ≥1 
M
 =1 for M>0, and N 
0
 =1. Thus, the condition N>0 guarantees N 
M
 >0. This needs to be formally proven, likely using a lemma like Nat.pow_pos which might be found in basic Nat properties or potentially Algebra.GroupPower.Order. The positivity tactic might also discharge this goal automatically if suitable lemmas are tagged.   
3.2. Macrostate Space (MBMacrostate)
Definition: A macrostate is defined by the number of particles q 
i
​
  in each state i∈Fin N, such that the total number of particles is M. This is formalized as a subtype of functions Fin N → ℕ:
Lean

def MBMacrostate N M := { q : Fin N → ℕ // ∑ i, q i = M }
Here, q.val accesses the function Fin N → ℕ, and q.property is the proof that ∑ 
i∈Fin N
​
 q.val(i)=M.
Fintype Instance: Establishing a Fintype instance for MBMacrostate N M is less direct than for OmegaMB N M. The base type Fin N → ℕ is infinite. However, the constraint ∑q 
i
​
 =M implies that each q 
i
​
  must be between 0 and M, making the number of valid functions q finite. Proving this requires constructing the finite set of all such functions or showing an equivalence to a known Fintype. This problem is equivalent to counting integer compositions of M into N parts. Mathlib's libraries on compositions (Mathlib.Combinatorics.Composition) or potentially multisets (Mathlib.Data.Multiset.Fintype ) might contain the necessary tools or require adaptation. This step represents a potential non-trivial hurdle in the formalization.   
3.3. Weight (W_MB)
Definition: The statistical weight W 
MB
​
 (q) of a macrostate q is the number of microstates that correspond to that macrostate. This is given by the multinomial coefficient ( 
q 
0
​
 ,q 
1
​
 ,...,q 
N−1
​
 
M
​
 )= 
q 
0
​
 !q 
1
​
 !...q 
N−1
​
 !
M!
​
 . Mathlib provides Nat.multinomial for this purpose.
Lean

noncomputable def W_MB (q : MBMacrostate N M) : ℕ :=
  Nat.multinomial Finset.univ fun i => q.val i
The noncomputable keyword is used because factorials and division underlying Nat.multinomial are often defined non-computably in Mathlib. The definition relies on Finset.univ : Finset (Fin N) representing the set of all possible states. The definition MBMacrostate ensures the implicit precondition of Nat.multinomial (that the arguments sum to the number whose factorial is in the numerator) is met, as ∑ 
i∈Finset.univ
​
 q.vali=M.   
3.4. Probability Distribution (p_MB)
Definition: Assuming equiprobability of microstates (the fundamental postulate of statistical mechanics), the probability of a macrostate q is the ratio of its weight W 
MB
​
 (q) to the total number of microstates ∣Ω 
MB
​
 ∣=N 
M
 . This is defined using ℝ≥0 for non-negative probabilities.
Lean

noncomputable def p_MB {N M : ℕ} (hN : N > 0) (hM : M > 0) (q : MBMacrostate N M) : ℝ≥0 :=
  if hNM : N ^ M > 0 then
    (W_MB q : ℝ≥0) * (↑(N ^ M) : ℝ≥0)⁻¹
  else 0
This definition requires coercions from ℕ to ℝ≥0 (↑), multiplication (*), and inversion (⁻¹) within ℝ≥0. The if statement handles the (physically unlikely but formally possible) case where N 
M
 =0, relying on the proof hNM : N ^ M > 0 derived from hN (as discussed in 3.1). Hypotheses hN and hM are included to reflect common physical assumptions, although hM > 0 might not be strictly necessary for the definition itself if N 
M
 >0.   
3.5. Normalization (∑p 
MB
​
 =1)
Goal: The fundamental requirement for p 
MB
​
  to be a valid probability distribution is that the sum over all possible macrostates equals 1:
Lean

theorem p_MB_sums_to_one {N M : ℕ} (hN : N > 0) (hM : M > 0) :
  ∑ q : MBMacrostate N M, p_MB hN hM q = 1
(Requires the Fintype (MBMacrostate N M) instance).
Strategy: Substituting the definition of p 
MB
​
  (and using the positivity hNM), the goal becomes proving: ∑ 
q:MBMacrostateNM
​
 (W 
MB
​
 (q):R 
≥0
​
 )×(↑(N 
M
 ):R 
≥0
​
 ) 
−1
 =1. Factoring out the constant inverse term (which requires the sum to be over a Finset, typically Finset.univ from the Fintype instance), this is equivalent to proving: (∑ 
q:MBMacrostateNM
​
 ↑(W 
MB
​
 (q)):R 
≥0
​
 )=(↑(N 
M
 ):R 
≥0
​
 ). Since coercion from ℕ to ℝ≥0 respects sums, this reduces to proving the identity in ℕ: ∑ 
q:MBMacrostateNM
​
 W 
MB
​
 (q)=N 
M
 .
Key Theorem: This required identity, ∑ 
{q∣∑q 
i
​
 =M}
​
  
q 
0
​
 !…q 
N−1
​
 !
M!
​
 =N 
M
 , is precisely the Multinomial Theorem applied to (1+1+⋯+1) 
M
  (with N terms). Mathlib formalizes the Multinomial Theorem as Finset.sum_pow. The theorem statement is roughly (s.sumx) 
n
 =∑ 
k s.t. ∑k 
i
​
 =n
​
 (multinomial coeff)×(∏(x 
i
​
 ) 
k 
i
​
 
 ). By setting the base s to Finset.univ : Finset (Fin N), the function x to be constantly 1, and the power n to M, the theorem yields: (∑ 
i∈Finset.univ
​
 1) 
M
 =∑ 
q:MBMacrostateNM
​
 (Nat.multinomial Finset.univ q.val)×(∏ 
i∈Finset.univ
​
 1 
q.vali
 ). Since ∑ 
i∈Finset.univ
​
 1=Fintype.card (Fin N)=N and ∏1 
q 
i
​
 
 =1, this simplifies exactly to N 
M
 =∑ 
q:MBMacrostateNM
​
 W 
MB
​
 (q), completing the normalization proof. The main task is thus to correctly instantiate and apply the Finset.sum_pow theorem from Mathlib.   
3.6. Table 1: Key Mathlib4 Components for MB Formalization
Category	Mathlib Artifact(s)	Purpose	Snippet Refs
Types	Fin N, ℕ, ℝ≥0	Particle states, counts, probabilities	
Fin M → Fin N	Microstate space (OmegaMB)	
{ q : Fin N → ℕ // ∑ i, q i = M } (MBMacrostate)	Macrostate space	
Fintype	Fintype (OmegaMB N M) (instance)	Enable iteration/summation over microstates	
Fintype (MBMacrostate N M) (needs proof/construction)	Enable iteration/summation over macrostates	?
Fintype.card	Calculate size of state spaces	
Cardinality	Nat.pow_pos (or similar)	Prove N 
M
 >0	?
Fintype.card_pi (via simp)	Prove card (OmegaMB N M) = N ^ M	
Weights	Nat.multinomial	Define W_MB	
Normalization	Finset.sum	Summation operator	
Finset.sum_pow (Multinomial Theorem)	Prove ∑W 
MB
​
 (q)=N 
M
 	
NNReal.inv, NNReal.mul, NNReal.coe_nat_cast	Define p_MB, arithmetic in ℝ≥0	
Tactics	simp, infer_instance, linarith, ring, positivity	Proof automation	
  
4. Formalizing Fermi-Dirac (FD) Statistics
FD statistics describe systems of indistinguishable particles (fermions) subject to the Pauli exclusion principle: no two particles can occupy the same quantum state.

4.1. State Space (Ω_FD)
Definition: A microstate corresponds to choosing M distinct states out of N available states for the M indistinguishable particles. This is modeled as a subset of Fin N with cardinality exactly M.
Lean

def OmegaFD (N M : ℕ) := { s : Finset (Fin N) // s.card = M }
We use Finset (Fin N) to represent subsets of the state space Fin N. The subtype condition s.card = M enforces that exactly M states are chosen.   
Fintype Instance: The type Finset (Fin N) is itself a Fintype (as Fin N is a Fintype). Mathlib provides that subtypes of Fintypes inherit the Fintype instance, likely via Fintype.subtype or similar mechanisms. Thus, OmegaFD N M is automatically a Fintype.
Lean

instance : Fintype (OmegaFD N M) := by infer_instance
  
Cardinality: The number of ways to choose a subset of size M from a set of size N is given by the binomial coefficient ( 
M
N
​
 ). This should correspond directly to the Fintype.card of the subtype definition.
Lean

lemma card_omega_fd (N M : ℕ) : Fintype.card (OmegaFD N M) = Nat.choose N M
This lemma likely follows from definitions in Data.Nat.Choose.Basic or Data.Fintype.Card, possibly using Fintype.card_subtype_eq or a similar result relating the cardinality of a subtype to the size of the corresponding Finset.   
Positivity (( 
M
N
​
 )>0): The probability definition requires the total number of states, ( 
M
N
​
 ), to be positive. The binomial coefficient ( 
M
N
​
 ) is positive if and only if M≤N (assuming M,N≥0). If M>N, it's impossible to choose M distinct items from N, so ( 
M
N
​
 )=0. If M≤N, such subsets exist (including the empty set if M=0, for which ( 
0
N
​
 )=1), so ( 
M
N
​
 )>0. This condition M≤N reflects the physical constraint imposed by the Pauli principle within N states. The formal proof requires a lemma like Nat.choose_pos from Mathlib, which likely takes M ≤ N as an assumption. The positivity tactic might handle this if M ≤ N is available in the context.   
4.2. Probability Distribution (p_FD)
Definition: FD statistics assumes each distinct microstate (valid choice of M states) is equally probable. The probability is uniform over Ω 
FD
​
 .
Lean

noncomputable def p_FD {N M : ℕ} (h_le : M ≤ N) (s : OmegaFD N M) : ℝ≥0 :=
  if h_card : Nat.choose N M > 0 then -- Proof follows from h_le
    (↑(Nat.choose N M) : ℝ≥0)⁻¹
  else 0 -- Should be unreachable if h_le implies h_card
(A better definition might take h_card : Nat.choose N M > 0 directly as input, derived from h_le separately). This uses Nat.choose , coercion to ℝ≥0, and inversion. The positivity condition h_card is essential.   
4.3. Normalization (∑p 
FD
​
 =1)
Goal: Prove that the sum of probabilities over all FD states is 1.
Lean

theorem p_FD_sums_to_one {N M : ℕ} (h_le : M ≤ N) :
  ∑ s : OmegaFD N M, p_FD h_le s = 1
(Requires the Fintype (OmegaFD N M) instance).
Strategy: Substitute the definition of p 
FD
​
 . Let k=( 
M
N
​
 ). Assuming k>0 (which follows from h 
le
​
 ), the sum is ∑ 
s:Ω 
FD
​
 
​
 (↑k:R 
≥0
​
 ) 
−1
 . This is a sum of a constant value over the Fintype Ω 
FD
​
 .
Key Theorem: The Mathlib theorem Finset.sum_const states that ∑ 
i∈s
​
 b=(Finset.card s)⋅b (using nsmul denoted by • for the additive monoid action). Applying this to the sum over Finset.univ for the Fintype Ω 
FD
​
 : ∑ 
s:Ω 
FD
​
 
​
 (↑k) 
−1
 =(Fintype.card Ω 
FD
​
 )⋅(↑k) 
−1
 . Using the card_omega_fd lemma, Fintype.card Ω 
FD
​
 =( 
M
N
​
 )=k. The sum becomes k⋅(↑k) 
−1
 . In the semiring ℝ≥0, the natural number action nsmul corresponds to multiplication by the coerced natural number (nsmul_eq_mul or similar implicit conversion): k⋅(↑k) 
−1
 =(↑k)×(↑k) 
−1
 . Since k=( 
M
N
​
 )>0 (due to h 
le
​
 ), the term ↑k is positive in ℝ≥0, and thus mul_inv_cancel applies, yielding 1. This demonstrates that normalization for uniform distributions over Fintypes follows a standard pattern in Mathlib, significantly simpler than the MB case involving the Multinomial Theorem.   
4.4. Table 2: Key Mathlib4 Components for FD Formalization
Category	Mathlib Artifact(s)	Purpose	Snippet Refs
Types	Fin N, Finset (Fin N), ℕ, ℝ≥0	States, sets of states, counts, probabilities	
{ s : Finset (Fin N) // s.card = M } (OmegaFD)	State space	
Fintype	Fintype (OmegaFD N M) (instance via subtype)	Enable iteration/summation over states	
Fintype.card	Calculate size of state space	
Cardinality	Nat.choose	Define cardinality ( 
M
N
​
 )	
Fintype.card_subtype_eq (or similar)	Prove card (OmegaFD N M) = Nat.choose N M	
Nat.choose_pos (or similar)	Prove ( 
M
N
​
 )>0 (requires M≤N)	?
Normalization	Finset.sum	Summation operator	
Finset.sum_const	Key theorem for summing the constant probability	
nsmul_eq_mul (or implicit)	Relate • to * in ℝ≥0	
NNReal.inv, NNReal.mul, NNReal.coe_nat_cast	Define p_FD, handle coercions	
mul_inv_cancel (for ℝ≥0)	Final step in normalization proof	?
Tactics	simp, infer_instance, linarith, positivity	Proof automation	
  
5. Formalizing Bose-Einstein (BE) Statistics
BE statistics describe systems of indistinguishable particles (bosons) where any number of particles can occupy the same state.

5.1. State Space (Ω_BE)
Definition: A microstate is defined by the number of particles q 
i
​
  occupying each state i, where the particles are indistinguishable. This means a configuration is entirely determined by the occupation numbers (q 
0
​
 ,q 
1
​
 ,…,q 
N−1
​
 ) such that ∑q 
i
​
 =M. This is mathematically identical to the definition of a macrostate in the MB case.
Lean

def OmegaBE (N M : ℕ) := MBMacrostate N M -- { q : Fin N → ℕ // ∑ i, q i = M }
Fintype Instance: The challenge of proving the Fintype instance is the same as for MBMacrostate (Section 3.2). It requires showing that the set of functions q : Fin N → ℕ satisfying ∑q 
i
​
 =M is finite.
5.2. Cardinality (card_omega_be)
Goal: The number of ways to place M indistinguishable particles into N distinguishable boxes (states) is given by the multiset coefficient ( 
M
N+M−1
​
 ). The goal is to prove:
Lean

lemma card_omega_be (N M : ℕ) : Fintype.card (OmegaBE N M) = Nat.choose (N + M - 1) M
Strategy: This is a classic combinatorial result often derived using the "stars and bars" argument. Mathlib formalizes concepts related to multisets and stars and bars. Snippet  is particularly relevant, discussing the connection between counting multisets and Nat.multichoose. It provides:
Nat.multichoose n k = Nat.choose (n + k - 1) k (likely in Data.Nat.Choose.Basic).
Sym α k represents multisets of size k over type α.
Sym.card_sym_eq_multichoose : Fintype.card (Sym α k) = Nat.multichoose (Fintype.card α) k. The strategy is therefore to establish a canonical equivalence (Equiv) between the state space OmegaBE N M (which is MBMacrostate N M) and the type of multisets of size M over Fin N, i.e., Sym (Fin N) M.
An element q∈MBMacrostate NM corresponds to a multiset containing q.val(i) copies of element i∈Fin N for each i. The total number of elements in the multiset is ∑q.val(i)=M. This correspondence suggests a natural equivalence. Mathlib may already contain this equivalence, possibly related to Multiset.toFinsupp or similar constructions.
Once the equivalence e : OmegaBE N M ≃ Sym (Fin N) M is established, Fintype.card_congr e gives Fintype.card (OmegaBE N M) = Fintype.card (Sym (Fin N) M).   
Then, applying Sym.card_sym_eq_multichoose : Fintype.card (Sym (Fin N) M) = Nat.multichoose (Fintype.card (Fin N)) M   
Since Fintype.card (Fin N) = N, this becomes Nat.multichoose N M.
Finally, using Nat.multichoose_eq: Nat.multichoose N M = Nat.choose (N + M - 1) M. This chain of lemmas proves the desired cardinality. The main step is finding or constructing the Equiv between MBMacrostate N M and Sym (Fin N) M.
  
Positivity: The probability definition requires ( 
M
N+M−1
​
 )>0. This generally holds if N>0 (since N≥1⟹N+M−1≥M) or if M=0 (where the result is 1). Formal proof uses Nat.choose_pos with the appropriate condition.
5.3. Probability Distribution (p_BE)
Definition: BE statistics assumes each distinct arrangement of indistinguishable particles (each element of Ω 
BE
​
 ) is equally probable. The probability is uniform over the state space Ω 
BE
​
 .
Lean

noncomputable def p_BE {N M : ℕ} (hN_pos : N > 0) (q : OmegaBE N M) : ℝ≥0 :=
  if h_card : Nat.choose (N + M - 1) M > 0 then -- Proof follows from hN_pos or M=0
    (↑(Nat.choose (N + M - 1) M) : ℝ≥0)⁻¹
  else 0
(Again, handling the positivity condition h_card might be better done via a direct hypothesis). This relies on Nat.choose, ℝ≥0 arithmetic, and the positivity proof.   
5.4. Normalization (∑p 
BE
​
 =1)
Goal: Prove ∑ 
q:Ω 
BE
​
 
​
 p 
BE
​
 (q)=1.
Lean

theorem p_BE_sums_to_one {N M : ℕ} (hN_pos : N > 0) :
  ∑ q : OmegaBE N M, p_BE hN_pos q = 1
(Requires Fintype (OmegaBE N M) instance).
Strategy: The structure is identical to the FD case. Let k=( 
M
N+M−1
​
 ). Assuming k>0 (from hN 
pos
​
  or M=0), the sum is ∑ 
q:Ω 
BE
​
 
​
 (↑k:R 
≥0
​
 ) 
−1
 .
Key Theorem: Apply Finset.sum_const. The sum equals (Fintype.card Ω 
BE
​
 )⋅(↑k) 
−1
 . Using the card_omega_be lemma, this is k⋅(↑k) 
−1
 =(↑k)×(↑k) 
−1
 =1 by nsmul_eq_mul and mul_inv_cancel, since k>0. The normalization proof, once the cardinality is established, follows the same simple pattern as FD.   
5.5. Table 3: Key Mathlib4 Components for BE Formalization
Category	Mathlib Artifact(s)	Purpose	Snippet Refs
Types	Fin N, ℕ, ℝ≥0	States, counts, probabilities	
{ q : Fin N → ℕ // ∑ i, q i = M } (OmegaBE)	State space (same type as MBMacrostate)	
Sym (Fin N) M (or Multiset)	Equivalent type used for cardinality proof	
Fintype	Fintype (OmegaBE N M) (needs proof/construction)	Enable iteration/summation over states	?
Fintype.card	Calculate size of state space	
Cardinality	Nat.choose	Used in cardinality formula ( 
M
N+M−1
​
 )	
Equiv between OmegaBE and Sym (Fin N) M	Connect state space to multiset cardinality	
Fintype.card_congr	Use the equivalence for cardinality calculation	
Sym.card_sym_eq_multichoose	Relate Sym cardinality to Nat.multichoose	
Nat.multichoose_eq	Relate multichoose to choose (Stars and Bars)	
Nat.choose_pos (or similar)	Prove ( 
M
N+M−1
​
 )>0	?
Normalization	Finset.sum	Summation operator	
Finset.sum_const	Key theorem for summing the constant probability	
nsmul_eq_mul (or implicit)	Relate • to * in ℝ≥0	
NNReal.inv, NNReal.mul, NNReal.coe_nat_cast	Define p_BE, handle coercions	
mul_inv_cancel (for ℝ≥0)	Final step in normalization proof	?
Tactics	simp, infer_instance, linarith, positivity	Proof automation	
  
6. Applying Rota's Entropy Theorem (RET)
Once the probability distributions p 
MB
​
 , p 
FD
​
 , and p 
BE
​
  are defined on their respective Fintype state spaces (α 
MB
​
 , α 
FD
​
 , α 
BE
​
 ) and proven to sum to 1, RET can be applied.

6.1. Mapping Distributions to Fin k → ℝ≥0
Requirement: The formalized RotaEntropyTheorem likely operates on a canonical probability space type, such as functions from Fin k to ℝ≥0 for some k. The distributions defined above map from custom types α 
MB
​
 , α 
FD
​
 , α 
BE
​
 .
Strategy: Mathlib provides a standard way to bridge this gap using Fintype.equivFin. For any Fintype α, Fintype.equivFin α provides an equivalence e : α ≃ Fin (Fintype.card α). Let k=Fintype.card α. Given a distribution p:α→R 
≥0
​
 , a corresponding distribution p 
′
 :Fin k→R 
≥0
​
  can be defined by composition with the inverse equivalence: p 
′
 (i):=p(e.symm(i)).   
Verification: It must be shown that if ∑ 
x:α
​
 p(x)=1, then ∑ 
i:Fin k
​
 p 
′
 (i)=1. This follows from standard Mathlib lemmas about summation over equivalences, such as Equiv.sum_comp or Finset.sum_equiv, which state that the sum remains invariant when composing the function with an equivalence and summing over the corresponding range.
Alternative: If the existing RotaEntropyTheorem was proven generically for any Fintype α, this mapping step might be unnecessary. The exact type signature of the theorem should be checked. Assuming it requires Fin k → ℝ≥0, the mapping is needed. This highlights a common practice in formalization: adapting specific instances to the types required by general theorems.
6.2. Stating Application Theorems
Let p 
MB_fin
​
 , p 
FD_fin
​
 , p 
BE_fin
​
  be the distributions transported to the appropriate Fin k → ℝ≥0 type using Fintype.equivFin. The application of RET is then straightforward:

Lean

theorem H_MB_eq_C_shannon (hH : IsEntropyFunction H) {N M : ℕ} (hN : N > 0) (hM : M > 0) :
  H (p_MB_fin hN hM) = C * stdShannonEntropyLn (p_MB_fin hN hM) := by
  apply RotaEntropyTheorem hH (p_MB_fin hN hM) -- Assuming p_MB_fin is proven to sum to 1

theorem H_FD_eq_C_shannon (hH : IsEntropyFunction H) {N M : ℕ} (h_le : M ≤ N) :
  H (p_FD_fin h_le) = C * stdShannonEntropyLn (p_FD_fin h_le) := by
  apply RotaEntropyTheorem hH (p_FD_fin h_le)

theorem H_BE_eq_C_shannon (hH : IsEntropyFunction H) {N M : ℕ} (hN_pos : N > 0) :
  H (p_BE_fin hN_pos) = C * stdShannonEntropyLn (p_BE_fin hN_pos) := by
  apply RotaEntropyTheorem hH (p_BE_fin hN_pos)
The proofs consist essentially of invoking the main theorem RotaEntropyTheorem, provided the transported distributions are shown to satisfy its preconditions (being valid probability distributions on the correct type).

6.3. Calculating Specific Entropies
For the uniform distributions FD and BE, the Shannon entropy takes a simple form. If p is uniform on a Fintype α with cardinality k=Fintype.card α, then p(x)=1/k for all x. The Shannon entropy is:
stdShannonEntropyLn(p)=−∑ 
x:α
​
 p(x)ln(p(x))=−∑ 
x:α
​
  
k
1
​
 ln( 
k
1
​
 )
=−k×( 
k
1
​
 ln( 
k
1
​
 ))=−ln( 
k
1
​
 )=ln(k).

Applying this to the FD and BE cases, using their respective cardinalities:

For FD: stdShannonEntropyLn(p 
FD_fin
​
 )=ln(Fintype.card Ω 
FD
​
 )=ln(( 
M
N
​
 )). Corollary: H p_FD_fin = C * Real.log (Nat.choose N M)
For BE: stdShannonEntropyLn(p 
BE_fin
​
 )=ln(Fintype.card Ω 
BE
​
 )=ln(( 
M
N+M−1
​
 )). Corollary: H p_BE_fin = C * Real.log (Nat.choose (N + M - 1) M)
For MB, the distribution p 
MB
​
  is generally non-uniform, depending on the weights W 
MB
​
 (q). The Shannon entropy is given by the full sum stdShannonEntropyLn(p 
MB_fin
​
 )=−∑ 
q
​
 p 
MB
​
 (q)ln(p 
MB
​
 (q)), which does not simplify to a logarithm of the cardinality. RET still guarantees H(p 
MB_fin
​
 )=C×stdShannonEntropyLn(p 
MB_fin
​
 ), determining the value of any valid entropy function H on this distribution.

7. Potential Challenges and Recommendations
Several aspects of this formalization plan warrant careful attention:

7.1. Fintype Instance for MBMacrostate N M / OmegaBE N M: This appears to be the most significant prerequisite requiring proof construction. The type { q : Fin N → ℕ // ∑ i, q i = M } needs a Fintype instance.
Recommendation: Explore Mathlib.Combinatorics.Composition for theorems about integer compositions. Investigate Mathlib.Data.Sym.Card  and Mathlib.Data.Multiset.Fintype  for connections between functions summing to M and multisets of size M. Search for an existing Equiv between MBMacrostate N M and Sym (Fin N) M. If no direct equivalence or instance is found, constructing the Finset.univ element explicitly, possibly via induction or by mapping from another known Fintype, will be necessary.   
7.2. MB Normalization Proof: The proof relies on correctly applying the Multinomial Theorem (Finset.sum_pow).
Recommendation: Carefully examine the precise statement and type signature of Finset.sum_pow in Mathlib4, ensuring compatibility with ℝ≥0 or proving the identity first in ℕ and then coercing. Pay close attention to the indexing set used in the summation (s.sym n or similar) and verify it correctly corresponds to MBMacrostate N M when x i = 1.
  
7.3. BE Cardinality Proof: This hinges on the stars and bars result, accessed via multisets (Sym) in Mathlib.
Recommendation: Focus on finding or constructing the Equiv between MBMacrostate N M (i.e., OmegaBE N M) and Sym (Fin N) M. Once established, the proof follows by chaining Fintype.card_congr , Sym.card_sym_eq_multichoose , and Nat.multichoose_eq.   
7.4. Positivity Proofs: Ensuring denominators like N 
M
 , ( 
M
N
​
 ), and ( 
M
N+M−1
​
 ) are positive requires explicit proof steps or appropriate hypotheses.
Recommendation: Utilize the positivity tactic  whenever applicable. For manual proofs, search Mathlib for specific lemmas like Nat.pow_pos , Nat.choose_pos, typically located near the definitions in files like Data.Nat.Basics, Algebra.GroupPower.Order, or Data.Nat.Choose.Basic. Ensure necessary preconditions (e.g., N>0, M≤N) are included as hypotheses in relevant definitions and lemmas.   
7.5. Type Compatibility for RET: The defined distributions must be adapted to the type expected by RotaEntropyTheorem, likely Fin k → ℝ≥0.
Recommendation: Employ Fintype.equivFin  to create the mapping. Use Equiv.sum_comp or a similar lemma to prove that the transported distribution still sums to 1. Verify the exact type signature of the proven RotaEntropyTheorem to confirm the target type.   
8. Conclusion
8.1. Summary
This report has outlined a detailed strategy for formalizing the Maxwell-Boltzmann, Fermi-Dirac, and Bose-Einstein probability distributions within Lean 4 using the Mathlib4 library. The plan involves:

Defining the appropriate state spaces (OmegaMB, OmegaFD, OmegaBE) using function types, subtypes of Finset, and subtypes of function types (MBMacrostate).
Establishing Fintype instances for these spaces, noting the potential complexity for MBMacrostate/OmegaBE.
Calculating the cardinalities of these spaces using Fintype.card and specific Mathlib combinatorial results (Fintype.card_pi, Nat.choose, Nat.multinomial, Nat.multichoose, Sym.card_sym_eq_multichoose).
Defining the probability distributions (p_MB, p_FD, p_BE) using ℝ≥0, incorporating statistical weights (W_MB) where necessary.
Proving normalization (∑p=1) using the Multinomial Theorem (Finset.sum_pow) for MB and Finset.sum_const for the uniform FD and BE cases.
Mapping these distributions to the type required by Rota's Entropy Theorem using Fintype.equivFin and applying the theorem.
Key Mathlib4 components, including specific types, definitions, theorems, and tactics, have been identified for each step.

8.2. Path Forward
This roadmap provides the necessary blueprint and identifies the essential Mathlib4 tools and potential challenges for the next phase of the project. The subsequent step involves the direct implementation of these definitions and proofs within the PPNP/Entropy/Physics.lean file. While the prior proof of Rota's Entropy Theorem simplifies the ultimate calculation of entropy values for functions satisfying the required axioms, the core task outlined here—the rigorous formalization of the combinatorial structures and probability spaces underlying statistical mechanics—remains a substantial undertaking that will significantly enhance the formal mathematical treatment of this area within Lean.


Sources used in the report

leanprover-community.github.io
Mathlib.Data.Real.Sqrt
Opens in a new window

florisvandoorn.com
Mathlib.Data.Finset.Defs
Opens in a new window

leanprover-community.github.io
data.fintype.pi - mathlib3 docs - Lean community
Opens in a new window

leanprover-community.github.io
data.finset.card - mathlib3 docs - Lean community
Opens in a new window

leanprover-community.github.io
data.real.nnreal - mathlib3 docs - Lean community
Opens in a new window

en.wikipedia.org
Multinomial theorem - Wikipedia
Opens in a new window

leanprover-community.github.io
Mathlib.Data.Fintype.Card - Lean community
Opens in a new window

leanprover-community.github.io
Mathlib.Data.Fintype.Pi
Opens in a new window

github.com
mathlib3/src/data/fintype/basic.lean at master - GitHub
Opens in a new window

leanprover-community.github.io
data.nat.choose.multinomial - mathlib3 docs - Lean community
Opens in a new window

leanprover-community.github.io
Mathlib.Data.Fintype.Basic - Lean community
Opens in a new window

github.com
mathlib3/src/data/multiset/fintype.lean at master - GitHub
Opens in a new window

plmlab.math.cnrs.fr
Mathlib/Algebra/GroupPower/Order.lean · forward-port-19105-v2 · Filippo Nuccio / mathlib4
Opens in a new window

leanprover-community.github.io
Mathlib.Logic.Equiv.Fintype - Lean community
Opens in a new window

leanprover-community.github.io
Mathlib.Algebra.BigOperators.Group.Finset.Basic - Lean community
Opens in a new window

leanprover-community.github.io
Mathlib.Tactic.Positivity.Core - Lean community
Opens in a new window

terrytao.wordpress.com
A slightly longer Lean 4 proof tour | What's new - Terence Tao
Opens in a new window

en.wikipedia.org
Stars and bars (combinatorics) - Wikipedia
Opens in a new window

leanprover-community.github.io
Mathlib.Data.Sym.Card - Lean community
Opens in a new window

cp-algorithms.com
Stars and bars - Algorithms for Competitive Programming