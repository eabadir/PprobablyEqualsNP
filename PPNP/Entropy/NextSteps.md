# Where are we now, and where are we going?

---

## Table of Contents
- [Phase 2: Bridging Physics, Decisions, and Computability](#phase-2-bridging-physics-decisions-and-computability)
  - [1. Physical Systems as Constrained Counting Problems (Recap)](#1-physical-systems-as-constrained-counting-problems-recap)
  - [2. Microstates as Solutions to Boolean Formulas (SAT Instances)](#2-microstates-as-solutions-to-boolean-formulas-sat-instances)
  - [3. Decision Problems and Shannon Entropy](#3-decision-problems-and-shannon-entropy)
  - [4. From Yes/No Questions to Boolean Circuits and Time Complexity](#4-from-yesno-questions-to-boolean-circuits-and-time-complexity)
- [Phase 2 Formalization Goals](#phase-2-formalization-goals)
- [Review of Current Status: Phase 1 Complete](#review-of-current-status-phase-1-complete)
- [Phase 1 Code vs. Rota's Proof (`RET_Excerpt.tex`)](#phase-1-code-vs-rotas-proof-ret_excerpttex)

---

## Phase 2: Bridging Physics, Decisions, and Computability
Okay, this is a great addition to set the stage for why Shannon entropy is so central to the "computational effort" idea. Here's a proposed introductory section for the README, incorporating these concepts and trying to bridge them for readers unfamiliar with coding theory or Lean:

---

### The Computational Essence of Entropy: From Particle Paths to Bits

At the heart of Rota's Entropy Theorem (RET) and its implications for physics lies a profound connection to **information theory**, specifically **Shannon's Source Coding Theorem**. To understand this bridge, we first need to reframe how we think about physical systems and their evolution.

### Particle Trajectories as Symbols from a Source

Imagine a physical system composed of $M$ particles evolving over a period of time $t$. Instead of looking at an instantaneous snapshot (a microstate), consider the **entire trajectory** or path of a single particle through its available states over this time window. We can conceptualize this entire path as a single "symbol" $s$.

*   **Source (S):** The physical process generating these particle paths can be thought of as a "source" $S$.
*   **Alphabet:** The "alphabet" of this source is the set of all possible trajectories a particle can take.
*   **Probability Distribution (P(s)):** Each possible trajectory $s$ has an associated probability $P(s)$ of occurring, determined by the underlying physics.
*   **Symbol Entropy (H(S)):** The Shannon entropy of this source is then:
    $H(S) = -\sum_{s} P(s) \log_2 P(s)$ bits per trajectory/symbol.

This $H(S)$ quantifies the average "surprise" or "information content" associated with observing one specific particle trajectory.

### Shannon's Source Coding Theorem: The Optimal Compression Limit

Shannon's Source Coding Theorem is a cornerstone of information theory. In essence, it states that:

> The minimum average number of bits required to losslessly represent (encode) a symbol drawn from a source $S$ is equal to its Shannon entropy $H(S)$.

*   **Codes:** A "code" is a mapping from symbols (our particle trajectories) to sequences of bits (typically `0`s and `1`s). A good code is **prefix-free**, meaning no codeword is the prefix of another, allowing unambiguous decoding.
*   **Expected Length:** For a code $C$ and symbols $s$ drawn from source $S$, $\mathbb{E}[\ell(C(s))]$ is the average length (in bits) of the encoded symbols.
*   **The Theorem (Informal):** You can find a prefix-free code such that the average number of bits you use per symbol is very close to $H(S)$ (specifically, less than $H(S) + \epsilon$ for any small $\epsilon > 0$, especially when encoding blocks of symbols). Crucially, no code can achieve an average length per symbol asymptotically less than $H(S)$.

**Analogy for Lean Users:**
Think of a Lean `inductive type` representing all possible particle trajectories. Each constructor (or a specific value of this type) is a "symbol" $s$. `P(s)` would be a function assigning a probability (perhaps an `NNReal`) to each such symbol. $H(S)$ is then a `Real` number calculated from these probabilities using `stdShannonEntropyLn`. The Source Coding Theorem tells us that if we wanted to "serialize" or "transmit" which specific trajectory occurred using the fewest average bits, $H(S)$ is our fundamental limit.

### Encoding Multiple Independent Particle Paths

Now, consider our system of $M$ **independent** particles. Each particle $i$ generates its own trajectory-symbol $s_i$ from an identical source $S$.

*   **Total Information:** To describe the state of the entire system (i.e., all $M$ trajectories), we need to encode $s_1, s_2, \dots, s_M$.
*   **Optimal Encoding:** By the Source Coding Theorem, each $s_i$ can be encoded using approximately $H(S)$ bits on average. Since the particles are independent, the information adds up.
*   **Total Average Bit-Length:** The total average number of bits to encode all $M$ trajectories is approximately $M \times H(S)$.

**Bottom Line:**
The minimum average number of bits needed to describe the complete evolution (all $M$ trajectories) of this system over time $t$ is $M \cdot H(S)$. No encoding scheme can be asymptotically more efficient.

If we consider the "length" of each trajectory in physical time to be $t$, then the **bit-rate** required to describe the system's evolution is $(M \cdot H(S)) / t$ bits per unit time.

### Connecting to Rota's Theorem and Computability

Rota's Entropy Theorem states that physical entropy (like that of MB, FD, BE distributions, which describe instantaneous microstates) is a scaled form of Shannon entropy. Our project extends this by viewing the problem of determining an instantaneous microstate or a sequence of them (leading to a trajectory) through the lens of information and computation:

1.  **Microstates as Symbols:** An instantaneous microstate $\omega$ of an MB/FD/BE system can itself be considered a "symbol" drawn from a distribution $D$ with entropy $H(D)$.
2.  **Determining a Microstate as Decoding:** Identifying *which* microstate $\omega$ occurred is analogous to decoding a received symbol.
3.  **Number of Questions = Bits:** The Source Coding Theorem implies that, on average, $H(D)$ bits are necessary and sufficient to specify $\omega$. These "bits" can be interpreted as answers to optimal binary (yes/no) questions.
4.  **Questions to Computations:** As explored in Phase 2, a sequence of yes/no questions can be mapped to a Boolean circuit, and the number of gates in this circuit (and thus computational time) is proportional to the number of questions.

Therefore, the Shannon entropy $H(D)$ of a physical distribution is not just an abstract measure of disorder or uncertainty; it reflects the **fundamental number of binary decisions or computational operations** required, on average, to specify the system's state. This perspective is key to our goal of formalizing the computability and complexity inherent in physical systems.

---

This introductory section aims to provide the conceptual scaffolding:
*   It introduces "codes" and "symbols" in a way that can be mapped to particle trajectories.
*   It explains Shannon's Source Coding Theorem and its relevance to minimal description length.
*   It connects this to the idea of describing $M$ independent particles.
*   It then (briefly, as the next section will elaborate) links this back to how we'll approach instantaneous microstates in MB/FD/BE systems via RET and the "questions to computations" bridge for Phase 2.

This should help readers understand why Shannon entropy and "bits" are so central to the project's thesis about the computational nature of physical entropy.

Phase 1 established that for uniform distributions (like those characterizing Bose-Einstein systems), any entropy measure satisfying Rota's axioms is proportional to Shannon entropy (`H_physical_system(p_uniform) = C * stdShannonEntropyLn(p_uniform)`). Phase 2 aims to deepen this connection by:

1.  Completing the formalization for Fermi-Dirac (FD) and Maxwell-Boltzmann (MB) statistics, demonstrating their entropy also conforms to this scaled Shannon form.
2.  Building a formal bridge from these physical distributions to computational complexity, showing that determining the state of such a system is equivalent to solving a specific kind of decision problem, whose complexity is directly related to its Shannon entropy.

Our approach in Phase 2 involves several conceptual steps, which will be formalized in Lean:

### 1. Physical Systems as Constrained Counting Problems (Recap)

As established, MB, FD, and BE statistics describe ways of distributing $M$ particles into $N$ states ("balls into boxes") under different constraints:
*   **MB:** Distinguishable particles, unlimited occupancy.
*   **FD:** Indistinguishable particles, at most one per state (Pauli exclusion).
*   **BE:** Indistinguishable particles, unlimited occupancy.

Each valid configuration of particles and states is a **microstate**. The fundamental assumption is that all valid microstates are equiprobable, leading to uniform distributions over their respective state spaces.

### 2. Microstates as Solutions to Boolean Formulas (SAT Instances)

The core idea for bridging to computability is to represent the problem of "identifying a microstate" as a **Boolean Satisfiability (SAT) problem**. For each statistical distribution $D \in \{\text{MB, FD, BE}\}$:

*   **Define Boolean Variables:** We introduce Boolean variables that capture the state of the system.
    *   For MB/FD: $x_{p,i}$ could mean "particle $p$ is in state $i$."
    *   For BE: $y_{i,k}$ could mean "state $i$ contains at least $k$ particles." (This allows encoding counts).
*   **Formulate Constraints as Propositional Logic:** The rules governing each distribution are translated into a Boolean formula ($\varphi_D$) using AND ($\land$), OR ($\lor$), and NOT ($\neg$) connectives.
    *   **MB ($\varphi_{\text{MB}}$):** Each particle $p$ must be in exactly one state $i$: $\bigwedge_p (\bigvee_i x_{p,i}) \land \dots$ (plus clauses for "not in two states").
    *   **FD ($\varphi_{\text{FD}}$):** Starts with $\varphi_{\text{MB}}$ and adds the exclusion principle: $\bigwedge_i \bigwedge_{p \neq q} (\neg x_{p,i} \lor \neg x_{q,i})$ (for any state $i$, particles $p$ and $q$ cannot both be in it).
    *   **BE ($\varphi_{\text{BE}}$):** Constraints on $y_{i,k}$ ensure consistency (e.g., if state $i$ has at least $k$ particles, it must also have at least $k-1$), plus a global constraint that the total number of particles is $M$.

The crucial link is:
> A configuration $\omega$ is a valid microstate under distribution $D$ **if and only if** $\omega$ corresponds to a satisfying assignment for the Boolean formula $\varphi_D$.

Thus, identifying a microstate is equivalent to finding a satisfying assignment for $\varphi_D$.

### 3. Decision Problems and Shannon Entropy

Identifying a specific microstate $\omega$ from the set of all possible microstates (given its probability $P(\omega)$) can be framed as a sequence of "yes/no" questions. **Shannon's Source Coding Theorem** provides a fundamental limit: the minimum average number of optimal binary (yes/no) questions needed to identify a microstate is given by the Shannon entropy of the distribution $H(D) = -\sum P(\omega) \log_2 P(\omega)$.

Since determining a microstate is equivalent to solving the SAT instance $\varphi_D$, the number of questions needed to resolve the SAT instance (i.e., find a satisfying assignment or determine properties of it) is also fundamentally linked to $H(D)$. The "size" of the SAT problem (number of variables/clauses, related to $N$ and $M$) and the depth of an optimal decision tree for solving it are expected to be related to $H(D)$. For uniform distributions where $P(\omega) = 1/|\Omega_D|$, $H(D) = \log_2 |\Omega_D|$.

### 4. From Yes/No Questions to Boolean Circuits and Time Complexity

The conceptual bridge from information (number of questions) to computation (time) is built as follows:

*   **Yes/No Questions as Boolean Gates:** Each binary decision ("Is variable $x_{p,i}$ true?") can be modeled as evaluating a Boolean input or a simple Boolean operation. A sequence of $Q$ such questions can be represented as a Boolean circuit composed of AND, OR, NOT gates. The number of gates in this circuit will be proportional to $Q$.
    *   Formal Lean Statement: `("Q yes/no questions") ⟹ (∃ Boolean Circuit C with |gates(C)| ≈ Q)`
*   **Boolean Circuits as Programs:** A Boolean circuit can be directly implemented as a program where each gate corresponds to one or a few elementary computational instructions.
*   **Gate Count as Time Complexity:** Executing the program means evaluating each gate. If a circuit has $Q_{gates}$ gates, the program takes roughly $Q_{gates}$ steps. This leads to a time complexity of $\mathcal{O}(Q_{gates})`.
    *   Formal Lean Statement: `("Circuit C with Q gates") ⟹ (∃ Program P implementing C with Time(P) = O(Q))`

Combining these, a sequence of $Q$ yes/no questions implies a computational time complexity of $\mathcal{O}(Q)$. If the number of questions needed to determine a microstate is $H(D)$, then the computational complexity associated with processing or identifying information about that microstate is related to $\mathcal{O}(H(D))$.

### Phase 2 Formalization Goals:

*   **Complete FD and MB:** Implement the state spaces and entropy theorems for FD and MB distributions, showing their entropy is $C \cdot \text{stdShannonEntropyLn}$.
*   **Boolean Logic Primitives:** Define Boolean expressions/circuits, their evaluation, and measures like gate count in Lean.
*   **SAT Encodings:** Formalize the construction of Boolean formulas $\varphi_D$ for MB, FD, and BE, proving (or stating as a goal for later proof) the equivalence: "$\omega$ is a valid microstate $\iff \omega$ satisfies $\varphi_D$."
*   **Complexity Links:** Formalize the implications: "Q questions $\implies \mathcal{O}(Q)$ circuit size" and "Circuit size $\implies $\mathcal{O}(\text{size})$ time."
*   **Connecting Entropy to Complexity:** The ultimate aim is to formally show that the number of operations (related to circuit size or decision tree depth for $\varphi_D$) scales with the Shannon entropy $H(D)$ of the physical system.

This phase will transform the `sorry` placeholders related to computability and complexity into concrete Lean definitions and theorems, demonstrating that the entropy of these physical systems isn't just an abstract quantity but is deeply tied to the computational resources needed to describe or determine their states.

---

This section outlines the conceptual journey. The actual Lean implementation will involve careful definitions of types for Boolean variables, clauses, circuits, and proving properties about their sizes and evaluation, then linking these to the combinatorial structures of MB, FD, and BE.

## Review of Current Status: Phase 1 Complete

The `RET_README.md` provides a high-level overview of Rota's Entropy Theorem, its significance, and the project's goals and phased approach.



## Phase 1 Code vs. Rota's Proof (`RET_Excerpt.tex`)

The core of Rota's "Uniqueness of Entropy" proof in `RET_Excerpt.tex.txt` revolves around defining a function `f(n) = H(1/n, ..., 1/n)` and proving `f(n) = C * log n`. Let's map this to your Lean code:

**Rota's Properties of Entropy (from TeX excerpt and your `HasRotaEntropyProperties`):**

1.  **Definition on Probability Sets:**
    *   TeX: "defined on sets \(\{p_1, ..., p_n\}\) of non-negative real numbers, which satisfy \(\sum p_i = 1\)."
    *   Lean: `H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal`. The domain `(α → NNReal)` combined with conditions like `∑ i, p i = 1` (e.g., in `probabilitySimplex` or as hypotheses) matches this. `NNReal` handles non-negativity.
    *   **Congruence:** Good.

2.  **Dependence on Nonzero Probabilities (Zero Invariance):**
    *   TeX: "H(p₁, ..., pₙ, 0) = H(p₁, ..., pₙ)."
    *   Lean: `IsEntropyZeroInvariance H_func` with `zero_invariance` field.
    *   **Congruence:** Good.

3.  **Continuity:**
    *   TeX: "An entropy function is continuous." (Rota notes it could be derived).
    *   Lean: `IsEntropyContinuous H_func` with `continuity` field.
    *   **Congruence:** Good, Lean takes it as an axiom for `H_func`.

4.  **Additivity via Conditional Entropy:**
    *   TeX: "H(π|σ) = H(π) - H(σ)" where H(π|σ) = ∑ P(σᵢ)H(π|σᵢ).
    *   Lean: `IsEntropyCondAdd H_func` with `cond_add`: `H_func (DependentPairDist prior P_cond) = H_func prior + ∑ i, prior i * H_func (fun j => P_cond i j)`. This is the direct form Rota uses for deriving `f(nm) = f(n) + f(m)`.
    *   **Congruence:** Good. This is the key additive property.

5.  **Maximum Entropy for Uniform Distribution:**
    *   TeX: "H(p₁, ..., pₙ) ≤ H(1/n, ..., 1/n)."
    *   Lean: `IsEntropyMaxUniform H_func` with `max_uniform`.
    *   **Congruence:** Good.

**Rota's Proof Steps for Uniqueness (and Lean equivalents in `RET.lean`):**

1.  **Define `f(n) = H(1/n, ..., 1/n)`:**
    *   TeX: `f(n) = H(1/n, ..., 1/n)`.
    *   Lean: `f0 hH_axioms n` (which is `H_func (uniformDist ...)` for `n > 0`, and 0 for `n=0`).
    *   **Congruence:** Good.

2.  **`f(1) = 0`:**
    *   TeX: "entropy of the partition consisting of just one block ... is zero."
    *   Lean: `f0_1_eq_0` theorem, derived from `IsEntropyNormalized`. (Rota's excerpt implies normalization is part of Property 1 or derived early).
    *   **Congruence:** Good.

3.  **`f(n)` is increasing:**
    *   TeX: "Using properties 2 and 5, we show that f(n) is increasing: f(n) ≤ f(n+1)."
    *   Lean: `f0_mono` theorem, derived using `zero_invariance` (Property 2) and `max_uniform` (Property 5).
    *   **Congruence:** Perfect.

4.  **`f(n^k) = k f(n)`:**
    *   TeX: Derived by considering a partition of `n^k` blocks, then subdividing each into `n` parts, using conditional entropy. "The conditional entropy ... for each block ... is clearly given by f(n). Thus the conditional entropy H(π|σ) is f(k) - f(k-1)" - this seems to be a typo in the excerpt, it should be related to `f(n^k) = f(n^{k-1}) + f(n)`. The excerpt jumps to `f(n^k) = kf(n)`.
    *   Lean:
        *   `f0_mul_eq_add_f0 hH_axioms hn_pos hm_pos : f0 hH_axioms (n * m) = f0 hH_axioms n + f0 hH_axioms m`. This is derived from `IsEntropyCondAdd` by constructing an independent product of two uniform distributions and showing it's equivalent to a single larger uniform distribution. This is the crucial step.
        *   `uniformEntropy_power_law hH_axioms hn_pos hk_pos : f0 hH_axioms (n ^ k) = (k : NNReal) * f0 hH_axioms n`. This is derived by induction using `f0_mul_eq_add_f0` (via `f0_pow_succ_step`).
    *   **Congruence & Discrepancy:** The result `f(n^k) = kf(n)` is the same. The derivation path in Lean (`f(nm)=f(n)+f(m)` then induction) is standard for proving `f(n^k)=kf(n)` for functions satisfying `f(nm)=f(n)+f(m)`. Rota's excerpt is a bit hand-wavy on this step ("apply this fact k times"). Your Lean proof is more explicit and sound.

5.  **Trapping Argument (`b/k ≤ f(n)/f(2) ≤ (b+1)/k` and `b/k ≤ log₂(n) ≤ (b+1)/k`):**
    *   TeX: Uses integers `b, k` such that `2^b ≤ n^k < 2^{b+1}` (error in excerpt, should be `b^j <= n^k < b^{j+1}` or similar, later uses base 2 like `2^b <= n^k < 2^{b+1}` implies `f(2^b) <= f(n^k) <= f(2^{b+1})` leading to `b f(2) <= k f(n) <= (b+1) f(2)`). Then divides to get bounds on `f(n)/f(2)`. Similar argument for `log₂(n)`. Concludes `|f(n)/f(2) - log₂(n)| ≤ 1/k`.
    *   Lean:
        *   `k_from_f0_trap_satisfies_pow_bounds_real`: For `n, m, b`, finds `k` such that `b^k ≤ n^m < b^(k+1)` (power bounds) AND `k/m ≤ (f0 H n)/(f0 H b) ≤ (k+1)/m` (ratio bounds for `f0` values). This uses `f0_mono` and `uniformEntropy_power_law`.
        *   `logarithmic_trapping`: Shows `|(f0 H n)/(f0 H b) - logb b n| ≤ 1/m`. This uses the previous lemma and properties of `logb`.
    *   **Congruence & Discrepancy:** The core idea of trapping between powers and using monotonicity is the same. Lean uses a more general base `b` (typically `b=2` for Shannon bits, or `b=e` for nats) and `logb` and allows an arbitrary `m` for the squeeze. Rota's TeX excerpt specializes to base 2 for `f(2)`. The division by `m` in the Lean version effectively allows the `1/k` (from Rota's `k`) to become arbitrarily small by choosing large `m`.

6.  **Conclusion `f(n) = C log n`:**
    *   TeX: `f(n)/f(2) = log₂(n)`, so `f(n) = f(2) log₂(n)`. Defines `C = -f(2)` (the minus sign seems unusual here, usually C is positive, and `f(2)` for entropy is non-negative). Rota later uses this for `p_i = a_i/N` and arrives at `H(\sigma) = -C \log_2(N) + C \sum p_i \log_2(a_i)` which simplifies to `C \sum p_i \log_2(1/p_i)`.
    *   Lean:
        *   `uniformEntropy_ratio_eq_logb`: `(f0 H n)/(f0 H b) = logb b n`.
        *   `C_constant_real hH_axioms := (f0 hH_axioms 2 : ℝ) / Real.log 2` (if non-trivial).
        *   `RotaUniformTheorem_formula_with_C_constant`: `(f0 hH_axioms n : ℝ) = C_val * Real.log n`. This is derived from `uniformEntropy_ratio_eq_logb` by setting `b=2` (or any base, then converting logs).
    *   **Congruence:** The final form `f(n) = C * log n` is achieved. The constant `C` is defined slightly differently but serves the same purpose. Lean uses natural log by default for `Real.log` and `stdShannonEntropyLn`, then `C_constant_real` adapts it. Rota's excerpt leans towards `log₂`. This is just a choice of base.

**Overall Congruence:** The Lean formalization in `RET.lean` very closely follows the spirit and key steps of Rota's uniqueness proof. It's more rigorous in places (e.g., derivation of `f(n^k)=kf(n)`) and uses standard Mathlib tools for real numbers and logarithms.

## Verification of BE/Uniform Implementation (No Circularity)

I looked at this in the thought process.
*   `OmegaUD N M` is defined as occupancy vectors `{ q : Fin N → ℕ // ∑ i, q i = M }`.
*   `udStateEquivMultiset` proves `OmegaUD N M ≃ SymFin N M` (multisets).
*   `card_omega_be` uses this equivalence and `Sym.card_sym_eq_multichoose` (Mathlib's stars and bars result for multisets) to correctly derive `Fintype.card (OmegaUD N M) = Nat.multichoose N M`.
*   `p_UD N M` (for BE) is `fun _q => uniformProb (Fintype.card (OmegaUD N M))`. This defines a uniform distribution over the *derived* cardinality.

**Conclusion:** The implementation correctly derives the cardinality of the BE state space using combinatorial principles *first* and *then* defines a uniform probability distribution over these states. There is no circularity. The "axiom" mentioned in the README that "only axiom is uniform on the state space" refers to the physical assumption of equiprobable microstates, which is then correctly translated into the definition of `p_UD`.

## Opinion on Phase 1 Implementation

Phase 1 appears to be **very well implemented** regarding its stated goals:
1.  **RET for Uniform Distributions (`RET.lean`):** This is robustly proven, based on the `HasRotaEntropyProperties` axioms. It successfully establishes `f0 H n = C * Real.log n`.
2.  **BE within PhysicsDist (`BoseEinstein.lean`, `UniformSystems.lean`):**
    *   The BE state space (`OmegaUD`) is correctly defined and its cardinality derived.
    *   The uniform distribution `p_UD` (aliased as `p_BE`) is correctly defined over this space.
    *   The main theorem `H_BE_from_Multiset_eq_C_shannon` successfully applies the general `RotaUniformTheorem` (via helpers like `H_p_BE_fin_eq_f_H_card` and `H_physical_dist_eq_C_shannon_if_uniform_and_equiv`) to show that for the BE distribution, `H_physical_system(p_BE_fin) = C * stdShannonEntropyLn(p_BE_fin)`.

**Axioms Remaining After Phase 1:**

*   `H_physical_system : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal` (in `Physics.Common`)
*   `H_physical_system_is_HasRotaEntropyProperties : HasRotaEntropyProperties H_physical_system` (in `Physics.Common`)

These are the main axioms. Phase 1 shows that *if* such a physical entropy function exists and satisfies Rota's axioms, *then* for a uniform distribution (like BE's), its value is proportional to Shannon entropy.

The project aims to eventually show that the "true" physical entropy *is* essentially Shannon entropy (or can be modeled by it for these systems), making `H_physical_system` concrete (e.g., `C * stdShannonEntropyLn`) and then `H_physical_system_is_HasRotaEntropyProperties` would become a theorem to prove about `stdShannonEntropyLn`.

No obvious invalidities found in the Phase 1 logic for RET (uniform) or its application to BE.

## Code Structure and Phasing

**Table 1: File/Namespace Roles & Phasing**

| File/Namespace                                | General Role                                                                                                 | Phase 1 State                                                                                                                                         | High-Level TODO for Upcoming Phases                                                                                                                                                                                                                                                              |
| :-------------------------------------------- | :----------------------------------------------------------------------------------------------------------- | :---------------------------------------------------------------------------------------------------------------------------------------------------- | :------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `PPNP.Entropy.Common`                         | Basic definitions: `uniformProb`, `uniformDist`, `stdShannonEntropyLn`, `HasRotaEntropyProperties` structure & components. | Foundational, complete for Phase 1.                                                                                                                     | Likely stable. Minor additions if FD/MB need new distribution construction helpers.                                                                                                                                                                                            |
| `PPNP.Entropy.RET`                            | Proof of Rota's Uniform Theorem: `f0 H n = C * log n`.                                                       | Core of Phase 1, complete. Derives `C_constant_real`.                                                                                                   | Stable. This is the main mathematical engine for RET.                                                                                                                                                                                                                            |
| `PPNP.Entropy.Physics.Common`                 | Common types/axioms for physics: `MBMacrostate`, `UDMacrostate`, `SymFin`, `H_physical_system` axiom.          | Defines `H_physical_system` axiomatically. Defines state space building blocks.                                                                       | The axiom `H_physical_system_is_HasRotaEntropyProperties` is central. Phase 2/3 may make `H_physical_system` concrete (e.g. `stdShannonEntropyLn`) and turn this axiom into a theorem. Add FD state space type.                                                                           |
| `PPNP.Entropy.Physics.UniformSystems`         | Helpers for uniform systems, `canonicalUniformDist`, `OmegaUD` (for BE/MB-like), `p_UD`. `H_physical_dist_eq_C_shannon_if_uniform_and_equiv`. | Defines `OmegaUD` (occupancy vectors for BE), proves its properties. Key bridging theorems.                                                             | Logic for `OmegaUD` is specific to systems where particles are indistinguishable and states distinguishable (BE) or where total particle count in distinguishable states matters. FD will need a new `OmegaFD` type (subsets) and related proofs. MB may use `Fin N → Fin M` or similar. |
| `PPNP.Entropy.Physics.BoseEinstein`           | Application of `UniformSystems` logic to Bose-Einstein statistics.                                           | Complete for BE. Uses `OmegaUD`, `p_UD`. Proves `card_omega_be = Nat.multichoose N M`. Theorem `H_BE_from_Multiset_eq_C_shannon`.                     | Stable. Serves as a template for `FermiDirac.lean` and `MaxwellBoltzmann.lean`.                                                                                                                                                                                    |
| `PPNP.Entropy.Physics.PhysicsDist`            | Placeholder/overview for all physics distributions, definition of a generic "Physics Distribution".            | Minimal (comments and imports).                                                                                                                       | **Phase 2/3:** Implement FD, MB state spaces and entropy theorems. Define a generalized `PhysicsDist` (e.g., as a sum type or a structure that can hold MB/FD/BE). Prove properties for this generalized distribution, potentially its computability.                            |
| `PPNP.Common.Basic` (assumed)                 | Basic utilities for PPNP project.                                                                            | Assumed basic and functional.                                                                                                                         | As needed.                                                                                                                                                                                                                                                                       |
| `RET_lean_proof/Entropy/NextSteps.md`         | Planning document for Phase 2.                                                                               | Input for current task.                                                                                                                               | Update with detailed Phase 2 plan.                                                                                                                                                                                                                                               |
| (New for Phase 2) `PPNP.Complexity.*`       | Modules for Boolean logic, circuits, SAT, complexity models.                                                   | Does not exist yet.                                                                                                                                   | **Phase 2:** Create these modules to formalize concepts from `NextSteps.md`.                                                                                                                                                                                                     |

**Table 2: Notable Constructs by File/Namespace (External Use Focus)**

| File/Namespace                        | Notable Constructs (Theorems/Defs/Axioms)                                                                    | Brief Description                                                                                                                                                                                             |
| :------------------------------------ | :----------------------------------------------------------------------------------------------------------- | :------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `PPNP.Entropy.Common`                 | `HasRotaEntropyProperties` (and its fields like `IsEntropyCondAdd`)                                                 | The axiomatic definition of an entropy function, crucial for `RET.lean`.                                                                                                                                      |
|                                       | `stdShannonEntropyLn`                                                                                        | The standard definition of Shannon entropy used as the target for RET.                                                                                                                                        |
|                                       | `uniformDist`, `sum_uniformDist`                                                                             | Generic uniform distribution and its sum property.                                                                                                                                                            |
|                                       | `stdShannonEntropyLn_uniform_eq_log_card`                                                                    | Key property: Shannon entropy of a uniform distribution is log(cardinality).                                                                                                                                  |
| `PPNP.Entropy.RET`                    | `RotaUniformTheorem`                                                                                         | Main result: `∃ C ≥ 0, ∀ n > 0, (f0 H n : ℝ) = C * Real.log n` for any `H` satisfying `HasRotaEntropyProperties`.                                                                                                        |
|                                       | `C_constant_real`                                                                                            | The proportionality constant `C` emerging from `RotaUniformTheorem`.                                                                                                                                            |
| `PPNP.Entropy.Physics.Common`         | `H_physical_system` (axiom)                                                                                  | Abstract physical entropy function.                                                                                                                                                                           |
|                                       | `H_physical_system_is_HasRotaEntropyProperties` (axiom)                                                             | Assumption that physical entropy satisfies Rota's axioms. Used by BE/FD/MB proofs.                                                                                                                            |
|                                       | `eval_H_phys_system_on_fin_dist_to_real`                                                                     | Coerces `H_physical_system` output to `Real`.                                                                                                                                                                 |
|                                       | `MBMacrostate`, `UDMacrostate`, `SymFin`                                                                     | Building blocks for defining state spaces. `UDMacrostate` is key for `OmegaUD`.                                                                                                                               |
| `PPNP.Entropy.Physics.UniformSystems` | `OmegaUD`, `udStateEquivMultiset`, `fintypeOmegaUD`, `card_omega_ud` (implicit in `p_UD` via `Fintype.card`) | Definition and properties of state space for BE-like systems (occupancy vectors).                                                                                                                             |
|                                       | `p_UD`, `p_UD_fin`                                                                                           | Uniform probability distribution over `OmegaUD` or its `Fin` equivalent.                                                                                                                                      |
|                                       | `H_physical_dist_eq_C_shannon_if_uniform_and_equiv`                                                          | Important theorem linking `H_func` of a generic uniform `p_sys` to its Shannon entropy, if `H_func` is an `HasRotaEntropyProperties` and `Ω_sys ≃ Fin k`. This is used by `BoseEinstein.lean`.                            |
| `PPNP.Entropy.Physics.BoseEinstein`   | `card_omega_be`                                                                                              | Cardinality of BE state space (`Nat.multichoose N M`).                                                                                                                                                        |
|                                       | `H_BE_from_Multiset_eq_C_shannon`                                                                            | Main theorem for BE: `H_physical_system(p_BE)` is proportional to `stdShannonEntropy(p_BE)`. Relies on `H_physical_system_is_HasRotaEntropyProperties`.                                                                  |
| `PPNP.Entropy.Physics.PhysicsDist`    | (Future) `PhysicsDistribution` type                                                                          | Will encapsulate MB, FD, BE and allow reasoning about general physical system entropy and its computability.                                                                                                  |

## Outline Plan for Phase 2 (from `NextSteps.md` and Review)

**Overall Goal for Phase 2:**
Formalize the connection between the "number of yes/no questions" / Boolean circuits and computational complexity (Big-O). Implement missing physics distributions (FD, MB). Begin replacing `sorry`s related to computability in a (hypothetical) `Complexity.Basic.lean`.

**Sub-Goals & Plan:**

1.  **Implement Fermi-Dirac (FD) and Maxwell-Boltzmann (MB) Statistics:**
    *   Create `PPNP.Entropy.Physics.FermiDirac.lean`:
        *   Define `OmegaFD N M := { s : Finset (Fin N) // s.card = M }` (sets of M occupied states out of N).
        *   Prove `Fintype (OmegaFD N M)`.
        *   Prove `Fintype.card (OmegaFD N M) = Nat.choose N M`.
        *   Define `p_FD N M` (uniform distribution over `OmegaFD`).
        *   Prove `H_FD_eq_C_shannon` analogous to the BE theorem, using `H_physical_dist_eq_C_shannon_if_uniform_and_equiv`.
    *   Create `PPNP.Entropy.Physics.MaxwellBoltzmann.lean`:
        *   MB microstates: Each of M distinguishable particles can be in N distinguishable states. Total `N^M` states. Each microstate is a function `Fin M → Fin N`.
        *   Define `OmegaMB N M := Fin M → Fin N`.
        *   Prove `Fintype.card (OmegaMB N M) = N ^ M`.
        *   Define `p_MB N M` (uniform distribution over `OmegaMB`).
        *   Prove `H_MB_eq_C_shannon`.
    *   *(Self-correction based on Rota's description of MB macrostates):* The above `OmegaMB` is for *microstates* if all are equiprobable. Rota's "Macrostate = occupancy vector \(\mathbf{q}=(q_1,\dots,q_N)\) with \(\sum_i q_i=M\)" means the MB *macrostates* (if particles are distinguishable but we only care about counts in boxes) are like `OmegaUD`. The number of microstates per macrostate is the multinomial coefficient. If the project assumes equiprobable *microstates* for MB, then `N^M` is correct. If it means equiprobable *macrostates* (unlikely for standard MB), it would be different. The README implies equiprobable microstates are fundamental. The statement `Ω_{MB}` has size `N^M` in the README sketch points to equiprobable microstates. This seems fine.

2.  **Formalize Boolean Circuits and Basic Complexity:**
    *   Create `PPNP.Complexity.BooleanGate.lean` (or similar name):
        *   Define an inductive type `BoolExpr` or `Circuit` with constructors for inputs, AND, OR, NOT.
        *   `def Circuit.eval (c : Circuit) (inputs : List Bool) : Bool`
        *   `def Circuit.num_gates (c : Circuit) : ℕ` (as in `NextSteps.md`).
        *   Prove simple lemmas about `eval` and `num_gates`.
    *   Create `PPNP.Complexity.ComplexityModel.lean`:
        *   Formalize "Q yes/no questions." This could be a list of boolean functions or a circuit evaluating to a final `Bool`.
        *   **Implication 1:** `"Q yes/no questions" ⟹ ∃ Circuit C with num_gates(C) ≈ Q`.
            *   This might involve showing how a sequence of decisions can be compiled into a circuit.
        *   Define a simple notion of "Program P implementing Circuit C".
        *   Define `Time(P)` based on `num_gates(C)`. This might be `Time(P) := num_gates(C)`.
        *   Formalize `O(Q)`: e.g., `IsBigO (f : ℕ → ℝ) (g : ℕ → ℝ) (l : Filter ℕ) := Filter.Eventually (fun n => |f n| ≤ C * |g n|) l` (Mathlib style) or simpler if only linear is needed.
        *   **Implication 2:** `"Circuit C of Q gates" ⟹ Time(P_C) = O(Q)`. This might be direct by definition of `Time(P_C)`.

3.  **Formalize SAT/CNF Representation (Focus on Existence):**
    *   Create `PPNP.Complexity.SAT.lean`:
        *   `Var : Type := ℕ` (or a generic type).
        *   `Literal : Type := Var × Bool` (variable and its polarity).
        *   `Clause : Type := List Literal` (or `Finset Literal`).
        *   `CNF : Type := List Clause` (or `Finset Clause`).
        *   `def Clause.is_satisfied_by (cl : Clause) (assignment : Var → Bool) : Bool`.
        *   `def CNF.is_satisfied_by (cnf : CNF) (assignment : Var → Bool) : Bool`.
        *   Function to encode Fermi-Dirac constraint: `def fd_constraint_to_cnf (particle_idx : ℕ) (state_idx : ℕ) (num_particles : ℕ) : CNF` (e.g., for "at most one particle in state"). This is where the focus on *existence of encoding* comes in, not necessarily solving SAT.

4.  **Refine `PPNP.Entropy.Physics.PhysicsDist.lean`:**
    *   Define a sum type or structure for `PhysicsSystemDist` that can represent MB, FD, BE systems (their N, M parameters, and distribution type).
    *   Possibly add a field for "number of yes/no questions to determine a microstate" or "circuit complexity to check a microstate". This is the bridge to complexity.

5.  **Update `Complexity.Basic.lean` (Conceptual):**
    *   The definitions from `PPNP.Complexity.*` would be used here to replace `sorry`s related to the claims in `NextSteps.md` about programs, gates, and Big-O.

**Relationship to "Unaxiomatizing":**
Phase 2 aims to unaxiomatize the *computational nature* of these systems by showing they can be represented by circuits and their complexity analyzed. It doesn't directly unaxiomatize `H_physical_system_is_HasRotaEntropyProperties` unless `H_physical_system` itself is defined in terms of these computational constructs (which would be a much larger step, possibly Phase 3/4).

This looks like a solid foundation for Phase 1 and a clear path for Phase 2. The project is ambitious and well-structured.