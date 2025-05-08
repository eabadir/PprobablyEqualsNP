import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic -- For logb
import Mathlib.Data.List.Basic -- Contains List.sum_replicate
import Mathlib.Data.List.Defs -- For List.replicate


namespace RotaEntropyTheoremProof

open Classical Real List

-- === Probability Distributions ===
/-- A predicate asserting that a list of real numbers represents a
    finite probability distribution (non-negative, sums to 1). -/
def IsProbDist (p : List Real) : Prop :=
  (∀ pi ∈ p, 0 ≤ pi) ∧ p.sum = 1

/-- The uniform probability distribution over `n` outcomes. -/
noncomputable def uniformDist (n : Nat) : List Real :=
  match n with
  | 0 => []
  | k+1 => replicate (k+1) (1 / (k+1 : Real))



lemma uniformDist_IsProbDist (n : Nat) (hn : 0 < n) : IsProbDist (uniformDist n) := by
  cases n with
  | zero => contradiction -- 0 < 0 is false
  | succ k => -- n = k+1
    simp only [uniformDist, IsProbDist, Nat.succ_eq_add_one]
    constructor
    · intro pi hpi; simp only [List.mem_replicate] at hpi; obtain ⟨_, h_eq⟩ := hpi; rw [h_eq]; positivity
    · rw [List.sum_replicate, nsmul_eq_mul]
      have h_denom_ne_zero : (k : Real) + 1 ≠ 0 := by positivity
      field_simp [h_denom_ne_zero]

-- === Entropy Function Type ===

/-- An abstract Entropy Function maps a probability distribution to a real value. -/
def EntropyFunction : Type := List Real → Real

-- === Shannon Entropy Definition ===

/-- Shannon Entropy H(p) = - Σ pᵢ log₂(pᵢ). Uses log base 2. -/
noncomputable def ShannonEntropyFunc : EntropyFunction :=
  fun p => - (p.map (fun pi => if pi > 0 then pi * (logb 2 pi) else 0)).sum

-- === Properties of Entropy Functions (Defined as Predicates) ===

/-- Property 0: Entropy of a certain event ([1]) is 0. -/
def EntropyProperty0 (H : EntropyFunction) : Prop := H [1] = 0

/-- Property 1: Domain is probability distributions. (Implicitly handled)
 Property 2: Ignoring zero-probability outcomes. -/
def EntropyProperty2 (H : EntropyFunction) : Prop :=
  ∀ (p : List Real), IsProbDist p → H (p.filter (· > 0)) = H p

/-- Property 3: Continuity. Stated abstractly.
    Replacing this requires a formal definition of continuity for List Real -> Real. -/
axiom IsContinuousEntropy (H : EntropyFunction) : Prop

/-- Property 4: Additivity / Conditional Entropy. (Handled via consequences in proof module)
Property 5: Maximum Entropy for Uniform Distribution. -/
def EntropyProperty5 (H : EntropyFunction) : Prop :=
  ∀ (p : List Real) (hp : IsProbDist p) (hlen : 0 < p.length),
    H p ≤ H (uniformDist p.length)

/-- Bundle the properties together for convenience.
    A proof of `HasEntropyProperties H` contains proofs that H satisfies
    each of the defined properties. -/
structure HasEntropyProperties (H : EntropyFunction) : Prop where
  prop0 : EntropyProperty0 H -- Now refers to the defined proposition
  prop2 : EntropyProperty2 H -- Now refers to the defined proposition
  prop3 : IsContinuousEntropy H -- Still uses the axiom (or would use a def if available)
  prop5 : EntropyProperty5 H -- Now refers to the defined proposition
  -- Property 4 is implicitly used via its consequences in the proof module

end RotaEntropyTheoremProof
