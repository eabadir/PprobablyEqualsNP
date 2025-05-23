--import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog -- For negMulLog, Real.log
--import Mathlib.Algebra.BigOperators.Fin -- For sum over Fin n
--import Mathlib.Data.Fin.Basic -- Basic Fin definitions and lemmas
--import Mathlib.Data.Fintype.Fin -- Instances for Fin n
--import Mathlib.Algebra.GroupWithZero.Units.Basic -- Provides mul_inv_cancel₀
--import Mathlib.Data.Nat.Basic -- Basic Nat properties
import Mathlib.Data.Sym.Card

--import Mathlib.Data.Multiset.Bind
--import Mathlib.Data.Multiset.Basic
--import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PPNP.Common.Basic
import PPNP.Entropy.Common
import PPNP.Entropy.Physics.Common
import PPNP.Entropy.RET
import PPNP.Entropy.Physics.UniformSystems
import PPNP.Entropy.Physics.BoseEinstein

namespace PPNP.Entropy.Physics.PhysicsDist

open PPNP.Entropy.RET

open Multiset NNReal
open PPNP.Common
open PPNP.Entropy.Common
open PPNP.Entropy.Physics.Common
open PPNP.Entropy.Physics.UniformSystems
open PPNP.Entropy.Physics.BE

/-! # Formalizing "Physics Distribution" To Mean A Combinatorial State Spaces, Or, Counting Problem Under Constraints

## Three Disjoint Constraint Cases Describe All Physical Systems

> Let $N$ boxes (states) and $M$ balls (particles). A microstate is a way of allocating the $M$ balls among the $N$ boxes. For convenience, we will refer to distinguishability interchangeably with the notion of constraint—e.g., distinguishable = constrained (trackable), indistinguishable = unconstrained (untrackable).
>
> There are exactly three—and only three—canonical constraint families for how balls may occupy boxes in statistical mechanics:
>
> * **Maxwell-Boltzmann (MB)**: Balls are **distinguishable** (constrained), boxes are **distinguishable** (constrained). Any number of balls may occupy a box.
> * **Fermi-Dirac (FD)**: Balls are **indistinguishable** (unconstrained), boxes are **distinguishable** (constrained), **with at most one ball per box** (exclusive occupancy constraint).
> * **Bose-Einstein (BE)**: Balls are **indistinguishable** (unconstrained), boxes are **distinguishable** (constrained), **with any number of balls per box** (inclusive occupancy).
>
> Note: If both balls and boxes are **indistinguishable**, the configuration space corresponds to the set of **integer partitions** of $M$, not to any of the three classical statistics. This case is **not** described by a multinomial distribution since multisets require distinguishable labels on the boxes.

This file consumes the proofs from each of the three statistics files (BoseEinstein.lean, FermiDirac.lean, and MaxwellBoltzmann.lean) which each establish equivalence to:
* the combinatorial state space (`OmegaC`), which is the standard combinatorial object: multisets of a fixed size (`SymFin`).
* the uniform distribution over the combinatorial state space (`OmegaC`), which is the standard uniform distribution over multisets of a fixed size (`SymFin`).
* equivlance to Shannon entropy via Rota's Entropy Theorem.

Consequently, leveraging the proofs in UniformSystems.lean allowing the additivity of uniform distributions and the the conditional entropy additivity proofs in Entropy.Common.lean, we define PhysicsDist as any linear combination of the three canonical distributions (MB, FD, BE) and further that this generalized distribution is mathematically equivalent to a combinatorial state space (multisets) i.e. computation of the evolution a physics distribution is the computation of a counting problem under constraints.


-/


-- For clarity, let's alias these
-- noncomputable def H_axiom := PPNP.Entropy.Physics.Common.H_physical_system -- Removed this alias
def hH_axioms_proof := PPNP.Entropy.Physics.Common.H_physical_system_has_Rota_entropy_properties
noncomputable def C_axiom_val : ℝ := PPNP.Entropy.RET.C_constant_real hH_axioms_proof

-- Define an enum for the type of statistical system
inductive StatSystemType | BoseEinstein | FermiDirac | MaxwellBoltzmann

-- Define parameters for each system. For simplicity, (N, M) for all.
-- More complex systems might need richer parameter types.
structure SystemParams where
  N : ℕ
  M : ℕ
  -- Could add constraints like N_pos : N > 0, etc., if always needed
  -- Or pass h_domain_valid separately.

/--
Calculates the entropy of a given statistical system (BE, FD, MB)
using the axiomatic H_physical_system.
The result is a Real value.
This function will dispatch to the appropriate underlying probability distribution
and apply H_axiom.
-/
noncomputable def entropy_of_stat_system (type : StatSystemType) (params : SystemParams)
    (_h_domain_valid : params.N ≠ 0 ∨ params.M = 0) : ℝ :=
  match type with
  | StatSystemType.BoseEinstein =>
    -- p_UD_fin is the uniform distribution on Fin (Fintype.card (OmegaUD N M))
    -- Using PPNP.Entropy.Physics.Common.H_physical_system directly
    (PPNP.Entropy.Physics.Common.H_physical_system (PPNP.Entropy.Physics.UniformSystems.p_UD_fin params.N params.M) : ℝ)
  | StatSystemType.FermiDirac =>
    -- Placeholder: Assume similar structure for FD
    -- (PPNP.Entropy.Physics.Common.H_physical_system (PPNP.Entropy.Physics.FermiDirac.p_FD_fin params.N params.M) : ℝ)
    0 -- Placeholder value
  | StatSystemType.MaxwellBoltzmann =>
    -- Placeholder: Assume similar structure for MB
    -- (PPNP.Entropy.Physics.Common.H_physical_system (PPNP.Entropy.Physics.MaxwellBoltzmann.p_MB_fin params.N params.M) : ℝ)
    0 -- Placeholder value

/--
Calculates the standard Shannon entropy (ln-based) of a given statistical system's
canonical (uniform) probability distribution.
Result is Real.
-/
noncomputable def shannon_entropy_of_stat_system (type : StatSystemType) (params : SystemParams)
    (_h_domain_valid : params.N ≠ 0 ∨ params.M = 0) : ℝ :=
  match type with
  | StatSystemType.BoseEinstein =>
    stdShannonEntropyLn (PPNP.Entropy.Physics.UniformSystems.p_UD_fin params.N params.M)
  | StatSystemType.FermiDirac =>
    -- Placeholder: stdShannonEntropyLn (PPNP.Entropy.Physics.FermiDirac.p_FD_fin params.N params.M)
    0 -- Placeholder value
  | StatSystemType.MaxwellBoltzmann =>
    -- Placeholder: stdShannonEntropyLn (PPNP.Entropy.Physics.MaxwellBoltzmann.p_MB_fin params.N params.M)
    0 -- Placeholder value

/--
Theorem: The axiomatic entropy of a Bose-Einstein system is C_axiom * its Shannon entropy.
-/
theorem entropy_BE_eq_C_shannon (params : SystemParams)
    (h_domain_valid : params.N ≠ 0 ∨ params.M = 0) :
    entropy_of_stat_system StatSystemType.BoseEinstein params h_domain_valid =
    C_axiom_val * shannon_entropy_of_stat_system StatSystemType.BoseEinstein params h_domain_valid := by
  -- 1. Unfold definitions
  simp only [entropy_of_stat_system, shannon_entropy_of_stat_system]
  -- Goal is now:
  -- (PPNP.Entropy.Physics.Common.H_physical_system (p_UD_fin params.N params.M) : ℝ) =
  --  C_axiom_val * stdShannonEntropyLn (p_UD_fin params.N params.M)

  -- 2. This directly matches the statement of H_BE_from_Multiset_eq_C_shannon
  --    Need to ensure the C_axiom_val here is the same as the one used in that theorem.
  --    `H_BE_from_Multiset_eq_C_shannon` uses `C_constant_real PPNP.Entropy.Physics.Common.H_physical_system_has_Rota_entropy_properties`
  --    Our `C_axiom_val` is defined identically.
  --    `axiomatic_entropy_of_stat_system` now directly uses `PPNP.Entropy.Physics.Common.H_physical_system`.
  exact PPNP.Entropy.Physics.BE.H_BE_from_Multiset_eq_C_shannon params.N params.M h_domain_valid

-- Similar theorems for FD and MB would be:
-- theorem axiomatic_entropy_FD_eq_C_shannon ...
-- theorem axiomatic_entropy_MB_eq_C_shannon ...


-- Structure to hold weights for each system type.
-- These are NNReal because they often represent probabilities or positive contributions.
structure SystemWeights where
  w_BE : NNReal
  w_FD : NNReal
  w_MB : NNReal
  -- Optional: constraint that they sum to 1 if representing probabilities of system type
  -- h_sum_to_one : w_BE + w_FD + w_MB = 1 -- If it's a convex combination

/--
Defines the total entropy of a "Physics Distribution" as a weighted sum
of the axiomatic entropies of its constituent statistical components (BE, FD, MB).
`params_map` provides the (N, M) parameters for each type of system.
`valid_map` provides the domain validity proofs.
-/
noncomputable def H_physics_dist_linear_combination
    (weights : SystemWeights)
    (params_BE : SystemParams) (h_valid_BE : params_BE.N ≠ 0 ∨ params_BE.M = 0)
    (params_FD : SystemParams) (h_valid_FD : params_FD.N ≠ 0 ∨ params_FD.M = 0) -- Placeholder
    (params_MB : SystemParams) (h_valid_MB : params_MB.N ≠ 0 ∨ params_MB.M = 0) -- Placeholder
    : ℝ :=
  (weights.w_BE : ℝ) * entropy_of_stat_system StatSystemType.BoseEinstein params_BE h_valid_BE +
  (weights.w_FD : ℝ) * entropy_of_stat_system StatSystemType.FermiDirac params_FD h_valid_FD + -- Will use actual FD params
  (weights.w_MB : ℝ) * entropy_of_stat_system StatSystemType.MaxwellBoltzmann params_MB h_valid_MB -- Will use actual MB params

/--
The "Generalized PhysicsDistCShannon definition".
This is C_axiom multiplied by the weighted sum of the Shannon entropies
of the constituent statistical components.
-/
noncomputable def generalized_PhysicsDist_C_times_Shannon
    (weights : SystemWeights)
    (params_BE : SystemParams) (h_valid_BE : params_BE.N ≠ 0 ∨ params_BE.M = 0)
    (params_FD : SystemParams) (h_valid_FD : params_FD.N ≠ 0 ∨ params_FD.M = 0) -- Placeholder
    (params_MB : SystemParams) (h_valid_MB : params_MB.N ≠ 0 ∨ params_MB.M = 0) -- Placeholder
    : ℝ :=
  C_axiom_val * (
    (weights.w_BE : ℝ) * shannon_entropy_of_stat_system StatSystemType.BoseEinstein params_BE h_valid_BE +
    (weights.w_FD : ℝ) * shannon_entropy_of_stat_system StatSystemType.FermiDirac params_FD h_valid_FD +
    (weights.w_MB : ℝ) * shannon_entropy_of_stat_system StatSystemType.MaxwellBoltzmann params_MB h_valid_MB
  )

/--
Main Theorem for PhysicsDist:
The linearly combined axiomatic entropy is equal to the
generalized C * Shannon form.
-/
theorem H_physics_dist_linear_combination_eq_generalized_C_Shannon
    (weights : SystemWeights)
    (params_BE : SystemParams) (h_valid_BE : params_BE.N ≠ 0 ∨ params_BE.M = 0)
    (params_FD : SystemParams) (h_valid_FD : params_FD.N ≠ 0 ∨ params_FD.M = 0) -- Placeholder proofs/params
    (params_MB : SystemParams) (h_valid_MB : params_MB.N ≠ 0 ∨ params_MB.M = 0) -- Placeholder proofs/params
    : H_physics_dist_linear_combination weights params_BE h_valid_BE params_FD h_valid_FD params_MB h_valid_MB =
      generalized_PhysicsDist_C_times_Shannon weights params_BE h_valid_BE params_FD h_valid_FD params_MB h_valid_MB := by
  -- 1. Unfold definitions
  simp only [H_physics_dist_linear_combination, generalized_PhysicsDist_C_times_Shannon]

  -- 2. Rewrite each axiomatic_entropy_of_stat_system term using its _eq_C_shannon theorem
  rw [entropy_BE_eq_C_shannon params_BE h_valid_BE]
  -- When FD and MB are done, add their rewrites:
  -- rw [axiomatic_entropy_FD_eq_C_shannon params_FD h_valid_FD] -- Assuming this theorem exists
  -- rw [axiomatic_entropy_MB_eq_C_shannon params_MB h_valid_MB] -- Assuming this theorem exists

  -- For now, with FD/MB axiomatic entropies being 0 (placeholders in `entropy_of_stat_system`),
  -- and their Shannon entropies also 0 (placeholders in `shannon_entropy_of_stat_system`),
  -- the FD and MB terms will simplify to 0 = C_axiom_val * 0.
  -- Let's make this explicit for the current state:
  simp only [entropy_of_stat_system, shannon_entropy_of_stat_system]
  -- This will resolve the match statements for FD and MB to 0.
  -- The goal becomes:
  -- (↑weights.w_BE) * (C_axiom_val * shannon_entropy_of_stat_system StatSystemType.BoseEinstein params_BE h_valid_BE) +
  -- (↑weights.w_FD) * 0 +
  -- (↑weights.w_MB) * 0 =
  -- C_axiom_val * (
  --   (↑weights.w_BE) * shannon_entropy_of_stat_system StatSystemType.BoseEinstein params_BE h_valid_BE +
  --   (↑weights.w_FD) * 0 +
  --   (↑weights.w_MB) * 0
  -- )
  simp only [mul_zero, add_zero] -- Clean up the zero terms

  -- The goal is now:
  -- (↑weights.w_BE) * (C_axiom_val * shannon_entropy_of_stat_system StatSystemType.BoseEinstein params_BE h_valid_BE) =
  -- C_axiom_val * ((↑weights.w_BE) * shannon_entropy_of_stat_system StatSystemType.BoseEinstein params_BE h_valid_BE)

  -- This is true by associativity and commutativity of multiplication for Reals.
  ring

-- In PPNP.Entropy.Physics.PhysicsDist

structure PhysicsSystemConfig where
  weights   : SystemWeights -- w_BE, w_FD, w_MB
  params_BE : SystemParams  -- N, M for BE
  params_FD : SystemParams  -- N, M for FD (placeholder usage)
  params_MB : SystemParams  -- N, M for MB (placeholder usage)
  -- We might need validity proofs here, or pass them separately later

/--
Calculates the weighted sum of Shannon entropies for a given configuration.
Handles domain validity internally for each component.
Returns 0 if a component's domain is invalid and its weight is non-zero.
(Or adjust error handling as preferred - returning 0 is simple for the decision problem).
-/
noncomputable def generalized_shannon_entropy_for_config (config : PhysicsSystemConfig) : ℝ :=
  let h_valid_BE := config.params_BE.N ≠ 0 ∨ config.params_BE.M = 0
  let entropy_BE := if h : h_valid_BE then
                     shannon_entropy_of_stat_system StatSystemType.BoseEinstein config.params_BE h
                   else 0

  let h_valid_FD := config.params_FD.N ≠ 0 ∨ config.params_FD.M = 0 -- Placeholder check
  let entropy_FD := if h : h_valid_FD then
                     shannon_entropy_of_stat_system StatSystemType.FermiDirac config.params_FD h
                   else 0 -- Currently returns 0 anyway due to placeholder

  let h_valid_MB := config.params_MB.N ≠ 0 ∨ config.params_MB.M = 0 -- Placeholder check
  let entropy_MB := if h : h_valid_MB then
                     shannon_entropy_of_stat_system StatSystemType.MaxwellBoltzmann config.params_MB h
                   else 0 -- Currently returns 0 anyway due to placeholder

  (config.weights.w_BE : ℝ) * entropy_BE +
  (config.weights.w_FD : ℝ) * entropy_FD +
  (config.weights.w_MB : ℝ) * entropy_MB


/--
`PhysicalEntropy` is the concrete instance of an `EntropyFunction`
represented by `H_physical_system`, which is axiomatically stated
to satisfy Rota's properties.
-/
noncomputable def PhysicalEntropy : EntropyFunction :=
  { H_func := H_physical_system,
    props  := H_physical_system_has_Rota_entropy_properties }



lemma p_BE_fin_is_H_physical_system_uniform_input (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    -- The let bindings for k_card_, hk_card_pos_, and H_sys_internal_pos_proof are moved into the proof block.
    -- The lemma statement now directly uses their definitions.
    p_UD_fin N M = uniformDist (α := Fin (Fintype.card (OmegaUD N M))) (by {
      simp only [Fintype.card_fin]
      exact card_omega_BE_pos N M h_domain_valid -- This was the definition of hk_card_pos_
    }) := by
  let k_card_ := Fintype.card (OmegaUD N M)
  have hk_card_pos_ : k_card_ > 0 := card_omega_BE_pos N M h_domain_valid
  funext i
  simp [p_UD_fin, uniformProb, uniformDist, Fintype.card_fin, k_card_, if_pos hk_card_pos_]

lemma eval_H_physical_system_on_p_UD_fin (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    H_physical_system (p_UD_fin N M) =
      H_physical_system_uniform_only_calc
        (Fintype.card (OmegaUD N M))
        (Nat.one_le_of_lt (card_omega_BE_pos N M h_domain_valid)) := by
  let k_card_ := Fintype.card (OmegaUD N M)
  have hk_card_pos_ : k_card_ > 0 := card_omega_BE_pos N M h_domain_valid
  -- have _hk_card_ge1_ : k_card_ ≥ 1 := Nat.one_le_of_lt hk_card_pos_ -- For the target RHS

  -- Unfold H_physical_system and simplify Fintype.card (Fin n) to n generally.
  simp only [H_physical_system, Fintype.card_fin]

  -- First `if` condition in H_physical_system: k_alpha = 0 (which became k_card_ = 0 after Fintype.card_fin)
  -- We use hk_card_pos_ (0 < k_card_) to show k_card_ ≠ 0.
  rw [dif_neg (Nat.ne_of_gt hk_card_pos_)]

  -- Now in the 'else' branch of the first 'if'.
  -- The expression involves a second 'if' checking if p_UD_fin is the uniformDist.
  -- Use p_BE_fin_is_H_physical_system_uniform_input to resolve this.
  -- This lemma states: p_UD_fin N M = uniformDist (α := Fin k_card_) (proof of 0 < k_card_)
  -- The simp will substitute p_UD_fin N M and simplify the equality condition of the if.
  -- The proofs of 0 < k_card_ will be definitionally equal due to proof irrelevance.
  simp only [p_BE_fin_is_H_physical_system_uniform_input N M h_domain_valid]

  -- The expression should now be:
  -- H_physical_system_uniform_only_calc k_card_ (Nat.one_le_of_lt P_internal) = H_physical_system_uniform_only_calc k_card_ (Nat.one_le_of_lt hk_card_pos_)
  -- This holds by definitional equality because `P_internal` (which is `Nat.pos_of_ne_zero (Nat.ne_of_gt hk_card_pos_)`) is definitionally equal to `hk_card_pos_`.
  -- `simp only []` or `rfl` should close this. Using `simp only []` for robustness.
  rfl

lemma stdShannon_of_p_UD_fin_when_k_is_1 (N M : ℕ) (h_k_is_1 : Fintype.card (OmegaUD N M) = 1) :
    stdShannonEntropyLn (p_UD_fin N M) = 0 := by
  -- Let k_card_ be Fintype.card (OmegaUD N M). We know k_card_ = 1 by h_k_is_1.
  -- The type of p_UD_fin N M is Fin k_card_ → NNReal.
  -- We want to show that for any x in its domain, (p_UD_fin N M x) is 1.
  -- Since k_card_ = 1, the domain Fin k_card_ is Fin 1.
  -- There's only one element in Fin 1, let's call it ` एकमात्र_el : Fin k_card_` (the unique element).
  -- (More formally, ` एकमात्र_el := (0 : Fin 1).cast (by rw ←h_k_is_1)` or similar if needed)

  -- Unfold stdShannonEntropyLn
  unfold stdShannonEntropyLn
  -- Goal: ∑ (x : Fin (Fintype.card (OmegaUD N M))), negMulLog ((p_UD_fin N M x) : ℝ) = 0

  -- Since Fintype.card (OmegaUD N M) = 1, the sum is over a singleton set (Fin 1).
  -- Use Finset.sum_eq_single_of_mem or rewrite the sum over Fin 1 directly.
  -- Fintype.card (Fin 1) = 1. Finset.univ for Fin 1 is {(0 : Fin 1)}.
  conv_lhs =>
    arg 1 -- The sum itself
    simp [h_k_is_1] -- Replace Fintype.card (OmegaUD N M) with 1 in the type
    -- Now summation is over Finset.univ (α := Fin 1)

  -- Goal is now: negMulLog ((p_UD_fin N M (0 : Fin 1)) : ℝ) = 0
  -- (The (0 : Fin 1) is the default element picked by Finset.sum_singleton if not specified)
  -- We need to evaluate p_UD_fin N M (0 : Fin 1)
  -- p_UD_fin N M is (fun _ => uniformProb (Fintype.card (OmegaUD N M)))
  -- Substitute h_k_is_1 for Fintype.card (OmegaUD N M)
  simp [p_UD_fin, h_k_is_1, uniformProb, inv_one, NNReal.coe_one, Real.negMulLog_one]
  -- uniformProb 1 simplifies to 1.
  -- Then negMulLog ((1 : NNReal) : ℝ) is negMulLog 1.0 which is 0.

theorem H_physical_system_is_rota_uniform (N M : ℕ) (h_domain_valid : N ≠ 0 ∨ M = 0) :
    (H_physical_system (p_UD_fin N M) : ℝ) =
      (C_physical_NNReal : ℝ) * stdShannonEntropyLn (p_UD_fin N M) := by
  let k_card_ := Fintype.card (OmegaUD N M)
  have hk_card_ge1_ : k_card_ ≥ 1 := Nat.one_le_of_lt (card_omega_BE_pos N M h_domain_valid)

  rw [eval_H_physical_system_on_p_UD_fin N M h_domain_valid]
  rw [H_physical_system_uniform_only_calc]

  if hk_eq_1 : k_card_ = 1 then
    rw [dif_pos hk_eq_1]
    simp only [NNReal.coe_zero] -- LHS is (0 : ℝ)
    -- Use the new helper lemma for the RHS
    rw [stdShannon_of_p_UD_fin_when_k_is_1 N M hk_eq_1]
    simp only [mul_zero]
  else
    rw [dif_neg hk_eq_1]
    simp only [PPNP.Common.RealLogNatToNNReal, NNReal.coe_mul, (Real.log_nonneg (Nat.one_le_cast.mpr hk_card_ge1_))]
    have h_shannon_eq_log_k : stdShannonEntropyLn (p_UD_fin N M) = Real.log (k_card_ : ℝ) := by
      rw [p_BE_fin_is_H_physical_system_uniform_input N M h_domain_valid]
      rw [stdShannonEntropyLn_uniform_eq_log_card]
      simp only [Fintype.card_fin]
      rfl
    rw [h_shannon_eq_log_k]
    rfl
