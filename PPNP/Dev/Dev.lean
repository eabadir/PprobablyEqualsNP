import Mathlib.Data.Sym.Card
import Std.Sat.CNF.Basic
import Mathlib.Tactic.Sat.FromLRAT
--import Std.Data.List.Lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic -- For Fintype (Fin n) if needed, though usually direct
import Mathlib.Logic.Equiv.Defs -- For Equiv

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic -- For Real.log, Real.log_pow, Real.log_ne_zero_of_pos_of_ne_one
--import Mathlib.Data.Nat.Order.Basic -- For Nat.pos_of_ne_zero, Nat.lt_irrefl
--import Mathlib.Algebra.Ring.NatCast -- For Nat.cast_pow (implicitly used by (↑(2^m_bits) : ℝ))
--                                      and Nat.cast_zero, Nat.cast_id
import Mathlib.Data.List.Basic -- For List.replicate, List.length_replicate (from Std, re-exported)

import PPNP.Common.Basic
import PPNP.Entropy.Common
import PPNP.Entropy.Physics.Common
import PPNP.Entropy.RET -- Uncommented
import PPNP.Entropy.Physics.UniformSystems -- Uncommented
-- import PPNP.Complexity.Program -- Assuming not needed for f0_mul_eq_add_f0
--import PPNP.Entropy.Physics.PhysicsDist
--import PPNP.Entropy.Physics.BoseEinstein
--import PPNP.Entropy.Physics.PhotonicCA

open Nat Real NNReal Multiset NNReal Fin Set Finset Filter Function BigOperators Topology     -- Added Function for comp_apply

open Multiset NNReal
open PPNP.Common
--open PPNP.Complexity.Program
open PPNP.Entropy.Common
open PPNP.Entropy.Physics.Common
open PPNP.Entropy.Physics.UniformSystems -- Opened
--open PPNP.Entropy.Physics.PhysicsDist
--open PPNP.Entropy.Physics.BE
--open PPNP.Entropy.Physics.PCA
open PPNP.Entropy.RET -- Opened

-- In PPNP.Entropy.RET.lean

open PPNP.Entropy.Common

/--
Helper lemma demonstrating that if M is asserted to be non-zero (via `NeZero M`),
then an assumption `M = 0` leads to a contradiction.
This is analogous to the internal helper in `cond_add_for_independent_distributions`.
The conclusion `H_func q_const = 0` is reached via `exfalso`.
-/
lemma H_func_of_cond_dist_on_empty_domain_from_false_assumption
    {H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    {N M : ℕ} [hM_is_nonzero : NeZero M] (q_const : Fin M → NNReal)
    (_i_idx : Fin N) (h_M_eq_0 : (fun (_ : Fin N) => M) _i_idx = 0) :
    H_func ((fun (_ : Fin N) => q_const) _i_idx) = 0 := by
  simp only at h_M_eq_0 -- Simplifies `(fun (_ : Fin N) => M) i_idx = 0` to `M = 0`
  have h_M_ne_zero : M ≠ 0 := NeZero.ne M -- From the [NeZero M] instance
  exfalso -- From M = 0 and M ≠ 0, we can prove anything.
  exact h_M_ne_zero h_M_eq_0

/--
Core definition for the conditional distribution based on a natural number `val`.
If `val = 0`, it's the distribution on `Fin 0`.
If `val = k + 1`, it's uniform on `Fin (k + 1)`.
-/
noncomputable def P_cond_sigma_def_core (val : ℕ) : Fin val → NNReal :=
  match h : val with
  | 0      => h ▸ (Fin.elim0 : Fin 0 → NNReal)
  | k + 1  => uniformDist (Fintype_card_fin_pos (Nat.succ_pos k))

/--
Defines the conditional distribution for the i-th component in Rota's rational setup.
It uses `P_cond_sigma_def_core` with `a_map i`.
-/
noncomputable def P_cond_sigma_def {n : ℕ} (a_map : Fin n → ℕ) (i : Fin n) :
    Fin (a_map i) → NNReal :=
  P_cond_sigma_def_core (a_map i)




/--
`H_func` evaluated on `P_cond_sigma_def` is `f0 hH` at the same
cardinality.
-/
lemma H_func_P_cond_sigma_def_eq_f0
    {n : ℕ}
    (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal)
    (hH : HasRotaEntropyProperties H_func)
    (a_map : Fin n → ℕ) (i : Fin n)
    {h0 : IsEntropyZeroOnEmptyDomain H_func} :
  H_func (P_cond_sigma_def a_map i) = f0 hH (a_map i) := by
  dsimp [P_cond_sigma_def] -- Exposes P_cond_sigma_def_core (a_map i)
  cases h_ai : a_map i with
  | zero =>
      -- h_ai : a_map i = 0
      -- Goal: H_func (P_cond_sigma_def_core 0) = f0 hH 0
      rw [P_cond_sigma_def_core] -- Unfold with val = 0
      -- LHS becomes H_func ((rfl : 0=0) ▸ Fin.elim0) which simplifies to H_func Fin.elim0
      --simp only [eq_rec_rfl, eq_symm_rfl] -- Handles `rfl ▸ E`
      -- Goal: H_func Fin.elim0 = f0 hH 0
      rw [f0, dif_neg (Nat.not_lt_zero 0)] -- RHS becomes 0
      rw [h0.apply_to_empty_domain] -- LHS becomes 0
      -- Goal: 0 = 0
  | succ k =>
      -- h_ai : a_map i = k.succ
      -- Goal: H_func (P_cond_sigma_def_core (k.succ)) = f0 hH (k.succ)
      rw [P_cond_sigma_def_core] -- Unfold with val = k.succ
      -- LHS becomes H_func (uniformDist (Fintype_card_fin_pos (Nat.succ_pos k)))
      have hk_pos : (k.succ) > 0 := Nat.succ_pos k
      rw [f0, dif_pos hk_pos] -- RHS becomes f hH hk_pos
      rw [f] -- RHS becomes H_func (uniformDist (Fintype_card_fin_pos hk_pos))
      -- Goal: H_func (uniformDist ...) = H_func (uniformDist ...)

lemma sum_P_cond_sigma_def_eq_one_of_pos {n : ℕ} (a_map : Fin n → ℕ) (i : Fin n) (ha_i_pos : a_map i > 0) :
    ∑ j, (P_cond_sigma_def a_map i) j = 1 := by
  simp_rw [P_cond_sigma_def, P_cond_sigma_def_core]
  -- Since ha_i_pos, a_map i cannot be 0. So it must be k.succ for some k.
  cases h_ai_cases : a_map i with -- Use cases on a_map i
  | zero => exact (Nat.not_succ_le_zero 0 (h_ai_cases ▸ ha_i_pos)).elim -- Contradiction from ha_i_pos
  | succ k => -- a_map i = k.succ
    -- The match in P_cond_sigma_def_core will take the succ k branch.
    simp only [h_ai_cases] -- Substitute a_map i = k.succ into the goal if needed by simp context
    -- LHS is now ∑ j : Fin (k.succ), uniformDist (Fintype_card_fin_pos (Nat.succ_pos k)) j
    exact sum_uniformDist (Fintype_card_fin_pos (Nat.succ_pos k))


-- -- FOR REFERENCE IN DEALING WITH ZERO In PPNP.Entropy.Common.lean, add this structure:
-- structure IsEntropyZeroOnEmptyDomain
--   (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) : Prop where
--   apply_to_empty_domain : H_func Fin.elim0 = 0
--   -- Fin.elim0 here denotes the unique function Fin 0 → NNReal.
--   -- The specific instance H_func {α := Fin 0} [Fintype (Fin 0)] Fin.elim0 is used.

/-- **(A)** Value of the conditional density at index `j`. -/
@[simp] lemma P_cond_sigma_def_core_eval {val : ℕ} :
    (P_cond_sigma_def_core val) =
      (match val with
       | 0      => Fin.elim0
       | m + 1  => λ _j => ((m+1 : NNReal)⁻¹)) := by
  cases val with
  | zero    => simp [P_cond_sigma_def_core]
  | succ m  => -- val is m + 1
      -- The goal is P_cond_sigma_def_core (m+1) = (λ _j => ((m+1 : NNReal)⁻¹))
      -- Unfolding P_cond_sigma_def_core (m+1) gives uniformDist (Fintype_card_fin_pos (Nat.succ_pos m))
      -- So, goal becomes: uniformDist (Fintype_card_fin_pos (Nat.succ_pos m)) = (λ _j => ((m+1 : NNReal)⁻¹))
      funext j -- Apply function extensionality: prove for an arbitrary argument j
      -- New goal: P_cond_sigma_def_core (m+1) j = ((m+1 : NNReal)⁻¹)
      -- (or (uniformDist ...) j = ((m+1 : NNReal)⁻¹) if P_cond_sigma_def_core was already unfolded by `cases`)
      -- Now simp should work:
      -- LHS: P_cond_sigma_def_core (m+1) j
      --   -> (uniformDist (Fintype_card_fin_pos (Nat.succ_pos m))) j  (by P_cond_sigma_def_core)
      --   -> (↑(Fintype.card (Fin (m+1))))⁻¹                         (by uniformDist)
      --   -> (↑(m+1))⁻¹                                              (by Fintype.card_fin)
      -- RHS: ((m+1 : NNReal)⁻¹)
      simp [P_cond_sigma_def_core, uniformDist, Fintype.card_fin]

/-- **(B)** Value of the uniform distribution on the σ-type. -/
@[simp] lemma uniform_sigma_eval
    {n : ℕ} {a : Fin n → ℕ} {N : ℕ}
    (h_sum : ∑ k, a k = N) (hN : 0 < N)
    (i : Fin n) (j : Fin (a i)) :
    (uniformDist
       (α := Σ k, Fin (a k))
       (by simpa [Fintype.card_sigma, Fintype.card_fin, h_sum] using hN)) ⟨i, j⟩
      = (N : NNReal)⁻¹ := by
  simp [uniformDist, h_sum]

/-- **(C)** Cancelling the `m` in front. -/
@[simp] lemma rational_factor_cancel {m N : ℕ} (hm : 0 < m) (hN : 0 < N) :
    ((m : NNReal) / N) * (m : NNReal)⁻¹ = (N : NNReal)⁻¹ := by
  have m_ne_zero : (m : NNReal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have N_ne_zero : (N : NNReal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  -- Use field_simp with the non-zero hypotheses.
  -- This should simplify expressions involving division and inverses.
  field_simp [m_ne_zero, N_ne_zero]
  -- If field_simp leaves a goal that is true by associativity and/or commutativity
  -- (e.g., X * Y = Y * X), ac_rfl can solve it.
  -- NNReal multiplication is associative and commutative.
  ac_rfl
-- In PPNP.Entropy.RET.lean (or Dev.lean)


/-! ### New point-wise helper ------------------------------------------ -/

/-- Point-wise value of P_cond_sigma_def_core when the size is `k.succ`. -/
@[simp] lemma P_cond_sigma_def_core_apply_succ
    {k : ℕ} {j : Fin (k.succ)} :
    P_cond_sigma_def_core (k.succ) j = ((k.succ : NNReal)⁻¹) := by
  simp [P_cond_sigma_def_core, uniformDist, Fintype.card_fin]

-- The new micro-lemma:
lemma LHS_eval_when_ai_is_succ (N_den k : ℕ) (j_val : Fin (k.succ)) (h_N_den_pos_lemma : N_den > 0) :
    (↑(k.succ) / ↑N_den : NNReal) * P_cond_sigma_def_core (k.succ) j_val = (N_den : NNReal)⁻¹ := by
  rw [P_cond_sigma_def_core_apply_succ (k := k) (j := j_val)]
  have hk_succ_pos_lemma : 0 < k.succ := Nat.succ_pos k
  exact rational_factor_cancel hk_succ_pos_lemma h_N_den_pos_lemma

/--
Rota’s marginal distribution `P_rat` together with the conditional
distributions `P_cond_sigma_def` yields the uniform distribution on
`Σ i : Fin n, Fin (a i)`.
-/
lemma P_joint_sigma_is_uniform_for_rota
    {n : ℕ}
    (a : Fin n → ℕ) (N_den : ℕ)
    (h_sum_a_eq_N : ∑ k, a k = N_den) (hN_den_pos : N_den > 0)
    (P_rat : Fin n → NNReal)
    (hP_rat_def :
      P_rat = create_rational_dist n a N_den h_sum_a_eq_N hN_den_pos) :
  DependentPairDistSigma P_rat a (P_cond_sigma_def a) =
    uniformDist
      (α := Σ i : Fin n, Fin (a i))
      (by
        simpa [Fintype.card_sigma, Fintype.card_fin, h_sum_a_eq_N]
          using hN_den_pos) := by
  -- 1.  Point-wise equality
  funext x
  rcases x with ⟨i, j⟩

  -- 2.  Expand definitions of the LHS's main components
  dsimp [DependentPairDistSigma, P_cond_sigma_def]
  simp_rw [hP_rat_def, create_rational_dist]
  -- LHS: ↑(a i) / ↑N_den * P_cond_sigma_def_core (a i) j

  -- 3.  Simplify the RHS to (N_den)⁻¹ using the helper
  conv_rhs =>
    rw [uniform_sigma_eval h_sum_a_eq_N hN_den_pos i j]
  -- Goal: ↑(a i) / ↑N_den * P_cond_sigma_def_core (a i) j = (N_den)⁻¹

  -- 4.  Since `j : Fin (a i)` exists, `a i` must be positive.
  --     So, `a i = k.succ` for some `k`.
  have hai_pos : 0 < a i := Fin.pos j
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hai_pos) with ⟨k, hk_eq_succ_ai⟩
  -- hk_eq_succ_ai : a i = k.succ

  -- 5.  Show that the LHS of the current goal is equal to the LHS of the micro-lemma,
  --     then use the micro-lemma.
  --     We use `hk_eq_succ_ai` to rewrite `a i` instances.
  --     The term `j : Fin (a i)` needs to be related to `j_val : Fin (k.succ)`.
  --     `Eq.subst` allows substituting along an equality and handles dependent types.
  --     Alternatively, `Fin.cast` can be used.

  -- Rewrite the LHS of the goal using hk_eq_succ_ai.
  -- `Eq.subst hk_eq_succ_ai (λ val => ...)` allows us to substitute `a i` with `k.succ`
  -- inside the expression, and `j` will be correctly typed for the new `val`.
  revert j -- Temporarily remove j from the context to make the substitution cleaner
  rw [hk_eq_succ_ai] -- Now `a i` is `k.succ` in the type of what `j` would be
  intro j -- Reintroduce j, now its type is Fin (k.succ)

  -- Now the goal is: ↑(k.succ) / ↑N_den * P_cond_sigma_def_core (k.succ) j = (N_den)⁻¹
  -- This matches the micro-lemma directly.
  exact LHS_eval_when_ai_is_succ N_den k j hN_den_pos
