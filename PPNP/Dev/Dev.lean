import Mathlib.Data.Sym.Card
import Std.Sat.CNF.Basic
import Mathlib.Tactic.Sat.FromLRAT
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog -- For negMulLog, Real.log
import Mathlib.Algebra.GroupWithZero.Units.Basic
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

open Nat Real NNReal Multiset NNReal Fin Set Finset Filter Function BigOperators Topology
    -- Added Function for comp_apply

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
