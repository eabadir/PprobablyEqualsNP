import Mathlib.Logic.Equiv.Defs -- For Equiv
import Mathlib.Logic.Equiv.Basic   -- Equiv API
import Mathlib.Logic.Equiv.Nat     -- intEquivNat, natSumNatEquivNat, …
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Cardinality
import Mathlib.Control.Random
import Mathlib.Data.Fintype.Vector
import EGPT.Basic


open List


namespace EGPT




class IIDParticleSource (α : Type) where
  stream : ℕ → α

/-- The canonical representation of a particle path sampled from an IIDParticleSource is symmetric and sorted with 1s first. For example `[true, true, false, false]` is the canonical representation of the path `[true, false, true, false]`. This means that the order of choices does not matter, only the counts of `true` and `false` do. -/
def CannonicalSymmetricParticlePath := List Bool

/-- A non-canonical particle path is just the list of movements describing a random walk -/
abbrev RandomWalkPath := List Bool


instance mkPseudoRandomSource (seed : Nat) : IIDParticleSource Bool :=
{ stream := fun n =>
    let gen0 := mkStdGen seed
    let genN := (List.range n).foldl (fun g _ => (stdNext g).2) gen0
    (randBool genN).1 }

/-- A biased IID particle source that generates `true` with probability `p / (p + q)` and `false` with probability `q / (p + q)`. -/
instance mkBiasedIIDParticleSource (seed : Nat) (p : ℕ) (q: ℕ) (_h : p + q > 0) : IIDParticleSource Bool :=
{ stream := fun n =>
    let gen0 := mkStdGen seed
    let genN := (List.range n).foldl (fun g _ => (stdNext g).2) gen0
    (randBool genN).1 }


/-- Calculates the number of `true` choices (e.g., "up-steps") in a path. -/
def numOnes (p_path : RandomWalkPath) : ℕ :=
  p_path.count true

/--
Calculates the "position" of a particle after `t` steps,
defined as (#trues - #falses).
-/
def particlePosition (p_path : RandomWalkPath) : ℤ :=
  let ones := numOnes p_path
  let path_len := p_path.length
  let zeros := path_len - ones
  (ones : ℤ) - (zeros : ℤ)
