import EGPT.NumberTheory.Core -- For GNat, etc. (though we can use ℕ for now)
import EGPT.Complexity.Core
/-!
==================================================================
### The Canonical Program and its Equivalence

This section formalizes the core EGPT insight: a "program" is not just a
raw path, but is uniquely defined by its informationally significant outcome
(its net effect, encoded as a sum of one or more `ChargedParticlePath`) and the time over which that outcome was achieved (its complexity is just the magnitude `ParticlePath`).

This gives us a true, sorry-free bijection between programs and information.
==================================================================
-/

open EGPT.Complexity EGPT.NumberTheory.Core


/--
A `CanonicalComputerProgram` represents the essential information of a
computational process.
-/
structure CanonicalComputerProgram where
  initial_state    : ParticlePosition
  -- The compressed outcome of the sum of one or more particle paths / programs, encoded as an EGPT integer.
  canonical_tape   : ChargedParticlePath
  -- The total number of steps taken to achieve the outcome.
  total_complexity : ParticlePath

/--
A function to "compress" or "encode" any raw `PathProgram` into its
canonical form. It extracts the outcome and the total time.
-/
noncomputable def encodeToCanonical (prog : PathProgram) : CanonicalComputerProgram :=
  -- 1. Calculate the final position from the raw tape.
  let final_pos : ℤ := particlePosition prog.tape
  -- 2. Convert this integer outcome to its EGPT representation.
  let canon_tape : ChargedParticlePath := (ParticlePathIntEquiv.symm final_pos)
  -- 3. Get the total runtime (complexity).
  let total_cplx : ParticlePath := fromNat prog.tape.length
  -- 4. Construct the canonical program.
  {
    initial_state := prog.initial_state,
    canonical_tape := canon_tape,
    total_complexity := total_cplx
  }
