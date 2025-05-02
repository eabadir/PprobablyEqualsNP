import Lake
open Lake DSL

-- Replace this with your package name
package PPNP where
  -- (you can add `defaultLibrary := "PPNP"` here if desired)

-- This makes your library the default build target
@[default_target]
lean_lib PPNP

-- Pull in mathlib4 from GitHub
require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"master"
