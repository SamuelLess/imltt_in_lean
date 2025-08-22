import Lake
open Lake DSL

package «iMLTT» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @"v4.23.0-rc2"

require aesop from git
  "https://github.com/leanprover-community/aesop" @"v4.23.0-rc2"

@[default_target]
lean_lib «IMLTT» where
  -- add any library configuration options here
