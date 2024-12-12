import Lake
open Lake DSL

package «iMLTT» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require aesop from git
  "https://github.com/leanprover-community/aesop"

@[default_target]
lean_lib «IMLTT» where
  -- add any library configuration options here
