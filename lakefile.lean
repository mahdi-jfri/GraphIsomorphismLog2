import Lake
open Lake DSL

package «graphIsomorphismLog2» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "2f9133abd9b05667d66a6f624311c5f5e6868ab7"

/-- The formalization. -/
@[default_target]
lean_lib «Workspace» where
  globs := #[.andSubmodules `Workspace]

/-- The statement of the main theorem, with `sorry`, for comparator. -/
lean_lib «Challenge»

/-- The main theorem, proved, for comparator. -/
@[default_target]
lean_lib «Solution»
