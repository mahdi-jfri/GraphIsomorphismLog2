import Lake
open Lake DSL

package «graphIsomorphismLog2» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Pinned to the revisions that AxiomMath/CFSG uses, so that `TauCeti.ClassificationStatement`
-- here is the statement CFSG proves, and so that CFSG's published build files apply.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "b63f6e8a68d220e3b3bc4f3792bb53650d375f24"
require TauCeti from git
  "https://github.com/TauCetiProject/TauCeti" @ "6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380"

-- The proofs of the classification of finite simple groups and of Maróti's theorem on the orders
-- of primitive groups. `Workspace/Cited/Facts.lean` imports them.
require cfsg from git
  "https://github.com/AxiomMath/CFSG" @ "69cb972f587a3ecc035e092253167ff2e303c962"
require MarotiOrdersOfPrimitiveGroups from git
  "https://github.com/mahdi-jfri/MarotiOrdersOfPrimitiveGroups.git" @ "826d2d7a58fb538ca10ccdb649a4a333b5aedadd"

/-- The formalization. -/
@[default_target]
lean_lib «Workspace» where
  globs := #[.andSubmodules `Workspace]

/-- The statement of the main theorem, with `sorry`, for comparator. -/
@[default_target]
lean_lib «Challenge»

/-- The main theorem, proved. -/
@[default_target]
lean_lib «Solution»
