import Lake
open Lake DSL

package «graphIsomorphismLog2» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Pinned to the revisions that AxiomMath/CFSG uses, so that `TauCeti.ClassificationStatement`
-- here is the statement CFSG proves, and so that CFSG's published build files apply.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "074063781836922cb02701cd12943c9f51731afa"
require TauCeti from git
  "https://github.com/TauCetiProject/TauCeti" @ "1f9b4414105d86e487a4ac4c3d3397076a44d0d2"

-- The proofs of the classification of finite simple groups and of Maróti's theorem on the orders
-- of primitive groups. `Workspace/Cited/Facts.lean` imports them.
require cfsg from git
  "https://github.com/AxiomMath/CFSG" @ "965a0775e82217494217503621b843e1b0e1e337"
require MarotiOrdersOfPrimitiveGroups from git
  "https://github.com/mahdi-jfri/MarotiOrdersOfPrimitiveGroups.git" @ "631aba5d4bdd9bbbbdc6659fd404f0263ab64c76"

/-- The formalization. -/
@[default_target]
lean_lib «Workspace» where
  globs := #[.andSubmodules `Workspace]

/-- The statements of the two theorems for Turing machines, with `sorry`, for comparator. -/
@[default_target]
lean_lib «Challenge»

/-- The two theorems for Turing machines, proved. -/
@[default_target]
lean_lib «Solution»
