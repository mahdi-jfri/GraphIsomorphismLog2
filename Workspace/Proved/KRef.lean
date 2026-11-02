import Workspace.Impl.KRefFinal
import Workspace.Lang.Bridge

/-!
# Joint `k`-ary coherent refinement in polynomial time

Source: Helfgott, Bajpai, Dona, arXiv:1710.04574v1, Sections 2.3–2.5 and Algorithm 3
(`k`-ary Weisfeiler–Leman). The program runs the rounds of Algorithm 3 on both colorings at once,
so that one palette serves both outputs: a round gives each tuple the rank, among the
signatures of all tuples of both inputs, of its signature (old color, equality pattern, colors
of `x ∘ τ` for all `τ`, and for each vector of colors the number of points `z` giving it). It
runs `2 n^k` rounds, the same number for every input; after that the joint coloring is stable.

* The mathematics is in `Workspace/Impl/KRefModel.lean`, `KRefRef.lean` and `KRefStable.lean`
  (`GI.Impl.kref_joint`).
* The program `GI.Impl.krefProg k` has no primitives (`Workspace/Impl/KRef*.lean`). On the input
  `[0^n, c, c']` it returns `[d, d']` with `JointRefinement c c' d d'` and colors below `2 n^k`,
  at cost at most `krefPolyK k * (wt + 1) ^ 36` (`GI.Impl.kref_main_spec`).
* The bridge `GI.Lang.polyTimeAt_ofVal_of_lang_cells` turns this into a machine program, with the
  cell bound `GI.Impl.kref_cells`.

The results used later are `GI.Proved.karyRefinement64` and `GI.Proved.karyRefinement2`.
-/

namespace GI.Proved

open GI.Lang GI.Impl

/-- **Joint `k`-ary coherent refinement in polynomial time, for every fixed `k`.** -/
theorem karyRefinement (k : ℕ) : GI.Cited.KaryRefinement k :=
  polyTimeAt_ofVal_of_lang_cells (krefProg k) 0 (krefPolyK k) 36 1 1 kref_cells kref_main_spec

/-- `KaryRefinement` at arity `64`. -/
theorem karyRefinement64 : GI.Cited.KaryRefinement64 := karyRefinement 64

/-- `KaryRefinement` at arity `2`. -/
theorem karyRefinement2 : GI.Cited.KaryRefinement2 := karyRefinement 2

end GI.Proved
