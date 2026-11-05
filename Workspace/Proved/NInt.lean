module

public import Workspace.Impl.NIntInter
public import Workspace.Proved.SSPointwiseStab
public import Workspace.Proved.SSConstructiveMembership

@[expose] public section

/-!
# Normalized intersection and factorization

Source: Luks–Miyazaki, DMTCS 13:4 (2011), Theorem 3.1(viii)(b),(c); Luks 1993, Prop. 7.1.
Both use the group `K = {(g, g m) : g ∈ G, m ∈ N}` (`GI.Proved.nintPairs`,
`Workspace/Proved/NIntMath.lean`).

* **Intersection** (`GI.Impl.nint_normalizedIntersection`, `Workspace/Impl/NIntInter.lean`):
  `G ∩ N` is the restriction to the first copy of the pointwise stabilizer of the second copy in
  `K`, acting on `Fin (n + n)`. Two calls of the pointwise stabilizer.
* **Factorization** (`GI.Impl.nint_normalizedFactor`, `Workspace/Impl/NIntFac.lean`): a
  straight-line program for `x` over `gs ++ ns`, evaluated with the entries of `ns` replaced by
  `1`, gives `y ∈ G` with `y⁻¹ x ∈ N`. One call of constructive membership.

Both are reductions to Schreier–Sims tasks. This file applies them to the current Schreier–Sims
results, in one place per task: when those tasks are proved, only the two arguments below change.
-/

namespace GI.Proved

/-- **Intersection with a normalized subgroup in polynomial time** ([LM, Theorem 3.1(viii)(b)]). -/
theorem normalizedIntersection : GI.Cited.NormalizedIntersection :=
  GI.Impl.nint_normalizedIntersection GI.Proved.pointwiseStab

/-- **Factorization in a normalized product in polynomial time** ([LM, Theorem 3.1(viii)(c)]). -/
theorem normalizedFactor : GI.Cited.NormalizedFactor :=
  GI.Impl.nint_normalizedFactor GI.Proved.constructiveMembership

end GI.Proved
