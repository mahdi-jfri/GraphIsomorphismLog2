module

public import Workspace.Algorithm.AuxBlocks
public import Workspace.Paper.CapsExplicit

@[expose] public section

/-!
# The parameters of an aggregation round, and its labels on the domain

`Params.Aggregates P` collects the conditions on the parameters that an aggregation round uses
(Section 7.5, "Choice of parameters"):

* `β ≥ 13/16`: item (iii), "`max{1/2, 1-δ, 1-ηδ, η} < β < 1`" with `δ = 1/4`, `η = 3/4`;
* `θ ≥ 1/2`: item (iii), "Choose `θ < 1` above `1/2` and `2η(1-η)`";
* `θ κ ≥ 1`: an affected test call has at most `s/κ ≤ θ s` positions (Lemma 4.1);
* `κ ≥ 5`: Lemma 4.1 ("a fixed constant `κ ≥ 5`");
* `q₀ ≥ 4κ + 2`: item (i), "The bounded ideal cutoff satisfies `q₀ ≥ 4κ+2`";
* `q₀ ≥ 2064`: item (i), "Enlarge it as needed for the coherent-configuration cap bounds". The
  number is the explicit threshold of Lemma A.12 for `β ≥ 3/4`, `2(4·4⁴ + 8)`
  (`GI.Paper.a12Threshold`, `GI.Paper.lem_exact_configuration_2064`);
* `a ≥ 3κ + 5`: Section 7.2, "Fix an absolute exponent `a ≥ 1` bounding the polynomial numbers
  of local and auxiliary calls". The round makes at most `N^{2κ+ℓ+4}` calls, with a source tuple
  of length `ℓ = κ + 1`;
* the support classification above the base size: item (i) and the base size paragraph, "Choose
  an absolute base size `N₀` large enough that, for every `N ≥ N₀`, `C(⌊N^α⌋, 3) > N` … and that
  the row threshold admits an odd integer `k > max{8, 2 + log₂ N}` with `2k-1 ≤ N^α`". These are
  the hypotheses of Corollary A.25 at the scale `q > λ` (Section 6.2, "Why the cases cover every
  large action"), so every phase size `N > N₀` has the support classification (`SupportCases`).

`GiantLabels.domMap` is the label map on the faithful image of the domain action, for labels
that are read on the domain (Section 3: "Every fresh call uses the faithful permutation image on
its own active domain"; the supplied alternating label set comes from a primitive quotient of
the domain action).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

/-- **The parameter conditions of an aggregation round** (Section 7.5, items (i) and (iii), and
the base size). -/
structure Params.Aggregates (P : Params) : Prop where
  β_cfg : 13 / 16 ≤ P.β
  θ_half : 1 / 2 ≤ P.θ
  θκ : 1 ≤ P.θ * P.κ
  κ_five : 5 ≤ P.κ
  κ_seven : 7 ≤ P.κ
  q₀_cert : 4 * P.κ + 2 ≤ P.q₀
  q₀_cfg : GI.Paper.a12Threshold ≤ P.q₀
  a_cert : 3 * (P.κ : ℝ) + 5 ≤ P.a
  cases : ∀ N : ℕ, P.N₀ < N → SupportCases P.α N

namespace GiantLabels

variable {Ω C : Type} {S : State Ω C} (L : GiantLabels S)

/-- The labels are read on the domain: an element of `G` that fixes every point of the domain
has trivial label image. -/
def OnDomain : Prop := ∀ g : S.G, S.domHom g = 1 → L.π g = 1

/-- **The label map on the faithful image of the domain action** `π_d : G|_dom → Alt(Γ)`. -/
noncomputable def domMap (h : L.OnDomain) : S.domGroup →* alternatingGroup (Fin L.q) :=
  S.domHom.rangeRestrict.liftOfRightInverse
    (Function.surjInv S.domHom.rangeRestrict_surjective)
    (Function.rightInverse_surjInv S.domHom.rangeRestrict_surjective)
    ⟨L.π, fun g hg => by
      rw [MonoidHom.mem_ker] at hg ⊢
      exact h g (by simpa using congrArg Subtype.val hg)⟩

/-- `π` factors through the domain action: `π_d(g|_dom) = π(g)`. -/
theorem domMap_spec (h : L.OnDomain) (g : S.G) :
    L.domMap h ⟨S.domHom g, g, rfl⟩ = L.π g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

end GiantLabels

end GI.Algorithm
