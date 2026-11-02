import Workspace.CleanComplementLogAssemble

/-! Renaming the block indices of a clean block action. The odd and even
constructions use the index types `Option (J × Bool)` and
`Option (Option (J × Bool))`; any index set of the same size is reached by
an equivalence. -/

namespace GI

open Equiv

namespace CleanBlockAction
variable {I I' V : Type*} [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
variable {G : Subgroup (Perm V)} (A : CleanBlockAction G I) (σ : I ≃ I')

/-- The same block system with the blocks renamed by `σ`. -/
def reindex : CleanBlockAction G I' where
  label x := σ (A.label x)
  label_surjective := σ.surjective.comp A.label_surjective
  top := σ.altCongrHom.toMonoidHom.comp A.top
  top_surjective := σ.altCongrHom.surjective.comp A.top_surjective
  action g x := by
    change σ (A.label (g.val x)) = σ ((A.top g).val (σ.symm (σ (A.label x))))
    rw [σ.symm_apply_apply, A.action]

theorem reindex_top_eq_one (g : G) : (A.reindex σ).top g = 1 ↔ A.top g = 1 := by
  change σ.altCongrHom (A.top g) = 1 ↔ _
  exact MulEquiv.map_eq_one_iff _

theorem reindex_ker : (A.reindex σ).top.ker = A.top.ker := by
  ext g
  exact A.reindex_top_eq_one σ g

theorem KernelTransitive.reindex (h : A.KernelTransitive) : (A.reindex σ).KernelTransitive := by
  intro x y hxy
  obtain ⟨g, hg, hgxy⟩ := h x y (σ.injective hxy)
  exact ⟨g, (A.reindex_top_eq_one σ g).mpr hg, hgxy⟩

theorem fiber_card_reindex [Fintype V] (i : I) :
    Fintype.card {x : V // (A.reindex σ).label x = σ i} =
      Fintype.card {x : V // A.label x = i} :=
  Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => σ.injective.eq_iff))

theorem BelowLogThreshold.reindex [Fintype V] {k : ℕ} (h : A.BelowLogThreshold k) :
    (A.reindex σ).BelowLogThreshold k := by
  intro i'
  have he := A.fiber_card_reindex σ (σ.symm i')
  rw [σ.apply_symm_apply] at he
  rw [he]
  exact h (σ.symm i')

end CleanBlockAction

namespace PureComplement
variable {I I' V : Type*} [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
variable {G : Subgroup (Perm V)} {A : CleanBlockAction G I} {σ : I ≃ I'}

/-- A clean complement for the renamed blocks is one for the original blocks. -/
def ofReindex (c : PureComplement (A.reindex σ)) : PureComplement A where
  Fiber := c.Fiber
  base := c.base
  coordinates := (Equiv.prodCongr (Equiv.refl _) σ).trans c.coordinates
  sectionHom := c.sectionHom.comp σ.altCongrHom.toMonoidHom
  label_coordinates b i := by
    have h := c.label_coordinates b (σ i)
    exact σ.injective h
  pure p b i := by
    change (c.sectionHom (σ.altCongrHom p)).val (c.coordinates (b, σ i)) =
      c.coordinates (b, σ (p.val i))
    rw [c.pure]
    congr 2
    change σ (p.val (σ.symm (σ i))) = σ (p.val i)
    rw [σ.symm_apply_apply]
  top_section p := by
    have h := c.top_section (σ.altCongrHom p)
    change σ.altCongrHom (A.top (c.sectionHom (σ.altCongrHom p))) = σ.altCongrHom p at h
    exact σ.altCongrHom.injective h
  isComplement := by
    have hr : (c.sectionHom.comp σ.altCongrHom.toMonoidHom).range = c.sectionHom.range := by
      rw [MonoidHom.range_comp, MulEquiv.toMonoidHom_eq_coe, MonoidHom.range_eq_top.mpr
        σ.altCongrHom.surjective, ← MonoidHom.range_eq_map]
    rw [hr, ← A.reindex_ker σ]
    exact c.isComplement

end PureComplement
end GI
