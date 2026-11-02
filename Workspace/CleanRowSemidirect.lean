import Workspace.CleanRowSubdirect

/-! The supplied original group is the actual row semidirect product. This
connects the concrete clean complement to the A.18 row-normal-form modules. -/
namespace GI.PureComplement
variable {I V : Type*} [Fintype I] [DecidableEq I]
variable {G : Subgroup (Equiv.Perm V)} {A : CleanBlockAction G I} (c : PureComplement A)

theorem row_conjugation (s : alternatingGroup I) (x : c.rowKernel) :
    c.rowIntoGroup (rowAltAction c.rowKernel c.rowKernel_invariant s x) =
      c.sectionHom s * c.rowIntoGroup x * (c.sectionHom s)⁻¹ := by
  apply Subtype.ext
  change c.rowMap (rowPermute s.val⁻¹ x.val) =
    (c.sectionHom s).val * c.rowMap x.val * (c.sectionHom s).val⁻¹
  rw [c.rowMap_reindex, map_inv, inv_inv, c.pureLift_eq_section s]

def semidirectHom : c.rowKernel ⋊[rowAltAction c.rowKernel c.rowKernel_invariant]
    alternatingGroup I →* G :=
  SemidirectProduct.lift c.rowIntoGroup c.sectionHom (fun s => by
    apply MonoidHom.ext
    intro x
    exact c.row_conjugation s x)

theorem semidirectHom_top (x : c.rowKernel ⋊[rowAltAction c.rowKernel c.rowKernel_invariant]
    alternatingGroup I) : A.top (c.semidirectHom x) = x.right := by
  change A.top (c.rowIntoGroup x.left * c.sectionHom x.right) = _
  rw [map_mul, c.row_top_one, c.top_section, one_mul]

theorem semidirectHom_injective : Function.Injective c.semidirectHom := by
  intro x y hxy
  have hs : x.right = y.right := by
    have h := congrArg A.top hxy
    simpa only [c.semidirectHom_top] using h
  have hprod : c.rowIntoGroup x.left * c.sectionHom x.right =
      c.rowIntoGroup y.left * c.sectionHom y.right := hxy
  rw [hs] at hprod
  have hn := mul_right_cancel hprod
  have hl : x.left = y.left := by
    apply Subtype.ext
    apply c.rowMap_injective
    exact congrArg Subtype.val hn
  exact SemidirectProduct.ext hl hs

theorem semidirectHom_surjective : Function.Surjective c.semidirectHom := by
  intro g
  obtain ⟨⟨k, r⟩, he, _⟩ := c.isComplement.existsUnique g
  obtain ⟨s, hs⟩ := r.property
  let x := c.kernelEquiv.symm k
  refine ⟨⟨x, s⟩, ?_⟩
  have hk : c.rowIntoGroup x = k.val := congrArg Subtype.val (c.kernelEquiv.apply_symm_apply k)
  change c.rowIntoGroup x * c.sectionHom s = g
  rw [hk, hs]
  exact he

noncomputable def semidirectEquiv :
    c.rowKernel ⋊[rowAltAction c.rowKernel c.rowKernel_invariant] alternatingGroup I ≃* G :=
  MulEquiv.ofBijective c.semidirectHom ⟨c.semidirectHom_injective, c.semidirectHom_surjective⟩

variable (hcard : 4 ≤ Fintype.card I) (i : I)

theorem commonRowAction_compatible (s : alternatingGroup I) :
    (rowAltAction c.rowKernel c.rowKernel_invariant s).trans
        (commonRowEquiv c.rowKernel c.rowKernel_invariant hcard i) =
      (commonRowEquiv c.rowKernel c.rowKernel_invariant hcard i).trans
        (rowAltAction (c.commonRows hcard i) (c.commonRows_invariant hcard i) s) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  funext j
  apply Subtype.ext
  rfl

/-- The precise row model used by A.18 is isomorphic to the original G,
with H extracted as its actual common local image and K proved subdirect. -/
noncomputable def commonSemidirectEquiv :
    (c.commonRows hcard i) ⋊[rowAltAction (c.commonRows hcard i) (c.commonRows_invariant hcard i)]
      alternatingGroup I ≃* G :=
  (SemidirectProduct.congr (commonRowEquiv c.rowKernel c.rowKernel_invariant hcard i)
    (MulEquiv.refl (alternatingGroup I)) (c.commonRowAction_compatible hcard i)).symm.trans c.semidirectEquiv

end GI.PureComplement
