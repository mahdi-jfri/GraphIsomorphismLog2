module

public import Workspace.CleanComplementLinear
public import Workspace.RowSemidirect

@[expose] public section

/-! Identify the actual kernel in clean coordinates with a subgroup of row
permutations, and derive alternating invariance from the clean section. -/
namespace GI
variable {I B : Type*}

def rowCoordinatePerm : (I → Equiv.Perm B) →* Equiv.Perm (B × I) where
  toFun := Equiv.prodCongrLeft
  map_one' := by apply Equiv.ext; intro x; rfl
  map_mul' _ _ := by apply Equiv.ext; intro x; rfl

theorem rowCoordinatePerm_injective : Function.Injective (rowCoordinatePerm (I := I) (B := B)) := by
  intro x y hxy
  funext i
  apply Equiv.ext
  intro b
  exact congrArg Prod.fst (congrArg (fun p : Equiv.Perm (B × I) => p (b, i)) hxy)

theorem row_inverse_second (p : Equiv.Perm (B × I)) (hp : ∀ x, (p x).2 = x.2) (x : B × I) :
    (p.symm x).2 = x.2 := by
  have h := hp (p.symm x)
  rw [p.apply_symm_apply] at h
  exact h.symm

def rowComponents (p : Equiv.Perm (B × I)) (hp : ∀ x, (p x).2 = x.2) (i : I) : Equiv.Perm B where
  toFun b := (p (b, i)).1
  invFun b := (p.symm (b, i)).1
  left_inv b := by
    have he : p (b, i) = ((p (b, i)).1, i) := Prod.ext rfl (hp (b, i))
    have h := congrArg Prod.fst (p.symm_apply_apply (b, i))
    rwa [he] at h
  right_inv b := by
    have he : p.symm (b, i) = ((p.symm (b, i)).1, i) :=
      Prod.ext rfl (row_inverse_second p hp (b, i))
    have h := congrArg Prod.fst (p.apply_symm_apply (b, i))
    rwa [he] at h

theorem rowCoordinatePerm_components (p : Equiv.Perm (B × I)) (hp : ∀ x, (p x).2 = x.2) :
    rowCoordinatePerm (rowComponents p hp) = p := by
  apply Equiv.ext
  rintro ⟨b, i⟩
  exact Prod.ext rfl (hp (b, i)).symm

theorem rowCoordinatePerm_reindex (s : Equiv.Perm I) (x : I → Equiv.Perm B) :
    rowCoordinatePerm (rowPermute s x) = (cleanPureHom s)⁻¹ * rowCoordinatePerm x * cleanPureHom s := by
  apply Equiv.ext
  rintro ⟨b, i⟩
  change (x (s i) b, i) = (x (s i) b, s.symm (s i))
  rw [s.symm_apply_apply]

namespace PureComplement
variable {V : Type*} [Fintype I] [DecidableEq I]
variable {G : Subgroup (Equiv.Perm V)} {A : CleanBlockAction G I} (c : PureComplement A)

def rowMap : (I → Equiv.Perm c.Fiber) →* Equiv.Perm V :=
  (relabelPerm c.coordinates).toMonoidHom.comp rowCoordinatePerm

theorem rowMap_apply (x : I → Equiv.Perm c.Fiber) (b : c.Fiber) (i : I) :
    c.rowMap x (c.coordinates (b, i)) = c.coordinates (x i b, i) := by
  change c.coordinates (rowCoordinatePerm x (c.coordinates.symm (c.coordinates (b, i)))) = _
  rw [c.coordinates.symm_apply_apply]
  rfl

theorem rowMap_injective : Function.Injective c.rowMap :=
  (relabelPerm c.coordinates).injective.comp rowCoordinatePerm_injective

def rowKernel : Subgroup (I → Equiv.Perm c.Fiber) := G.comap c.rowMap

def rowIntoGroup : c.rowKernel →* G where
  toFun x := ⟨c.rowMap x.val, x.property⟩
  map_one' := by apply Subtype.ext; exact c.rowMap.map_one
  map_mul' x y := by apply Subtype.ext; exact c.rowMap.map_mul x.val y.val

theorem row_top_one (x : c.rowKernel) : A.top (c.rowIntoGroup x) = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  have h := A.action (c.rowIntoGroup x) (c.coordinates (c.base, i))
  change A.label (c.rowMap x.val (c.coordinates (c.base, i))) =
    (A.top (c.rowIntoGroup x)).val (A.label (c.coordinates (c.base, i))) at h
  rw [c.rowMap_apply, c.label_coordinates, c.label_coordinates] at h
  exact h.symm

def kernelEmbedding : c.rowKernel →* A.top.ker where
  toFun x := ⟨c.rowIntoGroup x, c.row_top_one x⟩
  map_one' := by apply Subtype.ext; exact c.rowIntoGroup.map_one
  map_mul' x y := by apply Subtype.ext; exact c.rowIntoGroup.map_mul x y

theorem kernelEmbedding_injective : Function.Injective c.kernelEmbedding := by
  intro x y hxy
  apply Subtype.ext
  apply c.rowMap_injective
  exact congrArg (fun z : A.top.ker => z.val.val) hxy

theorem kernel_rows_preserved (g : A.top.ker) (x : c.Fiber × I) :
    (relabelPerm c.coordinates.symm g.val.val x).2 = x.2 := by
  have h := A.action g.val (c.coordinates x)
  have hg : A.top g.val = 1 := g.property
  rw [hg] at h
  change A.label (g.val.val (c.coordinates x)) = A.label (c.coordinates x) at h
  rw [c.label_coordinates] at h
  have he : c.coordinates (relabelPerm c.coordinates.symm g.val.val x) =
      g.val.val (c.coordinates x) := c.coordinates.apply_symm_apply _
  rw [← he, c.label_coordinates] at h
  exact h

theorem kernelEmbedding_surjective : Function.Surjective c.kernelEmbedding := by
  intro g
  let p := relabelPerm c.coordinates.symm g.val.val
  let x := rowComponents p (c.kernel_rows_preserved g)
  have hx : c.rowMap x = g.val.val := by
    change relabelPerm c.coordinates (rowCoordinatePerm x) = g.val.val
    rw [rowCoordinatePerm_components p (c.kernel_rows_preserved g)]
    apply Equiv.ext
    intro v
    change c.coordinates (c.coordinates.symm
      (g.val.val (c.coordinates (c.coordinates.symm v)))) = g.val.val v
    rw [c.coordinates.apply_symm_apply, c.coordinates.apply_symm_apply]
  have hmem : x ∈ c.rowKernel := by
    change c.rowMap x ∈ G
    rw [hx]
    exact g.val.property
  refine ⟨⟨x, hmem⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hx

noncomputable def kernelEquiv : c.rowKernel ≃* A.top.ker :=
  MulEquiv.ofBijective c.kernelEmbedding ⟨c.kernelEmbedding_injective, c.kernelEmbedding_surjective⟩

theorem pureLift_eq_section (p : alternatingGroup I) :
    coordinatePureLift c.coordinates p.val = (c.sectionHom p).val := by
  apply Equiv.ext
  intro v
  obtain ⟨⟨b, i⟩, rfl⟩ := c.coordinates.surjective v
  rw [coordinatePureLift_apply]
  exact (c.pure p b i).symm

theorem rowMap_reindex (s : Equiv.Perm I) (x : I → Equiv.Perm c.Fiber) :
    c.rowMap (rowPermute s x) = (coordinatePureLift c.coordinates s)⁻¹ * c.rowMap x *
      coordinatePureLift c.coordinates s := by
  change relabelPerm c.coordinates (rowCoordinatePerm (rowPermute s x)) = _
  rw [rowCoordinatePerm_reindex, map_mul, map_mul, map_inv]
  rfl

/-- Alternating invariance follows from conjugating by the actual clean section. -/
theorem rowKernel_invariant : RowAltInvariant c.rowKernel := by
  intro s hs x hx
  change c.rowMap (rowPermute s x) ∈ G
  rw [c.rowMap_reindex]
  have ht : coordinatePureLift c.coordinates s ∈ G := by
    rw [c.pureLift_eq_section ⟨s, hs⟩]
    exact (c.sectionHom ⟨s, hs⟩).property
  exact G.mul_mem (G.mul_mem (G.inv_mem ht) hx) ht

end PureComplement
end GI
