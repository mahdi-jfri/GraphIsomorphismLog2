import Workspace.RectangleQueries

namespace GI.ProductAction

variable {L R : Type*}

def hom : (Equiv.Perm L × Equiv.Perm R) →* Equiv.Perm (L × R) where
  toFun p :=
    { toFun x := (p.1 x.1, p.2 x.2)
      invFun x := (p.1⁻¹ x.1, p.2⁻¹ x.2)
      left_inv x := by simp
      right_inv x := by simp }
  map_one' := rfl
  map_mul' _ _ := rfl

theorem injective [Nonempty L] [Nonempty R] :
    Function.Injective (hom (L := L) (R := R)) := by
  obtain ⟨l⟩ := ‹Nonempty L›
  obtain ⟨r⟩ := ‹Nonempty R›
  intro p q hpq
  apply Prod.ext
  · apply Equiv.ext
    intro x
    exact congrArg (fun g : Equiv.Perm (L × R) => (g (x, r)).1) hpq
  · apply Equiv.ext
    intro y
    exact congrArg (fun g : Equiv.Perm (L × R) => (g (l, y)).2) hpq

noncomputable def imageEquiv [Nonempty L] [Nonempty R] :
    (Equiv.Perm L × Equiv.Perm R) ≃* (hom (L := L) (R := R)).range :=
  MonoidHom.ofInjective injective

end GI.ProductAction

namespace GI.Rectangle

variable {α : Type*} [Fintype α] [DecidableEq α] {W R : Finset α}

def sideAction : permitted W R →* (Equiv.Perm W × Equiv.Perm R) where
  toFun g :=
    ({ toFun := fun x => ⟨g.val.val x, (left_mem_iff W R g x).mpr x.property⟩
       invFun := fun x => ⟨g.val.val⁻¹ x, (left_mem_iff W R g⁻¹ x).mpr x.property⟩
       left_inv x := by apply Subtype.ext; exact g.val.val.symm_apply_apply x
       right_inv x := by apply Subtype.ext; exact g.val.val.apply_symm_apply x },
     { toFun := fun x => ⟨g.val.val x, (right_mem_iff W R g x).mpr x.property⟩
       invFun := fun x => ⟨g.val.val⁻¹ x, (right_mem_iff W R g⁻¹ x).mpr x.property⟩
       left_inv x := by apply Subtype.ext; exact g.val.val.symm_apply_apply x
       right_inv x := by apply Subtype.ext; exact g.val.val.apply_symm_apply x })
  map_one' := by apply Prod.ext <;> ext x <;> rfl
  map_mul' _ _ := by apply Prod.ext <;> ext x <;> rfl

theorem product_side (g : permitted W R) : ProductAction.hom (sideAction g) = rectangleAction g := by
  ext x <;> rfl

def productImage : (rectangleAction (W := W) (R := R)).range →*
    (ProductAction.hom (L := W) (R := R)).range where
  toFun p := ⟨p.val, by
    obtain ⟨g, hg⟩ := p.property
    exact ⟨sideAction g, (product_side g).trans hg⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable [Nonempty W] [Nonempty R]

/-- Recover the actual row and column permutations from a permitted
permutation of the rectangle. Nonempty sides make this recovery unique. -/
noncomputable def extractSides : (rectangleAction (W := W) (R := R)).range →*
    (Equiv.Perm W × Equiv.Perm R) :=
  ProductAction.imageEquiv.symm.toMonoidHom.comp productImage

theorem product_extract (p : (rectangleAction (W := W) (R := R)).range) :
    ProductAction.hom (extractSides p) = p.val :=
  congrArg Subtype.val (ProductAction.imageEquiv.apply_symm_apply (productImage p))

theorem extractSides_injective : Function.Injective (extractSides (W := W) (R := R)) := by
  intro p q hpq
  apply Subtype.ext
  have h := congrArg ProductAction.hom hpq
  simpa only [product_extract] using h

theorem extractSides_apply (g : permitted W R) :
    extractSides (rectangleAction.rangeRestrict g) = sideAction g := by
  apply ProductAction.injective
  rw [product_extract, product_side]
  rfl

theorem extractSides_range : (extractSides (W := W) (R := R)).range = sideAction.range := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨g, hg⟩ := q.property
    have he : q = rectangleAction.rangeRestrict g := Subtype.ext hg.symm
    rw [he, extractSides_apply]
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨rectangleAction.rangeRestrict g, extractSides_apply g⟩

theorem extractSides_transports {C : Type*} (x y : W → R → C)
    (p : (rectangleAction (W := W) (R := R)).range) :
    Transports (Function.uncurry x) (Function.uncurry y) p.val ↔
      ∀ a b, y ((extractSides p).1 a) ((extractSides p).2 b) = x a b := by
  rw [← product_extract p]
  constructor
  · intro h a b
    exact h (a, b)
  · intro h z
    exact h z.1 z.2

end GI.Rectangle
