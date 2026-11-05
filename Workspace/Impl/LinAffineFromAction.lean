module

public import Workspace.Impl.LinAffineHomogenize
public import Workspace.Impl.AddEquivGroup
public import Mathlib.Algebra.Group.Equiv.Basic

@[expose] public section

/-! Recover the linear part and the translation cocycle from an action
whose maps satisfy the affine addition identity. -/
namespace GI.Impl
variable {G V : Type*} [Group G] [AddCommGroup V]

def linActionLinearMap (F : G →* Equiv.Perm V)
    (hF : ∀ g x y, F g (x + y) + F g 0 = F g x + F g y) (g : G) : V →+ V where
  toFun x := F g x - F g 0
  map_zero' := sub_self _
  map_add' x y := by
    have hh := eq_sub_of_add_eq (hF g x y)
    rw [hh]
    abel

theorem linActionLinearMap_bijective (F : G →* Equiv.Perm V)
    (hF : ∀ g x y, F g (x + y) + F g 0 = F g x + F g y) (g : G) :
    Function.Bijective (linActionLinearMap F hF g) := by
  constructor
  · intro x y hxy
    apply (F g).injective
    have hh := congrArg (fun z => z + F g 0) hxy
    simpa only [linActionLinearMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, sub_add_cancel] using hh
  · intro y
    refine ⟨(F g).symm (y + F g 0), ?_⟩
    simp [linActionLinearMap]

noncomputable def linActionLinearEquiv (F : G →* Equiv.Perm V)
    (hF : ∀ g x y, F g (x + y) + F g 0 = F g x + F g y) (g : G) : V ≃+ V :=
  AddEquiv.ofBijective (linActionLinearMap F hF g) (linActionLinearMap_bijective F hF g)

theorem linActionLinearEquiv_eval (F : G →* Equiv.Perm V)
    (hF : ∀ g x y, F g (x + y) + F g 0 = F g x + F g y) (g : G) (x : V) :
    linActionLinearEquiv F hF g x + F g 0 = F g x := by
  change (F g x - F g 0) + F g 0 = F g x
  exact sub_add_cancel _ _

noncomputable def linActionLinearRep (F : G →* Equiv.Perm V)
    (hF : ∀ g x y, F g (x + y) + F g 0 = F g x + F g y) : G →* (V ≃+ V) where
  toFun := linActionLinearEquiv F hF
  map_one' := by ext x; simp [linActionLinearEquiv, linActionLinearMap]
  map_mul' g h := by
    ext x
    change F (g * h) x - F (g * h) 0 =
      linActionLinearEquiv F hF g (linActionLinearEquiv F hF h x)
    rw [map_mul]
    change F g (F h x) - F g (F h 0) = _
    rw [← linActionLinearEquiv_eval F hF g (F h x),
      ← linActionLinearEquiv_eval F hF g (F h 0)]
    rw [add_sub_add_right_eq_sub, ← map_sub]
    rfl

theorem linAction_offset_cocycle (F : G →* Equiv.Perm V)
    (hF : ∀ g x y, F g (x + y) + F g 0 = F g x + F g y) (g h : G) :
    F (g * h) 0 = linActionLinearRep F hF g (F h 0) + F g 0 := by
  rw [map_mul]
  exact (linActionLinearEquiv_eval F hF g (F h 0)).symm

end GI.Impl
