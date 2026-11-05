module

public import Workspace.RelabeledCartesianCover
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace GI.CartesianCoordinates

variable {G V I D : Type*} [Fintype I] [Fintype D]

noncomputable def finiteCoordinates (e : V ≃ (I → D)) :
    V ≃ (Fin (Fintype.card I) → Fin (Fintype.card D)) :=
  e.trans (Equiv.arrowCongr (Fintype.equivFin I) (Fintype.equivFin D))

theorem finiteCoordinates_fibers [Group G] [MulAction G V]
    (e : V ≃ (I → D)) (p : G →* Equiv.Perm I)
    (fibers : ∀ g i x y, e x i = e y i → e (g • x) (p g i) = e (g • y) (p g i))
    (g : G) (i : Fin (Fintype.card I)) (x y : V)
    (hxy : finiteCoordinates e x i = finiteCoordinates e y i) :
    finiteCoordinates e (g • x)
        (relabelPerm (Fintype.equivFin I) (p g) i) =
      finiteCoordinates e (g • y) (relabelPerm (Fintype.equivFin I) (p g) i) := by
  let a := Fintype.equivFin I
  let b := Fintype.equivFin D
  change b (e x (a.symm i)) = b (e y (a.symm i)) at hxy
  have h := fibers g (a.symm i) x y (b.injective hxy)
  change b (e (g • x) (a.symm (a (p g (a.symm i))))) =
    b (e (g • y) (a.symm (a (p g (a.symm i)))))
  rw [a.symm_apply_apply]
  exact congrArg b h

/-- Finite reindexing produces exactly the Cartesian witness consumed by
the existing primitive-alternative budget theorem. -/
theorem finite_cartesian_witness (H : Subgroup (Equiv.Perm V))
    (e : V ≃ (I → D)) (p : H →* Equiv.Perm I)
    (fibers : ∀ (h : H) i x y, e x i = e y i →
      e ((h : Equiv.Perm V) x) (p h i) = e ((h : Equiv.Perm V) y) (p h i))
    (hd : 2 ≤ Fintype.card D) (hi : 2 ≤ Fintype.card I) :
    ∃ d s : ℕ, 2 ≤ d ∧ 2 ≤ s ∧
      ∃ f : V ≃ (Fin s → Fin d), Nonempty (CartesianCover (H.map (relabelPerm f).toMonoidHom)) := by
  let p' := (relabelPerm (Fintype.equivFin I)).toMonoidHom.comp p
  refine ⟨Fintype.card D, Fintype.card I, hd, hi, finiteCoordinates e, ⟨?_⟩⟩
  exact CartesianCover.ofRelabeledFiberInvariance H (finiteCoordinates e) p'
    (finiteCoordinates_fibers e p fibers)

end GI.CartesianCoordinates
