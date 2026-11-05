module

public import Workspace.Impl.LinActiveMatrix
public import Workspace.Impl.AddEquivGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

/-! Dense matrices of the linear action on p^j V_p / p^(j+1) V_p.
Inactive coordinates receive the identity action as a harmless fixed padding. -/
namespace GI.Impl
open scoped BigOperators

noncomputable def linPrimaryFieldMatrix {d : ℕ} (p : ℕ) (ν : Fin d → ℕ) (j : ℕ)
    (f : linFiniteVec (linPrimaryOrders p ν) →+ linFiniteVec (linPrimaryOrders p ν)) :
    Matrix (Fin d) (Fin d) (ZMod p) :=
  linActiveMatrix (fun i => j < ν i)
    (fun i k => (linFiniteMatrix (linPrimaryOrders p ν) f i k : ZMod p))

theorem linPrimaryFieldMatrix_drop {d : ℕ} (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (f : linFiniteVec (linPrimaryOrders p ν) →+ linFiniteVec (linPrimaryOrders p ν))
    (i k : Fin d) (hi : j < ν i) (hk : ¬j < ν k) :
    (linFiniteMatrix (linPrimaryOrders p ν) f i k : ZMod p) = 0 := by
  exact (ZMod.natCast_eq_zero_iff _ _).mpr
    (linPrimaryCoefficientDrop p hp ν f i k (by omega))

theorem linPrimaryFieldMatrix_one {d : ℕ} (p : ℕ) (ν : Fin d → ℕ) (j : ℕ) :
    linPrimaryFieldMatrix p ν j (AddMonoidHom.id (linFiniteVec (linPrimaryOrders p ν))) = 1 := by
  unfold linPrimaryFieldMatrix
  calc _ = linActiveMatrix (fun i => j < ν i) (1 : Matrix (Fin d) (Fin d) (ZMod p)) := by
          apply linActiveMatrix_congr
          intro i k hi
          have hpi : p ∣ linPrimaryOrders p ν i := dvd_pow_self p (by omega : ν i ≠ 0)
          simpa only [Matrix.one_apply] using linFiniteMatrix_id_mod (linPrimaryOrders p ν) p i k hpi
    _ = 1 := linActiveMatrix_one _

set_option backward.isDefEq.respectTransparency false in
theorem linPrimaryFieldMatrix_comp {d : ℕ} (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (f g : linFiniteVec (linPrimaryOrders p ν) →+ linFiniteVec (linPrimaryOrders p ν)) :
    linPrimaryFieldMatrix p ν j (f.comp g) =
      linPrimaryFieldMatrix p ν j f * linPrimaryFieldMatrix p ν j g := by
  have hm : ∀ i, 0 < linPrimaryOrders p ν i := fun i => Nat.pow_pos hp
  unfold linPrimaryFieldMatrix
  rw [← linActiveMatrix_mul _ _ _ (linPrimaryFieldMatrix_drop p hp ν j f)]
  apply linActiveMatrix_congr
  intro i k hi
  have hpi : p ∣ linPrimaryOrders p ν i := dvd_pow_self p (by omega : ν i ≠ 0)
  exact linFiniteMatrix_comp_mod (linPrimaryOrders p ν) hm p f g i k hpi

/-- The inverse full action supplies the inverse layer matrix. No faithfulness
of either representation is assumed. -/
noncomputable def linPrimaryFieldGL {d : ℕ} (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (f : linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)) :
    Matrix.GeneralLinearGroup (Fin d) (ZMod p) where
  val := linPrimaryFieldMatrix p ν j f.toAddMonoidHom
  inv := linPrimaryFieldMatrix p ν j f.symm.toAddMonoidHom
  val_inv := by
    rw [← linPrimaryFieldMatrix_comp p hp ν j]
    have he : f.toAddMonoidHom.comp f.symm.toAddMonoidHom =
        AddMonoidHom.id (linFiniteVec (linPrimaryOrders p ν)) := by
      apply AddMonoidHom.ext
      intro x
      exact f.apply_symm_apply x
    rw [he, linPrimaryFieldMatrix_one]
  inv_val := by
    rw [← linPrimaryFieldMatrix_comp p hp ν j]
    have he : f.symm.toAddMonoidHom.comp f.toAddMonoidHom =
        AddMonoidHom.id (linFiniteVec (linPrimaryOrders p ν)) := by
      apply AddMonoidHom.ext
      intro x
      exact f.symm_apply_apply x
    rw [he, linPrimaryFieldMatrix_one]

noncomputable def linPrimaryFieldRep {G : Type*} [Group G] {d : ℕ}
    (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (ρ : G →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν))) :
    G →* Matrix.GeneralLinearGroup (Fin d) (ZMod p) where
  toFun g := linPrimaryFieldGL p hp ν j (ρ g)
  map_one' := by
    apply Units.ext
    change linPrimaryFieldMatrix p ν j (ρ 1).toAddMonoidHom = 1
    rw [map_one]
    exact linPrimaryFieldMatrix_one p ν j
  map_mul' g h := by
    apply Units.ext
    change linPrimaryFieldMatrix p ν j (ρ (g * h)).toAddMonoidHom =
      linPrimaryFieldMatrix p ν j (ρ g).toAddMonoidHom * linPrimaryFieldMatrix p ν j (ρ h).toAddMonoidHom
    rw [map_mul]
    exact linPrimaryFieldMatrix_comp p hp ν j (ρ g).toAddMonoidHom (ρ h).toAddMonoidHom

end GI.Impl
