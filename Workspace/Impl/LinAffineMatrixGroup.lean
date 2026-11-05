module

public import Workspace.Impl.LinAffineMatrix
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.Solvable

@[expose] public section

/-! The dense matrices built by linAffineMatrix_spec form the homogeneous
representation, so they can be supplied directly to VectorStabilizerTask. -/
namespace GI.Impl
variable {R : Type*} [CommRing R] {d : ℕ}

theorem linAffineMatrix_mul (A B : Matrix (Fin d) (Fin d) R) (u v : Fin d → R) :
    linAffineMatrix A u * linAffineMatrix B v = linAffineMatrix (A * B) (A.mulVec v + u) := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_castSucc]
  by_cases hi : i.val < d <;> by_cases hj : j.val < d <;>
    simp [linAffineMatrix, linExtend, hi, hj, Matrix.mul_apply, Matrix.mulVec, dotProduct]

@[simp] theorem linAffineMatrix_one :
    linAffineMatrix (1 : Matrix (Fin d) (Fin d) R) 0 = 1 := by
  ext i j
  by_cases hi : i.val < d <;> by_cases hj : j.val < d
  · simp [linAffineMatrix, linExtend, hi, hj, Matrix.one_apply, Fin.ext_iff]
  · have hij : i ≠ j := by intro h; subst j; exact hj hi
    simp [linAffineMatrix, linExtend, hi, hj, Matrix.one_apply, hij]
  · have hij : i ≠ j := by intro h; subst j; exact hi hj
    simp [linAffineMatrix, linExtend, hi, hj, Matrix.one_apply, hij]
  · have hij : i = j := by apply Fin.ext; omega
    simp [linAffineMatrix, linExtend, hi, hj, Matrix.one_apply, hij]

/-- The homogeneous matrix is a unit for every invertible linear part. -/
def linAffineMatrixGL (A : Matrix.GeneralLinearGroup (Fin d) R) (u : Fin d → R) :
    Matrix.GeneralLinearGroup (Fin (d + 1)) R where
  val := linAffineMatrix A.val u
  inv := linAffineMatrix A.inv (-(A.inv.mulVec u))
  val_inv := by
    rw [linAffineMatrix_mul]
    have hu : A.val.mulVec (-(A.inv.mulVec u)) + u = 0 := by
      rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, A.val_inv, Matrix.one_mulVec]
      simp
    rw [A.val_inv, hu, linAffineMatrix_one]
  inv_val := by
    rw [linAffineMatrix_mul, A.inv_val]
    simp

@[simp] theorem linAffineMatrixGL_val (A : Matrix.GeneralLinearGroup (Fin d) R) (u : Fin d → R) :
    (linAffineMatrixGL A u).val = linAffineMatrix A.val u := rfl

/-- A translation cocycle gives an actual matrix representation. -/
def linAffineGLRep {G : Type*} [Group G]
    (ρ : G →* Matrix.GeneralLinearGroup (Fin d) R) (c : G → Fin d → R)
    (hc : ∀ g h, c (g * h) = (ρ g).val.mulVec (c h) + c g) :
    G →* Matrix.GeneralLinearGroup (Fin (d + 1)) R where
  toFun g := linAffineMatrixGL (ρ g) (c g)
  map_one' := by
    have hh := hc 1 1
    simp only [one_mul, map_one, Units.val_one, Matrix.one_mulVec] at hh
    have hz : c 1 = 0 := add_left_cancel (show c 1 + c 1 = c 1 + 0 by simpa using hh.symm)
    apply Units.ext
    change linAffineMatrix (ρ 1).val (c 1) = 1
    rw [map_one, hz, Units.val_one, linAffineMatrix_one]
  map_mul' g h := by
    apply Units.ext
    change linAffineMatrix (ρ (g * h)).val (c (g * h)) =
      linAffineMatrix (ρ g).val (c g) * linAffineMatrix (ρ h).val (c h)
    rw [linAffineMatrix_mul, map_mul, Units.val_mul, hc]

/-- Stabilizing the homogeneous vector is the original affine equation. -/
theorem linAffineGLRep_fixed {G : Type*} [Group G]
    (ρ : G →* Matrix.GeneralLinearGroup (Fin d) R) (c : G → Fin d → R)
    (hc : ∀ g h, c (g * h) = (ρ g).val.mulVec (c h) + c g) (g : G) (x : Fin d → R) :
    (linAffineGLRep ρ c hc g).val.mulVec (linExtend x 1) = linExtend x 1 ↔
      (ρ g).val.mulVec x + c g = x := by
  change (linAffineMatrix (ρ g).val (c g)).mulVec (linExtend x 1) = linExtend x 1 ↔ _
  rw [linAffineMatrix_mulVec, one_smul]
  constructor
  · intro h
    funext i
    have hh := congrFun h i.castSucc
    simpa using hh
  · intro h; rw [h]

theorem solvable_range_of_ker_le {G A B : Type*} [Group G] [Group A] [Group B]
    (ρ : G →* A) (ψ : G →* B) (hker : ρ.ker ≤ ψ.ker) (hsol : Group.IsSolvable ρ.range) :
    Group.IsSolvable ψ.range := by
  let f : G ⧸ ρ.ker →* ψ.range :=
    QuotientGroup.lift ρ.ker ψ.rangeRestrict (fun g hg => Subtype.ext (hker hg))
  have hf : Function.Surjective f := fun ⟨_, g, rfl⟩ => ⟨QuotientGroup.mk g, rfl⟩
  letI : Group.IsSolvable ρ.range := hsol
  letI : Group.IsSolvable (G ⧸ ρ.ker) :=
    solvable_of_solvable_injective (QuotientGroup.quotientKerEquivRange ρ).injective
  exact solvable_of_surjective hf

theorem linAffineGLRep_range_solvable {G : Type*} [Group G]
    (ρ : G →* Matrix.GeneralLinearGroup (Fin d) R) (c : G → Fin d → R)
    (hc : ∀ g h, c (g * h) = (ρ g).val.mulVec (c h) + c g)
    (hsol : Group.IsSolvable ρ.range) :
    Group.IsSolvable (linAffineGLRep ρ c hc).range := by
  let φ := linAffineGLRep ρ c hc
  have hker : φ.ker ≤ ρ.ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply Units.ext
    ext i j
    have hij := congrArg (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) R => M i.castSucc j.castSucc)
      (congrArg Units.val hg)
    simpa [φ, linAffineGLRep, linAffineMatrix, Matrix.one_apply, Fin.ext_iff] using hij
  let q : G ⧸ φ.ker →* ρ.range :=
    QuotientGroup.lift φ.ker ρ.rangeRestrict (fun g hg => Subtype.ext (hker hg))
  let π : φ.range →* ρ.range :=
    q.comp (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom
  have hπ (g : G) : π (φ.rangeRestrict g) = ρ.rangeRestrict g := by
    change q ((QuotientGroup.quotientKerEquivRange φ).symm (φ.rangeRestrict g)) = _
    have heq : (QuotientGroup.quotientKerEquivRange φ).symm (φ.rangeRestrict g) =
        QuotientGroup.mk g :=
      (QuotientGroup.quotientKerEquivRange φ).symm_apply_eq.mpr rfl
    rw [heq]
    rfl
  have hcomm : ∀ a b : π.ker, a * b = b * a := by
    rintro ⟨⟨_, g, rfl⟩, ha⟩ ⟨⟨_, h, rfl⟩, hb⟩
    have hg : ρ g = 1 := congrArg Subtype.val ((hπ g).symm.trans (MonoidHom.mem_ker.mp ha))
    have hh : ρ h = 1 := congrArg Subtype.val ((hπ h).symm.trans (MonoidHom.mem_ker.mp hb))
    apply Subtype.ext
    apply Subtype.ext
    change φ g * φ h = φ h * φ g
    rw [← map_mul, ← map_mul]
    apply Units.ext
    change linAffineMatrix (ρ (g * h)).val (c (g * h)) =
      linAffineMatrix (ρ (h * g)).val (c (h * g))
    simp [map_mul, hc, hg, hh, Matrix.one_mulVec, add_comm]
  have : Group.IsSolvable π.ker := ⟨⟨1, by
    rw [derivedSeries_one, eq_bot_iff]
    change ⁅(⊤ : Subgroup π.ker), ⊤⁆ ≤ ⊥
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_def, hcomm a b, mul_inv_cancel_right, mul_inv_cancel]⟩⟩
  have : Group.IsSolvable ρ.range := hsol
  exact solvable_of_ker_le_range π.ker.subtype π (fun x hx => ⟨⟨x, hx⟩, rfl⟩)

end GI.Impl
