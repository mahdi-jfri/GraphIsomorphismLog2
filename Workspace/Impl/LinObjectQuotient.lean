module

public import Workspace.Impl.LinPresentationExtend

@[expose] public section

/-! The object-glue quotient `W/D`. Each component of `W` is the quotient
of the abelian group `A/N` by a local stabilizer. The diagonal relations
ask for one common translation, rather than separate translations. -/
namespace GI.Impl

variable {ι Q : Type*} [AddCommGroup Q] {d : ℕ}

/-- The diagonal map into the product of local quotients. -/
def linObjectDiagonal (B : ι → Submodule ℤ Q) :
    Q →ₗ[ℤ] (∀ i, Q ⧸ B i) where
  toFun a i := (B i).mkQ a
  map_add' a b := by ext i; simp
  map_smul' n a := by ext i; simp

/-- Apply the presentation map separately in each piece. -/
def linObjectProductMap (B : ι → Submodule ℤ Q)
    (f : (Fin d → ℤ) →ₗ[ℤ] Q) :
    (ι → Fin d → ℤ) →ₗ[ℤ] (∀ i, Q ⧸ B i) where
  toFun z i := (B i).mkQ (f (z i))
  map_add' a b := by ext i; simp
  map_smul' n a := by
    ext i
    change (B i).mkQ (f (n • a i)) = n • (B i).mkQ (f (a i))
    rw [map_smul, map_smul]

theorem linObjectProductMap_surjective (B : ι → Submodule ℤ Q)
    (f : (Fin d → ℤ) →ₗ[ℤ] Q) (hf : Function.Surjective f) :
    Function.Surjective (linObjectProductMap B f) := by
  intro w
  classical
  have h (i : ι) : ∃ z, (B i).mkQ (f z) = w i :=
    ((Submodule.mkQ_surjective (B i)).comp hf) (w i)
  choose z hz using h
  exact ⟨z, funext hz⟩

theorem linObjectProductMap_ker (B : ι → Submodule ℤ Q)
    (f : (Fin d → ℤ) →ₗ[ℤ] Q) (z : ι → Fin d → ℤ) :
    z ∈ LinearMap.ker (linObjectProductMap B f) ↔ ∀ i, f (z i) ∈ B i := by
  change (fun i => (B i).mkQ (f (z i))) = 0 ↔ _
  simp only [funext_iff, Pi.zero_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]

/-- Vanishing in `W/D` is exactly the existence of a common negative
translation. This is the additive form of `DCond`, with the same sign. -/
theorem linObjectCommonCorrection (B : ι → Submodule ℤ Q)
    (w : ∀ i, Q ⧸ B i) :
    (LinearMap.range (linObjectDiagonal B)).mkQ w = 0 ↔
      ∃ a : Q, ∀ i, w i + (B i).mkQ a = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨-a, fun i => by simp [linObjectDiagonal]⟩
  · rintro ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    ext i
    have hi := ha i
    change (B i).mkQ (-a) = w i
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left hi).symm

/-- In original abelian coordinates, the common correction lands in every
local stabilizer. No enumeration of the finite quotient is involved. -/
theorem linObjectCommonCorrection_coordinates (B : ι → Submodule ℤ Q)
    (f : (Fin d → ℤ) →ₗ[ℤ] Q) (z : ι → Fin d → ℤ) :
    (LinearMap.range (linObjectDiagonal B)).mkQ (linObjectProductMap B f z) = 0 ↔
      ∃ a : Q, ∀ i, f (z i) + a ∈ B i := by
  rw [linObjectCommonCorrection]
  apply exists_congr
  intro a
  apply forall_congr'
  intro i
  change (B i).mkQ (f (z i)) + (B i).mkQ a = 0 ↔ _
  rw [← map_add, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- Repeat an integer vector in each piece. These are the additional
relations which impose the diagonal image of `A/N`. -/
def linObjectIntegerDiagonal : (Fin d → ℤ) →ₗ[ℤ] (ι → Fin d → ℤ) where
  toFun z _ := z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem linObjectDiagonal_range (B : ι → Submodule ℤ Q)
    (f : (Fin d → ℤ) →ₗ[ℤ] Q) (hf : Function.Surjective f) :
    (LinearMap.range (linObjectIntegerDiagonal (ι := ι) (d := d))).map
      (linObjectProductMap B f) = LinearMap.range (linObjectDiagonal B) := by
  ext w
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨f z, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨z, rfl⟩ := hf a
    exact ⟨linObjectIntegerDiagonal z, ⟨z, rfl⟩, rfl⟩

/-- The full integer kernel for `W/D`: local relations plus diagonal
relations. Thus appending diagonal rows gives the desired quotient. -/
theorem linObjectQuotient_ker (B : ι → Submodule ℤ Q)
    (f : (Fin d → ℤ) →ₗ[ℤ] Q) (hf : Function.Surjective f) :
    LinearMap.ker ((LinearMap.range (linObjectDiagonal B)).mkQ.comp
      (linObjectProductMap B f)) =
      LinearMap.ker (linObjectProductMap B f) ⊔
        LinearMap.range (linObjectIntegerDiagonal (ι := ι) (d := d)) := by
  rw [← linObjectDiagonal_range B f hf, LinearMap.ker_comp,
    Submodule.ker_mkQ, Submodule.comap_map_eq, sup_comm]

/-- The presentation of `W/D`, with the map specified on all representatives. -/
noncomputable def linObjectQuotientEquiv (B : ι → Submodule ℤ Q)
    (f : (Fin d → ℤ) →ₗ[ℤ] Q) (hf : Function.Surjective f) :
    ((ι → Fin d → ℤ) ⧸ (LinearMap.ker (linObjectProductMap B f) ⊔
      LinearMap.range (linObjectIntegerDiagonal (ι := ι) (d := d)))) ≃ₗ[ℤ]
      ((∀ i, Q ⧸ B i) ⧸ LinearMap.range (linObjectDiagonal B)) := by
  let g := (LinearMap.range (linObjectDiagonal B)).mkQ.comp (linObjectProductMap B f)
  have hg : Function.Surjective g := (Submodule.mkQ_surjective _).comp
    (linObjectProductMap_surjective B f hf)
  exact (Submodule.quotEquivOfEq _ _ (linObjectQuotient_ker B f hf).symm).trans
    (g.quotKerEquivOfSurjective hg)

@[simp] theorem linObjectQuotientEquiv_mk (B : ι → Submodule ℤ Q)
    (f : (Fin d → ℤ) →ₗ[ℤ] Q) (hf : Function.Surjective f) (z : ι → Fin d → ℤ) :
    linObjectQuotientEquiv B f hf
      ((LinearMap.ker (linObjectProductMap B f) ⊔
        LinearMap.range (linObjectIntegerDiagonal (ι := ι) (d := d))).mkQ z) =
      (LinearMap.range (linObjectDiagonal B)).mkQ (linObjectProductMap B f z) := rfl

end GI.Impl
