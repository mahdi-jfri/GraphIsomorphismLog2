module

public import Workspace.Proved.GMPProducts

@[expose] public section

namespace GI.Proved

open GI.Composition

/-- The same intersection viewed inside either subgroup. -/
def gmpIntersectionEquiv {A : Type*} [Group A] (R K : Subgroup A) :
    R.subgroupOf K ≃* K.subgroupOf R where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The quotient by a normal subgroup splits over any surjective homomorphism. -/
theorem gmp_bFac_quotient_surjective {A B : Type*} [Group A] [Finite A]
    [Group B] [Finite B] (f : A →* B) (hf : Function.Surjective f)
    (R : Subgroup A) [R.Normal] [(R.map f).Normal] :
    bFac (A ⧸ R) = bFac (f.ker ⧸ R.subgroupOf f.ker) * bFac (B ⧸ R.map f) := by
  have hR : bFac R = bFac (R.subgroupOf f.ker) * bFac (R.map f) := by
    let r := f.subgroupMap R
    have hr := bFac_mul r.ker (X := R)
    rw [bFac_congr (QuotientGroup.quotientKerEquivOfSurjective r
      (f.subgroupMap_surjective R)), Subgroup.ker_subgroupMap,
      ← bFac_congr (gmpIntersectionEquiv R f.ker)] at hr
    exact hr
  have h := bFac_mul f.ker (X := A)
  rw [bFac_congr (QuotientGroup.quotientKerEquivOfSurjective f hf),
    bFac_mul (R.subgroupOf f.ker), bFac_mul (R.map f), bFac_mul R] at h
  rw [hR] at h
  have h' : (bFac (R.subgroupOf f.ker) * bFac (R.map f)) * bFac (A ⧸ R) =
      (bFac (R.subgroupOf f.ker) * bFac (R.map f)) *
        (bFac (f.ker ⧸ R.subgroupOf f.ker) * bFac (B ⧸ R.map f)) := by
    calc
      _ = (bFac (R.subgroupOf f.ker) * bFac (f.ker ⧸ R.subgroupOf f.ker)) *
          (bFac (R.map f) * bFac (B ⧸ R.map f)) := h
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos bFac_pos bFac_pos) h'

instance gmp_normal_image_range {A B : Type*} [Group A] [Group B]
    (f : A →* B) (R : Subgroup A) [R.Normal] :
    ((R.map f).subgroupOf f.range).Normal := by
  constructor
  intro x hx g
  obtain ⟨a, ha⟩ := g.property
  obtain ⟨r, hr, her⟩ := hx
  change f r = x.val at her
  change g.val * x.val * g.val⁻¹ ∈ R.map f
  exact ⟨a * r * a⁻¹, (inferInstance : R.Normal).conj_mem r hr a,
    by simp only [map_mul, map_inv, ha, her]⟩

/-- The splitting used in GMP Theorem 2.3, with the top group represented
as the actual image of a possibly non-surjective homomorphism. -/
theorem gmp_bFac_quotient_hom {A B : Type*} [Group A] [Finite A]
    [Group B] [Finite B] (f : A →* B) (R : Subgroup A) [R.Normal] :
    bFac (A ⧸ R) = bFac (f.ker ⧸ R.subgroupOf f.ker) *
      bFac (f.range ⧸ (R.map f).subgroupOf f.range) := by
  have hR : bFac R = bFac (R.subgroupOf f.ker) * bFac (R.map f) := by
    let r := f.subgroupMap R
    have hr := bFac_mul r.ker (X := R)
    rw [bFac_congr (QuotientGroup.quotientKerEquivOfSurjective r
      (f.subgroupMap_surjective R)), Subgroup.ker_subgroupMap,
      ← bFac_congr (gmpIntersectionEquiv R f.ker)] at hr
    exact hr
  have h := bFac_ker_range f
  rw [bFac_mul (R.subgroupOf f.ker), bFac_mul ((R.map f).subgroupOf f.range),
    bFac_congr (Subgroup.subgroupOfEquivOfLe (R.map_le_range f)), bFac_mul R] at h
  rw [hR] at h
  have h' : (bFac (R.subgroupOf f.ker) * bFac (R.map f)) * bFac (A ⧸ R) =
      (bFac (R.subgroupOf f.ker) * bFac (R.map f)) *
        (bFac (f.ker ⧸ R.subgroupOf f.ker) *
          bFac (f.range ⧸ (R.map f).subgroupOf f.range)) := by
    calc
      _ = (bFac (R.subgroupOf f.ker) * bFac (f.ker ⧸ R.subgroupOf f.ker)) *
          (bFac (R.map f) * bFac (f.range ⧸ (R.map f).subgroupOf f.range)) := h
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos bFac_pos bFac_pos) h'

end GI.Proved
