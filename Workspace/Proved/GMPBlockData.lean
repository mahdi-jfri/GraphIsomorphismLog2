module

public import Workspace.Proved.GMPKernel
public import Workspace.BlockKernelCard

@[expose] public section

/-! # Coordinate maps for the block reduction in GMP -/

namespace GI.Proved

open GI.Composition
open scoped commutatorElement

variable {V B : Type*} {A : Subgroup (Equiv.Perm V)}

def gmpBlockStabilizer (c : BlockCover A B) (b : B) : Subgroup A :=
  (MulAction.stabilizer (Equiv.Perm B) b).comap c.project

def gmpBlockProject (c : BlockCover A B) (b : B) :
    gmpBlockStabilizer c b →* Equiv.Perm {x : V // c.label x = b} where
  toFun g :=
    { toFun x := ⟨(g.val : Equiv.Perm V) x.val, by
        rw [c.equivariant, x.property]; exact g.property⟩
      invFun x := ⟨(g.val : Equiv.Perm V)⁻¹ x.val, by
        change c.label (((g.val⁻¹ : A) : Equiv.Perm V) x.val) = b
        rw [c.equivariant, x.property]; exact g⁻¹.property⟩
      left_inv x := Subtype.ext ((g.val : Equiv.Perm V).symm_apply_apply x.val)
      right_inv x := Subtype.ext ((g.val : Equiv.Perm V).apply_symm_apply x.val) }
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

def gmpBlockKernelInclusion (c : BlockCover A B) (b : B) :
    c.project.ker →* gmpBlockStabilizer c b :=
  Subgroup.inclusion (fun g hg => congrArg (fun p : Equiv.Perm B => p b) hg)

def gmpBlockCoordinate (c : BlockCover A B) (b : B) :
    c.project.ker →* (gmpBlockProject c b).range :=
  (gmpBlockProject c b).rangeRestrict.comp (gmpBlockKernelInclusion c b)

def gmpBlockNormalImage (c : BlockCover A B) (R : Subgroup A) (b : B) :
    Subgroup (gmpBlockProject c b).range :=
  (R.subgroupOf (gmpBlockStabilizer c b)).map (gmpBlockProject c b).rangeRestrict

instance gmpBlockNormalImage_normal (c : BlockCover A B) (R : Subgroup A)
    [R.Normal] (b : B) : (gmpBlockNormalImage c R b).Normal :=
  Subgroup.Normal.map inferInstance _ (gmpBlockProject c b).rangeRestrict_surjective

theorem gmpBlockCoordinate_faithful (c : BlockCover A B)
    (k : c.project.ker) (hk : ∀ b, gmpBlockCoordinate c b k = 1) : k = 1 := by
  apply c.kernelFiberHom_injective
  funext b
  exact congrArg Subtype.val (hk b)

theorem gmpBlockNormalImage_mem (c : BlockCover A B) (R : Subgroup A)
    (b : B) (k : c.project.ker) (hk : k.val ∈ R) :
    gmpBlockCoordinate c b k ∈ gmpBlockNormalImage c R b :=
  ⟨gmpBlockKernelInclusion c b k, hk, rfl⟩

/-- Normality in the ambient group places the coordinate commutators
in the projection of the intersection of the two normal subgroups. -/
theorem gmpBlockCoordinate_commutator (c : BlockCover A B) (R : Subgroup A)
    [R.Normal] (b : B) (k l : c.project.ker)
    (hl : gmpBlockCoordinate c b l ∈ gmpBlockNormalImage c R b) :
    ⁅gmpBlockCoordinate c b k, gmpBlockCoordinate c b l⁆ ∈
      (R.subgroupOf c.project.ker).map (gmpBlockCoordinate c b) := by
  obtain ⟨r, hr, her⟩ := hl
  have hR : ⁅k.val, r.val⁆ ∈ R :=
    (Subgroup.commutator_le_right ⊤ R)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) hr)
  have hK : ⁅k.val, r.val⁆ ∈ c.project.ker :=
    (Subgroup.commutator_le_left c.project.ker ⊤)
      (Subgroup.commutator_mem_commutator k.property (Subgroup.mem_top _))
  refine ⟨⟨⁅k.val, r.val⁆, hK⟩, hR, ?_⟩
  change (gmpBlockProject c b).rangeRestrict ⁅gmpBlockKernelInclusion c b k, r⁆ = _
  rw [map_commutatorElement, her]
  rfl

/-- If a base-kernel element agrees with an element of `R` on one
fiber, normality and transitivity of `R` give agreement on every fiber. -/
theorem gmpBlockCoordinate_determined (c : BlockCover A B) (R : Subgroup A)
    [R.Normal] [MulAction.IsPretransitive R V]
    (hsurj : Function.Surjective c.label) (b₀ : B) (k : c.project.ker)
    (hk : gmpBlockCoordinate c b₀ k ∈ gmpBlockNormalImage c R b₀) (b : B) :
    gmpBlockCoordinate c b k ∈ gmpBlockNormalImage c R b := by
  obtain ⟨r, hr, her⟩ := hk
  obtain ⟨x₀, hx₀⟩ := hsurj b₀
  obtain ⟨x, hx⟩ := hsurj b
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R x₀ x
  have hgb : c.project g.val b₀ = b := by
    rw [← hx₀, ← c.equivariant, show (g.val : Equiv.Perm V) x₀ = x from hg, hx]
  have hrb : c.project r.val b₀ = b₀ := r.property
  have hkb : c.project k.val = 1 := k.property
  let t : A := k.val * g.val * k.val⁻¹ * r.val * g.val⁻¹
  have htR : t ∈ R :=
    R.mul_mem (R.mul_mem ((inferInstance : R.Normal).conj_mem g.val g.property k.val) hr)
      (R.inv_mem g.property)
  have htb : c.project t b = b := by
    change c.project (k.val * g.val * k.val⁻¹ * r.val * g.val⁻¹) b = b
    simp only [map_mul, map_inv, hkb, one_mul, inv_one, mul_one,
      Equiv.Perm.mul_apply, Equiv.Perm.inv_apply_self]
    rw [← hgb, Equiv.Perm.inv_apply_self, hrb, hgb]
  refine ⟨⟨t, htb⟩, htR, ?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro y
  apply Subtype.ext
  have hy₀ : c.label ((g.val⁻¹ : A) • y.val) = b₀ := by
    change c.label (((g.val⁻¹ : A) : Equiv.Perm V) y.val) = b₀
    rw [c.equivariant, y.property, map_inv, ← hgb, Equiv.Perm.inv_apply_self]
  have hmatch : (r.val : Equiv.Perm V) ((g.val⁻¹ : A) • y.val) =
      (k.val : Equiv.Perm V) ((g.val⁻¹ : A) • y.val) :=
    congrArg (fun p : (gmpBlockProject c b₀).range =>
      ((p.val : Equiv.Perm {x : V // c.label x = b₀})
        ⟨(g.val⁻¹ : A) • y.val, hy₀⟩).val) her
  change r.val • (g.val⁻¹ • y.val) = k.val • (g.val⁻¹ • y.val) at hmatch
  change t • y.val = k.val • y.val
  dsimp only [t]
  simp only [mul_smul]
  change k.val • (g.val • (k.val⁻¹ • (r.val • (g.val⁻¹ • y.val)))) = _
  rw [hmatch, inv_smul_smul, smul_inv_smul]

end GI.Proved
