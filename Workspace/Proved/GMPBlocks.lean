module

public import Workspace.Proved.GMPBlockData
public import Workspace.Proved.GMPExactSequence

@[expose] public section

/-! # GMP Theorem 2.3 for the action on an actual block system -/

namespace GI.Proved

open GI.Composition

variable {V B : Type*} [Finite V] [Fintype B]
  {A : Subgroup (Equiv.Perm V)}

/-- GMP Theorem 2.3. The action on labels gives the top quotient, and
the action of a block stabilizer on one fiber gives the local quotient. -/
theorem gmp_block_quotient_bound (c : BlockCover A B) (R : Subgroup A)
    [R.Normal] [MulAction.IsPretransitive R V]
    (hsurj : Function.Surjective c.label) (b : B) :
    bFac (A ⧸ R) ≤
      bFac (c.project.range ⧸ (R.map c.project).subgroupOf c.project.range) *
      bFac ((gmpBlockProject c b).range ⧸ gmpBlockNormalImage c R b) := by
  have hker := gmp_wreath_kernel_bound (R.subgroupOf c.project.ker)
    (fun b => (gmpBlockProject c b).range) (gmpBlockCoordinate c)
    (gmpBlockNormalImage c R) b (gmpBlockCoordinate_faithful c)
    (fun b k hk => gmpBlockNormalImage_mem c R b k hk)
    (fun k hk b' => gmpBlockCoordinate_determined c R hsurj b k hk b')
    (fun b k l hl => gmpBlockCoordinate_commutator c R b k l (hl b))
  rw [gmp_bFac_quotient_hom c.project R, mul_comm]
  exact Nat.mul_le_mul_left _ hker

/-- The normal image in the top permutation group is transitive. -/
theorem gmp_block_top_transitive (c : BlockCover A B) (R : Subgroup A)
    [MulAction.IsPretransitive R V] (hsurj : Function.Surjective c.label) :
    MulAction.IsPretransitive ((R.map c.project).subgroupOf c.project.range) B := by
  constructor
  intro b d
  obtain ⟨x, rfl⟩ := hsurj b
  obtain ⟨y, rfl⟩ := hsurj d
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R x y
  refine ⟨⟨⟨c.project r.val, ⟨r.val, rfl⟩⟩,
    Subgroup.mem_map_of_mem c.project r.property⟩, ?_⟩
  change c.project r.val (c.label x) = c.label y
  rw [← c.equivariant]
  exact congrArg c.label hr

/-- The image of the normal subgroup's block stabilizer is transitive
on that block, since a transporter between its points fixes its label. -/
theorem gmp_block_local_transitive (c : BlockCover A B) (R : Subgroup A)
    [MulAction.IsPretransitive R V] (b : B) :
    MulAction.IsPretransitive
      (gmpBlockNormalImage c R b) {x : V // c.label x = b} := by
  constructor
  intro x y
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R x.val y.val
  have hstab : c.project r.val b = b := by
    rw [← x.property, ← c.equivariant,
      show (r.val : Equiv.Perm V) x.val = y.val from hr, y.property]
    exact x.property.symm
  let rS : gmpBlockStabilizer c b := ⟨r.val, hstab⟩
  refine ⟨⟨(gmpBlockProject c b).rangeRestrict rS, ⟨rS, r.property, rfl⟩⟩, ?_⟩
  exact Subtype.ext hr

/-- The local normal subgroup, as a subgroup of the full permutation
group, is the same image as its range-valued version. -/
theorem gmp_block_local_image (c : BlockCover A B) (R : Subgroup A) (b : B) :
    (gmpBlockNormalImage c R b).map (gmpBlockProject c b).range.subtype =
      (R.subgroupOf (gmpBlockStabilizer c b)).map (gmpBlockProject c b) := by
  rw [gmpBlockNormalImage, Subgroup.map_map]
  rfl

end GI.Proved
