module

public import Workspace.CosetProductCoordinates
public import Mathlib.GroupTheory.GroupAction.Primitive

@[expose] public section

namespace GI.PrimitiveCoordinates

open GI.PrimitiveCartesian

variable {G V W : Type*} [Group G] [MulAction G V] [MulAction G W]
  [MulAction.IsPretransitive G V] [MulAction.IsPretransitive G W]

/-- Actual coordinates between two transitive actions whose actual
base-point stabilizers agree. -/
noncomputable def sameStabilizerCoordinates (a : V) (b : W)
    (hstab : MulAction.stabilizer G a = MulAction.stabilizer G b) : V ≃ W :=
  (transitiveCosetCoordinates (G := G) a).trans
    ((Subgroup.quotientEquivOfEq hstab).trans (transitiveCosetCoordinates (G := G) b).symm)

theorem sameStabilizerCoordinates_smul (a : V) (b : W)
    (hstab : MulAction.stabilizer G a = MulAction.stabilizer G b) (g : G) :
    sameStabilizerCoordinates a b hstab (g • a) = g • b := by
  change (transitiveCosetCoordinates (G := G) b).symm
    ((Subgroup.quotientEquivOfEq hstab) (transitiveCosetCoordinates a (g • a))) = _
  rw [transitiveCosetCoordinates_smul]
  rfl

theorem sameStabilizerCoordinates_equivariant (a : V) (b : W)
    (hstab : MulAction.stabilizer G a = MulAction.stabilizer G b) (g : G) (v : V) :
    sameStabilizerCoordinates a b hstab (g • v) =
      g • sameStabilizerCoordinates a b hstab v := by
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq G a v
  rw [← mul_smul, sameStabilizerCoordinates_smul, sameStabilizerCoordinates_smul, mul_smul]

variable [Nontrivial V] [Nontrivial W] [MulAction.IsPreprimitive G V]

omit [MulAction.IsPretransitive G V] in
/-- Maximality identifies the two actual stabilizers as soon as one
contains the primitive-action stabilizer and the target action is nontrivial. -/
theorem primitive_stabilizer_eq (a : V) (b : W)
    (hle : MulAction.stabilizer G a ≤ MulAction.stabilizer G b) :
    MulAction.stabilizer G a = MulAction.stabilizer G b := by
  have hproper : MulAction.stabilizer G b ≠ ⊤ := by
    intro he
    obtain ⟨c, hc⟩ := exists_ne b
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G b c
    have hgb : g • b = b := by
      exact (show g ∈ MulAction.stabilizer G b from he ▸ Subgroup.mem_top g)
    exact hc (hg.symm.trans hgb)
  rcases (MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G a).le_iff.mp hle
    with htop | heq
  · exact (hproper htop).elim
  · exact heq.symm

end GI.PrimitiveCoordinates
