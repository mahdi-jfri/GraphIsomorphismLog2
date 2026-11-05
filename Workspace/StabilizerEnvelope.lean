module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.Algebra.Group.Subgroup.Pointwise

@[expose] public section

namespace GI.PrimitiveCartesian

open scoped Pointwise

variable {G V : Type*} [Group G]

/-- Maximality collapses an actual normalized envelope to the intersection
with the maximal subgroup, unless the envelope fills the containing group. -/
theorem coatom_normalized_envelope (N M R : Subgroup G) (hM : IsCoatom M)
    (hRN : R ≤ N) (hinter : N ⊓ M ≤ R) (hnorm : M ≤ (Subgroup.normalizer R)) :
    R = N ⊓ M ∨ R = N := by
  rcases hM.le_iff.mp (show M ≤ R ⊔ M from le_sup_right) with htop | hself
  · right
    apply le_antisymm hRN
    intro n hn
    have hnSup : n ∈ R ⊔ M := by rw [htop]; exact Subgroup.mem_top n
    have hnMul : n ∈ (R : Set G) * (M : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left R M hnorm]
      exact hnSup
    obtain ⟨r, hr, m, hm, he⟩ := hnMul
    have hmN : m ∈ N := by
      have h := N.mul_mem (N.inv_mem (hRN hr)) hn
      rwa [← he, inv_mul_cancel_left] at h
    rw [← he]
    exact R.mul_mem hr (hinter ⟨hmN, hm⟩)
  · left
    apply le_antisymm _ hinter
    exact le_inf hRN (by rw [← hself]; exact le_sup_left)

/-- A proper normalized envelope of the socle-point stabilizer cannot be
larger than that stabilizer in a primitive physical action. -/
theorem primitive_proper_envelope_eq [MulAction G V] [Nontrivial V]
    [MulAction.IsPreprimitive G V] (a : V) (N R : Subgroup G)
    (hRN : R ≤ N) (hinter : N ⊓ MulAction.stabilizer G a ≤ R)
    (hnorm : MulAction.stabilizer G a ≤ (Subgroup.normalizer R)) (hproper : R ≠ N) :
    R = N ⊓ MulAction.stabilizer G a :=
  (coatom_normalized_envelope N (MulAction.stabilizer G a) R
    (MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G a)
    hRN hinter hnorm).resolve_right hproper

end GI.PrimitiveCartesian
