import Workspace.AlternatingSections
import Workspace.BlockPartition

/-!
# Width bounds through invariant labelings and partitions

Helpers for Lemmas A.12 and A.29: the alternating-section width
(`GI.SectionCaps.Cap`) of a permutation group is at most the larger of the number
of blocks of an invariant partition and the largest block size.
-/

namespace GI.Carrier

open Equiv Equiv.Perm

/-- A group that acts faithfully on `X` and fixes a labeling of `X` has
alternating-section width at most the largest label class. It is the product of
its restrictions to the label classes. -/
theorem cap_of_fixed_labels {L X B : Type*} [Group L] [Finite X] [Finite B]
    (ρ : L →* Perm X) (faithful : Function.Injective ρ) (label : X → B)
    (fixes : ∀ g x, label (ρ g x) = label x) {s : ℕ}
    (classes : ∀ b, Nat.card {x // label x = b} ≤ s) :
    GI.SectionCaps.Cap L s := by
  classical
  haveI := Fintype.ofFinite X
  haveI := Fintype.ofFinite B
  let act : ∀ b : B, L →* Perm {x // label x = b} := fun b =>
    { toFun := fun g =>
        { toFun := fun x => ⟨ρ g x.val, (fixes g x.val).trans x.property⟩
          invFun := fun x => ⟨ρ g⁻¹ x.val, (fixes g⁻¹ x.val).trans x.property⟩
          left_inv := fun x => by
            apply Subtype.ext
            change ρ g⁻¹ (ρ g x.val) = x.val
            rw [← Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Perm.one_apply]
          right_inv := fun x => by
            apply Subtype.ext
            change ρ g (ρ g⁻¹ x.val) = x.val
            rw [← Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Perm.one_apply] }
      map_one' := by ext x; simp
      map_mul' := fun g h => by ext x; simp }
  refine GI.SectionCaps.faithful_family act ?_ (fun b => ?_)
  · intro g hg
    apply faithful
    rw [map_one]
    ext x
    have h := congrArg (fun p : Perm {y // label y = label x} => (p ⟨x, rfl⟩).val)
      (hg (label x))
    simpa [act] using h
  · rw [← Nat.card_eq_fintype_card]
    exact classes b

/-- **Partition width bound.** If `H ≤ Sym(V)` preserves a partition with at most
`u` points in each block, then `aw(H) ≤ max {number of blocks, u}`: the image on
the blocks lies in a symmetric group of that degree, and the kernel acts
faithfully on the blocks, each of size at most `u`. -/
theorem partition_cap {V : Type*} [Fintype V] [DecidableEq V] {H : Subgroup (Perm V)}
    (p : GI.InvariantPartition H) [Fintype (Quotient p.setoid)]
    [DecidableEq (Quotient p.setoid)] {u : ℕ}
    (hu : ∀ b : Quotient p.setoid,
      Fintype.card {x : V // (⟦x⟧ : Quotient p.setoid) = b} ≤ u) :
    GI.SectionCaps.Cap H (max (Fintype.card (Quotient p.setoid)) u) := by
  classical
  have image : GI.SectionCaps.Cap p.quotientHom.range (Fintype.card (Quotient p.setoid)) :=
    GI.SectionCaps.subgroup GI.SectionCaps.permutations _
  let K := p.quotientHom.ker
  let ρ : K →* Perm V := H.subtype.comp K.subtype
  have faithful : Function.Injective ρ := fun a b h => Subtype.ext (Subtype.ext h)
  have kernel : GI.SectionCaps.Cap K u := by
    refine cap_of_fixed_labels ρ faithful (fun x => (⟦x⟧ : Quotient p.setoid)) ?_ ?_
    · intro g x
      have hg : p.quotientHom g.val = 1 := g.property
      have h := congrArg (fun f : Perm (Quotient p.setoid) => f ⟦x⟧) hg
      exact h
    · intro b
      rw [Nat.card_eq_fintype_card]
      convert hu b
  have h := GI.SectionCaps.extension p.quotientHom.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict]; exact kernel) image
  intro U k hk q onto
  have := h U k hk q onto
  omega

end GI.Carrier
