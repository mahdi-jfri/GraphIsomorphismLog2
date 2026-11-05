module

public import Workspace.BlockHereditary
public import Mathlib.Data.Quot

@[expose] public section

namespace GI

variable {V : Type*} {H : Subgroup (Equiv.Perm V)}

/-- A preserved partition given by its actual equivalence relation. -/
structure InvariantPartition (H : Subgroup (Equiv.Perm V)) where
  setoid : Setoid V
  preserved : ∀ (h : H) (x y : V), setoid.r x y →
    setoid.r ((h : Equiv.Perm V) x) ((h : Equiv.Perm V) y)

namespace InvariantPartition

def quotientPerm (p : InvariantPartition H) (h : H) : Equiv.Perm (Quotient p.setoid) where
  toFun := @Quotient.map V V p.setoid p.setoid (h : Equiv.Perm V)
    (fun {x y} hab => p.preserved h x y hab)
  invFun := @Quotient.map V V p.setoid p.setoid ((h⁻¹ : H) : Equiv.Perm V)
    (fun {x y} hab => p.preserved h⁻¹ x y hab)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h x =>
      change Quotient.mk p.setoid ((h : Equiv.Perm V)⁻¹ ((h : Equiv.Perm V) x)) = _
      simp
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h x =>
      change Quotient.mk p.setoid ((h : Equiv.Perm V) ((h : Equiv.Perm V)⁻¹ x)) = _
      simp

def quotientHom (p : InvariantPartition H) : H →* Equiv.Perm (Quotient p.setoid) where
  toFun := p.quotientPerm
  map_one' := by
    ext q
    induction q using Quotient.inductionOn with
    | h x => rfl
  map_mul' g h := by
    ext q
    induction q using Quotient.inductionOn with
    | h x => rfl

/-- The induced block-label homomorphism is constructed from preservation;
it is not supplied as an additional structural assumption. -/
def blockCover (p : InvariantPartition H) : BlockCover H (Quotient p.setoid) where
  label := Quotient.mk p.setoid
  project := p.quotientHom
  equivariant _ _ := rfl

theorem label_surjective (p : InvariantPartition H) :
    Function.Surjective p.blockCover.label := by
  intro q
  induction q using Quotient.inductionOn with
  | h x => exact ⟨x, rfl⟩

theorem same_block_iff (p : InvariantPartition H) (x y : V) :
    p.blockCover.label x = p.blockCover.label y ↔ p.setoid.r x y :=
  ⟨Quotient.exact, Quotient.sound⟩

def restrict (p : InvariantPartition H) {L : Subgroup (Equiv.Perm V)} (hle : L ≤ H) :
    InvariantPartition L where
  setoid := p.setoid
  preserved l := p.preserved (Subgroup.inclusion hle l)

theorem restriction_preserves_label (p : InvariantPartition H)
    {L : Subgroup (Equiv.Perm V)} (hle : L ≤ H) (x : V) :
    (p.restrict hle).blockCover.label x = p.blockCover.label x := rfl

end InvariantPartition

end GI
