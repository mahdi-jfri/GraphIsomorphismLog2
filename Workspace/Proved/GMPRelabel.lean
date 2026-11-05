module

public import Workspace.Proved.GMPBase
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace GI.Proved

open GI.Composition

/-- The inductive assertion on the canonical domain of a given degree. -/
def GMPDegreeBound (n : ℕ) : Prop :=
  ∀ (A : Subgroup (Equiv.Perm (Fin n))) (R : Subgroup A)
    [R.Normal] [MulAction.IsPretransitive R (Fin n)],
    (bFac (A ⧸ R) : ℝ) ≤ (n : ℝ) ^ Real.logb 2 n

/-- Renumbering the domain lets the induction hypothesis apply to the
actual block set and the actual fiber, without changing their quotient groups. -/
theorem gmp_degreeBound_relabel {α : Type*} [Finite α]
    (h : GMPDegreeBound (Nat.card α))
    (A : Subgroup (Equiv.Perm α)) (R : Subgroup A) [R.Normal]
    [MulAction.IsPretransitive R α] :
    (bFac (A ⧸ R) : ℝ) ≤ (Nat.card α : ℝ) ^ Real.logb 2 (Nat.card α) := by
  let e := Finite.equivFin α
  let eP := e.permCongrHom
  let A' := A.map eP.toMonoidHom
  let eA : A ≃* A' := eP.subgroupMap A
  let R' := R.map eA.toMonoidHom
  have : R'.Normal := Subgroup.Normal.map inferInstance eA.toMonoidHom eA.surjective
  let eR : R ≃* R' := eA.subgroupMap R
  let f : α →ₑ[eR] Fin (Nat.card α) :=
    { toFun := e
      map_smul' := by
        intro r x
        change e ((r.val : Equiv.Perm α) x) =
          e ((r.val : Equiv.Perm α) (e.symm (e x)))
        rw [Equiv.symm_apply_apply] }
  have : MulAction.IsPretransitive R' (Fin (Nat.card α)) :=
    MulAction.IsPretransitive.of_surjective_map (f := f) e.surjective inferInstance
  have hb := h A' R'
  let q : A ⧸ R ≃* A' ⧸ R' := QuotientGroup.congr R R' eA rfl
  rw [bFac_congr q]
  exact hb

end GI.Proved
