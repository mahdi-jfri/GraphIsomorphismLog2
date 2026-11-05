module

public import Workspace.Impl.GenNormNumbering
public import Workspace.Impl.GenNormLabels
public import Workspace.Impl.LargestOrbit

@[expose] public section

/-!
# Computing the fiber size of the Johnson block map

Block zero meets the domain, and off-domain positions have the unused label `d ≥ 2`.
Counting zeroes in the exposed numbering therefore counts exactly the fiber used by the
normalization labels. No group computation is needed.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

/-- Zeroes of the block numbering correspond exactly to domain points in block zero. -/
theorem normFiber_count {Ω C : Type} {S : State Ω C} {n : ℕ} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) :
    ((List.finRange n).map (Q.labFin en)).count 0 =
      Nat.card {v : S.dom // Q.blk v.1 = ⟨0, by have := Q.two_le; omega⟩} := by
  classical
  have hz (i : Fin n) : Q.labFin en i = 0 ↔ en.symm i ∈ S.dom ∧
      Q.blk (en.symm i) = ⟨0, by have := Q.two_le; omega⟩ := by
    unfold PrimitiveQuotient.labFin
    by_cases hi : en.symm i ∈ S.dom
    · rw [if_pos hi]
      exact ⟨fun h => ⟨hi, Fin.ext h⟩, fun h => congrArg Fin.val h.2⟩
    · rw [if_neg hi]
      exact iff_of_false (by have := Q.two_le; omega) (fun h => hi h.1)
  rw [count_map_finRange, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun i => ⟨⟨en.symm i.1, (hz i.1).mp i.2 |>.1⟩, (hz i.1).mp i.2 |>.2⟩
      invFun := fun v => ⟨en v.1.1, (hz (en v.1.1)).mpr (by
        simpa only [en.symm_apply_apply] using (And.intro v.1.2 v.2))⟩
      left_inv := fun i => by ext; simp
      right_inv := fun v => by ext; simp }

/-- The existing count program computes exactly the fiber size in `normLabelVal`. -/
theorem normFiber_spec {Pg : Program} {b : ℕ} (hb : Pg.HasAt b (countFuns b))
    {Ω C : Type} {S : State Ω C} {n : ℕ} (en : Ω ≃ Fin n) (Q : PrimitiveQuotient S)
    (num : Fin n → ℕ) (hnum : ∀ i, num i = Q.labFin en i) :
    FunDet Pg b (.list [.nat 0, encFun num])
      (.nat (Nat.card {v : S.dom // Q.blk v.1 = ⟨0, by have := Q.two_le; omega⟩}))
      (countK * (n + 1) ^ 3) := by
  have h := count_spec hb (xs := (List.finRange n).map num) (j := 0) (B := n)
    (by
      intro a ha
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
      rw [hnum]
      exact (Q.labFin_le en i).trans (Q.d_le_card en)) (by omega) (by simp)
  have he : num = Q.labFin en := funext hnum
  subst he
  rw [normFiber_count en Q] at h
  simpa only [encFun_eq_natList] using h

end GI.Impl
