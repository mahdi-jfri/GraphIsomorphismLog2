module

public import Workspace.Impl.ColLink

@[expose] public section

/-!
# The child hierarchy of the column step, entry by entry

The column step stores `dropTriv I.hier'`, where `I.hier'` is the list of lower pieces, the row
interval and the list of upper pieces, built by the recursion `towerSplit`. A program builds the
pieces level by level. This file gives

* `colTowerSplit_eq`: `towerSplit` as a list of the pieces of each level (`List.ofFn`);
* `colForall₂_filter`: canonical interval values pass through the filter of `dropTriv` when the
  program's filter reads the stored ratio.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω : Type}

section Tower

variable {H : Type*} [Group H] (L : ℕ → Subgroup H) (N : Subgroup H) (p₁ p₂ : ℕ → Setoid Ω)

/-- The lower piece of level `j` of the split, for an interval `I`. -/
noncomputable def colLowerI (j : ℕ) (I : Interval Ω) : Interval Ω :=
  ⟨p₁ j, (L j ⊓ N).relIndex (L (j + 1) ⊓ N), min I.cap ((L j ⊓ N).relIndex (L (j + 1) ⊓ N)),
    I.origin⟩

/-- The upper piece of level `j` of the split, for an interval `I`. -/
noncomputable def colUpperI (j : ℕ) (I : Interval Ω) : Interval Ω :=
  ⟨p₂ j, (N ⊔ L j).relIndex (N ⊔ L (j + 1)), min I.cap ((N ⊔ L j).relIndex (N ⊔ L (j + 1))),
    I.origin⟩

/-- **The split, level by level.** -/
theorem colTowerSplit_eq : ∀ (j : ℕ) (l : List (Interval Ω)),
    towerSplit L N p₁ p₂ j l =
      List.ofFn fun k : Fin l.length =>
        (colLowerI L N p₁ (j + k) l[k], colUpperI L N p₂ (j + k) l[k])
  | _, [] => rfl
  | j, I :: l => by
    rw [towerSplit, colTowerSplit_eq (j + 1) l, List.ofFn_succ]
    simp only [Fin.val_zero, add_zero, Fin.val_succ, List.cons.injEq]
    refine ⟨rfl, ?_⟩
    congr 1
    funext k
    rw [show j + 1 + (k : ℕ) = j + ((k : ℕ) + 1) by omega]
    rfl

end Tower

/-- **Filtering both sides of `Forall₂`.** If `R v I` relates each value to its interval and the
test `p` on the value agrees with the test `q` on the interval, the filtered lists are still
related. -/
theorem colForall₂_filter {α β : Type*} {R : α → β → Prop} (p : α → Bool) (q : β → Bool)
    (hpq : ∀ a b, R a b → p a = q b) :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs →
      List.Forall₂ R (as.filter p) (bs.filter q)
  | _, _, .nil => .nil
  | a :: as, b :: bs, .cons h hs => by
    have ih := colForall₂_filter p q hpq hs
    simp only [List.filter_cons, hpq a b h]
    split_ifs
    · exact .cons h ih
    · exact ih

/-! ### The hierarchy value of the child -/

/-- An interval value from its parts. -/
def colIV {n : ℕ} (lab : Fin n → ℕ) (r c o : ℕ) : Val :=
  .list [encFun lab, .nat r, .nat c, .nat o]

/-- The program's filter of `dropTriv`: keep an interval value whose ratio is at least `2`. -/
def colKeep : Val → Bool
  | .list [_, .nat r, _, _] => decide (2 ≤ r)
  | _ => false

theorem colKeep_of_IntervalValC {n : ℕ} {e : Ω ≃ Fin n} {v : Val} {I : Interval Ω}
    (h : IntervalValC e v I) : colKeep v = decide (2 ≤ I.ratio) := by
  obtain ⟨pv, -, rfl⟩ := h
  rfl

theorem colIV_IntervalValC {n : ℕ} {e : Ω ≃ Fin n} {lab : Fin n → ℕ} {I : Interval Ω}
    (h : PartitionValC e (encFun lab) I.part) : IntervalValC e (colIV lab I.ratio I.cap I.origin) I :=
  ⟨_, h, rfl⟩

variable {C : Type} {S : State Ω C} {L : GiantLabels S}

/-- **The child hierarchy value.** Let `lowLab k`, `upLab k` label the lower and upper parts of
level `k`, `colLab` the columns, and `lr k`, `ur k` be the lower and upper ratios. Then the
filtered list of interval values is a canonical value of `dropTriv I.hier'`. -/
theorem colHierVal {n : ℕ} (e : Ω ≃ Fin n) (I : ColumnPre S L)
    (lowLab upLab : Fin I.loc.length → Fin n → ℕ) (colLab : Fin n → ℕ)
    (lr ur : Fin I.loc.length → ℕ)
    (hlow : ∀ k, PartitionValC e (encFun (lowLab k)) (I.lowerPart k))
    (hup : ∀ k, PartitionValC e (encFun (upLab k)) (I.upperPart k))
    (hcols : PartitionValC e (encFun colLab) I.cols)
    (hlr : ∀ k : Fin I.loc.length, lr k =
      (RowForm.localTower I.e I.i0 I.loc I.b₀ k ⊓ I.Nl).relIndex
        (RowForm.localTower I.e I.i0 I.loc I.b₀ (k + 1) ⊓ I.Nl))
    (hur : ∀ k : Fin I.loc.length, ur k =
      (I.Nl ⊔ RowForm.localTower I.e I.i0 I.loc I.b₀ k).relIndex
        (I.Nl ⊔ RowForm.localTower I.e I.i0 I.loc I.b₀ (k + 1))) :
    HierValC e (.list (((List.ofFn fun k => colIV (lowLab k) (lr k) (min I.loc[k].cap (lr k))
        I.loc[k].origin) ++ [colIV colLab I.rowI.ratio I.rowI.cap I.rowI.origin] ++
        List.ofFn fun k => colIV (upLab k) (ur k) (min I.loc[k].cap (ur k)) I.loc[k].origin).filter
          colKeep)) (dropTriv I.hier') := by
  refine ⟨_, rfl, ?_⟩
  unfold dropTriv ColumnPre.hier' ColumnPre.split
  rw [colTowerSplit_eq]
  refine colForall₂_filter _ _ (fun a b h => colKeep_of_IntervalValC h) ?_
  simp only [List.map_ofFn]
  refine List.rel_append (List.rel_append ?_ ?_) ?_
  · rw [List.forall₂_iff_get]
    refine ⟨by simp, fun i h1 h2 => ?_⟩
    have hi : i < I.loc.length := by simpa using h1
    simp only [List.get_eq_getElem, List.getElem_ofFn, Function.comp_apply, zero_add]
    have := colIV_IntervalValC (lab := lowLab ⟨i, hi⟩)
      (I := colLowerI (RowForm.localTower I.e I.i0 I.loc I.b₀) I.Nl I.lowerPart i I.loc[i])
      (hlow _)
    unfold colLowerI at this ⊢
    rw [hlr]
    exact this
  · exact List.Forall₂.cons (colIV_IntervalValC hcols) .nil
  · rw [List.forall₂_iff_get]
    refine ⟨by simp, fun i h1 h2 => ?_⟩
    have hi : i < I.loc.length := by simpa using h1
    simp only [List.get_eq_getElem, List.getElem_ofFn, Function.comp_apply, zero_add]
    have := colIV_IntervalValC (lab := upLab ⟨i, hi⟩)
      (I := colUpperI (RowForm.localTower I.e I.i0 I.loc I.b₀) I.Nl I.upperPart i I.loc[i])
      (hup _)
    unfold colUpperI at this ⊢
    rw [hur]
    exact this

end GI.Impl
