import Workspace.Impl.GenExposeCand

/-!
# Keeping the quotient numbering in the exposure contract

The quotient action and the Cameron identification use numbered blocks. Equality of blocks
alone does not say which block has which number. Exposure already numbers blocks by their
least representatives. Numbering its representative labels again gives exactly the same
numbers. This file records that fact so normalization can compute each generator's quotient
permutation in the coordinates used by Cameron recognition.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

private theorem normRepOf_congr {n : ℕ} {key key' : Fin n → ℕ}
    (h : ∀ i j, key i = key j ↔ key' i = key' j) : Cls.repOf key = Cls.repOf key' := by
  funext i
  simp only [Cls.repOf, List.findIdx_map, Function.comp_def]
  congr 1
  funext j
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact h j i

private theorem normRepsOf_congr {n : ℕ} (dm : Fin n → ℕ) {key key' : Fin n → ℕ}
    (h : ∀ i j, key i = key j ↔ key' i = key' j) :
    Cls.repsOf dm key = Cls.repsOf dm key' := by
  have hr := normRepOf_congr h
  unfold Cls.repsOf
  congr 1
  funext j
  unfold Cls.repTest
  simp only [hr]

private theorem normNumOf_congr {n : ℕ} (dm : Fin n → ℕ) {key key' : Fin n → ℕ}
    (h : ∀ i j, key i = key j ↔ key' i = key' j) :
    Cls.numOf dm key = Cls.numOf dm key' := by
  have hr := normRepOf_congr h
  have hrs := normRepsOf_congr dm h
  funext i
  unfold Cls.numOf
  rw [hrs, hr]

private theorem normRekey_rep {n : ℕ} (lab dm : Fin n → ℕ) (hl : Cls.LabOK lab dm) :
    ∀ i j, Cls.keyOf lab dm i = Cls.keyOf lab dm j ↔
      Cls.keyOf (Cls.repOf (Cls.keyOf lab dm)) dm i =
        Cls.keyOf (Cls.repOf (Cls.keyOf lab dm)) dm j := by
  intro i j
  have hri := Cls.repOf_lt (Cls.keyOf lab dm) i
  have hrj := Cls.repOf_lt (Cls.keyOf lab dm) j
  by_cases hi : dm i = 0 <;> by_cases hj : dm j = 0
  · simp only [Cls.keyOf, hi, hj, if_true]
  · have hlj := hl j hj
    simp only [Cls.keyOf, hi, hj, if_true, if_false]
    exact iff_of_false (by omega) (by omega)
  · have hli := hl i hi
    simp only [Cls.keyOf, hi, hj, if_true, if_false]
    exact iff_of_false (by omega) (by omega)
  · have h := (Cls.repOf_eq_iff (Cls.keyOf lab dm) i j).symm
    simpa only [Cls.keyOf, hi, hj, if_false] using h

/-- Replacing labels by their least representatives keeps the exact class numbers. -/
theorem normRenumber_rep {n : ℕ} (lab dm : Fin n → ℕ) (hl : Cls.LabOK lab dm) :
    Cls.numOf dm (Cls.keyOf (Cls.repOf (Cls.keyOf lab dm)) dm) =
      Cls.numOf dm (Cls.keyOf lab dm) :=
  (normNumOf_congr dm (normRekey_rep lab dm hl)).symm

/-- It also keeps the ordered list of domain representatives. -/
theorem normReps_rep {n : ℕ} (lab dm : Fin n → ℕ) (hl : Cls.LabOK lab dm) :
    Cls.repsOf dm (Cls.keyOf (Cls.repOf (Cls.keyOf lab dm)) dm) =
      Cls.repsOf dm (Cls.keyOf lab dm) :=
  (normRepsOf_congr dm (normRekey_rep lab dm hl)).symm

/-- The quotient uses precisely the block numbers recomputed from its exposed representative
labels, in increasing representative order. The value layout does not need another field. -/
def normNumbered {Ω C : Type} {n : ℕ} (en : Ω ≃ Fin n) {S : State Ω C}
    (Q : PrimitiveQuotient S) (rep : Val) : Prop :=
  ∃ lab : Fin n → ℕ, rep = encFun lab ∧ (∀ i, lab i < n) ∧
    (∀ i, Q.labFin en i = Cls.numOf (indF en S.dom) (Cls.keyOf lab (indF en S.dom)) i) ∧
    Q.d = (Cls.repsOf (indF en S.dom) (Cls.keyOf lab (indF en S.dom))).length

/-- The representative labels computed by exposure preserve its chosen quotient numbering. -/
theorem normNumbered_of {Ω C : Type} {n : ℕ} {en : Ω ≃ Fin n} {S : State Ω C}
    (Q : PrimitiveQuotient S) {lab : Fin n → ℕ} (hl : Cls.LabOK lab (indF en S.dom))
    (hd : Q.d = (Cls.repsOf (indF en S.dom) (Cls.keyOf lab (indF en S.dom))).length)
    (hblk : ∀ v ∈ S.dom, (Q.blk v : ℕ) =
      Cls.numOf (indF en S.dom) (Cls.keyOf lab (indF en S.dom)) (en v)) :
    normNumbered en Q (encFun (Cls.repOf (Cls.keyOf lab (indF en S.dom)))) := by
  refine ⟨_, rfl, Cls.repOf_lt _, ?_, ?_⟩
  · intro i
    rw [normRenumber_rep lab _ hl]
    exact labFin_eq_numOf Q hd hblk i
  · rw [normReps_rep lab _ hl]
    exact hd

/-- The numerical block data consumed by the point-pairing program. -/
def normBlockData {Ω C : Type} {n : ℕ} (en : Ω ≃ Fin n) {S : State Ω C}
    (Q : PrimitiveQuotient S) (num : Fin n → ℕ) (reps : List ℕ) : Prop :=
  (∀ i, num i ≤ n) ∧ (∀ r ∈ reps, r < n) ∧ reps.length = Q.d ∧
    (∀ v ∈ S.dom, (Q.blk v : ℕ) = num (en v)) ∧
    (∀ t (ht : t < reps.length), ∃ h : reps[t] < n, en.symm ⟨_, h⟩ ∈ S.dom ∧ num ⟨_, h⟩ = t)

/-- Recomputing the exposed numbering gives the concrete block map and representatives used
by the pairing program, in the exact quotient coordinates of Cameron's table. -/
theorem normNumbering_spec {Pg : Program} {b : ℕ} (hcls : Pg.HasAt b (clsFuns b))
    {Ω C : Type} {n : ℕ} (en : Ω ≃ Fin n) {S : State Ω C} (Q : PrimitiveQuotient S)
    {rep : Val} (hrep : normNumbered en Q rep) :
    FunAll Pg b (.list [rep, encFun (indF en S.dom)]) (fun w cost =>
      ∃ (num : Fin n → ℕ) (reps : List ℕ) (rep' : Val),
        w = .list [encFun num, natList reps, rep'] ∧ normBlockData en Q num reps ∧
          (∀ i, num i = Q.labFin en i) ∧ cost ≤ clsK * (n + 1) ^ 4) := by
  obtain ⟨lab, rfl, hlt, hnum, hd⟩ := hrep
  have h := cls_spec hcls lab (indF en S.dom) (X := n) (fun i => (hlt i).le)
    (fun i => by unfold indF; split_ifs <;> omega) le_rfl
  refine FunAll.mono h fun w cost hw => ?_
  refine ⟨Cls.numOf (indF en S.dom) (Cls.keyOf lab (indF en S.dom)),
    Cls.repsOf (indF en S.dom) (Cls.keyOf lab (indF en S.dom)), _, hw.1, ?_, (fun i => (hnum i).symm), hw.2⟩
  refine ⟨numOf_le _ _, ?_, hd.symm, ?_, fun t ht => repsOf_rep t ht⟩
  · intro r hr
    exact ((Cls.mem_repsOf (indF en S.dom) (Cls.keyOf lab (indF en S.dom))).mp hr).choose
  · intro v hv
    have h := hnum (en v)
    unfold PrimitiveQuotient.labFin at h
    rw [en.symm_apply_apply v, if_pos hv] at h
    exact h

end GI.Impl
