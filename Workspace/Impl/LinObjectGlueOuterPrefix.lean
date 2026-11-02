import Workspace.Impl.LinObjectGlueOuterGrowth

namespace GI.Impl
open GI.Cited GI.Lang

variable {n : ℕ} (I : linObjectGlueRaw n)

noncomputable def linObjectGlueRaw.normalizedAll : List (TmRiO n) :=
  (I.Y++I.X).map (linObjectNorm (linObjectColor (I.Y++I.X)))
noncomputable def linObjectGlueRaw.normalizedTarget : List (TmRiO n) :=
  I.Y.map (linObjectNorm (linObjectColor (I.Y++I.X)))
noncomputable def linObjectGlueRaw.normalizedSource : List (TmRiO n) :=
  I.X.map (linObjectNorm (linObjectColor (I.Y++I.X)))

theorem linObjectGlueRaw.normalizedAll_split : I.normalizedAll = I.normalizedTarget++I.normalizedSource :=
  List.map_append

theorem linObjectGlueRaw.normalize_value : I.normalize.value =
    .list [encGroup I.hs,encGroup I.ns,encGroup (keepList I.as),tmGlObjsVal I.normalizedSource,
      tmGlObjsVal I.normalizedTarget,encGroup I.bs,encPerm I.τ] := rfl

noncomputable def linObjectGlueRaw.prefixValues : List Val :=
  [I.value,tmGlObjsVal (I.Y++I.X),tmGlObjsVal I.normalizedAll,tmGlObjsVal I.normalizedTarget,
    tmGlObjsVal I.normalizedSource,encGroup (keepList I.as)]

def linObjectGlueOuterInv (i : ℕ) (env : List Val) : Prop := env = I.prefixValues.take (i+1)

def linObjectGlueOuterSteps (append normalize slice reduce : ℕ) : List (ℕ × linObjectReadPlan) :=
  [(append,linObjectGlueJoinPlan),(normalize,linObjectGlueNormalizePlan),(slice,linObjectGlueTargetPlan),
    (slice,linObjectGlueSourcePlan),(reduce,linObjectGlueReducePlan)]

theorem linObjectGlueOuterInv_root {i : ℕ} {env : List Val} (h : linObjectGlueOuterInv I i env) :
    env[0]? = some I.value := by rw [h]; rfl

theorem linObjectGlueRaw.size_bounds : n ≤ I.value.wt ∧ I.as.length ≤ I.value.wt := by
  have wa : (encGroup I.as).wt < I.value.wt := wt_le_wt_list (by simp [linObjectGlueRaw.value,tmGlIn])
  have hn := S_le_wt_encGroup I.as
  have h1 : n+1 ≤ (I.as.length+2)*(n+1) := Nat.le_mul_of_pos_left _ (by omega)
  have h2 : I.as.length+2 ≤ (I.as.length+2)*(n+1) := Nat.le_mul_of_pos_right _ (by omega)
  constructor <;> omega

theorem linObjectGlueRaw.target_slice_spec {P : Program} {b : ℕ} (h : P.HasAt b (linSliceFuns b)) :
    let input := Val.list [.nat 0,.nat I.Y.length,tmGlObjsVal I.normalizedAll]
    FunDet P b input (tmGlObjsVal I.normalizedTarget) (linSliceCost input.wt) := by
  let ys := I.normalizedTarget.map tmGlObjVal
  let xs := I.normalizedSource.map tmGlObjVal
  have hY : ys.length = I.Y.length := by simp only [ys,linObjectGlueRaw.normalizedTarget,List.length_map]
  have hsplit : I.normalizedAll.map tmGlObjVal = ys++xs := by rw [I.normalizedAll_split,List.map_append]
  have hr := linSlice_spec h (ys++xs) 0 ys.length (by simp)
  simp only [List.drop_zero,List.take_left] at hr
  simpa only [hY,tmGlObjsVal,hsplit] using hr

theorem linObjectGlueRaw.source_slice_spec {P : Program} {b : ℕ} (h : P.HasAt b (linSliceFuns b)) :
    let input := Val.list [.nat I.Y.length,.nat I.X.length,tmGlObjsVal I.normalizedAll]
    FunDet P b input (tmGlObjsVal I.normalizedSource) (linSliceCost input.wt) := by
  let ys := I.normalizedTarget.map tmGlObjVal
  let xs := I.normalizedSource.map tmGlObjVal
  have hY : ys.length = I.Y.length := by simp only [ys,linObjectGlueRaw.normalizedTarget,List.length_map]
  have hX : xs.length = I.X.length := by simp only [xs,linObjectGlueRaw.normalizedSource,List.length_map]
  have hsplit : I.normalizedAll.map tmGlObjVal = ys++xs := by rw [I.normalizedAll_split,List.map_append]
  have hr := linSlice_spec h (ys++xs) ys.length xs.length (by simp)
  simp only [List.drop_left,List.take_length] at hr
  simpa only [hY,hX,tmGlObjsVal,hsplit] using hr

end GI.Impl
