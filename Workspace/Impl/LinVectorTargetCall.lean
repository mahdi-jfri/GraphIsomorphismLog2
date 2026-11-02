import Workspace.Impl.LinVectorTransportProg

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linVectorTargetCost (h : VectorStabilizer) (W : ℕ) : ℕ :=
  10000 * (W + (vectorStabilizerPrim h).boundSize (100 * (W + 1)) + 13 * (W + 1) ^ 6 + 1)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4000 in
theorem linVectorTarget_call (h : VectorStabilizer) {P : Program} {j : ℕ}
    (hj : P.prims[j]? = some (vectorStabilizerPrim h)) (I : VecStabInst)
    (w : Fin I.d → ZMod I.p) (rest : List Val) :
    EvalAll P (.list [vecStabEnc I, encVec w] :: rest)
      (.prim j (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
        (.get (arg 0) (.nat 2)) (arg 1)))
      (fun out cost => GensVal I.n out (vecStabSub (linVectorTarget I w)) ∧
        cost ≤ linVectorTargetCost h (Val.list [vecStabEnc I, encVec w]).wt) := by
  let a := Val.list [vecStabEnc I, encVec w]
  let W := a.wt
  let ms := Val.list (I.gs.attach.map fun g =>
    encModMatrix (I.φ ⟨g.val, Subgroup.subset_closure g.property⟩).val)
  have ws : (vecStabEnc I).wt < W := wt_le_wt_list (by simp [W, a])
  have ww : (encVec w).wt < W := wt_le_wt_list (by simp [W, a])
  have wg : (encGroup I.gs).wt < (vecStabEnc I).wt := wt_le_wt_list (by simp [vecStabEnc])
  have wp : (Val.nat I.p).wt < (vecStabEnc I).wt := wt_le_wt_list (by simp [vecStabEnc])
  have wm : ms.wt < (vecStabEnc I).wt := wt_le_wt_list (by simp [ms, vecStabEnc])
  have wtgt : (vecStabEnc (linVectorTarget I w)).wt ≤ 100 * (W + 1) := by
    have hh := wt_list4_le (encGroup I.gs) (.nat I.p) ms (encVec w)
    change (Val.list [encGroup I.gs, .nat I.p, ms, encVec w]).wt ≤ _
    omega
  have dn := Det.arg' (P := P) (vs := [vecStabEnc I, encVec w]) (rest := rest) (j := 0) rfl
  have dv := Det.arg' (P := P) (vs := [vecStabEnc I, encVec w]) (rest := rest) (j := 1) rfl
  have dg := Det.get' dn (Det.nat 0) rfl
  have dp := Det.get' dn (Det.nat 1) rfl
  have dm := Det.get' dn (Det.nat 2) rfl
  have da := Det.mk4 dg dp dm dv
  have hh := vectorStabilizer_call h (linVectorTarget I w) hj da
  have hs := (vecStabEnc (linVectorTarget I w)).size_le_wt.trans wtgt
  have hp : (vectorStabilizerPrim h).bound (vecStabEnc (linVectorTarget I w)) ≤
      (vectorStabilizerPrim h).boundSize (100 * (W + 1)) := by
    unfold Prim.bound Prim.boundSize
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hs 2) _)
  have hn : I.n ≤ W := (linWreathInput_dimensions I w).1
  have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 6
  refine hh.mono fun out cost ho => ⟨ho.1, ?_⟩
  have hc := ho.2
  change cost ≤ linVectorTargetCost h W
  dsimp only [linVectorTargetCost]
  have wmk := wt_list4_le (encGroup I.gs) (.nat I.p) ms (encVec w)
  dsimp only [a, W, ms, linVectorTarget, vecStabEnc] at *
  omega

theorem linVectorTargetCost_poly (h : VectorStabilizer) :
    PBU (fun _ W _ => linVectorTargetCost h W) := by
  unfold linVectorTargetCost Prim.boundSize
  norm_poly

end GI.Impl
