import Workspace.Impl.LinAssignUnits
import Workspace.Impl.LinIntPad

/-! Build the zero/unit assignment table consumed by the exponent interpreter. -/
namespace GI.Impl
open GI.Cited GI.Lang

theorem linZeroVec_value (t : ℕ) :
    linVecVal (0 : Fin t → ℤ) = .list (List.replicate t (encInt 0)) := by
  apply congrArg Val.list
  apply List.eq_replicate_iff.mpr
  constructor
  · simp
  · intro v hv
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
    rfl

def linAssignF (rep units : ℕ) : Expr :=
  .letE (.call rep (mk2 (arg 0) linIntZeroE))
    (.letE (.call rep (mk2 (arg 1) (.var 1)))
      (.letE (.call units (mk3 (arg 0) (arg 2) (.var 2)))
        (mk2 (.var 3) (.var 1))))

def linAssignRepCost (W n B : ℕ) : ℕ :=
  loopModK * (n + 1) * (10 * (W + B + 1) + n + linVectorAccWt n B + 1)
def linAssignZeroWt (t : ℕ) : ℕ := linVectorAccWt t 100
def linAssignInitWt (t ns : ℕ) : ℕ := linVectorAccWt ns (linAssignZeroWt t)
def linAssignUnitsArg (W t ns : ℕ) : ℕ := 10 * (W + linAssignInitWt t ns + 1)
def linAssignCost (W t ns i : ℕ) : ℕ :=
  1000 * (W + t + ns + linAssignRepCost W t 100 +
    linAssignRepCost W ns (linAssignZeroWt t) + linAssignUnitCost (linAssignUnitsArg W t ns) t i +
    linAssignZeroWt t + linAssignInitWt t ns + 1)

/-- Monotonicity of the shared unit-table loop in its input weight. -/
theorem linAssignUnitCost_mono {W V : ℕ} (h : W ≤ V) (t i : ℕ) :
    linAssignUnitCost W t i ≤ linAssignUnitCost V t i := by
  have hb : linAssignUnitBasisCost W t ≤ linAssignUnitBasisCost V t := by
    unfold linAssignUnitBasisCost linBasisCost linAssignUnitBasisArg
    gcongr
  have hm : linAssignUnitAccWt W t ≤ linAssignUnitAccWt V t := by
    unfold linAssignUnitAccWt linVectorAccWt
    gcongr
  unfold linAssignUnitCost linAssignUnitStepCost
  gcongr

set_option maxHeartbeats 1000000 in
theorem linAssign_spec {P : Program} {f rep units basis : ℕ}
    (hf : P.funs[f]? = some (linAssignF rep units)) (hr : P.HasAt rep (replicateFuns rep))
    (hu : P.HasAt units (linAssignUnitFuns units basis)) (hb : P.HasAt basis (linBasisFuns basis))
    (t ns i : ℕ) (hi : i ≤ t) :
    FunDet P f (.list [.nat t, .nat ns, .nat i])
      (.list [.list ((linPrefixVectors t ns i).map linVecVal), linVecVal (0 : Fin t → ℤ)])
      (linAssignCost (Val.list [.nat t, .nat ns, .nat i]).wt t ns i) := by
  let a := Val.list [.nat t, .nat ns, .nat i]
  let W := a.wt
  let zero := linVecVal (0 : Fin t → ℤ)
  let zs := List.replicate ns zero
  let out := zs ++ (((List.finRange t).take i).map fun j => linVecVal (Pi.single j (1 : ℤ)))
  have wt : (Val.nat t).wt < W := wt_le_wt_list (by simp)
  have wn : (Val.nat ns).wt < W := wt_le_wt_list (by simp)
  have wi : (Val.nat i).wt < W := wt_le_wt_list (by simp)
  have wz : zero.wt ≤ linAssignZeroWt t := by
    have hh := linWtList (vs := List.replicate t (encInt 0)) (B := 100) (by
      intro v hv
      rw [List.eq_of_mem_replicate hv]
      decide)
    simpa only [zero, linZeroVec_value, List.length_replicate, linAssignZeroWt, linVectorAccWt] using hh
  have wzs : (Val.list zs).wt ≤ linAssignInitWt t ns := by
    have hh := linWtList (vs := zs) (B := linAssignZeroWt t) (by
      intro v hv
      rw [List.eq_of_mem_replicate hv]
      exact wz)
    simpa only [zs, List.length_replicate, linAssignInitWt, linVectorAccWt] using hh
  have r0 := linReplicate_det hr t (encInt 0)
  rw [← linZeroVec_value] at r0
  have wr0 := wt_list2_le (.nat t) (encInt 0)
  have wzero : (encInt 0).wt ≤ 100 := by decide
  have r0' := r0.mono (show _ ≤ linAssignRepCost W t 100 by
    unfold linAssignRepCost
    apply Nat.mul_le_mul_left
    have ho : (linVecVal (0 : Fin t → ℤ)).wt ≤ linVectorAccWt t 100 := wz
    omega)
  have rn := linReplicate_det hr ns zero
  have wrn := wt_list2_le (.nat ns) zero
  have rn' := rn.mono (show _ ≤ linAssignRepCost W ns (linAssignZeroWt t) by
    unfold linAssignRepCost
    apply Nat.mul_le_mul_left
    have ho : (Val.list (List.replicate ns zero)).wt ≤ linVectorAccWt ns (linAssignZeroWt t) := wzs
    omega)
  have wuarg := wt_list3_le (.nat t) (.nat i) (.list zs)
  have wuin : (Val.list [.nat t, .nat i, .list zs]).wt ≤ linAssignUnitsArg W t ns := by
    unfold linAssignUnitsArg
    omega
  have us := (linAssignUnit_spec hu hb i hi zs).mono (linAssignUnitCost_mono wuin t i)
  have wo := us.wt_lt.le
  have wout := wt_list2_le (.list out) zero
  have darg (j : ℕ) (rest : List Val) {v : Val} (hv : [.nat t, .nat ns, .nat i][j]? = some v) :=
    Det.arg' (P := P) (vs := [.nat t, .nat ns, .nat i]) (rest := rest) (j := j) hv
  have dz : Det P [a] linIntZeroE (encInt 0) _ := Det.mk2 (Det.nat 0) Det.nil
  have d0 := Det.call (Det.mk2 (darg 0 [] rfl) dz) r0'
  have dn := Det.call (Det.mk2 (darg 1 [zero] rfl)
    (Det.var' (P := P) (env := [a, zero]) (i := 1) rfl)) rn'
  have du := Det.call (Det.mk3 (darg 0 [zero, .list zs] rfl) (darg 2 [zero, .list zs] rfl)
    (Det.var' (P := P) (env := [a, zero, .list zs]) (i := 2) rfl)) us
  have dout := Det.mk2 (Det.var' (P := P) (env := [a, zero, .list zs, .list out]) (i := 3) rfl)
    (Det.var' (P := P) (env := [a, zero, .list zs, .list out]) (i := 1) rfl)
  have heq : (linPrefixVectors t ns i).map linVecVal = out := by
    simp [linPrefixVectors, out, zs, zero, Function.comp_def]
  rw [heq]
  apply FunDet.intro hf
  refine (Det.letE d0 (Det.letE dn (Det.letE du dout))).mono ?_
  have w0 : (Val.nat 0).wt = 2 := rfl
  have wnil : (Val.list []).wt = 4 := rfl
  change _ ≤ linAssignCost W t ns i
  unfold linAssignCost
  simp only [W, a, zero, zs, out] at *
  norm_num [encInt, Nat.bits] at *
  omega

end GI.Impl
