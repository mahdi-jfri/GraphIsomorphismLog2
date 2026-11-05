module

public import Workspace.Impl.LinObjectAffineMatrix
public import Workspace.Impl.LinObjectEvalBound

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

/-- The concrete column program composes basis creation, affine evaluation,
and subtraction of the translation. -/
theorem linObjectAffineColumn_comp {P : Program} {f basis eval difference C d j : ℕ}
    (he : P.funs[f]? = some (linObjectAffineMatrixColumnF basis eval difference))
    (ctx g offset orders bv ev answer : Val)
    (horders : normReadVal ctx [4] = some orders)
    (hC : 100 ≤ C)
    (hw : (Val.list [.list [ctx,g,offset,.nat d],.nat j]).wt ≤ C)
    (hb : FunDet P basis (.list [.nat j,encInt 1,.nat d]) bv C)
    (heval : FunDet P eval (.list [ctx,g,bv]) ev C)
    (hsub : FunDet P difference (.list [orders,ev,offset]) answer C) :
    FunDet P f (.list [.list [ctx,g,offset,.nat d],.nat j]) answer (100000000 * (C + 2) ^ 2) := by
  let input := Val.list [.list [ctx,g,offset,.nat d],.nat j]
  have e0 : normEnvBound C [input] := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    exact hw
  have rj := linObjectEvalRead (P := P) e0 (slot := 0) rfl [1] rfl (by decide) (by decide) hC
  have rd := linObjectEvalRead (P := P) e0 (slot := 0) rfl [0,3] rfl (by decide) (by decide) hC
  have done : Det P [input] linIntOneE (encInt 1) 100 :=
    (Det.mk2 (Det.nat 0) (Det.mk1 (Det.nat 1))).mono (by decide)
  have wone : (encInt 1).wt = 21 := rfl
  have hp : C + 2 ≤ (C + 2) ^ 2 := Nat.le_self_pow (by decide) _
  have done' := done.mono (show 100 ≤ 2 * linObjectEvalAtom C by unfold linObjectEvalAtom; omega)
  have db := linObjectEvalPack3 (by omega : (Val.nat j).wt ≤ C + 1)
    (by omega : (encInt 1).wt ≤ C + 1) (by omega : (Val.nat d).wt ≤ C + 1)
    (rj.2.mono (by omega)) done' (rd.2.mono (by omega))
  apply FunAll.intro he
  apply EvalAll.letE (normBound_call db hb)
  intro v cb hv
  obtain ⟨heq,wb,hcb⟩ := hv
  subst v
  have e1 : normEnvBound C [input,bv] := normEnvBound_snoc e0 le_rfl wb
  have rc := linObjectEvalRead (P := P) e1 (slot := 0) rfl [0,0] rfl (by decide) (by decide) hC
  have rg := linObjectEvalRead (P := P) e1 (slot := 0) rfl [0,1] rfl (by decide) (by decide) hC
  have rb := linObjectEvalRead (P := P) e1 (slot := 1) rfl [] rfl (by decide) (by decide) hC
  have de := linObjectEvalPack3 (by omega : ctx.wt ≤ C + 1) (by omega : g.wt ≤ C + 1)
    (by omega : bv.wt ≤ C + 1) (rc.2.mono (by omega)) (rg.2.mono (by omega)) (rb.2.mono (by omega))
  apply EvalAll.letE (normBound_call de heval)
  intro v ce hv
  obtain ⟨heq,we,hce⟩ := hv
  subst v
  have e2 : normEnvBound C [input,bv,ev] := normEnvBound_snoc e1 le_rfl we
  have ro := linObjectEvalRead (P := P) e2 (slot := 0) rfl [0,0,4]
    (by change normReadVal ctx [4] = some orders; exact horders) (by decide) (by decide) hC
  have re := linObjectEvalRead (P := P) e2 (slot := 2) rfl [] rfl (by decide) (by decide) hC
  have rf := linObjectEvalRead (P := P) e2 (slot := 0) rfl [0,2] rfl (by decide) (by decide) hC
  have ds := linObjectEvalPack3 (by omega : orders.wt ≤ C + 1) (by omega : ev.wt ≤ C + 1)
    (by omega : offset.wt ≤ C + 1) (ro.2.mono (by omega)) (re.2.mono (by omega)) (rf.2.mono (by omega))
  have wa := hsub.wt_lt.le
  refine (Det.call ds hsub).post fun cost hc => ⟨rfl,?_⟩
  change _ ≤ 100000000 * (C + 2) ^ 2
  unfold linObjectEvalPack at *
  omega

end GI.Impl
