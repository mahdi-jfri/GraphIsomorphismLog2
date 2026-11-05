module

public import Workspace.Impl.LinObjectMatrixColumn

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linObjectAffineMatrix_comp {P : Program} {f zero eval range map transpose C : ℕ}
    (he : P.funs[f]? = some (linObjectAffineMatrixF zero eval range map transpose))
    (ctx g zv offset ids columns matrix : Val) (orders : List Val)
    (horders : normReadVal ctx [4] = some (.list orders)) (hC : 100 ≤ C)
    (hw : (Val.list [ctx,g]).wt ≤ C)
    (hz : FunDet P zero (.list [.nat orders.length,encInt 0]) zv C)
    (heval : FunDet P eval (.list [ctx,g,zv]) offset C)
    (hrange : FunDet P range (.nat orders.length) ids C)
    (hmap : FunDet P map (.list [.list [ctx,g,offset,.nat orders.length],ids]) columns C)
    (ht : FunDet P transpose (.list [.nat orders.length,columns]) matrix C) :
    FunDet P f (.list [ctx,g]) (.list [matrix,offset]) (10000000000 * (C + 2) ^ 2) := by
  let input := Val.list [ctx,g]
  have e0 : normEnvBound C [input] := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    exact hw
  have rm := linObjectEvalRead (P := P) e0 (slot := 0) rfl [0,4]
    (by change normReadVal ctx [4] = some (.list orders); exact horders) (by decide) (by decide) hC
  have rd := linObjectEvalLength rm.1 rm.2
  have dzero : Det P [input] linIntZeroE (encInt 0) 100 :=
    (Det.mk2 (Det.nat 0) Det.nil).mono (by decide)
  have wz0 : (encInt 0).wt = 15 := rfl
  have hp : C + 2 ≤ (C + 2) ^ 2 := Nat.le_self_pow (by decide) _
  have dzero' := dzero.mono (show 100 ≤ 2 * linObjectEvalAtom C by unfold linObjectEvalAtom; omega)
  have dz := linObjectEvalPack2 rd.1 (by omega : (encInt 0).wt ≤ C + 1) rd.2 dzero'
  apply FunAll.intro he
  apply EvalAll.letE (normBound_call dz hz)
  intro v cz hv
  obtain ⟨heq,wz,hcz⟩ := hv
  subst v
  have e1 : normEnvBound C [input,zv] := normEnvBound_snoc e0 le_rfl wz
  have rc := linObjectEvalRead (P := P) e1 (slot := 0) rfl [0] rfl (by decide) (by decide) hC
  have rg := linObjectEvalRead (P := P) e1 (slot := 0) rfl [1] rfl (by decide) (by decide) hC
  have rz := linObjectEvalRead (P := P) e1 (slot := 1) rfl [] rfl (by decide) (by decide) hC
  have de := linObjectEvalPack3 (by omega : ctx.wt ≤ C + 1) (by omega : g.wt ≤ C + 1)
    (by omega : zv.wt ≤ C + 1) (rc.2.mono (by omega)) (rg.2.mono (by omega)) (rz.2.mono (by omega))
  apply EvalAll.letE (normBound_call de heval)
  intro v ce hv
  obtain ⟨heq,wo,hce⟩ := hv
  subst v
  have e2 : normEnvBound C [input,zv,offset] := normEnvBound_snoc e1 le_rfl wo
  have rm := linObjectEvalRead (P := P) e2 (slot := 0) rfl [0,4]
    (by change normReadVal ctx [4] = some (.list orders); exact horders) (by decide) (by decide) hC
  have rd := linObjectEvalLength rm.1 rm.2
  have dr := rd.2.mono (show 2 * linObjectEvalAtom C ≤ linObjectEvalPack C by
    unfold linObjectEvalAtom linObjectEvalPack; omega)
  apply EvalAll.letE (normBound_call dr hrange)
  intro v cr hv
  obtain ⟨heq,wi,hcr⟩ := hv
  subst v
  have e3 : normEnvBound C [input,zv,offset,ids] := normEnvBound_snoc e2 le_rfl wi
  have rc := linObjectEvalRead (P := P) e3 (slot := 0) rfl [0] rfl (by decide) (by decide) hC
  have rg := linObjectEvalRead (P := P) e3 (slot := 0) rfl [1] rfl (by decide) (by decide) hC
  have ro := linObjectEvalRead (P := P) e3 (slot := 2) rfl [] rfl (by decide) (by decide) hC
  have ri := linObjectEvalRead (P := P) e3 (slot := 3) rfl [] rfl (by decide) (by decide) hC
  have rm := linObjectEvalRead (P := P) e3 (slot := 0) rfl [0,4]
    (by change normReadVal ctx [4] = some (.list orders); exact horders) (by decide) (by decide) hC
  have rd := linObjectEvalLength rm.1 rm.2
  have dc := linObjectEvalPack4 (by omega : ctx.wt ≤ C + 1) (by omega : g.wt ≤ C + 1)
    (by omega : offset.wt ≤ C + 1) rd.1
    (rc.2.mono (by omega)) (rg.2.mono (by omega)) (ro.2.mono (by omega)) rd.2
  have dm := Det.mk2 dc ri.2
  have dm' : Det P [input,zv,offset,ids]
      (mk2 (mk4 (arg 0) (arg 1) (.var 2) (.length (.get (arg 0) (.nat 4)))) (.var 3))
      (.list [.list [ctx,g,offset,.nat orders.length],ids]) (10 * linObjectEvalPack C) := by
    refine dm.mono ?_
    have wc := wt_list4_le ctx g offset (.nat orders.length)
    have wa := wt_list2_le (.list [ctx,g,offset,.nat orders.length]) ids
    unfold linObjectEvalPack linObjectEvalAtom
    omega
  apply EvalAll.letE (normBound_call dm' hmap)
  intro v cm hv
  obtain ⟨heq,wc,hcm⟩ := hv
  subst v
  have e4 : normEnvBound C [input,zv,offset,ids,columns] := normEnvBound_snoc e3 le_rfl wc
  have rm := linObjectEvalRead (P := P) e4 (slot := 0) rfl [0,4]
    (by change normReadVal ctx [4] = some (.list orders); exact horders) (by decide) (by decide) hC
  have rd := linObjectEvalLength rm.1 rm.2
  have rcols := linObjectEvalRead (P := P) e4 (slot := 4) rfl [] rfl (by decide) (by decide) hC
  have dt := linObjectEvalPack2 rd.1 (by omega : columns.wt ≤ C + 1) rd.2 (rcols.2.mono (by omega))
  apply EvalAll.letE (normBound_call dt ht)
  intro v ct hv
  obtain ⟨heq,wmat,hct⟩ := hv
  subst v
  have e5 : normEnvBound C [input,zv,offset,ids,columns,matrix] := normEnvBound_snoc e4 le_rfl wmat
  have rmat := linObjectEvalRead (P := P) e5 (slot := 5) rfl [] rfl (by decide) (by decide) hC
  have ro := linObjectEvalRead (P := P) e5 (slot := 2) rfl [] rfl (by decide) (by decide) hC
  have dret := linObjectEvalPack2 (by omega : matrix.wt ≤ C + 1) (by omega : offset.wt ≤ C + 1)
    (rmat.2.mono (by omega)) (ro.2.mono (by omega))
  refine dret.post fun cost hc => ⟨rfl,?_⟩
  have wret := wt_list2_le matrix offset
  change _ ≤ 10000000000 * (C + 2) ^ 2
  unfold linObjectEvalPack at *
  omega

end GI.Impl
