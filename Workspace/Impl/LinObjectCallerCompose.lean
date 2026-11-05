module

public import Workspace.Impl.LinObjectAffineCaller
public import Workspace.Impl.LinObjectEvalBound

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linObjectAffineCaller_comp {P : Program} {f slice records affine C : ℕ}
    (he : P.funs[f]? = some (linObjectAffineCallerF slice records affine))
    (ctx degree one orders v w rec : Val) (raw : List Val) (R : Val → Prop)
    (horders : normReadVal ctx [4] = some orders) (hC : 100 ≤ C)
    (hw : (Val.list [ctx,.list [degree,.list (one :: raw)],v,w]).wt ≤ C)
    (hs : FunDet P slice (.list [.nat 1,.nat raw.length,.list (one :: raw)]) (.list raw) C)
    (hr : FunDet P records (.list [ctx,.list raw]) rec C)
    (ha : FunAll P affine (.list [.list [degree,.list (one :: raw)],orders,rec,v,w]) (fun out c => R out ∧ c ≤ C)) :
    FunAll P f (.list [ctx,.list [degree,.list (one :: raw)],v,w])
      (fun out c => R out ∧ c ≤ 10000000000 * (C + 2) ^ 2) := by
  let input := Val.list [ctx,.list [degree,.list (one :: raw)],v,w]
  have hp : C + 2 ≤ (C + 2) ^ 2 := Nat.le_self_pow (by decide) _
  have e0 : normEnvBound C [input] := by
    intro u hu
    simp only [List.mem_singleton] at hu
    subst u
    exact hw
  have rs := linObjectEvalRead (P := P) e0 (slot := 0) rfl [1,1] rfl (by decide) (by decide) hC
  have hlen := length_lt_wt_list (one :: raw)
  simp only [List.length_cons] at hlen
  have hnn := wt_nat_le raw.length
  have dc := Det.arith' (op := .sub) (Det.length rs.2) (Det.nat 1)
    (z := raw.length) (by simp [GI.Machine.BinOp.eval])
  have dc' := dc.mono (show _ ≤ 2 * linObjectEvalAtom C by
    simp only [List.length_cons]
    unfold linObjectEvalAtom
    omega)
  have d1 : Det P [input] (.nat 1) (.nat 1) (2 * linObjectEvalAtom C) := by
    refine (Det.nat 1).mono ?_
    unfold linObjectEvalAtom
    omega
  have wn1 : (Val.nat 1).wt = 3 := rfl
  have ds := linObjectEvalPack3 (by omega : (Val.nat 1).wt ≤ C + 1)
    (by omega : (Val.nat raw.length).wt ≤ C + 1) (by omega : (Val.list (one :: raw)).wt ≤ C + 1)
    d1 dc' (rs.2.mono (by omega))
  apply FunAll.intro he
  apply EvalAll.letE (normBound_call ds hs)
  intro u cs hu
  obtain ⟨rfl,ws,hcs⟩ := hu
  have e1 : normEnvBound C [input,.list raw] := normEnvBound_snoc e0 le_rfl ws
  have rc := linObjectEvalRead (P := P) e1 (slot := 0) rfl [0] rfl (by decide) (by decide) hC
  have rr := linObjectEvalRead (P := P) e1 (slot := 1) rfl [] rfl (by decide) (by decide) hC
  have dr := linObjectEvalPack2 (by omega : ctx.wt ≤ C + 1) (by omega : (Val.list raw).wt ≤ C + 1)
    (rc.2.mono (by omega)) (rr.2.mono (by omega))
  apply EvalAll.letE (normBound_call dr hr)
  intro u cr hu
  obtain ⟨heq,wr,hcr⟩ := hu
  subst u
  have e2 : normEnvBound C [input,.list raw,rec] := normEnvBound_snoc e1 le_rfl wr
  have rg := linObjectEvalRead (P := P) e2 (slot := 0) rfl [1] rfl (by decide) (by decide) hC
  have ro := linObjectEvalRead (P := P) e2 (slot := 0) rfl [0,4]
    (by change normReadVal ctx [4] = some orders; exact horders) (by decide) (by decide) hC
  have rr := linObjectEvalRead (P := P) e2 (slot := 2) rfl [] rfl (by decide) (by decide) hC
  have rv := linObjectEvalRead (P := P) e2 (slot := 0) rfl [2] rfl (by decide) (by decide) hC
  have rw' := linObjectEvalRead (P := P) e2 (slot := 0) rfl [3] rfl (by decide) (by decide) hC
  have d4 := linObjectEvalPack4 (by omega : (Val.list [degree,.list (one :: raw)]).wt ≤ C + 1)
    (by omega : orders.wt ≤ C + 1) (by omega : rec.wt ≤ C + 1) (by omega : v.wt ≤ C + 1)
    (rg.2.mono (by omega)) (ro.2.mono (by omega)) (rr.2.mono (by omega)) (rv.2.mono (by omega))
  have da := Det.snoc d4 rw'.2
  have da' := da.mono (show _ ≤ 10 * linObjectEvalPack C by
    have w4 := wt_list4_le (.list [degree,.list (one :: raw)]) orders rec v
    have w5 := wt_list_le [.list [degree,.list (one :: raw)],orders,rec,v,w]
    simp only [List.cons_append,List.nil_append]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at w5
    unfold linObjectEvalPack linObjectEvalAtom
    omega)
  refine (normBound_call da' ha).mono fun out cost hout => ⟨hout.1,?_⟩
  have hc := hout.2.2
  have wo := hout.2.1
  change _ ≤ 10000000000 * (C + 2) ^ 2
  unfold linObjectEvalPack at *
  omega

end GI.Impl
