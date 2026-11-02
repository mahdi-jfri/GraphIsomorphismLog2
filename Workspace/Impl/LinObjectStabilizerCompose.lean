import Workspace.Impl.LinObjectStabilizer

namespace GI.Impl
open GI.Cited GI.Lang

set_option maxHeartbeats 400000 in
theorem linObjectStabilizer_comp {P : Program} {f correct kernel adjoin C : ℕ}
    (he : P.funs[f]? = some (linObjectStabilizerF correct kernel adjoin))
    (ctx groups gs A nv : Val) (Rm Rk R : Val → Prop) (hC : 100 ≤ C)
    (hw : (Val.list [ctx,groups,gs]).wt ≤ C)
    (hA : normReadVal ctx [0] = some A) (hn : normReadVal ctx [0,0] = some nv)
    (hm : FunAll P correct (.list [ctx,gs]) (fun v c => Rm v ∧ c ≤ C))
    (hk : FunAll P kernel (.list [A,groups]) (fun v c => Rk v ∧ c ≤ C))
    (ha : ∀ raw, Rm raw → raw.wt ≤ C → ∀ kv, Rk kv → kv.wt ≤ C →
      FunAll P adjoin (.list [nv,raw,kv]) (fun out c => R out ∧ c ≤ C)) :
    FunAll P f (.list [ctx,groups,gs]) (fun out c => R out ∧ c ≤ 100000000*(C+2)^2) := by
  let input := Val.list [ctx,groups,gs]
  have e0 : normEnvBound C [input] := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    exact hw
  have rc := linObjectEvalRead (P:=P) e0 (slot:=0) rfl [0] rfl (by decide) (by decide) hC
  have rg := linObjectEvalRead (P:=P) e0 (slot:=0) rfl [2] rfl (by decide) (by decide) hC
  have dm := linObjectEvalPack2 (by omega : ctx.wt ≤ C+1) (by omega : gs.wt ≤ C+1)
    (rc.2.mono (by omega)) (rg.2.mono (by omega))
  apply FunAll.intro he
  apply EvalAll.letE (normBound_call dm hm)
  intro raw cm hm'
  obtain ⟨hmR,wm,hcm⟩ := hm'
  have e1 : normEnvBound C [input,raw] := normEnvBound_snoc e0 le_rfl wm
  have ra := linObjectEvalRead (P:=P) e1 (slot:=0) rfl [0,0] hA (by decide) (by decide) hC
  have rgp := linObjectEvalRead (P:=P) e1 (slot:=0) rfl [1] rfl (by decide) (by decide) hC
  have dk := linObjectEvalPack2 (by omega : A.wt ≤ C+1) (by omega : groups.wt ≤ C+1)
    (ra.2.mono (by omega)) (rgp.2.mono (by omega))
  apply EvalAll.letE (normBound_call dk hk)
  intro kv ck hk'
  obtain ⟨hkR,wk,hck⟩ := hk'
  have e2 : normEnvBound C [input,raw,kv] := normEnvBound_snoc e1 le_rfl wk
  have rn := linObjectEvalRead (P:=P) e2 (slot:=0) rfl [0,0,0] hn (by decide) (by decide) hC
  have rr := linObjectEvalRead (P:=P) e2 (slot:=1) rfl [] rfl (by decide) (by decide) hC
  have rk := linObjectEvalRead (P:=P) e2 (slot:=2) rfl [] rfl (by decide) (by decide) hC
  have da := linObjectEvalPack3 (by omega : nv.wt ≤ C+1) (by omega : raw.wt ≤ C+1)
    (by omega : kv.wt ≤ C+1) (rn.2.mono (by omega)) (rr.2.mono (by omega)) (rk.2.mono (by omega))
  refine (normBound_call da (ha raw hmR wm kv hkR wk)).mono fun out cost hout => ⟨hout.1,?_⟩
  have hp : C+2 ≤ (C+2)^2 := Nat.le_self_pow (by decide) _
  unfold linObjectEvalPack at *
  omega

end GI.Impl
