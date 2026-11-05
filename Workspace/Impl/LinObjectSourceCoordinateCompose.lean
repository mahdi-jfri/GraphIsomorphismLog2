module

public import Workspace.Impl.LinObjectSourceCoordinate

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

set_option maxHeartbeats 400000 in
theorem linObjectSourceCoordinate_comp {P : Program} {f offsets row reduce C : ℕ}
    (he : P.funs[f]? = some (linObjectSourceCoordinateF offsets row reduce))
    (A N Ps V : Val) (ms : List Val) (src g answer : Val) (R : Val → Prop) (image : Val → Val)
    (hC : 100 ≤ C) (hw : (Val.list [.list [A,N,Ps,V,.list ms],src,g]).wt ≤ C)
    (ho : FunAll P offsets (.list [A,N,Ps,src,g]) (fun v c => R v ∧ c ≤ C))
    (hr : ∀ v, R v → FunDet P row (.list [.nat ms.length,v,V]) (image v) C)
    (hf : ∀ v, R v → FunDet P reduce (.list [image v,.list ms]) answer C) :
    FunDet P f (.list [.list [A,N,Ps,V,.list ms],src,g]) answer (100000000*(C+2)^2) := by
  let input := Val.list [.list [A,N,Ps,V,.list ms],src,g]
  have e0 : normEnvBound C [input] := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    exact hw
  have rA := linObjectEvalRead (P:=P) e0 (slot:=0) rfl [0,0] rfl (by decide) (by decide) hC
  have rN := linObjectEvalRead (P:=P) e0 (slot:=0) rfl [0,1] rfl (by decide) (by decide) hC
  have rP := linObjectEvalRead (P:=P) e0 (slot:=0) rfl [0,2] rfl (by decide) (by decide) hC
  have rS := linObjectEvalRead (P:=P) e0 (slot:=0) rfl [1] rfl (by decide) (by decide) hC
  have rG := linObjectEvalRead (P:=P) e0 (slot:=0) rfl [2] rfl (by decide) (by decide) hC
  have da := linObjectEvalPack5 (by omega : A.wt ≤ C+1) (by omega : N.wt ≤ C+1)
    (by omega : Ps.wt ≤ C+1) (by omega : src.wt ≤ C+1) (by omega : g.wt ≤ C+1)
    (rA.2.mono (by omega)) (rN.2.mono (by omega)) (rP.2.mono (by omega))
    (rS.2.mono (by omega)) (rG.2.mono (by omega))
  apply FunDet.intro he
  apply EvalAll.letE (normBound_call da ho)
  intro v co hv
  obtain ⟨hvR,wv,hco⟩ := hv
  have e1 : normEnvBound C [input,v] := normEnvBound_snoc e0 le_rfl wv
  have rm := linObjectEvalRead (P:=P) e1 (slot:=0) rfl [0,4] rfl (by decide) (by decide) hC
  have rd := linObjectEvalLength rm.1 rm.2
  have rv := linObjectEvalRead (P:=P) e1 (slot:=1) rfl [] rfl (by decide) (by decide) hC
  have rV := linObjectEvalRead (P:=P) e1 (slot:=0) rfl [0,3] rfl (by decide) (by decide) hC
  have db := linObjectEvalPack3 rd.1 (by omega : v.wt ≤ C+1) (by omega : V.wt ≤ C+1)
    rd.2 (rv.2.mono (by omega)) (rV.2.mono (by omega))
  have rr := hr v hvR
  apply EvalAll.letE (normBound_call db rr)
  intro iv cr hiv
  obtain ⟨rfl,wiv,hcr⟩ := hiv
  have e2 : normEnvBound C [input,v,image v] := normEnvBound_snoc e1 le_rfl wiv
  have ri := linObjectEvalRead (P:=P) e2 (slot:=2) rfl [] rfl (by decide) (by decide) hC
  have rms := linObjectEvalRead (P:=P) e2 (slot:=0) rfl [0,4] rfl (by decide) (by decide) hC
  have dc := linObjectEvalPack2 (by omega : (image v).wt ≤ C+1) (by omega : (Val.list ms).wt ≤ C+1)
    (ri.2.mono (by omega)) (rms.2.mono (by omega))
  refine (normBound_call dc (hf v hvR)).mono fun out cost hout => ⟨hout.1,?_⟩
  have hp : C+2 ≤ (C+2)^2 := Nat.le_self_pow (by decide) _
  unfold linObjectEvalPack at *
  omega

end GI.Impl
