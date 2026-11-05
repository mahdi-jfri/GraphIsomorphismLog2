module

public import Workspace.Impl.LinObjectShiftOffsets
public import Workspace.Impl.LinObjectEvalBound

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linObjectShiftOffsets_comp {P : Program} {f move offsets C : ℕ}
    (he : P.funs[f]? = some (linObjectShiftOffsetsF move offsets))
    (A N Ps g moved : Val) (R : Val → Prop) (hC : 100 ≤ C)
    (hw : (Val.list [A,N,Ps,g]).wt ≤ C)
    (hm : FunDet P move (.list [g,Ps]) moved C)
    (ho : FunAll P offsets (.list [A,N,Ps,moved]) (fun out c => R out ∧ c ≤ C)) :
    FunAll P f (.list [A,N,Ps,g]) (fun out c => R out ∧ c ≤ 100000000 * (C + 2) ^ 2) := by
  let input := Val.list [A,N,Ps,g]
  have hp : C + 2 ≤ (C + 2) ^ 2 := Nat.le_self_pow (by decide) _
  have e0 : normEnvBound C [input] := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    exact hw
  have rg := linObjectEvalRead (P := P) e0 (slot := 0) rfl [3] rfl (by decide) (by decide) hC
  have rp := linObjectEvalRead (P := P) e0 (slot := 0) rfl [2] rfl (by decide) (by decide) hC
  have dm := linObjectEvalPack2 (by omega : g.wt ≤ C + 1) (by omega : Ps.wt ≤ C + 1)
    (rg.2.mono (by omega)) (rp.2.mono (by omega))
  apply FunAll.intro he
  apply EvalAll.letE (normBound_call dm hm)
  intro v cm hv
  obtain ⟨heq,wm,hcm⟩ := hv
  subst v
  have e1 : normEnvBound C [input,moved] := normEnvBound_snoc e0 le_rfl wm
  have rA := linObjectEvalRead (P := P) e1 (slot := 0) rfl [0] rfl (by decide) (by decide) hC
  have rN := linObjectEvalRead (P := P) e1 (slot := 0) rfl [1] rfl (by decide) (by decide) hC
  have rP := linObjectEvalRead (P := P) e1 (slot := 0) rfl [2] rfl (by decide) (by decide) hC
  have rM := linObjectEvalRead (P := P) e1 (slot := 1) rfl [] rfl (by decide) (by decide) hC
  have dout := linObjectEvalPack4 (by omega : A.wt ≤ C + 1) (by omega : N.wt ≤ C + 1)
    (by omega : Ps.wt ≤ C + 1) (by omega : moved.wt ≤ C + 1)
    (rA.2.mono (by omega)) (rN.2.mono (by omega)) (rP.2.mono (by omega)) (rM.2.mono (by omega))
  refine (normBound_call dout ho).mono fun out cost hout => ⟨hout.1,?_⟩
  have hc := hout.2.2
  have wo := hout.2.1
  change _ ≤ 100000000 * (C + 2) ^ 2
  unfold linObjectEvalPack at *
  omega

end GI.Impl
