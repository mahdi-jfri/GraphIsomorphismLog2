import Workspace.Impl.LinObjectAffineItem

namespace GI.Impl
open GI.Cited GI.Lang

theorem linObjectAffineItem_comp {P : Program} {f matrix inv C : ℕ}
    (he : P.funs[f]? = some (linObjectAffineItemF matrix inv))
    (ctx g gi M u Mi ui : Val) (hC : 100 ≤ C) (hw : (Val.list [ctx,g]).wt ≤ C)
    (hm : FunDet P matrix (.list [ctx,g]) (.list [M,u]) C)
    (hi : FunDet P inv g gi C)
    (hmi : FunDet P matrix (.list [ctx,gi]) (.list [Mi,ui]) C) :
    FunDet P f (.list [ctx,g]) (.list [M,u,Mi,ui]) (100000000 * (C + 2) ^ 2) := by
  let input := Val.list [ctx,g]
  have hw' : input.wt ≤ C := hw
  have hp : C + 2 ≤ (C + 2) ^ 2 := Nat.le_self_pow (by decide) _
  have e0 : normEnvBound C [input] := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    exact hw
  have din : Det P [input] (.var 0) input (linObjectEvalPack C) := by
    refine (Det.var' rfl).mono ?_
    unfold linObjectEvalPack
    omega
  apply FunAll.intro he
  apply EvalAll.letE (normBound_call din hm)
  intro v cm hv
  obtain ⟨rfl,wm,hcm⟩ := hv
  have e1 : normEnvBound C [input,.list [M,u]] := normEnvBound_snoc e0 le_rfl wm
  have rg := linObjectEvalRead (P := P) e1 (slot := 0) rfl [1] rfl (by decide) (by decide) hC
  have dg := rg.2.mono (show linObjectEvalAtom C ≤ linObjectEvalPack C by
    unfold linObjectEvalAtom linObjectEvalPack; omega)
  apply EvalAll.letE (normBound_call dg hi)
  intro v ci hv
  obtain ⟨heq,wi,hci⟩ := hv
  subst v
  have e2 : normEnvBound C [input,.list [M,u],gi] := normEnvBound_snoc e1 le_rfl wi
  have rc := linObjectEvalRead (P := P) e2 (slot := 0) rfl [0] rfl (by decide) (by decide) hC
  have ri := linObjectEvalRead (P := P) e2 (slot := 2) rfl [] rfl (by decide) (by decide) hC
  have dm := linObjectEvalPack2 (by omega : ctx.wt ≤ C + 1) (by omega : gi.wt ≤ C + 1)
    (rc.2.mono (by omega)) (ri.2.mono (by omega))
  apply EvalAll.letE (normBound_call dm hmi)
  intro v cmi hv
  obtain ⟨rfl,wmi,hcmi⟩ := hv
  have e3 : normEnvBound C [input,.list [M,u],gi,.list [Mi,ui]] := normEnvBound_snoc e2 le_rfl wmi
  have rM := linObjectEvalRead (P := P) e3 (slot := 1) rfl [0] rfl (by decide) (by decide) hC
  have ru := linObjectEvalRead (P := P) e3 (slot := 1) rfl [1] rfl (by decide) (by decide) hC
  have rMi := linObjectEvalRead (P := P) e3 (slot := 3) rfl [0] rfl (by decide) (by decide) hC
  have rui := linObjectEvalRead (P := P) e3 (slot := 3) rfl [1] rfl (by decide) (by decide) hC
  have dout := linObjectEvalPack4 (by omega : M.wt ≤ C + 1) (by omega : u.wt ≤ C + 1)
    (by omega : Mi.wt ≤ C + 1) (by omega : ui.wt ≤ C + 1)
    (rM.2.mono (by omega)) (ru.2.mono (by omega)) (rMi.2.mono (by omega)) (rui.2.mono (by omega))
  refine dout.post fun cost hc => ⟨rfl,?_⟩
  have wout := wt_list4_le M u Mi ui
  change _ ≤ 100000000 * (C + 2) ^ 2
  unfold linObjectEvalPack at *
  omega

end GI.Impl
