module

public import Workspace.Impl.LinObjectEvalBound

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

/-- Composition of the seven concrete stages. The bound C is supplied by the
proved polynomial bounds of those stages, and is independent of their choices. -/
theorem linObjectAffineEval_comp {P : Program} {f lift build inv move offsets row reduce C : ℕ}
    (he : P.funs[f]? = some (linObjectAffineEvalF lift build inv move offsets row reduce))
    (A N Ps V : Val) (ms : List Val) (g gi x z built moved answer : Val)
    (R : Val → Prop) (image : Val → Val)
    (hC : 100 ≤ C)
    (hw : (Val.list [.list [A,N,Ps,V,.list ms],g,x]).wt ≤ C)
    (hlift : FunDet P lift (.list [.nat ms.length,V,x]) z C)
    (hbuild : FunDet P build (.list [A,Ps,z]) built C)
    (hinv : FunDet P inv g gi C)
    (hmove : FunDet P move (.list [gi,built]) moved C)
    (hoffsets : FunAll P offsets (.list [A,N,Ps,moved]) (fun w c => R w ∧ c ≤ C))
    (hrow : ∀ w, R w → FunDet P row (.list [.nat ms.length,w,V]) (image w) C)
    (hreduce : ∀ w, R w → FunDet P reduce (.list [image w,.list ms]) answer C) :
    FunDet P f (.list [.list [A,N,Ps,V,.list ms],g,x]) answer (100000000 * (C + 2) ^ 2) := by
  let input := Val.list [.list [A,N,Ps,V,.list ms],g,x]
  have e0 : normEnvBound C [input] := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    exact hw
  have rA := linObjectEvalRead (P := P) e0 (slot := 0) rfl [0,0] rfl (by decide) (by decide) hC
  have rV := linObjectEvalRead (P := P) e0 (slot := 0) rfl [0,3] rfl (by decide) (by decide) hC
  have rx := linObjectEvalRead (P := P) e0 (slot := 0) rfl [2] rfl (by decide) (by decide) hC
  have rm := linObjectEvalRead (P := P) e0 (slot := 0) rfl [0,4] rfl (by decide) (by decide) hC
  have rd := linObjectEvalLength rm.1 rm.2
  have dl := linObjectEvalPack3 rd.1 (by omega : V.wt ≤ C + 1) (by omega : x.wt ≤ C + 1)
    rd.2 (rV.2.mono (by omega)) (rx.2.mono (by omega))
  apply FunAll.intro he
  apply EvalAll.letE (normBound_call dl hlift)
  intro v cl hv
  obtain ⟨heq,wz,hcl⟩ := hv
  subst v
  have e1 : normEnvBound C [input,z] := normEnvBound_snoc e0 le_rfl wz
  have rA := linObjectEvalRead (P := P) e1 (slot := 0) rfl [0,0] rfl (by decide) (by decide) hC
  have rPs := linObjectEvalRead (P := P) e1 (slot := 0) rfl [0,2] rfl (by decide) (by decide) hC
  have rz := linObjectEvalRead (P := P) e1 (slot := 1) rfl [] rfl (by decide) (by decide) hC
  have db := linObjectEvalPack3 (by omega : A.wt ≤ C + 1) (by omega : Ps.wt ≤ C + 1)
    (by omega : z.wt ≤ C + 1) (rA.2.mono (by omega)) (rPs.2.mono (by omega)) (rz.2.mono (by omega))
  apply EvalAll.letE (normBound_call db hbuild)
  intro v cb hv
  obtain ⟨heq,wb,hcb⟩ := hv
  subst v
  have e2 : normEnvBound C [input,z,built] := normEnvBound_snoc e1 le_rfl wb
  have rg := linObjectEvalRead (P := P) e2 (slot := 0) rfl [1] rfl (by decide) (by decide) hC
  have dg := rg.2.mono (show linObjectEvalAtom C ≤ linObjectEvalPack C by
    unfold linObjectEvalAtom linObjectEvalPack; omega)
  apply EvalAll.letE (normBound_call dg hinv)
  intro v cg hv
  obtain ⟨heq,wg,hcg⟩ := hv
  subst v
  have e3 : normEnvBound C [input,z,built,gi] := normEnvBound_snoc e2 le_rfl wg
  have ri := linObjectEvalRead (P := P) e3 (slot := 3) rfl [] rfl (by decide) (by decide) hC
  have rb := linObjectEvalRead (P := P) e3 (slot := 2) rfl [] rfl (by decide) (by decide) hC
  have dm := linObjectEvalPack2 (by omega : gi.wt ≤ C + 1) (by omega : built.wt ≤ C + 1)
    (ri.2.mono (by omega)) (rb.2.mono (by omega))
  apply EvalAll.letE (normBound_call dm hmove)
  intro v cm hv
  obtain ⟨heq,wm,hcm⟩ := hv
  subst v
  have e4 : normEnvBound C [input,z,built,gi,moved] := normEnvBound_snoc e3 le_rfl wm
  have rA := linObjectEvalRead (P := P) e4 (slot := 0) rfl [0,0] rfl (by decide) (by decide) hC
  have rN := linObjectEvalRead (P := P) e4 (slot := 0) rfl [0,1] rfl (by decide) (by decide) hC
  have rPs := linObjectEvalRead (P := P) e4 (slot := 0) rfl [0,2] rfl (by decide) (by decide) hC
  have rm := linObjectEvalRead (P := P) e4 (slot := 4) rfl [] rfl (by decide) (by decide) hC
  have doff := linObjectEvalPack4 (by omega : A.wt ≤ C + 1) (by omega : N.wt ≤ C + 1)
    (by omega : Ps.wt ≤ C + 1) (by omega : moved.wt ≤ C + 1)
    (rA.2.mono (by omega)) (rN.2.mono (by omega)) (rPs.2.mono (by omega)) (rm.2.mono (by omega))
  apply EvalAll.letE (normBound_call doff hoffsets)
  intro w co hw'
  obtain ⟨hR,ww,hco⟩ := hw'
  have e5 : normEnvBound C [input,z,built,gi,moved,w] := normEnvBound_snoc e4 le_rfl ww
  have rmod := linObjectEvalRead (P := P) e5 (slot := 0) rfl [0,4] rfl (by decide) (by decide) hC
  have rd := linObjectEvalLength rmod.1 rmod.2
  have rw' := linObjectEvalRead (P := P) e5 (slot := 5) rfl [] rfl (by decide) (by decide) hC
  have rV := linObjectEvalRead (P := P) e5 (slot := 0) rfl [0,3] rfl (by decide) (by decide) hC
  have dr := linObjectEvalPack3 rd.1 (by omega : w.wt ≤ C + 1) (by omega : V.wt ≤ C + 1)
    rd.2 (rw'.2.mono (by omega)) (rV.2.mono (by omega))
  apply EvalAll.letE (normBound_call dr (hrow w hR))
  intro v cr hv
  obtain ⟨rfl,wr,hcr⟩ := hv
  have e6 : normEnvBound C [input,z,built,gi,moved,w,image w] := normEnvBound_snoc e5 le_rfl wr
  have rrow := linObjectEvalRead (P := P) e6 (slot := 6) rfl [] rfl (by decide) (by decide) hC
  have rmod := linObjectEvalRead (P := P) e6 (slot := 0) rfl [0,4] rfl (by decide) (by decide) hC
  have df := linObjectEvalPack2 (by omega : (image w).wt ≤ C + 1) (by omega : (Val.list ms).wt ≤ C + 1)
    (rrow.2.mono (by omega)) (rmod.2.mono (by omega))
  have wa := (hreduce w hR).wt_lt.le
  refine (Det.call df (hreduce w hR)).post fun cost hc => ⟨rfl, ?_⟩
  have hcost := hc
  have hp : C + 2 ≤ (C + 2) ^ 2 := Nat.le_self_pow (by decide) _
  change _ ≤ 100000000 * (C + 2) ^ 2
  unfold linObjectEvalPack at *
  omega

end GI.Impl
