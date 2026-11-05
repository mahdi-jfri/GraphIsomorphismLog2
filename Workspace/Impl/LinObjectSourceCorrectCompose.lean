module

public import Workspace.Impl.LinObjectSourceCorrect
public import Workspace.Impl.LinObjectCorrectOneCompose

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

set_option maxHeartbeats 400000 in
theorem linObjectSourceCorrect_comp {P : Program} {f offsets lift compose n C : ℕ}
    (he : P.funs[f]? = some (linObjectSourceCorrectF offsets lift compose))
    (A N Ps L src : Val) (g : Equiv.Perm (Fin n)) (S R : Val → Prop)
    (hC : 100 ≤ C) (hw : (Val.list [A,N,Ps,L,src,encPerm g]).wt ≤ C)
    (ho : FunAll P offsets (.list [A,N,Ps,src,encPerm g]) (fun w c => S w ∧ c ≤ C))
    (hl : ∀ w, S w → w.wt ≤ C → FunAll P lift (.list [A,L,w])
      (fun ans c => linObjectCorrectOneLiftResult g R ans ∧ c ≤ C))
    (hc : ∀ a : Equiv.Perm (Fin n),
      FunDet P compose (.list [encPerm g,encPerm a]) (encPerm (g*a)) C) :
    FunAll P f (.list [A,N,Ps,L,src,encPerm g]) (fun out c => R out ∧ c ≤ 100000000 * (C+2)^2) := by
  let input := Val.list [A,N,Ps,L,src,encPerm g]
  have e0 : normEnvBound C [input] := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    exact hw
  have rA := linObjectEvalRead (P:=P) e0 (slot:=0) rfl [0] rfl (by decide) (by decide) hC
  have rN := linObjectEvalRead (P:=P) e0 (slot:=0) rfl [1] rfl (by decide) (by decide) hC
  have rP := linObjectEvalRead (P:=P) e0 (slot:=0) rfl [2] rfl (by decide) (by decide) hC
  have rG := linObjectEvalRead (P:=P) e0 (slot:=0) rfl [5] rfl (by decide) (by decide) hC
  have rS := linObjectEvalRead (P:=P) e0 (slot:=0) rfl [4] rfl (by decide) (by decide) hC
  have doff := linObjectEvalPack5 (by omega : A.wt ≤ C+1) (by omega : N.wt ≤ C+1)
    (by omega : Ps.wt ≤ C+1) (by omega : src.wt ≤ C+1) (by omega : (encPerm g).wt ≤ C+1)
    (rA.2.mono (by omega)) (rN.2.mono (by omega)) (rP.2.mono (by omega)) (rS.2.mono (by omega)) (rG.2.mono (by omega))
  apply FunAll.intro he
  apply EvalAll.letE (normBound_call doff ho)
  intro w cw hw'
  obtain ⟨hs,ww,hcw⟩ := hw'
  have e1 : normEnvBound C [input,w] := normEnvBound_snoc e0 le_rfl ww
  have rA1 := linObjectEvalRead (P:=P) e1 (slot:=0) rfl [0] rfl (by decide) (by decide) hC
  have rL1 := linObjectEvalRead (P:=P) e1 (slot:=0) rfl [3] rfl (by decide) (by decide) hC
  have rW1 := linObjectEvalRead (P:=P) e1 (slot:=1) rfl [] rfl (by decide) (by decide) hC
  have dlift := linObjectEvalPack3 (by omega : A.wt ≤ C+1) (by omega : L.wt ≤ C+1)
    (by omega : w.wt ≤ C+1) (rA1.2.mono (by omega)) (rL1.2.mono (by omega)) (rW1.2.mono (by omega))
  apply EvalAll.letE (normBound_call dlift (hl w hs ww))
  intro ans ca ha
  obtain ⟨hans,wa,hca⟩ := ha
  rcases hans with ⟨rfl,hr⟩ | ⟨a,rfl,hr⟩
  · have dt := Det.isNat (Det.var' (P:=P) (env:=[input,w,.nat 0]) (i:=2) rfl)
    have dd := Det.ite_pos dt (by decide : 1 ≠ 0) (Det.nat 0)
      (e := .call compose (mk2 (arg 5) (.get (.var 2) (.nat 1))))
    refine dd.post fun cost hcost => ⟨hr,?_⟩
    have hwi : input.wt ≤ C := hw
    have hp : C+2 ≤ (C+2)^2 := Nat.le_self_pow (by decide) _
    unfold linObjectEvalPack at *
    omega
  · have e2 : normEnvBound C [input,w,.list [.nat 1,encPerm a]] := normEnvBound_snoc e1 le_rfl wa
    have rg := linObjectEvalRead (P:=P) e2 (slot:=0) rfl [5] rfl (by decide) (by decide) hC
    have ra := linObjectEvalRead (P:=P) e2 (slot:=2) rfl [1] rfl (by decide) (by decide) hC
    have darg := linObjectEvalPack2 (by omega : (encPerm g).wt ≤ C+1)
      (by omega : (encPerm a).wt ≤ C+1) (rg.2.mono (by omega)) (ra.2.mono (by omega))
    have wout := (hc a).wt_lt
    have dt := Det.isNat (Det.var' (P:=P) (env:=[input,w,.list [.nat 1,encPerm a]]) (i:=2) rfl)
    have dd := Det.ite_zero dt (Det.call darg (hc a)) (t:=.nat 0)
    refine dd.post fun cost hcost => ⟨hr,?_⟩
    have hp : C+2 ≤ (C+2)^2 := Nat.le_self_pow (by decide) _
    unfold linObjectEvalPack at *
    omega

end GI.Impl
