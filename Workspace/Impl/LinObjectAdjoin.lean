module

public import Workspace.Impl.LinAppend
public import Workspace.Impl.LinObjectCorrectedList

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

def linObjectAdjoinF (append build reduce : ℕ) : Expr :=
  .letE (.call append (mk2 (arg 1) (.get (arg 2) (.nat 1))))
    (.letE (.call build (mk2 (arg 0) (.var 1))) (.call reduce (.var 2)))

def linObjectAdjoinFuns (b jmem : ℕ) : List Expr :=
  [linObjectAdjoinF (b+1) (b+4) (b+11)] ++ appendFuns (b+1) ++
    mkGroupFuns (b+4) ++ reduceFuns (b+11) jmem

theorem linObjectAdjoinFuns_length (b jmem : ℕ) : (linObjectAdjoinFuns b jmem).length = 16 := rfl

structure linObjectAdjoinAt (P : Program) (b jmem : ℕ) : Prop where
  entry : P.funs[b]? = some (linObjectAdjoinF (b+1) (b+4) (b+11))
  append : P.HasAt (b+1) (appendFuns (b+1))
  build : P.HasAt (b+4) (mkGroupFuns (b+4))
  reduce : P.HasAt (b+11) (reduceFuns (b+11) jmem)

theorem linObjectAdjoinAt_of {P : Program} {b jmem : ℕ}
    (h : P.HasAt b (linObjectAdjoinFuns b jmem)) : linObjectAdjoinAt P b jmem := by
  exact ⟨(h.block 0 rfl).single,h.block 1 rfl,h.block 4 rfl,h.block 11 rfl⟩

theorem linObjectAdjoin_comp {P : Program} {b jmem C : ℕ} (h : linObjectAdjoinAt P b jmem)
    (nv raw group pieces both built result : Val) (hC : 100 ≤ C)
    (hw : (Val.list [nv,raw,group]).wt ≤ C) (hp : normReadVal group [1] = some pieces)
    (ha : FunDet P (b+1) (.list [raw,pieces]) both C)
    (hb : FunDet P (b+4) (.list [nv,both]) built C)
    (hr : FunDet P (b+11) built result C) :
    FunDet P b (.list [nv,raw,group]) result (100000000*(C+2)^2) := by
  let input := Val.list [nv,raw,group]
  have e0 : normEnvBound C [input] := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    exact hw
  have rr := linObjectEvalRead (P:=P) e0 (slot:=0) rfl [1] rfl (by decide) (by decide) hC
  have rp := linObjectEvalRead (P:=P) e0 (slot:=0) rfl [2,1] hp (by decide) (by decide) hC
  have da := linObjectEvalPack2 (by omega : raw.wt ≤ C+1) (by omega : pieces.wt ≤ C+1)
    (rr.2.mono (by omega)) (rp.2.mono (by omega))
  have e1 : normEnvBound C [input,both] := normEnvBound_snoc e0 le_rfl ha.wt_lt.le
  have rn := linObjectEvalRead (P:=P) e1 (slot:=0) rfl [0] rfl (by decide) (by decide) hC
  have rb := linObjectEvalRead (P:=P) e1 (slot:=1) rfl [] rfl (by decide) (by decide) hC
  have db := linObjectEvalPack2 (by omega : nv.wt ≤ C+1) (by omega : both.wt ≤ C+1)
    (rn.2.mono (by omega)) (rb.2.mono (by omega))
  have dd := Det.letE (Det.call da ha) (Det.letE (Det.call db hb)
    (Det.call (Det.var' (P:=P) (env:=[input,both,built]) (i:=2) rfl) hr))
  apply FunDet.intro h.entry
  refine dd.mono ?_
  have wb := hb.wt_lt
  have wr := hr.wt_lt
  have hp' : C+2 ≤ (C+2)^2 := Nat.le_self_pow (by decide) _
  unfold linObjectEvalPack at *
  omega

end GI.Impl
