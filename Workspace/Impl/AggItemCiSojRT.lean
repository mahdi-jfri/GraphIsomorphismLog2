module

public import Workspace.Impl.AggItemCiSojRB
public import Workspace.Impl.GenCls

@[expose] public section

/-! # Projecting the complete list of canonical rectangle answers -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

/-- On `[payload,answers]`, index the answers and project each with its recorded twist. -/
def itcsRowsF (rng mp : ℕ) : Expr :=
  .letE (.call rng (.length (arg 1))) (.call mp (mk2 (.var 0) (.var 1)))

/-- Common callback budget in a projection map. -/
def itcsRowsBW (ctx : Val) (n Cr : ℕ) : ℕ :=
  100*(10*(ctx.wt+n+10)+Cr+10)

/-- Bound for the projection map itself. -/
def itcsRowsMC (ctx : Val) (n Cr : ℕ) : ℕ :=
  n*(50*(itcsRowsBW ctx n Cr+1)+Cr)+mapK*(n+1)*
    (2*ctx.wt+8*(n+1)^2+6+(n*(2*Cr+1)+4)+1)

/-- The complete projection-list constructor cost. -/
def itcsRowsC (ctx : Val) (n Cr : ℕ) : ℕ :=
  50*(100*(itcsRowsBW ctx n Cr+n*(2*Cr+1)+4*(n+1)^2+ctx.wt+100)+1)+
    7000*(n+1)^3+itcsRowsMC ctx n Cr

set_option maxHeartbeats 400000 in
/-- Both the range and the map are actual installed programs, and every row is
paired with the corresponding recorded target twist. -/
theorem itcs_rows_prog {Pg : Program} {f rng mp cb pr Cr : ℕ}
    (hf : Pg.funs[f]? = some (itcsRowsF rng mp)) (hr : Pg.HasAt rng (rangeFuns rng))
    (hm : Pg.HasAt mp (mapFuns mp cb)) (hb : Pg.funs[cb]? = some (itcsRowF pr))
    (qv av fv ctx : Val) (twists answers : List Val) (ht : twists.length=answers.length)
    (F : Fin answers.length → Val)
    (hp : ∀ i : Fin answers.length,FunDet Pg pr (.list [ctx,answers[i],twists[i.val]'(by omega)]) (F i) Cr) :
    let payload := Val.list [qv,av,fv,ctx,.list twists]
    let rowctx := Val.list [payload,.list answers]
    FunDet Pg f rowctx (.list ((List.finRange answers.length).map F)) (itcsRowsC rowctx answers.length Cr) := by
  dsimp only
  let payload : Val := .list [qv,av,fv,ctx,.list twists]
  let rowctx : Val := .list [payload,.list answers]
  let n := answers.length
  let Cb := 50*(itcsRowsBW rowctx n Cr+1)+Cr
  have hcb (i : Fin answers.length) :
      FunDet Pg cb (.list [rowctx,.nat i]) (F i) Cb := by
    have hh := itcs_row_prog qv av fv ctx answers[i] (twists[i.val]'(by omega)) (F i)
      twists answers (List.getElem?_eq_getElem i.isLt) (List.getElem?_eq_getElem (by omega)) hb (hp i)
    have hw : (Val.list [rowctx,.nat i]).wt≤10*(rowctx.wt+n+10) := by
      have h:=wt_list2_le rowctx (.nat i)
      have hi:=wt_nat_le (i:ℕ)
      have hin:=i.isLt
      omega
    exact hh.mono (by dsimp only [Cb,itcsRowsBW,n,rowctx,payload] at *; omega)
  have mapped := mapList_spec hm (List.finRange answers.length) (fun i:Fin answers.length=>Val.nat i.val) F
    (c:=rowctx) (B:=Cb) (fun a _ b _ h=>by cases Fin.ext (Val.nat.inj h); rfl)
    (fun i _=>hcb i)
  have wout : (Val.list ((List.finRange answers.length).map F)).wt≤n*(2*Cr+1)+4 := by
    have hh:=wt_list_map_le (List.finRange answers.length) F (W:=Cr)
      (fun i _=>itcs_det_weight (hp i))
    simpa only [List.length_finRange] using hh
  have wr := wt_range_le n
  have wmap := wt_list2_le rowctx (natList (List.range n))
  have mapCall : FunDet Pg mp (.list [rowctx,natList (List.range n)])
      (.list ((List.finRange answers.length).map F)) (itcsRowsMC rowctx n Cr) := by
    rw [it_range_eq]
    refine mapped.mono ?_
    simp only [List.length_finRange]
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    rw [it_range_eq] at wr wmap
    dsimp only [n] at *
    omega
  let Bw := 100*(itcsRowsBW rowctx n Cr+n*(2*Cr+1)+4*(n+1)^2+rowctx.wt+100)
  have budget : 10*rowctx.wt+10*(n*(2*Cr+1))+40*(n+1)^2+1000≤Bw := by
    dsimp only [Bw]; omega
  have hn : n≤(n+1)^2 := (Nat.le_add_right n 1).trans (Nat.le_self_pow (by omega) _)
  have hs : (Val.list answers).wt≤rowctx.wt := st_wt_mem (by simp : Val.list answers∈[payload,.list answers])
  have wi : rowctx.wt ≤ Bw := by omega
  have ga : StDC Pg [rowctx] (arg 1) (.list answers) 3 0 Bw :=
    StDC.arg rfl wi (by omega) (hs.trans (by omega))
  have gl := StDC.length ga (by change n+2≤Bw; omega)
  have rg := StDC.call gl (range_det hr n) (wr.trans (by omega))
  have r1 : StDC Pg [rowctx,natList (List.range n)] (.var 1) (natList (List.range n)) 1 0 Bw :=
    StDC.var' rfl (wr.trans (by omega))
  have c0 : StDC Pg [rowctx,natList (List.range n)] (.var 0) rowctx 1 0 Bw := StDC.var' rfl (by omega)
  have mc := StDC.call (StDC.mk2 c0 r1 (by omega) (by omega)) mapCall (wout.trans (by omega))
  have body := StDC.letE rg mc (wout.trans (by omega))
  clear budget hn hs ga gl rg r1 c0 mc wmap wr wout mapped hcb mapCall
  exact StDC.funDet hf body (by unfold itcsRowsC; dsimp only [Bw,n,rowctx,payload] at *; omega)

end GI.Impl
