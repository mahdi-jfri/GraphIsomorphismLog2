module

public import Workspace.Impl.AggItemCiSojPR
public import Workspace.Impl.AggItemCiSojWt

@[expose] public section

/-! # Matching each canonical answer with its recorded target twist -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

/-- Map callback on `[[payload,answers],i]`. The payload fields are
`[q,alignment,fixing generators,lift context,twists]`. -/
def itcsRowF (pr : ℕ) : Expr :=
  let payload := Expr.get (arg 0) (.nat 0)
  .call pr (mk3 (.get payload (.nat 3)) (.get (.get (arg 0) (.nat 1)) (arg 1))
    (.get (.get payload (.nat 4)) (arg 1)))

/-- Each canonical answer is projected with precisely its query's twist. -/
theorem itcs_row_prog {Pg : Program} {f pr i Cr : ℕ} (qv av fv ctx u t out : Val)
    (twists answers : List Val) (hu : answers[i]?=some u) (ht : twists[i]?=some t)
    (hf : Pg.funs[f]? = some (itcsRowF pr))
    (hp : FunDet Pg pr (.list [ctx,u,t]) out Cr) :
    let payload := Val.list [qv,av,fv,ctx,.list twists]
    let inp := Val.list [.list [payload,.list answers],.nat i]
    FunDet Pg f inp out (50*(100*(inp.wt+Cr+10)+1)+Cr) := by
  dsimp only
  let payload : Val := .list [qv,av,fv,ctx,.list twists]
  let rowctx : Val := .list [payload,.list answers]
  let inp : Val := .list [rowctx,.nat i]
  let Bw := 100*(inp.wt+Cr+10)
  have budget : 10*inp.wt+10*Cr+100≤Bw := by dsimp only [Bw]; omega
  have wr : rowctx.wt≤ inp.wt := st_wt_mem (List.mem_cons_self ..)
  have wp : payload.wt≤ inp.wt := (st_wt_mem (List.mem_cons_self ..)).trans wr
  have wa : (Val.list answers).wt≤ inp.wt := (st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans wr
  have wc : ctx.wt≤ inp.wt := (st_wt_mem (by simp : ctx∈[qv,av,fv,ctx,.list twists])).trans wp
  have wt : (Val.list twists).wt≤ inp.wt := (st_wt_mem (by simp : Val.list twists∈[qv,av,fv,ctx,.list twists])).trans wp
  have wu : u.wt≤ inp.wt := (st_wt_mem (List.mem_of_getElem? hu)).trans wa
  have wtv : t.wt≤ inp.wt := (st_wt_mem (List.mem_of_getElem? ht)).trans wt
  have widx : (Val.nat i).wt≤ inp.wt := st_wt_mem (by simp : Val.nat i∈[rowctx,.nat i])
  have wo : out.wt≤Bw := (itcs_det_weight hp).trans (by omega)
  have warg : (Val.list [ctx,u,t]).wt≤Bw := (st_wt_list3 wc wu wtv).trans (by omega)
  have wi : inp.wt ≤ Bw := by omega
  let env : List Val := [inp]
  have a0 : StDC Pg env (arg 0) rowctx 3 0 Bw := StDC.arg rfl wi (by omega) (by omega)
  have a1 : StDC Pg env (arg 1) (.nat i) 3 0 Bw := StDC.arg rfl wi (by omega) (by omega)
  have pp := StDC.get a0 (StDC.nat 0 (by omega)) rfl (wp.trans (by omega))
  have cc := StDC.get pp (StDC.nat 3 (by omega)) rfl (wc.trans (by omega))
  have tt := StDC.get pp (StDC.nat 4 (by omega)) rfl (wt.trans (by omega))
  have aa := StDC.get a0 (StDC.nat 1 (by omega)) rfl (wa.trans (by omega))
  have uu := StDC.get aa a1 hu (wu.trans (by omega))
  have tv := StDC.get tt a1 ht (wtv.trans (by omega))
  have call := StDC.call (StDC.mk3 cc uu tv warg (by omega)) hp wo
  exact StDC.funDet hf call (by dsimp only [Bw,inp,rowctx,payload] at *; omega)

end GI.Impl
