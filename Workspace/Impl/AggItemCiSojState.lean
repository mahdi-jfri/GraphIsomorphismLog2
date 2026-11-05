module

public import Workspace.Impl.AggItemCiSojQV

@[expose] public section

/-!
# Retaining the parent fields in the inherited query encoding

Read the physical degree, hierarchy, and phase size from the canonical parent.
The four freshly computed group/domain/color values replace the corresponding
fields, and the row, floor, and local-size fields become `[], 0, 2`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

/-- On `[parent state,group,domain,source,target]`, encode the inherited query. -/
def itcsStateF : Expr :=
  itcsMk10 (.get (arg 0) (.nat 0)) (arg 1) (arg 2) (arg 3) (arg 4)
    (.get (arg 0) (.nat 5)) .nil (.nat 0) (.nat 2) (.get (arg 0) (.nat 9))

/-- The exact inherited-state constructor, with all argument and result weights
bounded by the actual encoded input. -/
theorem itcs_state_prog {Pg : Program} {f k N : ℕ} (sv : List Val) (gv dv xv yv hv : Val)
    (hk : sv[0]?=some (.nat k)) (hh : sv[5]?=some hv) (hN : sv[9]?=some (.nat N))
    (hf : Pg.funs[f]? = some itcsStateF) :
    let inp:=Val.list [.list sv,gv,dv,xv,yv]
    FunDet Pg f inp (winVal' k gv dv xv yv hv N) (100*(100*(inp.wt+100)+1)) := by
  dsimp only
  let inp : Val:=.list [.list sv,gv,dv,xv,yv]
  let Bw:=100*(inp.wt+100)
  have budget : 50*inp.wt+1000≤ Bw := by dsimp only [Bw]; omega
  have ws : (Val.list sv).wt≤ inp.wt := st_wt_mem (List.mem_cons_self ..)
  have wk : (Val.nat k).wt≤ inp.wt := (st_wt_mem (List.mem_of_getElem? hk)).trans ws
  have wh : hv.wt≤ inp.wt := (st_wt_mem (List.mem_of_getElem? hh)).trans ws
  have wN : (Val.nat N).wt≤ inp.wt := (st_wt_mem (List.mem_of_getElem? hN)).trans ws
  have wg : gv.wt≤ inp.wt := st_wt_mem (by simp : gv∈[.list sv,gv,dv,xv,yv])
  have wd : dv.wt≤ inp.wt := st_wt_mem (by simp : dv∈[.list sv,gv,dv,xv,yv])
  have wx : xv.wt≤ inp.wt := st_wt_mem (by simp : xv∈[.list sv,gv,dv,xv,yv])
  have wy : yv.wt≤ inp.wt := st_wt_mem (by simp : yv∈[.list sv,gv,dv,xv,yv])
  have wo : (winVal' k gv dv xv yv hv N).wt≤ Bw := by
    have h:=wt_list_map_le [Val.nat k,gv,dv,xv,yv,hv,.list [],.nat 0,.nat 2,.nat N] id
      (W:=inp.wt+10) (by
        intro v hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [id_eq,wt_list_nil] <;>
          first | omega | exact (wt_nat_le _).trans (by omega))
    simp only [List.map_id,List.length_cons,List.length_nil] at h
    exact h.trans (by omega)
  have wi : inp.wt ≤ Bw := by omega
  have get {i : ℕ} {v : Val} (hi:[Val.list sv,gv,dv,xv,yv][i]?=some v) (hii:i+2≤ Bw) :
      StDC Pg [inp] (arg i) v 3 0 Bw :=
    StDC.arg hi wi hii ((st_wt_mem (List.mem_of_getElem? hi)).trans wi)
  have parent:=get (i:=0) rfl (by omega)
  have pk:=StDC.get parent (StDC.nat 0 (by omega)) hk (wk.trans (by omega))
  have ph:=StDC.get parent (StDC.nat 5 (by omega)) hh (wh.trans (by omega))
  have pN:=StDC.get parent (StDC.nat 9 (by omega)) hN (wN.trans (by omega))
  have body:=itcs_mk10 pk (get (i:=1) rfl (by omega)) (get (i:=2) rfl (by omega))
    (get (i:=3) rfl (by omega)) (get (i:=4) rfl (by omega)) ph (StDC.nil (by omega))
    (StDC.nat 0 (by omega)) (StDC.nat 2 (by omega)) pN wo (by omega)
  exact StDC.funDet hf body (by dsimp only [Bw,inp] at *; omega)

end GI.Impl
