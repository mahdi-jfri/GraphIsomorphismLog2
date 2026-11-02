import Workspace.Impl.AggItemCiSojSpec
import Workspace.Impl.AggItemCiSojWt

/-! # Returning a finished first-rectangle item with its empty kept value -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

/-- The item's finished-result encoding. The kept value remains empty. -/
def itcsResE (ovs : Expr) : Expr := mk2 (.nat 0) (mk3 .nil ovs .nil)

/-- A finished item with overcoset value `ovs`. -/
def itcsResV (ovs : Val) : Val := .list [.nat 0,.list [.list [],ovs,.list []]]

/-- The finished-result wrapper adds only a linear amount of weight. -/
theorem itcs_res_weight (ovs : Val) : (itcsResV ovs).wt≤4*ovs.wt+60 := by
  have hi:=wt_list3_le (.list []) ovs (.list [])
  have ho:=wt_list2_le (.nat 0) (.list [.list [],ovs,.list []])
  have hz:=wt_nat_le 0
  simp only [wt_list_nil] at hi
  dsimp only [itcsResV]
  omega

/-- Wrap any computed overcoset list in the exact finished-item encoding. -/
theorem itcs_res_dc {Pg : Program} {env : List Val} {e : Expr} {v : Val} {n C Bw : ℕ}
    (hv : StDC Pg env e v n C Bw) (hw : (itcsResV v).wt≤Bw) (h4 : 4≤Bw) :
    StDC Pg env (itcsResE e) (itcsResV v) (n+10) C Bw := by
  have hi : (Val.list [.list [],v,.list []]).wt≤Bw :=
    (st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans hw
  have body := StDC.mk2 (StDC.nat 0 (by omega))
    (StDC.mk3 (StDC.nil h4) hv (StDC.nil h4) hi h4) hw h4
  exact body.mono (by omega) (by omega)

/-- A concrete callee can be returned as a finished item. -/
theorem itcs_res_prog {Pg : Program} {f callee C : ℕ} {v out : Val}
    (hf : Pg.funs[f]? = some (itcsResE (.call callee (.var 0))))
    (hc : FunDet Pg callee v out C) :
    FunDet Pg f v (itcsResV out) (30*(100*(v.wt+C+100)+1)+C) := by
  let Bw:=100*(v.wt+C+100)
  have wo:=itcs_det_weight hc
  have wr : (itcsResV out).wt≤Bw := (itcs_res_weight out).trans (by dsimp only [Bw]; omega)
  have hcall:=StDC.call (StDC.var' (i:=0) (P:=Pg) (W:=Bw) (env:=[v]) rfl (by dsimp only [Bw]; omega))
    hc (by dsimp only [Bw]; omega)
  have body:=itcs_res_dc hcall wr (by dsimp only [Bw]; omega)
  exact StDC.funDet hf body (by dsimp only [Bw]; omega)

end GI.Impl
