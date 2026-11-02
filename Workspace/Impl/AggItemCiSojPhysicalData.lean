import Workspace.Impl.AggItemCiSojColorsState
import Workspace.Impl.AggItemCiSojGP
import Workspace.Impl.AggItemCiSojDW
import Workspace.Impl.AggItemCiSojLC

/-! # Building the physical group, inherited domain, and stored projection context -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

/-- Input `[parent,q,graph generators,cells]`. Return the physical group,
inherited domain, and swapped graph context used for processing answers. -/
def itcsPhysicalDataF (gp lc rng dom : ℕ) : Expr :=
  let k := Expr.get (arg 0) (.nat 0)
  .letE (.call gp (mk2 k (arg 2)))
    (.letE (.call lc (mk2 (mk2 k (arg 1)) (arg 2)))
      (.letE (.call rng k)
        (.letE (.call dom (mk2 (mk2 (.get (arg 0) (.nat 2)) (arg 3)) (.var 3)))
          (mk3 (.var 1) (.var 4) (.var 2)))))

/-- A scalar bound for this fixed sequence of encoding calls. -/
def itcsPhysicalDataC (W Cg Cl Cr Cd : ℕ) : ℕ :=
  300*(1000*(W+Cg+Cl+Cr+Cd+100)+1)+Cg+Cl+Cr+Cd

set_option maxRecDepth 2000 in
set_option maxHeartbeats 400000 in
/-- Every intermediate weight is discharged from the actual encoded parent and
the exact graph/domain/projection-context callee bounds. -/
theorem itcs_physical_data_prog {Pg : Program} {f gp lc rng dom Cg Cl Cr Cd : ℕ}
    (hf : Pg.funs[f]? = some (itcsPhysicalDataF gp lc rng dom))
    (sv : List Val) (q hs cells kv dp G LC range D : Val)
    (hk : sv[0]? = some kv) (hdp : sv[2]? = some dp)
    (hg : FunDet Pg gp (.list [kv,hs]) G Cg)
    (hl : FunDet Pg lc (.list [.list [kv,q],hs]) LC Cl)
    (hr : FunDet Pg rng kv range Cr)
    (hd : FunDet Pg dom (.list [.list [dp,cells],range]) D Cd) :
    let inp := Val.list [.list sv,q,hs,cells]
    FunDet Pg f inp (.list [G,D,LC]) (itcsPhysicalDataC inp.wt Cg Cl Cr Cd) := by
  dsimp only
  let inp := Val.list [.list sv,q,hs,cells]
  let M := inp.wt+Cg+Cl+Cr+Cd+100
  let Bw := 1000*M
  have budget : 20*inp.wt+20*Cg+20*Cl+20*Cr+20*Cd+1000 ≤ Bw := by dsimp only [Bw,M]; omega
  have wG := itcs_det_weight hg
  have wL := itcs_det_weight hl
  have wr := itcs_det_weight hr
  have wD := itcs_det_weight hd
  have wi : inp.wt ≤ Bw := by omega
  have ws : (Val.list sv).wt ≤ inp.wt := st_wt_mem (List.mem_cons_self ..)
  have wk : kv.wt ≤ inp.wt := (st_wt_mem (List.mem_of_getElem? hk)).trans ws
  have wd : dp.wt ≤ inp.wt := (st_wt_mem (List.mem_of_getElem? hdp)).trans ws
  have wfield {z : Val} (hz : z ∈ [Val.list sv,q,hs,cells]) : z.wt ≤ inp.wt := st_wt_mem hz
  have wpair {a b : Val} (ha : a.wt ≤ inp.wt) (hb : b.wt ≤ inp.wt) :
      (Val.list [a,b]).wt ≤ 5*inp.wt+10 := by have hh := wt_list2_le a b; omega
  have wget {rest : List Val} {i : ℕ} {z : Val}
      (hi : [Val.list sv,q,hs,cells][i]? = some z) (hii : i+2 ≤ Bw) :
      StDC Pg (inp::rest) (arg i) z 3 0 Bw :=
    StDC.arg hi wi hii ((st_wt_mem (List.mem_of_getElem? hi)).trans wi)
  have h2 : 2 ≤ Bw := by omega
  have h4 : 4 ≤ Bw := by omega
  have getK (rest : List Val) : StDC Pg (inp::rest) (.get (arg 0) (.nat 0)) kv 5 0 Bw :=
    by
      have ga : StDC Pg (inp::rest) (arg 0) (.list sv) 3 0 Bw := wget (i:=0) (rest:=rest) rfl (by omega)
      exact StDC.get (P:=Pg) (env:=inp::rest) (W:=Bw) (vs:=sv) (x:=0) (na:=3) (nb:=1) (Ea:=0) (Eb:=0) ga (StDC.nat 0 h2) hk (wk.trans wi)
  have getD (rest : List Val) : StDC Pg (inp::rest) (.get (arg 0) (.nat 2)) dp 5 0 Bw :=
    by
      have ga : StDC Pg (inp::rest) (arg 0) (.list sv) 3 0 Bw := wget (i:=0) (rest:=rest) rfl (by omega)
      exact StDC.get (P:=Pg) (env:=inp::rest) (W:=Bw) (vs:=sv) (x:=2) (na:=3) (nb:=1) (Ea:=0) (Eb:=0) ga (StDC.nat 2 h4) hdp (wd.trans wi)
  have wgi : (Val.list [kv,hs]).wt ≤ Bw := (wpair wk (wfield (by simp))).trans (by omega)
  have gc := StDC.call (StDC.mk2 (getK []) (wget (i:=2) rfl (by omega)) wgi (by omega)) hg (by omega)
  have wkq := wpair wk (wfield (by simp : q ∈ [Val.list sv,q,hs,cells]))
  have wlci : (Val.list [.list [kv,q],hs]).wt ≤ Bw := by
    have hh := wt_list2_le (.list [kv,q]) hs
    have wh := wfield (by simp : hs ∈ [Val.list sv,q,hs,cells])
    omega
  have lcCall := StDC.call (StDC.mk2 (StDC.mk2 (getK [G]) (wget (i:=1) rfl (by omega))
    (wkq.trans (by omega)) (by omega)) (wget (i:=2) rfl (by omega)) wlci (by omega)) hl (by omega)
  have rc := StDC.call (getK [G,LC]) hr (by omega)
  have wdc := wpair wd (wfield (by simp : cells ∈ [Val.list sv,q,hs,cells]))
  have wdci : (Val.list [.list [dp,cells],range]).wt ≤ Bw := by
    have hh := wt_list2_le (.list [dp,cells]) range
    omega
  have r3 : StDC Pg [inp,G,LC,range] (.var 3) range 1 0 Bw := StDC.var' rfl (by omega)
  have dc := StDC.call (StDC.mk2 (StDC.mk2 (getD [G,LC,range]) (wget (i:=3) rfl (by omega))
    (wdc.trans (by omega)) (by omega)) r3 wdci (by omega)) hd (by omega)
  have wout : (Val.list [G,D,LC]).wt ≤ Bw := by have hh := wt_list3_le G D LC; omega
  have g1 : StDC Pg [inp,G,LC,range,D] (.var 1) G 1 0 Bw := StDC.var' rfl (by omega)
  have d4 : StDC Pg [inp,G,LC,range,D] (.var 4) D 1 0 Bw := StDC.var' rfl (by omega)
  have l2 : StDC Pg [inp,G,LC,range,D] (.var 2) LC 1 0 Bw := StDC.var' rfl (by omega)
  have result := StDC.mk3 g1 d4 l2 wout (by omega)
  have body := StDC.letE gc (StDC.letE lcCall (StDC.letE rc (StDC.letE dc result wout) wout) wout) wout
  clear budget wi ws wk wd wfield wpair wget getK getD wgi gc wkq wlci lcCall rc wdc wdci r3 dc wout g1 d4 l2 result
  exact StDC.funDet hf body (by unfold itcsPhysicalDataC; dsimp only [Bw,M,inp] at *; omega)

end GI.Impl
