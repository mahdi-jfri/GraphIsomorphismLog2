import Workspace.Impl.AggItemCiSojWt
import Workspace.Impl.AggItemCiSojPW
import Workspace.Impl.AggItemCiSojState

/-! # Building the two matrix color tables and the exact query state -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

/-- Input: `[parent,group,domain,X-table,Y-table,edge,q,cells,alignment,twist]`.
Build the physical source table and the alignment/twist target table, then the
inherited query state. -/
def itcsColorsStateF (cmp rng pull state : ℕ) : Expr :=
  .letE (.call cmp (mk2 (arg 8) (arg 9)))
    (.letE (.call rng (arg 6))
      (.letE (.call pull (mk2 (mk4 (arg 3) (arg 5) (arg 6) (.var 2)) (arg 7)))
        (.letE (.call pull (mk2 (mk4 (arg 4) (arg 5) (arg 6) (.var 1)) (arg 7)))
          (.call state (itcsMk5 (arg 0) (arg 1) (arg 2) (.var 3) (.var 4))))))

/-- A scalar cost for the fixed table-building pipeline. -/
def itcsColorsStateC (W Cp Cr Cx Cy Cs : ℕ) : ℕ :=
  500*(1000*(W+Cp+Cr+Cx+Cy+Cs+100)+1)+Cp+Cr+Cx+Cy+Cs

set_option maxHeartbeats 400000 in
/-- Compose the actual permutation, range, pullback and state-constructor calls.
Every byte-value argument and result bound follows from the input weight and
these callee bounds. -/
theorem itcs_colors_state_prog {Pg : Program} {f cmp rng pull state Cp Cr Cx Cy Cs : ℕ}
    (hf : Pg.funs[f]? = some (itcsColorsStateF cmp rng pull state))
    (sv gv dv xt yt v q cells a t p id xv yv out : Val)
    (hp : FunDet Pg cmp (.list [a,t]) p Cp)
    (hr : FunDet Pg rng q id Cr)
    (hx : FunDet Pg pull (.list [.list [xt,v,q,id],cells]) xv Cx)
    (hy : FunDet Pg pull (.list [.list [yt,v,q,p],cells]) yv Cy)
    (hs : FunDet Pg state (.list [sv,gv,dv,xv,yv]) out Cs) :
    let inp := Val.list [sv,gv,dv,xt,yt,v,q,cells,a,t]
    FunDet Pg f inp out (itcsColorsStateC inp.wt Cp Cr Cx Cy Cs) := by
  dsimp only
  let inp := Val.list [sv,gv,dv,xt,yt,v,q,cells,a,t]
  let M := inp.wt+Cp+Cr+Cx+Cy+Cs+100
  let Bw := 1000*M
  have budget : 20*inp.wt+20*Cp+20*Cr+20*Cx+20*Cy+20*Cs+1000 ≤ Bw := by
    dsimp only [Bw,M]; omega
  have wp := itcs_det_weight hp
  have wr := itcs_det_weight hr
  have wx := itcs_det_weight hx
  have wy := itcs_det_weight hy
  have wo := itcs_det_weight hs
  have wfield {z : Val} (hz : z ∈ [sv,gv,dv,xt,yt,v,q,cells,a,t]) : z.wt ≤ M :=
    (st_wt_mem hz).trans (show inp.wt ≤ M from by dsimp only [M]; omega)
  have pM : p.wt ≤ M := wp.trans (by dsimp only [M]; omega)
  have idM : id.wt ≤ M := wr.trans (by dsimp only [M]; omega)
  have xM : xv.wt ≤ M := wx.trans (by dsimp only [M]; omega)
  have yM : yv.wt ≤ M := wy.trans (by dsimp only [M]; omega)
  have mBw : 20*M+20 ≤ Bw := by dsimp only [M,Bw]; omega
  have w2 {a b : Val} (ha : a.wt ≤ M) (hb : b.wt ≤ M) : (Val.list [a,b]).wt ≤ Bw := by
    have hh := wt_list2_le a b
    omega
  have w4 {a b c d : Val} (ha : a.wt ≤ M) (hb : b.wt ≤ M) (hc : c.wt ≤ M) (hd : d.wt ≤ M) :
      (Val.list [a,b,c,d]).wt ≤ 10*M+10 := by
    have hh := wt_list4_le a b c d
    omega
  have w4pair {a b c d z : Val} (ha : a.wt ≤ M) (hb : b.wt ≤ M)
      (hc : c.wt ≤ M) (hd : d.wt ≤ M) (hz : z.wt ≤ M) :
      (Val.list [.list [a,b,c,d],z]).wt ≤ Bw := by
    have hh := wt_list2_le (.list [a,b,c,d]) z
    have hw := w4 ha hb hc hd
    omega
  have w5 {a b c d e : Val} (ha : a.wt ≤ M) (hb : b.wt ≤ M)
      (hc : c.wt ≤ M) (hd : d.wt ≤ M) (he : e.wt ≤ M) :
      (Val.list [a,b,c,d,e]).wt ≤ Bw := by
    have hh := itcs_wt_list5 a b c d e
    omega
  have wi : inp.wt ≤ Bw := by omega
  have get {rest : List Val} {i : ℕ} {z : Val}
      (hi : [sv,gv,dv,xt,yt,v,q,cells,a,t][i]? = some z) (hii : i+2 ≤ Bw) :
      StDC Pg (inp::rest) (arg i) z 3 0 Bw :=
    StDC.arg hi wi hii ((st_wt_mem (List.mem_of_getElem? hi)).trans wi)
  have pc := StDC.call (StDC.mk2 (get (i:=8) (rest:=[]) rfl (by omega))
    (get (i:=9) rfl (by omega)) (w2 (wfield (by simp)) (wfield (by simp))) (by omega)) hp (by omega)
  have rc := StDC.call (get (i:=6) (rest:=[p]) rfl (by omega)) hr (by omega)
  have id2 : StDC Pg [inp,p,id] (.var 2) id 1 0 Bw := StDC.var' rfl (by omega)
  have px := StDC.mk4 (get (i:=3) (rest:=[p,id]) rfl (by omega))
    (get (i:=5) rfl (by omega)) (get (i:=6) rfl (by omega)) id2
    ((w4 (wfield (by simp)) (wfield (by simp)) (wfield (by simp)) idM).trans (by omega)) (by omega)
  have xc := StDC.call (StDC.mk2 px (get (i:=7) rfl (by omega))
    (w4pair (wfield (by simp)) (wfield (by simp)) (wfield (by simp)) idM (wfield (by simp)))
    (by omega)) hx (by omega)
  have p1 : StDC Pg [inp,p,id,xv] (.var 1) p 1 0 Bw := StDC.var' rfl (by omega)
  have py := StDC.mk4 (get (i:=4) (rest:=[p,id,xv]) rfl (by omega))
    (get (i:=5) rfl (by omega)) (get (i:=6) rfl (by omega)) p1
    ((w4 (wfield (by simp)) (wfield (by simp)) (wfield (by simp)) pM).trans (by omega)) (by omega)
  have yc := StDC.call (StDC.mk2 py (get (i:=7) rfl (by omega))
    (w4pair (wfield (by simp)) (wfield (by simp)) (wfield (by simp)) pM (wfield (by simp)))
    (by omega)) hy (by omega)
  have x3 : StDC Pg [inp,p,id,xv,yv] (.var 3) xv 1 0 Bw := StDC.var' rfl (by omega)
  have y4 : StDC Pg [inp,p,id,xv,yv] (.var 4) yv 1 0 Bw := StDC.var' rfl (by omega)
  have sc := StDC.call (itcs_mk5 (get (i:=0) (rest:=[p,id,xv,yv]) rfl (by omega))
    (get (i:=1) rfl (by omega)) (get (i:=2) rfl (by omega)) x3 y4
    (w5 (wfield (by simp)) (wfield (by simp)) (wfield (by simp)) xM yM) (by omega)) hs (by omega)
  have body := StDC.letE pc (StDC.letE rc (StDC.letE xc (StDC.letE yc sc (by omega)) (by omega)) (by omega)) (by omega)
  clear budget wfield pM idM xM yM mBw w2 w4 w4pair w5 wi get pc rc id2 px xc p1 py yc x3 y4 sc
  exact StDC.funDet hf body (by unfold itcsColorsStateC; dsimp only [Bw,M,inp] at *; omega)

end GI.Impl
