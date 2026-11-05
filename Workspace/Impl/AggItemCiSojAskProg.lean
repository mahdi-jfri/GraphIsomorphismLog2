module

public import Workspace.Impl.AggItemCiSojRectStart
public import Workspace.Impl.AggItemCiSojWt

@[expose] public section

/-! # The actual initial-query constructor on the representation bytes -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
/-- Construct both query occurrences and the exact saved payload. Every
structural value weight follows from the actual input and the three callee
bounds. An identity optional twist is handled as a second occurrence. -/
theorem itcs_ask_prog {Pg : Program} {f data colors Cd C₀ C₁ : ℕ}
    (hf : Pg.funs[f]? = some (itcsAskF data colors))
    (sv q v a fix hs cells idv side xt yt G D LC Q₀ Q₁ : Val) (xc yc : List Val) (tw : Option Val)
    (hx : xc[0]? = some xt) (hy : yc[0]? = some yt)
    (hd : FunDet Pg data (.list [sv,q,hs,cells]) (.list [G,D,LC]) Cd)
    (h₀ : FunDet Pg colors (.list [sv,G,D,xt,yt,v,q,cells,a,idv]) Q₀ C₀)
    (h₁ : ∀ t, tw=some t → FunDet Pg colors (.list [sv,G,D,xt,yt,v,q,cells,a,t]) Q₁ C₁) :
    let inp := Val.list [sv,q,.list xc,.list yc,v,a,fix,.list [hs,cells,.list tw.toList],idv,side]
    let payload := Val.list [q,a,fix,LC,.list (idv::tw.toList)]
    let pending := Val.list (tw.toList.map fun _ => Q₁)
    FunDet Pg f inp (itcsAskV Q₀ payload pending) (itcsAskC inp.wt Cd C₀ C₁) := by
  dsimp only
  let inp := Val.list [sv,q,.list xc,.list yc,v,a,fix,.list [hs,cells,.list tw.toList],idv,side]
  let dv := Val.list [G,D,LC]
  let M := inp.wt+Cd+C₀+C₁+100
  let Bw := 1000*M
  have m100 : 100≤ M := by dsimp only [M]; omega
  have mb : M≤ Bw := by dsimp only [Bw]; omega
  have h20 : 20≤ Bw := by omega
  have wiM : inp.wt≤ M := by dsimp only [M]; omega
  have wi : inp.wt≤ Bw := wiM.trans mb
  have cdM : Cd≤ M := by dsimp only [M]; omega
  have c₀M : C₀≤ M := by dsimp only [M]; omega
  have c₁M : C₁≤ M := by dsimp only [M]; omega
  have wd : dv.wt≤ Cd := itcs_det_weight hd
  have wq₀ : Q₀.wt≤ M := (itcs_det_weight h₀).trans c₀M
  have field {z : Val} (hz : z∈[sv,q,Val.list xc,.list yc,v,a,fix,.list [hs,cells,.list tw.toList],idv,side]) :
      z.wt≤ M := (st_wt_mem hz).trans (show inp.wt≤ M from wiM)
  have repW : (Val.list [hs,cells,.list tw.toList]).wt≤ M := field (by simp)
  have repField {z : Val} (hz : z∈[hs,cells,Val.list tw.toList]) : z.wt≤ M :=
    (st_wt_mem hz).trans repW
  have dataField {z : Val} (hz : z∈[G,D,LC]) : z.wt≤ M :=
    (st_wt_mem hz).trans (wd.trans cdM)
  have wx : xt.wt≤ M := (st_wt_mem (List.mem_of_getElem? hx)).trans (field (by simp))
  have wy : yt.wt≤ M := (st_wt_mem (List.mem_of_getElem? hy)).trans (field (by simp))
  have get {rest : List Val} {i : ℕ} {z : Val}
      (hi : [sv,q,Val.list xc,.list yc,v,a,fix,.list [hs,cells,.list tw.toList],idv,side][i]?=some z)
      (hii : i+2≤ Bw) : StDC Pg (inp::dv::rest) (arg i) z 3 0 Bw :=
    StDC.arg hi wi hii ((st_wt_mem (List.mem_of_getElem? hi)).trans wi)
  have gd {rest : List Val} {i : ℕ} {z : Val} (hi : [G,D,LC][i]?=some z) (hii : i+2≤ Bw) :
      StDC Pg (inp::dv::rest) (.get (.var 1) (.nat i)) z 3 0 Bw :=
    StDC.get (vs:=[G,D,LC]) (x:=i) (na:=1) (nb:=1) (Ea:=0) (Eb:=0)
      (StDC.var' rfl ((wd.trans cdM).trans mb)) (StDC.nat i hii) hi
      ((dataField (List.mem_of_getElem? hi)).trans mb)
  have gr {rest : List Val} {i : ℕ} {z : Val} (hi : [hs,cells,Val.list tw.toList][i]?=some z) (hii : i+2≤ Bw) :
      StDC Pg (inp::dv::rest) (.get (arg 7) (.nat i)) z 5 0 Bw :=
    StDC.get (vs:=[hs,cells,Val.list tw.toList]) (x:=i) (na:=3) (nb:=1) (Ea:=0) (Eb:=0)
      (get (i:=7) rfl (by omega)) (StDC.nat i hii) hi ((repField (List.mem_of_getElem? hi)).trans mb)
  have gx (rest : List Val) : StDC Pg (inp::dv::rest) (.get (arg 2) (.nat 0)) xt 5 0 Bw :=
    StDC.get (vs:=xc) (x:=0) (na:=3) (nb:=1) (Ea:=0) (Eb:=0)
      (get (i:=2) rfl (by omega)) (StDC.nat 0 (by omega)) hx (wx.trans mb)
  have gy (rest : List Val) : StDC Pg (inp::dv::rest) (.get (arg 3) (.nat 0)) yt 5 0 Bw :=
    StDC.get (vs:=yc) (x:=0) (na:=3) (nb:=1) (Ea:=0) (Eb:=0)
      (get (i:=3) rfl (by omega)) (StDC.nat 0 (by omega)) hy (wy.trans mb)
  have query {rest : List Val} {te : Expr} {t Q : Val} {nt C : ℕ}
      (ht : StDC Pg (inp::dv::rest) te t nt 0 Bw) (wt : t.wt≤ M)
      (hq : FunDet Pg colors (.list [sv,G,D,xt,yt,v,q,cells,a,t]) Q C) (hC : C≤ M) :
      StDC Pg (inp::dv::rest) (itcsAskQuery colors te) Q (nt+50) C Bw := by
    have wa : (Val.list [sv,G,D,xt,yt,v,q,cells,a,t]).wt≤ Bw := by
      have hh := wt_list_le [sv,G,D,xt,yt,v,q,cells,a,t]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at hh
      have wsv := field (by simp : sv∈[sv,q,Val.list xc,.list yc,v,a,fix,.list [hs,cells,.list tw.toList],idv,side])
      have wG := dataField (by simp : G∈[G,D,LC])
      have wD := dataField (by simp : D∈[G,D,LC])
      have wv := field (by simp : v∈[sv,q,Val.list xc,.list yc,v,a,fix,.list [hs,cells,.list tw.toList],idv,side])
      have wq := field (by simp : q∈[sv,q,Val.list xc,.list yc,v,a,fix,.list [hs,cells,.list tw.toList],idv,side])
      have wc := repField (by simp : cells∈[hs,cells,Val.list tw.toList])
      have wa := field (by simp : a∈[sv,q,Val.list xc,.list yc,v,a,fix,.list [hs,cells,.list tw.toList],idv,side])
      dsimp only [Bw]
      omega
    have args := itcs_mk10 (get (i:=0) rfl (by omega)) (gd (i:=0) rfl (by omega))
      (gd (i:=1) rfl (by omega)) (gx rest) (gy rest) (get (i:=4) rfl (by omega))
      (get (i:=1) rfl (by omega)) (gr (i:=1) rfl (by omega)) (get (i:=5) rfl (by omega)) ht wa (by omega)
    exact (StDC.call args hq (((itcs_det_weight hq).trans hC).trans mb)).mono (by omega) (by omega)
  have payloadW (ts : Val) (hw : ts.wt≤6*M+10) : (Val.list [q,a,fix,LC,ts]).wt≤50*M+50 := by
    have hh := itcs_wt_list5 q a fix LC ts
    have wq := field (by simp : q∈[sv,q,Val.list xc,.list yc,v,a,fix,.list [hs,cells,.list tw.toList],idv,side])
    have wa := field (by simp : a∈[sv,q,Val.list xc,.list yc,v,a,fix,.list [hs,cells,.list tw.toList],idv,side])
    have wf := field (by simp : fix∈[sv,q,Val.list xc,.list yc,v,a,fix,.list [hs,cells,.list tw.toList],idv,side])
    have wl := dataField (by simp : LC∈[G,D,LC])
    omega
  have payload {rest : List Val} {te : Expr} {ts : Val} {nt : ℕ}
      (ht : StDC Pg (inp::dv::rest) te ts nt 0 Bw) (hw : ts.wt≤6*M+10) :
      StDC Pg (inp::dv::rest) (itcsAskPayload te) (.list [q,a,fix,LC,ts]) (nt+30) 0 Bw := by
    have ww : (Val.list [q,a,fix,LC,ts]).wt≤ Bw := (payloadW ts hw).trans (by dsimp only [Bw]; omega)
    exact (itcs_mk5 (get (i:=1) rfl (by omega)) (get (i:=5) rfl (by omega))
      (get (i:=6) rfl (by omega)) (gd (i:=2) rfl (by omega)) ht ww (by omega)).mono (by omega) (by omega)
  have askW (pl pn : Val) (wp : pl.wt≤50*M+50) (wn : pn.wt≤6*M+10) :
      (itcsAskV Q₀ pl pn).wt≤ Bw := by
    have hh := itcs_ask_weight Q₀ pl pn
    dsimp only [Bw]
    omega
  have ask {rest : List Val} {pe ne : Expr} {pl pn : Val} {np nn : ℕ}
      (hp : StDC Pg (inp::dv::Q₀::rest) pe pl np 0 Bw)
      (hn : StDC Pg (inp::dv::Q₀::rest) ne pn nn 0 Bw)
      (wp : pl.wt≤50*M+50) (wn : pn.wt≤6*M+10) :
      StDC Pg (inp::dv::Q₀::rest) (itcsAskE pe ne) (itcsAskV Q₀ pl pn) (np+nn+30) 0 Bw := by
    have wo := askW pl pn wp wn
    have wk : (Val.list [pl,pn,.list []]).wt≤ Bw :=
      (st_wt_mem (by simp : Val.list [pl,pn,.list []]∈[.nat 1,.nat 1,Q₀,.list [pl,pn,.list []]])).trans wo
    have q₂ : StDC Pg (inp::dv::Q₀::rest) (.var 2) Q₀ 1 0 Bw := StDC.var' rfl (wq₀.trans mb)
    exact (StDC.mk4 (StDC.nat 1 (by omega)) (StDC.nat 1 (by omega)) q₂
      (StDC.mk3 hp hn (StDC.nil (by omega)) wk (by omega)) wo (by omega)).mono (by omega) (by omega)
  have dataArgsW : (Val.list [sv,q,hs,cells]).wt≤ Bw := by
    have hh := wt_list4_le sv q hs cells
    have ws := field (by simp : sv∈[sv,q,Val.list xc,.list yc,v,a,fix,.list [hs,cells,.list tw.toList],idv,side])
    have wq := field (by simp : q∈[sv,q,Val.list xc,.list yc,v,a,fix,.list [hs,cells,.list tw.toList],idv,side])
    have wh := repField (by simp : hs∈[hs,cells,Val.list tw.toList])
    have wc := repField (by simp : cells∈[hs,cells,Val.list tw.toList])
    dsimp only [Bw]
    omega
  have get₀ {i : ℕ} {z : Val}
      (hi : [sv,q,Val.list xc,.list yc,v,a,fix,.list [hs,cells,.list tw.toList],idv,side][i]?=some z)
      (hii : i+2≤ Bw) : StDC Pg [inp] (arg i) z 3 0 Bw :=
    StDC.arg hi wi hii ((st_wt_mem (List.mem_of_getElem? hi)).trans wi)
  have gr₀ {i : ℕ} {z : Val} (hi : [hs,cells,Val.list tw.toList][i]?=some z) (hii : i+2≤ Bw) :
      StDC Pg [inp] (.get (arg 7) (.nat i)) z 5 0 Bw :=
    StDC.get (vs:=[hs,cells,Val.list tw.toList]) (x:=i) (na:=3) (nb:=1) (Ea:=0) (Eb:=0)
      (get₀ (i:=7) rfl (by omega)) (StDC.nat i hii) hi ((repField (List.mem_of_getElem? hi)).trans mb)
  have dcall := StDC.call (StDC.mk4 (get₀ (i:=0) rfl (by omega)) (get₀ (i:=1) rfl (by omega))
    (gr₀ (i:=0) rfl (by omega)) (gr₀ (i:=1) rfl (by omega)) dataArgsW (by omega)) hd ((wd.trans cdM).trans mb)
  have idM : idv.wt≤ M := field (by simp)
  have qcall := query (rest:=[]) (get (i:=8) rfl (by omega)) idM h₀ c₀M
  cases tw with
  | none =>
    have tsW : (Val.list [idv]).wt≤6*M+10 := by
      have hh := wt_list_le [idv]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at hh
      omega
    have ts := StDC.snoc (StDC.nil (P:=Pg) (env:=[inp,dv,Q₀]) (W:=Bw) (by omega))
      (get (i:=8) rfl (by omega)) (tsW.trans (by dsimp only [Bw]; omega))
    have pl := payload ts tsW
    have wnil : (Val.list []).wt≤6*M+10 := by simp only [wt_list_nil]; omega
    have done := ask pl (StDC.nil (by omega)) (payloadW _ tsW) wnil
    have wo := askW _ _ (payloadW _ tsW) wnil
    have len : StDC Pg [inp,dv,Q₀] (.length (.get (arg 7) (.nat 2))) (.nat 0) 6 0 Bw :=
      StDC.length (gr (i:=2) rfl (by omega)) (by change 0+2≤ Bw; omega)
    have tail := StDC.ite (t:=.letE (itcsAskQuery colors (.get (.get (arg 7) (.nat 2)) (.nat 0)))
      (itcsAskE (itcsAskPayload (mk2 (arg 8) (.get (.get (arg 7) (.nat 2)) (.nat 0)))) (.snoc .nil (.var 3))))
      (nt:=200) (ne:=100) (Et:=C₁) (Ee:=0) len (fun h => by omega)
      (fun _ => done.mono (by omega) (by omega)) wo
    have body := StDC.letE dcall (StDC.letE qcall tail wo) wo
    have body' : StDC Pg [inp] (itcsAskF data colors)
        (itcsAskV Q₀ (.list [q,a,fix,LC,.list [idv]]) (.list [])) 500 (Cd+C₀+C₁) Bw :=
      body.mono (by omega) (by omega)
    exact StDC.funDet hf body' (by simp only [itcsAskC,Bw,M,inp,Nat.add_assoc]; exact le_refl _)
  | some t =>
    have twM : (Val.list [t]).wt ≤ M := repField (by simp)
    have tM : t.wt ≤ M := (st_wt_mem (vs:=[t]) (List.mem_cons_self ..)).trans twM
    have gt (rest : List Val) : StDC Pg (inp::dv::rest) (.get (.get (arg 7) (.nat 2)) (.nat 0)) t 7 0 Bw :=
      StDC.get (vs:=[t]) (x:=0) (na:=5) (nb:=1) (Ea:=0) (Eb:=0)
        (gr (i:=2) rfl (by omega)) (StDC.nat 0 (by omega)) rfl (tM.trans mb)
    have qc := query (rest:=[Q₀]) (gt [Q₀]) tM (h₁ t rfl) c₁M
    have wq₁ : Q₁.wt≤ M := (itcs_det_weight (h₁ t rfl)).trans c₁M
    have tsW : (Val.list [idv,t]).wt≤6*M+10 := by have hh := wt_list2_le idv t; omega
    have ts := StDC.mk2 (get (rest:=[Q₀,Q₁]) (i:=8) rfl (by omega)) (gt [Q₀,Q₁])
      (tsW.trans (by dsimp only [Bw]; omega)) (by omega)
    have pl := payload ts tsW
    have pnW : (Val.list [Q₁]).wt≤6*M+10 := by
      have hh := wt_list_le [Q₁]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at hh
      omega
    have pn := StDC.snoc (StDC.nil (P:=Pg) (env:=[inp,dv,Q₀,Q₁]) (W:=Bw) (by omega))
      (StDC.var' (i:=3) rfl (wq₁.trans mb)) (pnW.trans (by dsimp only [Bw]; omega))
    have done := ask pl pn (payloadW _ tsW) pnW
    have wo := askW _ _ (payloadW _ tsW) pnW
    have branch := StDC.letE qc done wo
    have len : StDC Pg [inp,dv,Q₀] (.length (.get (arg 7) (.nat 2))) (.nat 1) 6 0 Bw :=
      StDC.length (gr (i:=2) rfl (by omega)) (by change 1+2≤ Bw; omega)
    have tail := StDC.ite (e:=itcsAskE (itcsAskPayload (.snoc .nil (arg 8))) .nil)
      (nt:=200) (ne:=100) (Et:=C₁) (Ee:=0) len
      (fun _ => branch.mono (by omega) (by omega)) (fun h => by omega) wo
    have body := StDC.letE dcall (StDC.letE qcall tail wo) wo
    have body' : StDC Pg [inp] (itcsAskF data colors)
        (itcsAskV Q₀ (.list [q,a,fix,LC,.list [idv,t]]) (.list [Q₁])) 500 (Cd+C₀+C₁) Bw :=
      body.mono (by omega) (by omega)
    exact StDC.funDet hf body' (by simp only [itcsAskC,Bw,M,inp,Nat.add_assoc]; exact le_refl _)

end GI.Impl
