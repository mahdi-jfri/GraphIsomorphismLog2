module

public import Workspace.Impl.AggItemCiSojRectStart
public import Workspace.Impl.AggItemCiSojACount

@[expose] public section

/-! # Evaluating the certified first-rectangle controller -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

/-- Own structural cost plus the costs of the ten actual controller calls. -/
def itcsRectPrepC (W Cr Cb Cs Cg Ca Cf Cw Ct Cp Cq : ℕ) : ℕ :=
  1000*(1000*(W+Cr+Cb+Cs+Cg+Ca+Cf+Cw+Ct+Cp+Cq+100)+1)+
    (Cr+Cb+2*Cs+Cg+Ca+Cf+Cw+Ct+Cp+Cq)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
/-- Evaluate the literal target-size guard before making the alignment or
representation call. The representation output may have several encodings;
the same continuation contract must hold for each certified encoding. -/
theorem itcs_rect_prep_prog {Pg : Program}
    {f rng bal sides guard align fix markW markR rep ask : ℕ}
    {Cr Cb Cs Cg Ca Cf Cw Ct Cp Cq : ℕ}
    (hf : Pg.funs[f]?=some (itcsRectPrepF rng bal sides guard align fix markW markR rep ask))
    (oi ki si li ox oy xc yc cv : List Val) (fiber bx sv q ps vL vR vE : Val)
    (ho : oi[0]?=some (.list ki)) (hk : ki[0]?=some (.list si))
    (hs : si[0]?=some sv) (hl : si[1]?=some (.list li))
    (hq : li[1]?=some q) (hp : si[2]?=some ps)
    (hox : oi[2]?=some (.list ox)) (hoy : oi[3]?=some (.list oy))
    (hx : ox[1]?=some (.list xc)) (hy : oy[1]?=some (.list yc))
    (hcL : cv[0]?=some vL) (hcR : cv[1]?=some vR) (hcE : cv[2]?=some vE)
    (range byv sx sy av fv wm rm : Val) (g : ℕ) (R P : Val → Prop)
    (hr : FunDet Pg rng q range Cr)
    (hb : FunDet Pg bal (.list [.list yc,range]) byv Cb)
    (hsx : FunDet Pg sides (.list [.list [bx,vL,vR],range]) sx Cs)
    (hsy : FunDet Pg sides (.list [.list [byv,vL,vR],range]) sy Cs)
    (hg : FunDet Pg guard (.list [sx,sy]) (.nat g) Cg)
    (ha : g≠0 → FunDet Pg align (.list [sx,sy]) av Ca)
    (hfix : g≠0 → FunDet Pg fix sx fv Cf)
    (hw : g≠0 → FunDet Pg markW (.list [sx,range]) wm Cw)
    (ht : g≠0 → FunDet Pg markR (.list [sx,range]) rm Ct)
    (hrp : g≠0 → FunAll Pg rep (.list [sv,q,ps,wm,rm]) fun w cost => R w ∧ cost≤ Cp)
    (hask : ∀ rv, g≠0 → R rv → FunAll Pg ask
      (.list [sv,q,.list xc,.list yc,vE,av,fv,rv,range,sx]) fun w cost => P w ∧ cost≤ Cq)
    (hskip : g=0 → P (itcsResV (.list []))) :
    let inp := Val.list [.list oi,fiber,bx,.list cv]
    FunAll Pg f inp fun w cost => P w ∧ cost≤ itcsRectPrepC inp.wt Cr Cb Cs Cg Ca Cf Cw Ct Cp Cq := by
  dsimp only
  let inp := Val.list [.list oi,fiber,bx,.list cv]
  let M := inp.wt+Cr+Cb+Cs+Cg+Ca+Cf+Cw+Ct+Cp+Cq+100
  let Bw := 1000*M
  have mb : M≤ Bw := by dsimp only [Bw]; omega
  have m100 : 100≤ M := by dsimp only [M]; omega
  have wi : inp.wt≤ M := by dsimp only [M]; omega
  have h20 : 20≤ Bw := by omega
  have cf_cost : ∀ c∈[Cr,Cb,Cs,Cg,Ca,Cf,Cw,Ct,Cp,Cq], c≤ M := by
    intro c hc
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hc
    dsimp only [M]
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have cR := cf_cost Cr (by simp)
  have cB := cf_cost Cb (by simp)
  have cS := cf_cost Cs (by simp)
  have cG := cf_cost Cg (by simp)
  have cA := cf_cost Ca (by simp)
  have cF := cf_cost Cf (by simp)
  have cW := cf_cost Cw (by simp)
  have cT := cf_cost Ct (by simp)
  have cP := cf_cost Cp (by simp)
  have cQ := cf_cost Cq (by simp)
  have memw {ls : List Val} {z : Val} {i : ℕ} (h : ls[i]?=some z) (w : (Val.list ls).wt≤ M) : z.wt≤ M :=
    (st_wt_mem (List.mem_of_getElem? h)).trans w
  have woi : (Val.list oi).wt≤ M := memw (i:=0) rfl wi
  have wki := memw ho woi
  have wsi := memw hk wki
  have wli := memw hl wsi
  have wox := memw hox woi
  have woy := memw hoy woi
  have wxc := memw hx wox
  have wyc := memw hy woy
  have wcv : (Val.list cv).wt≤ M := memw (i:=3) rfl wi
  have wsv := memw hs wsi
  have wq := memw hq wli
  have wps := memw hp wsi
  have wL := memw hcL wcv
  have wR := memw hcR wcv
  have wE := memw hcE wcv
  have wbx : bx.wt≤ M := memw (i:=2) rfl wi
  have wr : range.wt≤ M := (itcs_det_weight hr).trans cR
  have wb : byv.wt≤ M := (itcs_det_weight hb).trans cB
  have wsx : sx.wt≤ M := (itcs_det_weight hsx).trans cS
  have wsy : sy.wt≤ M := (itcs_det_weight hsy).trans cS
  have listw (ls : List Val) (hn : ls.length≤10) (hh : ∀z∈ls,z.wt≤ M) : (Val.list ls).wt≤ Bw := by
    have hw := wt_list_map_le ls id (W:=M) (by simpa using hh)
    simp only [List.map_id] at hw
    have hw' := hw.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (2*M+1) hn) 4)
    dsimp only [Bw]
    omega
  have read {env : List Val} {e : Expr} {ls : List Val} {i n : ℕ} {z : Val}
      (he : StDC Pg env e (.list ls) n 0 Bw) (hi : ls[i]?=some z)
      (wl : (Val.list ls).wt≤ M) (hii : i+2≤ Bw) :
      StDC Pg env (.get e (.nat i)) z (n+2) 0 Bw :=
    StDC.get (vs:=ls) (x:=i) (na:=n) (nb:=1) (Ea:=0) (Eb:=0) he (StDC.nat i hii) hi ((memw hi wl).trans mb)
  have argd {rest : List Val} {i : ℕ} {z : Val}
      (hi : [Val.list oi,fiber,bx,.list cv][i]?=some z) (hii : i+2≤ Bw) :
      StDC Pg (inp::rest) (arg i) z 3 0 Bw :=
    StDC.arg hi (wi.trans mb) hii ((memw hi wi).trans mb)
  have orig (rest : List Val) : StDC Pg (inp::rest) (arg 0) (.list oi) 3 0 Bw := argd (i:=0) rfl (by omega)
  have st (rest : List Val) := read (read (orig rest) ho woi (by omega)) hk wki (by omega)
  have svd (rest : List Val) := read (st rest) hs wsi (by omega)
  have qd (rest : List Val) := read (read (st rest) hl wsi (by omega)) hq wli (by omega)
  have psd (rest : List Val) := read (st rest) hp wsi (by omega)
  have xd (rest : List Val) := read (read (orig rest) hox woi (by omega)) hx wox (by omega)
  have yd (rest : List Val) := read (read (orig rest) hoy woi (by omega)) hy woy (by omega)
  have certd {rest : List Val} {i : ℕ} {z : Val} (hi : cv[i]?=some z) (hii : i+2≤ Bw) :=
    read (argd (i:=3) rfl (by omega) (rest:=rest)) hi wcv hii
  have vd {rest : List Val} {i : ℕ} {z : Val} (hi : rest[i-1]?=some z) (hii : i≠0) (hw : z.wt≤ M) :
      StDC Pg (inp::rest) (.var i) z 1 0 Bw := StDC.var' (by cases i with | zero => contradiction | succ i => simpa using hi) (hw.trans mb)
  have rcall := StDC.call (qd []) hr (wr.trans mb)
  have bargs := StDC.mk2 (yd [range]) (vd (i:=1) rfl (by decide) wr)
    (listw _ (by simp only [List.length_cons,List.length_nil]; decide) (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]; rintro z (rfl|rfl) <;> assumption)) (by omega)
  have bcall := StDC.call bargs hb (wb.trans mb)
  have sxargs := StDC.mk2
    (StDC.mk3 (argd (i:=2) rfl (by omega) (rest:=[range,byv]))
      (certd (i:=0) hcL (by omega)) (certd (i:=1) hcR (by omega))
      (listw _ (by simp only [List.length_cons,List.length_nil]; decide) (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]; rintro z (rfl|rfl|rfl) <;> assumption)) (by omega))
    (vd (i:=1) rfl (by decide) wr)
    (by have h := wt_list2_le (.list [bx,vL,vR]) range; have hh := wt_list3_le bx vL vR; dsimp only [Bw]; omega) (by omega)
  have sxcall := StDC.call sxargs hsx (wsx.trans mb)
  have syargs := StDC.mk2
    (StDC.mk3 (vd (i:=2) rfl (by decide) wb (rest:=[range,byv,sx]))
      (certd (i:=0) hcL (by omega)) (certd (i:=1) hcR (by omega))
      (listw _ (by simp only [List.length_cons,List.length_nil]; decide) (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]; rintro z (rfl|rfl|rfl) <;> assumption)) (by omega))
    (vd (i:=1) rfl (by decide) wr)
    (by have h := wt_list2_le (.list [byv,vL,vR]) range; have hh := wt_list3_le byv vL vR; dsimp only [Bw]; omega) (by omega)
  have sycall := StDC.call syargs hsy (wsy.trans mb)
  have sidesW := listw [sx,sy] (by simp only [List.length_cons,List.length_nil]; decide) (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]; rintro z (rfl|rfl) <;> assumption)
  have sideargs := StDC.mk2 (vd (rest:=[range,byv,sx,sy]) (i:=3) rfl (by decide) wsx)
    (vd (i:=4) rfl (by decide) wsy) sidesW (by omega)
  have wg : (Val.nat g).wt≤ M := (itcs_det_weight hg).trans cG
  have gc := StDC.call sideargs hg (wg.trans mb)
  have pass (hg0 : g≠0) := ha hg0
  have wav (hg0 : g≠0) : av.wt≤ M := (itcs_det_weight (ha hg0)).trans cA
  have wfv (hg0 : g≠0) : fv.wt≤ M := (itcs_det_weight (hfix hg0)).trans cF
  have wwm (hg0 : g≠0) : wm.wt≤ M := (itcs_det_weight (hw hg0)).trans cW
  have wrm (hg0 : g≠0) : rm.wt≤ M := (itcs_det_weight (ht hg0)).trans cT
  have onpass (hg0 : g≠0) : itcsAC Pg [inp,range,byv,sx,sy]
      (.letE (.call align (mk2 (.var 3) (.var 4)))
      (.letE (.call fix (.var 3))
        (.letE (.call markW (mk2 (.var 3) (.var 1)))
          (.letE (.call markR (mk2 (.var 3) (.var 1)))
            (.letE (.call rep (itcsMk5 (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 0))
              (.get (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 1)) (.nat 1))
              (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 2)) (.var 7) (.var 8)))
              (.call ask (itcsMk10 (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 0))
                (.get (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 1)) (.nat 1))
                (.get (.get (arg 0) (.nat 2)) (.nat 1)) (.get (.get (arg 0) (.nat 3)) (.nat 1))
                (.get (arg 3) (.nat 2)) (.var 5) (.var 6) (.var 9) (.var 1) (.var 3))))))))
      P 600 (Ca+Cf+Cw+Ct+Cp+Cq) Bw := by
    have ac := StDC.call sideargs (ha hg0) ((wav hg0).trans mb)
    have fc := StDC.call (vd (rest:=[range,byv,sx,sy,av]) (i:=3) rfl (by decide) wsx)
      (hfix hg0) ((wfv hg0).trans mb)
    have marks {rest : List Val} (hr : rest[0]?=some range) (hs : rest[2]?=some sx) :=
      StDC.mk2 (vd (rest:=rest) (i:=3) hs (by decide) wsx) (vd (i:=1) hr (by decide) wr)
        (listw _ (by simp only [List.length_cons,List.length_nil]; decide) (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]; rintro z (rfl|rfl) <;> assumption)) (by omega)
    have wc := StDC.call (marks (rest:=[range,byv,sx,sy,av,fv]) rfl rfl) (hw hg0) ((wwm hg0).trans mb)
    have tc := StDC.call (marks (rest:=[range,byv,sx,sy,av,fv,wm]) rfl rfl) (ht hg0) ((wrm hg0).trans mb)
    have rpArgs := itcs_mk5 (svd [range,byv,sx,sy,av,fv,wm,rm])
      (qd _) (psd _) (vd (i:=7) rfl (by decide) (wwm hg0)) (vd (i:=8) rfl (by decide) (wrm hg0))
      (listw _ (by simp only [List.length_cons,List.length_nil]; decide) (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]; rintro z (rfl|rfl|rfl|rfl|rfl) <;> first | assumption | exact wwm hg0 | exact wrm hg0)) (by omega)
    have rpCert : FunAll Pg rep (.list [sv,q,ps,wm,rm])
        (fun rv cost => (R rv ∧ rv.wt≤ Cp) ∧ cost≤ Cp) :=
      (hrp hg0).wt_lt.mono fun rv cost hh => ⟨⟨hh.1.1,hh.2.le.trans hh.1.2⟩,hh.1.2⟩
    have rpCall := itcsAC.call rpArgs rpCert (cP.trans mb)
    have after : ∀ rv, (R rv ∧ rv.wt≤ Cp) → rv.wt≤ Bw → itcsAC Pg
        [inp,range,byv,sx,sy,av,fv,wm,rm,rv]
        (.call ask (itcsMk10 (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 0))
          (.get (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 1)) (.nat 1))
          (.get (.get (arg 0) (.nat 2)) (.nat 1)) (.get (.get (arg 0) (.nat 3)) (.nat 1))
          (.get (arg 3) (.nat 2)) (.var 5) (.var 6) (.var 9) (.var 1) (.var 3))) P 100 Cq Bw := by
      intro rv ⟨hrv,wrp⟩ wrv
      have wrM : rv.wt≤ M := wrp.trans cP
      -- The returned representation is paid for by the representation call.
      have call := hask rv hg0 hrv
      have argsW : (Val.list [sv,q,.list xc,.list yc,vE,av,fv,rv,range,sx]).wt≤ Bw := by
        have hh := wt_list_le [sv,q,.list xc,.list yc,vE,av,fv,rv,range,sx]
        simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at hh
        have wa := wav hg0
        have wf := wfv hg0
        dsimp only [Bw]
        omega
      have args := itcs_mk10 (svd [range,byv,sx,sy,av,fv,wm,rm,rv]) (qd _) (xd _) (yd _)
        (certd (i:=2) hcE (by omega)) (vd (i:=5) rfl (by decide) (wav hg0))
        (vd (i:=6) rfl (by decide) (wfv hg0))
        (StDC.var' (i:=9) rfl wrv) (vd (i:=1) rfl (by decide) wr) (vd (i:=3) rfl (by decide) wsx) argsW (by omega)
      exact (itcsAC.call args call (cQ.trans mb)).mono (by omega) (by omega)
    have body := itcsAC.let_dc ac (itcsAC.let_dc fc (itcsAC.let_dc wc (itcsAC.let_dc tc (itcsAC.letE rpCall after))))
    exact body.mono (by omega) (by omega)
  have skip : g=0 → itcsAC Pg [inp,range,byv,sx,sy] (itcsResE .nil) P 20 0 Bw := by
    intro hg0
    have wo : (itcsResV (.list [])).wt≤ Bw := (itcs_res_weight _).trans (by simp only [wt_list_nil]; omega)
    exact (itcsAC.of_dc (itcs_res_dc (StDC.nil (by omega)) wo (by omega)) (hskip hg0) wo).mono (by omega) (by omega)
  have branches := itcsAC.ite gc onpass skip
  have body := itcsAC.let_dc rcall (itcsAC.let_dc bcall (itcsAC.let_dc sxcall (itcsAC.let_dc sycall branches)))
  have body' : itcsAC Pg [inp] (itcsRectPrepF rng bal sides guard align fix markW markR rep ask)
      P 1000 (Cr+Cb+2*Cs+Cg+Ca+Cf+Cw+Ct+Cp+Cq) Bw := body.mono (by omega) (by omega)
  exact itcsAC.funAll hf body' (by simp only [itcsRectPrepC,Bw,M,inp,Nat.add_assoc]; exact le_refl _)

end GI.Impl
