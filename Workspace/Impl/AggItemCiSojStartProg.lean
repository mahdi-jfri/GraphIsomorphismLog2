module

public import Workspace.Impl.AggItemCiSojStart
public import Workspace.Impl.AggItemCiSojACount

@[expose] public section

/-! # The actual first-rectangle source dispatch -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

/-- The front computes a square-size ordered-pair scan. All remaining own work
is linear in the returned table and the cited callee budgets. -/
def itcsStartC (W Cf Cp Ci Cr Cb Ct Cpart Ccert Crect : ℕ) : ℕ :=
  1000*(10000*(W+Cf+Cp+Ci+Cr+Cb+Ct+Cpart+Ccert+Crect+100)^2+1)+
    (Cf+Cp+Ci+Cr+Cb+Ct+Cpart+Ccert+Crect)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
/-- The source dispatch uses the actual ordered-pair test and actual balance
callback. Only the unbalanced primitive branch calls the certificate function.
Its possibly varying certificate encodings are passed to the same rectangle
continuation. -/
theorem itcs_start_prog {Pg : Program}
    {f front pc rng bal baltest imp part cert rect : ℕ}
    {Cf Cp Ci Cr Cb Ct Cpart Ccert Crect : ℕ}
    (hf : Pg.funs[f]?=some (itcsStartF front pc rng bal baltest imp part cert rect))
    (kv tb wk : Val) (xc yc rows fiber : List Val) (j g : ℕ) (v ovs povs range bx : Val)
    (hx : xc[0]?=some (.list rows)) (R P : Val → Prop)
    (hfront : FunDet Pg front (.list xc) (.list [.list fiber,.nat j]) Cf)
    (hpc : j<fiber.length*fiber.length → FunDet Pg pc
      (.list [.list [.list rows,.list fiber,.nat fiber.length],.nat j]) v Cp)
    (himp : j<fiber.length*fiber.length → FunDet Pg imp (.list [.list xc,.list yc,v]) ovs Ci)
    (hipost : j<fiber.length*fiber.length → P (itcsResV ovs))
    (hr : FunDet Pg rng (.nat rows.length) range Cr)
    (hb : FunDet Pg bal (.list [.list xc,range]) bx Cb)
    (ht : FunDet Pg baltest (.list [.list [bx,.nat fiber.length],.list fiber]) (.nat g) Ct)
    (hpart : ¬j<fiber.length*fiber.length → g≠0 → FunDet Pg part (.list [.list xc,.list yc]) povs Cpart)
    (hppost : ¬j<fiber.length*fiber.length → g≠0 → P (itcsResV povs))
    (hcert : ¬j<fiber.length*fiber.length → g=0 → FunAll Pg cert (.list xc) fun w cost => R w ∧ cost≤ Ccert)
    (hrect : ∀ cv, ¬j<fiber.length*fiber.length → g=0 → R cv → FunAll Pg rect
      (.list [.list [kv,tb,.list [.nat 2,.list xc],.list [.nat 2,.list yc],wk],.list fiber,bx,cv])
      fun w cost => P w ∧ cost≤ Crect) :
    let inp := Val.list [kv,tb,.list [.nat 2,.list xc],.list [.nat 2,.list yc],wk]
    FunAll Pg f inp fun w cost => P w ∧ cost≤ itcsStartC inp.wt Cf Cp Ci Cr Cb Ct Cpart Ccert Crect := by
  dsimp only
  let inp := Val.list [kv,tb,.list [.nat 2,.list xc],.list [.nat 2,.list yc],wk]
  let M := inp.wt+Cf+Cp+Ci+Cr+Cb+Ct+Cpart+Ccert+Crect+100
  let Bw := 10000*M^2
  have m100 : 100≤ M := by dsimp only [M]; omega
  have mm : M≤ M^2 := Nat.le_self_pow (by decide : 2≠0) M
  have mb : M≤ Bw := mm.trans (Nat.le_mul_of_pos_left _ (by decide : 0<10000))
  have h20 : 20≤ Bw := by omega
  have wi : inp.wt≤ M := by dsimp only [M]; omega
  have costs : ∀ c∈[Cf,Cp,Ci,Cr,Cb,Ct,Cpart,Ccert,Crect], c≤ M := by
    intro c hc
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    dsimp only [M]
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have cF := costs Cf (by simp)
  have cP := costs Cp (by simp)
  have cI := costs Ci (by simp)
  have cR := costs Cr (by simp)
  have cB := costs Cb (by simp)
  have cT := costs Ct (by simp)
  have cPart := costs Cpart (by simp)
  have cCert := costs Ccert (by simp)
  have cRect := costs Crect (by simp)
  have wox : (Val.list [.nat 2,.list xc]).wt≤ M := (st_wt_mem (by simp)).trans (show inp.wt≤ M from wi)
  have woy : (Val.list [.nat 2,.list yc]).wt≤ M := (st_wt_mem (by simp)).trans (show inp.wt≤ M from wi)
  have wx : (Val.list xc).wt≤ M := (st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans wox
  have wy : (Val.list yc).wt≤ M := (st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans woy
  have wrows : (Val.list rows).wt≤ M := (st_wt_mem (List.mem_of_getElem? hx)).trans wx
  have wf : (Val.list [.list fiber,.nat j]).wt≤ M := (itcs_det_weight hfront).trans cF
  have wfi : (Val.list fiber).wt≤ M := (st_wt_mem (List.mem_cons_self ..)).trans wf
  have wj : (Val.nat j).wt≤ M := (st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans wf
  have hn : fiber.length≤ M := (length_lt_wt_list fiber).le.trans wfi
  have hq : rows.length≤ M := (length_lt_wt_list rows).le.trans wrows
  have wn : (Val.nat fiber.length).wt≤ M+2 := (wt_nat_le _).trans (Nat.add_le_add_right hn 2)
  have wr := (itcs_det_weight hr).trans cR
  have wb := (itcs_det_weight hb).trans cB
  have wg := (itcs_det_weight ht).trans cT
  have read {env : List Val} {e : Expr} {ls : List Val} {i n : ℕ} {z : Val}
      (he : StDC Pg env e (.list ls) n 0 Bw) (hi : ls[i]?=some z)
      (hw : z.wt≤ Bw) (hii : i+2≤ Bw) : StDC Pg env (.get e (.nat i)) z (n+2) 0 Bw :=
    StDC.get (vs:=ls) (x:=i) (na:=n) (nb:=1) (Ea:=0) (Eb:=0) he (StDC.nat i hii) hi hw
  have argd {rest : List Val} {i : ℕ} {z : Val}
      (hi : [kv,tb,Val.list [.nat 2,.list xc],.list [.nat 2,.list yc],wk][i]?=some z) (hw : z.wt≤ Bw)
      (hii : i+2≤ Bw) : StDC Pg (inp::rest) (arg i) z 3 0 Bw := StDC.arg hi (wi.trans mb) hii hw
  have xd (rest : List Val) := read (argd (i:=2) rfl (wox.trans mb) (by omega) (rest:=rest))
    (i:=1) rfl (wx.trans mb) (by omega)
  have yd (rest : List Val) := read (argd (i:=3) rfl (woy.trans mb) (by omega) (rest:=rest))
    (i:=1) rfl (wy.trans mb) (by omega)
  have rowsd (rest : List Val) := read (xd rest) hx (wrows.trans mb) (by omega)
  have fd {rest : List Val} : StDC Pg (inp::.list [.list fiber,.nat j]::rest)
      (.get (.var 1) (.nat 0)) (.list fiber) 3 0 Bw :=
    read (StDC.var' (i:=1) rfl (wf.trans mb)) (i:=0) rfl (wfi.trans mb) (by omega)
  have jd {rest : List Val} : StDC Pg (inp::.list [.list fiber,.nat j]::rest)
      (.get (.var 1) (.nat 1)) (.nat j) 3 0 Bw :=
    read (StDC.var' (i:=1) rfl (wf.trans mb)) (i:=1) rfl (wj.trans mb) (by omega)
  have nd {rest : List Val} := StDC.length (fd (rest:=rest)) (show fiber.length+2≤ Bw by omega)
  have square {rest : List Val} : StDC Pg (inp::.list [.list fiber,.nat j]::rest)
      (.arith .mul (.length (.get (.var 1) (.nat 0))) (.length (.get (.var 1) (.nat 0))))
      (.nat (fiber.length*fiber.length)) 9 0 Bw := by
    have hsq := Nat.mul_le_mul hn hn
    have hw := wt_nat_le (fiber.length*fiber.length)
    have hw' : (Val.nat (fiber.length*fiber.length)).wt≤ Bw := by
      rw [Nat.pow_two] at mm
      dsimp only [Bw]
      rw [Nat.pow_two]
      omega
    exact StDC.arith (na:=4) (nb:=4) (Ea:=0) (Eb:=0) nd nd rfl hw'
  have test : StDC Pg [inp,.list [.list fiber,.nat j]]
      (.arith .lt (.get (.var 1) (.nat 1))
        (.arith .mul (.length (.get (.var 1) (.nat 0))) (.length (.get (.var 1) (.nat 0)))))
      (.nat (if j<fiber.length*fiber.length then 1 else 0)) 13 0 Bw := by
    apply StDC.arith jd square
    · simp [GI.Machine.BinOp.eval]
    · split_ifs <;> exact (wt_nat_le _).trans (by omega)
  have pass (hj : j<fiber.length*fiber.length) : itcsAC Pg [inp,.list [.list fiber,.nat j]]
      (.letE (.call pc (mk2 (mk3 (.get (.get (arg 2) (.nat 1)) (.nat 0))
        (.get (.var 1) (.nat 0)) (.length (.get (.var 1) (.nat 0)))) (.get (.var 1) (.nat 1))))
        (itcsResE (.call imp (mk3 (.get (arg 2) (.nat 1)) (.get (arg 3) (.nat 1)) (.var 2)))))
      P 200 (Cp+Ci) Bw := by
    have wv : v.wt≤ M := (itcs_det_weight (hpc hj)).trans cP
    have wo : ovs.wt≤ M := (itcs_det_weight (himp hj)).trans cI
    have wrs : (itcsResV ovs).wt≤ Bw := (itcs_res_weight _).trans (by dsimp only [Bw]; omega)
    have wa : (Val.list [.list [.list rows,.list fiber,.nat fiber.length],.nat j]).wt≤ Bw := by
      have h := wt_list3_le (.list rows) (.list fiber) (.nat fiber.length)
      have hh := wt_list2_le (.list [.list rows,.list fiber,.nat fiber.length]) (.nat j)
      dsimp only [Bw]; omega
    have wctx : (Val.list [.list rows,.list fiber,.nat fiber.length]).wt≤ Bw :=
      (st_wt_mem (List.mem_cons_self ..)).trans wa
    have args := StDC.mk2 (StDC.mk3 (rowsd [.list [.list fiber,.nat j]]) fd nd wctx (by omega)) jd wa (by omega)
    have pcCall := StDC.call args (hpc hj) (wv.trans mb)
    have wiargs : (Val.list [.list xc,.list yc,v]).wt≤ Bw := by
      have h := wt_list3_le (.list xc) (.list yc) v; dsimp only [Bw]; omega
    have impCall := StDC.call (StDC.mk3 (xd [.list [.list fiber,.nat j],v]) (yd _)
      (StDC.var' (i:=2) rfl (wv.trans mb)) wiargs (by omega)) (himp hj) (wo.trans mb)
    have done := itcs_res_dc impCall wrs (by omega)
    exact (itcsAC.of_dc (StDC.letE pcCall done wrs) (hipost hj) wrs).mono (by omega) (by omega)
  have otherwise (hnot : ¬j<fiber.length*fiber.length) : itcsAC Pg [inp,.list [.list fiber,.nat j]]
      (.letE (.call rng (.length (.get (.get (arg 2) (.nat 1)) (.nat 0))))
        (.letE (.call bal (mk2 (.get (arg 2) (.nat 1)) (.var 2)))
          (.ite (.call baltest (mk2 (mk2 (.var 3) (.length (.get (.var 1) (.nat 0)))) (.get (.var 1) (.nat 0))))
            (itcsResE (.call part (mk2 (.get (arg 2) (.nat 1)) (.get (arg 3) (.nat 1)))))
            (.letE (.call cert (.get (arg 2) (.nat 1)))
              (.call rect (mk4 (.var 0) (.get (.var 1) (.nat 0)) (.var 3) (.var 4)))))))
      P 600 (Cr+Cb+Ct+Cpart+Ccert+Crect) Bw := by
    have rangeCall := StDC.call (StDC.length (rowsd [.list [.list fiber,.nat j]]) (show rows.length+2≤ Bw by omega)) hr (wr.trans mb)
    have wba : (Val.list [.list xc,range]).wt≤ Bw := by have h := wt_list2_le (.list xc) range; dsimp only [Bw]; omega
    have balCall := StDC.call (StDC.mk2 (xd [.list [.list fiber,.nat j],range])
      (StDC.var' (i:=2) rfl (wr.trans mb)) wba (by omega)) hb (wb.trans mb)
    have wta : (Val.list [.list [bx,.nat fiber.length],.list fiber]).wt≤ Bw := by
      have h := wt_list2_le bx (.nat fiber.length)
      have hh := wt_list2_le (.list [bx,.nat fiber.length]) (.list fiber)
      dsimp only [Bw]; omega
    have wtctx : (Val.list [bx,.nat fiber.length]).wt≤ Bw := (st_wt_mem (List.mem_cons_self ..)).trans wta
    have args := StDC.mk2 (StDC.mk2 (StDC.var' (i:=3) (env:=[inp,.list [.list fiber,.nat j],range,bx]) rfl (wb.trans mb)) nd wtctx (by omega)) fd wta (by omega)
    have testCall := StDC.call args ht (wg.trans mb)
    have yes (hg : g≠0) : itcsAC Pg [inp,.list [.list fiber,.nat j],range,bx]
        (itcsResE (.call part (mk2 (.get (arg 2) (.nat 1)) (.get (arg 3) (.nat 1))))) P 100 Cpart Bw := by
      have wo := (itcs_det_weight (hpart hnot hg)).trans cPart
      have wres : (itcsResV povs).wt≤ Bw := (itcs_res_weight _).trans (by dsimp only [Bw]; omega)
      have wargs : (Val.list [.list xc,.list yc]).wt≤ Bw := by have h := wt_list2_le (.list xc) (.list yc); dsimp only [Bw]; omega
      have call := StDC.call (StDC.mk2 (xd [.list [.list fiber,.nat j],range,bx]) (yd _) wargs (by omega)) (hpart hnot hg) (wo.trans mb)
      exact (itcsAC.of_dc (itcs_res_dc call wres (by omega)) (hppost hnot hg) wres).mono (by omega) (by omega)
    have no (hg0 : g=0) := by
      have certC : FunAll Pg cert (.list xc) (fun cv cost => (R cv ∧ cv.wt≤ Ccert) ∧ cost≤ Ccert) :=
        (hcert hnot hg0).wt_lt.mono fun cv cost hh => ⟨⟨hh.1.1,hh.2.le.trans hh.1.2⟩,hh.1.2⟩
      have certCall := itcsAC.call (xd [.list [.list fiber,.nat j],range,bx]) certC (cCert.trans mb)
      have after : ∀ cv, (R cv ∧ cv.wt≤ Ccert) → cv.wt≤ Bw → itcsAC Pg
          [inp,.list [.list fiber,.nat j],range,bx,cv]
          (.call rect (mk4 (.var 0) (.get (.var 1) (.nat 0)) (.var 3) (.var 4))) P 100 Crect Bw := by
        intro cv ⟨hcv,wcv⟩ _
        have wcv' := wcv.trans cCert
        have wa : (Val.list [inp,.list fiber,bx,cv]).wt≤ Bw := by
          have h := wt_list4_le inp (.list fiber) bx cv
          dsimp only [Bw]; omega
        have args := StDC.mk4 (StDC.var' (i:=0) (env:=[inp,.list [.list fiber,.nat j],range,bx,cv]) rfl (wi.trans mb)) fd
          (StDC.var' (i:=3) rfl (wb.trans mb)) (StDC.var' (i:=4) rfl (wcv'.trans mb)) wa (by omega)
        exact (itcsAC.call args (hrect cv hnot hg0 hcv) (cRect.trans mb)).mono (by omega) (by omega)
      exact itcsAC.letE certCall after
    have branches := itcsAC.ite testCall yes no
    exact (itcsAC.let_dc rangeCall (itcsAC.let_dc balCall branches)).mono (by omega) (by omega)
  have branches := itcsAC.ite test
    (fun h => pass (by split_ifs at h with hj <;> simp_all)) (fun h => otherwise (by split_ifs at h with hj <;> simp_all))
  have frontCall := StDC.call (xd []) hfront (wf.trans mb)
  have body := itcsAC.let_dc frontCall branches
  have body' : itcsAC Pg [inp] (itcsStartF front pc rng bal baltest imp part cert rect)
      P 1000 (Cf+Cp+Ci+Cr+Cb+Ct+Cpart+Ccert+Crect) Bw := body.mono (by omega) (by omega)
  exact itcsAC.funAll hf body' (by simp only [itcsStartC,Bw,M,inp,Nat.add_assoc]; exact le_refl _)

end GI.Impl
