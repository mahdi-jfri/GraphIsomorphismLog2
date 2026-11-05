module

public import Workspace.Impl.AggItemSrcP

@[expose] public section

/-!
# The structure step of the items

The items start by computing what fixes the round's free fields (`itRound`): the refined tuple
colorings `(d, d')` of the two strings, the case of `π(F_x)`, and the source tuple. The program
`itStrF` on the start state `st` returns `[st, [d, d'], code, src]`:
1. `w = [d, d']`: the joint refinement of the two class colorings (`it_col_spec`, one call of the
   cited **KaryRefinement κ**);
2. `code`: the case code of the group of the second parts of `fx` (`it_case_spec`, with the
   cited **PointwiseStab** and **GroupOrder**);
3. `src`: the entries of the source tuple (`it_srcp_spec`).

`it_str_spec` states the result in terms of the round: for the joint refinement
`J = stSetJ Ag.hK … d d'` (the value of `hK` replaced at the class colorings by `(d, d')`), the
code is that of `aggCase (itX0 Ag J).grp` and the source tuple is `itSrc Ag J`, the source tuple of
the round `itRound Ag J` (`ItStrOut`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encPts encKColoring PointwiseStab GroupOrder)

variable {Ω C : Type} {k : ℕ}

/-- **What the structure step returns**: `v = [st, [d, d'], code, src]` for a joint refinement
`(d, d')` of the class colorings of the round (with colors below `2 q^κ`), where, for the joint
refinement `J` that takes the value `(d, d')` at the class colorings, `code` is the case code of
`π(F_x)` and `src` lists the entries of the source tuple `itSrc Ag J`. -/
def ItStrOut {S : State Ω C} {L : GiantLabels S} (Ag : Aggregation P₀ S L) (st v : Val) : Prop :=
  haveI := Ag.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  ∃ (d d' : (Fin P₀.κ → Fin L.q) → ℕ)
    (hJ : JointOK (tcol S Ag.πd P₀.κ (itNum Ag) (dstr S S.x))
      (tcol S Ag.πd P₀.κ (itNum Ag) (dstr S S.y)) d d'),
    (∀ x, d x < 2 * L.q ^ P₀.κ) ∧ (∀ x, d' x < 2 * L.q ^ P₀.κ) ∧
    v = .list [st, .list [encKColoring d, encKColoring d'],
      .nat (AggCase.code (aggCase (itX0 Ag (stSetJ Ag.hK L.q P₀.κ _ _ d d' hJ)).grp)),
      natList (stL fun i => (itSrc Ag (stSetJ Ag.hK L.q P₀.κ _ _ d d' hJ) i : ℕ))]

/-- On the items' start state: `[st, [d, d'], code, src]`. -/
def itStrF (col cse sp : ℕ) : Expr :=
  .letE (.call col (.var 0))
    (.letE (.call cse (.var 0))
      (mk4 (.var 0) (.var 1) (.var 2) (.call sp (mk3 (.var 0) (.var 1) (.var 2)))))

/-- The cost bound of `itStrF` besides the cited refinement call, for the size parameter `M`. -/
noncomputable def itStrC (hst : PointwiseStab) (hO : GroupOrder) (M : ℕ) : ℕ :=
  itColC M + itCaseC hst hO M + itSrcPC M + 10 ^ 4 * (M + 1) ^ 2

/-- The group of the second parts of `fx` is that of the structures of the round, for every
joint refinement. -/
theorem it_gens_itX0 (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S}
    (Ag : Aggregation P₀ S L) {fx : List (Perm (Fin k) × Perm (Fin L.q))}
    (h : PairGens e L (itCertLift Ag.fin S Ag.πd P₀.κ S.x) fx) (J : JointFn) :
    gens (fx.map Prod.snd) = (itX0 Ag J).grp :=
  it_gens_strX e Ag h fun _ => ⟨0, it_q_pos Ag⟩

set_option maxHeartbeats 2000000 in
/-- **The structure step.** On the items' start state, `itStrF` returns `[st, [d, d'], code, src]`
as described by `ItStrOut`. -/
theorem it_str_spec (hk : GI.Cited.KaryRefinement P₀.κ) (hst : PointwiseStab) (hO : GroupOrder)
    {P : Program} {f col cse sp ts pw rb mp tv dc bc brel fr brep jk acp grp mp' sf app
      dom s2b s3 rep orb fd pd cnt fs sp' des : ℕ}
    (hf : P.funs[f]? = some (itStrF col cse sp))
    (hcol : P.funs[col]? = some (itColF ts bc fr P₀.κ))
    (hts : P.funs[ts]? = some (itTsF pw rb mp)) (hpw : P.HasAt pw (stDPowFuns pw))
    (hrb : P.HasAt rb (rangeFuns rb)) (hmp : P.HasAt mp (mapFuns mp tv))
    (htv : P.funs[tv]? = some (itTvF dc)) (hdc : P.HasAt dc (stDDecFuns dc))
    (hbc : P.HasAt bc (stColsFuns bc brel)) (hrel : P.HasAt brel (stRelFuns brel))
    (hfr : P.funs[fr]? = some (stRefF brep jk)) (hrep' : P.HasAt brep (replicateFuns brep))
    (hjk : P.prims[jk]? = some (karyRefinementPrim hk))
    (hcse : P.funs[cse]? = some (itCaseF acp grp)) (hacp : ItCaseOK P acp hst hO)
    (hgrp : P.funs[grp]? = some (itGrpF rb mp' app)) (hmp' : P.HasAt mp' (mapFuns mp' sf))
    (hsf : P.funs[sf]? = some itSndF) (happ : P.HasAt app (appendFuns app))
    (hsp : P.funs[sp]? = some (itSrcF grp dom s2b s3 rep P₀.κ))
    (hdom : P.funs[dom]? = some (itDomF orb rb fd)) (horb : P.HasAt orb (orbitFuns orb))
    (hfd : P.HasAt fd (filterFuns fd pd))
    (hpd : P.funs[pd]? = some (acpDomF cnt)) (hcnt : P.HasAt cnt (countFuns cnt))
    (hs2b : P.funs[s2b]? = some (itS2bF app rep P₀.κ)) (hrep : P.HasAt rep (replicateFuns rep))
    (hs3 : P.funs[s3]? = some (stDSrcF pw fs rb dc))
    (hfs : P.HasAt fs (findFuns fs sp')) (hsp' : P.funs[sp']? = some (stDSrcPF des dc))
    (hdes : StDesOK P des)
    (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S} (Ag : Aggregation P₀ S L) (sv : Val)
    (ps fx fy : List (Perm (Fin k) × Perm (Fin L.q))) (O : TestTupleOrder L.q P₀.κ)
    (hfx : PairGens e L (itCertLift Ag.fin S Ag.πd P₀.κ S.x) fx) {M : ℕ}
    (hM : (itSt sv k L.q ps fx fy O.tuples (itCr Ag.fin S Ag.πd P₀.κ)).wt + L.q ^ P₀.κ + L.q +
      P₀.κ ≤ M) :
    FunAll P f (itSt sv k L.q ps fx fy O.tuples (itCr Ag.fin S Ag.πd P₀.κ)) (fun v cost =>
      ItStrOut Ag (itSt sv k L.q ps fx fy O.tuples (itCr Ag.fin S Ag.πd P₀.κ)) v ∧
      cost ≤ itStrC hst hO M + (karyRefinementPrim hk).bound
        (haveI := Ag.fin
         letI : Fintype S.dom := Fintype.ofFinite _
         letI : DecidableEq S.dom := Classical.decEq _
         karyEnc (tcol S Ag.πd P₀.κ (itNum Ag) (dstr S S.x))
          (tcol S Ag.πd P₀.κ (itNum Ag) (dstr S S.y))) ∧
      v.wt ≤ 100 * (M + 1) ^ 2) := by
  haveI := Ag.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  have hq24 : 24 ≤ L.q := by have := it_q_large Ag; have := Ag.params.κ_seven; omega
  set st := itSt sv k L.q ps fx fy O.tuples (itCr Ag.fin S Ag.πd P₀.κ) with hstd
  have hst' : st = itSt sv k L.q ps fx fy O.tuples
      (stCr S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y)) := rfl
  obtain ⟨hc0, hc1⟩ := it_cz_tcol Ag
  have hC := it_col_spec hk hcol hts hpw hrb hmp htv hdc hbc hrel hfr hrep' hjk S Ag.πd
    (dstr S S.x) (dstr S S.y) O sv k (ps := ps) (fx := fx) (fy := fy) (it_q_pos Ag) (M := M)
    (by rw [← hst']; exact hM)
  rw [← hst', hc0, hc1] at hC
  have hMq : L.q ≤ M := by omega
  have hstM : st.wt ≤ M := by omega
  set c₀ := tcol S Ag.πd P₀.κ (itNum Ag) (dstr S S.x) with hc₀
  set c₁ := tcol S Ag.πd P₀.κ (itNum Ag) (dstr S S.y) with hc₁
  set B := (karyRefinementPrim hk).bound (karyEnc c₀ c₁) with hB
  refine FunAll.intro hf (EvalAll.letE (Ra := fun w c => KaryOut c₀ c₁ w ∧
      c ≤ st.wt + 1 + (itColC M + B) + w.wt + 1)
    (EvalAll.call_funAll (Det.var' (P := P) (env := [st]) (i := 0) rfl) fun v0 c0 h0 => ?_)
    fun w cw hw => ?_)
  · obtain ⟨rfl, hc0'⟩ := h0
    exact hC.mono fun w cb hw => ⟨hw.1, by have := hw.2; omega⟩
  · obtain ⟨⟨d, d', rfl, hd, hd', hJR⟩, hcw⟩ := hw
    have hJ : JointOK c₀ c₁ d d' := st_jointOK hJR
    set J := stSetJ Ag.hK L.q P₀.κ c₀ c₁ d d' hJ with hJdef
    have hg : gens (fx.map Prod.snd) = (itX0 Ag J).grp := it_gens_itX0 e Ag hfx J
    have hcl : (itX0 Ag J).col = d :=
      (stSetJ_col Ag.fin S L Ag.πd Ag.hK P₀.κ (itNum Ag) d d' hJ fun _ => ⟨0, it_q_pos Ag⟩).1
    have hsrc : itSrcOf (gens (fx.map Prod.snd)) d (by omega) = itSrc Ag J := by
      rw [itSrc_eq_of, ← hg, hcl]
    set cv := Val.nat (AggCase.code (aggCase (gens (fx.map Prod.snd)))) with hcv
    set wv := Val.list [encKColoring d, encKColoring d'] with hwv
    set sr := natList (stL fun i => (itSrcOf (gens (fx.map Prod.snd)) d (by omega) i : ℕ)) with hsr
    -- the case code
    have hcs := it_case_spec hst hO hcse hacp hgrp hrb hmp' hsf happ sv ps fx fy O.tuples
      (itCr Ag.fin S Ag.πd P₀.κ) (W := M) hstM hMq
    have dcs := Det.call (Det.var' (P := P) (env := [st, wv]) (i := 0) rfl) hcs
    -- the source tuple
    have hsp2 := it_srcp_spec hsp hgrp hrb hmp' hsf happ hdom horb hrb hfd hpd hcnt hs2b hrep hs3
      hpw hfs hsp' hdes hdc hrb sv ps fx fy O.tuples (itCr Ag.fin S Ag.πd P₀.κ) d d' hd hd' hq24
      (W := M) hM
    have dsp := Det.call (Det.mk3 (Det.var' (P := P) (env := [st, wv, cv]) (i := 0) rfl)
      (Det.var' (i := 1) rfl) (Det.var' (i := 2) rfl)) hsp2
    have dout := Det.letE dcs (Det.mk4 (Det.var' (P := P) (env := [st, wv, cv]) (i := 0) rfl)
      (Det.var' (i := 1) rfl) (Det.var' (i := 2) rfl) dsp)
    refine dout.post fun c hc => ?_
    -- weights
    have wd := wt_encKColoring_le hd
    have wd' := wt_encKColoring_le hd'
    have hww : wv.wt ≤ _ := wt_list2_le (encKColoring d) (encKColoring d')
    have hqκ : (L.q ^ P₀.κ + 1) ^ 2 ≤ (M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hcode := it_code_le (aggCase (gens (fx.map Prod.snd)))
    have hcw : cv.wt ≤ 5 := (wt_nat_le _).trans (by omega)
    have hsw : sr.wt ≤ 5 * (M + 1) ^ 2 := it_wt_src _ (by omega) (by omega)
    have hm3 : (Val.list [st, wv, .nat (AggCase.code (aggCase (gens (fx.map Prod.snd))))]).wt ≤
        2 * (st.wt + wv.wt + cv.wt) + 7 := wt_list3_le st wv cv
    have hm4 : (Val.list [st, wv, .nat (AggCase.code (aggCase (gens (fx.map Prod.snd)))),
        natList (stL fun i => (itSrcOf (gens (fx.map Prod.snd)) d (by omega) i : ℕ))]).wt ≤
        2 * (st.wt + wv.wt + cv.wt + sr.wt) + 8 := wt_list4_le st wv cv sr
    have e3 : (Val.list [st, wv, cv]).wt =
        (Val.list [st, wv, .nat (AggCase.code (aggCase (gens (fx.map Prod.snd))))]).wt := rfl
    have ecv : (Val.nat (AggCase.code (aggCase (gens (fx.map Prod.snd))))).wt = cv.wt := rfl
    have esr : (natList (stL fun i => (itSrcOf (gens (fx.map Prod.snd)) d (by omega) i : ℕ))).wt =
      sr.wt := rfl
    have hM1 : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    refine ⟨⟨d, d', hJ, hd, hd', ?_⟩, ?_, by omega⟩
    · rw [hsrc, hg]
    · unfold itStrC
      omega

/-- **The bound of the refinement call is polynomial** in the size parameter `M`: the input
`karyEnc c₀ c₁` weighs at most `40 (M + 1)²`. -/
theorem it_kary_bound_le (hk : GI.Cited.KaryRefinement P₀.κ) {S : State Ω C} {L : GiantLabels S}
    (Ag : Aggregation P₀ S L) {M : ℕ} (hM : L.q ^ P₀.κ + L.q ≤ M) :
    (karyRefinementPrim hk).bound
        (haveI := Ag.fin
         letI : Fintype S.dom := Fintype.ofFinite _
         letI : DecidableEq S.dom := Classical.decEq _
         karyEnc (tcol S Ag.πd P₀.κ (itNum Ag) (dstr S S.x))
          (tcol S Ag.πd P₀.κ (itNum Ag) (dstr S S.y))) ≤
      (karyRefinementPrim hk).c * (40 * (M + 1) ^ 2 + 2) ^ (karyRefinementPrim hk).k := by
  haveI := Ag.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  obtain ⟨hc0, hc1⟩ := it_cz_tcol Ag
  rw [← hc0, ← hc1]
  unfold Prim.bound
  refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
  have w0 := it_wt_cz (stRel S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y)) 0
  have w1 := it_wt_cz (stRel S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y)) 1
  have hr : (Val.list (List.replicate L.q (Val.nat 0))).wt ≤ 5 * (M + 1) ^ 2 := by
    have := wt_natList_le_sq (xs := List.replicate L.q 0) (B := M)
      (fun x hx => by rw [List.eq_of_mem_replicate hx]; omega) (by simp; omega)
    simpa [natList] using this
  have h3 := wt_list3_le (.list (List.replicate L.q (Val.nat 0)))
    (encKColoring (stCz (stRel S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y)) 0))
    (encKColoring (stCz (stRel S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y)) 1))
  have hs := (karyEnc (stCz (stRel S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y)) 0)
    (stCz (stRel S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y)) 1)).size_le_wt
  have hqκ : (L.q ^ P₀.κ + 1) ^ 2 ≤ (M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have e : (karyEnc (stCz (stRel S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y)) 0)
      (stCz (stRel S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y)) 1)).wt =
      (Val.list [.list (List.replicate L.q (Val.nat 0)),
        encKColoring (stCz (stRel S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y)) 0),
        encKColoring (stCz (stRel S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y)) 1)]).wt := rfl
  have h1 : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

end GI.Impl
