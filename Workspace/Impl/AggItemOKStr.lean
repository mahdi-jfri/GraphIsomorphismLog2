import Workspace.Impl.AggItemOK

/-!
# The structure step meets `ItSStrOK`

`it_str_spec` gives the structure step on the hand-over state, with the size parameter
`M ≥ st.wt + q^κ + q + κ`. For a call with input weight `W₀`, the start state weighs at most
`cmOutB (2 W₀ + 3)` (`itS_stW0`), so `M = itSMs W₀` works, and the cost of the cited refinement
is polynomial in `M` (`it_kary_bound_le`). This gives `ItSStrOK` with the bound `itSXs`
(`itS_strOK`), and `itSXs` is polynomial (`itS_Xs_pbu`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encPts encKColoring PointwiseStab GroupOrder)

variable {Ω C : Type} {k : ℕ}

/-- **The weight of the start state**, from the data of the hand-over. -/
theorem itS_stW0 (I : Iface) (Pg : Program) (F : Funs) {e : Ω ≃ Fin k} {c : C → ℕ}
    {S : State Ω C} {sv lv : Val} {L : SuppliedLabels S} (hc : AsCall I Pg F e c S sv lv L)
    {sv' : Val} (hcan : Canon e c sv' S) {ps fx fy : List (Perm (Fin k) × Perm (Fin L.q))}
    (lps : ps.length ≤ (k + L.q) ^ 2) (lfx : fx.length ≤ (k + L.q) ^ 2)
    (lfy : fy.length ≤ (k + L.q) ^ 2) (O : TestTupleOrder L.q P₀.κ)
    (Ag : Aggregation P₀ S L.toGiantLabels) :
    (itSt sv' k L.q ps fx fy O.tuples (itCr Ag.fin S Ag.πd P₀.κ)).wt ≤
      cmOutB (2 * I.inW .giant S + 3) := by
  obtain ⟨hkq, hκ, hq, -, -, -⟩ := itS_size I Pg F hc
  have hsv : sv'.wt ≤ I.inW .giant S := by
    have := Canon.wt_le hcan
    simp only [Iface.inW, Iface.card_eq e]
    omega
  have htl : O.tuples.length ≤ cmNb (2 * I.inW .giant S + 3) := by
    have := itS_tt_length O
    unfold cmNb
    omega
  have hP := cm_wt_par (sv := sv') (ps := ps) (fx := fx) (fy := fy)
    (logs := ([] : List (CmLog k L.q))) (tt := O.tuples) (n := 0)
    (K := 2 * I.inW .giant S + 3) (by omega) hkq lps lfx lfy (by simp)
    (by simp) htl (by omega) (by omega)
  have e : itSt sv' k L.q ps fx fy O.tuples (itCr Ag.fin S Ag.πd P₀.κ) = cmOutV sv' k ps fx fy
      O.tuples (O.tuples.flatMap fun a => O.tuples.map (itCr Ag.fin S Ag.πd P₀.κ a)) := rfl
  rw [e]
  refine cm_wt_out hP htl ?_
  rw [List.length_flatMap]
  simp only [List.length_map]
  rw [List.map_const', List.sum_replicate, smul_eq_mul]

/-- The size parameter of the structure step. -/
def itSMs (W : ℕ) : ℕ := cmOutB (2 * W + 3) + (2 * W + 3) ^ 64 + (2 * W + 3) + 64

/-- **The bound of the structure step.** -/
noncomputable def itSXs (hk : GI.Cited.KaryRefinement P₀.κ) (hst : PointwiseStab)
    (hO : GroupOrder) (W : ℕ) : ℕ :=
  itStrC hst hO (itSMs W) +
    (karyRefinementPrim hk).c * (40 * (itSMs W + 1) ^ 2 + 2) ^ (karyRefinementPrim hk).k +
    100 * (itSMs W + 1) ^ 2

/-- **The structure step meets `ItSStrOK`** with the bound `itSXs`. -/
theorem itS_strOK (hk : GI.Cited.KaryRefinement P₀.κ) (hst : PointwiseStab) (hO : GroupOrder)
    (I : Iface) (Pg : Program) (F : Funs)
     {f col cse sp ts pw rb mp tv dc bc brel fr brep jk acp grp mp' sf app
      dom s2b s3 rep orb fd pd cnt fs sp' des : ℕ}
    (hf : Pg.funs[f]? = some (itStrF col cse sp))
    (hcol : Pg.funs[col]? = some (itColF ts bc fr P₀.κ))
    (hts : Pg.funs[ts]? = some (itTsF pw rb mp)) (hpw : Pg.HasAt pw (stDPowFuns pw))
    (hrb : Pg.HasAt rb (rangeFuns rb)) (hmp : Pg.HasAt mp (mapFuns mp tv))
    (htv : Pg.funs[tv]? = some (itTvF dc)) (hdc : Pg.HasAt dc (stDDecFuns dc))
    (hbc : Pg.HasAt bc (stColsFuns bc brel)) (hrel : Pg.HasAt brel (stRelFuns brel))
    (hfr : Pg.funs[fr]? = some (stRefF brep jk)) (hrep' : Pg.HasAt brep (replicateFuns brep))
    (hjk : Pg.prims[jk]? = some (karyRefinementPrim hk))
    (hcse : Pg.funs[cse]? = some (itCaseF acp grp)) (hacp : ItCaseOK Pg acp hst hO)
    (hgrp : Pg.funs[grp]? = some (itGrpF rb mp' app)) (hmp' : Pg.HasAt mp' (mapFuns mp' sf))
    (hsf : Pg.funs[sf]? = some itSndF) (happ : Pg.HasAt app (appendFuns app))
    (hsp : Pg.funs[sp]? = some (itSrcF grp dom s2b s3 rep P₀.κ))
    (hdom : Pg.funs[dom]? = some (itDomF orb rb fd)) (horb : Pg.HasAt orb (orbitFuns orb))
    (hfd : Pg.HasAt fd (filterFuns fd pd))
    (hpd : Pg.funs[pd]? = some (acpDomF cnt)) (hcnt : Pg.HasAt cnt (countFuns cnt))
    (hs2b : Pg.funs[s2b]? = some (itS2bF app rep P₀.κ)) (hrep : Pg.HasAt rep (replicateFuns rep))
    (hs3 : Pg.funs[s3]? = some (stDSrcF pw fs rb dc))
    (hfs : Pg.HasAt fs (findFuns fs sp')) (hsp' : Pg.funs[sp']? = some (stDSrcPF des dc))
    (hdes : StDesOK Pg des) :
    ItSStrOK I Pg F f (itSXs hk hst hO) := by
  intro Ω C k e c S sv lv L hc Ag sv' ps fx fy O hAg hcan hfx lps lfx lfy
  obtain ⟨hkq, hκ, hq, -, -, -⟩ := itS_size I Pg F hc
  have hst0 := itS_stW0 I Pg F hc hcan lps lfx lfy O Ag
  have hκ64 : P₀.κ = 64 := rfl
  have hqp : L.q ^ P₀.κ ≤ (2 * I.inW .giant S + 3) ^ 64 := by
    rw [hκ64]; exact Nat.pow_le_pow_left (by omega) 64
  have hM : (itSt sv' k L.q ps fx fy O.tuples (itCr Ag.fin S Ag.πd P₀.κ)).wt + L.q ^ P₀.κ + L.q +
      P₀.κ ≤ itSMs (I.inW .giant S) := by
    unfold itSMs; omega
  have hkb := it_kary_bound_le hk Ag (M := itSMs (I.inW .giant S)) (by unfold itSMs; omega)
  refine FunAll.mono (it_str_spec hk hst hO hf hcol hts hpw hrb hmp htv hdc hbc hrel hfr hrep' hjk
    hcse hacp hgrp hmp' hsf happ hsp hdom horb hfd hpd hcnt hs2b hrep hs3 hfs hsp' hdes e Ag sv' ps
    fx fy O hfx hM) fun v cost ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · unfold itSXs; omega
  · unfold itSXs; omega

/-- **The bound of the structure step is polynomial.** -/
theorem itS_Xs_pbu (hk : GI.Cited.KaryRefinement P₀.κ) (hst : PointwiseStab) (hO : GroupOrder) :
    PBU fun _ W _ => itSXs hk hst hO W := by
  simp only [itSXs, itSMs, itStrC, itColC, itCaseC, itSrcPC, cmOutB, cmPb, cmNb, itTsC, itTvC,
    itTvW, mapK, stDPowK, stDDecK, stColsCost, stMapCost, stColCost, acpCC, acpGC, acpPB, itGrpC, itDomC, itS2bC]
  norm_poly

end GI.Impl
