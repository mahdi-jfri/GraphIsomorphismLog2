import Workspace.Impl.AggItemHvInitB

/-!
# Case 2a: the init program as one list

`itHvConc b IC` is the init program of Case 2a with all its functions, as one list to be placed
at `b` (181 entries, `length_itHvConc`). It uses the Case 1 helpers at `IC` (range, count,
compose, append, the label data, the swap table and the parity) and the primitives
**NormalizedFactor** at `3` and **PointwiseStab** at `0`. The module `kr` is `krFuns … 0`
(`ab_krOK`).

`it_hvConc_initOK`: if a program has `itHvConc b IC` at `b` and the Case 1 helpers at `IC`, then
it meets `ItHvInitOK I P F b (itHvXh hfac hst)` for every interface `I`, and `itHvXh_pbu` shows
the bound is polynomial.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (PointwiseStab NormalizedFactor)

set_option maxRecDepth 100000

/-- **The init program of Case 2a with all its functions**, at base `b`. -/
noncomputable def itHvConc (b : ℕ) (IC : ItC1Idx) : List Expr :=
  [itHvIF (b + 1) (b + 2)] ++
  ([itHvPreF (b + 9) (b + 14)] ++
  ([itHvMF (b + 3) (b + 83) (b + 103) (b + 4)] ++
  ([itHvDaF (b + 51) (b + 56) (b + 57) (b + 161) (b + 177)] ++
  ([itHvOutF (b + 5)] ++
  (gatherFuns (b + 5) ++
  ([itGrpF IC.rng (b + 10) IC.app] ++
  (mapFuns (b + 10) (b + 13) ++
  ([itSndF] ++
  ([itDomF (b + 15) IC.rng (b + 47)] ++
  (orbitFuns (b + 15) ++
  (filterFuns (b + 47) (b + 50) ++
  ([acpDomF IC.cnt] ++
  ([itHvIndF IC.rng (b + 52)] ++
  (mapFuns (b + 52) (b + 55) ++
  ([itHvIndB IC.cnt] ++
  ([itHvSgF IC.dat IC.swt IC.cmp IC.par] ++
  ([itHvLcF IC.rng (b + 58) (b + 79)] ++
  ([grpF (b + 59) (b + 72)] ++
  (pEncMapFuns (b + 59) ++
  (mkGroupFuns (b + 72) ++
  (fstMapFuns (b + 79) ++
  ([itHvLtF (b + 84) IC.rng IC.cmp] ++
  ([liftLabF (b + 85) (b + 94) 3] ++
  ([.nil] ++
  ([shiftAppF (b + 87) (b + 90)] ++
  (appendFuns (b + 87) ++
  (mapFuns (b + 90) (b + 93) ++
  ([addKF] ++
  (pSplitFuns (b + 94) ++
  ([itHvKgF (b + 104) (b + 108) (b + 141)] ++
  (mapFuns (b + 104) (b + 107) ++
  ([addKF] ++
  (graphStabFuns (b + 108) 0 ++
  (krFuns (b + 141) 0 ++
  ([itHvAF (b + 162) (b + 171)] ++
  (findFuns (b + 162) (b + 165) ++
  ([itHvChF (b + 166) IC.par] ++
  ([itHvRsF IC.rng (b + 167)] ++
  (mapFuns (b + 167) (b + 170) ++
  ([itHvRsB] ++
  ([itHvSchF IC.rng (b + 172)] ++
  (mapFuns (b + 172) (b + 175) ++
  ([itHvSchB (b + 165) (b + 176)] ++
  ([itHvPmF IC.cmp] ++
  (mapFuns (b + 177) (b + 180) ++
  ([itHvFstB]))))))))))))))))))))))))))))))))))))))))))))))

theorem length_itHvConc (b : ℕ) (IC : ItC1Idx) : (itHvConc b IC).length = 181 := rfl

/-- The places of the functions of `itHvConc b IC`. -/
def itHvJ (b : ℕ) : ItHvIIdx where
  f0 := b + 0
  pre := b + 1
  m := b + 2
  da := b + 3
  out := b + 4
  col := b + 5
  grp := b + 9
  mpG := b + 10
  sf := b + 13
  dom := b + 14
  orb := b + 15
  fd := b + 47
  pd := b + 50
  ind := b + 51
  mpI := b + 52
  ib := b + 55
  sg := b + 56
  lc := b + 57
  gr := b + 58
  en := b + 59
  mkg := b + 72
  fm := b + 79
  lt := b + 83
  lift := b + 84
  sb := b + 85
  sp := b + 94
  kg := b + 103
  am := b + 104
  ak := b + 107
  stab := b + 108
  kr := b + 141
  af := b + 161
  fdA := b + 162
  ch := b + 165
  rs := b + 166
  mpR := b + 167
  rb := b + 170
  sch := b + 171
  mpA := b + 172
  sbA := b + 175
  pm := b + 176
  fst := b + 177
  fb := b + 180
  jfac := 3
  jp := 0

/-- The bound of the Case 2a init program in the layout. -/
noncomputable def itHvXh (hfac : NormalizedFactor) (hst : PointwiseStab) (W : ℕ) : ℕ :=
  itHvIX (normalizedFactorPrim hfac) (pointwiseStabPrim hst) (abKrC hst) W

theorem itHvXh_pbu (hfac : NormalizedFactor) (hst : PointwiseStab) :
    PBU fun _ W _ => itHvXh hfac hst W :=
  itHvIX_pbu _ hst

private theorem itHv_peel {P : Program} {b N n N' : ℕ} {A B : List Expr}
    (h : P.HasAt (b + N) (A ++ B)) (hl : A.length = n) (hN : N + n = N') :
    P.HasAt (b + N) A ∧ P.HasAt (b + N') B := by
  refine ⟨h.left, ?_⟩
  have h2 := h.right
  rw [hl, Nat.add_assoc, hN] at h2
  exact h2

set_option maxHeartbeats 4000000 in
/-- The function table `ItHvIOk` of `itHvConc b IC`. -/
theorem itHvConc_ok (hfac : NormalizedFactor) (hst : PointwiseStab) {P : Program} {b : ℕ}
    {IC : ItC1Idx} (h : P.HasAt b (itHvConc b IC))
    (hjf : P.prims[3]? = some (normalizedFactorPrim hfac))
    (hjp : P.prims[0]? = some (pointwiseStabPrim hst)) :
    ItHvIOk P (itHvJ b) IC hfac hst (abKrC hst) := by
  have h : P.HasAt (b + 0) (itHvConc b IC) := h
  unfold itHvConc at h
  obtain ⟨x_f0, h⟩ := itHv_peel (N' := 1) h rfl rfl
  obtain ⟨x_pre, h⟩ := itHv_peel (N' := 2) h rfl rfl
  obtain ⟨x_m, h⟩ := itHv_peel (N' := 3) h rfl rfl
  obtain ⟨x_da, h⟩ := itHv_peel (N' := 4) h rfl rfl
  obtain ⟨x_out, h⟩ := itHv_peel (N' := 5) h rfl rfl
  obtain ⟨x_col, h⟩ := itHv_peel (N' := 9) h rfl rfl
  obtain ⟨x_grp, h⟩ := itHv_peel (N' := 10) h rfl rfl
  obtain ⟨x_mpG, h⟩ := itHv_peel (N' := 13) h rfl rfl
  obtain ⟨x_sf, h⟩ := itHv_peel (N' := 14) h rfl rfl
  obtain ⟨x_dom, h⟩ := itHv_peel (N' := 15) h rfl rfl
  obtain ⟨x_orb, h⟩ := itHv_peel (N' := 47) h rfl rfl
  obtain ⟨x_fd, h⟩ := itHv_peel (N' := 50) h rfl rfl
  obtain ⟨x_pd, h⟩ := itHv_peel (N' := 51) h rfl rfl
  obtain ⟨x_ind, h⟩ := itHv_peel (N' := 52) h rfl rfl
  obtain ⟨x_mpI, h⟩ := itHv_peel (N' := 55) h rfl rfl
  obtain ⟨x_ib, h⟩ := itHv_peel (N' := 56) h rfl rfl
  obtain ⟨x_sg, h⟩ := itHv_peel (N' := 57) h rfl rfl
  obtain ⟨x_lc, h⟩ := itHv_peel (N' := 58) h rfl rfl
  obtain ⟨x_gr, h⟩ := itHv_peel (N' := 59) h rfl rfl
  obtain ⟨x_en, h⟩ := itHv_peel (N' := 72) h rfl rfl
  obtain ⟨x_mkg, h⟩ := itHv_peel (N' := 79) h rfl rfl
  obtain ⟨x_fm, h⟩ := itHv_peel (N' := 83) h rfl rfl
  obtain ⟨x_lt, h⟩ := itHv_peel (N' := 84) h rfl rfl
  obtain ⟨x_lift, h⟩ := itHv_peel (N' := 85) h rfl rfl
  obtain ⟨x_sb, h⟩ := itHv_peel (N' := 86) h rfl rfl
  obtain ⟨x_sb1, h⟩ := itHv_peel (N' := 87) h rfl rfl
  obtain ⟨x_sb2, h⟩ := itHv_peel (N' := 90) h rfl rfl
  obtain ⟨x_sb5, h⟩ := itHv_peel (N' := 93) h rfl rfl
  obtain ⟨x_sb8, h⟩ := itHv_peel (N' := 94) h rfl rfl
  obtain ⟨x_sp, h⟩ := itHv_peel (N' := 103) h rfl rfl
  obtain ⟨x_kg, h⟩ := itHv_peel (N' := 104) h rfl rfl
  obtain ⟨x_am, h⟩ := itHv_peel (N' := 107) h rfl rfl
  obtain ⟨x_ak, h⟩ := itHv_peel (N' := 108) h rfl rfl
  obtain ⟨x_stab, h⟩ := itHv_peel (N' := 141) h rfl rfl
  obtain ⟨x_kr, h⟩ := itHv_peel (N' := 161) h rfl rfl
  obtain ⟨x_af, h⟩ := itHv_peel (N' := 162) h rfl rfl
  obtain ⟨x_fdA, h⟩ := itHv_peel (N' := 165) h rfl rfl
  obtain ⟨x_ch, h⟩ := itHv_peel (N' := 166) h rfl rfl
  obtain ⟨x_rs, h⟩ := itHv_peel (N' := 167) h rfl rfl
  obtain ⟨x_mpR, h⟩ := itHv_peel (N' := 170) h rfl rfl
  obtain ⟨x_rb, h⟩ := itHv_peel (N' := 171) h rfl rfl
  obtain ⟨x_sch, h⟩ := itHv_peel (N' := 172) h rfl rfl
  obtain ⟨x_mpA, h⟩ := itHv_peel (N' := 175) h rfl rfl
  obtain ⟨x_sbA, h⟩ := itHv_peel (N' := 176) h rfl rfl
  obtain ⟨x_pm, h⟩ := itHv_peel (N' := 177) h rfl rfl
  obtain ⟨x_fst, h⟩ := itHv_peel (N' := 180) h rfl rfl
  exact
    { f0 := x_f0.single
      pre := x_pre.single
      m := x_m.single
      da := x_da.single
      out := x_out.single
      col := x_col
      grp := x_grp.single
      mpG := x_mpG
      sf := x_sf.single
      dom := x_dom.single
      orb := x_orb
      fd := x_fd
      pd := x_pd.single
      ind := x_ind.single
      mpI := x_mpI
      ib := x_ib.single
      sg := x_sg.single
      lc := x_lc.single
      gr := x_gr.single
      en := x_en
      mkg := x_mkg
      fm := x_fm
      lt := x_lt.single
      lift := x_lift.single
      sb := ⟨x_sb1.single, x_sb2, x_sb5, x_sb8.single⟩
      sp := x_sp
      kg := x_kg.single
      am := x_am
      ak := x_ak.single
      stab := x_stab
      kr := ab_krOK hst x_kr hjp
      af := x_af.single
      fdA := x_fdA
      ch := x_ch.single
      rs := x_rs.single
      mpR := x_mpR
      rb := x_rb.single
      sch := x_sch.single
      mpA := x_mpA
      sbA := x_sbA.single
      pm := x_pm.single
      fst := x_fst
      fb := h.single
      jfac := hjf
      jp := hjp
      krm := abKrC_mono hst }

/-- **The init program of Case 2a meets `ItHvInitOK`** at its place `b`, for every interface. -/
theorem it_hvConc_initOK (I : Iface) (hfac : NormalizedFactor) (hst : PointwiseStab)
    {P : Program} {F : Funs} {b : ℕ} {IC : ItC1Idx} (hc1 : ItC1Ok P IC)
    (h : P.HasAt b (itHvConc b IC)) (hjf : P.prims[3]? = some (normalizedFactorPrim hfac))
    (hjp : P.prims[0]? = some (pointwiseStabPrim hst)) :
    ItHvInitOK I P F b (itHvXh hfac hst) :=
  it_hvInitOK I hfac hst hc1 (itHvConc_ok hfac hst h hjf hjp)

end GI.Impl
