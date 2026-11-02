import Workspace.Impl.AggItemCfObj
import Workspace.Impl.FinLayoutItems

/-! # The object stage of Cases 2b/3 as one installed list

`fc8ObConc b` is a self-contained list of 214 functions for the base `b`. The three entry
functions `col`, `orb`, `des` sit at offsets 0, 1, 2. Offsets 3–31 hold the other single
functions and offsets 32–213 the library blocks (the last one, at offset 211, is the `find` block
of the anchor colors of the cell function); all their callees are inside the list. One
range block (offset 64) serves the col, orbital and design programs, one count block (offset 70)
serves the domain and the design domain, and one degree block (offset 75) serves the col and
orbital degree calls. The pointwise stabilizer is primitive `0`.

`fc8_objSpec` reads the list and applies `itCf_objSpec`.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (PointwiseStab)

/-- The design indices inside `fc8ObConc b`. -/
def fc8DIdx (b : ℕ) : ItCfDIdx where
  rb := b + 64
  cf := b + 14
  hor := b + 178
  vm := b + 15
  vmap := b + 181
  vf := b + 16
  dv := b + 17
  dvv := b + 18
  cb := b + 70
  ad := b + 184
  fd := b + 187
  rf := b + 19
  df := b + 20
  fr := b + 190
  adr := b + 193
  sp := b + 21
  hit2 := b + 22
  hit := b + 23
  fh := b + 196
  bl := b + 24
  bm := b + 199
  br := b + 25
  brm := b + 202
  bce := b + 26
  tb := b + 27
  tm := b + 205
  tr := b + 28
  trm := b + 208
  tce := b + 29
  atf := b + 30
  core := b + 31

/-- The object stage at base `b`. -/
def fc8ObConc (b : ℕ) : List Expr :=
  [itCfColF (b + 3) (b + 126) (b + 129) (b + 132) (b + 140) (b + 64) (b + 163)] ++ (
  [itCfROrbF (b + 4) (b + 9) (b + 10)] ++ (
  [itCfDesF (b + 31)] ++ (
  [itCfFrF (b + 4) (b + 75)] ++ (
  [itDomF (b + 32) (b + 64) (b + 67)] ++ (
  [acpDomF (b + 70)] ++ (
  [itCfCellF (b + 166) (b + 169) (b + 211)] ++ (
  [itCfEqP] ++ (
  [itCfPairP] ++ (
  [itCfRDegreeF (b + 75)] ++ (
  [itCfRReadF (b + 11) (b + 13)] ++ (
  [itCfRTableF (b + 172) (b + 64)] ++ (
  [itCfRRowF (b + 175) (b + 64)] ++ (
  [itCfRCellF] ++ (
  [stDColF (b + 178)] ++ (
  [stDVMapF (b + 181) (b + 64)] ++ (
  [stDVF (b + 14)] ++ (
  [stDDomF (b + 18)] ++ (
  [stDDomVF (b + 70)] ++ (
  [stDRefF] ++ (
  [stDDifF (b + 19) (b + 14)] ++ (
  [stDSplitF (b + 187) (b + 190) (b + 193) (b + 64) (b + 14)] ++ (
  [stDHit2F (b + 184) (b + 64) (b + 21)] ++ (
  [stDHitF (b + 22) (b + 15)] ++ (
  [itCfRTableF (b + 199) (b + 64)] ++ (
  [itCfRRowF (b + 202) (b + 64)] ++ (
  [itCfDBlockCellF] ++ (
  [itCfRTableF (b + 205) (b + 64)] ++ (
  [itCfRRowF (b + 208) (b + 64)] ++ (
  [itCfDPairCellF (b + 14)] ++ (
  [itCfDAtF (b + 15) (b + 184) (b + 187) (b + 64) (b + 24) (b + 27)] ++ (
  [itCfDCoreF (b + 196) (b + 64) (b + 30)] ++ (
  orbitFuns (b + 32) ++ (
  rangeFuns (b + 64) ++ (
  filterFuns (b + 67) (b + 5) ++ (
  countFuns (b + 70) ++ (
  itCfDegFuns (b + 75) 0 ++ (
  replicateFuns (b + 126) ++ (
  linTakeFuns (b + 129) ++ (
  pstabFuns (b + 132) 0 ++ (
  tupOrbFuns (b + 140) ++ (
  mapFuns (b + 163) (b + 6) ++ (
  anyFuns (b + 166) (b + 7) ++ (
  anyFuns (b + 169) (b + 8) ++ (
  mapFuns (b + 172) (b + 12) ++ (
  mapFuns (b + 175) (b + 13) ++ (
  stDHorFuns (b + 178) ++ (
  mapFuns (b + 181) (b + 16) ++ (
  anyFuns (b + 184) (b + 17) ++ (
  findFuns (b + 187) (b + 17) ++ (
  findFuns (b + 190) (b + 19) ++ (
  anyFuns (b + 193) (b + 20) ++ (
  findFuns (b + 196) (b + 23) ++ (
  mapFuns (b + 199) (b + 25) ++ (
  mapFuns (b + 202) (b + 26) ++ (
  mapFuns (b + 205) (b + 28) ++ (
  mapFuns (b + 208) (b + 29) ++
  findFuns (b + 211) (b + 7)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 20000 in
theorem fc8_obConc_length (b : ℕ) : (fc8ObConc b).length = 214 := rfl

set_option maxHeartbeats 1000000 in
/-- **The object stage meets `ItCfObjSpec`** at the base of its list, with the pointwise
stabilizer at primitive `0`. -/
theorem fc8_objSpec (hps : PointwiseStab) {P : Program} {b : ℕ}
    (h : P.HasAt b (fc8ObConc b)) (hj : P.prims[0]? = some (pointwiseStabPrim hps)) :
    ItCfObjSpec P b (b + 1) (b + 2) (itCfObjCo hps) (itCfObjDo hps) := by
  have h : P.HasAt (b + 0) (fc8ObConc b) := h
  unfold fc8ObConc at h
  obtain ⟨h_col, h⟩ := fit_peel (N' := 1) h rfl rfl
  obtain ⟨h_orb, h⟩ := fit_peel (N' := 2) h rfl rfl
  obtain ⟨h_des, h⟩ := fit_peel (N' := 3) h rfl rfl
  obtain ⟨h_fr, h⟩ := fit_peel (N' := 4) h rfl rfl
  obtain ⟨h_dom, h⟩ := fit_peel (N' := 5) h rfl rfl
  obtain ⟨h_pd, h⟩ := fit_peel (N' := 6) h rfl rfl
  obtain ⟨h_fc, h⟩ := fit_peel (N' := 7) h rfl rfl
  obtain ⟨h_pe, h⟩ := fit_peel (N' := 8) h rfl rfl
  obtain ⟨h_pp, h⟩ := fit_peel (N' := 9) h rfl rfl
  obtain ⟨h_dg, h⟩ := fit_peel (N' := 10) h rfl rfl
  obtain ⟨h_rd, h⟩ := fit_peel (N' := 11) h rfl rfl
  obtain ⟨h_tb, h⟩ := fit_peel (N' := 12) h rfl rfl
  obtain ⟨h_rw, h⟩ := fit_peel (N' := 13) h rfl rfl
  obtain ⟨h_ce, h⟩ := fit_peel (N' := 14) h rfl rfl
  obtain ⟨h_cf, h⟩ := fit_peel (N' := 15) h rfl rfl
  obtain ⟨h_vm, h⟩ := fit_peel (N' := 16) h rfl rfl
  obtain ⟨h_vf, h⟩ := fit_peel (N' := 17) h rfl rfl
  obtain ⟨h_dv, h⟩ := fit_peel (N' := 18) h rfl rfl
  obtain ⟨h_dvv, h⟩ := fit_peel (N' := 19) h rfl rfl
  obtain ⟨h_rf, h⟩ := fit_peel (N' := 20) h rfl rfl
  obtain ⟨h_df, h⟩ := fit_peel (N' := 21) h rfl rfl
  obtain ⟨h_sp, h⟩ := fit_peel (N' := 22) h rfl rfl
  obtain ⟨h_hit2, h⟩ := fit_peel (N' := 23) h rfl rfl
  obtain ⟨h_hit, h⟩ := fit_peel (N' := 24) h rfl rfl
  obtain ⟨h_bl, h⟩ := fit_peel (N' := 25) h rfl rfl
  obtain ⟨h_br, h⟩ := fit_peel (N' := 26) h rfl rfl
  obtain ⟨h_bce, h⟩ := fit_peel (N' := 27) h rfl rfl
  obtain ⟨h_dtb, h⟩ := fit_peel (N' := 28) h rfl rfl
  obtain ⟨h_tr, h⟩ := fit_peel (N' := 29) h rfl rfl
  obtain ⟨h_tce, h⟩ := fit_peel (N' := 30) h rfl rfl
  obtain ⟨h_atf, h⟩ := fit_peel (N' := 31) h rfl rfl
  obtain ⟨h_core, h⟩ := fit_peel (N' := 32) h rfl rfl
  obtain ⟨h_orbF, h⟩ := fit_peel (N' := 64) h rfl rfl
  obtain ⟨h_rng, h⟩ := fit_peel (N' := 67) h rfl rfl
  obtain ⟨h_fd, h⟩ := fit_peel (N' := 70) h rfl rfl
  obtain ⟨h_cnt, h⟩ := fit_peel (N' := 75) h rfl rfl
  obtain ⟨h_deg, h⟩ := fit_peel (N' := 126) h rfl rfl
  obtain ⟨h_rep, h⟩ := fit_peel (N' := 129) h rfl rfl
  obtain ⟨h_tk, h⟩ := fit_peel (N' := 132) h rfl rfl
  obtain ⟨h_ps, h⟩ := fit_peel (N' := 140) h rfl rfl
  obtain ⟨h_tor, h⟩ := fit_peel (N' := 163) h rfl rfl
  obtain ⟨h_mp, h⟩ := fit_peel (N' := 166) h rfl rfl
  obtain ⟨h_an1, h⟩ := fit_peel (N' := 169) h rfl rfl
  obtain ⟨h_an2, h⟩ := fit_peel (N' := 172) h rfl rfl
  obtain ⟨h_mb, h⟩ := fit_peel (N' := 175) h rfl rfl
  obtain ⟨h_rm, h⟩ := fit_peel (N' := 178) h rfl rfl
  obtain ⟨h_hor, h⟩ := fit_peel (N' := 181) h rfl rfl
  obtain ⟨h_vmap, h⟩ := fit_peel (N' := 184) h rfl rfl
  obtain ⟨h_ad, h⟩ := fit_peel (N' := 187) h rfl rfl
  obtain ⟨h_dfd, h⟩ := fit_peel (N' := 190) h rfl rfl
  obtain ⟨h_dfr, h⟩ := fit_peel (N' := 193) h rfl rfl
  obtain ⟨h_adr, h⟩ := fit_peel (N' := 196) h rfl rfl
  obtain ⟨h_fh, h⟩ := fit_peel (N' := 199) h rfl rfl
  obtain ⟨h_bm, h⟩ := fit_peel (N' := 202) h rfl rfl
  obtain ⟨h_brm, h⟩ := fit_peel (N' := 205) h rfl rfl
  obtain ⟨h_tm, h⟩ := fit_peel (N' := 208) h rfl rfl
  obtain ⟨h_trm, h_fnd⟩ := fit_peel (N' := 211) h rfl rfl
  have hD : ItCfDOk P (fc8DIdx b) :=
    ⟨h_rng, h_cf.single, h_hor, h_vm.single, h_vmap, h_vf.single, h_dv.single, h_dvv.single,
      h_cnt, h_ad, h_dfd, h_rf.single, h_df.single, h_dfr, h_adr, h_sp.single, h_hit2.single,
      h_hit.single, h_fh, h_bl.single, h_bm, h_br.single, h_brm, h_bce.single, h_dtb.single,
      h_tm, h_tr.single, h_trm, h_tce.single, h_atf.single, h_core.single⟩
  have h_col : P.funs[b]? = some (itCfColF (b + 3) (b + 126) (b + 129) (b + 132) (b + 140)
      (b + 64) (b + 163)) := h_col.single
  exact itCf_objSpec hps h_col h_fr.single h_dom.single h_orbF h_rng h_fd h_pd.single h_cnt
    h_deg hj h_rep h_tk h_ps h_tor h_rng h_mp h_fc.single h_an1 h_pe.single h_an2 h_pp.single h_fnd
    h_orb.single h_dom.single h_dg.single h_deg h_rd.single h_tb.single h_mb h_rw.single h_rm
    h_ce.single hD h_des.single

end GI.Impl
