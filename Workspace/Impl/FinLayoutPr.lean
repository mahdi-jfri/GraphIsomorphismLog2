module

public import Workspace.Impl.FinLayoutPrTr
public import Workspace.Impl.AggItemCiCfgTab
public import Workspace.Impl.FinLayoutC23OK

@[expose] public section

/-!
# The pair room

The pair part of Cases 2b/3 sits at `fitC23Idx + 100000` (`fc23F`). Its list `fc10PrF sojF` has
these offsets from the base `b`:

* 0: the trampoline `fc10TrF (b + 1000)` (the init of the pair part calls the init of `sojItem`);
* 1, 2: the pair start `itciPS` and the pair step `itciPK`;
* 3–104: the configuration branch, with the library blocks it calls (`fc10Ix`, `ItcqTab`);
* 1000 on: the sub-list `sojF` of `sojItem`, with its init, start and step at offsets 0, 1, 2.

`fc10_pairSpec` gives `ItciPairSpec` of the room from `ItciSojSpec` of `sojF`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang

/-- The fixed functions of the pair room, without padding. -/
noncomputable def fc10Conc (b : ℕ) : List Expr :=
  [fc10TrF (b + 1000)] ++ (
  [itciPS (b + 3) (b + 1001)] ++ (
  [itciPK (b + 42) (b + 1002)] ++ (
  [itcqStF (b + 4) (b + 12)] ++ (
  [itcqFlF (b + 5) (b + 8)] ++ (
  rangeFuns (b + 5) ++ (
  filterFuns (b + 8) (b + 11) ++ (
  [itcqFbT] ++ (
  [itcqArgF (b + 5) (b + 13) (b + 26) (b + 29) (b + 38)] ++ (
  [itcqClF (b + 14) (b + 18)] ++ (
  mapFuns (b + 14) (b + 17) ++ (
  [itcqPcF] ++ (
  appendFuns (b + 18) ++ (
  findFuns (b + 21) (b + 24) ++ (
  [eqTestF] ++ (
  [itcqCdF (b + 17) (b + 21)] ++ (
  mapFuns (b + 26) (b + 25) ++ (
  [itcqGrpF (b + 5) (b + 30) (b + 18)] ++ (
  mapFuns (b + 30) (b + 33) ++ (
  [itcqGenF (b + 34)] ++ (
  mapFuns (b + 34) (b + 37) ++ (
  [itcqSwF] ++ (
  mapFuns (b + 38) (b + 41) ++ (
  [itcqOneF] ++ (
  [itcqSkF (b + 43) (b + 118)] ++ (
  [itcqSbF (b + 5) (b + 44) (b + 18) (b + 49) (b + 61) (b + 70) (b + 73) (b + 82)] ++ (
  [itcqDsF (b + 105) (b + 106) (b + 5) (b + 114)] ++ (
  filterFuns (b + 45) (b + 48) ++ (
  [itcqNfT (b + 11)] ++ (
  invFuns (b + 49) ++ (
  [itcqLfB (b + 62) (b + 66)] ++ (
  mapFuns (b + 62) (b + 65) ++ (
  [itcqRhB] ++ (
  composeFuns (b + 66) ++ (
  mapFuns (b + 70) (b + 61) ++ (
  [itcqCsF (b + 5) (b + 74)] ++ (
  mapFuns (b + 74) (b + 77) ++ (
  [itcqCsB (b + 78)] ++ (
  mapFuns (b + 78) (b + 81) ++ (
  [itcqSwB] ++ (
  [itcqOuF (b + 83) (b + 87) (b + 66) (b + 100)] ++ (
  findFuns (b + 83) (b + 86) ++ (
  [itcqOdT (b + 87)] ++ (
  [itParF (b + 5) (b + 88) (b + 96)] ++ (
  mapFuns (b + 88) (b + 91) ++ (
  [itInvB (b + 92)] ++ (
  filterFuns (b + 92) (b + 95) ++ (
  [itInvT] ++ (
  foldlFuns (b + 96) (b + 99) ++ (
  [itParS] ++ (
  [itSchF (b + 5) (b + 101)] ++ (
  mapFuns (b + 101) (b + 104) ++ (
  [itSchB (b + 87) (b + 66)] ++ (
  [itcqFlF (b + 5) (b + 45)] ++ (
  mapFuns (b + 106) (b + 109) ++ (
  [itcqRkB (b + 110)] ++ (
  filterFuns (b + 110) (b + 113) ++ (
  [itcqLtT] ++ (
  mapFuns (b + 114) (b + 117) ++ (
  [itcqAtB (b + 21)] ++ (
  [itcqAlF (b + 44) (b + 119) (b + 123)] ++ (
  mapFuns (b + 119) (b + 122) ++ (
  [itcqCoB] ++ (
  eqNatsFuns (b + 123))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 20000 in
theorem fc10Conc_length (b : ℕ) : (fc10Conc b).length = 126 := rfl

/-- The indices of the configuration branch in the pair room at `b`. -/
def fc10Ix (b : ℕ) : ItcqIdx where
  fs := b + 3
  fl := b + 4
  fr := b + 5
  ff := b + 8
  fb := b + 11
  fa := b + 12
  fcl := b + 13
  fmp := b + 14
  fpc := b + 17
  fap := b + 18
  ffb := b + 21
  fe := b + 24
  fcdi := b + 25
  fcd := b + 26
  fg := b + 29
  fgm := b + 30
  fgg := b + 33
  fgm' := b + 34
  fsw := b + 37
  fd := b + 38
  f1 := b + 41
  fk := b + 42
  fB := b + 43
  fdl := b + 44
  ff2 := b + 45
  fn := b + 48
  finv := b + 49
  flf := b + 61
  fmb := b + 62
  frh := b + 65
  fcmp := b + 66
  flm := b + 70
  fcs := b + 73
  fcm := b + 74
  fcb := b + 77
  fsm := b + 78
  fsw2 := b + 81
  fou := b + 82
  ffnd := b + 83
  fo := b + 86
  fpar := b + 87
  fpm := b + 88
  fib := b + 91
  fflt := b + 92
  fit := b + 95
  fpfl := b + 96
  fst := b + 99
  fsch := b + 100
  fsmp := b + 101
  fssb := b + 104
  fdr := b + 105
  frm := b + 106
  frb := b + 109
  flq := b + 110
  flt := b + 113
  fam := b + 114
  fat := b + 117
  fal := b + 118
  fcm2 := b + 119
  fco := b + 122
  feq := b + 123

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The pair room at `b` holds the configuration table**, the trampoline and the two pair
programs. -/
theorem fc10_conc_at {P : Program} {b : ℕ} (h : P.HasAt b (fc10Conc b)) :
    P.funs[b + 0]? = some (fc10TrF (b + 1000)) ∧
    P.funs[b + 1]? = some (itciPS (b + 3) (b + 1001)) ∧
    P.funs[b + 2]? = some (itciPK (b + 42) (b + 1002)) ∧ ItcqTab P (fc10Ix b) := by
  have h : P.HasAt (b + 0) (fc10Conc b) := h
  unfold fc10Conc at h
  obtain ⟨h_tr, h⟩ := fit_peel (N' := 1) h rfl rfl
  obtain ⟨h_ps, h⟩ := fit_peel (N' := 2) h rfl rfl
  obtain ⟨h_pk, h⟩ := fit_peel (N' := 3) h rfl rfl
  obtain ⟨h_fs, h⟩ := fit_peel (N' := 4) h rfl rfl
  obtain ⟨h_fl, h⟩ := fit_peel (N' := 5) h rfl rfl
  obtain ⟨h_fr, h⟩ := fit_peel (N' := 8) h rfl rfl
  obtain ⟨h_ff, h⟩ := fit_peel (N' := 11) h rfl rfl
  obtain ⟨h_fb, h⟩ := fit_peel (N' := 12) h rfl rfl
  obtain ⟨h_fa, h⟩ := fit_peel (N' := 13) h rfl rfl
  obtain ⟨h_fcl, h⟩ := fit_peel (N' := 14) h rfl rfl
  obtain ⟨h_fmp, h⟩ := fit_peel (N' := 17) h rfl rfl
  obtain ⟨h_fpc, h⟩ := fit_peel (N' := 18) h rfl rfl
  obtain ⟨h_fap, h⟩ := fit_peel (N' := 21) h rfl rfl
  obtain ⟨h_ffb, h⟩ := fit_peel (N' := 24) h rfl rfl
  obtain ⟨h_fe, h⟩ := fit_peel (N' := 25) h rfl rfl
  obtain ⟨h_fcdi, h⟩ := fit_peel (N' := 26) h rfl rfl
  obtain ⟨h_fcd, h⟩ := fit_peel (N' := 29) h rfl rfl
  obtain ⟨h_fg, h⟩ := fit_peel (N' := 30) h rfl rfl
  obtain ⟨h_fgm, h⟩ := fit_peel (N' := 33) h rfl rfl
  obtain ⟨h_fgg, h⟩ := fit_peel (N' := 34) h rfl rfl
  obtain ⟨h_fgm_, h⟩ := fit_peel (N' := 37) h rfl rfl
  obtain ⟨h_fsw, h⟩ := fit_peel (N' := 38) h rfl rfl
  obtain ⟨h_fd, h⟩ := fit_peel (N' := 41) h rfl rfl
  obtain ⟨h_f1, h⟩ := fit_peel (N' := 42) h rfl rfl
  obtain ⟨h_fk, h⟩ := fit_peel (N' := 43) h rfl rfl
  obtain ⟨h_fB, h⟩ := fit_peel (N' := 44) h rfl rfl
  obtain ⟨h_fdl, h⟩ := fit_peel (N' := 45) h rfl rfl
  obtain ⟨h_ff2, h⟩ := fit_peel (N' := 48) h rfl rfl
  obtain ⟨h_fn, h⟩ := fit_peel (N' := 49) h rfl rfl
  obtain ⟨h_finv, h⟩ := fit_peel (N' := 61) h rfl rfl
  obtain ⟨h_flf, h⟩ := fit_peel (N' := 62) h rfl rfl
  obtain ⟨h_fmb, h⟩ := fit_peel (N' := 65) h rfl rfl
  obtain ⟨h_frh, h⟩ := fit_peel (N' := 66) h rfl rfl
  obtain ⟨h_fcmp, h⟩ := fit_peel (N' := 70) h rfl rfl
  obtain ⟨h_flm, h⟩ := fit_peel (N' := 73) h rfl rfl
  obtain ⟨h_fcs, h⟩ := fit_peel (N' := 74) h rfl rfl
  obtain ⟨h_fcm, h⟩ := fit_peel (N' := 77) h rfl rfl
  obtain ⟨h_fcb, h⟩ := fit_peel (N' := 78) h rfl rfl
  obtain ⟨h_fsm, h⟩ := fit_peel (N' := 81) h rfl rfl
  obtain ⟨h_fsw2, h⟩ := fit_peel (N' := 82) h rfl rfl
  obtain ⟨h_fou, h⟩ := fit_peel (N' := 83) h rfl rfl
  obtain ⟨h_ffnd, h⟩ := fit_peel (N' := 86) h rfl rfl
  obtain ⟨h_fo, h⟩ := fit_peel (N' := 87) h rfl rfl
  obtain ⟨h_fpar, h⟩ := fit_peel (N' := 88) h rfl rfl
  obtain ⟨h_fpm, h⟩ := fit_peel (N' := 91) h rfl rfl
  obtain ⟨h_fib, h⟩ := fit_peel (N' := 92) h rfl rfl
  obtain ⟨h_fflt, h⟩ := fit_peel (N' := 95) h rfl rfl
  obtain ⟨h_fit, h⟩ := fit_peel (N' := 96) h rfl rfl
  obtain ⟨h_fpfl, h⟩ := fit_peel (N' := 99) h rfl rfl
  obtain ⟨h_fst, h⟩ := fit_peel (N' := 100) h rfl rfl
  obtain ⟨h_fsch, h⟩ := fit_peel (N' := 101) h rfl rfl
  obtain ⟨h_fsmp, h⟩ := fit_peel (N' := 104) h rfl rfl
  obtain ⟨h_fssb, h⟩ := fit_peel (N' := 105) h rfl rfl
  obtain ⟨h_fdr, h⟩ := fit_peel (N' := 106) h rfl rfl
  obtain ⟨h_frm, h⟩ := fit_peel (N' := 109) h rfl rfl
  obtain ⟨h_frb, h⟩ := fit_peel (N' := 110) h rfl rfl
  obtain ⟨h_flq, h⟩ := fit_peel (N' := 113) h rfl rfl
  obtain ⟨h_flt, h⟩ := fit_peel (N' := 114) h rfl rfl
  obtain ⟨h_fam, h⟩ := fit_peel (N' := 117) h rfl rfl
  obtain ⟨h_fat, h⟩ := fit_peel (N' := 118) h rfl rfl
  obtain ⟨h_fal, h⟩ := fit_peel (N' := 119) h rfl rfl
  obtain ⟨h_fcm2, h⟩ := fit_peel (N' := 122) h rfl rfl
  obtain ⟨h_fco, h⟩ := fit_peel (N' := 123) h rfl rfl
  exact ⟨h_tr.single, h_ps.single, h_pk.single, ⟨h_fs.single, h_fl.single, h_fr, h_ff, h_fb.single, h_fa.single, h_fcl.single, h_fmp, h_fpc.single, h_fap, h_ffb, h_fe.single, h_fcdi.single, h_fcd, h_fg.single, h_fgm, h_fgg.single, h_fgm_, h_fsw.single, h_fd, h_f1.single, h_fk.single, h_fB.single, h_fdl.single, h_ff2, h_fn.single, h_finv, h_flf.single, h_fmb, h_frh.single, h_fcmp, h_flm, h_fcs.single, h_fcm, h_fcb.single, h_fsm, h_fsw2.single, h_fou.single, h_ffnd, h_fo.single, h_fpar.single, h_fpm, h_fib.single, h_fflt, h_fit.single, h_fpfl, h_fst.single, h_fsch.single, h_fsmp, h_fssb.single, h_fdr.single, h_frm, h_frb.single, h_flq, h_flt.single, h_fam, h_fat.single, h_fal.single, h_fcm2, h_fco.single, h⟩⟩

/-- **The bound of the pair part** from the bound `Xs` of `sojItem`. -/
def fc10Xp (Xs : ℕ → ℕ) : ℕ → ℕ := itciXp itcqXc (fc10TrX Xs)

theorem fc10Xp_pbu {Xs : ℕ → ℕ} (hs : PBU fun _ W _ => Xs W) : PBU fun _ W _ => fc10Xp Xs W :=
  itciXp_pbu (fc10TrX_pbu hs) (itcqXc_pbu (fc10TrX_pbu hs))

/-- **The pair room at a base `b`** from the contract of `sojItem` at `b + 1000`, `b + 1001`,
`b + 1002`. -/
theorem fc10_pairSpec_at (I : Iface) {P : Program} {F : Funs} {b : ℕ} {sojF : List Expr}
    {Xs : ℕ → ℕ} (h : P.HasAt b (asmPad 1000 (fc10Conc b) ++ sojF))
    (hs : ItciSojSpec I P F (b + 1000) (b + 1001) (b + 1002) Xs) :
    ItciPairSpec I P F b (b + 1) (b + 2) (fc10Xp Xs) := by
  have hc : (fc10Conc b).length ≤ 1000 := by rw [fc10Conc_length]; decide
  obtain ⟨htr, hps, hpk, htab⟩ := fc10_conc_at h.left.left
  have hs' : ItciSojSpec I P F (b + 1000) (b + 1001) (b + 1002) Xs := hs
  exact itci_pairSpec_of I P (itcq_cfgSpec_of htab) (fc10_sojSpec_tr I htr hs') hps hpk

/-- **The pair list**: the fixed functions, padded to 1000, then the sub-list of `sojItem`. -/
noncomputable def fc10PrF (sojF : List Expr) : List Expr :=
  asmPad 1000 (fc10Conc (fitC23Idx + 100000)) ++ sojF

theorem fc10PrF_fits {sojF : List Expr} (h : sojF.length ≤ 99000) :
    (fc10PrF sojF).length ≤ 100000 := by
  have hc : (fc10Conc (fitC23Idx + 100000)).length ≤ 1000 := by rw [fc10Conc_length]; decide
  simp only [fc10PrF, List.length_append, length_asmPad hc]
  omega

/-- **The pair room in its final slot.** -/
theorem fc10_pairSpec (I : Iface) {P : Program} {F : Funs} {sojF : List Expr} {Xs : ℕ → ℕ}
    (h : P.HasAt (fitC23Idx + 100000) (fc10PrF sojF))
    (hs : ItciSojSpec I P F (fitC23Idx + 101000) (fitC23Idx + 101001) (fitC23Idx + 101002) Xs) :
    ItciPairSpec I P F (fitC23Idx + 100000) (fitC23Idx + 100001) (fitC23Idx + 100002)
      (fc10Xp Xs) :=
  fc10_pairSpec_at I h hs

end GI.Impl
