import Workspace.Impl.AggItemHvInitT

/-!
# Case 2a: the init program meets `ItHvInitOK`, and the case meets `ItSCaseOK`

The init program of Case 2a is `itHvIF` (`AggItemHvInitT.lean`) with its parts at the indices
`ItHvIIdx`. On the output `K.v` of the structure step it computes, once per round
(Lemma A.11 of the paper, Case 2a):

1. `Φ` and `Φ'`, the dominant orbits of the label groups of `F_x` and `F_y` (`it_grp_spec`,
   `it_dom_spec`), and the test `|Φ| = |Φ'| ≥ 2` of `halvingItem`;
2. the even aligner `σ` with `σ Φ = Φ'` and the paired transposition `(a b)(c d)`
   (`it_hvSg_spec`), the flag `[2 ≤ |Φᶜ|]`, the graph pairs of `A` (`it_hvA_spec`) and their
   first parts;
3. a lift `τ₀ ∈ G` of `σ` and a lift `t` of `(a b)(c d)` (or `t = 1` if the flag is `0`), by
   **NormalizedFactor** (`it_hvLt_spec`);
4. a group value of the kernel `K = π⁻¹((Alt(Φ) × Alt(C)) ⊓ fix Φ)`, by **PointwiseStab**
   (`it_hvKg_spec`);
5. the canonical values of the three kernel calls on `x`, `y ∘ τ₀` and `y ∘ τ₀ t`
   (`it_hvOut_spec`).

`it_hvInitOK` proves `ItHvInitOK` with the bound `itHvIX`, and `itS_c2a_caseOK_full` combines it
with `itS_c2a_caseOK` into the contract `ItSCaseOK` of Case 2a. The cited algorithms enter only
through the primitives at the indices `jfac` (NormalizedFactor) and `jp` (PointwiseStab) and the
module `kr` (`LcKrOK`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPts gens encGroup encKColoring NormalizedFactor PointwiseStab)

variable {Ω C : Type} {k : ℕ}

/-! ### The indices -/

/-- **The function indices of the Case 2a init program.** -/
structure ItHvIIdx where
  (f0 pre m da out col : ℕ)
  (grp mpG sf dom orb fd pd : ℕ)
  (ind mpI ib sg : ℕ)
  (lc gr en mkg fm : ℕ)
  (lt lift sb sp jfac : ℕ)
  (kg am ak stab jp kr : ℕ)
  (af fdA ch rs mpR rb sch mpA sbA pm : ℕ)
  (fst fb : ℕ)

/-- **The program has the Case 2a init program at `J`**, with the helpers of the Case 1 item at
`IC` (range, count, compose, append, the label data, the swap table and the parity). The cited
algorithms: NormalizedFactor at `jfac`, PointwiseStab at `jp`, and the module `kr` (`LcKrOK`). -/
structure ItHvIOk (P : Program) (J : ItHvIIdx) (IC : ItC1Idx) (hfac : NormalizedFactor)
    (hst : PointwiseStab) (krC : ℕ → ℕ) : Prop where
  f0 : P.funs[J.f0]? = some (itHvIF J.pre J.m)
  pre : P.funs[J.pre]? = some (itHvPreF J.grp J.dom)
  m : P.funs[J.m]? = some (itHvMF J.da J.lt J.kg J.out)
  da : P.funs[J.da]? = some (itHvDaF J.ind J.sg J.lc J.af J.fst)
  out : P.funs[J.out]? = some (itHvOutF J.col)
  col : P.HasAt J.col (gatherFuns J.col)
  grp : P.funs[J.grp]? = some (itGrpF IC.rng J.mpG IC.app)
  mpG : P.HasAt J.mpG (mapFuns J.mpG J.sf)
  sf : P.funs[J.sf]? = some itSndF
  dom : P.funs[J.dom]? = some (itDomF J.orb IC.rng J.fd)
  orb : P.HasAt J.orb (orbitFuns J.orb)
  fd : P.HasAt J.fd (filterFuns J.fd J.pd)
  pd : P.funs[J.pd]? = some (acpDomF IC.cnt)
  ind : P.funs[J.ind]? = some (itHvIndF IC.rng J.mpI)
  mpI : P.HasAt J.mpI (mapFuns J.mpI J.ib)
  ib : P.funs[J.ib]? = some (itHvIndB IC.cnt)
  sg : P.funs[J.sg]? = some (itHvSgF IC.dat IC.swt IC.cmp IC.par)
  lc : P.funs[J.lc]? = some (itHvLcF IC.rng J.gr J.fm)
  gr : P.funs[J.gr]? = some (grpF J.en J.mkg)
  en : P.HasAt J.en (pEncMapFuns J.en)
  mkg : P.HasAt J.mkg (mkGroupFuns J.mkg)
  fm : P.HasAt J.fm (fstMapFuns J.fm)
  lt : P.funs[J.lt]? = some (itHvLtF J.lift IC.rng IC.cmp)
  lift : P.funs[J.lift]? = some (liftLabF J.sb J.sp J.jfac)
  sb : ShiftAt P J.sb
  sp : P.HasAt J.sp (pSplitFuns J.sp)
  jfac : P.prims[J.jfac]? = some (normalizedFactorPrim hfac)
  kg : P.funs[J.kg]? = some (itHvKgF J.am J.stab J.kr)
  am : P.HasAt J.am (mapFuns J.am J.ak)
  ak : P.funs[J.ak]? = some addKF
  stab : P.HasAt J.stab (graphStabFuns J.stab J.jp)
  jp : P.prims[J.jp]? = some (pointwiseStabPrim hst)
  kr : LcKrOK P J.kr krC
  krm : Monotone krC
  af : P.funs[J.af]? = some (itHvAF J.fdA J.sch)
  fdA : P.HasAt J.fdA (findFuns J.fdA J.ch)
  ch : P.funs[J.ch]? = some (itHvChF J.rs IC.par)
  rs : P.funs[J.rs]? = some (itHvRsF IC.rng J.mpR)
  mpR : P.HasAt J.mpR (mapFuns J.mpR J.rb)
  rb : P.funs[J.rb]? = some itHvRsB
  sch : P.funs[J.sch]? = some (itHvSchF IC.rng J.mpA)
  mpA : P.HasAt J.mpA (mapFuns J.mpA J.sbA)
  sbA : P.funs[J.sbA]? = some (itHvSchB J.ch J.pm)
  pm : P.funs[J.pm]? = some (itHvPmF IC.cmp)
  fst : P.HasAt J.fst (mapFuns J.fst J.fb)
  fb : P.funs[J.fb]? = some itHvFstB

/-! ### The bound -/

/-- The weight bound of the inputs of the middle part. -/
def itHvIMd (W₀ : ℕ) : ℕ := 2 * (itSVB W₀ + 10 * (itSVB W₀ + 1) ^ 2) + 7

/-- The bound of the two label lifts. -/
def itHvIL (pf : Prim) (W₀ : ℕ) : ℕ := 2 * liftLabCost pf (itHvIMd W₀) + itHvLtC (itHvIMd W₀)

/-- The weight bound of a group value of `K`. -/
def itHvIBK (W₀ : ℕ) : ℕ := 320 * (itHvIMd W₀ + 1) ^ 6

/-- The weight bound of the input of the kept-value program. -/
def itHvIMo (W₀ : ℕ) : ℕ :=
  2 * (itSVB W₀ + 20 * (itHvIMd W₀ + 1) ^ 2 + itHvIBK W₀ + itHvDaC (itHvIMd W₀)) + 8

/-- The cost bound of the middle part. -/
def itHvIMC (pf pst : Prim) (krC : ℕ → ℕ) (W₀ : ℕ) : ℕ :=
  itHvDaC (itHvIMd W₀) + 2 * itHvIL pf W₀ + itHvKgC pst krC (itHvIMd W₀) +
    5 * itHvOutC (itHvIMo W₀) +
    itHvMK (itHvIMd W₀ + itHvDaC (itHvIMd W₀) + itHvIL pf W₀ + itHvIBK W₀)

/-- The cost bound of the test. -/
def itHvIP (W₀ : ℕ) : ℕ :=
  itHvPreC (itSVB W₀) (itGrpC (itSVB W₀)) (itDomC (100 * (itSVB W₀ + 1) ^ 3))

/-- **The bound of the Case 2a init program**, with the costs `pf` of NormalizedFactor, `pst` of
PointwiseStab and `krC` of the module `kr`. -/
def itHvIX (pf pst : Prim) (krC : ℕ → ℕ) (W₀ : ℕ) : ℕ :=
  itHvIC (itSVB W₀) (itHvIP W₀) (itHvIMC pf pst krC W₀)

/-! ### Small facts -/

/-- The sign of the paired transposition is `1`. -/
theorem itHv_pair_sign {q : ℕ} (hq : 2 ≤ q) (Φ : Finset (Fin q)) {a b : Fin q} (hab : a ≠ b) :
    sign (swap a b * itHvCD Φ hq) = 1 := by
  have hcd : (itpPosE (itHvLab Φ))⁻¹ ⟨0, by omega⟩ ≠ (itpPosE (itHvLab Φ))⁻¹ ⟨1, by omega⟩ := by
    intro h
    have := (itpPosE (itHvLab Φ))⁻¹.injective h
    simp at this
  unfold itHvCD
  rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
  decide

/-- The first two points of a sorted list of at least two points. -/
theorem itHv_sort_two {q : ℕ} {Φ : Finset (Fin q)} (h : 2 ≤ Φ.card) :
    ∃ a b rest, Φ.sort (· ≤ ·) = a :: b :: rest := by
  have hl : (Φ.sort (· ≤ ·)).length = Φ.card := Finset.length_sort _
  match hs : Φ.sort (· ≤ ·) with
  | [] => rw [hs] at hl; simp at hl; omega
  | [_] => rw [hs] at hl; simp at hl; omega
  | a :: b :: rest => exact ⟨a, b, rest, rfl⟩

theorem itHv_sort_mem {q : ℕ} {Φ : Finset (Fin q)} {a b : Fin q} {rest : List (Fin q)}
    (hs : Φ.sort (· ≤ ·) = a :: b :: rest) : a ∈ Φ ∧ b ∈ Φ ∧ a ≠ b := by
  have hmem : ∀ x, x ∈ Φ.sort (· ≤ ·) ↔ x ∈ Φ := fun x => Finset.mem_sort _
  refine ⟨(hmem a).1 (by rw [hs]; simp), (hmem b).1 (by rw [hs]; simp), ?_⟩
  have hn := Finset.sort_nodup Φ (· ≤ ·)
  rw [hs] at hn
  intro h
  rw [h] at hn
  simp at hn

theorem itHvLtC_mono {a b : ℕ} (h : a ≤ b) : itHvLtC a ≤ itHvLtC b :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 4)

theorem itHv_K0_le (W₀ : ℕ) : 2 * W₀ + 3 ≤ itSVB W₀ := by
  have h : 2 * W₀ + 3 + 1 ≤ (2 * W₀ + 3 + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  unfold itSVB
  omega

/-! ### The kept value -/

section Kept

variable {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {L : SuppliedLabels S} {K : ItSCtx k S L}

/-- **The program's outputs give the facts of the kept value.** The lift `a₀` of the even
aligner gives the alignment (`it_hv_al_of`, `itHvSig_image`); the lift `a₁` of the paired
transposition, with the flag `[2 ≤ |Φᶜ|]`, gives the twist (`itHv_tw_choice`); the first parts of
`itHvAL Φ fx` generate `A` (`itHv_A_gens`). -/
theorem itHv_kept_of (hK : K.OK e c) (hq2 : 2 ≤ L.q)
    (hcard : (itHvPhi K).card = (itHvPhi' K).card) (h2 : 2 ≤ (itHvPhi K).card)
    {a b : Fin L.q} {rest : List (Fin L.q)} (hs : (itHvPhi K).sort (· ≤ ·) = a :: b :: rest)
    {gv dv xv yv hv rv : Val}
    (hsveq : K.sv = .list [.nat k, gv, dv, xv, yv, hv, rv, boolVal S.floor, .nat S.h, .nat S.N])
    (hxv : ColorVal e c xv S.x) {a₀ a₁ : Perm (Fin k)}
    (h0 : (a₀, itHvSig (itHvPhi K) (itHvPhi' K) a b) ∈ Subgroup.closure {p | p ∈ K.ps})
    (h1 : (a₁, swap a b * itHvCD (itHvPhi K) hq2) ∈ Subgroup.closure {p | p ∈ K.ps})
    {kgv : Val} (hkgv : GroupValC k kgv (groupFin e (itHvKer L.toGiantLabels (itHvPhi K)))) :
    ItHvKept e c K (.list [.nat 1, winVal' k kgv dv xv xv hv S.N,
      winVal' k kgv dv xv (itHvYv e c S.y a₀) hv S.N,
      winVal' k kgv dv xv (itHvYv e c S.y
        (a₀ * if (if 1 < L.q - (itHvPhi K).card then 1 else 0) = 0 then 1 else a₁)) hv S.N,
      encPerm a₀,
      encPerm (a₀ * if (if 1 < L.q - (itHvPhi K).card then 1 else 0) = 0 then 1 else a₁),
      .list ((itHvAL (itHvPhi K) K.fx).map fun p => encPerm p.1)])
      ((toFin e).symm a₀)
      ((toFin e).symm (if (if 1 < L.q - (itHvPhi K).card then 1 else 0) = 0 then 1 else a₁)) := by
  obtain ⟨ha, hb, -⟩ := itHv_sort_mem hs
  have hd : L.q < 2 * (itHvPhi K).card := itHv_dom_big h2
  set x₁ : Perm (Fin k) := if (if 1 < L.q - (itHvPhi K).card then 1 else 0) = 0 then 1 else a₁
    with hx₁
  have hmul : (toFin e).symm (a₀ * x₁) = (toFin e).symm a₀ * (toFin e).symm x₁ := map_mul _ _ _
  have hy1 : ColorVal e c (itHvYv e c S.y (a₀ * x₁)) (S.y ∘ ((toFin e).symm a₀ * (toFin e).symm x₁)) := by
    rw [← hmul]; exact itHvYv_colorVal e c S.y _
  have hgA := itHv_A_gens (S := S) (L := L.toGiantLabels)
    (State.liftGroup_le _) hK.hfx
  refine ⟨it_hv_al_of hK.hps h0 (itHvSig_image hcard hd ha hb), itHv_tw_choice hK.hps hd hq2 hs h1,
    ⟨gv, kgv, dv, xv, yv, hv, rv, boolVal S.floor, .nat S.h, itHvYv e c S.y a₀,
      itHvYv e c S.y (a₀ * x₁), S.N, (itHvAL (itHvPhi K) K.fx).map Prod.fst, hsveq, hkgv, hxv,
      itHvYv_colorVal e c S.y a₀, hy1, hgA, ?_⟩⟩
  rw [MulEquiv.apply_symm_apply, ← hmul, MulEquiv.apply_symm_apply, List.map_map]
  rfl

end Kept

/-! ### The middle part in the context of a call -/

section Mid

variable {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {L : SuppliedLabels S} {K : ItSCtx k S L}

set_option maxHeartbeats 4000000 in
/-- **The middle part of the init program, when the test passes**: it returns a kept value with
its facts (`ItHvKept`), at cost at most `itHvIMC`. -/
theorem it_hv_mid (hfac : NormalizedFactor) (hst : PointwiseStab) {P : Program} {krC : ℕ → ℕ}
    {J : ItHvIIdx} {IC : ItC1Idx} (hc1 : ItC1Ok P IC) (hJ : ItHvIOk P J IC hfac hst krC)
    (hK : K.OK e c) (hq2 : 2 ≤ L.q) (hcond : ItHvCond K) {W₀ : ℕ}
    (hstV : K.st.wt ≤ itSVB W₀) (hkqV : k + L.q + 1 ≤ itSVB W₀) :
    FunAll P J.m (.list [K.st, encPts ((itHvPhi K).sort (· ≤ ·)),
      encPts ((itHvPhi' K).sort (· ≤ ·))])
      (fun w cost => (∃ τ₀ t, ItHvKept e c K w τ₀ t) ∧
        cost ≤ itHvIMC (normalizedFactorPrim hfac) (pointwiseStabPrim hst) krC W₀) := by
  obtain ⟨hcard, h2⟩ := hcond
  obtain ⟨a, b, rest, hs⟩ := itHv_sort_two h2
  obtain ⟨ha, hb, hab⟩ := itHv_sort_mem hs
  set V := itSVB W₀ with hV
  set Md := itHvIMd W₀ with hMd
  set Φ := itHvPhi K with hΦ
  set Φ' := itHvPhi' K with hΦ'
  set cv := stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ) with hcv
  set psV := Val.list (K.ps.map pairV) with hpsV
  have eMd : Md = 2 * (V + 10 * (V + 1) ^ 2) + 7 := rfl
  have eMo : itHvIMo W₀ = 2 * (V + 20 * (Md + 1) ^ 2 + itHvIBK W₀ + itHvDaC Md) + 8 := rfl
  have eIL : itHvIL (normalizedFactorPrim hfac) W₀ =
      2 * liftLabCost (normalizedFactorPrim hfac) Md + itHvLtC Md := rfl
  have est : K.st = .list [K.sv, .list [.nat k, .nat L.q], psV, .list (K.fx.map pairV),
      .list (K.fy.map pairV), cv] := rfl
  -- sizes
  have wsv : K.sv.wt < K.st.wt := by rw [est]; exact wt_le_wt_list (by simp)
  have wps : psV.wt < K.st.wt := by rw [est]; exact wt_le_wt_list (by simp)
  have lps : K.ps.length < psV.wt := by
    have := length_lt_wt_list (K.ps.map pairV); simpa using this
  have wPx := itHv_pts_wt Φ
  have wPy := itHv_pts_wt Φ'
  have hqV : (L.q + 1) ^ 2 ≤ (V + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hM : (Val.list [K.st, encPts (Φ.sort (· ≤ ·)), encPts (Φ'.sort (· ≤ ·))]).wt ≤ Md := by
    have := wt_list3_le K.st (encPts (Φ.sort (· ≤ ·))) (encPts (Φ'.sort (· ≤ ·)))
    rw [eMd]; omega
  have hVMd : 2 * V + 7 ≤ Md := by rw [eMd]; omega
  -- the state value
  obtain ⟨gv, dv, xv, yv, hv, rv, -, -, hxv, hyv, -, -, hsveq⟩ := hK.can.val
  -- the callees
  have hpar : ∀ σ : Perm (Fin L.q), FunDet P IC.par (encPerm σ) (.nat (itpNInv σ % 2))
      (itParC L.q) := fun σ =>
    it_par_spec hc1.par hc1.rng hc1.mpI hc1.ib hc1.fltI hc1.it hc1.fld hc1.st σ
  have hda := it_hvDa_spec (k := k) hJ.da hq2
    (fun Ψ => it_hvInd_spec hJ.ind hc1.rng hJ.mpI hJ.ib hc1.cnt Ψ)
    (fun Ψ Ψ' u v r hr => it_hvSg_spec hJ.sg
      (fun lab hlt => it_dat_spec hc1.dat hc1.rng hc1.mpS hc1.sz hc1.cnt hc1.mpP hc1.pb hc1.flt
        hc1.kb hc1.inv hlt) (fun u v => it_swTab_spec hc1.swt hc1.sb u v) hc1.cmp hpar hq2 Ψ Ψ' hr)
    (fun ps => it_hvLc_spec hJ.lc hc1.rng hJ.gr hJ.en hJ.mkg hJ.fm ps)
    (fun Ψ T hT M hM => it_hvA_spec hJ.af hJ.fdA hJ.sch hc1.rng hJ.mpA hJ.sbA Ψ
      (fun s hs => it_hvCh_spec hJ.ch hJ.rs hc1.rng hJ.mpR hJ.rb hpar Ψ s hs)
      (fun u v => it_hvPm_spec hJ.pm hc1.cmp u v) hT hM)
    (fun ps => it_hvFst_spec hJ.fst hJ.fb ps) K.sv cv K.ps K.fx K.fy Φ Φ' (itHv_fx_inv K.fx) hs
    (M := Md) hM (by omega)
  set gAV := Val.list ((itHvAL Φ K.fx).map fun p => encPerm p.1) with hgAV
  set fl := if 1 < L.q - Φ.card then 1 else 0 with hfl
  have hfl1 : fl ≤ 1 := by rw [hfl]; split_ifs <;> omega
  have wgA : gAV.wt < itHvDaC Md := by
    have h1 := FunDet.wt_lt hda
    have h2 : gAV.wt < (Val.list [.list [encPerm (itHvSig Φ Φ' a b),
        encPerm (swap a b * itHvCD Φ hq2)], liftLabCtx k L.q K.ps, .nat fl, gAV]).wt :=
      wt_le_wt_list (by simp)
    omega
  -- the lifts
  have hlt := it_hvLt_spec hfac hJ.lt hJ.lift hJ.sb hJ.sp hJ.jfac hc1.rng hc1.cmp K.ps
    (it_hv_lift_exists hK.hps (itHvSig_sign Φ Φ' hab))
    (it_hv_lift_exists hK.hps (itHv_pair_sign hq2 Φ hab)) hfl1
  have hLc : 2 * liftLabCost (normalizedFactorPrim hfac) (K.ps.length + k + L.q + 2) +
      itHvLtC (K.ps.length + k + L.q + 2) ≤ itHvIL (normalizedFactorPrim hfac) W₀ := by
    have h1 : K.ps.length + k + L.q + 2 ≤ Md := by omega
    have := lc_liftLabCost_mono (normalizedFactorPrim hfac) h1
    have := itHvLtC_mono h1
    rw [eIL]; omega
  -- the kernel
  have hkg := it_hvKg_spec hst hJ.kg hJ.am hJ.ak hJ.stab hJ.jp hJ.kr hJ.krm hK.hps Φ
  have hkC : itHvKgC (pointwiseStabPrim hst) krC (pM k L.q K.ps) ≤
      itHvKgC (pointwiseStabPrim hst) krC Md :=
    itHvKgC_mono _ hJ.krm (by unfold pM; omega)
  have hBK : 320 * (k + 1) ^ 6 ≤ itHvIBK W₀ := by
    show 320 * (k + 1) ^ 6 ≤ 320 * (Md + 1) ^ 6
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6)
  -- the middle program
  have hm := it_hvM_spec hJ.m K.sv (.list [.nat k, .nat L.q]) psV (.list (K.fx.map pairV))
    (.list (K.fy.map pairV)) cv (encPts (Φ.sort (· ≤ ·))) (encPts (Φ'.sort (· ≤ ·)))
    (encPerm (itHvSig Φ Φ' a b)) (encPerm (swap a b * itHvCD Φ hq2)) (liftLabCtx k L.q K.ps) gAV fl
    (Rl := fun a₀ a₁' => ∃ a₁, a₁' = a₀ * (if fl = 0 then 1 else a₁) ∧
      (a₀, itHvSig Φ Φ' a b) ∈ Subgroup.closure {p | p ∈ K.ps} ∧
      (a₁, swap a b * itHvCD Φ hq2) ∈ Subgroup.closure {p | p ∈ K.ps})
    (Rk := fun w => GroupValC k w (groupFin e (itHvKer L.toGiantLabels Φ)) ∧ w.wt ≤ itHvIBK W₀)
    (Ov := fun a₀ a₁' kgv => .list [.nat 1, winVal' k kgv dv xv xv hv S.N,
      winVal' k kgv dv xv (itHvYv e c S.y a₀) hv S.N, winVal' k kgv dv xv (itHvYv e c S.y a₁') hv S.N,
      encPerm a₀, encPerm a₁', gAV])
    (cL := itHvIL (normalizedFactorPrim hfac) W₀) (BK := itHvIBK W₀)
    (cK := itHvKgC (pointwiseStabPrim hst) krC Md) (cO := itHvOutC (itHvIMo W₀)) hda
    (hlt.mono fun w cst ⟨a₀, a₁, hw, h0, h1, hc⟩ => ⟨a₀, _, hw, ⟨a₁, rfl, h0, h1⟩, hc.trans hLc⟩)
    (hkg.mono fun w cst ⟨h1, h2, h3⟩ => ⟨⟨h1, h2.trans hBK⟩, h2.trans hBK, h3.trans hkC⟩)
    (fun a₀ a₁' kgv _ hRk => by
      have hsvw : K.sv.wt ≤ V := by omega
      rw [hsveq] at hsvw ⊢
      refine it_hvOut_spec hJ.out hJ.col gv dv xv yv hv rv _ _ S.N hyv a₀ a₁' kgv gAV ?_
      have h4 := wt_list4_le (.list [.nat k, gv, dv, xv, yv, hv, rv, boolVal S.floor, .nat S.h,
        .nat S.N]) (.list [encPerm a₀, encPerm a₁']) kgv gAV
      have h2 := wt_list2_le (encPerm a₀) (encPerm a₁')
      have p₀ := wt_encPerm_le a₀
      have p₁ := wt_encPerm_le a₁'
      have hk2 : 4 * (k + 1) ^ 2 ≤ 4 * (Md + 1) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      have := hRk.2
      have h4M : 2 ^ 2 ≤ (Md + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      rw [eMo]
      omega)
  refine hm.mono fun w cst h => ?_
  obtain ⟨a₀, a₁', kgv, ⟨a₁, rfl, h0, h1⟩, ⟨hkgv, -⟩, rfl, hc⟩ := h
  refine ⟨⟨_, _, itHv_kept_of hK hq2 hcard h2 hs hsveq hxv h0 h1 hkgv⟩, ?_⟩
  · have hx : (Val.list [Val.list [K.sv, .list [.nat k, .nat L.q], psV, .list (K.fx.map pairV),
        .list (K.fy.map pairV), cv], encPts (Φ.sort (· ≤ ·)), encPts (Φ'.sort (· ≤ ·))]).wt ≤ Md :=
      est ▸ hM
    have eMC : itHvIMC (normalizedFactorPrim hfac) (pointwiseStabPrim hst) krC W₀ =
        itHvDaC Md + 2 * itHvIL (normalizedFactorPrim hfac) W₀ +
          itHvKgC (pointwiseStabPrim hst) krC Md + 5 * itHvOutC (itHvIMo W₀) +
          itHvMK (Md + itHvDaC Md + itHvIL (normalizedFactorPrim hfac) W₀ + itHvIBK W₀) := rfl
    rw [eMC]
    simp only [itHvMK] at hc ⊢
    exact hc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 1000 (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hx _) _) _) _)) _)

end Mid

/-! ### The contract -/

theorem itHvIC_mono {a a' b b' c c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    itHvIC a b c ≤ itHvIC a' b' c' := by
  unfold itHvIC; omega

set_option maxHeartbeats 4000000 in
/-- **The init program of Case 2a meets `ItHvInitOK`**, at any program that has its functions at
`J` and the Case 1 helpers at `IC`, with the bound `itHvIX`. -/
theorem it_hvInitOK (I : Iface) (hfac : NormalizedFactor) (hst : PointwiseStab) {Pg : Program}
    {F : Funs} {krC : ℕ → ℕ} {J : ItHvIIdx} {IC : ItC1Idx} (hc1 : ItC1Ok Pg IC)
    (hJ : ItHvIOk Pg J IC hfac hst krC) :
    ItHvInitOK I Pg F J.f0 (itHvIX (normalizedFactorPrim hfac) (pointwiseStabPrim hst) krC) := by
  intro Ω C k e c S sv lv L hc K hK hcs
  obtain ⟨hkq, hκ, hq, hq0, -, hκq⟩ := itS_size I Pg F hc
  have hvw := itS_vW I Pg F hc hK
  have hK0 := itHv_K0_le (I.inW .giant S)
  have hκ64 : P₀.κ = 64 := rfl
  have hq2 : 2 ≤ L.q := by omega
  set V := itSVB (I.inW .giant S) with hV
  set cv := stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ) with hcv
  set psV := Val.list (K.ps.map pairV) with hpsV
  set fxV := Val.list (K.fx.map pairV) with hfxV
  set fyV := Val.list (K.fy.map pairV) with hfyV
  set dd := Val.list [encKColoring K.d, encKColoring K.d'] with hdd
  set cd := Val.nat (AggCase.code K.case) with hcd
  set sr := natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ)) with hsr
  have est : K.st = .list [K.sv, .list [.nat k, .nat L.q], psV, fxV, fyV, cv] := rfl
  have ev : K.v = .list [K.st, dd, cd, sr] := rfl
  have wst : K.st.wt < K.v.wt := by rw [ev]; exact wt_le_wt_list (by simp)
  have wfx : fxV.wt < K.st.wt := by rw [est]; exact wt_le_wt_list (by simp)
  have wfy : fyV.wt < K.st.wt := by rw [est]; exact wt_le_wt_list (by simp)
  have efx : (Val.list (K.fx.map pairV)).wt = fxV.wt := rfl
  have efy : (Val.list (K.fy.map pairV)).wt = fyV.wt := rfl
  -- the groups and the dominant sets
  have hgx := it_grp_spec hJ.grp hc1.rng hJ.mpG hJ.sf hc1.app K.fx (W := V) (by omega) (by omega)
  have hgy := it_grp_spec hJ.grp hc1.rng hJ.mpG hJ.sf hc1.app K.fy (W := V) (by omega) (by omega)
  have hdx := (it_dom_spec hJ.dom hJ.orb hc1.rng hJ.fd hJ.pd hc1.cnt (K.fx.map Prod.snd)).mono
    (itDomC_mono (it_grp_wt K.fx (W := V) (by omega) (by omega)))
  have hdy := (it_dom_spec hJ.dom hJ.orb hc1.rng hJ.fd hJ.pd hc1.cnt (K.fy.map Prod.snd)).mono
    (itDomC_mono (it_grp_wt K.fy (W := V) (by omega) (by omega)))
  have hpre := it_hvPre_spec hJ.pre K.sv psV cv dd cd sr K.fx K.fy (itHvPhi K) (itHvPhi' K) _ _
    hgx hgy hdx hdy (V := V) hvw (by omega)
  have htop := it_hvI_spec hJ.f0 K.v K.st _ _ _ hpre (fun htv =>
    it_hv_mid hfac hst hc1 hJ hK hq2 (itHvTv_ne_zero.1 htv) (W₀ := I.inW .giant S) (by omega)
      (by omega))
  refine htop.wt_lt.mono fun w cst ⟨⟨h, hcst⟩, hwt⟩ => ?_
  have hb : itHvIC K.v.wt (itHvPreC V (itGrpC V) (itDomC (100 * (V + 1) ^ 3)))
      (itHvIMC (normalizedFactorPrim hfac) (pointwiseStabPrim hst) krC (I.inW .giant S)) ≤
      itHvIX (normalizedFactorPrim hfac) (pointwiseStabPrim hst) krC (I.inW .giant S) :=
    itHvIC_mono hvw le_rfl le_rfl
  refine ⟨hcst.trans hb, by omega, ?_⟩
  rcases h with ⟨h0, rfl⟩ | ⟨h0, hk⟩
  · exact Or.inl ⟨fun hc' => itHvTv_ne_zero.2 hc' h0, rfl⟩
  · exact Or.inr ⟨itHvTv_ne_zero.1 h0, hk⟩

/-- **Case 2a meets its contract** `ItSCaseOK`, with the init program at `J.f0` (`it_hvInitOK`),
the branch step `itHvBF` at `fb` and the piece program `itHvPcF` at `pc`. -/
theorem itS_c2a_caseOK_full (I : Iface) (hfac : NormalizedFactor) (hst : PointwiseStab)
    {Pg : Program} {F : Funs} {krC : ℕ → ℕ} {J : ItHvIIdx} {IC : ItC1Idx} (hc1 : ItC1Ok Pg IC)
    (hJ : ItHvIOk Pg J IC hfac hst krC) {fb pc : ℕ} (hfb : Pg.funs[fb]? = some (itHvBF pc))
    (hpc : Pg.funs[pc]? = some (itHvPcF IC.cmp IC.app)) :
    ItSCaseOK I Pg F (· = .twoA) J.f0 fb
      (itHvX (itHvIX (normalizedFactorPrim hfac) (pointwiseStabPrim hst) krC)) :=
  itS_c2a_caseOK I Pg (it_hvInitOK I hfac hst hc1 hJ) hfb hpc hc1.cmp hc1.app

end GI.Impl
