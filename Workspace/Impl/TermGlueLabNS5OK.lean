module

public import Workspace.Impl.TermGlueLabNS5C

@[expose] public section

/-!
# The label driver: step 5 meets its contract

Proof of Theorem A.23, step 5. `tmGLN_s5_ok` proves the contract
`Iface.TmGLNS5OK` of the step-5 function `tmGLNS5F dist s5o s5p` of the driver:

* the setup (`tmGLPSetD_spec`, which also handles `t = 0`) with the abelian coordinates of
  `N / N*` (its preconditions `N* ≤ N` and `[N, N] ≤ N*` are those of the row normal form);
* the plain per-generator program (`tmGLPGen_spec`), with the facts of each generator of `S`
  (`tmGLN_gen_hyps`) and the lift bound `Y = tmGLPL1C pf (4 B)` (`tmGLN_lift_size`);
* when all types are distinct, the orientation entries (`tmGLPEps_spec`) and the orientation
  per-generator program (`tmGLPGenO_spec`), then `tmGLPStep5O_spec`;
* the dispatch `tmGLNS5_spec` and the adapters `tmGLN_s5At_plain`, `tmGLN_s5At_or`.

The callees of the setup (abelian coordinates, the quotient by Hermite and Smith forms, the
matrix inverse) enter through their contracts with monotone bounds `FA`, `FQ`, `FI`.
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Lang GI.Paper Equiv
open GI.Cited (Val encPerm encGroup encIntMatrix gens FullRankInst fullRankInput Membership
  NormalizedFactor ConstructiveMembership PointwiseStab)

attribute [local instance] stringRAct

/-- The number of rows is below the weight of the coordinates. -/
private theorem tmGLN_q_lt {Ω C : Type} {k m q : ℕ} (e : Ω ≃ Fin k) (S : State Ω C)
    (E : Fin m × Fin q ≃ S.dom) : q < (coordsVal e S E).wt := by
  have w8 := length_lt_wt_list ((List.finRange q).map fun j =>
    natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))
  simp only [List.length_map, List.length_finRange] at w8
  exact w8

set_option maxHeartbeats 4000000 in
/-- **Step 5 meets its contract.** -/
theorem tmGLN_s5_ok (hm : Membership) (hfac : NormalizedFactor) (hcm : ConstructiveMembership)
    {hst : PointwiseStab} {P : Program}
    {s5 dist s5o s5p s5q setd set items itemsO gen genO eps cons app blk inv half mp off lb xs ov
      or abel mec ec jm quo minv : ℕ}
    (hf : P.funs[s5]? = some (tmGLNS5F dist s5o s5p)) (hd : P.HasAt dist (tmGLNDistFuns dist))
    (h5p : P.funs[s5p]? = some (tmGLPStep5F setd items)) (hit : P.HasAt items (mapFuns items gen))
    (h5q : P.funs[s5q]? = some (tmGLPStep5F setd itemsO))
    (hitO : P.HasAt itemsO (mapFuns itemsO genO))
    (h5o : P.funs[s5o]? = some (tmGLPStep5OF s5q cons))
    (hcons : P.funs[cons]? = some (tmGLPConsF app)) (happ : P.HasAt app (appendFuns app))
    (hgO : P.funs[genO]? = some (tmGLPGenOF inv eps gen cons blk))
    (hblk : P.HasAt blk (tmGLPBlkFuns blk))
    (heps : P.funs[eps]? = some (tmGLPEpsF off or)) (hor : P.HasAt or (tmGLPOrFuns or))
    (hg : P.funs[gen]? = some (tmGLPGenF inv half mp)) (hinv : P.HasAt inv (invFuns inv))
    (hhalf : P.funs[half]? = some (tmGLPHalfF off (lb + 1) xs ov))
    (hoffA : TmGLPOffAt P off hm hfac) (hlA : TmGLPL1At P lb hst hfac) (hxsA : TmGLPXsAt P xs)
    (hovA : TmGLPOVecAt P ov hcm) (hmpA : TmGLPMPairAt P mp hcm)
    {Ce De Cs Ds Cv Dv Cc Dc Cm Dm : ℕ} (hEB : ∀ W, linElementBudget hcm W ≤ Ce * (W + 2) ^ De)
    (hCS : ∀ W, tmGLPCSumC Ce De W ≤ Cs * (W + 2) ^ Ds)
    (hVC : ∀ W t, tmGLPVecC W t ≤ Cv * (W + 0 + t + 2) ^ Dv)
    (hCM : ∀ W, tmGLPCMatC Ce De W ≤ Cc * (W + 2) ^ Dc)
    (hMC : ∀ W t, tmGLPMatC W t ≤ Cm * (W + 0 + t + 2) ^ Dm)
    (hsd : P.funs[setd]? = some (tmGLPSetDF set))
    (hset : P.funs[set]? = some (tmGLPSetF abel mec app quo minv))
    {FA FQ FI : ℕ → ℕ} (hFA : Monotone FA) (hFQ : Monotone FQ) (hFI : Monotone FI)
    (hab : ∀ {n : ℕ} (ns as : List (Perm (Fin n))), gens ns ≤ gens as →
      (∀ x ∈ gens as, ∀ y ∈ gens as, x * y * x⁻¹ * y⁻¹ ∈ gens ns) →
      FunAll P abel (.list [encGroup ns, encGroup as]) (fun out c =>
        (∃ M : Matrix (Fin as.length) (Fin as.length) ℤ, out = encIntMatrix M ∧
          linPermPresentation ns as M) ∧ c ≤ FA (Val.list [encGroup ns, encGroup as]).wt))
    (hmec : P.HasAt mec (mapFuns mec ec)) (hec : linElementCoordinatesAt P ec jm hcm)
    (hquo : ∀ I : FullRankInst, FunAll P quo (fullRankInput I) (fun out c =>
      TmGLQOut I.A out ∧ c ≤ FQ (fullRankInput I).wt))
    (hminv : ∀ {t : ℕ} (ht : 0 < t) (V : Matrix (Fin t) (Fin t) ℤ) (hV : IsUnit V.det),
      FunAll P minv (fullRankInput (tmGLPInst ht V hV)) (fun w c =>
        ∃ U : Matrix (Fin t) (Fin t) ℤ, w = encIntMatrix U ∧ U * V = 1 ∧ V * U = 1 ∧
          c ≤ FI (fullRankInput (tmGLPInst ht V hV)).wt)) :
    Iface.TmGLNS5OK P s5 (tmGLNS5Cost (membershipPrim hm) (normalizedFactorPrim hfac) FA FQ FI
      Ce De Cs Ds Cv Dv Cc Dc Cm Dm) := by
  intro Ω C Pp S L label hnat hq m h0 E hP htr hcard hsN hN hqα k e σS σN bs gs vs xl ps' hσN
    hσS hbs hT hZ hxl hps' hgl hSN B hB
  set pm := membershipPrim hm
  set pf := normalizedFactorPrim hfac
  set lc : Val := .list [liftLabCtx k m ps', coordsVal e S E] with hlc
  set a : Val := tmGLPStep5In σS σN bs vs L.q xl lc gs with ha
  -- weights
  have wlc : lc.wt < a.wt := wt_le_wt_list (by simp)
  have wq : L.q < lc.wt := (tmGLN_q_lt e S E).trans (wt_le_wt_list (by simp))
  have elc : (Val.list [liftLabCtx k m ps', coordsVal e S E]).wt = lc.wt := rfl
  have hqB : L.q ≤ B := by omega
  have hY : tmGLPL1C pf (ps'.length + k + k + L.q + 2) ≤ tmGLPL1C pf (4 * B) :=
    tmGLN_L1C_mono pf ((tmGLN_lift_size e S E ps').trans (by omega))
  -- the row terminal
  have hgs : gens gs ≤ Aut (@id (Subgroup (Perm (Fin m)))
      (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).Hb)
      (types (@id (Subgroup (Perm (Fin m))) (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).Nb)
        (@id (Fin L.q → Fin m → C)
          (rowTuple (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).e S.x))) := hSN
  have hNH : gens σN ≤ (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).Hb := by
    rw [hσN]; exact (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).Nb_le
  have hn : GI.Multicoset.Normalizes (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).Hb (gens σN) := by
    rw [hσN]; exact (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).normalizes
  have hbs' : ∀ b ∈ bs, b ∈ gens σN := fun b hb => by
    obtain ⟨j, hj⟩ := hbs.1 b hb
    exact aut_le _ _ hj
  -- the preconditions of the abelian coordinates: the row normal form
  have hle : gens σS ≤ gens σN := by
    rw [hσS, hσN]
    exact Subgroup.map_mono (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rnf.nstar_le
  have hcomm : ∀ x ∈ gens σN, ∀ y ∈ gens σN, x * y * x⁻¹ * y⁻¹ ∈ gens σS := by
    intro x hx y hy
    rw [hσN] at hx hy
    rw [hσS]
    obtain ⟨a', ha', rfl⟩ := hx
    obtain ⟨b', hb', rfl⟩ := hy
    exact ⟨_, (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rnf.abelian a' ha' b' hb',
      rfl⟩
  have hsetS := tmGLPSetD_spec hcm hsd hset σS σN bs hFA hFQ hFI (hab σS σN hle hcomm) hmec
    hec hEB hbs' happ hquo hminv
  have hSC := tmGLPSetDC_mono hFA hFQ hFI Ce De
  -- the plain per-generator program
  have hG : Monotone (tmGLNS5G pm pf Cs Ds Cv Dv Cc Dc Cm Dm B) :=
    fun _ _ h => tmGLPGenC_mono _ _ _ _ _ _ _ _ _ _ _ h
  have hgenP : ∀ (U V : Matrix (Fin σN.length) (Fin σN.length) ℤ) (d : Fin σN.length → ℤ),
      ∀ g ∈ gs, FunAll P gen (.list [tmGLPHCtx σN U V d vs L.q xl lc, encPerm g]) (fun w c =>
        TmGLPGenOut E ⟨0, by omega⟩ σN (fun i => tmRowStr S E (.inl i)) U V d g w ∧
          c ≤ tmGLNS5G pm pf Cs Ds Cv Dv Cc Dc Cm Dm B
            (Val.list [tmGLPHCtx σN U V d vs L.q xl lc, encPerm g]).wt) := by
    intro U V d g hgm
    obtain ⟨hD, hs, hyN, hs1, hs2⟩ := tmGLN_gen_hyps hnat hq h0 E hP htr hcard hsN hN hqα hσN
      hgs hgm
    exact tmGLPGen_spec hm hfac hcm hg hinv hhalf hoffA hlA hxsA hovA hmpA hEB hCS hVC hCM hMC E
      hnat (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).e_label ⟨0, by omega⟩ hps' hY hNH hn hT hZ hxl
      U V d g hD hs hyN hs1 hs2
  -- the orientation per-generator program
  have hEp : Monotone (tmGLPEpsC pm pf B) := fun _ _ h => tmGLPEpsC_mono _ _ _ h
  have hgenO : ∀ (U V : Matrix (Fin σN.length) (Fin σN.length) ℤ) (d : Fin σN.length → ℤ),
      (types (gens σN) (fun i => tmRowStr S E (.inl i))).Nodup →
      ∀ g ∈ gs, FunAll P genO (.list [tmGLPHCtx σN U V d vs L.q xl lc, encPerm g]) (fun w c =>
        TmGLPGenOOut E ⟨0, by omega⟩ σN (fun i => tmRowStr S E (.inl i)) U V d g w ∧
          c ≤ tmGLPGenOC (tmGLNS5G pm pf Cs Ds Cv Dv Cc Dc Cm Dm B) (tmGLPEpsC pm pf B)
            (Val.list [tmGLPHCtx σN U V d vs L.q xl lc, encPerm g]).wt) := by
    intro U V d hTd g hgm
    obtain ⟨hD, -⟩ := tmGLN_gen_hyps hnat hq h0 E hP htr hcard hsN hN hqα hσN hgs hgm
    refine tmGLPGenO_spec hgO hinv hcons happ hblk hEp E ⟨0, by omega⟩ σN _ U V d vs xl lc g
      (hgenP U V d g hgm) fun h hh => ?_
    have hD' : h⁻¹ ∈ Aut (@id (Subgroup (Perm (Fin m)))
        (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).Hb)
        (types (gens σN) (fun i => tmRowStr S E (.inl i))) := by
      rcases hh with rfl | rfl
      · exact Subgroup.inv_mem _ hD
      · rw [inv_inv]; exact hD
    exact FunAll.mono (tmGLPEps_spec hm hfac heps hoffA hor hNH hn hT hZ hxl ⟨0, by omega⟩ hTd
      hD') fun w c hw => ⟨hw.1, hw.2.trans (tmGLN_epsC_q _ _ hqB _)⟩
  have hGO := tmGLPGenOC_mono hG hEp
  -- the two variants and the dispatch
  have hPl : ¬ (types (gens σN) (fun i => tmRowStr S E (.inl i))).Nodup →
      FunAll P s5p a (fun w c =>
        TmGLPStep5Out E ⟨0, by omega⟩ σS σN bs (fun i => tmRowStr S E (.inl i)) gs w ∧
          c ≤ tmGLPStep5C (tmGLPSetDC FA FQ FI Ce De)
            (tmGLNS5G pm pf Cs Ds Cv Dv Cc Dc Cm Dm B) a.wt) := fun _ =>
    tmGLPStep5_spec h5p hit E ⟨0, by omega⟩ σS σN bs _ vs xl lc gs hSC hG hsetS hgenP
  have hOr : (types (gens σN) (fun i => tmRowStr S E (.inl i))).Nodup →
      FunAll P s5o a (fun w c =>
        TmGLPStep5OOut σS σN bs (TmGLPGenOOut E ⟨0, by omega⟩ σN
          (fun i => tmRowStr S E (.inl i))) gs w ∧
          c ≤ tmGLPStep5OC (tmGLPStep5C (tmGLPSetDC FA FQ FI Ce De)
            (tmGLPGenOC (tmGLNS5G pm pf Cs Ds Cv Dv Cc Dc Cm Dm B) (tmGLPEpsC pm pf B)) a.wt)
            a.wt) := fun hTd =>
    tmGLPStep5O_spec h5o hcons happ σS σN bs _ gs a
      (tmGLPStep5R_spec h5q hitO σS σN bs _ vs xl lc gs hSC hGO hsetS
        fun U V d => hgenO U V d hTd)
  refine (tmGLNS5_spec hf hd σS σN bs vs L.q xl lc gs hxl hOr hPl).mono fun w c hw => ?_
  obtain ⟨hR, hc⟩ := hw
  refine ⟨?_, hc.trans (tmGLN_S5C_mono hB
    (tmGLN_step5OC_mono (tmGLN_step5C_mono hSC hGO hB) hB) (tmGLN_step5C_mono hSC hG hB))⟩
  rcases hR with ⟨hTd, hRO⟩ | ⟨hTd, hRP⟩
  · exact tmGLN_s5At_or hnat hq h0 E hP htr hcard hsN hN hqα hσN hσS hbs hgs
      (by rw [← hσN]; exact hTd) hRO
  · exact tmGLN_s5At_plain hnat hq h0 E hP htr hcard hsN hN hqα hσN hσS hbs hgs
      (by rw [← hσN]; exact hTd) hRP

end GI.Impl
