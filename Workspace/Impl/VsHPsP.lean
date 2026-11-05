module

public import Workspace.Impl.VsHSplitHyp
public import Workspace.Impl.VsHQ8P
public import Workspace.Impl.VsWProgId
public import Workspace.Impl.VsFAlgSpanProg
public import Workspace.Impl.VsWProgNil
public import Workspace.Impl.VsWProgEig
public import Workspace.Impl.VsQAnaAb

@[expose] public section

/-!
# The program for the pieces

On `[vsPGIn s as Lb ccs tcs ys r, K]` the program `vsHPsE` computes the stored local matrices of
`L = (1 :: as) ++ K`, a basis of the algebra they generate (`vsFAlgSpan`), its Frobenius fixed
points (`vsFFix`) and the pieces (`vsFEig`), and returns `vsFMatsVal (vsHPs s L)` (`vsHPs_spec`).
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I}

theorem vsHBm_length [Fact I.p.Prime] (L : List (Perm (Fin I.n))) : (vsHBm s L).length ≤ vsQD s * vsQD s := by
  have h := (vsFAlgSpanL_span I.prime (vsWZ_zero I.prime.pos (vsQD s)) (vsWId_sq I.prime.one_lt _)
    (vsFMatrix_vsWId _) fun g hg => vsFSq_of_wSq (vsHGms_sq (s := s) L g hg)).1
  rw [vsHBm, ← h.nb]
  exact vsFA_ech_length I.prime h.ech fun r hr => (h.len r hr).1

/-- The item of the map: on `[[Γ, frame], g]`, the stored local matrix of `g`. -/
def vsHLocItE (loc : ℕ) : Expr := .call loc (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1))

/-- The prime and the dimension, read from the hand-off value. -/
def vsHPp : Expr := .get vsHF0 (.nat 0)
def vsHDd : Expr := .length (.get vsHF0 (.nat 3))

/-- The pieces program, on `[vsPGIn …, K]`. -/
def vsHPsE (app mp idp alg fix eig : ℕ) : Expr :=
  .letE (.call app (mk2 (.get (vsHG 5) (.nat 1)) (arg 1)))
  (.letE (.call mp (mk2 (mk2 (vsHG 0) (vsHG 4)) (.var 1)))
  (.letE (.call idp vsHDd)
  (.letE (.call alg (mk4 vsHPp (.var 2) (.get vsHF0 (.nat 3)) (.var 3)))
    (.call eig (mk3 vsHPp vsHDd (.call fix (mk3 vsHPp vsHDd (.get (.var 4) (.nat 1)))))))))

/-- The cost of the pieces program. -/
def vsHPsCost (Cφ N : ℕ) : ℕ := (N + 1) * (vsPLocCost Cφ N + 10 ^ 4 * (N + 1) ^ 3) + 10 ^ 19 * (N + 1) ^ 8

/-- The indices of the pieces program. -/
structure VsHPX where
  (ps app mp it loc phi idp alg fix eig : ℕ)

/-- The layout of the pieces program. -/
structure VsHPLay (P : Program) (x : VsHPX) : Prop where
  hps : P.funs[x.ps]? = some (vsHPsE x.app x.mp x.idp x.alg x.fix x.eig)
  happ : P.HasAt x.app (appendFuns x.app)
  hmp : P.HasAt x.mp (mapFuns x.mp x.it)
  hit : P.funs[x.it]? = some (vsHLocItE x.loc)
  hloc : P.funs[x.loc]? = some (vsPLocE x.phi (x.loc + 1))
  hwl : P.HasAt (x.loc + 1) (vsWLocFuns (x.loc + 1))
  hidp : P.HasAt x.idp (vsWIdFuns x.idp)
  halg : P.HasAt x.alg (vsFAlgSpanFuns x.alg)
  hfix : P.HasAt x.fix (vsFFixFuns x.fix)
  heig : P.HasAt x.eig (vsFEigFuns x.eig)

set_option maxHeartbeats 8000000 in
/-- **The pieces program.** -/
theorem vsHPs_spec [Fact I.p.Prime] {P : Program} {x : VsHPX} (L : VsHPLay P x) {Cφ N : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hs : VsQStOK s) {as ccs tcs ys : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))} {r : ℕ}
    (hsz : VsQSz I.p I.d (vsQExp I) N) (hΓ : (vsQGam I).wt ≤ N) (hn : I.n ≤ N)
    (hfr : VsWFrOK I.p N I.d s.ws' (vsQCs s))
    {K : List (Perm (Fin I.n))} (has : gens as ≤ gens s.hs) (hK : ∀ g ∈ K, g ∈ gens s.hs)
    (hN : 1 + vsQD s * vsQD s * ((1 :: as) ++ K).length ≤ N)
    (hLl : ((1 :: as) ++ K).length ≤ N) (hW : (vsPGIn s as Lb ccs tcs ys r).wt ≤ N) :
    FunDet P x.ps (.list [vsPGIn s as Lb ccs tcs ys r, .list (K.map encPerm)])
      (vsFMatsVal (vsHPs s ((1 :: as) ++ K))) (vsHPsCost Cφ N) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hpN := hsz.pN
  set D := vsQD s
  set LL := (1 :: as) ++ K
  set A := vsPGIn s as Lb ccs tcs ys r
  set fr := vsWFrVal I.p I.d s.ws' (vsQCs s)
  set F0 := Val.list [.nat I.p, .nat I.d, natList (vsWZ I.d), natList (vsWZ (vsQCs s).length)]
  set gl := [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, fr, encGroup as, encGroup ccs,
    Val.list (tcs.map encPerm), Val.list (ys.map encPerm), .nat r, vsFMatsVal Lb]
  set vs := [A, Val.list (K.map encPerm)]
  have rd : ∀ (rest : List Val) (k : ℕ) (v : Val), gl[k]? = some v →
      Det P (Val.list vs :: rest) (vsHG k) v (2 * (Val.list vs).wt + 0 + 5 + (k + 3) + v.wt + 1) := by
    intro rest k v h
    have a0 : Det P (Val.list vs :: rest) (arg 0) (.list gl) _ :=
      Det.arg' (P := P) (vs := vs) (rest := rest) (j := 0) rfl
    exact Det.get' a0 (Det.nat k) h
  have hvA : A.wt < (Val.list vs).wt := wt_le_wt_list (by simp [vs])
  have eA : A.wt = (Val.list gl).wt := rfl
  have hfr' : fr.wt < (Val.list gl).wt := wt_le_wt_list (by simp [gl])
  have hF0 : F0.wt < fr.wt := wt_le_wt_list (by simp [fr, F0, vsWFrVal])
  have hpF : (Val.nat I.p).wt < F0.wt := wt_le_wt_list (by simp [F0])
  have hzF : (natList (vsWZ (vsQCs s).length)).wt < F0.wt := wt_le_wt_list (by simp [F0])
  have w0 := wt_nat_le 0; have w3 := wt_nat_le 3; have w4 := wt_nat_le 4
  have rF : ∀ rest : List Val, ∃ c, Det P (Val.list vs :: rest) vsHF0 F0 c ∧ c ≤ 6 * (Val.list vs).wt + 40 :=
    fun rest => ⟨_, Det.get' (rd rest 4 fr rfl) (Det.nat 0) rfl, by omega⟩
  have rp : ∀ rest : List Val, ∃ c, Det P (Val.list vs :: rest) vsHPp (.nat I.p) c ∧
      c ≤ 8 * (Val.list vs).wt + 60 := by
    intro rest
    obtain ⟨c, d, hc⟩ := rF rest
    exact ⟨_, Det.get' d (Det.nat 0) rfl, by omega⟩
  have ezz : (natList (vsWZ D)).wt = (natList (vsWZ (vsQCs s).length)).wt := rfl
  have rz : ∀ rest : List Val, ∃ c, Det P (Val.list vs :: rest) (.get vsHF0 (.nat 3))
      (natList (vsWZ D)) c ∧ c ≤ 8 * (Val.list vs).wt + 60 := by
    intro rest
    obtain ⟨c, d, hc⟩ := rF rest
    exact ⟨_, Det.get' d (Det.nat 3) rfl, by omega⟩
  have rD : ∀ rest : List Val, ∃ c, Det P (Val.list vs :: rest) vsHDd (.nat D) c ∧
      c ≤ 10 * (Val.list vs).wt + 80 := by
    intro rest
    obtain ⟨c, d, hc⟩ := rz rest
    have := Det.length d
    rw [List.length_map, show (vsWZ D).length = D by simp [vsWZ]] at this
    refine ⟨_, this, ?_⟩
    have : D ≤ (Val.list ((vsWZ D).map Val.nat)).wt := by
      have h0 := length_lt_wt_list ((vsWZ D).map Val.nat)
      rw [List.length_map, show (vsWZ D).length = D by simp [vsWZ]] at h0
      omega
    have e : (Val.list ((vsWZ D).map Val.nat)).wt = (natList (vsWZ (vsQCs s).length)).wt := rfl
    omega
  -- 1. the list `(1 :: as) ++ K`
  have dG : Det P [Val.list vs] (.get (vsHG 5) (.nat 1)) (.list ((1 :: as).map encPerm)) _ :=
    Det.get' (rd [] 5 (encGroup as) rfl) (Det.nat 1) rfl
  have dK := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  obtain ⟨KA, hKA, dA⟩ : ∃ KA, KA = _ ∧ Det P [Val.list vs] (mk2 (.get (vsHG 5) (.nat 1)) (arg 1))
      (.list [.list ((1 :: as).map encPerm), .list (K.map encPerm)]) KA := ⟨_, rfl, Det.mk2 dG dK⟩
  set KP := loopModK * (K.length + 1) * ((Val.list [.list ((1 :: as).map encPerm),
    .list (K.map encPerm)]).wt + K.length + (Val.list (LL.map encPerm)).wt + 1)
  have d1 : Det P [Val.list vs] (.call x.app (mk2 (.get (vsHG 5) (.nat 1)) (arg 1)))
      (.list (LL.map encPerm)) (KA + KP + (Val.list (LL.map encPerm)).wt + 1) := by
    refine EvalAll.call_funAll dA fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (append_spec L.happ ((1 :: as).map encPerm) (K.map encPerm)).mono fun w c hw => ?_
    have hw1 : w = .list (LL.map encPerm) := by rw [hw.1, ← List.map_append]
    refine ⟨hw1, ?_⟩
    have h2 := hw.2
    rw [List.length_map, hw1] at h2
    rw [hw1]
    have hKP : loopModK * (K.length + 1) * ((Val.list [.list ((1 :: as).map encPerm),
      .list (K.map encPerm)]).wt + K.length + (Val.list (LL.map encPerm)).wt + 1) = KP := rfl
    omega
  -- 2. the stored local matrices
  have hLs : ∀ g ∈ LL, g ∈ gens s.hs := fun g hg => by
    rcases List.mem_append.1 hg with hg | hg
    · rcases List.mem_cons.1 hg with rfl | hg
      · exact one_mem _
      · exact has (Subgroup.subset_closure hg)
    · exact hK g hg
  set E1 := [Val.list vs, Val.list (LL.map encPerm)]
  have hitm : ∀ g ∈ LL, FunDet P x.it (.list [.list [vsQGam I, fr], encPerm g])
      (vsWVs (vsPLocL I s.ws' (vsQCs s) g)) (vsPLocCost Cφ N + 10 ^ 4 * (N + 1) ^ 3) := by
    intro g hg
    have c0 := Det.arg' (P := P) (vs := [.list [vsQGam I, fr], encPerm g]) (rest := []) (j := 0) rfl
    have c1 := Det.arg' (P := P) (vs := [.list [vsQGam I, fr], encPerm g]) (rest := []) (j := 1) rfl
    have cΓ := Det.get' c0 (Det.nat 0) (show [vsQGam I, fr][0]? = some (vsQGam I) from rfl)
    have cF := Det.get' c0 (Det.nat 1) (show [vsQGam I, fr][1]? = some fr from rfl)
    refine FunDet.intro L.hit ((Det.call (Det.mk3 cΓ cF c1) (vsPLoc_spec L.hloc L.hwl hphi hsz hΓ hn hfr
      (hs.prob.le (hLs g hg)))).mono ?_)
    have wF : fr.wt ≤ 500 * (N + 1) ^ 3 := wt_vsWFrVal_le hfr
    have wg := wt_encPerm_le g
    have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have l1 := wt_list2_le (vsQGam I) fr
    have l2 := wt_list2_le (Val.list [vsQGam I, fr]) (encPerm g)
    have l3 := wt_list3_le (vsQGam I) fr (encPerm g)
    have hsq := vsPLocL_sq (I := I) (ws' := s.ws') (cs := vsQCs s) g
    have hDN' : (vsQCs s).length ≤ N := by have := hfr.hl; omega
    have wL := wt_vsWVs_le (N := N) (VsWFit.bnd hsq.1 hpN hDN') (by rw [hsq.2]; omega)
    have q13 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by omega) _
    have := wt_nat_le 0; have := wt_nat_le 1
    omega
  have d2 := Det.call (Det.mk2 (Det.mk2 (rd [Val.list (LL.map encPerm)] 0 (vsQGam I) rfl)
    (rd [Val.list (LL.map encPerm)] 4 fr rfl)) (Det.var' (P := P) (env := E1) (i := 1) rfl))
    (vsQ_map L.hmp LL encPerm (fun g => vsWVs (vsPLocL I s.ws' (vsQCs s) g)) encPerm_injective hitm)
  have eG : Val.list (LL.map fun g => vsWVs (vsPLocL I s.ws' (vsQCs s) g)) = vsFMatsVal (vsHGms s LL) := by
    simp [vsFMatsVal, vsHGms, vsWVs, List.map_map, Function.comp_def]
  rw [eG] at d2
  set G := vsHGms s LL
  -- 3. the identity
  set E2 := [Val.list vs, Val.list (LL.map encPerm), vsFMatsVal G]
  have hDD : D * D ≤ N := by
    have : D * D ≤ D * D * LL.length := Nat.le_mul_of_pos_right _ (by simp [LL])
    omega
  have hDN : D ≤ N := (Nat.le_mul_self D).trans hDD
  obtain ⟨cD2, dD2, hcD2⟩ := rD [Val.list (LL.map encPerm), vsFMatsVal G]
  have d3 := Det.call dD2 (vsWId_spec L.hidp hDN)
  -- 4. the algebra
  set E3 := [Val.list vs, Val.list (LL.map encPerm), vsFMatsVal G, vsWVs (vsWId D)]
  obtain ⟨cp3, dp3, hcp3⟩ := rp [Val.list (LL.map encPerm), vsFMatsVal G, vsWVs (vsWId D)]
  obtain ⟨cz3, dz3, hcz3⟩ := rz [Val.list (LL.map encPerm), vsFMatsVal G, vsWVs (vsWId D)]
  have dalg := Det.call (Det.mk4 dp3 (Det.var' (P := P) (env := E3) (i := 2) rfl) dz3
    (Det.var' (P := P) (env := E3) (i := 3) rfl))
    (vsFAlgSpan_spec L.halg I.prime.pos hpN hDD (gs := G)
      (fun g hg => vsFSq_of_wSq (vsHGms_sq LL g hg)) (by simpa [G, vsHGms] using hN)
      (by simpa [G, vsHGms] using hLl)
      (fun y hy => by have := I.prime.pos; simp [vsWZ] at hy; omega) (by simp [vsWZ])
      (vsWId_sq I.prime.one_lt D))
  -- 5. the fixed points and 6. the pieces
  set st := vsFAlgSpanL I.p (vsWZ D) (vsWId D) G (D * D)
  set E4 := [Val.list vs, Val.list (LL.map encPerm), vsFMatsVal G, vsWVs (vsWId D), vsFAVal st]
  have dBm := Det.get' (Det.var' (P := P) (env := E4) (i := 4) rfl) (Det.nat 1)
    (show [vsAccVal st.1, vsFMatsVal st.2][1]? = some (vsFMatsVal st.2) from rfl)
  have eBm : st.2 = vsHBm s LL := rfl
  rw [eBm] at dBm
  obtain ⟨cp4, dp4, hcp4⟩ := rp [Val.list (LL.map encPerm), vsFMatsVal G, vsWVs (vsWId D), vsFAVal st]
  obtain ⟨cD4, dD4, hcD4⟩ := rD [Val.list (LL.map encPerm), vsFMatsVal G, vsWVs (vsWId D), vsFAVal st]
  have hBl : (vsHBm s LL).length ≤ N := (vsHBm_length LL).trans hDD
  have dfix := Det.call (Det.mk3 dp4 dD4 dBm) (vsFFix_spec L.hfix I.prime.one_lt hpN hDD
    (vsHBm_sq LL) hBl)
  have hFl : (vsHFx s LL).length ≤ N :=
    (vsFFixL_length I.prime.one_lt hpN hDD (vsHBm_sq LL) hBl).trans hBl
  have deig := Det.call (Det.mk3 dp4 dD4 dfix) (vsFEig_spec L.heig I.prime hpN hDN
    (vsHFx_sq LL) hFl)
  refine FunDet.intro L.hps ((Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE dalg deig)))).mono ?_)
  -- weights
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q47 : (N + 1) ^ 4 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have q78 : (N + 1) ^ 7 ≤ (N + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hKl : K.length ≤ N := by simp [LL] at hLl; omega
  have wK := vsP_wt_perms hn K (by omega)
  have wLL := vsP_wt_perms hn LL (by omega)
  have was := vsP_wt_perms hn (1 :: as) (by simp [LL] at hLl ⊢; omega)
  have wvs := wt_list2_le A (Val.list (K.map encPerm))
  have evs : (Val.list vs).wt = (Val.list [A, Val.list (K.map encPerm)]).wt := rfl
  have wF : fr.wt ≤ 500 * (N + 1) ^ 3 := wt_vsWFrVal_le hfr
  have wG : (vsFMatsVal G).wt ≤ 40 * (N + 1) ^ 4 :=
    wt_vsFMatsVal_le hpN hDN (fun g hg => vsFSq_of_wSq (vsHGms_sq LL g hg)) (by simp [G, vsHGms]; omega)
  have wBm : (vsFMatsVal (vsHBm s LL)).wt ≤ 40 * (N + 1) ^ 4 :=
    wt_vsFMatsVal_le hpN hDN (fun M hM => vsFSq_of_wSq (vsHBm_sq LL M hM)) (by omega)
  have wFx : (vsFMatsVal (vsFFixL I.p D (vsHBm s LL))).wt ≤ 40 * (N + 1) ^ 4 :=
    wt_vsFMatsVal_le hpN hDN (fun M hM => vsFSq_of_wSq (vsHFx_sq LL M hM)) (by
      have : (vsFFixL I.p D (vsHBm s LL)).length ≤ N := hFl
      omega)
  have wId : (vsWVs (vsWId D)).wt ≤ 11 * (N + 1) ^ 3 + 4 :=
    wt_vsWVs_le (fun u hu => ⟨fun y hy => ((vsWId_fit I.prime.one_lt D u hu).1 y hy).le.trans hpN,
      by rw [(vsWId_fit I.prime.one_lt D u hu).2]; exact hDN⟩) (by simp [vsWId]; omega)
  have wSt : (vsFAVal st).wt < 10 ^ 9 * (N + 1) ^ 7 := FunDet.wt_lt' (vsFAlgSpan_spec L.halg I.prime.pos
      hpN hDD (gs := G) (fun g hg => vsFSq_of_wSq (vsHGms_sq LL g hg)) (by simpa [G, vsHGms] using hN)
      (by simpa [G, vsHGms] using hLl)
      (fun y hy => by have := I.prime.pos; simp [vsWZ] at hy; omega) (by simp [vsWZ])
      (vsWId_sq I.prime.one_lt D))
  have eSt : (Val.list [vsAccVal st.1, vsFMatsVal (vsHBm s LL)]).wt = (vsFAVal st).wt := rfl
  have wPs : (vsFMatsVal (vsFEigL I.p D (vsFFixL I.p D (vsHBm s LL)))).wt < 10 ^ 17 * (N + 1) ^ 8 :=
    FunDet.wt_lt' (vsFEig_spec L.heig I.prime hpN hDN (vsHFx_sq LL) hFl)
  have hzD : (natList (vsWZ D)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wp := wt_nat_le I.p
  have wD := wt_nat_le D
  have l1 := wt_list_le [Val.nat I.p, vsFMatsVal G, natList (vsWZ D), vsWVs (vsWId D)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at l1
  have l2 := wt_list3_le (Val.nat I.p) (Val.nat D) (vsFMatsVal (vsHBm s LL))
  have l3 := wt_list3_le (Val.nat I.p) (Val.nat D) (vsFMatsVal (vsFFixL I.p D (vsHBm s LL)))
  have l4 := wt_list2_le (vsQGam I) fr
  have l5 := wt_list2_le (Val.list [vsQGam I, fr]) (Val.list (LL.map encPerm))
  have l6 := wt_list2_le (Val.list ((1 :: as).map encPerm)) (Val.list (K.map encPerm))
  have hga : (encGroup as).wt < (Val.list gl).wt := wt_le_wt_list (by simp [gl])
  have hG' : (vsQGam I).wt < (Val.list gl).wt := wt_le_wt_list (by simp [gl])
  have hM1 : LL.length * (vsPLocCost Cφ N + 10 ^ 4 * (N + 1) ^ 3) ≤
      (N + 1) * (vsPLocCost Cφ N + 10 ^ 4 * (N + 1) ^ 3) := Nat.mul_le_mul_right _ (by omega)
  have hM2 : mapK * (LL.length + 1) * ((Val.list [Val.list [vsQGam I, fr],
      Val.list (List.map encPerm LL)]).wt + (vsFMatsVal G).wt + 1) ≤
      1000 * (N + 1) * (2000 * (N + 1) ^ 4) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have eM2 : 1000 * (N + 1) * (2000 * (N + 1) ^ 4) = 2 * 10 ^ 6 * (N + 1) ^ 5 := by ring
  have q58 : (N + 1) ^ 5 ≤ (N + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hKP' : KP ≤ 1000 * (N + 1) * (200 * (N + 1) ^ 3) := by
    simp only [KP]
    exact Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have eKP : 1000 * (N + 1) * (200 * (N + 1) ^ 3) = 2 * 10 ^ 5 * (N + 1) ^ 4 := by ring
  have mk : mapK = 1000 := rfl
  clear_value KP
  unfold vsHPsCost
  linarith

end GI.Impl
