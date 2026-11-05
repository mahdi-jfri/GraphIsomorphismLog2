module

public import Workspace.Impl.VsQA3M

@[expose] public section

/-!
# The program

On `[lc, encGroup as, Lb]` (after step 2 found that `L` is a field) the program `vsQA3E` computes
`C = C_H(A)` with a transversal `us` (`vsQCent_spec`), the context of step 4 and the abelian test
of `C`. If `C̄` is abelian it returns the split of case 3; otherwise it returns `[3, vsPIn s as Lb
ks us]`, the input of step 4 (`vsQA3_spec`).
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-- Entry `k` of the state, inside the local context in argument 0. -/
def vsQSx (k : ℕ) : Expr := .get (.get (arg 0) (.nat 0)) (.nat k)

/-- Step 3, on `[lc, encGroup as, Lb]`. -/
def vsQA3E (cent ctx ab : ℕ) : Expr :=
  .letE (.call cent (mk2 (vsPMk11 (vsQSx 0) (vsQSx 1) (vsQSx 2) (vsQSx 3) (.get (arg 0) (.nat 1)) (arg 1)
      (vsQSx 1) .nil .nil (.nat 0) (arg 2)) (.get (arg 1) (.nat 1))))
  (.letE (vsPMk5 (arg 0) (arg 1) (arg 2) (.get (.var 1) (.nat 2)) (.get (.var 1) (.nat 1)))
  (.letE (.call ctx (.var 2))
  (.ite (.call ab (mk2 (.var 3) (.get (.var 1) (.nat 2))))
    (mk4 (.nat 1) (.get (.var 1) (.nat 1)) (.get (.var 1) (.nat 2)) (mk1 (vsQSx 2)))
    (mk2 (.nat 3) (.var 2)))))

/-- The indices of step 3. -/
structure VsQA3X where
  (f ctx flm it fl rws rep ab fo no fi nc comp loc eq phi : ℕ) (c : VsHQX)

/-- The layout of step 3. -/
structure VsQA3At (P : Program) (x : VsQA3X) (hps : PointwiseStab) (hm : Membership) : Prop where
  hf : P.funs[x.f]? = some (vsQA3E x.c.q8 x.ctx x.ab)
  C : VsQCLay P x.c hps hm
  hctx : P.funs[x.ctx]? = some (vsPCtxE x.flm x.rws x.rep)
  hflm : P.HasAt x.flm (mapFuns x.flm x.it)
  hit : P.funs[x.it]? = some (vsPFlItemE x.fl)
  hfl : P.HasAt x.fl (vsWFlatFuns x.fl)
  hrws : P.HasAt x.rws (vsWRowsFuns x.rws)
  hrep : P.HasAt x.rep (replicateFuns x.rep)
  hab : P.funs[x.ab]? = some (vsPAbE x.fo)
  hfo : P.HasAt x.fo (findFuns x.fo x.no)
  hno : P.funs[x.no]? = some (vsPNoE x.fi)
  hfi : P.HasAt x.fi (findFuns x.fi x.nc)
  hnc : P.funs[x.nc]? = some (vsPNcE x.comp x.loc x.eq)
  hcomp : P.HasAt x.comp (composeFuns x.comp)
  hloc : P.funs[x.loc]? = some (vsPLocE x.phi (x.loc + 1))
  hwl : P.HasAt (x.loc + 1) (vsWLocFuns (x.loc + 1))
  heq : P.HasAt x.eq (vsPEqFuns x.eq)

/-- What step 3 returns. -/
def VsQA3Out [Fact I.p.Prime] {s : VsQSt I} (hs : VsQStOK s) (as : List (Perm (Fin I.n)))
    (Lb : List (List (List ℕ))) (Tm : ℕ) (w : Val) : Prop :=
  (∃ ts cs lows, w = vsQSplitV ts cs lows ∧ VsQSplitOK s 278 Tm ts cs lows) ∨
    (∃ ks us : List (Perm (Fin I.n)), w = .list [.nat 3, vsPIn s as Lb ks us] ∧ VsPHyp hs as Lb ks ∧
      (∀ u ∈ us, u ∈ gens s.hs) ∧ (∀ h ∈ gens s.hs, ∃ u ∈ us, u⁻¹ * h ∈ gens ks) ∧
      us.length ≤ vsQD s)

/-- The size bound of the transporter in step 3. -/
def vsQSs (S : ℕ) : ℕ := 10 ^ 9 * S ^ 8

/-- The cost of step 3. -/
noncomputable def vsQA3Cost (hps : PointwiseStab) (hm : Membership) (Cφ S : ℕ) : ℕ :=
  vsHQ8Cost hps hm Cφ (vsPN S) I.n (vsQSs S) + vsPCtxPCost (vsPN S) (10 ^ 9 * S ^ 8) +
    vsPAbCost Cφ (vsPN S) (10 ^ 8 * S ^ 6) + 10 ^ 12 * S ^ 8


theorem vsQ_wt_ac {S Tm : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) :
    (vsHAcV s).wt ≤ 1000 * (vsPN S + 1) ^ 3 := by
  have hS1 := hS.one_le
  have hD := vsQD_le hs
  have hSd := hS.d
  have hSp := hS.p
  have hS2 : 2 ≤ S := by have := I.prime.two_le; omega
  have wF := vsQ_wt_fr hS hs
  have wG := hS.g
  have wz : (natList (vsWZ (vsQD s))).wt ≤ 5 * (S + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have l := wt_list_le [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p, .nat (vsQD s),
    natList (vsWZ (vsQD s))]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at l
  have := wt_nat_le I.p; have := wt_nat_le (vsQD s)
  have e : (vsHAcV s).wt = (Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p,
    .nat (vsQD s), natList (vsWZ (vsQD s))]).wt := rfl
  have h1 : (S + 1) ^ 2 ≤ 4 * S ^ 2 := by nlinarith
  have h2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 8 * S ^ 3 ≤ S ^ 6 := by
    have : S ^ 6 = S ^ 3 * S ^ 3 := by ring
    have : 8 ≤ S ^ 3 := by
      have := Nat.pow_le_pow_left hS2 3; simpa using this
    nlinarith
  have h4 : 64 * S ^ 6 ≤ (vsPN S + 1) ^ 3 := by
    have : 4 * S ^ 2 ≤ vsPN S + 1 := by unfold vsPN; omega
    have := Nat.pow_le_pow_left this 3
    have e : (4 * S ^ 2) ^ 3 = 64 * S ^ 6 := by ring
    omega
  have h5 : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
  omega

set_option maxHeartbeats 16000000 in
/-- **Step 3.** -/
theorem vsQA3_spec [Fact I.p.Prime] {P : Program} {x : VsQA3X} {hps : PointwiseStab}
    {hm : Membership} (L : VsQA3At P x hps hm) {Cφ S Tm : ℕ}
    (hphiC : ∀ g ∈ gens I.gs, FunDet P x.c.t.c.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hphiA : ∀ g ∈ gens I.gs, FunDet P x.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) (hTm : (I.d + 1) ^ 278 ≤ Tm) {s : VsQSt I} (hs : VsQStOK s)
    (hD2 : 2 ≤ vsQD s) (hnab : ¬ s.Ab) {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))}
    (h : VsQAHyp hs as Lb) (hdom : vsTDom (vsTAlg (vsPBar hs (gens as)))) :
    FunAll P x.f (.list [vsQLCV s, encGroup as, vsFMatsVal Lb]) (fun w c =>
      VsQA3Out hs as Lb Tm w ∧ c ≤ 64 * vsQA3Cost (I := I) hps hm Cφ S) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hSd := hS.d
  have hSp := hS.p
  have hSn := hS.n
  set D := vsQD s with hD
  set N := vsPN S with hN
  set Ss := vsQSs S with hSs
  set lc := vsQLCV s
  set EG := encGroup as
  set LbV := vsFMatsVal Lb
  set A := Val.list [lc, EG, LbV]
  set stV := vsQStV I s
  set frV := vsWFrVal I.p I.d s.ws' (vsQCs s)
  set MsV := vsFMatsVal (vsQMs s)
  have elc : lc = .list [stV, frV, .nat D, MsV] := rfl
  have est : stV = .list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y] := rfl
  have a0 : ∀ rest, Det P (A :: rest) (arg 0) lc (2 * A.wt + 0 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [lc, EG, LbV]) (rest := rest) (j := 0) rfl
  have a1 : ∀ rest, Det P (A :: rest) (arg 1) EG (2 * A.wt + 1 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [lc, EG, LbV]) (rest := rest) (j := 1) rfl
  have a2 : ∀ rest, Det P (A :: rest) (arg 2) LbV (2 * A.wt + 2 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [lc, EG, LbV]) (rest := rest) (j := 2) rfl
  have dst : ∀ rest, Det P (A :: rest) (.get (arg 0) (.nat 0)) stV _ := fun rest =>
    Det.get' (a0 rest) (Det.nat 0) rfl
  have dsx : ∀ rest (k : ℕ) (v : Val),
      [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y][k]? = some v →
      Det P (A :: rest) (vsQSx k) v _ := fun rest k v hv => Det.get' (dst rest) (Det.nat k) hv
  have dfr : ∀ rest, Det P (A :: rest) (.get (arg 0) (.nat 1)) frV _ := fun rest =>
    Det.get' (a0 rest) (Det.nat 1) rfl
  -- 1. the centralizer
  have hLsq : ∀ M ∈ Lb, VsWSq I.p D M := h.sq
  have hDD : D * D ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
  have hSS : S * S = S ^ 2 := (sq S).symm
  have hLbN : Lb.length ≤ N := by
    have h1 : Lb.length ≤ D * D := h.hLbl
    simp only [N, vsPN]; omega
  have HC := vsPCtx_ok hS hs hLsq hLbN
  have hDD1 : D * D + 1 ≤ N := by simp only [N, vsPN]; have := Nat.one_le_pow 2 S hS1; omega
  have hB : ∀ b ∈ 1 :: as, b ∈ gens s.hs := fun b hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact one_mem _
    · exact h.has (Subgroup.subset_closure hb)
  have hBl : (1 :: as).length ≤ N := by
    have h2 : (I.n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hS.n 2
    have h3 : (I.n + 1) ^ 2 = I.n ^ 2 + 2 * I.n + 1 := by ring
    have := h.hal
    simp only [List.length_cons, N, vsPN]; omega
  haveI : Nontrivial (Fin D → ZMod I.p) := by
    haveI : Nonempty (Fin D) := ⟨⟨0, by omega⟩⟩
    infer_instance
  have hidx : (Subgroup.centralizer (vsPBar hs (gens as) : Set (Module.End (ZMod I.p) (Fin D → ZMod I.p))ˣ)).relIndex
      (vsPBar hs (gens s.hs)) ≤ D := by
    have := vsM_cent (p := I.p) (V := Fin D → ZMod I.p) _ _ h.abNormal hdom
    rwa [Module.finrank_fin_fun] at this
  have hBY : ∀ b ∈ 1 :: as, vsPRho hs b ∈ vsPBar hs (gens as) := fun b hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · rw [vsPRho_one hs]; exact one_mem _
    · exact vsPRho_mem_vsPBar hs (Subgroup.subset_closure hb) (h.has (Subgroup.subset_closure hb))
  -- sizes for the transporter
  have hN4 : (N + 1) ^ 4 ≤ 625 * S ^ 8 := by
    have h1 : N + 1 ≤ 5 * S ^ 2 := by simp only [N, vsPN]; have := Nat.one_le_pow 2 S hS1; omega
    calc (N + 1) ^ 4 ≤ (5 * S ^ 2) ^ 4 := Nat.pow_le_pow_left h1 4
      _ = 625 * S ^ 8 := by ring
  have hN34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have wG := vsQ_wt_LC hS hs
  set G := vsPGIn s as Lb s.hs [] [] 0
  have wLb : LbV.wt ≤ 40 * (N + 1) ^ 4 :=
    wt_vsFMatsVal_le (by simp only [N, vsPN]; have : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _; omega)
      (by simp only [N, vsPN]; have : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _; omega)
      (fun M hM => vsFSq_of_wSq (hLsq M hM)) (by omega)
  have wGr : G.wt ≤ 10 ^ 8 * S ^ 8 := by
    have l := wt_list_le [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, frV, EG, encGroup s.hs,
      Val.list (([] : List (Perm (Fin I.n))).map encPerm), Val.list (([] : List (Perm (Fin I.n))).map encPerm),
      .nat 0, LbV]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at l
    have e : G.wt = (Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, frV, EG, encGroup s.hs,
      Val.list [], Val.list [], .nat 0, LbV]).wt := rfl
    have w1 := hS.g
    have w2 := hS.wt_group hs.hsl
    have w3 := hS.wt_bas hs.fit' hs.wl'
    have w4 := hS.wt_bas hs.fit hs.wl
    have w5 : frV.wt ≤ 100000 * S ^ 3 := vsQ_wt_fr hS hs
    have w6 : EG.wt ≤ 320 * S ^ 6 := hS.wt_group h.hal
    have w7 : (Val.list []).wt ≤ 10 := (wt_list_le []).trans (by simp)
    have w8 := wt_nat_le 0
    have q36 : S ^ 3 ≤ S ^ 8 := hS.pow_le (by omega)
    have q68 : S ^ 6 ≤ S ^ 8 := hS.pow_le (by omega)
    have q18 : S ≤ S ^ 8 := Nat.le_self_pow (by norm_num) _
    omega
  have hcent := vsQCent_spec L.C hphiC HC hDD1 (vsQ_wt_ac hS hs) hB hBl (ccs := s.hs) le_rfl hs.hsl
    (as := as) (Lb := Lb) (tcs := []) (ys := []) (r := 0) hBY hidx
    (Ss := Ss) (by
      have h2 : (I.n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hS.n 2
      have h3 : (I.n + 1) ^ 2 = I.n ^ 2 + 2 * I.n + 1 := by ring
      have : S ^ 2 ≤ S ^ 8 := hS.pow_le (by omega)
      simp only [Ss, vsQSs]; omega)
    (by show 1000 * (N + 1) ^ 3 ≤ Ss; simp only [Ss, vsQSs]; omega)
    (by show 20 * (N + 1) ^ 4 ≤ Ss; simp only [Ss, vsQSs]; omega)
    (by show G.wt + 100 * (N + 1) ^ 3 ≤ Ss; simp only [Ss, vsQSs]; omega)
  -- the program: the centralizer
  have dG := Det.vsPMk11 (dsx [] 0 _ rfl) (dsx [] 1 _ rfl) (dsx [] 2 _ rfl) (dsx [] 3 _ rfl) (dfr [])
    (a1 []) (dsx [] 1 _ rfl) (Det.nil (P := P) (env := [A])) (Det.nil (P := P) (env := [A]))
    (Det.nat (P := P) (env := [A]) 0) (a2 [])
  have eG : Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, frV, EG, encGroup s.hs, Val.list [],
      Val.list [], .nat 0, LbV] = G := rfl
  rw [eG] at dG
  have dB : Det P [A] (.get (arg 1) (.nat 1)) (.list ((1 :: as).map encPerm)) _ :=
    Det.get' (a1 []) (Det.nat 1) rfl
  set CQ := vsHQ8Cost hps hm Cφ N I.n Ss
  refine FunAll.intro L.hf (EvalAll.letE (Q := fun w c => VsQA3Out hs as Lb Tm w ∧
      c ≤ 64 * vsQA3Cost (I := I) hps hm Cφ S)
    (Ra := fun w c => ∃ (Lo : List (List (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) × Perm (Fin I.n)))
        (ks : List (Perm (Fin I.n))),
        w = .list [.nat 2, .list (Lo.map fun q => encPerm q.2), encGroup ks] ∧
        VsQOrbL (vsHAlT s) (1 :: s.hs) ((1 :: as).map (vsHT s)) Lo ∧
        (∀ h, h ∈ gens ks ↔ h ∈ gens s.hs ∧ vsHAlT s h ((1 :: as).map (vsHT s)) = (1 :: as).map (vsHT s)) ∧
        ks.length ≤ I.n ^ 2 ∧ c ≤ 10 ^ 10 * S ^ 8 + 2 * CQ ∧ w.wt ≤ CQ)
    (EvalAll.call_funAll (Det.mk2 dG dB) fun v ca hv => ?_) fun R cR hR => ?_)
  · obtain ⟨rfl, hca⟩ := hv
    refine hcent.wt_lt.mono fun w c hw => ?_
    obtain ⟨⟨Lo, ks, hw1, hLo, hks, hksl, hc⟩, hwc⟩ := hw
    refine ⟨Lo, ks, hw1, hLo, hks, hksl, ?_, by omega⟩
    have wA := wt_list3_le lc EG LbV
    have wlc : lc.wt ≤ 10 ^ 6 * S ^ 6 := vsQ_wt_LC hS hs
    have eA : A.wt = (Val.list [lc, EG, LbV]).wt := rfl
    have w6 : EG.wt ≤ 320 * S ^ 6 := hS.wt_group h.hal
    have hst : stV.wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV, stV])
    have hfr : frV.wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV, frV])
    have hsx : ∀ v ∈ [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y],
        v.wt < stV.wt := fun v hv => wt_le_wt_list hv
    have h0 := hsx _ (by simp : vsQGam I ∈ _); have h1 := hsx _ (by simp : encGroup s.hs ∈ _)
    have h2 := hsx _ (by simp : vsWVs s.ws' ∈ [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y])
    have h3 := hsx _ (by simp : vsWVs s.ws ∈ [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y])
    have hEG1 : (Val.list ((1 :: as).map encPerm)).wt < EG.wt := wt_le_wt_list (by simp [EG, encGroup, encPerms])
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3
    have w2 := wt_list2_le G (Val.list ((1 :: as).map encPerm))
    have q68 : S ^ 6 ≤ S ^ 8 := hS.pow_le (by omega)
    have w11 : (Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, frV, EG, encGroup s.hs, Val.list [],
      Val.list [], .nat 0, LbV]).wt = G.wt := rfl
    clear_value lc EG LbV A stV frV MsV G CQ
    omega
  obtain ⟨Lo, ks, rfl, hLo, hks, hksl, hcR, hwR⟩ := hR
  set us := Lo.map Prod.snd
  set R := Val.list [.nat 2, .list (Lo.map fun q => encPerm q.2), encGroup ks]
  set E1 := [A, R]
  have eus : Val.list (Lo.map fun q => encPerm q.2) = .list (us.map encPerm) := by
    simp [us, List.map_map, Function.comp_def]
  have dR := Det.var' (P := P) (env := E1) (i := 1) rfl
  have dks := Det.get' dR (Det.nat 2) (show [Val.nat 2, .list (Lo.map fun q => encPerm q.2), encGroup ks][2]? =
    some (encGroup ks) from rfl)
  have dus := Det.get' dR (Det.nat 1) (show [Val.nat 2, .list (Lo.map fun q => encPerm q.2), encGroup ks][1]? =
    some (.list (us.map encPerm)) by rw [← eus]; rfl)
  have dIn := Det.vsPMk5 (a0 [R]) (a1 [R]) (a2 [R]) dks dus
  have eIn : Val.list [lc, EG, LbV, encGroup ks, .list (us.map encPerm)] = vsPIn s as Lb ks us := rfl
  rw [eIn] at dIn
  refine EvalAll.letE dIn fun v2 c2 hv2 => ?_
  obtain ⟨rfl, hc2⟩ := hv2
  set In := vsPIn s as Lb ks us
  set E2 := [A, R, In]
  -- facts
  have hK : gens ks ≤ gens s.hs := vsQA3_le h.has hks
  obtain ⟨htmem, hcov⟩ := vsHQ8_cover hs (ccs := s.hs) le_rfl hLo hks
  have hKg : genGroup (1 :: s.hs) ≤ gens s.hs := (Subgroup.closure_le _).2 fun g hg => by
    rcases List.mem_cons.1 hg with rfl | hg
    · exact one_mem _
    · exact Subgroup.subset_closure hg
  have hCb : ∀ g ∈ genGroup (1 :: s.hs), vsPRho hs g ∈ vsPBar hs (gens s.hs) := fun g hg =>
    vsPRho_mem_vsPBar hs (hKg hg) (hKg hg)
  have hus : us.length ≤ D := by
    simp only [us, List.length_map]
    rw [hLo.length_eq]
    exact (vsH_q8_orbit hs hB hKg hCb hBY).trans hidx
  have hns : ∀ g ∈ ks, g ∈ gens I.gs := fun g hg => hs.prob.le (hK (Subgroup.subset_closure hg))
  -- 2. the context
  have wlc : lc.wt ≤ 10 ^ 6 * S ^ 6 := vsQ_wt_LC hS hs
  have wEG : EG.wt ≤ 320 * S ^ 6 := hS.wt_group h.hal
  have wks : (encGroup ks).wt ≤ 320 * S ^ 6 := hS.wt_group hksl
  have wusl : (Val.list (us.map encPerm)).wt ≤ 20 * S ^ 3 := by
    have h1 := vs_wt_list_le_of (us.map encPerm) (c := 4 * S ^ 2) (by
      intro v hv
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hv
      exact hS.wt_perm u)
    rw [List.length_map] at h1
    have h2 : us.length * (2 * (4 * S ^ 2) + 1) ≤ S * (9 * S ^ 2) := Nat.mul_le_mul (by omega)
      (by have := Nat.one_le_pow 2 S hS1; omega)
    have e : S * (9 * S ^ 2) = 9 * S ^ 3 := by ring
    have := Nat.one_le_pow 3 S hS1
    omega
  have q68 : S ^ 6 ≤ S ^ 8 := hS.pow_le (by omega)
  have q38 : S ^ 3 ≤ S ^ 8 := hS.pow_le (by omega)
  have q08 : 1 ≤ S ^ 8 := Nat.one_le_pow _ _ hS1
  have hW2 : In.wt ≤ 10 ^ 9 * S ^ 8 := by
    have l := wt_list_le [lc, EG, LbV, encGroup ks, .list (us.map encPerm)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at l
    have e : In.wt = (Val.list [lc, EG, LbV, encGroup ks, .list (us.map encPerm)]).wt := rfl
    omega
  have dctx := Det.call (Det.var' (P := P) (env := E2) (i := 2) rfl)
    (vsPCtxP_spec L.hctx L.hflm L.hit L.hfl L.hrws L.hrep hs (N := N) (W := 10 ^ 9 * S ^ 8)
      (by simp only [N, vsPN]; have : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _; omega)
      (by show D * D ≤ N; simp only [N, vsPN]; omega) hLsq hLbN hW2)
  refine EvalAll.letE dctx fun v3 c3 hv3 => ?_
  obtain ⟨rfl, hc3⟩ := hv3
  set CV := vsPCtx I s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs
  set E3 := [A, R, In, CV]
  -- 3. the abelian test
  have dks3 := Det.get' (Det.var' (P := P) (env := E3) (i := 1) rfl) (Det.nat 2)
    (show [Val.nat 2, .list (Lo.map fun q => encPerm q.2), encGroup ks][2]? = some (encGroup ks) from rfl)
  have dab := Det.call (Det.mk2 (Det.var' (P := P) (env := E3) (i := 3) rfl) dks3)
    (vsPAb_spec L.hab L.hfo L.hno L.hfi L.hnc L.hcomp L.hloc L.hwl L.heq hphiA HC hns hksl)
  by_cases ht : ∀ g ∈ 1 :: ks, ∀ h ∈ 1 :: ks,
      vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g)
  · -- `C̄` is abelian: the split of case 3
    have ev : boolVal (decide (∀ g ∈ 1 :: ks, ∀ h ∈ 1 :: ks,
        vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g))) = .nat 1 := by
      rw [decide_eq_true ht]; rfl
    rw [ev] at dab
    have dus3 := Det.get' (Det.var' (P := P) (env := E3) (i := 1) rfl) (Det.nat 1)
      (show [Val.nat 2, .list (Lo.map fun q => encPerm q.2), encGroup ks][1]? =
        some (.list (us.map encPerm)) by rw [← eus]; rfl)
    have dws := Det.get' (Det.get' (a0 [R, In, CV]) (Det.nat 0) rfl) (Det.nat 2)
      (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y][2]? =
        some (vsWVs s.ws') from rfl)
    have dout := Det.mk4 (Det.nat (P := P) (env := E3) 1) dus3 dks3 (Det.mk1 dws)
    have eout : Val.list [.nat 1, .list (us.map encPerm), encGroup ks, .list [vsWVs s.ws']] =
      vsQSplitV us ks [s.ws'] := rfl
    rw [eout] at dout
    refine Det.post (Det.ite_pos dab one_ne_zero dout) fun c hc => ⟨Or.inl ⟨us, ks, [s.ws'], rfl, ?_⟩, ?_⟩
    · exact vsQA3_splitOK hs hksl hK htmem hcov
        (le_trans hus (le_trans (by omega) ((Nat.le_self_pow (by norm_num) _).trans
          ((Nat.pow_le_pow_left (by omega) 278).trans hTm))))
        (vsQAb_of_comm hs hK (vsQ_comm_of_test hs hK ht)) hnab hD2 hus
    · have wA3 := wt_list3_le lc EG LbV
      have eA : A.wt = (Val.list [lc, EG, LbV]).wt := rfl
      have wLbN : LbV.wt ≤ 25000 * S ^ 8 := by omega
      have wCV : CV.wt < vsPCtxPCost N (10 ^ 9 * S ^ 8) := FunDet.wt_lt' (vsPCtxP_spec L.hctx L.hflm L.hit
        L.hfl L.hrws L.hrep hs (N := N) (W := 10 ^ 9 * S ^ 8)
        (by simp only [N, vsPN]; have : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _; omega)
        (by show D * D ≤ N; simp only [N, vsPN]; omega) hLsq hLbN hW2)
      have eR : R.wt = (Val.list [.nat 2, .list (us.map encPerm), encGroup ks]).wt := by
        simp only [R]; rw [eus]
      have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3
      have l5 := wt_list_le [lc, EG, LbV, encGroup ks, .list (us.map encPerm)]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil] at l5
      have eIn : In.wt = (Val.list [lc, EG, LbV, encGroup ks, .list (us.map encPerm)]).wt := rfl
      have l3 := wt_list3_le (.nat 2) (.list (us.map encPerm)) (encGroup ks)
      have l2 := wt_list2_le CV (encGroup ks)
      have hksR : (encGroup ks).wt < R.wt := wt_le_wt_list (by simp [R])
      unfold vsQA3Cost
      rw [← hN, ← hSs]
      have eR' : (Val.list [Val.nat 2, Val.list (List.map (fun q => encPerm q.2) Lo), encGroup ks]).wt = R.wt := rfl
      have eCQ : CQ = vsHQ8Cost hps hm Cφ N I.n Ss := rfl
      have eAb : vsPAbCost Cφ (vsPN S) (10 ^ 8 * S ^ 6) = vsPAbCost Cφ N (10 ^ 8 * S ^ 6) := rfl
      have wws := hS.wt_bas hs.fit' hs.wl'
      have hst2 : (Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x,
          natList s.y]).wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV, vsQStV])
      have hws2 : (vsWVs s.ws').wt < (Val.list [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
          natList s.x, natList s.y]).wt := wt_le_wt_list (by simp)
      have l4 := wt_list4_le (.nat 1) (.list (us.map encPerm)) (encGroup ks) (.list [vsWVs s.ws'])
      have l1 := wt_list1_le (vsWVs s.ws')
      have eO : (vsQSplitV us ks [s.ws']).wt = (Val.list [.nat 1, .list (us.map encPerm), encGroup ks,
        .list [vsWVs s.ws']]).wt := rfl
      clear_value lc EG LbV A stV frV MsV G CQ R In CV us
      omega
  · -- `C̄` is not abelian: the input of step 4
    have ev : boolVal (decide (∀ g ∈ 1 :: ks, ∀ h ∈ 1 :: ks,
        vsPLocL I s.ws' (vsQCs s) (g * h) = vsPLocL I s.ws' (vsQCs s) (h * g))) = .nat 0 := by
      rw [decide_eq_false ht]; rfl
    rw [ev] at dab
    have dout := Det.mk2 (Det.nat (P := P) (env := E3) 3) (Det.var' (P := P) (env := E3) (i := 2) rfl)
    refine Det.post (Det.ite_zero dab dout) fun c hc => ⟨Or.inr ⟨ks, us, rfl,
      ⟨h.has, h.hasn, h.hal, h.habl, hdom, h.hLb, h.hspan, h.hLbl, hK, vsQA3_normd h.has hks hs h.hasn,
        hksl, vsQA3_cent h.has hks, vsQ_nab_of_test hs hK ht, vsQA_solv hs⟩, htmem, hcov, hus⟩, ?_⟩
    have wA3 := wt_list3_le lc EG LbV
    have eA : A.wt = (Val.list [lc, EG, LbV]).wt := rfl
    have wLbN : LbV.wt ≤ 25000 * S ^ 8 := by omega
    have wCV : CV.wt < vsPCtxPCost N (10 ^ 9 * S ^ 8) := FunDet.wt_lt' (vsPCtxP_spec L.hctx L.hflm L.hit
      L.hfl L.hrws L.hrep hs (N := N) (W := 10 ^ 9 * S ^ 8)
      (by simp only [N, vsPN]; have : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _; omega)
      (by show D * D ≤ N; simp only [N, vsPN]; omega) hLsq hLbN hW2)
    have eR : R.wt = (Val.list [.nat 2, .list (us.map encPerm), encGroup ks]).wt := by
      simp only [R]; rw [eus]
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3
    have l5 := wt_list_le [lc, EG, LbV, encGroup ks, .list (us.map encPerm)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at l5
    have eIn : In.wt = (Val.list [lc, EG, LbV, encGroup ks, .list (us.map encPerm)]).wt := rfl
    have l3 := wt_list3_le (.nat 2) (.list (us.map encPerm)) (encGroup ks)
    have l2 := wt_list2_le CV (encGroup ks)
    have hksR : (encGroup ks).wt < R.wt := wt_le_wt_list (by simp [R])
    unfold vsQA3Cost
    rw [← hN, ← hSs]
    have eR' : (Val.list [Val.nat 2, Val.list (List.map (fun q => encPerm q.2) Lo), encGroup ks]).wt = R.wt := rfl
    have eCQ : CQ = vsHQ8Cost hps hm Cφ N I.n Ss := rfl
    have eAb : vsPAbCost Cφ (vsPN S) (10 ^ 8 * S ^ 6) = vsPAbCost Cφ N (10 ^ 8 * S ^ 6) := rfl
    have l2' := wt_list2_le (.nat 3) In
    clear_value lc EG LbV A stV frV MsV G CQ R In CV us
    omega

end GI.Impl
