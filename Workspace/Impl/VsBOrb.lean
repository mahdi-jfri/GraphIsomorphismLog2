import Workspace.Proved.VsBAff
import Workspace.Impl.VsQDrvC

/-!
# A leaf answer from a small orbit

On a valid state whose point `x̄ ∈ (x + W)/W'` has a small orbit under `H` (at most `B`
points), the small orbit transporter for the affine action `vsBAlpha` (on local coordinates,
keys `vsQVec`) gives the orbit with a transversal and the stabilizer. The answer is the
transversal element at the coordinates of `ȳ`, if they occur, with the stabilizer.

* `vsBOrbFuns b phi jp jm` (213 functions), `vsBOrb_spec`: on `[vsQStV I s, B]` a leaf
  `vsQLeafV a` with `VsQAnsOK hs.prob a`. This is the result used later (with `B = p` for `D = 1`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- A list of five values. -/
def vsBmk5 (a b c d e : Expr) : Expr := .snoc (mk4 a b c d) e

theorem Det.vsBmk5 {P : Program} {env : List Val} {a b c d e : Expr} {va vb vc vd ve : Val}
    {ca cb cc cd ce : ℕ} (ha : Det P env a va ca) (hb : Det P env b vb cb) (hc : Det P env c vc cc)
    (hd : Det P env d vd cd) (he : Det P env e ve ce) :
    Det P env (vsBmk5 a b c d e) (.list [va, vb, vc, vd, ve])
      (ca + cb + cc + cd + ce + 5 * (Val.list [va, vb, vc, vd, ve]).wt + 10) := by
  have h1 := wt_list_mono (show [va, vb, vc, vd] <+: [va, vb, vc, vd, ve] from ⟨[ve], rfl⟩)
  have := Det.snoc (Det.mk4 ha hb hc hd) he
  exact this.mono (by simp only [List.cons_append, List.nil_append] at *; omega)

/-- Entry `k` of the state. -/
def vsBSt (k : ℕ) : Expr := .get (arg 0) (.nat k)

/-- The prime, from `Γ`. -/
def vsBP : Expr := .get (.get (vsBSt 0) (.nat 2)) (.nat 0)

/-- The dimension `d`, from `Γ`. -/
def vsBD : Expr := .length (.get (.get (vsBSt 0) (.nat 2)) (.nat 1))

/-- The main function, on `[state, B]`. -/
def vsBOrbF (b : ℕ) : Expr :=
  .letE (.call (b + 1) (mk4 vsBP vsBD (vsBSt 2) (vsBSt 3)))
  (.letE (.call (b + 175) (vsBmk5 (mk3 (vsBSt 0) (.var 1) (vsBSt 4)) (.get (vsBSt 1) (.nat 1))
      (.call (b + 210) (mk2 (.arith .add (.length (.get (.var 1) (.nat 2))) (.nat 1)) (.nat 0)))
      (arg 1) (.get (vsBSt 1) (.nat 0))))
  (.letE (.call (b + 150) (mk2 (mk1 (.nat 0)) (.call (b + 137) (mk2 (.var 1)
      (.call (b + 116) (vsBmk5 vsBP (.nat 1) (.arith .sub vsBP (.nat 1)) (vsBSt 5) (vsBSt 4)))))))
  (.letE (.call (b + 161) (mk2 (.var 3) (.get (.var 2) (.nat 0))))
  (.ite (.arith .lt (.var 4) (.length (.get (.var 2) (.nat 0))))
    (mk2 (.nat 0) (mk3 (.nat 1) (.get (.get (.get (.var 2) (.nat 0)) (.var 4)) (.nat 1))
      (.get (.var 2) (.nat 1))))
    (mk2 (.nat 0) (mk1 (.nat 0)))))))

/-- The orbit program at base `b` (213 functions). -/
def vsBOrbFuns (b phi jp jm : ℕ) : List Expr :=
  [vsBOrbF b] ++ (vsWFrameFuns (b + 1) ++ (vsBActFuns (b + 96) phi ++
    (vsQSotFuns (b + 153) (b + 96) jp jm ++ replicateFuns (b + 210))))

theorem vsBOrbFuns_length (b phi jp jm : ℕ) : (vsBOrbFuns b phi jp jm).length = 213 := by
  simp [vsBOrbFuns, vsWFrameFuns_length, vsBActFuns_length, vsQSotFuns, length_orbTFuns,
    replicateFuns, loopFuns, mkGroupFuns, mapFuns, appendFuns, gatherFuns, reduceFuns, rangeFuns,
    foldlFuns]

/-- The cost of the orbit program. -/
noncomputable def vsBOrbCost (hps : PointwiseStab) (hm : Membership) (n S Cφ N : ℕ) : ℕ :=
  vsQSotCost hps hm n S (Cφ + 10 ^ 9 * (N + 1) ^ 6) + 10 ^ 10 * S ^ 4

theorem vsQVec_injective {p d : ℕ} [NeZero p] :
    Function.Injective (vsQVec : (Fin d → ZMod p) → List ℕ) := fun a b h => by
  rw [← vsWV_vsQVec a, ← vsWV_vsQVec b, h]

theorem vsBOrb_arith_found {cfr csv ctk cidx cb ct S So p g j pr ep k x3 x2 len c : ℕ}
    (hfr : cfr ≤ 10 ^ 9 * S ^ 3) (htk : ctk ≤ 10 ^ 9 * S ^ 3) (hidx : cidx ≤ 10 ^ 6 * S ^ 4)
    (hsv : csv ≤ 10 ^ 9 * S ^ 4 + So)
    (hct : ct ≤ 0 + 3 + (1 + 3 + (p + 1 + (0 + 3) + g + 1 + (j + 1) + pr + 1 + (1 + 3) + ep + 1) +
      (p + 1 + (1 + 3) + k + 1) + 3 * x3 + 8) + 2 * x2 + 7)
    (hcb : cb ≤ (j + 1 + (p + 1 + (0 + 3) + g + 1 + len + 3) + c) + 3 + ct + x2 + 1)
    (hc : c ≤ 1) (hp : p ≤ 50000 * S ^ 3) (hg : g ≤ p) (hk : k ≤ p) (hj : j ≤ len + 2)
    (hlen : len ≤ S) (hpr : pr ≤ 16 * S ^ 2) (hep : ep ≤ 16 * S) (hx3 : x3 ≤ 10 ^ 6 * S ^ 3)
    (hx2 : x2 ≤ 10 ^ 6 * S ^ 3) (h1 : 1 ≤ S) (h12 : S ≤ S ^ 2) (h23 : S ^ 2 ≤ S ^ 3) (h34 : S ^ 3 ≤ S ^ 4) :
    cfr + (csv + (ctk + (cidx + cb + x2 + 1) + x2 + 1) + x2 + 1) + x2 + 1 ≤ So + 10 ^ 10 * S ^ 4 := by
  omega

theorem vsBOrb_arith_none {cfr csv ctk cidx cb ce S So p g j len x0 c : ℕ}
    (hfr : cfr ≤ 10 ^ 9 * S ^ 3) (htk : ctk ≤ 10 ^ 9 * S ^ 3) (hidx : cidx ≤ 10 ^ 6 * S ^ 4)
    (hsv : csv ≤ 10 ^ 9 * S ^ 4 + So) (hce : ce ≤ 200)
    (hcb : cb ≤ (j + 1 + (p + 1 + (0 + 3) + g + 1 + len + 3) + c) + 3 + ce + x0 + 1)
    (hc : c ≤ 1) (hx0 : x0 ≤ 20) (hp : p ≤ 50000 * S ^ 3) (hg : g ≤ p) (hj : j ≤ len + 2)
    (hlen : len ≤ S) (h1 : 1 ≤ S) (h12 : S ≤ S ^ 2) (h23 : S ^ 2 ≤ S ^ 3) (h34 : S ^ 3 ≤ S ^ 4) :
    cfr + (csv + (ctk + (cidx + cb + x0 + 1) + x0 + 1) + x0 + 1) + x0 + 1 ≤ So + 10 ^ 10 * S ^ 4 := by
  omega

/-- The size hypotheses of the orbit program. -/
structure VsBOrbSz (I : VecStabInst) (N S B : ℕ) : Prop where
  sz : VsQSz I.p I.d (vsQExp I) N
  n : I.n ≤ N
  g : (vsQGam I).wt ≤ N
  d : 4 * I.d + 4 ≤ N
  sn : I.n ^ 2 + 2 ≤ S
  sN : 10 ^ 4 * (N + 1) ^ 4 ≤ S
  b : B + 1 ≤ S

set_option maxHeartbeats 8000000 in
/-- **A leaf from a small orbit.** -/
theorem vsBOrb_spec (hps : PointwiseStab) (hm : Membership) {P : Program} {b phi jp jm Cφ N S B : ℕ}
    (h : P.HasAt b (vsBOrbFuns b phi jp jm)) (hjp : P.prims[jp]? = some (pointwiseStabPrim hps))
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hz : VsBOrbSz I N S B) {s : VsQSt I} (hs : VsQStOK s)
    (hB : (vsQOrb (vsBAlpha s) (1 :: s.hs) 0).ncard ≤ B) :
    FunAll P b (.list [vsQStV I s, .nat B]) (fun w c => ∃ a, w = vsQLeafV a ∧
      VsQAnsOK hs.prob a ∧ c ≤ vsBOrbCost hps hm I.n S Cφ N) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hcy : vsWV I.p I.d s.y - vsWV I.p I.d s.x ∈ vsQSp I s.ws := hs.prob.cy
  have hp := I.prime.pos
  have hp1 := I.prime.one_lt
  have hpN := hz.sz.pN
  have hdN := hz.sz.dN
  obtain ⟨h0', h1⟩ := h.split (k := 1) rfl
  have h0 : P.funs[b]? = some (vsBOrbF b) := h0'.single
  obtain ⟨hfr, h2⟩ := h1.split (vsWFrameFuns_length _)
  obtain ⟨hact, h3⟩ := h2.split (vsBActFuns_length _ _)
  obtain ⟨hsot, hrep⟩ := h3.split (k := 57) (by
    simp [vsQSotFuns, length_orbTFuns, loopFuns, mkGroupFuns, mapFuns, appendFuns, gatherFuns,
      reduceFuns, rangeFuns, foldlFuns])
  -- values
  set Γ := vsQGam I with hΓdef
  set stV := vsQStV I s
  set inp := Val.list [stV, .nat B]
  set E := vsQE I.p I.d (vsQExp I) 1 with hE
  have hst : ∀ rest k v, [Γ, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y][k]? =
      some v → Det P (inp :: rest) (vsBSt k) v _ := fun rest k v hv =>
    Det.get' (Det.arg' (P := P) (rest := rest) (vs := [stV, .nat B]) (j := 0) rfl) (Det.nat k) hv
  have dE : ∀ rest, Det P (inp :: rest) (.get (vsBSt 0) (.nat 2)) E _ := fun rest =>
    Det.get' (hst rest 0 Γ rfl) (Det.nat 2)
      (show [encGroup I.gs, vsQTable I, E][2]? = some E from rfl)
  have dP : ∀ rest, Det P (inp :: rest) vsBP (.nat I.p) _ := fun rest =>
    Det.get' (dE rest) (Det.nat 0)
      (show [Val.nat I.p, natList (List.replicate I.d 0), .nat (vsQExp I),
        .list ((vsQL (Matrix.transpose (1 : Matrix (Fin I.d) (Fin I.d) (ZMod I.p)))).map natList)][0]? =
        some (.nat I.p) from rfl)
  have dD0 := Det.length (Det.get' (dE []) (Det.nat 1)
      (show [Val.nat I.p, natList (List.replicate I.d 0), .nat (vsQExp I),
        .list ((vsQL (Matrix.transpose (1 : Matrix (Fin I.d) (Fin I.d) (ZMod I.p)))).map natList)][1]? =
        some (.list ((List.replicate I.d 0).map Val.nat)) from rfl))
  have eD : ((List.replicate I.d 0).map Val.nat).length = I.d := by simp
  rw [eD] at dD0
  have dfr := Det.call (Det.mk4 (dP []) dD0 (hst [] 2 _ rfl) (hst [] 3 _ rfl))
    (vsWFrame_spec hfr hp1 hpN hdN hs.fit' hs.fit (by have := hs.wl; have := hs.wl'; have := hz.d; omega))
  refine FunAll.intro h0 (EvalAll.letE dfr fun frv cfr hfrv => ?_)
  obtain ⟨rfl, hcfr⟩ := hfrv
  set cs := vsQCs s
  set D := vsQD s
  set fr := vsWFrVal I.p I.d s.ws' cs
  have hcf : VsWFit I.p I.d cs := vsWComp_fit hp hs.fit' hs.fit
  have hcl : cs.length ≤ s.ws'.length + s.ws.length := vsWComp_length_le hp hpN hdN hs.fit' hs.fit
  have hOK : VsWFrOK I.p N I.d s.ws' cs :=
    ⟨hp1, hpN, hdN, hs.fit', hcf, by have := hs.wl; have := hs.wl'; have := hz.d; omega⟩
  set ac := Val.list [Γ, fr, natList s.x]
  set A := Cφ + 10 ^ 9 * (N + 1) ^ 6
  have hα := vsBAlpha_act hs
  have hK : genGroup (1 :: s.hs) ≤ gens s.hs := le_of_eq (vsB_genGroup_cons s.hs)
  have hsl := hs.hsl
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have wfr := wt_vsWFrVal_le hOK
  have hxf := hs.fx s.x (List.mem_singleton_self _)
  have wx := wt_natList_le_sq (B := N) (xs := s.x) (fun y hy => (hxf.1 y hy).le.trans hpN)
    (by rw [hxf.2]; exact hdN)
  have hDl : D ≤ 2 * I.d := by have := hs.wl; have := hs.wl'; show cs.length ≤ _; omega
  have wkey : ∀ y : Fin D → ZMod I.p, (natList (0 :: vsQVec y)).wt ≤ S := by
    intro y
    have := wt_natList_le_sq (B := N) (xs := 0 :: vsQVec y) (fun z hz => by
      rcases List.mem_cons.mp hz with rfl | hz
      · omega
      · exact (vsQVec_lt y z hz).le.trans hpN) (by simp [vsQVec_length]; have := hz.d; omega)
    have := hz.sN
    omega
  have H : VsQSotHyp P (b + 96) (gens s.hs) (vsBAlpha s) (1 :: s.hs) vsQVec 0 ac S A B :=
    { hk := vsQVec_injective
      hK := hK
      hn := by have := hz.sn; have : I.n ≤ I.n ^ 2 := Nat.le_self_pow (by norm_num) _; omega
      hm := by have := hz.sn; simp; omega
      hac := by
        have := wt_list3_le Γ fr (natList s.x)
        have := hz.g; have := hz.sN
        have : fr.wt = (vsWFrVal I.p I.d s.ws' cs).wt := rfl
        have : Γ.wt = (vsQGam I).wt := rfl
        show (Val.list [Γ, fr, natList s.x]).wt ≤ S
        omega
      hkey := fun y _ => wkey y
      hfa := by
        intro g hg y _
        have hgs : g ∈ gens s.hs := hK (Subgroup.subset_closure hg)
        have := vsBAct_spec (hact : P.HasAt (b + 96) _) hphi hz.sz hz.n hz.g hOK hs.fx
          (hs.prob.le hgs) (vsQVec_lt y) (by rw [vsQVec_length])
        rw [vsBAct_vsQVec hs] at this
        exact this
      hBS := hz.b
      hB := hB }
  -- the arguments of the transporter, in the environment `[inp, fr]`
  have dac := Det.mk3 (hst [fr] 0 Γ rfl) (Det.var' (P := P) (env := [inp, fr]) (i := 1) rfl)
    (hst [fr] 4 _ rfl)
  have dG : Det P [inp, fr] (vsBSt 1) (.list [.nat I.n, .list ((1 :: s.hs).map encPerm)]) _ :=
    hst [fr] 1 _ rfl
  have dgs := Det.get' dG (Det.nat 1)
    (show [Val.nat I.n, .list ((1 :: s.hs).map encPerm)][1]? =
      some (.list ((1 :: s.hs).map encPerm)) from rfl)
  have dn := Det.get' dG (Det.nat 0)
    (show [Val.nat I.n, .list ((1 :: s.hs).map encPerm)][0]? = some (.nat I.n) from rfl)
  set F0 := Val.list [.nat I.p, .nat I.d, natList (vsWZ I.d), natList (vsWZ cs.length)]
  have dlen := Det.length (Det.get' (Det.var' (P := P) (env := [inp, fr]) (i := 1) rfl) (Det.nat 2)
    (show [F0, vsWVs s.ws', vsWVs cs, .list ((vsWFrRows I.p s.ws' cs).map VsRow.val)][2]? =
      some (.list (cs.map natList)) from rfl))
  have eDl : (cs.map natList).length = D := by simp [D, cs]
  rw [eDl] at dlen
  have dk := Det.arith' (op := .add) dlen (Det.nat 1) (z := D + 1) rfl
  have hK' : loopModK = 1000 := rfl
  have krep : loopModK * (D + 1 + 1) * ((Val.list [.nat (D + 1), .nat 0]).wt + (D + 1) +
      (Val.list (List.replicate (D + 1) (Val.nat 0))).wt + 1) ≤ 10 ^ 5 * (N + 1) ^ 3 := by
    have e1 : Val.list (List.replicate (D + 1) (Val.nat 0)) = natList (0 :: vsQVec (0 : Fin D → ZMod I.p)) := by
      simp [natList, vsQVec, List.replicate_succ, List.map_replicate]
    have w1 := wkey 0
    have w2 := wt_list2_le (.nat (D + 1)) (.nat 0)
    have w3 := wt_nat_le (D + 1)
    have w4 := wt_nat_le 0
    have w5 := wt_natList_le_sq (B := N) (xs := 0 :: vsQVec (0 : Fin D → ZMod I.p)) (fun z hz => by
      rcases List.mem_cons.mp hz with rfl | hz
      · omega
      · exact (vsQVec_lt _ z hz).le.trans hpN) (by simp [vsQVec_length]; have := hz.d; omega)
    rw [e1, hK']
    have : D + 1 + 1 ≤ N + 1 := by have := hz.d; omega
    calc 1000 * (D + 1 + 1) * _ ≤ 1000 * (N + 1) * (40 * (N + 1) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ this) (by omega)
      _ = 40000 * (N + 1) ^ 3 := by ring
      _ ≤ _ := by omega
  have e1r : Val.list (List.replicate (D + 1) (Val.nat 0)) =
      natList (0 :: vsQVec (0 : Fin D → ZMod I.p)) := by
    simp [natList, vsQVec, List.replicate_succ, List.map_replicate]
  have drep := Det.call (Det.mk2 dk (Det.nat 0)) ((replicate_spec (hrep : P.HasAt (b + 210) _) (D + 1)
      (.nat 0)).mono fun w c hw => ⟨hw.1, hw.2.trans (hw.1 ▸ krep)⟩)
  rw [e1r] at drep
  have dB := Det.arg' (P := P) (rest := [fr]) (vs := [stV, .nat B]) (j := 1) rfl
  have dargs := Det.vsBmk5 dac dgs drep dB dn
  have hsot' := vsQSot_spec hps hm (hsot : P.HasAt (b + 153) _) hjp hjm hα H
  -- weights
  have hS1 : 1 ≤ S := by have := hz.sn; omega
  have hnS : (I.n + 1) ^ 2 ≤ 4 * S := by
    have := hz.sn
    have : (I.n + 1) ^ 2 = I.n ^ 2 + 2 * I.n + 1 := by ring
    have : I.n ≤ I.n ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hn6 : (I.n + 1) ^ 6 ≤ 64 * S ^ 3 := by
    have := Nat.pow_le_pow_left hnS 3
    have e1 : ((I.n + 1) ^ 2) ^ 3 = (I.n + 1) ^ 6 := by ring
    have e2 : (4 * S) ^ 3 = 64 * S ^ 3 := by ring
    omega
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
  have hS34 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hS23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hSS2 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have wG := wt_encGroup_le_sq hsl
  have hyf := hs.fy s.y (List.mem_singleton_self _)
  have wy := wt_natList_le_sq (B := N) (xs := s.y) (fun y hy => (hyf.1 y hy).le.trans hpN)
    (by rw [hyf.2]; exact hdN)
  have w1' := wt_vsWVs_le (VsWFit.bnd hs.fit' hpN hdN) (show s.ws'.length ≤ N + 1 by
    have := hs.wl'; omega)
  have w1 := wt_vsWVs_le (VsWFit.bnd hs.fit hpN hdN) (show s.ws.length ≤ N + 1 by
    have := hs.wl; omega)
  have wΓ : Γ.wt ≤ N := hz.g
  have hzn := hz.n
  have hzd := hz.d
  have hN4 := hz.sN
  have wst : stV.wt ≤ 10 ^ 5 * S ^ 3 := by
    have := wt_list_le [Γ, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    show (Val.list [Γ, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]).wt ≤ _
    omega
  have wB := wt_nat_le B
  have winp : inp.wt ≤ 3 * 10 ^ 5 * S ^ 3 := by
    have := wt_list2_le stV (.nat B)
    have := hz.b
    show (Val.list [stV, .nat B]).wt ≤ _
    omega
  have wfr' : fr.wt ≤ S := by
    have : fr.wt = (vsWFrVal I.p I.d s.ws' cs).wt := rfl
    omega
  have wac : ac.wt ≤ S := H.hac
  have wgs := (wt_vsQSotIn_le hα H).2
  have wIn := (wt_vsQSotIn_le hα H).1
  have hsot'' : FunAll P (b + 175) (vsQSotIn ac (1 :: s.hs) vsQVec 0 B) _ := hsot'
  refine EvalAll.letE (Ra := fun w c => ∃ (L : List ((Fin D → ZMod I.p) × Perm (Fin I.n)))
      (ks : List (Perm (Fin I.n))), w = .list [vsQPairs vsQVec L, encGroup ks] ∧
      VsQOrbL (vsBAlpha s) (1 :: s.hs) 0 L ∧ gens ks = vsQStabG hα hK 0 ∧ ks.length ≤ I.n ^ 2 ∧
      c ≤ 10 ^ 9 * S ^ 4 + vsQSotCost hps hm I.n S A)
    (EvalAll.call_funAll dargs fun v ca hv => ?_) fun sv csv hsv => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine hsot''.mono fun w c hw => ?_
    obtain ⟨L, ks, rfl, hL, hks, hksl, hc⟩ := hw
    refine ⟨L, ks, rfl, hL, hks, hksl, ?_⟩
    have wP := (H.wt_pairs hL).2.2
    have wK := wt_encGroup_le_sq hksl
    have wo := wt_list2_le (vsQPairs vsQVec L) (encGroup ks)
    have eIn : (Val.list [ac, .list ((1 :: s.hs).map encPerm), natList (0 :: vsQVec (0 : Fin D → ZMod I.p)),
      .nat B, .nat I.n]).wt = (vsQSotIn ac (1 :: s.hs) vsQVec 0 B).wt := rfl
    have wk0 := wkey 0
    have wn := wt_nat_le I.n
    have wD := wt_nat_le D
    have wD1 := wt_nat_le (D + 1)
    have wF0 : F0.wt < fr.wt := wt_le_wt_list (by simp [fr, vsWFrVal, F0])
    have wcs : (Val.list (cs.map natList)).wt < fr.wt :=
      wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have wcl := length_lt_wt_list (cs.map natList)
    have wΓ2 := wt_list2_le inp fr
    have wenv : (Val.list [Γ, fr, natList s.x]).wt = ac.wt := rfl
    have wG2 : (Val.list [Val.nat I.n, .list ((1 :: s.hs).map encPerm)]).wt = (encGroup s.hs).wt := rfl
    have estV : stV.wt = (Val.list [Γ, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]).wt := rfl
    have wstG : (encGroup s.hs).wt < (Val.list [Γ, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]).wt := wt_le_wt_list (by simp)
    have wstΓ : Γ.wt < (Val.list [Γ, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]).wt := wt_le_wt_list (by simp)
    have wstx : (natList s.x).wt < (Val.list [Γ, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y]).wt := wt_le_wt_list (by simp)
    have w4 := wt_list2_le (.nat (D + 1)) (.nat 0)
    have w0 := wt_nat_le 0
    have w1n := wt_nat_le 1
    have w2n := wt_nat_le 2
    have w4n := wt_nat_le 4
    have wdl : (cs.map natList).length ≤ 2 * I.d := by simp; omega
    have eg : (Val.list [stV, .nat B]).wt = inp.wt := rfl
    have eac2 : (Val.list [Val.list [Γ, fr, natList s.x], Val.list (List.map encPerm (1 :: s.hs)),
      natList (0 :: vsQVec (0 : Fin D → ZMod I.p)), Val.nat B, Val.nat I.n]).wt =
      (Val.list [ac, Val.list (List.map encPerm (1 :: s.hs)), natList (0 :: vsQVec (0 : Fin D → ZMod I.p)),
        Val.nat B, Val.nat I.n]).wt := rfl
    have efr2 : (Val.list [Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d), natList (vsWZ cs.length)],
      vsWVs s.ws', vsWVs cs, Val.list (List.map VsRow.val (vsWFrRows I.p s.ws' cs))]).wt = fr.wt := rfl
    omega
  obtain ⟨L, ks, rfl, hL, hks, hksl, hcsv⟩ := hsv
  -- the target key, in the environment `[inp, fr, sotV]`
  set sotV := Val.list [vsQPairs vsQVec L, encGroup ks]
  have hlin : P.HasAt (b + 116) (vsLinFuns (b + 116)) := (hact : P.HasAt (b + 96) _).block 20 rfl
  have hco : P.HasAt (b + 137) (vsWCoFuns (b + 137)) := (hact : P.HasAt (b + 96) _).block 41 rfl
  have hapd : P.HasAt (b + 150) (appendFuns (b + 150)) := (hact : P.HasAt (b + 96) _).block 54 rfl
  have dP2 := dP [fr, sotV]
  have dsub := Det.arith' (op := .sub) dP2 (Det.nat 1) (z := I.p - 1) rfl
  have dlin := Det.call (Det.vsBmk5 dP2 (Det.nat 1) dsub (hst [fr, sotV] 5 _ rfl) (hst [fr, sotV] 4 _ rfl))
    (vsLin_spec hlin (v := s.y) (u := s.x) (a := 1) (b := I.p - 1) hp
      (fun y hy => (hyf.1 y hy).le.trans hpN) (fun y hy => (hxf.1 y hy).le.trans hpN)
      (by omega) (by omega) (by omega) hpN (by omega) (by omega))
  have hLf := vsLin_fit (a := 1) (b' := I.p - 1) (u := s.x) hp hs.fy
  have dco := Det.call (Det.mk2 (Det.var' (P := P) (env := [inp, fr, sotV]) (i := 1) rfl) dlin)
    (vsWCo_spec hco hOK hLf)
  set t := vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)
  rw [vsB_target hs] at dco
  have wt0 := wkey t
  have hK0 : loopModK = 1000 := rfl
  have kap : loopModK * ((vsQVec t).map Val.nat).length.succ *
      ((Val.list [.list [.nat 0], .list ((vsQVec t).map Val.nat)]).wt + ((vsQVec t).map Val.nat).length +
        (Val.list ([Val.nat 0] ++ (vsQVec t).map Val.nat)).wt + 1) ≤ 10 ^ 5 * (N + 1) ^ 3 := by
    have w2 := wt_list2_le (.list [.nat 0]) (.list ((vsQVec t).map Val.nat))
    have w1 : (Val.list [.nat 0]).wt ≤ 10 := by decide
    have e1 : (Val.list ((vsQVec t).map Val.nat)).wt = (natList (vsQVec t)).wt := rfl
    have e2 : (Val.list ([Val.nat 0] ++ (vsQVec t).map Val.nat)).wt = (natList (0 :: vsQVec t)).wt := rfl
    have w3 := wt_natList_le_sq (B := N) (xs := vsQVec t) (fun z hz => (vsQVec_lt t z hz).le.trans hpN)
      (by rw [vsQVec_length]; omega)
    have w4 := wt_natList_le_sq (B := N + 1) (xs := 0 :: vsQVec t) (fun z hz => by
      rcases List.mem_cons.mp hz with rfl | hz
      · omega
      · exact (vsQVec_lt t z hz).le.trans (by omega)) (by simp [vsQVec_length]; omega)
    have q2' : (N + 1 + 1) ^ 2 ≤ 4 * (N + 1) ^ 2 := by
      have := Nat.pow_le_pow_left (show N + 1 + 1 ≤ 2 * (N + 1) by omega) 2
      have e : (2 * (N + 1)) ^ 2 = 4 * (N + 1) ^ 2 := by ring
      omega
    rw [hK0, List.length_map, vsQVec_length]
    have hk : (D).succ ≤ N + 1 := by omega
    calc 1000 * D.succ * _ ≤ 1000 * (N + 1) * (100 * (N + 1) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hk) (by omega)
      _ = 10 ^ 5 * (N + 1) ^ 3 := by ring
  have dtk := Det.call (Det.mk2 (Det.mk1 (Det.nat (P := P) (env := [inp, fr, sotV]) 0)) dco)
    ((append_spec hapd [.nat 0] ((vsQVec t).map Val.nat)).mono fun w c hw => ⟨hw.1, hw.2.trans (hw.1 ▸ kap)⟩)
  -- the search, in the environment `[inp, fr, sotV, tk]`
  set key : (Fin D → ZMod I.p) → List ℕ := fun y => 0 :: vsQVec y with hkey
  have hk' : Function.Injective key := fun a b' e => vsQVec_injective (List.cons.inj e).2
  obtain ⟨hO, -⟩ := (hsot : P.HasAt (b + 153) _).split (length_orbTFuns _ _)
  have hfd : P.HasAt (b + 153 + 8) (findFuns (b + 153 + 8) (b + 153 + 8 + 3)) := hO.block 8 (by rfl)
  have ht : P.funs[b + 153 + 8 + 3]? = some (orbTestF (b + 153 + 16)) :=
    (hO.block 11 (gs := [_]) (by rfl)).single
  have heq : P.HasAt (b + 153 + 16) (eqNatsFuns (b + 153 + 16)) := hO.block 16 (by rfl)
  have wpairs := (H.wt_pairs hL)
  have hF := find_spec hfd (c := natList (key t)) (xs := L.map (GI.Lang.encPair key))
    (q := pairTest I.n key t) (B := fun _ => 100000 * S ^ 2) (by
      intro v hv
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
      have := orbTest_spec ht heq key hS1 t q (wkey t) (wkey q.1) (wpairs.2.1 q hq)
      rw [pairTest_encPair hk']
      have e : decide (key t = key q.1) = decide (q.1 = t) :=
        Bool.decide_congr ⟨fun h => (hk' h).symm, fun h => h ▸ rfl⟩
      rw [e] at this
      exact this)
  set i := L.findIdx (fun q => decide (q.1 = t))
  have hF' : FunDet P (b + 153 + 8) (.list [natList (key t), .list (L.map (GI.Lang.encPair key))]) (.nat i)
      (200000 * S ^ 4) := by
    refine hF.mono fun w cost hw => ⟨by rw [hw.1, findIdx_map_pairTest hk'], ?_⟩
    have hc := hw.2
    rw [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
    have w1 := wt_list2_le (natList (key t)) (.list (L.map (GI.Lang.encPair key)))
    have w2 : (natList (key t)).wt ≤ S := wkey t
    have w3 := wpairs.2.2
    have e0 : (vsQPairs vsQVec L).wt = (Val.list (L.map (GI.Lang.encPair key))).wt := rfl
    have hLS := wpairs.1
    have h1 : L.length * (100000 * S ^ 2) ≤ S * (100000 * S ^ 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : loopModK * (L.length + 1) * ((Val.list [natList (key t),
        .list (L.map (GI.Lang.encPair key))]).wt + 2 * L.length + 3) ≤ loopModK * S * (95 * S ^ 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e2 : S * (100000 * S ^ 2) = 100000 * S ^ 3 := by ring
    have e3 : loopModK * S * (95 * S ^ 3) = 95000 * S ^ 4 := by simp only [loopModK]; ring
    omega
  have dpairs := Det.get' (Det.var' (P := P) (env := [inp, fr, sotV, natList (key t)]) (i := 2) rfl)
    (Det.nat 0) (show [vsQPairs vsQVec L, encGroup ks][0]? = some (.list (L.map (GI.Lang.encPair key))) from rfl)
  have didx := Det.call (Det.mk2 (Det.var' (P := P) (env := [inp, fr, sotV, natList (key t)]) (i := 3) rfl)
    dpairs) hF'
  -- the test and the two branches, in the environment `[inp, fr, sotV, tk, i]`
  set env5 := [inp, fr, sotV, natList (key t), Val.nat i]
  have dpairs5 := Det.get' (Det.var' (P := P) (env := env5) (i := 2) rfl)
    (Det.nat 0) (show [vsQPairs vsQVec L, encGroup ks][0]? = some (.list (L.map (GI.Lang.encPair key))) from rfl)
  have dlt := Det.arith' (op := .lt) (Det.var' (P := P) (env := env5) (i := 4) rfl) (Det.length dpairs5)
    (z := if i < (L.map (GI.Lang.encPair key)).length then 1 else 0) rfl
  have hiL : i ≤ L.length := List.findIdx_le_length
  have wlt : (if i < (L.map (GI.Lang.encPair key)).length then 1 else 0) ≤ 1 := by split <;> omega
  have hP := hs.prob
  refine EvalAll.letE dtk fun tkv ctk htk => ?_
  obtain ⟨rfl, hctk⟩ := htk
  refine EvalAll.letE didx fun iv cidx hidx => ?_
  obtain ⟨rfl, hcidx⟩ := hidx
  -- weight facts for the final cost
  have wE : E.wt < Γ.wt := wt_le_wt_list (show E ∈ [encGroup I.gs, vsQTable I, E] by simp)
  have wZ : (Val.list ((List.replicate I.d 0).map Val.nat)).wt < E.wt :=
    wt_le_wt_list (show Val.list ((List.replicate I.d 0).map Val.nat) ∈ [Val.nat I.p,
      natList (List.replicate I.d 0), .nat (vsQExp I),
      .list ((vsQL (Matrix.transpose (1 : Matrix (Fin I.d) (Fin I.d) (ZMod I.p)))).map natList)] by
        simp [natList])
  have wPn : (Val.nat I.p).wt ≤ N + 2 := by have := wt_nat_le I.p; omega
  have wDn : (Val.nat I.d).wt ≤ N + 2 := by have := wt_nat_le I.d; omega
  have wfrC : (vsWFrVal I.p I.d s.ws' (vsWComp I.p s.ws' s.ws)).wt ≤ 500 * (N + 1) ^ 3 := wfr
  have w4fr := wt_list4_le (.nat I.p) (.nat I.d) (vsWVs s.ws') (vsWVs s.ws)
  have wsot : sotV.wt ≤ 50000 * S ^ 3 := by
    have := wt_list2_le (vsQPairs vsQVec L) (encGroup ks)
    have := wpairs.2.2
    have := wt_encGroup_le_sq hksl
    show (Val.list [vsQPairs vsQVec L, encGroup ks]).wt ≤ _
    omega
  have wtk : (natList (key t)).wt ≤ S := wkey t
  have wtk' : (natList (0 :: vsQVec t)).wt ≤ S := wkey t
  have wLyx := wt_vsLinArg_le (p := I.p) (a := 1) (b := I.p - 1) (v := s.y) (u := s.x)
    (fun y hy => (hyf.1 y hy).le.trans hpN) (fun y hy => (hxf.1 y hy).le.trans hpN)
    (by omega) (by omega) hpN (by omega) (by omega)
  have eLyx : (vsLinArg I.p 1 (I.p - 1) s.y s.x).wt = (Val.list [Val.nat I.p, Val.nat 1,
    Val.nat (I.p - 1), natList s.y, natList s.x]).wt := rfl
  have hLf' := hLf _ (List.mem_singleton_self _)
  have wLin := wt_natList_le_sq (B := N) (xs := vsLin I.p 1 (I.p - 1) s.y s.x)
    (fun y hy => (hLf'.1 y hy).le.trans hpN) (by rw [hLf'.2]; exact hdN)
  have wco2 := wt_list2_le fr (natList (vsLin I.p 1 (I.p - 1) s.y s.x))
  have wvq := wt_natList_le_sq (B := N) (xs := vsQVec t) (fun z hz => (vsQVec_lt t z hz).le.trans hpN)
    (by rw [vsQVec_length]; omega)
  have wtk2 := wt_list2_le (.list [.nat 0]) (natList (vsQVec t))
  have w10 : (Val.list [.nat 0]).wt ≤ 10 := by decide
  have wpk := wt_list2_le (natList (key t)) (.list (L.map (GI.Lang.encPair key)))
  have ePk : (vsQPairs vsQVec L).wt = (Val.list (L.map (GI.Lang.encPair key))).wt := rfl
  have wPs : (vsQPairs vsQVec L).wt < sotV.wt :=
    wt_le_wt_list (show vsQPairs vsQVec L ∈ [vsQPairs vsQVec L, encGroup ks] by simp)
  have wKs : (encGroup ks).wt < sotV.wt :=
    wt_le_wt_list (show encGroup ks ∈ [vsQPairs vsQVec L, encGroup ks] by simp)
  have wi := wt_nat_le i
  have wlen := wt_nat_le (L.map (GI.Lang.encPair key)).length
  have hLlen : (L.map (GI.Lang.encPair key)).length = L.length := List.length_map _
  have hLS := wpairs.1
  have wenv5 := wt_list_le env5
  have wenv5' : (Val.list env5).wt ≤ 10 ^ 6 * S ^ 3 := by
    have := wt_list_le [inp, fr, sotV, natList (key t), Val.nat i]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    show (Val.list [inp, fr, sotV, natList (key t), Val.nat i]).wt ≤ _
    omega
  have q5 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hS5 : (N + 1) ^ 5 ≤ S ^ 2 := by
    have : (N + 1) ^ 5 ≤ ((N + 1) ^ 4) ^ 2 := by
      rw [← pow_mul]; exact Nat.pow_le_pow_right (by omega) (by norm_num)
    have := Nat.pow_le_pow_left (show (N + 1) ^ 4 ≤ S by omega) 2
    omega
  have w0n := wt_nat_le 0
  have w1n := wt_nat_le 1
  have w2n := wt_nat_le 2
  have w3n := wt_nat_le 3
  have w4n := wt_nat_le 4
  have w5n := wt_nat_le 5
  have wp1 := wt_nat_le (I.p - 1)
  have eg' : (Val.list [stV, .nat B]).wt = inp.wt := rfl
  have eA : vsQSotCost hps hm I.n S A = vsQSotCost hps hm I.n S (Cφ + 10 ^ 9 * (N + 1) ^ 6) := rfl
  have efr1 : (vsWFrVal I.p I.d s.ws' (vsWComp I.p s.ws' s.ws)).wt = fr.wt := rfl
  have efr3 : (vsWFrVal I.p I.d s.ws' cs).wt = fr.wt := rfl
  have et1 : (natList (vsQVec (vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)))).wt =
    (natList (vsQVec t)).wt := rfl
  have et2 : (Val.list [Val.list [Val.nat 0], natList (vsQVec (vsBCo s (vsWV I.p I.d s.y -
    vsWV I.p I.d s.x)))]).wt = (Val.list [Val.list [Val.nat 0], natList (vsQVec t)]).wt := rfl
  have et3 : (Val.list ([Val.nat 0] ++ List.map Val.nat (vsQVec t))).wt =
    (natList (0 :: vsQVec t)).wt := rfl
  have et4 : (natList (key t)).wt = (natList (0 :: vsQVec t)).wt := rfl
  have esot : (Val.list [vsQPairs vsQVec L, encGroup ks]).wt = sotV.wt := rfl
  unfold vsBOrbCost
  have wNS : N + 1 ≤ S := by omega
  have hBfr : cfr ≤ 10 ^ 9 * S ^ 3 := by
    clear * - hcfr winp eg' wΓ wE wZ wPn wDn w1 w1' w4fr hS5 hS23 wfrC hdN q1 q2 q3 q5 hN4 hS1 hS3 wNS
    omega
  have hBtk : ctk ≤ 10 ^ 9 * S ^ 3 := by
    clear * - hctk winp eg' wΓ wE wPn wp1 wfr' wy wx wLyx eLyx wLin wco2 wvq et1 et2 wtk2 w10 et3 wtk'
      q1 q2 q3 hN4 hS1 hS3 hS23 hpN wNS w0n w1n w2n w3n w4n w5n
    omega
  have hBidx : cidx ≤ 10 ^ 6 * S ^ 4 := by
    clear * - hcidx wtk esot wsot ePk wpk wi hiL hLS hS1 hS3 hS23 hS34 wPs
    omega
  have hXr : ∀ r ∈ L, (Val.list [.nat 0, .list [.nat 1, encPerm r.2, encGroup ks]]).wt ≤ 10 ^ 6 * S ^ 3 ∧
      (Val.list [.nat 1, encPerm r.2, encGroup ks]).wt ≤ 10 ^ 6 * S ^ 3 ∧ (encPerm r.2).wt ≤ 16 * S := by
    intro r _
    have wh := wt_encPerm_le r.2
    have w3k := wt_list3_le (.nat 1) (encPerm r.2) (encGroup ks)
    have w2k := wt_list2_le (.nat 0) (.list [.nat 1, encPerm r.2, encGroup ks])
    clear * - wh w3k w2k hnS wsot esot wKs w0n w1n hS1 hS3 hS23 hSS2
    omega
  have hpS : (Val.list [vsQPairs vsQVec L, encGroup ks]).wt ≤ 50000 * S ^ 3 := by
    clear * - wsot esot; omega
  have hgS : (Val.list (List.map (GI.Lang.encPair key) L)).wt ≤ (Val.list [vsQPairs vsQVec L, encGroup ks]).wt := by
    clear * - wPs esot ePk; omega
  have hkS : (encGroup ks).wt ≤ (Val.list [vsQPairs vsQVec L, encGroup ks]).wt := by
    clear * - wKs esot; omega
  have hjS : (Val.nat i).wt ≤ (L.map (GI.Lang.encPair key)).length + 2 := by
    clear * - wi hiL hLlen; omega
  have hlS : (L.map (GI.Lang.encPair key)).length ≤ S := by clear * - hLlen hLS; omega
  by_cases hfound : i < L.length
  · -- found
    have hpi : (L[i]).1 = t := by
      exact of_decide_eq_true (List.findIdx_getElem (xs := L) (p := fun q => decide (q.1 = t)) (w := hfound))
    have hv : (L.map (GI.Lang.encPair key))[i]? = some (GI.Lang.encPair key L[i]) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hfound]; rfl
    have dh := Det.get' (Det.get' dpairs5 (Det.var' (P := P) (env := env5) (i := 4) rfl) hv) (Det.nat 1)
      (show [natList (key L[i].1), encPerm L[i].2][1]? = some (encPerm L[i].2) from rfl)
    have dks := Det.get' (Det.var' (P := P) (env := env5) (i := 2) rfl) (Det.nat 1)
      (show [vsQPairs vsQVec L, encGroup ks][1]? = some (encGroup ks) from rfl)
    have dthen := Det.mk2 (Det.nat (P := P) (env := env5) 0) (Det.mk3 (Det.nat 1) dh dks)
    have hx1 : (if i < (L.map (GI.Lang.encPair key)).length then 1 else 0) ≠ 0 := by
      rw [List.length_map, if_pos hfound]; exact one_ne_zero
    refine (GI.Impl.EvalAll.vsQ_ite_pos' dlt hx1 dthen).mono ?_
    rintro w cb ⟨ct, ⟨rfl, hct⟩, hcb⟩
    refine ⟨some (L[i].2, ks), rfl, ?_, ?_⟩
    · have hpr := hL.pr L[i] (List.getElem_mem hfound)
      have hg : L[i].2 ∈ gens s.hs := by rw [← vsB_genGroup_cons]; exact hpr.1
      refine ⟨⟨hg, ?_⟩, ?_, hksl⟩
      · rw [← vsBAlpha_zero_eq hs hg _ hcy]
        rw [hpr.2, hpi]
      · rw [hks]; exact vsB_stabG_eq hs
    · have wh := wt_encPerm_le L[i].2
      have wpr : (Val.list [natList (key L[i].1), encPerm L[i].2]).wt ≤ 16 * S ^ 2 :=
        wpairs.2.1 L[i] (List.getElem_mem hfound)
      have w3k := wt_list3_le (.nat 1) (encPerm L[i].2) (encGroup ks)
      have w2k := wt_list2_le (.nat 0) (.list [.nat 1, encPerm L[i].2, encGroup ks])
      have hn2 : 4 * (I.n + 1) ^ 2 ≤ 16 * S := by omega
      clear * - hBfr hBtk hBidx hcsv eA hct hcb wh wpr w3k w2k hn2 wsot esot ePk wi hiL hLS hS1 hS3 hS23
        hS34 wPs wKs wlen hLlen w0n w1n wlt
      omega
  · -- not found
    have hx0 : (if i < (L.map (GI.Lang.encPair key)).length then 1 else 0) = 0 := by
      rw [List.length_map, if_neg hfound]
    rw [hx0] at dlt
    have delse := (Det.mk2 (Det.nat (P := P) (env := env5) 0)
      (Det.mk1 (Det.nat (P := P) (env := env5) 0))).mono (c' := 200) (by decide)
    refine (GI.Impl.EvalAll.vsQ_ite_zero' dlt delse).mono ?_
    rintro w cb ⟨ce, ⟨rfl, hce⟩, hcb⟩
    refine ⟨none, rfl, ?_, ?_⟩
    · show vsQSol I (gens s.hs) (vsQSp I s.ws') (vsWV I.p I.d s.x) (vsWV I.p I.d s.y) = ∅
      ext g
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨hg, hgs⟩
      apply hfound
      have hα0 : vsBAlpha s g 0 = t := (vsBAlpha_zero_eq hs hg _ hcy).mpr hgs
      have hmem : t ∈ vsQOrb (vsBAlpha s) (1 :: s.hs) 0 :=
        ⟨g, by rw [vsB_genGroup_cons]; exact hg, hα0⟩
      obtain ⟨r, hr, hr1⟩ := List.mem_map.mp ((hL.mem t).mpr hmem)
      exact List.findIdx_lt_length_of_exists ⟨r, hr, by simp [hr1]⟩
    · have hx0 : (Val.list [Val.nat 0, Val.list [Val.nat 0]]).wt ≤ 20 := by decide
      exact vsBOrb_arith_none hBfr hBtk hBidx hcsv hce hcb (Nat.zero_le 1) hx0 hpS hgS hjS hlS
        hS1 hSS2 hS23 hS34

end GI.Impl
