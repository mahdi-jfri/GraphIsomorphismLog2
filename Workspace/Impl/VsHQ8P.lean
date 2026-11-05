module

public import Workspace.Impl.VsHY0

@[expose] public section

/-!
# The `Q₈` branch

On `[vsPGIn s as Lb ccs tcs ys r, B]` the program `vsHQ8E` runs the small orbit transporter for
the conjugation of the tuple `(T(b))_{b ∈ B}` by `⟨ccs⟩`. It returns `[2, us, ⟨ks⟩]`: `us` are the
transversal elements of the orbit list and `⟨ks⟩` is the stabilizer (`vsHQ8_spec`).
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I}

theorem vsHKeyT_wt {N : ℕ} (hpN : I.p ≤ N) (hDD1 : vsQD s * vsQD s + 1 ≤ N)
    (zs : List (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p))) (hz : zs.length ≤ N) :
    (natList (0 :: vsHKeyT zs)).wt ≤ 20 * (N + 1) ^ 4 := by
  have hl : (zs.map vsHPc).flatten.length = zs.length * (vsQD s * vsQD s + 1) := by
    simp only [List.length_flatten, List.map_map, Function.comp_def, vsHPc_length]
    simp
  have hm : zs.length * (vsQD s * vsQD s + 1) ≤ N * N := Nat.mul_le_mul hz (by omega)
  have q2 : N * N + 1 ≤ (N + 1) ^ 2 := by nlinarith
  have hzz : ∀ y ∈ 0 :: vsHKeyT zs, y ≤ (N + 1) ^ 2 := by
    intro y hy
    simp only [vsHKeyT, List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · omega
    · nlinarith
    · obtain ⟨l, hl, hyl⟩ := List.mem_flatten.1 hy
      obtain ⟨M, -, rfl⟩ := List.mem_map.1 hl
      rcases List.mem_cons.1 hyl with rfl | hy'
      · omega
      · have := (vsHKey_lt M y hy').le.trans hpN; nlinarith
  have := wt_natList_le_sq (xs := 0 :: vsHKeyT zs) (B := (N + 1) ^ 2) hzz (by
    simp only [vsHKeyT, List.length_cons, hl]; nlinarith)
  have e : 5 * ((N + 1) ^ 2 + 1) ^ 2 ≤ 20 * (N + 1) ^ 4 := by nlinarith
  exact this.trans e

/-- Entry `k` of the hand-off value, in the `Q₈` program. -/
def vsHG (k : ℕ) : Expr := .get (arg 0) (.nat k)

/-- The frame block `[p, d, 0^d, 0^D]`. -/
def vsHF0 : Expr := .get (vsHG 4) (.nat 0)

/-- The map item: the permutation of a pair. -/
def vsHSndE : Expr := .get (arg 1) (.nat 1)

/-- The `Q₈` program, on `[vsPGIn …, B]`. -/
def vsHQ8E (y0 sot mp : ℕ) : Expr :=
  .letE (vsPMk5 (vsHG 0) (vsHG 4) (.get vsHF0 (.nat 0)) (.length (.get vsHF0 (.nat 3)))
      (.get vsHF0 (.nat 3)))
  (.letE (.call y0 (mk2 (mk2 (vsHG 0) (vsHG 4)) (arg 1)))
  (.letE (.call sot (vsPMk5 (.var 1) (.get (vsHG 6) (.nat 1)) (.var 2) (.nat 24) (.get (vsHG 6) (.nat 0))))
    (mk3 (.nat 2) (.call mp (mk2 (.nat 0) (.get (.var 3) (.nat 0)))) (.get (.var 3) (.nat 1)))))

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I}

/-- The indices of the `Q₈` program. -/
structure VsHQX where
  (t : VsHTX) (q8 y0 mpy ity sb jp jm mp2 it2 : ℕ)

/-- The layout of the `Q₈` program. -/
structure VsHQLay (P : Program) (x : VsHQX) (hps : PointwiseStab) (hm : Membership) : Prop where
  t : VsHTLay P x.t
  hq8 : P.funs[x.q8]? = some (vsHQ8E x.y0 (x.sb + 22) x.mp2)
  hy0 : P.funs[x.y0]? = some (vsHY0E x.mpy x.t.cat x.t.c.app)
  hmpy : P.HasAt x.mpy (mapFuns x.mpy x.ity)
  hity : P.funs[x.ity]? = some (vsHPcE x.t.c.loc x.t.c.fl x.t.c.app)
  hsot : P.HasAt x.sb (vsQSotFuns x.sb x.t.conjT x.jp x.jm)
  hjp : P.prims[x.jp]? = some (pointwiseStabPrim hps)
  hjm : P.prims[x.jm]? = some (membershipPrim hm)
  hmp2 : P.HasAt x.mp2 (mapFuns x.mp2 x.it2)
  hit2 : P.funs[x.it2]? = some vsHSndE

/-- The cost of the `Q₈` program. -/
noncomputable def vsHQ8Cost (hps : PointwiseStab) (hm : Membership) (Cφ N n Ss : ℕ) : ℕ :=
  vsHY0Cost Cφ N + vsQSotCost hps hm n Ss (vsHConjTCost Cφ N) + 10 ^ 6 * Ss ^ 4

set_option maxHeartbeats 8000000 in
/-- **The `Q₈` program.** -/
theorem vsHQ8_spec [Fact I.p.Prime] {P : Program} {x : VsHQX} {hps : PointwiseStab} {hm : Membership}
    (L : VsHQLay P x hps hm) {Cφ N W Ss : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.t.c.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {hs : VsQStOK s} {as : List (Perm (Fin I.n))} {Lb : List (List (List ℕ))}
    {ccs tcs ys : List (Perm (Fin I.n))} {r : ℕ}
    (H : VsPCtxOK I N W s.ws' (vsQCs s) (vsPRows I.p Lb) s.hs) (hDD1 : vsQD s * vsQD s + 1 ≤ N)
    (hac : (vsHAcV s).wt ≤ 1000 * (N + 1) ^ 3)
    {B : List (Perm (Fin I.n))} (hB : ∀ b ∈ B, b ∈ gens s.hs) (hBl : B.length ≤ N)
    (hcc : gens ccs ≤ gens s.hs) (hccl : ccs.length ≤ I.n ^ 2)
    {Y : Subgroup (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ}
    (hBY : ∀ b ∈ B, vsPRho hs b ∈ Y)
    (hidx : (Subgroup.centralizer (Y : Set (Module.End (ZMod I.p) (Fin (vsQD s) → ZMod I.p))ˣ)).relIndex
      (vsPBar hs (gens ccs)) ≤ 24)
    (hSn : I.n ^ 2 + 2 ≤ Ss) (hSac : 1000 * (N + 1) ^ 3 ≤ Ss) (hSk : 20 * (N + 1) ^ 4 ≤ Ss)
    (hSW : (vsPGIn s as Lb ccs tcs ys r).wt + 100 * (N + 1) ^ 3 ≤ Ss) :
    FunAll P x.q8 (.list [vsPGIn s as Lb ccs tcs ys r, .list (B.map encPerm)]) (fun w c =>
      ∃ (Lo : List (List (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) × Perm (Fin I.n)))
        (ks : List (Perm (Fin I.n))),
        w = .list [.nat 2, .list (Lo.map fun q => encPerm q.2), encGroup ks] ∧
        VsQOrbL (vsHAlT s) (1 :: ccs) (B.map (vsHT s)) Lo ∧
        (∀ h, h ∈ gens ks ↔ h ∈ gens ccs ∧ vsHAlT s h (B.map (vsHT s)) = B.map (vsHT s)) ∧
        ks.length ≤ I.n ^ 2 ∧ c ≤ vsHQ8Cost hps hm Cφ N I.n Ss) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hpN := H.sz.pN
  have hn := H.n
  set A := vsPGIn s as Lb ccs tcs ys r
  set fr := vsWFrVal I.p I.d s.ws' (vsQCs s)
  set F0 := Val.list [.nat I.p, .nat I.d, natList (vsWZ I.d), natList (vsWZ (vsQCs s).length)]
  set gl := [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, fr, encGroup as, encGroup ccs,
    Val.list (tcs.map encPerm), Val.list (ys.map encPerm), .nat r, vsFMatsVal Lb]
  have eA : A = .list gl := rfl
  set vs := [A, Val.list (B.map encPerm)]
  -- reading the hand-off value
  have rd : ∀ (rest : List Val) (k : ℕ) (v : Val), gl[k]? = some v →
      Det P (Val.list vs :: rest) (vsHG k) v (2 * (Val.list vs).wt + 0 + 5 + (k + 3) + v.wt + 1) := by
    intro rest k v h
    have a0 : Det P (Val.list vs :: rest) (arg 0) (.list gl) _ :=
      Det.arg' (P := P) (vs := vs) (rest := rest) (j := 0) rfl
    exact Det.get' a0 (Det.nat k) h
  have rF0 : ∀ rest : List Val, ∃ c, Det P (Val.list vs :: rest) vsHF0 F0 c ∧ c ≤ 4 * (Val.list vs).wt + 40 := by
    intro rest
    refine ⟨_, Det.get' (rd rest 4 fr rfl) (Det.nat 0) rfl, ?_⟩
    have h1 : fr.wt < (Val.list gl).wt := wt_le_wt_list (by simp [gl])
    have h2 : (Val.list gl).wt < (Val.list vs).wt := wt_le_wt_list (by simp [vs, eA])
    have h3 : F0.wt < fr.wt := wt_le_wt_list (by simp [fr, F0, vsWFrVal])
    have := wt_nat_le 0; have := wt_nat_le 4
    omega
  -- the action context
  obtain ⟨c0, d0, hc0⟩ := rF0 []
  have dp := Det.get' d0 (Det.nat 0) (show [Val.nat I.p, .nat I.d, natList (vsWZ I.d),
    natList (vsWZ (vsQCs s).length)][0]? = some (.nat I.p) from rfl)
  have dz := Det.get' d0 (Det.nat 3) (show [Val.nat I.p, .nat I.d, natList (vsWZ I.d),
    natList (vsWZ (vsQCs s).length)][3]? = some (natList (vsWZ (vsQCs s).length)) from rfl)
  have dz' : Det P [Val.list vs] (.get vsHF0 (.nat 3)) (.list ((vsWZ (vsQD s)).map Val.nat)) _ := dz
  have dD := Det.length dz'
  rw [List.length_map, show (vsWZ (vsQD s)).length = vsQD s by simp [vsWZ]] at dD
  have dac := Det.vsPMk5 (rd [] 0 (vsQGam I) rfl) (rd [] 4 fr rfl) dp dD dz
  have eac : Val.list [vsQGam I, fr, .nat I.p, .nat (vsQD s), natList (vsWZ (vsQCs s).length)] =
      vsHAcV s := rfl
  rw [eac] at dac
  -- the start point
  set E1 := [Val.list vs, vsHAcV s]
  have b1 := Det.arg' (P := P) (vs := vs) (rest := [vsHAcV s]) (j := 1) rfl
  have hBI : ∀ b ∈ B, b ∈ gens I.gs := fun b hb => hs.prob.le (hB b hb)
  have dY := Det.call (Det.mk2 (Det.mk2 (rd [vsHAcV s] 0 (vsQGam I) rfl) (rd [vsHAcV s] 4 fr rfl)) b1)
    (vsHY0_spec L.hy0 L.hmpy L.hity L.t.hcat L.t.c.hloc L.t.c.hwl L.t.c.hfl L.t.c.happ hphi H.sz H.gam
      H.n H.fr hDD1 hBI hBl)
  -- the transporter
  set y0 := B.map (vsHT s)
  have hK : genGroup (1 :: ccs) ≤ gens s.hs := (Subgroup.closure_le _).2 fun g hg => by
    rcases List.mem_cons.1 hg with rfl | hg
    · exact one_mem _
    · exact hcc (Subgroup.subset_closure hg)
  have hα := vsH_conjT_act hs
  have hlen : ∀ y ∈ vsQOrb (vsHAlT s) (1 :: ccs) y0, y.length ≤ N := by
    rintro _ ⟨g, -, rfl⟩
    simp [vsHAlT, y0, hBl]
  have hN1 : 1 ≤ N := by omega
  have q4 : 16 ≤ (N + 1) ^ 4 := by
    have : 2 ^ 4 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    simpa using this
  have hCb : ∀ g ∈ genGroup (1 :: ccs), vsPRho hs g ∈ vsPBar hs (gens ccs) := by
    intro g hg
    have hgc : g ∈ gens ccs := (Subgroup.closure_le _).2 (fun x hx => by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact one_mem _
      · exact Subgroup.subset_closure hx) hg
    exact vsPRho_mem_vsPBar hs hgc (hcc hgc)
  have HS : VsQSotHyp P x.t.conjT (gens s.hs) (vsHAlT s) (1 :: ccs) vsHKeyT y0 (vsHAcV s) Ss
      (vsHConjTCost Cφ N) 24 :=
    { hk := vsHKeyT_injective
      hK := hK
      hn := by nlinarith
      hm := by simp; omega
      hac := by omega
      hkey := fun y hy => (vsHKeyT_wt hpN hDD1 y (hlen y hy)).trans hSk
      hfa := fun g hg y hy => vsHConjT_spec L.t hphi H.sz H.gam H.n H.fr hDD1 hac
        (hs.prob.le (hK (Subgroup.subset_closure hg))) y (hlen y hy)
      hBS := by omega
      hB := (vsH_q8_orbit hs hB hK hCb hBY).trans hidx }
  have hsot := vsQSot_spec hps hm L.hsot L.hjp L.hjm hα HS
  set E2 := [Val.list vs, vsHAcV s, natList (0 :: vsHKeyT y0)]
  have rG : Det P E2 (vsHG 6) (encGroup ccs) _ := rd [vsHAcV s, natList (0 :: vsHKeyT y0)] 6 _ rfl
  have rG' : Det P E2 (vsHG 6) (.list [.nat I.n, .list ((1 :: ccs).map encPerm)]) _ := rG
  have dgs := Det.get' rG' (Det.nat 1) (show [Val.nat I.n, Val.list ((1 :: ccs).map encPerm)][1]? =
    some (.list ((1 :: ccs).map encPerm)) from rfl)
  have dn := Det.get' rG' (Det.nat 0) (show [Val.nat I.n, Val.list ((1 :: ccs).map encPerm)][0]? =
    some (.nat I.n) from rfl)
  have dIn := Det.vsPMk5 (Det.var' (P := P) (env := E2) (i := 1) rfl) dgs
    (Det.var' (P := P) (env := E2) (i := 2) rfl) (Det.nat (P := P) (env := E2) 24) dn
  have eIn : Val.list [vsHAcV s, .list ((1 :: ccs).map encPerm), natList (0 :: vsHKeyT y0), .nat 24,
      .nat I.n] = vsQSotIn (vsHAcV s) (1 :: ccs) vsHKeyT y0 24 := rfl
  rw [eIn] at dIn
  obtain ⟨KI, hKI, dIn'⟩ : ∃ KI, KI = _ ∧ Det P E2 _ (vsQSotIn (vsHAcV s) (1 :: ccs) vsHKeyT y0 24) KI :=
    ⟨_, rfl, dIn⟩
  set SC := vsQSotCost hps hm I.n Ss (vsHConjTCost Cφ N)
  have dS : EvalAll P E2 (.call (x.sb + 22) (vsPMk5 (.var 1) (.get (vsHG 6) (.nat 1)) (.var 2) (.nat 24)
      (.get (vsHG 6) (.nat 0)))) (fun w c => ∃ (Lo : List (List (Matrix (Fin (vsQD s)) (Fin (vsQD s))
        (ZMod I.p)) × Perm (Fin I.n))) (ks : List (Perm (Fin I.n))),
        w = .list [vsQPairs vsHKeyT Lo, encGroup ks] ∧ VsQOrbL (vsHAlT s) (1 :: ccs) y0 Lo ∧
        gens ks = vsQStabG hα hK y0 ∧ ks.length ≤ I.n ^ 2 ∧ c ≤ KI + SC + w.wt + 1) := by
    refine EvalAll.call_funAll dIn' fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine hsot.mono fun w c hw => ?_
    obtain ⟨Lo, ks, hw1, h2, h3, h4, h5⟩ := hw
    exact ⟨Lo, ks, hw1, h2, h3, h4, by omega⟩
  refine FunAll.intro L.hq8 (EvalAll.letE dac fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  refine EvalAll.letE dY fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  refine EvalAll.letE dS fun v3 c3 h3 => ?_
  obtain ⟨Lo, ks, rfl, hLo, hks, hksl, hc3⟩ := h3
  -- the output
  set E3 := [Val.list vs, vsHAcV s, natList (0 :: vsHKeyT y0), Val.list [vsQPairs vsHKeyT Lo, encGroup ks]]
  have v3 := Det.var' (P := P) (env := E3) (i := 3) rfl
  have dpr := Det.get' v3 (Det.nat 0)
    (show [vsQPairs vsHKeyT Lo, encGroup ks][0]? = some (vsQPairs vsHKeyT Lo) from rfl)
  have dks := Det.get' v3 (Det.nat 1)
    (show [vsQPairs vsHKeyT Lo, encGroup ks][1]? = some (encGroup ks) from rfl)
  have wp := HS.wt_pairs hLo
  set enc := fun q : List (Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) × Perm (Fin I.n) =>
    Val.list [natList (0 :: vsHKeyT q.1), encPerm q.2]
  have henc : Function.Injective enc := by
    rintro ⟨a, g⟩ ⟨a', g'⟩ h
    simp only [enc, Val.list.injEq, List.cons.injEq] at h
    obtain ⟨h1, h2, -⟩ := h
    have := vsFMat_natList_inj h1
    rw [vsHKeyT_injective (List.cons.inj this).2, encPerm_injective h2]
  have hit : ∀ q ∈ Lo, FunDet P x.it2 (.list [.nat 0, enc q]) (encPerm q.2) (100 * Ss ^ 2 + 100) := by
    intro q hq
    have a1 := Det.arg' (P := P) (vs := [Val.nat 0, enc q]) (rest := []) (j := 1) rfl
    refine FunDet.intro L.hit2 ((Det.get' a1 (Det.nat 1)
      (show [natList (0 :: vsHKeyT q.1), encPerm q.2][1]? = some (encPerm q.2) from rfl)).mono ?_)
    have := wp.2.1 q hq
    have l2 := wt_list2_le (Val.nat 0) (enc q)
    have : (enc q).wt = (Val.list [natList (0 :: vsHKeyT q.1), encPerm q.2]).wt := rfl
    have := wt_nat_le 0; have := wt_nat_le 1
    have wq : (encPerm q.2).wt < (enc q).wt := wt_le_wt_list (by simp [enc])
    omega
  have dm := Det.call (Det.mk2 (Det.nat (P := P) (env := E3) 0) dpr) (vsQ_map L.hmp2 Lo enc
    (fun q => encPerm q.2) henc hit)
  have dO := Det.mk3 (Det.nat (P := P) (env := E3) 2) dm dks
  refine EvalAll.mono dO fun w c hw => ⟨Lo, ks, hw.1, hLo, fun h => ?_, hksl, ?_⟩
  · rw [hks]
    show h ∈ genGroup (1 :: ccs) ∧ _ ↔ _
    have e : genGroup (1 :: ccs) = gens ccs := by
      apply le_antisymm
      · exact (Subgroup.closure_le _).2 fun g hg => by
          rcases List.mem_cons.1 hg with rfl | hg
          · exact one_mem _
          · exact Subgroup.subset_closure hg
      · exact Subgroup.closure_mono fun g hg => List.mem_cons_of_mem _ hg
    rw [e]
  · obtain ⟨hw1, hc⟩ := hw
    have hS1 : 1 ≤ Ss := by omega
    have s12 : Ss ≤ Ss ^ 2 := Nat.le_self_pow (by norm_num) _
    have s23 : Ss ^ 2 ≤ Ss ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
    have s34 : Ss ^ 3 ≤ Ss ^ 4 := Nat.pow_le_pow_right hS1 (by norm_num)
    have hn2 : (I.n + 1) ^ 2 ≤ 2 * Ss := by nlinarith
    have hn6 : (I.n + 1) ^ 6 ≤ 8 * Ss ^ 3 := by
      have := Nat.pow_le_pow_left hn2 3
      have e1 : ((I.n + 1) ^ 2) ^ 3 = (I.n + 1) ^ 6 := by ring
      have e2 : (2 * Ss) ^ 3 = 8 * Ss ^ 3 := by ring
      omega
    have wks := wt_encGroup_le_sq hksl
    have hLl := wp.1
    have wpr := wp.2.2
    have ePr : (Val.list (Lo.map enc)).wt = (vsQPairs vsHKeyT Lo).wt := rfl
    have wus : (Val.list (Lo.map fun q => encPerm q.2)).wt ≤ 9 * Ss ^ 3 + 4 := by
      have := vs_wt_list_le_of (Lo.map fun q => encPerm q.2) (c := 4 * Ss ^ 2) (by
        intro v hv
        obtain ⟨q, -, rfl⟩ := List.mem_map.1 hv
        exact HS.wt_perm q.2)
      rw [List.length_map] at this
      have : Lo.length * (2 * (4 * Ss ^ 2) + 1) ≤ Ss * (9 * Ss ^ 2) := Nat.mul_le_mul (by omega) (by omega)
      have e : Ss * (9 * Ss ^ 2) = 9 * Ss ^ 3 := by ring
      omega
    have l1 := wt_list2_le (vsQPairs vsHKeyT Lo) (encGroup ks)
    have l2 := wt_list2_le (Val.nat 0) (vsQPairs vsHKeyT Lo)
    have l3 := wt_list2_le (Val.nat 0) (Val.list (Lo.map enc))
    have l4 := wt_list3_le (Val.nat 2) (Val.list (Lo.map fun q => encPerm q.2)) (encGroup ks)
    have w0 := wt_nat_le 0; have w2 := wt_nat_le 2; have w24 := wt_nat_le 24
    have hm1 : Lo.length * (100 * Ss ^ 2 + 100) ≤ Ss * (200 * Ss ^ 2) := Nat.mul_le_mul (by omega) (by omega)
    have em1 : Ss * (200 * Ss ^ 2) = 200 * Ss ^ 3 := by ring
    have hm2 : mapK * (Lo.length + 1) * ((Val.list [Val.nat 0, Val.list (List.map enc Lo)]).wt +
        (Val.list (List.map (fun q => encPerm q.2) Lo)).wt + 1) ≤ 1000 * Ss * (100 * Ss ^ 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
    have em2 : 1000 * Ss * (100 * Ss ^ 3) = 10 ^ 5 * Ss ^ 4 := by ring
    -- the earlier stages
    have wIn := (wt_vsQSotIn_le hα HS).1
    have wBl := vsP_wt_perms hn B (by omega)
    have wvs := wt_list2_le A (Val.list (B.map encPerm))
    have evs : (Val.list vs).wt = (Val.list [A, Val.list (B.map encPerm)]).wt := rfl
    have hfr : fr.wt < (Val.list gl).wt := wt_le_wt_list (by simp [gl])
    have hΓ : (vsQGam I).wt < (Val.list gl).wt := wt_le_wt_list (by simp [gl])
    have hG6 : (encGroup ccs).wt < (Val.list gl).wt := wt_le_wt_list (by simp [gl])
    have eAg : A.wt = (Val.list gl).wt := rfl
    have wyk := vsHKeyT_wt hpN hDD1 y0 (by simp [y0, hBl])
    have l5 := wt_list_le [vsQGam I, fr, Val.nat I.p, Val.nat (vsQD s), natList (vsWZ (vsQCs s).length)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at l5
    have eac' : (vsHAcV s).wt = (Val.list [vsQGam I, fr, Val.nat I.p, Val.nat (vsQD s),
      natList (vsWZ (vsQCs s).length)]).wt := rfl
    have wpn := wt_nat_le I.p
    have wDn := wt_nat_le (vsQD s)
    have hD : vsQD s ≤ N := (Nat.le_mul_self _).trans (by omega)
    have l6 := wt_list2_le (vsQGam I) fr
    have l7 := wt_list2_le (Val.list [vsQGam I, fr]) (Val.list (B.map encPerm))
    have hz' : (natList (vsWZ (vsQCs s).length)).wt < F0.wt := wt_le_wt_list (by simp [F0])
    have hF0 : F0.wt < fr.wt := wt_le_wt_list (by simp [fr, F0, vsWFrVal])
    have ezz : (Val.list ((vsWZ (vsQD s)).map Val.nat)).wt = (natList (vsWZ (vsQCs s).length)).wt := rfl
    have wn' := wt_nat_le I.n
    have l8 := wt_list2_le (Val.nat I.n) (Val.list ((1 :: ccs).map encPerm))
    have eG : (encGroup ccs).wt = (Val.list [Val.nat I.n, Val.list ((1 :: ccs).map encPerm)]).wt := rfl
    have hq3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have hgs : (Val.list ((1 :: ccs).map encPerm)).wt <
        (Val.list [Val.nat I.n, Val.list ((1 :: ccs).map encPerm)]).wt := wt_le_wt_list (by simp)
    have eIn' : (vsQSotIn (vsHAcV s) (1 :: ccs) vsHKeyT y0 24).wt = (Val.list [vsHAcV s,
      Val.list ((1 :: ccs).map encPerm), natList (0 :: vsHKeyT y0), Val.nat 24, Val.nat I.n]).wt := rfl
    have q13 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by omega) _
    have hvs : (Val.list vs).wt ≤ 4 * Ss := by omega
    have hC1 : c1 ≤ 1000 * Ss := by omega
    have hC2 : c2 ≤ vsHY0Cost Cφ N + 1000 * Ss := by omega
    have hKI' : KI ≤ 400 * Ss ^ 4 := by
      rw [hKI]
      have := wIn
      have q14 : N + 1 ≤ (N + 1) ^ 4 := by omega
      linarith
    have hC3 : c3 ≤ SC + 10 ^ 4 * Ss ^ 4 := by linarith
    have mk : mapK = 1000 := rfl
    have hCc : c ≤ 2 * 10 ^ 5 * Ss ^ 4 := by linarith
    rw [hw1] at *
    unfold vsHQ8Cost
    have mk : mapK = 1000 := rfl
    have hSC : SC = vsQSotCost hps hm I.n Ss (vsHConjTCost Cφ N) := rfl
    clear_value SC
    omega

end GI.Impl
