module

public import Workspace.Impl.VsBFld0E

@[expose] public section

/-!
# The field-line base

On `[lc, Lb]`: the preparation (both chains and `t`), then the test `T = 0`, which reads the
first orbit list of the translation chain: it has one point when `T = 0` and `p` points when
`T = M'`. Then the case `T = 0` (`vsB0E`) or `T = M'` (`vsBCaseME`).

* `vsBFldE`, `vsBFld_spec`: the program satisfies `VsQFldHyp`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-! ### The mathematics of the test -/

theorem vsB_wM_e0 {s : VsQSt I} (hD : 1 ≤ vsQD s) (M : List (List ℕ)) :
    vsWM I.p (vsQD s) M *ᵥ vsBe0 s hD = vsWV I.p (vsQD s) (M.getD 0 []) := by
  funext i
  simp [vsBe0, vsWM, vsFMatrix, Matrix.mulVec_single]

/-- The first columns of `Lb` span everything, so every vector is `X e₀` with `X ∈ L`. -/
theorem vsB_span_rows0 {s : VsQSt I} (hD : 1 ≤ vsQD s) {Lb : List (List (List ℕ))}
    (hLb : ∀ X, X ∈ Submodule.span (ZMod I.p) {X | ∃ M ∈ Lb, vsWM I.p (vsQD s) M = X} ↔ X ∈ vsBLamA s)
    (htop : vsWSp I.p (vsQD s) (vsQRows0 Lb) = ⊤) :
    ∀ v, ∃ X ∈ vsBLamA s, X *ᵥ vsBe0 s hD = v := by
  have hle : vsWSp I.p (vsQD s) (vsQRows0 Lb) ≤
      (Subalgebra.toSubmodule (vsBLamA s)).map (LinearMap.applyₗ (R := ZMod I.p) (vsBe0 s hD) ∘ₗ
        Matrix.toLin'.toLinearMap.comp (LinearMap.id)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hu
    refine ⟨vsWM I.p (vsQD s) M, (hLb _).mp (Submodule.subset_span ⟨M, hM, rfl⟩), ?_⟩
    simp [Matrix.toLin'_apply, vsB_wM_e0 hD]
  intro v
  have hv : v ∈ vsWSp I.p (vsQD s) (vsQRows0 Lb) := htop ▸ Submodule.mem_top
  obtain ⟨X, hX, hXv⟩ := hle hv
  exact ⟨X, hX, by simpa [Matrix.toLin'_apply] using hXv⟩

section Test

variable {s : VsQSt I} (hs : VsQStOK s) (hD : 1 ≤ vsQD s) {L : List (ZMod I.p × Perm (Fin I.n))}
  (hL : VsBOrbL (vsBAj s 0) (vsBH1 hs : Set (Perm (Fin I.n))) 0 L)
include hs hL

/-- If `T = 0`, the first orbit has one point. -/
theorem vsB_orb_T0 (hT : ∀ k ∈ vsBH1 hs, vsBAlpha s k 0 = 0) : L.length ≤ 1 := by
  have hsub : (L.map Prod.fst).toFinset ⊆ {0} := by
    intro y hy
    rw [List.mem_toFinset, hL.mem] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    simp [vsBAj, hT k hk]
  have h1 := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hL.nodup, List.length_map] at h1
  simpa using h1

include hD in
/-- If `T = M'`, the first orbit has at least two points. -/
theorem vsB_orb_TM (htm : ∀ v, ∃ k ∈ vsBH1 hs, vsBAlpha s k 0 = v) : 2 ≤ L.length := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  obtain ⟨k, hk, hkv⟩ := htm (vsBe0 s hD)
  have h0 : (0 : ZMod I.p) ∈ L.map Prod.fst := by
    rw [hL.mem]
    exact ⟨1, (vsBH1 hs).one_mem, by simp [vsBAj, (vsBAlpha_act hs).one]⟩
  have h1 : (1 : ZMod I.p) ∈ L.map Prod.fst := by
    rw [hL.mem]
    refine ⟨k, hk, ?_⟩
    rw [vsBAj, dif_pos (show 0 < vsQD s by omega), hkv]
    simp [vsBe0]
  have hsub : ({0, 1} : Finset (ZMod I.p)) ⊆ (L.map Prod.fst).toFinset := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact List.mem_toFinset.mpr h0
    · exact List.mem_toFinset.mpr h1
  have h2 := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hL.nodup, List.length_map, Finset.card_pair zero_ne_one] at h2
  exact h2

end Test


/-- The weight of the output of the preparation. -/
theorem vsB_wt_prep (hps : PointwiseStab) (hm : Membership) {S Tm Cφ : ℕ} (hS : VsQDSz I S Tm) {s : VsQSt I}
    (hs : VsQStOK s) (hD : 1 ≤ vsQD s) {gsA : List (Perm (Fin I.n))}
    {LsA : List (List ((Fin (vsQD s) → ZMod I.p) × Perm (Fin I.n)))}
    {gsB : List (Perm (Fin I.n))} {LsB : List (List (ZMod I.p × Perm (Fin I.n)))}
    (hglA : gsA.length ≤ I.n ^ 2 + 2) (hlA : LsA.length = (vsBPs I.n).length) (hWA : ∀ L ∈ LsA, VsBPW (vsBS2 S) vsQVec L)
    (hglB : gsB.length ≤ I.n ^ 2 + 2) (hlB : LsB.length = vsQD s) (hWB : ∀ L ∈ LsB, VsBPW (vsBS2 S) vsBKeyB L) :
    (Val.list [vsBCtxA s hD, vsBCtxB s,
      .list [.list (gsA.map encPerm), .list (LsA.map (vsQPairs vsQVec))],
      .list [.list (gsB.map encPerm), .list (LsB.map (vsQPairs vsBKeyB))],
      natList (vsQVec (vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)))]).wt ≤
      4 * vsBChCost hps hm I.n S Cφ + 10 ^ 8 * S ^ 6 := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hdS := hS.d
  have hnS := hS.n
  have wA := vsB_chain_out_wt hps hm (Cφ := Cφ) hS1 (vsB_wt_gens hS hglA)
    (by rw [hlA]; simp [vsBPs]; omega) hWA
  have wB := vsB_chain_out_wt hps hm (Cφ := Cφ) hS1 (vsB_wt_gens hS hglB) (by omega) hWB
  have w1 := vsB_wt_ctxA hS hs hD
  have w2 := vsB_wt_ctxB hS hs
  have w3 := (vsB_wt_vecA hS hs (vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x))).1
  have w := wt_list_le [vsBCtxA s hD, vsBCtxB s,
      .list [.list (gsA.map encPerm), .list (LsA.map (vsQPairs vsQVec))],
      .list [.list (gsB.map encPerm), .list (LsB.map (vsQPairs vsBKeyB))],
      natList (vsQVec (vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)))]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w
  have q36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have := Nat.one_le_pow 6 S hS1
  omega

/-! ### The program -/

/-- The field-line base, on `[lc, Lb]`. -/
def vsBFldE (prep c0 cM : ℕ) : Expr :=
  .letE (.call prep (arg 0))
  (.ite (.arith .lt (.length (.get (.get (.get (.var 1) (.nat 3)) (.nat 1)) (.nat 0))) (.nat 2))
    (.call c0 (mk3 (arg 0) (.var 1) (arg 1)))
    (.call cM (mk2 (arg 0) (.var 1))))

/-- The layout of the field-line base. -/
structure VsBFldAt (P : Program) (hps : PointwiseStab) (hm : Membership) (f prep c0 cM unit appd rng chA chB co lin
    sotA sotB bA bB phi jp jm fd tst c0b m eqN tau dA red sc sv mI fI mF fF sv2 rp mm fl ch cmp dB mc cr : ℕ) :
    Prop where
  hf0 : P.funs[f]? = some (vsBFldE prep c0 cM)
  hprep : VsBPrepAt P hps hm prep unit appd rng chA chB co lin sotA sotB bA bB phi jp jm
  hc0 : VsB0At P hm c0 fd tst c0b m lin eqN tau rng dA red appd bA bB sc sv mI fI mF fF sv2 rp mm fl ch sotA cmp
    phi jp jm
  hcM : VsBMAt P hm cM rng dB mc cr appd red bB sotB cmp phi jp jm

/-- The weight bound of the inputs of the two cases. -/
noncomputable def vsBFldW (hps : PointwiseStab) (hm : Membership) (n S Cφ : ℕ) : ℕ :=
  10 * vsBChCost hps hm n S Cφ + 10 ^ 10 * S ^ 8

/-- The cost bound of the field-line base. -/
noncomputable def vsBFldCost (hps : PointwiseStab) (hm : Membership) (n S Cφ : ℕ) : ℕ :=
  110 * vsBChCost hps hm n S Cφ + 10 ^ 13 * S ^ 8 + vsBMCost hm n S Cφ + vsB0TCost hm n S Cφ +
    10 ^ 5 * S ^ 2 * vsBFldW hps hm n S Cφ

set_option maxHeartbeats 16000000 in
/-- **The field-line base.** -/
theorem vsBFld_spec (hps : PointwiseStab) (hm : Membership) {P : Program}
    {f prep c0 cM unit appd rng chA chB co lin sotA sotB bA bB phi jp jm fd tst c0b m eqN tau dA red sc sv mI fI
      mF fF sv2 rp mm fl ch cmp dB mc cr Cφ S Tm : ℕ}
    (H : VsBFldAt P hps hm f prep c0 cM unit appd rng chA chB co lin sotA sotB bA bB phi jp jm fd tst c0b m eqN
      tau dA red sc sv mI fI mF fF sv2 rp mm fl ch cmp dB mc cr)
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) (hab : s.Ab) (hD : 1 ≤ vsQD s) :
    VsQFldHyp P f (vsBFldCost hps hm I.n S Cφ) hs := by
  intro Lb hLb hdom' htop hLbl hsq
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hdom : VsBDom s := hdom'
  have hspan := vsB_span_rows0 hD hLb htop
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hdS := hS.d
  have hnS := hS.n
  have hpS := hS.p
  set lc := vsQLCV s
  set LbV := vsFMatsVal Lb
  set A := Val.list [lc, LbV]
  have wlc : lc.wt ≤ 10 ^ 6 * S ^ 6 := vsQ_wt_LC hS hs
  have hs2 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ hS1
  have hSS : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have wLb : LbV.wt ≤ 640 * S ^ 8 := by
    have := wt_vsWMats_le (N := S ^ 2) (hpS.trans hSS) (by omega) hsq (by
      have := Nat.mul_le_mul (show vsQD s ≤ S by omega) (show vsQD s ≤ S by omega)
      rw [sq]; omega)
    have h1 : (S ^ 2 + 1) ^ 4 ≤ (2 * S ^ 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have e : (2 * S ^ 2) ^ 4 = 16 * S ^ 8 := by ring
    have eL : LbV.wt = (vsFMatsVal Lb).wt := rfl
    omega
  have rd : ∀ rest k v, [lc, LbV][k]? = some v → Det P (A :: rest) (arg k) v (2 * A.wt + k + 5) :=
    fun rest k v hv => Det.arg' (vs := [lc, LbV]) (rest := rest) hv
  have wA : A.wt ≤ 2 * (10 ^ 6 * S ^ 6 + 640 * S ^ 8) + 10 := by
    have := wt_list2_le lc LbV
    have eA : A.wt = (Val.list [lc, LbV]).wt := rfl
    omega
  have q68 : S ^ 6 ≤ S ^ 8 := Nat.pow_le_pow_right hS1 (by norm_num)
  refine FunAll.intro H.hf0 (EvalAll.letE (Ra := fun w c => VsBPrepOut hs hD S w ∧
      c ≤ 110 * vsBChCost hps hm I.n S Cφ + 10 ^ 13 * S ^ 8)
    (EvalAll.call_funAll (rd [] 0 lc rfl) fun v ca hv => ?_) fun v1 c1 hv1 => ?_)
  · obtain ⟨rfl, hca⟩ := hv
    refine (vsBPrep_spec hps hm H.hprep hphi hS hs hab hD hdom).mono fun w c hw => ⟨hw.1, ?_⟩
    obtain ⟨⟨gsA, LsA, gsB, LsB, rfl, -, hglA, hlA, -, hWA, -, hglB, hlB, -, hWB⟩, hc⟩ := hw
    have wp := vsB_wt_prep hps hm (Cφ := Cφ) hS hs hD hglA hlA hWA hglB hlB hWB
    have q8 : 1 ≤ S ^ 8 := Nat.one_le_pow _ _ hS1
    clear_value lc LbV A
    omega
  obtain ⟨⟨gsA, LsA, gsB, LsB, rfl, hgA, hglA, hlA, hOA, hWA, hgB, hglB, hlB, hOB, hWB⟩, hc1⟩ := hv1
  obtain ⟨L0, LsB', rfl⟩ : ∃ L0 LsB', LsB = L0 :: LsB' :=
    List.exists_cons_of_ne_nil (by rintro rfl; simp at hlB; omega)
  have wp := vsB_wt_prep hps hm (Cφ := Cφ) hS hs hD hglA hlA hWA hglB hlB hWB
  set chB := Val.list [.list (gsB.map encPerm), .list ((L0 :: LsB').map (vsQPairs vsBKeyB))]
  set pv := Val.list [vsBCtxA s hD, vsBCtxB s,
      .list [.list (gsA.map encPerm), .list (LsA.map (vsQPairs vsQVec))], chB,
      natList (vsQVec (vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)))]
  set E1 := [A, pv]
  have hLB0 : 0 < (L0 :: LsB').length := by simp
  have dchB := Det.get' (Det.var' (P := P) (env := E1) (i := 1) rfl) (Det.nat 3)
    (show [vsBCtxA s hD, vsBCtxB s, .list [.list (gsA.map encPerm), .list (LsA.map (vsQPairs vsQVec))], chB,
      natList (vsQVec (vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)))][3]? = some chB from rfl)
  have dLs := Det.get' dchB (Det.nat 1)
    (show [Val.list (gsB.map encPerm), .list ((L0 :: LsB').map (vsQPairs vsBKeyB))][1]? =
      some (.list ((L0 :: LsB').map (vsQPairs vsBKeyB))) from rfl)
  have dL0 := Det.get' dLs (Det.nat 0)
    (show ((L0 :: LsB').map (vsQPairs vsBKeyB))[0]? = some (vsQPairs vsBKeyB L0) from rfl)
  have dlen := Det.length (vs := L0.map fun q => .list [natList (0 :: vsBKeyB q.1), encPerm q.2]) dL0
  have dlt := Det.arith (op := .lt) dlen (Det.nat 2)
  simp only [List.length_map, GI.Machine.BinOp.eval] at dlt
  have hO0 : VsBOrbL (vsBAj s 0) (vsBH1 hs : Set (Perm (Fin I.n))) 0 L0 := by
    have := hOB 0 hLB0
    simp only [List.getElem_cons_zero] at this
    rw [show (List.range (vsQD s)).getD 0 0 = 0 by
      rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp, List.take_zero, vsBKs_nil] at this
    exact this
  have wpv : pv.wt ≤ 4 * vsBChCost hps hm I.n S Cφ + 10 ^ 8 * S ^ 6 := wp
  have q8 : 1 ≤ S ^ 8 := Nat.one_le_pow _ _ hS1
  have hW3 : (Val.list [lc, pv, LbV]).wt ≤ vsBFldW hps hm I.n S Cφ := by
    have := wt_list3_le lc pv LbV
    unfold vsBFldW; omega
  have hW2 : (Val.list [lc, pv]).wt ≤ vsBFldW hps hm I.n S Cφ := by
    have := wt_list2_le lc pv
    unfold vsBFldW; omega
  have wchB : chB.wt < pv.wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have wLs : (Val.list ((L0 :: LsB').map (vsQPairs vsBKeyB))).wt < chB.wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ List.mem_cons_self)
  have wL0 : (vsQPairs vsBKeyB L0).wt < (Val.list ((L0 :: LsB').map (vsQPairs vsBKeyB))).wt :=
    wt_le_wt_list List.mem_cons_self
  refine EvalAll.ite dlt (fun _ _ h => ⟨_, h.1⟩) fun x cc hx => ?_
  obtain ⟨hx1, hcc⟩ := hx
  have hx2 : x = if L0.length < 2 then 1 else 0 := Val.nat.inj hx1
  have hcc' : cc ≤ 30 * vsBChCost hps hm I.n S Cφ + 10 ^ 10 * S ^ 6 := by
    have := wt_nat_le L0.length
    have hl0 : L0.length ≤ (vsQPairs vsBKeyB L0).wt := by
      have := length_lt_wt_list (L0.map fun q => Val.list [natList (0 :: vsBKeyB q.1), encPerm q.2])
      rw [List.length_map] at this
      exact this.le
    have := wt_nat_le (if L0.length < 2 then 1 else 0)
    have : (if L0.length < 2 then 1 else 0) ≤ 1 := by split <;> omega
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3
    have := Nat.one_le_pow 6 S hS1
    have epv : (Val.list [vsBCtxA s hD, vsBCtxB s,
      .list [.list (gsA.map encPerm), .list (LsA.map (vsQPairs vsQVec))], chB,
      natList (vsQVec (vsBCo s (vsWV I.p I.d s.y - vsWV I.p I.d s.x)))]).wt = pv.wt := rfl
    have wp' := vsB_wt_prep hps hm (Cφ := Cφ) hS hs hD hglA hlA hWA hglB hlB hWB
    clear_value lc LbV A chB pv
    omega
  clear hcc hx1
  have hW1 : vsBFldW hps hm I.n S Cφ ≤ S ^ 2 * vsBFldW hps hm I.n S Cφ := Nat.le_mul_of_pos_left _ hs2
  have eW : 10 ^ 5 * S ^ 2 * vsBFldW hps hm I.n S Cφ = 10 ^ 5 * (S ^ 2 * vsBFldW hps hm I.n S Cφ) := by ring
  have eW3 : 3 * 10 ^ 4 * S ^ 2 * vsBFldW hps hm I.n S Cφ = 3 * 10 ^ 4 * (S ^ 2 * vsBFldW hps hm I.n S Cφ) := by
    ring
  have hWc : vsBChCost hps hm I.n S Cφ ≤ vsBFldW hps hm I.n S Cφ := by unfold vsBFldW; omega
  have hW8 : 10 ^ 10 * S ^ 8 ≤ vsBFldW hps hm I.n S Cφ := by unfold vsBFldW; omega
  have q68' : S ^ 6 ≤ S ^ 8 := Nat.pow_le_pow_right hS1 (by norm_num)
  by_cases hlt : L0.length < 2
  · have hx0 : x ≠ 0 := by rw [hx2, if_pos hlt]; decide
    rw [if_neg hx0]
    have hT : ∀ k ∈ vsBH1 hs, vsBAlpha s k 0 = 0 := by
      rcases vsB_dich hs hdom hD hspan with hT | htm
      · exact hT
      · exact absurd (vsB_orb_TM hs hD hO0 htm) (by omega)
    refine EvalAll.call_funAll (Det.mk3 (rd [pv] 0 lc rfl) (Det.var' (P := P) (env := E1) (i := 1) rfl)
      (rd [pv] 1 LbV rfl)) fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (vsB0_spec hm H.hc0 hphi hS hs hab hD hdom hspan hLb hsq hLbl hgA hglA hlA hOA hWA chB hT hW3).mono ?_
    rintro w c ⟨a, rfl, ha, hc⟩
    refine ⟨⟨a, rfl, ha⟩, ?_⟩
    have wl := hS.wt_ans (a := a) (by
      rcases a with _ | ⟨h0, ks⟩
      · simp
      · intro r hr; simp at hr; rw [← hr]; exact ha.2.2)
    have wl2 := wt_list2_le (.nat 0) (vsQAnsV a)
    have el : (vsQLeafV a).wt = (Val.list [.nat 0, vsQAnsV a]).wt := rfl
    have w3 := wt_list3_le lc pv LbV
    have := wt_nat_le 0
    have := Nat.one_le_pow 6 S hS1
    unfold vsBFldCost
    clear_value lc LbV A chB pv
    omega
  · have hx0 : x = 0 := by rw [hx2, if_neg hlt]
    rw [if_pos hx0]
    have htm : ∀ v, ∃ k ∈ vsBH1 hs, vsBAlpha s k 0 = v := by
      rcases vsB_dich hs hdom hD hspan with hT | htm
      · exact absurd (vsB_orb_T0 hs hO0 hT) (by omega)
      · exact htm
    refine EvalAll.call_funAll (Det.mk2 (rd [pv] 0 lc rfl) (Det.var' (P := P) (env := E1) (i := 1) rfl))
      fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (vsBCaseM_spec hm H.hcM hphi hS hs hD hgB hglB hlB hOB hWB htm hW2).mono ?_
    rintro w c ⟨a, rfl, ha, hc⟩
    refine ⟨⟨a, rfl, ha⟩, ?_⟩
    have wl := hS.wt_ans (a := a) (by
      rcases a with _ | ⟨h0, ks⟩
      · simp
      · intro r hr; simp at hr; rw [← hr]; exact ha.2.2)
    have wl2 := wt_list2_le (.nat 0) (vsQAnsV a)
    have el : (vsQLeafV a).wt = (Val.list [.nat 0, vsQAnsV a]).wt := rfl
    have w2 := wt_list2_le lc pv
    have := wt_nat_le 0
    have := Nat.one_le_pow 6 S hS1
    unfold vsBFldCost
    clear_value lc LbV A chB pv
    omega

end GI.Impl
