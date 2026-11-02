import Workspace.Impl.VsHQ8Math

/-!
# The key of the tuple `(T(b))_{b ∈ B}`

* `vsHPcE`, `vsHPc_spec`: on `[[Γ, frame], b]`, the piece `[0, key T(b)]`.
* `vsHY0E`, `vsHY0_spec`: on `[[Γ, frame], B]`, `[0, keyT (T(b))_b]`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I}

/-- On `[[Γ, frame], b]`: the piece of `T(b)`. -/
def vsHPcE (loc fl app : ℕ) : Expr :=
  .call app (mk2 (mk1 (.nat 0))
    (.call fl (.call loc (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1)))))

/-- On `[[Γ, frame], B]`: the key of the tuple. -/
def vsHY0E (mp cat app : ℕ) : Expr :=
  .call app (mk2 (mk2 (.nat 0) (.length (arg 1))) (.call cat (.call mp (mk2 (arg 0) (arg 1)))))

/-- The cost of a piece. -/
def vsHPcCost (Cφ N : ℕ) : ℕ := vsPLocCost Cφ N + 10 ^ 8 * (N + 1) ^ 4

set_option maxHeartbeats 4000000 in
theorem vsHPc_spec {P : Program} {f loc fl app phi Cφ N : ℕ} (hf : P.funs[f]? = some (vsHPcE loc fl app))
    (hloc : P.funs[loc]? = some (vsPLocE phi (loc + 1))) (hwl : P.HasAt (loc + 1) (vsWLocFuns (loc + 1)))
    (hfl : P.HasAt fl (vsWFlatFuns fl)) (happ : P.HasAt app (appendFuns app))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hsz : VsQSz I.p I.d (vsQExp I) N) (hΓ : (vsQGam I).wt ≤ N) (hn : I.n ≤ N)
    (hfr : VsWFrOK I.p N I.d s.ws' (vsQCs s)) (hDD1 : vsQD s * vsQD s + 1 ≤ N)
    {b : Perm (Fin I.n)} (hb : b ∈ gens I.gs) :
    FunDet P f (.list [.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s)], encPerm b])
      (natList (vsHPc (vsHT s b))) (vsHPcCost Cφ N) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hpN := hsz.pN
  have hDD : vsQD s * vsQD s ≤ N := by omega
  have hDN : vsQD s ≤ N := (Nat.le_mul_self _).trans hDD
  set cl := [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s)]
  set vs := [Val.list cl, encPerm b]
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have gΓ := Det.get' a0 (Det.nat 0) (show cl[0]? = some (vsQGam I) from rfl)
  have gF := Det.get' a0 (Det.nat 1) (show cl[1]? = some (vsWFrVal I.p I.d s.ws' (vsQCs s)) from rfl)
  have dL := Det.call (Det.mk3 gΓ gF a1) (vsPLoc_spec hloc hwl hphi hsz hΓ hn hfr hb)
  rw [vsPLocL_eq_vsQL] at dL
  have hsq := vsQL_sq (p := I.p) (vsHT s b)
  have dF := Det.call dL (vsWFlat_spec hfl hpN hDD (M := vsQL (vsHT s b)) ⟨fun a ha => hsq.rows a ha, hsq.len⟩)
  have eF : natList (vsQL (vsHT s b)).flatten = .list ((vsHKey (vsHT s b)).map Val.nat) := rfl
  rw [eF] at dF
  obtain ⟨KA, hKA, dA⟩ : ∃ KA, KA = _ ∧ Det P [Val.list vs] (mk2 (mk1 (.nat 0))
      (.call fl (.call loc (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1)))))
      (.list [.list [Val.nat 0], .list ((vsHKey (vsHT s b)).map Val.nat)]) KA :=
    ⟨_, rfl, Det.mk2 (Det.mk1 (Det.nat 0)) dF⟩
  have hkl := vsHKey_length (vsHT s b)
  have wY : (natList (vsHPc (vsHT s b))).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (B := N) (fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · omega
      · exact (vsHKey_lt _ y hy).le.trans hpN) (by rw [vsHPc_length]; omega)
  refine FunDet.intro hf (EvalAll.call_funAll dA fun v ca hv => ?_)
  obtain ⟨rfl, hca⟩ := hv
  refine (append_spec happ [Val.nat 0] ((vsHKey (vsHT s b)).map Val.nat)).mono fun w cc hw => ⟨?_, ?_⟩
  · rw [hw.1]; rfl
  · have hw' : w = natList (vsHPc (vsHT s b)) := by rw [hw.1]; rfl
    obtain ⟨-, h2⟩ := hw
    rw [hw'] at h2 ⊢
    rw [List.length_map, hkl] at h2
    have wFr : (vsWFrVal I.p I.d s.ws' (vsQCs s)).wt ≤ 500 * (N + 1) ^ 3 := wt_vsWFrVal_le hfr
    have wb := wt_encPerm_le b
    have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
    have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have l1 := wt_list2_le (vsQGam I) (vsWFrVal I.p I.d s.ws' (vsQCs s))
    have l2 := wt_list2_le (Val.list cl) (encPerm b)
    have l3 := wt_list3_le (vsQGam I) (vsWFrVal I.p I.d s.ws' (vsQCs s)) (encPerm b)
    have wq := wt_vsWVs_le (N := N) (us := vsQL (vsHT s b)) (fun u hu => ⟨fun y hy =>
      ((hsq.rows u hu).1 y hy).le.trans hpN, by rw [(hsq.rows u hu).2]; exact hDN⟩) (by rw [hsq.len]; omega)
    have wk : (Val.list ((vsHKey (vsHT s b)).map Val.nat)).wt ≤ 5 * (N + 1) ^ 2 :=
      le_trans (wt_list_sublist (List.sublist_cons_self _ _)) wY
    have l4 := wt_list2_le (Val.list [Val.nat 0]) (Val.list ((vsHKey (vsHT s b)).map Val.nat))
    have l5 := wt_list_le [Val.nat 0]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at l5
    have w0 := wt_nat_le 0
    have evs : (Val.list vs).wt = (Val.list [Val.list cl, encPerm b]).wt := rfl
    have ecl : (Val.list cl).wt = (Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s)]).wt := rfl
    have hKP : loopModK * (vsQD s * vsQD s + 1) * ((Val.list [Val.list [Val.nat 0],
        Val.list ((vsHKey (vsHT s b)).map Val.nat)]).wt + vsQD s * vsQD s + (natList (vsHPc (vsHT s b))).wt + 1)
        ≤ 1000 * (N + 1) * (30 * (N + 1) ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
    have e3 : 1000 * (N + 1) * (30 * (N + 1) ^ 2) = 30000 * (N + 1) ^ 3 := by ring
    simp only [vsHPcCost, vsPLocCost] at *
    omega

/-- The cost of the tuple key. -/
def vsHY0Cost (Cφ N : ℕ) : ℕ := (N + 1) * vsHPcCost Cφ N + 10 ^ 12 * (N + 1) ^ 8

set_option maxHeartbeats 8000000 in
theorem vsHY0_spec {P : Program} {f mp it cat loc fl app phi Cφ N : ℕ} (hf : P.funs[f]? = some (vsHY0E mp cat app))
    (hmp : P.HasAt mp (mapFuns mp it)) (hit : P.funs[it]? = some (vsHPcE loc fl app))
    (hcat : P.HasAt cat (vsWFlatFuns cat))
    (hloc : P.funs[loc]? = some (vsPLocE phi (loc + 1))) (hwl : P.HasAt (loc + 1) (vsWLocFuns (loc + 1)))
    (hfl : P.HasAt fl (vsWFlatFuns fl)) (happ : P.HasAt app (appendFuns app))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hsz : VsQSz I.p I.d (vsQExp I) N) (hΓ : (vsQGam I).wt ≤ N) (hn : I.n ≤ N)
    (hfr : VsWFrOK I.p N I.d s.ws' (vsQCs s)) (hDD1 : vsQD s * vsQD s + 1 ≤ N)
    {B : List (Perm (Fin I.n))} (hB : ∀ b ∈ B, b ∈ gens I.gs) (hBl : B.length ≤ N) :
    FunDet P f (.list [.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s)], .list (B.map encPerm)])
      (natList (0 :: vsHKeyT (B.map (vsHT s)))) (vsHY0Cost Cφ N) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hpN := hsz.pN
  set cl := [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s)]
  set vs := [Val.list cl, Val.list (B.map encPerm)]
  set m := B.length
  set DD := vsQD s * vsQD s
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have hit' : ∀ b ∈ B, FunDet P it (.list [Val.list cl, encPerm b]) (natList (vsHPc (vsHT s b)))
      (vsHPcCost Cφ N) := fun b hb =>
    vsHPc_spec hit hloc hwl hfl happ hphi hsz hΓ hn hfr hDD1 (hB b hb)
  have dmap := Det.call (Det.mk2 a0 a1) (vsQ_map hmp B encPerm (fun b => natList (vsHPc (vsHT s b)))
    encPerm_injective hit')
  set xss := B.map fun b => (vsHPc (vsHT s b)).map Val.nat
  have exs : Val.list (B.map fun b => natList (vsHPc (vsHT s b))) = Val.list (xss.map Val.list) := by
    simp [xss, List.map_map, Function.comp_def, natList]
  rw [exs] at dmap
  set ys := B.map (vsHT s)
  have hys : ys.length = m := by simp [ys, m]
  have ef : xss.flatten = (ys.map vsHPc).flatten.map Val.nat := by
    simp [xss, ys, List.map_flatten, List.map_map, Function.comp_def]
  have wpc : ∀ M' : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p),
      (natList (vsHPc M')).wt ≤ 5 * (N + 1) ^ 2 := fun M' =>
    wt_natList_le_sq (B := N) (fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · omega
      · exact (vsHKey_lt M' y hy).le.trans hpN) (by rw [vsHPc_length]; omega)
  have hmDD : m * (DD + 1) ≤ N * N := Nat.mul_le_mul hBl (by omega)
  have q2 : N * N + 1 ≤ (N + 1) ^ 2 := by nlinarith
  have hl : (ys.map vsHPc).flatten.length = m * (DD + 1) := by
    simp only [List.length_flatten, List.map_map, Function.comp_def, vsHPc_length]
    simp [hys]
    exact Or.inl rfl
  have hfw : (Val.list ((ys.map vsHPc).flatten.map Val.nat)).wt ≤ 20 * (N + 1) ^ 4 := by
    have hz : ∀ y ∈ (ys.map vsHPc).flatten, y ≤ N := by
      intro y hy
      obtain ⟨l, hl, hyl⟩ := List.mem_flatten.1 hy
      obtain ⟨M, -, rfl⟩ := List.mem_map.1 hl
      rcases List.mem_cons.1 hyl with rfl | hy'
      · omega
      · exact (vsHKey_lt M y hy').le.trans hpN
    have := wt_natList_le_sq (xs := (ys.map vsHPc).flatten) (B := (N + 1) ^ 2)
      (fun y hy => (hz y hy).trans (by nlinarith)) (by rw [hl]; omega)
    have e : 5 * ((N + 1) ^ 2 + 1) ^ 2 ≤ 20 * (N + 1) ^ 4 := by nlinarith
    exact this.trans e
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have p3 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hWi : (Val.list (xss.map Val.list)).wt ≤ 1000 * (N + 1) ^ 4 := by
    have := vs_wt_list_le_of (xss.map Val.list) (c := 5 * (N + 1) ^ 2) (by
      intro v hv
      simp only [xss, List.map_map, List.mem_map, Function.comp_def] at hv
      obtain ⟨b, -, rfl⟩ := hv
      exact wpc _)
    have hlen : (xss.map Val.list).length = m := by simp [xss, m]
    rw [hlen] at this
    have : m * (2 * (5 * (N + 1) ^ 2) + 1) ≤ (N + 1) * (11 * (N + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (N + 1) * (11 * (N + 1) ^ 2) = 11 * (N + 1) ^ 3 := by ring
    omega
  have dcat := Det.call dmap
    (vsWConcat_spec hcat xss (N := N) (by simp [xss]; omega)
      (fun xs hxs => by
        simp only [xss, List.mem_map] at hxs
        obtain ⟨b, -, rfl⟩ := hxs
        rw [List.length_map, vsHPc_length]; omega)
      (by rw [ef]; exact hfw.trans (by omega)) hWi)
  rw [ef] at dcat
  have dl := Det.length a1
  rw [List.length_map] at dl
  set fl' := (ys.map vsHPc).flatten
  obtain ⟨KA, hKA, dA⟩ : ∃ KA, KA = _ ∧ Det P [Val.list vs] (mk2 (mk2 (.nat 0) (.length (arg 1)))
      (.call cat (.call mp (mk2 (arg 0) (arg 1))))) (.list [.list [Val.nat 0, Val.nat m], .list (fl'.map Val.nat)]) KA :=
    ⟨_, rfl, Det.mk2 (Det.mk2 (Det.nat 0) dl) dcat⟩
  have wout : (natList (0 :: vsHKeyT ys)).wt ≤ 20 * (N + 1) ^ 4 := by
    have hz : ∀ y ∈ 0 :: vsHKeyT ys, y ≤ (N + 1) ^ 2 := by
      intro y hy
      simp only [vsHKeyT, List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · omega
      · rw [hys]; nlinarith
      · obtain ⟨l, hl, hyl⟩ := List.mem_flatten.1 hy
        obtain ⟨M, -, rfl⟩ := List.mem_map.1 hl
        rcases List.mem_cons.1 hyl with rfl | hy'
        · omega
        · have := (vsHKey_lt M y hy').le.trans hpN; nlinarith
    have := wt_natList_le_sq (xs := 0 :: vsHKeyT ys) (B := (N + 1) ^ 2) hz (by
      simp only [vsHKeyT, List.length_cons, hl]; nlinarith)
    have e : 5 * ((N + 1) ^ 2 + 1) ^ 2 ≤ 20 * (N + 1) ^ 4 := by nlinarith
    exact this.trans e
  set KP := loopModK * (m * (DD + 1) + 1) *
    ((Val.list [.list [Val.nat 0, Val.nat m], .list (fl'.map Val.nat)]).wt + m * (DD + 1) +
      (natList (0 :: vsHKeyT ys)).wt + 1)
  refine FunDet.intro hf (EvalAll.call_funAll dA fun v ca hv => ?_)
  obtain ⟨rfl, hca⟩ := hv
  refine (append_spec happ [Val.nat 0, Val.nat m] (fl'.map Val.nat)).mono fun w c hw => ⟨?_, ?_⟩
  · rw [hw.1]; simp [vsHKeyT, hys, natList, fl']
  · have hw' : w = natList (0 :: vsHKeyT ys) := by rw [hw.1]; simp [vsHKeyT, hys, natList, fl']
    obtain ⟨-, h2⟩ := hw
    rw [hw'] at h2 ⊢
    have hc : c ≤ KP := by
      simp only [KP]
      rw [List.length_map, hl] at h2
      exact h2
    have wFr := wt_vsWFrVal_le hfr
    have wBl := vsP_wt_perms hn B (by omega)
    have l1 := wt_list2_le (vsQGam I) (vsWFrVal I.p I.d s.ws' (vsQCs s))
    have ecl : (Val.list cl).wt = (Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s)]).wt := rfl
    have l2 := wt_list2_le (Val.list cl) (Val.list (B.map encPerm))
    have evs : (Val.list vs).wt = (Val.list [Val.list cl, Val.list (B.map encPerm)]).wt := rfl
    have l3 := wt_list2_le (Val.list [Val.nat 0, Val.nat m]) (Val.list (fl'.map Val.nat))
    have l4 := wt_list2_le (Val.nat 0) (Val.nat m)
    have w0 := wt_nat_le 0
    have wm := wt_nat_le m
    have hfw' : (Val.list (fl'.map Val.nat)).wt ≤ 20 * (N + 1) ^ 4 := hfw
    have hmD : m * (DD + 1) ≤ (N + 1) ^ 2 := by omega
    have q46 : (N + 1) ^ 4 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have q68 : (N + 1) ^ 6 ≤ (N + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    have q58 : (N + 1) ^ 5 ≤ (N + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    have hKPa : (Val.list [.list [Val.nat 0, Val.nat m], .list (fl'.map Val.nat)]).wt + m * (DD + 1) +
        (natList (0 :: vsHKeyT ys)).wt + 1 ≤ 200 * (N + 1) ^ 4 := by
      have p4 : N + 1 ≤ (N + 1) ^ 4 := by omega
      clear_value fl'
      omega
    have hKP : KP ≤ 1000 * (N + 1) ^ 2 * (200 * (N + 1) ^ 4) := by
      simp only [KP]
      exact Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) hKPa
    have e6 : 1000 * (N + 1) ^ 2 * (200 * (N + 1) ^ 4) = 2 * 10 ^ 5 * (N + 1) ^ 6 := by ring
    have hM1 : m * vsHPcCost Cφ N ≤ (N + 1) * vsHPcCost Cφ N := Nat.mul_le_mul_right _ (by omega)
    have hM2 : mapK * (m + 1) * ((Val.list [Val.list cl, Val.list (B.map encPerm)]).wt +
        (Val.list (xss.map Val.list)).wt + 1) ≤ 1000 * (N + 1) * (10 ^ 4 * (N + 1) ^ 4) := by
      refine Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
    have e5 : 1000 * (N + 1) * (10 ^ 4 * (N + 1) ^ 4) = 10 ^ 7 * (N + 1) ^ 5 := by ring
    clear_value KP
    unfold vsHY0Cost
    have lk : loopModK = 1000 := rfl
    have mk : mapK = 1000 := rfl
    linarith

end GI.Impl
