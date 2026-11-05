module

public import Workspace.Impl.VsHConjMath
public import Workspace.Impl.VsQChunk

@[expose] public section

/-!
# The conjugation program

`vsHConjE` is the action program of the small orbit transporter for `vsHAl`: on
`[ac, g, [0, key M]]` (with `key M` the flattened canonical list of `M`) it returns
`[0, key (T(g⁻¹) M T(g))]` (`vsHConj_spec`).
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {s : VsQSt I}

/-- The key of a matrix: its canonical list, flattened. -/
noncomputable def vsHKey (M : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) : List ℕ :=
  (vsQL M).flatten

theorem vsHKey_length (M : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) :
    (vsHKey M).length = vsQD s * vsQD s := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have h := vsQL_sq (p := I.p) M
  rw [vsHKey, GI.Proved.vsFA_flatten_length fun r hr => (h.rows r hr).2, h.len]

theorem vsHKey_lt (M : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) : ∀ y ∈ vsHKey M, y < I.p := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have h := vsQL_sq (p := I.p) M
  exact GI.Proved.vsFA_flatten_lt fun r hr => (h.rows r hr).1

/-- Cutting the key gives back the rows. -/
theorem vsHKey_chunk (M : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) :
    Val.list ((vsQChunk (.nat 0) (vsQD s) (vsQD s) ((vsHKey M).map Val.nat)).map Val.list) =
      vsWVs (vsQL M) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have h := vsQL_sq (p := I.p) M
  have e : (vsHKey M).map Val.nat = ((vsQL M).map fun r => r.map Val.nat).flatten := by
    rw [vsHKey, List.map_flatten]
  have hl : ((vsQL M).map fun r => r.map Val.nat).length = vsQD s := by rw [List.length_map, h.len]
  have hc := vsQChunk_flatten (Val.nat 0) (vsQD s) ((vsQL M).map fun r => r.map Val.nat)
    (fun x hx => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
      rw [List.length_map]; exact (h.rows r hr).2)
  rw [hl] at hc
  rw [e, hc]
  simp [vsWVs, List.map_map, Function.comp_def, natList]

theorem vsHKey_injective : Function.Injective (vsHKey (s := s)) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  intro M M' h
  have := congrArg (fun k => Val.list ((vsQChunk (.nat 0) (vsQD s) (vsQD s) (k.map Val.nat)).map Val.list)) h
  simp only [vsHKey_chunk] at this
  have e : vsQL M = vsQL M' := by
    have := congrArg (fun v : Val => v) this
    unfold vsWVs at this
    have h1 := Val.list.inj this
    exact (List.map_injective_iff.2 (fun a b hab => vsFMat_natList_inj hab)) h1
  rw [← vsFMatrix_vsQL (p := I.p) M, e, vsFMatrix_vsQL]

/-- The stored local matrix of `g` is the canonical list of `T(g)`. -/
theorem vsPLocL_eq_vsQL (g : Perm (Fin I.n)) :
    vsPLocL I s.ws' (vsQCs s) g = vsQL (vsHT s g) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hsq := vsPLocL_sq (I := I) (ws' := s.ws') (cs := vsQCs s) g
  rw [vsQL_of_sq (p := I.p) (d := vsQD s) ⟨hsq.2, fun a ha => hsq.1 a ha⟩, vsFMatrix_loc]
  rfl

/-- Entry `k` of the action context. -/
def vsHAc (k : ℕ) : Expr := .get (arg 0) (.nat k)

/-- The action context: `[Γ, frame, p, D, 0^D]`. -/
noncomputable def vsHAcV (s : VsQSt I) : Val :=
  .list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat I.p, .nat (vsQD s), natList (vsWZ (vsQD s))]

/-- The conjugation program, on `[ac, g, [0, key M]]`. -/
def vsHConjE (tl ch loc inv mm fl app : ℕ) : Expr :=
  .letE (.call tl (arg 2))
  (.letE (.call ch (mk3 (vsHAc 3) (vsHAc 3) (.var 1)))
  (.letE (.call loc (mk3 (vsHAc 0) (vsHAc 1) (arg 1)))
  (.letE (.call loc (mk3 (vsHAc 0) (vsHAc 1) (.call inv (arg 1))))
  (.letE (.call mm (mk2 (mk3 (vsHAc 2) (.var 3) (vsHAc 4)) (.var 2)))
  (.letE (.call mm (mk2 (mk3 (vsHAc 2) (.var 5) (vsHAc 4)) (.var 4)))
    (.call app (mk2 (mk1 (.nat 0)) (.call fl (.var 6)))))))))

/-- The indices of the conjugation program. -/
structure VsHCX where
  (conj tl ch loc phi inv mm fl app : ℕ)

/-- The layout of the conjugation program. -/
structure VsHCLay (P : Program) (x : VsHCX) : Prop where
  hconj : P.funs[x.conj]? = some (vsHConjE x.tl x.ch x.loc x.inv x.mm x.fl x.app)
  htl : P.HasAt x.tl (tailFuns x.tl)
  hch : P.HasAt x.ch (vsQChunkFuns x.ch)
  hloc : P.funs[x.loc]? = some (vsPLocE x.phi (x.loc + 1))
  hwl : P.HasAt (x.loc + 1) (vsWLocFuns (x.loc + 1))
  hinv : P.HasAt x.inv (invFuns x.inv)
  hmm : P.HasAt x.mm (vsFMatMulFuns x.mm)
  hfl : P.HasAt x.fl (vsWFlatFuns x.fl)
  happ : P.HasAt x.app (appendFuns x.app)

/-- The cost of the conjugation program. -/
def vsHConjCost (Cφ N : ℕ) : ℕ := 2 * vsPLocCost Cφ N + 10 ^ 11 * (N + 1) ^ 6

/-- **The conjugation program.** -/
theorem vsHConj_spec {P : Program} {x : VsHCX} (L : VsHCLay P x) {Cφ N : ℕ}
    (hphi : ∀ g ∈ gens I.gs, FunDet P x.phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hsz : VsQSz I.p I.d (vsQExp I) N) (hΓ : (vsQGam I).wt ≤ N) (hn : I.n ≤ N)
    (hfr : VsWFrOK I.p N I.d s.ws' (vsQCs s)) (hDD1 : vsQD s * vsQD s + 1 ≤ N)
    (hac : (vsHAcV s).wt ≤ 1000 * (N + 1) ^ 3)
    {g : Perm (Fin I.n)} (hg : g ∈ gens I.gs) (M : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)) :
    FunDet P x.conj (.list [vsHAcV s, encPerm g, natList (0 :: vsHKey M)])
      (natList (0 :: vsHKey (vsHT s g⁻¹ * M * vsHT s g)))
      (vsHConjCost Cφ N) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hp0 := I.prime.pos
  have hpN := hsz.pN
  have hDc : (vsQCs s).length = (vsQD s) := rfl
  have hDD : (vsQD s) * (vsQD s) ≤ N := by omega
  have hDN : (vsQD s) ≤ N := (Nat.le_mul_self (vsQD s)).trans hDD
  set fr := vsWFrVal I.p I.d s.ws' (vsQCs s)
  set acl := [vsQGam I, fr, .nat I.p, .nat (vsQD s), natList (vsWZ (vsQD s))]
  have eac : vsHAcV s = .list acl := rfl
  rw [eac] at hac ⊢
  set k := vsHKey M
  set vs := [Val.list acl, encPerm g, natList (0 :: k)]
  -- reading
  have rac : ∀ rest : List Val, ∀ j (v : Val), acl[j]? = some v →
      Det P (Val.list vs :: rest) (vsHAc j) v (2 * (Val.list vs).wt + 0 + 5 + (j + 3) + v.wt + 1) :=
    fun rest j v h => Det.get' (Det.arg' (P := P) (vs := vs) (rest := rest) (j := 0) rfl) (Det.nat j) h
  have rg : ∀ rest : List Val, Det P (Val.list vs :: rest) (arg 1) (encPerm g) _ := fun rest =>
    Det.arg' (P := P) (vs := vs) (rest := rest) (j := 1) rfl
  -- 1. the tail
  have d1 := Det.call (Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl)
    (GI.Lang.tail_spec L.htl (Val.nat 0) (k.map Val.nat))
  -- 2. the rows
  set E1 := [Val.list vs, Val.list (k.map Val.nat)]
  have hkl : k.length = (vsQD s) * (vsQD s) := vsHKey_length M
  have wk : (natList (0 :: k)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (B := N) (fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · omega
      · exact (vsHKey_lt M y hy).le.trans hpN) (by simp; omega)
  have wk' : (Val.list (k.map Val.nat)).wt ≤ 5 * (N + 1) ^ 2 :=
    le_trans (wt_list_sublist (List.sublist_cons_self _ _)) wk
  have d2 := Det.call (Det.mk3 (rac [Val.list (k.map Val.nat)] 3 (Val.nat (vsQD s)) rfl)
    (rac [Val.list (k.map Val.nat)] 3 (Val.nat (vsQD s)) rfl) (Det.var' (P := P) (env := E1) (i := 1) rfl))
    (vsQChunk_spec L.hch (k := (vsQD s)) (m := (vsQD s)) (N := N) (W := 5 * (N + 1) ^ 2) (by simp [hkl]) hDN hDN wk')
  rw [vsHKey_chunk] at d2
  -- 3. `T(g)`
  set E2 := [Val.list vs, Val.list (k.map Val.nat), vsWVs (vsQL M)]
  have d3 := Det.call (Det.mk3 (rac [Val.list (k.map Val.nat), vsWVs (vsQL M)] 0 (vsQGam I) rfl)
    (rac [Val.list (k.map Val.nat), vsWVs (vsQL M)] 1 fr rfl) (rg [Val.list (k.map Val.nat), vsWVs (vsQL M)]))
    (vsPLoc_spec L.hloc L.hwl hphi hsz hΓ hn hfr hg)
  rw [vsPLocL_eq_vsQL] at d3
  -- 4. `T(g⁻¹)`
  set R := vsWVs (vsQL (vsHT s g))
  set E3 := [Val.list vs, Val.list (k.map Val.nat), vsWVs (vsQL M), R]
  have di := Det.call (rg [Val.list (k.map Val.nat), vsWVs (vsQL M), R]) (inv_spec L.hinv g)
  have d4 := Det.call (Det.mk3 (rac [Val.list (k.map Val.nat), vsWVs (vsQL M), R] 0 (vsQGam I) rfl)
    (rac [Val.list (k.map Val.nat), vsWVs (vsQL M), R] 1 fr rfl) di)
    (vsPLoc_spec L.hloc L.hwl hphi hsz hΓ hn hfr (inv_mem hg))
  rw [vsPLocL_eq_vsQL] at d4
  set Li := vsWVs (vsQL (vsHT s g⁻¹))
  -- 5. `M T(g)`
  set z := vsWZ (vsQD s)
  have hzF : ∀ X : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p), VsFMatFits I.p N (vsQL X) z := by
    intro X
    have hX := vsQL_sq (p := I.p) X
    refine ⟨fun y hy => ?_, by simp [z, vsWZ]; omega, fun r hr y hy => ((hX.rows r hr).1 y hy).le.trans hpN,
      fun r hr => by rw [(hX.rows r hr).2]; exact hDN, fun r hr => by
        rw [(hX.rows r hr).2]; simp [z, vsWZ], by rw [hX.len]; exact hDN⟩
    simp only [z, vsWZ, List.mem_replicate] at hy; omega
  have hAF : ∀ X Y : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p), ∀ a ∈ vsQL X,
      (∀ y ∈ a, y < I.p) ∧ a.length ≤ N ∧ (vsQL (p := I.p) Y).length ≤ a.length := by
    intro X Y a ha
    have hX := vsQL_sq (p := I.p) X
    have hM := vsQL_sq (p := I.p) Y
    exact ⟨(hX.rows a ha).1, by rw [(hX.rows a ha).2]; exact hDN, by rw [(hX.rows a ha).2, hM.len]⟩
  have hmul : ∀ A B : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p),
      Val.list ((vsQL A).map fun a => natList (vsFRowMul I.p a (vsQL B) z)) = vsWVs (vsQL (A * B)) := by
    intro A B
    rw [← vsQL_mul (p := I.p) A B]
    simp only [vsWVs, vsFMatMulL, List.map_map, Function.comp_def, z, vsWZ]
  set E4 := [Val.list vs, Val.list (k.map Val.nat), vsWVs (vsQL M), R, Li]
  have rz := rac [Val.list (k.map Val.nat), vsWVs (vsQL M), R, Li] 4 (natList z) rfl
  have rp := rac [Val.list (k.map Val.nat), vsWVs (vsQL M), R, Li] 2 (.nat I.p) rfl
  have d5 := Det.call (Det.mk2 (Det.mk3 rp (Det.var' (P := P) (env := E4) (i := 3) rfl) rz)
    (Det.var' (P := P) (env := E4) (i := 2) rfl))
    (vsFMatMul_spec L.hmm hp0 hpN (hzF (vsHT s g)) (hAF M _) (by
      rw [(vsQL_sq (p := I.p) M).len]; exact hDN))
  rw [hmul] at d5
  -- 6. `T(g⁻¹) (M T(g))`
  set X := vsWVs (vsQL (M * vsHT s g))
  set E5 := [Val.list vs, Val.list (k.map Val.nat), vsWVs (vsQL M), R, Li, X]
  have rz' := rac [Val.list (k.map Val.nat), vsWVs (vsQL M), R, Li, X] 4 (natList z) rfl
  have rp' := rac [Val.list (k.map Val.nat), vsWVs (vsQL M), R, Li, X] 2 (.nat I.p) rfl
  have d6 := Det.call (Det.mk2 (Det.mk3 rp' (Det.var' (P := P) (env := E5) (i := 5) rfl) rz')
    (Det.var' (P := P) (env := E5) (i := 4) rfl))
    (vsFMatMul_spec L.hmm hp0 hpN (hzF (M * vsHT s g)) (hAF (vsHT s g⁻¹) _) (by
      rw [(vsQL_sq (p := I.p) (vsHT s g⁻¹)).len]; exact hDN))
  rw [hmul, ← _root_.mul_assoc] at d6
  -- 7. flatten, 8. prepend `0`
  set Y := vsHT s g⁻¹ * M * vsHT s g
  set E6 := [Val.list vs, Val.list (k.map Val.nat), vsWVs (vsQL M), R, Li, X, vsWVs (vsQL Y)]
  have hYsq := vsQL_sq (p := I.p) Y
  have d7 := Det.call (Det.var' (P := P) (env := E6) (i := 6) rfl)
    (vsWFlat_spec L.hfl hpN hDD (M := vsQL Y) ⟨fun a ha => hYsq.rows a ha, hYsq.len⟩)
  have d0 := Det.mk1 (Det.nat (P := P) (env := E6) 0)
  have eF : natList (vsQL Y).flatten = .list ((vsHKey Y).map Val.nat) := rfl
  rw [eF] at d7
  obtain ⟨KA, hKA, dA⟩ : ∃ KA, KA = _ ∧ Det P E6 (mk2 (mk1 (.nat 0)) (.call x.fl (.var 6)))
      (.list [.list [Val.nat 0], .list ((vsHKey Y).map Val.nat)]) KA := ⟨_, rfl, Det.mk2 d0 d7⟩
  have hYl : (vsHKey Y).length = (vsQD s) * (vsQD s) := vsHKey_length Y
  have wY : (natList (0 :: vsHKey Y)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (B := N) (fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · omega
      · exact (vsHKey_lt Y y hy).le.trans hpN) (by simp; omega)
  set KP := loopModK * ((vsQD s) * (vsQD s) + 1) *
    ((Val.list [.list [Val.nat 0], .list ((vsHKey Y).map Val.nat)]).wt + (vsQD s) * (vsQD s) + 5 * (N + 1) ^ 2 + 1)
  have d8 : Det P E6 (.call x.app (mk2 (mk1 (.nat 0)) (.call x.fl (.var 6))))
      (natList (0 :: vsHKey Y)) (KA + KP + (natList (0 :: vsHKey Y)).wt + 1) := by
    refine EvalAll.call_funAll dA fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (append_spec L.happ [Val.nat 0] ((vsHKey Y).map Val.nat)).mono fun w c hw => ⟨?_, ?_⟩
    · rw [hw.1]; rfl
    · have h2 := hw.2
      have hw' : w = natList (0 :: vsHKey Y) := by rw [hw.1]; rfl
      rw [List.length_map, hYl] at h2
      rw [hw'] at h2 ⊢
      have hKPle : loopModK * ((vsQD s) * (vsQD s) + 1) * ((Val.list [.list [Val.nat 0], .list ((vsHKey Y).map Val.nat)]).wt +
          (vsQD s) * (vsQD s) + (natList (0 :: vsHKey Y)).wt + 1) ≤ KP :=
        Nat.mul_le_mul_left _ (by omega)
      clear rac rg d1 d2 d3 di d4 hzF hAF hmul rz rp d5 rz' rp' d6 hYsq d7 d0 dA
      clear_value fr acl k vs E1 E2 R E3 Li z E4 X E5 Y E6 KP
      omega
  refine FunDet.intro L.hconj ((Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE d4
    (Det.letE d5 (Det.letE d6 d8)))))).mono ?_)
  clear rac rg d1 d2 d3 di d4 hzF hAF hmul rz rp d5 rz' rp' d6 hYsq d7 d0 dA d8 L hphi hsz hfr
  -- weights
  have wsq : ∀ Z : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p),
      (vsWVs (vsQL Z)).wt ≤ 11 * (N + 1) ^ 3 + 4 := fun Z => by
    have hZ := vsQL_sq (p := I.p) Z
    exact wt_vsWVs_le (fun u hu => ⟨fun y hy => ((hZ.rows u hu).1 y hy).le.trans hpN,
      by rw [(hZ.rows u hu).2]; exact hDN⟩) (by rw [hZ.len]; omega)
  have wM := wsq M
  have wR : R.wt ≤ 11 * (N + 1) ^ 3 + 4 := wsq _
  have wLi : Li.wt ≤ 11 * (N + 1) ^ 3 + 4 := wsq _
  have wX : X.wt ≤ 11 * (N + 1) ^ 3 + 4 := wsq _
  have wYv := wsq Y
  clear wsq
  have wg := wt_encPerm_le g
  have wgi := wt_encPerm_le g⁻¹
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hn4 : (I.n + 1) ^ 4 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q45 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q56 : (N + 1) ^ 5 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have wvs := wt_list3_le (Val.list acl) (encPerm g) (natList (0 :: k))
  have hm : ∀ v ∈ acl, v.wt < (Val.list acl).wt := fun v hv => wt_le_wt_list hv
  have m0 := hm (vsQGam I) (by simp [acl])
  have m1 := hm fr (by simp [acl])
  have m2 := hm (.nat I.p) (by simp [acl])
  have m3 := hm (.nat (vsQD s)) (by simp [acl])
  have m4 := hm (natList z) (by simp [acl, z])
  clear hm
  have l3 := wt_list3_le (Val.nat (vsQD s)) (Val.nat (vsQD s)) (Val.list (k.map Val.nat))
  have l4 := wt_list3_le (vsQGam I) fr (encPerm g)
  have l5 := wt_list3_le (vsQGam I) fr (encPerm g⁻¹)
  have l6 := wt_list3_le (Val.nat I.p) R (natList z)
  have l7 := wt_list2_le (Val.list [Val.nat I.p, R, natList z]) (vsWVs (vsQL M))
  have l8 := wt_list3_le (Val.nat I.p) X (natList z)
  have l9 := wt_list2_le (Val.list [Val.nat I.p, X, natList z]) Li
  have l10 := wt_list2_le (Val.list [Val.nat 0]) (Val.list ((vsHKey Y).map Val.nat))
  have l11 := wt_list_le [Val.nat 0]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at l11
  have wY' : (Val.list ((vsHKey Y).map Val.nat)).wt ≤ 5 * (N + 1) ^ 2 :=
    le_trans (wt_list_sublist (List.sublist_cons_self _ _)) wY
  have w0 := wt_nat_le 0
  have wkl : k.length ≤ N := by omega
  have hT : loopModK * ((k.map Val.nat).length + 1) * (3 * (Val.list (Val.nat 0 :: k.map Val.nat)).wt + 1) ≤
      1000 * (N + 1) * (15 * (N + 1) ^ 2 + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by simp; omega)) (by
      have : (Val.list (Val.nat 0 :: k.map Val.nat)).wt = (natList (0 :: k)).wt := rfl
      omega)
  have hT' : 1000 * (N + 1) * (15 * (N + 1) ^ 2 + 1) ≤ 16000 * (N + 1) ^ 3 := by
    have : 1000 * (N + 1) * (15 * (N + 1) ^ 2 + 1) ≤ 1000 * (N + 1) * (16 * (N + 1) ^ 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have e : 1000 * (N + 1) * (16 * (N + 1) ^ 2) = 16000 * (N + 1) ^ 3 := by ring
    omega
  have hC : 10 ^ 8 * (N + 1) ^ 4 * (5 * (N + 1) ^ 2 + (N + 1) ^ 2) = 6 * 10 ^ 8 * (N + 1) ^ 6 := by ring
  have hKP : KP ≤ 1000 * (N + 1) * (30 * (N + 1) ^ 2) := by
    simp only [KP]
    exact Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
  have hKP' : 1000 * (N + 1) * (30 * (N + 1) ^ 2) = 30000 * (N + 1) ^ 3 := by ring
  have ez : (natList z).wt = (natList (vsWZ (vsQD s))).wt := rfl
  have evs : (Val.list vs).wt = (Val.list [Val.list acl, encPerm g, natList (0 :: k)]).wt := rfl
  clear_value fr acl k vs E1 E2 R E3 Li z E4 X E5 Y E6 KP
  simp only [vsHConjCost, vsPLocCost, invK] at *
  omega

end GI.Impl
