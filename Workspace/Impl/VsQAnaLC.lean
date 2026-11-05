module

public import Workspace.Impl.VsQDrv
public import Workspace.Proved.VsQLoc
public import Workspace.Impl.VsWProgFrame
public import Workspace.Impl.VsWProgCo
public import Workspace.Impl.VsFAlgSpanStep

@[expose] public section

/-!
# The local context of the analysis

The analysis starts by computing the frame of the state and the local matrices of the
generators `1 :: hs` (`vsQLC_spec`). The result is the *local context*
`[state, frame, D, local matrices]` (`vsQLCV`).
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The local matrices (stored) of `1 :: hs`. -/
noncomputable def vsQMs (s : VsQSt I) : List (List (List ℕ)) :=
  (1 :: s.hs).map fun h => vsWLoc I.p I.d s.ws' (vsQCs s) (vsQL (vsQPhi I h)ᵀ)

/-- The local context. -/
noncomputable def vsQLCV (s : VsQSt I) : Val :=
  .list [vsQStV I s, vsWFrVal I.p I.d s.ws' (vsQCs s), .nat (vsQD s), vsFMatsVal (vsQMs s)]

/-- On `[[Γ, frame], h]`: the local matrix of `h`. -/
def vsQLCItemE (phi loc : ℕ) : Expr :=
  .call loc (mk2 (.get (arg 0) (.nat 1))
    (.get (.call phi (mk2 (.get (arg 0) (.nat 0)) (arg 1))) (.nat 3)))

/-- On a state: the local context. -/
def vsQLCE (fr mp : ℕ) : Expr :=
  .letE (.call fr (mk4 (.get (.get (arg 0) (.nat 2)) (.nat 0))
      (.length (.get (.get (arg 0) (.nat 2)) (.nat 1))) (arg 2) (arg 3)))
    (.letE (.call mp (mk2 (mk2 (arg 0) (.var 1)) (.get (arg 1) (.nat 1))))
      (mk4 (.var 0) (.var 1) (.length (.get (.var 1) (.nat 2))) (.var 2)))

/-- The local context program at base `b` (133 functions). -/
def vsQLCFuns (b phi : ℕ) : List Expr :=
  [vsQLCE (b + 2) (b + 97), vsQLCItemE phi (b + 100)] ++ vsWFrameFuns (b + 2) ++
    mapFuns (b + 97) (b + 1) ++ vsWLocFuns (b + 100)

theorem vsQLCFuns_length (b phi : ℕ) : (vsQLCFuns b phi).length = 133 := by
  simp [vsQLCFuns, vsWFrameFuns_length, vsWLocFuns_length, mapFuns, loopFuns]

/-- The cost of the local context. -/
def vsQLCCost (Cφ S : ℕ) : ℕ := S ^ 2 * Cφ + 10 ^ 17 * S ^ 9

theorem vsQ_four_pow {S : ℕ} (k : ℕ) (hS : 1 ≤ S) : (4 * S + 1) ^ k ≤ 5 ^ k * S ^ k := by
  rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) k

theorem vsQMs_sq (s : VsQSt I) : ∀ M ∈ vsQMs s, VsWSq I.p (vsQD s) M := by
  intro M hM
  simp only [vsQMs, List.mem_map] at hM
  obtain ⟨h, -, rfl⟩ := hM
  exact vsWLoc_fit I.prime.pos _ _ _

theorem vsQD_le {s : VsQSt I} (hs : VsQStOK s) : vsQD s ≤ I.d := by
  rw [vsQD_eq hs]; unfold VsQSt.dim; have := vsQRk_le (I := I) s.ws; omega

set_option maxHeartbeats 4000000 in
/-- **The local context.** -/
theorem vsQLC_spec {P : Program} {b phi Cφ S Tm : ℕ} (h : P.HasAt b (vsQLCFuns b phi))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) :
    FunDet P b (vsQStV I s) (vsQLCV s) (vsQLCCost Cφ S) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hSn := hS.n
  have hSd := hS.d
  have hSp := hS.p
  have hp1 := I.prime.one_lt
  have h0 : P.funs[b]? = some (vsQLCE (b + 2) (b + 97)) := h.get (j := 0) (by simp [vsQLCFuns])
  have h1 : P.funs[b + 1]? = some (vsQLCItemE phi (b + 100)) := h.get (j := 1) (by simp [vsQLCFuns])
  have hfr : P.HasAt (b + 2) (vsWFrameFuns (b + 2)) := h.block 2 rfl
  have hmp : P.HasAt (b + 97) (mapFuns (b + 97) (b + 1)) := h.block 97 rfl
  have hloc : P.HasAt (b + 100) (vsWLocFuns (b + 100)) := h.block 100 rfl
  set N := 4 * S with hN
  have hcl : (vsQCs s).length ≤ s.ws'.length + s.ws.length :=
    vsWComp_length_le I.prime.pos (show I.p ≤ N by omega) (show I.d ≤ N by omega) hs.fit' hs.fit
  have hwl := hs.wl
  have hwl' := hs.wl'
  have hFr : VsWFrOK I.p N I.d s.ws' (vsQCs s) :=
    ⟨hp1, by omega, by omega, hs.fit', vsWComp_fit I.prime.pos hs.fit' hs.fit, by omega⟩
  have hsz : VsQSz I.p I.d (vsQExp I) S := by
    refine ⟨by omega, by omega, ?_, I.prime.pos⟩
    have h1 := hS.g
    have h2 : (Val.nat (vsQExp I)).wt < (vsQE I.p I.d (vsQExp I) 1).wt :=
      wt_le_wt_list (show Val.nat (vsQExp I) ∈ [Val.nat I.p, natList (List.replicate I.d 0),
        .nat (vsQExp I), .list ((vsQL (1 : Matrix (Fin I.d) (Fin I.d) (ZMod I.p))ᵀ).map natList)]
        by simp)
    have h3 : (vsQE I.p I.d (vsQExp I) 1).wt < (vsQGam I).wt :=
      wt_le_wt_list (show vsQE I.p I.d (vsQExp I) 1 ∈ [encGroup I.gs, vsQTable I,
        vsQE I.p I.d (vsQExp I) 1] by simp)
    omega
  -- powers of `S`
  have p5 := vsQ_four_pow 5 hS1
  have p3 := vsQ_four_pow 3 hS1
  have q35 : S ^ 3 ≤ S ^ 5 := hS.pow_le (by omega)
  have q57 : S ^ 5 ≤ S ^ 7 := hS.pow_le (by omega)
  have q79 : S ^ 7 ≤ S ^ 9 := hS.pow_le (by omega)
  have q13 : S ≤ S ^ 3 := by have := hS.pow_le (show 1 ≤ 3 by omega); simpa using this
  have q23 : S ^ 2 ≤ S ^ 3 := hS.pow_le (by omega)
  have q02 : 1 ≤ S ^ 2 := by have := hS.pow_le (show 0 ≤ 2 by omega); simpa using this
  norm_num at p5 p3
  -- the item
  set Γ := vsQGam I with hΓ
  set frV := vsWFrVal I.p I.d s.ws' (vsQCs s) with hfrV
  have wfr : frV.wt ≤ 500 * (N + 1) ^ 3 := wt_vsWFrVal_le hFr
  have hitem : ∀ g ∈ 1 :: s.hs, FunDet P (b + 1) (.list [.list [Γ, frV], encPerm g])
      (vsWVs (vsWLoc I.p I.d s.ws' (vsQCs s) (vsQL (vsQPhi I g)ᵀ)))
      (Cφ + 10 ^ 14 * S ^ 5) := by
    intro g hg
    have hgG : g ∈ gens I.gs := by
      rcases List.mem_cons.mp hg with rfl | hg
      · exact one_mem _
      · exact hs.prob.le (Subgroup.subset_closure hg)
    set c := Val.list [Γ, frV]
    set a := Val.list [c, encPerm g]
    have a0 := Det.arg' (P := P) (rest := []) (vs := [c, encPerm g]) (j := 0) rfl
    have a1 := Det.arg' (P := P) (rest := []) (vs := [c, encPerm g]) (j := 1) rfl
    have gΓ := Det.get' a0 (Det.nat 0) (show [Γ, frV][0]? = some Γ from rfl)
    have gF := Det.get' a0 (Det.nat 1) (show [Γ, frV][1]? = some frV from rfl)
    have dE := Det.call (Det.mk2 gΓ a1) (hphi g hgG)
    have hsq := vsQL_sq (vsQPhi I g)ᵀ
    have dA := Det.get' dE (Det.nat 3) (show [Val.nat I.p, natList (List.replicate I.d 0),
      .nat (vsQExp I), .list ((vsQL (vsQPhi I g)ᵀ).map natList)][3]? =
        some (vsWVs (vsQL (vsQPhi I g)ᵀ)) from rfl)
    have dL := Det.call (Det.mk2 gF dA) (vsWLoc_spec hloc hFr (A := vsQL (vsQPhi I g)ᵀ)
      ⟨fun r hr => hsq.rows r hr, hsq.len⟩)
    refine FunDet.intro h1 (dL.mono ?_)
    have wE := wt_vsQE_le hsz (vsQPhi I g)
    have wA := wt_vsQL_le hsz (vsQPhi I g)ᵀ
    have wg := hS.wt_perm g
    have wΓ := hS.g
    have wc := wt_list2_le Γ frV
    have wa := wt_list2_le c (encPerm g)
    have w2 := wt_list2_le Γ (encPerm g)
    have w3 := wt_list2_le frV (vsWVs (vsQL (vsQPhi I g)ᵀ))
    have wL := wt_vsWVs_le (N := N) (VsWFit.bnd (vsWLoc_fit (d := I.d) I.prime.pos s.ws' (vsQCs s)
      (vsQL (vsQPhi I g)ᵀ)).1 (by omega) (by omega))
      (by rw [(vsWLoc_fit (d := I.d) I.prime.pos s.ws' (vsQCs s) (vsQL (vsQPhi I g)ᵀ)).2]; omega)
    have eA : (vsWVs (vsQL (vsQPhi I g)ᵀ)).wt = (Val.list ((vsQL (vsQPhi I g)ᵀ).map natList)).wt :=
      rfl
    have ec : c.wt = (Val.list [Γ, frV]).wt := rfl
    have ea : a.wt = (Val.list [c, encPerm g]).wt := rfl
    have := wt_nat_le 3
    have eΓ : Γ.wt = (vsQGam I).wt := rfl
    have eN5 : (N + 1) ^ 5 = (4 * S + 1) ^ 5 := rfl
    have q1 : (S + 1) ^ 3 ≤ 8 * S ^ 3 := by
      have : (S + 1) ^ 3 ≤ (2 * S) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      nlinarith
    rw [hN] at wfr wL
    omega
  have dmap := vsQ_map hmp (1 :: s.hs) encPerm
    (fun g => vsWVs (vsWLoc I.p I.d s.ws' (vsQCs s) (vsQL (vsQPhi I g)ᵀ))) encPerm_injective hitem
  -- the main body
  set st := vsQStV I s with hst
  have a0 := Det.arg' (P := P) (rest := []) (vs := [Γ, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
    natList s.x, natList s.y]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [Γ, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
    natList s.x, natList s.y]) (j := 1) rfl
  have a2 := Det.arg' (P := P) (rest := []) (vs := [Γ, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
    natList s.x, natList s.y]) (j := 2) rfl
  have a3 := Det.arg' (P := P) (rest := []) (vs := [Γ, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
    natList s.x, natList s.y]) (j := 3) rfl
  have gE := Det.get' a0 (Det.nat 2) (show [encGroup I.gs, vsQTable I,
    vsQE I.p I.d (vsQExp I) 1][2]? = some (vsQE I.p I.d (vsQExp I) 1) from rfl)
  have gp := Det.get' gE (Det.nat 0) (show [Val.nat I.p, natList (List.replicate I.d 0),
    .nat (vsQExp I), .list ((vsQL (1 : Matrix (Fin I.d) (Fin I.d) (ZMod I.p))ᵀ).map natList)][0]? =
      some (.nat I.p) from rfl)
  have gz := Det.get' gE (Det.nat 1) (show [Val.nat I.p, natList (List.replicate I.d 0),
    .nat (vsQExp I), .list ((vsQL (1 : Matrix (Fin I.d) (Fin I.d) (ZMod I.p))ᵀ).map natList)][1]? =
      some (natList (List.replicate I.d 0)) from rfl)
  have gd := Det.length gz
  have elen : ((List.replicate I.d 0).map Val.nat).length = I.d := by simp
  rw [elen] at gd
  have dfr := Det.call (Det.mk4 gp gd a2 a3) (vsWFrame_spec hfr hp1 (N := N) (by omega) (by omega)
    hs.fit' hs.fit (by omega))
  have ecs : vsWComp I.p s.ws' s.ws = vsQCs s := rfl
  rw [ecs] at dfr
  have ecsl : ((vsQCs s).map natList).length = vsQD s := by simp
  set Ms := (1 :: s.hs).map fun g => vsWVs (vsWLoc I.p I.d s.ws' (vsQCs s) (vsQL (vsQPhi I g)ᵀ))
    with hMs
  have eMs : Val.list Ms = vsFMatsVal (vsQMs s) := by
    simp only [hMs, vsFMatsVal, vsQMs, List.map_map]; rfl
  set e1 : List Val := [frV] with he1
  have b0 := Det.arg' (P := P) (rest := e1) (vs := [Γ, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
    natList s.x, natList s.y]) (j := 0) rfl
  have b1 := Det.arg' (P := P) (rest := e1) (vs := [Γ, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
    natList s.x, natList s.y]) (j := 1) rfl
  have gl := Det.get' b1 (Det.nat 1) (show [Val.nat I.n, .list ((1 :: s.hs).map encPerm)][1]? =
    some (.list ((1 :: s.hs).map encPerm)) from rfl)
  have v1 := Det.var' (P := P) (env := st :: e1) (i := 1) rfl
  have dM := Det.call (Det.mk2 (Det.mk2 b0 v1) gl) dmap
  have v0' := Det.var' (P := P) (env := st :: e1 ++ [Val.list Ms]) (i := 0) rfl
  have v1' := Det.var' (P := P) (env := st :: e1 ++ [Val.list Ms]) (i := 1) rfl
  have v2' := Det.var' (P := P) (env := st :: e1 ++ [Val.list Ms]) (i := 2) rfl
  have dD := Det.length (Det.get' v1' (Det.nat 2) (show [Val.list [.nat I.p, .nat I.d,
    natList (vsWZ I.d), natList (vsWZ (vsQCs s).length)], vsWVs s.ws', vsWVs (vsQCs s),
    .list ((vsWFrRows I.p s.ws' (vsQCs s)).map VsRow.val)][2]? =
      some (.list ((vsQCs s).map natList)) from rfl))
  rw [ecsl] at dD
  have dres := Det.mk4 v0' v1' dD v2' 
  have dfr' : Det P [st] _ frV _ := dfr
  have dM' : Det P ([st] ++ [frV]) _ (Val.list Ms) _ := dM
  have dres' : Det P ([st] ++ [frV] ++ [Val.list Ms])
      (mk4 (.var 0) (.var 1) (.length (.get (.var 1) (.nat 2))) (.var 2))
      (Val.list [st, frV, .nat (vsQD s), vsFMatsVal (vsQMs s)])
      (20 * (st.wt + frV.wt + (Val.list Ms).wt) + 20 * S + 200) := by
    have w4 := wt_list4_le st frV (.nat (vsQD s)) (Val.list Ms)
    have wD := wt_nat_le (vsQD s)
    have hDS : vsQD s ≤ S := by have := vsQD_le hs; omega
    have hDS' : (Val.nat (vsQD s)).wt ≤ S + 2 := by have := wt_nat_le (vsQD s); omega
    have wcs : (Val.list ((vsQCs s).map natList)).wt < frV.wt := wt_le_wt_list (show
      Val.list ((vsQCs s).map natList) ∈ [Val.list [.nat I.p, .nat I.d, natList (vsWZ I.d),
      natList (vsWZ (vsQCs s).length)], vsWVs s.ws', vsWVs (vsQCs s),
      .list ((vsWFrRows I.p s.ws' (vsQCs s)).map VsRow.val)] by simp [vsWVs])
    have eD : vsQD s = (vsQCs s).length := rfl
    have := dres.mono (c' := 20 * (st.wt + frV.wt + (Val.list Ms).wt) + 20 * S + 200) (by omega)
    rw [← eMs]; exact this
  have dall := Det.letE dfr' (Det.letE dM' dres')
  refine FunDet.intro h0 (dall.mono ?_)
  -- the cost
  have est : st.wt = (Val.list [Γ, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x,
    natList s.y]).wt := rfl
  have eF : frV.wt = (vsWFrVal I.p I.d s.ws' (vsQCs s)).wt := rfl
  have wst : st.wt ≤ 2000 * S ^ 6 := hS.wt_st hs
  have hE : ∀ v ∈ [Γ, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y],
      v.wt < st.wt := fun v hv => wt_le_wt_list hv
  have w2' := hE _ (by simp : vsWVs s.ws' ∈ _)
  have w3' := hE _ (by simp : vsWVs s.ws ∈ _)
  have wΓ' := hS.g
  have eΓ : Γ.wt = (vsQGam I).wt := rfl
  have wE1 : (vsQE I.p I.d (vsQExp I) 1).wt < Γ.wt :=
    wt_le_wt_list (show vsQE I.p I.d (vsQExp I) 1 ∈ [encGroup I.gs, vsQTable I,
      vsQE I.p I.d (vsQExp I) 1] by simp)
  have wz : (natList (List.replicate I.d 0)).wt < (vsQE I.p I.d (vsQExp I) 1).wt :=
    wt_le_wt_list (show natList (List.replicate I.d 0) ∈ [Val.nat I.p, natList (List.replicate I.d 0),
      .nat (vsQExp I), .list ((vsQL (1 : Matrix (Fin I.d) (Fin I.d) (ZMod I.p))ᵀ).map natList)]
      by simp)
  have wp := wt_nat_le I.p
  have wd := wt_nat_le I.d
  have w4 := wt_list4_le (.nat I.p) (.nat I.d) (vsWVs s.ws') (vsWVs s.ws)
  have e5 : (N + 1) ^ 5 = (4 * S + 1) ^ 5 := rfl
  have e3 : (N + 1) ^ 3 = (4 * S + 1) ^ 3 := rfl
  have wc := wt_list2_le Γ frV
  -- the local matrices
  have hL : (1 :: s.hs).length ≤ S ^ 2 := by
    have h1 := hs.hsl
    have h2 : (I.n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hSn 2
    have h3 : I.n ^ 2 + 1 ≤ (I.n + 1) ^ 2 := by nlinarith
    simp only [List.length_cons]; omega
  have wMs := vs_wt_list_le_of Ms (c := 1500 * S ^ 3) (by
    intro v hv
    simp only [hMs, List.mem_map] at hv
    obtain ⟨g, -, rfl⟩ := hv
    have wL := wt_vsWVs_le (N := N) (VsWFit.bnd (vsWLoc_fit (d := I.d) I.prime.pos s.ws' (vsQCs s)
      (vsQL (vsQPhi I g)ᵀ)).1 (by omega) (by omega))
      (by rw [(vsWLoc_fit (d := I.d) I.prime.pos s.ws' (vsQCs s) (vsQL (vsQPhi I g)ᵀ)).2]; omega)
    rw [e3] at wL
    omega)
  have hMl : Ms.length = (1 :: s.hs).length := by simp [hMs]
  rw [hMl] at wMs
  have wMs2 : (1 :: s.hs).length * (2 * (1500 * S ^ 3) + 1) ≤ S ^ 2 * (3001 * S ^ 3) :=
    Nat.mul_le_mul hL (by omega)
  have e23 : S ^ 2 * (3001 * S ^ 3) = 3001 * S ^ 5 := by ring
  have wPs := vs_wt_list_le_of ((1 :: s.hs).map encPerm) (c := 4 * S ^ 2) (by
    intro v hv
    obtain ⟨g, -, rfl⟩ := List.mem_map.mp hv
    exact hS.wt_perm g)
  rw [List.length_map] at wPs
  have wPs2 : (1 :: s.hs).length * (2 * (4 * S ^ 2) + 1) ≤ S ^ 2 * (9 * S ^ 2) :=
    Nat.mul_le_mul hL (by omega)
  have e22 : S ^ 2 * (9 * S ^ 2) = 9 * S ^ 4 := by ring
  have q45 : S ^ 4 ≤ S ^ 5 := hS.pow_le (by omega)
  have q56 : S ^ 5 ≤ S ^ 6 := hS.pow_le (by omega)
  have wA := wt_list2_le (Val.list [Γ, frV]) (Val.list ((1 :: s.hs).map encPerm))
  have hX : (Val.list [Val.list [Γ, frV], Val.list ((1 :: s.hs).map encPerm)]).wt +
      (Val.list Ms).wt + 1 ≤ 400000 * S ^ 6 := by
    rw [e3] at wfr; omega
  have hM1 : mapK * ((1 :: s.hs).length + 1) * ((Val.list [Val.list [Γ, frV],
      Val.list ((1 :: s.hs).map encPerm)]).wt + (Val.list Ms).wt + 1) ≤
      1000 * ((2 * S ^ 2) * (400000 * S ^ 6)) := by
    rw [show mapK = 1000 from rfl, mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) hX)
  have e26 : 2 * S ^ 2 * (400000 * S ^ 6) = 800000 * S ^ 8 := by ring
  have hM2 : (1 :: s.hs).length * (Cφ + 10 ^ 14 * S ^ 5) ≤ S ^ 2 * Cφ + 10 ^ 14 * S ^ 7 := by
    have : (1 :: s.hs).length * (Cφ + 10 ^ 14 * S ^ 5) ≤ S ^ 2 * (Cφ + 10 ^ 14 * S ^ 5) :=
      Nat.mul_le_mul_right _ hL
    have e : S ^ 2 * (Cφ + 10 ^ 14 * S ^ 5) = S ^ 2 * Cφ + 10 ^ 14 * S ^ 7 := by ring
    omega
  have q89 : S ^ 8 ≤ S ^ 9 := hS.pow_le (by omega)
  have q69 : S ^ 6 ≤ S ^ 9 := hS.pow_le (by omega)
  have wfin := wt_list4_le st frV (.nat (vsQD s)) (vsFMatsVal (vsQMs s))
  have eM : (vsFMatsVal (vsQMs s)).wt = (Val.list Ms).wt := by rw [eMs]
  have hDS : vsQD s ≤ S := by have := vsQD_le hs; omega
  have wD := wt_nat_le (vsQD s)
  have eLC : (vsQLCV s).wt = (Val.list [st, frV, .nat (vsQD s), vsFMatsVal (vsQMs s)]).wt := rfl
  rw [e3] at wfr
  simp only [vsQLCCost]
  have hb5 : (N + 1) ^ 5 ≤ 3125 * S ^ 5 := by rw [e5]; exact p5
  have er : mapK * ((1 :: s.hs).length + 1) * ((Val.list [Val.list (Γ :: e1),
      Val.list ((1 :: s.hs).map encPerm)]).wt + (Val.list Ms).wt + 1) =
      mapK * ((1 :: s.hs).length + 1) * ((Val.list [Val.list [Γ, frV],
      Val.list ((1 :: s.hs).map encPerm)]).wt + (Val.list Ms).wt + 1) := rfl
  omega

end GI.Impl
