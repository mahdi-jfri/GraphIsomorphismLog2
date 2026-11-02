import Workspace.Impl.VsWProgBas

/-!
# Images and cuts as programs

* `vsWZero_det`: the zero vector `vsWZ d`, built by `replicate`.
* `vsWImgFuns b` (20 functions), `vsWImg_spec`: on `[p, d, vsWVs A, vsWVs us]` the images
  `vsWVs (vsWImg p d A us)`. Meaning: `GI.Proved.vsWImg_span`.
* `vsWCutFuns b` (77 functions), `vsWCut_spec`: on `[p, d, vsWVs us, vsWVs A]` the value
  `vsWVs (vsWCut p d us A)`. Meaning: `GI.Proved.vsWCut_span`.
-/

namespace GI.Impl

open GI.Lang GI.Cited

/-- **The zero vector**, by `replicate` at `rep`. -/
theorem vsWZero_det {P : Program} {rep : ℕ} (h : P.HasAt rep (replicateFuns rep)) {env : List Val}
    {e : Expr} {d c N : ℕ} (hd : Det P env e (.nat d) c) (hdN : d ≤ N) :
    Det P env (.call rep (mk2 e (.nat 0))) (natList (vsWZ d)) (c + 10 ^ 5 * (N + 1) ^ 3) := by
  have e1 : natList (vsWZ d) = .list (List.replicate d (.nat 0)) := by
    simp [vsWZ, natList, List.map_replicate]
  have wz : (natList (vsWZ d)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  rw [e1] at wz ⊢
  have w2 := wt_list2_le (.nat d) (.nat 0)
  have wd := wt_nat_le d
  have w0 := wt_nat_le 0
  have hK : loopModK = 1000 := rfl
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have k : loopModK * (d + 1) * ((Val.list [.nat d, .nat 0]).wt + d +
      (Val.list (List.replicate d (Val.nat 0))).wt + 1) ≤ 1000 * (N + 1) * (20 * (N + 1) ^ 2) := by
    rw [hK]; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e2 : 1000 * (N + 1) * (20 * (N + 1) ^ 2) = 20000 * (N + 1) ^ 3 := by ring
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  refine (Det.call (Det.mk2 hd (Det.nat 0)) ((replicate_spec h d (.nat 0)).mono
    fun w c hw => ⟨hw.1, hw.2.trans (hw.1 ▸ k)⟩)).mono ?_
  omega

/-! ### Images -/

/-- The images, on `[p, d, A, us]`. -/
def vsWImgF (rep mm : ℕ) : Expr :=
  .call mm (mk2 (mk3 (arg 0) (arg 2) (.call rep (mk2 (arg 1) (.nat 0)))) (arg 3))

/-- The images program at base `b` (20 functions). -/
def vsWImgFuns (b : ℕ) : List Expr :=
  [vsWImgF (b + 1) (b + 4)] ++ replicateFuns (b + 1) ++ vsFMatMulFuns (b + 4)

theorem vsWImgFuns_length (b : ℕ) : (vsWImgFuns b).length = 20 := rfl

/-- The images are vectors of length `d` with entries below `p`. -/
theorem vsWImg_fit' {p d : ℕ} (hp : 0 < p) (A us : List (List ℕ)) :
    GI.Proved.VsWFit p d (vsWImg p d A us) := by
  intro x hx
  simp only [vsWImg, List.mem_map] at hx
  obtain ⟨u, -, rfl⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [vsFRowMul]
    exact vsFMulAcc_foldl_lt hp _ _ (fun y hy => by simp [vsWZ] at hy; omega)
  · rw [vsFRowMul, vsFMulAcc_foldl_length]
    simp [vsWZ]

/-- **The images program.** `A` has rows of length `d`, and the vectors `us` have length
`A.length`. -/
theorem vsWImg_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWImgFuns b)) {p N d : ℕ}
    (hp : 0 < p) (hpN : p ≤ N) (hdN : d ≤ N) {A us : List (List ℕ)}
    (hA : GI.Proved.VsWFit p d A) (hAl : A.length ≤ N) (hus : GI.Proved.VsWFit p A.length us)
    (hl : us.length ≤ N) :
    FunDet P b (.list [.nat p, .nat d, vsWVs A, vsWVs us]) (vsWVs (vsWImg p d A us))
      (6 * 10 ^ 6 * (N + 1) ^ 5) := by
  have h0 : P.funs[b]? = some (vsWImgF (b + 1) (b + 4)) := h.get (j := 0) (by simp [vsWImgFuns])
  have hr : P.HasAt (b + 1) (replicateFuns (b + 1)) := h.block 1 rfl
  have hm : P.HasAt (b + 4) (vsFMatMulFuns (b + 4)) := h.block 4 rfl
  set X := Val.list [.nat p, .nat d, vsWVs A, vsWVs us]
  have a0 := Det.arg' (P := P) (rest := []) (vs := [Val.nat p, .nat d, vsWVs A, vsWVs us]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [Val.nat p, .nat d, vsWVs A, vsWVs us]) (j := 1) rfl
  have a2 : Det P [X] (arg 2) (.list (A.map natList)) _ :=
    Det.arg' (P := P) (rest := []) (vs := [Val.nat p, .nat d, vsWVs A, vsWVs us]) (j := 2) rfl
  have a3 : Det P [X] (arg 3) (.list (us.map natList)) _ :=
    Det.arg' (P := P) (rest := []) (vs := [Val.nat p, .nat d, vsWVs A, vsWVs us]) (j := 3) rfl
  have dz := vsWZero_det hr a1 hdN
  have dctx := Det.mk3 a0 a2 dz
  have HB : VsFMatFits p N A (vsWZ d) :=
    ⟨fun y hy => by simp [vsWZ] at hy; omega, by simp [vsWZ]; omega,
      fun r hr y hy => ((hA r hr).1 y hy).le.trans hpN, fun r hr => (hA r hr).2.le.trans hdN,
      fun r hr => by simp [vsWZ, (hA r hr).2], hAl⟩
  have HA : ∀ a ∈ us, (∀ y ∈ a, y < p) ∧ a.length ≤ N ∧ A.length ≤ a.length :=
    fun a ha => ⟨(hus a ha).1, (hus a ha).2 ▸ hAl, (hus a ha).2.ge⟩
  have dmm := Det.call (Det.mk2 dctx a3) (vsFMatMul_spec hm hp hpN HB HA hl)
  have e1 : Val.list (us.map fun a => natList (vsFRowMul p a A (vsWZ d))) =
      vsWVs (vsWImg p d A us) := by simp [vsWVs, vsWImg]
  rw [e1] at dmm
  refine FunDet.intro h0 (dmm.mono ?_)
  have wA := wt_vsWVs_le (VsWFit.bnd hA hpN hdN) (show A.length ≤ N + 1 by omega)
  have wus := wt_vsWVs_le (N := N) (us := us)
    (fun u hu => ⟨fun y hy => ((hus u hu).1 y hy).le.trans hpN, (hus u hu).2.le.trans hAl⟩)
    (show us.length ≤ N + 1 by omega)
  have wI := wt_vsWVs_le (VsWFit.bnd (vsWImg_fit' (d := d) hp A us) hpN hdN)
    (show (vsWImg p d A us).length ≤ N + 1 by simp [vsWImg]; omega)
  have wz : (natList (vsWZ d)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wp := wt_nat_le p
  have wd := wt_nat_le d
  have w0 := wt_nat_le 0
  have wX := wt_list4_le (.nat p) (.nat d) (vsWVs A) (vsWVs us)
  have w3 := wt_list3_le (.nat p) (.list (A.map natList)) (natList (vsWZ d))
  have w2 := wt_list2_le (Val.list [.nat p, .list (A.map natList), natList (vsWZ d)])
    (.list (us.map natList))
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have eX : X.wt = (Val.list [.nat p, .nat d, vsWVs A, vsWVs us]).wt := rfl
  have eA : (vsWVs A).wt = (Val.list (A.map natList)).wt := rfl
  have eU : (vsWVs us).wt = (Val.list (us.map natList)).wt := rfl
  have eC : (vsFMatCtx p A (vsWZ d)) = Val.list [.nat p, .list (A.map natList), natList (vsWZ d)] :=
    rfl
  omega

/-! ### Cuts -/

theorem vsWKer_length_le {p N d : ℕ} (hp1 : 1 < p) (hpN : p ≤ N) (hdN : d ≤ N)
    {us : List (List ℕ)} (hus : GI.Proved.VsWFit p d us) (hl : us.length ≤ N) :
    (vsWKer p us).length ≤ us.length := by
  have hok := GI.Proved.vsWUnitPairs_ok hus hp1
  have hL : ∀ xt ∈ vsUnitPairs us.length us,
      VsPairFits p N xt ∧ xt.1.length = d ∧ xt.2.length = us.length := fun xt hxt => by
    obtain ⟨h1, h2, h3, h4⟩ := hok xt hxt
    exact ⟨⟨h1, h2, by omega, by omega⟩, h3, h4⟩
  have := (vsInsertAll_fits (by omega) hpN hL).nrels
  simpa [vsUnitPairs] using this

/-- The cut, on `[p, d, us, A]`: the images of the relations among the images of `us`. -/
def vsWCutF (img ker : ℕ) : Expr :=
  .call img (mk4 (arg 0) (arg 1) (arg 2)
    (.call ker (mk2 (arg 0) (.call img (mk4 (arg 0) (arg 1) (arg 3) (arg 2))))))

/-- The cut program at base `b` (57 functions). -/
def vsWCutFuns (b : ℕ) : List Expr :=
  [vsWCutF (b + 1) (b + 21)] ++ vsWImgFuns (b + 1) ++ vsWKerFuns (b + 21)

theorem vsWCutFuns_length (b : ℕ) : (vsWCutFuns b).length = 57 := rfl

/-- **The cut program.** -/
theorem vsWCut_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWCutFuns b)) {p N d : ℕ}
    (hp1 : 1 < p) (hpN : p ≤ N) (hdN : d ≤ N) {us A : List (List ℕ)}
    (hus : GI.Proved.VsWFit p d us) (hl : us.length ≤ N) (hA : GI.Proved.VsWSq p d A) :
    FunDet P b (.list [.nat p, .nat d, vsWVs us, vsWVs A]) (vsWVs (vsWCut p d us A))
      (10 ^ 8 * (N + 1) ^ 5) := by
  have h0 : P.funs[b]? = some (vsWCutF (b + 1) (b + 21)) := h.get (j := 0) (by simp [vsWCutFuns])
  have hi : P.HasAt (b + 1) (vsWImgFuns (b + 1)) := h.block 1 rfl
  have hk : P.HasAt (b + 21) (vsWKerFuns (b + 21)) := h.block 21 rfl
  set X := Val.list [.nat p, .nat d, vsWVs us, vsWVs A]
  have a0 := Det.arg' (P := P) (rest := []) (vs := [Val.nat p, .nat d, vsWVs us, vsWVs A]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [Val.nat p, .nat d, vsWVs us, vsWVs A]) (j := 1) rfl
  have a2 := Det.arg' (P := P) (rest := []) (vs := [Val.nat p, .nat d, vsWVs us, vsWVs A]) (j := 2) rfl
  have a3 := Det.arg' (P := P) (rest := []) (vs := [Val.nat p, .nat d, vsWVs us, vsWVs A]) (j := 3) rfl
  have hAl : A.length = d := hA.2
  have hus' : GI.Proved.VsWFit p A.length us := by rw [hAl]; exact hus
  have d1 := Det.call (Det.mk4 a0 a1 a3 a2) (vsWImg_spec hi (by omega) hpN hdN hA.1 (by rw [hAl]; exact hdN) hus' hl)
  have hIf := vsWImg_fit' (p := p) (d := d) (by omega) A us
  have hIl : (vsWImg p d A us).length ≤ N := by simp [vsWImg]; omega
  have d2 := Det.call (Det.mk2 a0 d1) (vsWKer_spec hk hp1 hpN hdN hIf hIl)
  have hKf := GI.Proved.vsWKer_fit hp1 hIf
  have hKl : (vsWImg p d A us).length = us.length := by simp [vsWImg]
  rw [hKl] at hKf
  have hKn : (vsWKer p (vsWImg p d A us)).length ≤ N :=
    (vsWKer_length_le hp1 hpN hdN hIf hIl).trans hIl
  have d3 := Det.call (Det.mk4 a0 a1 a2 d2) (vsWImg_spec hi (by omega) hpN hdN hus hl hKf hKn)
  have e1 : vsWImg p d us (vsWKer p (vsWImg p d A us)) = vsWCut p d us A := rfl
  rw [e1] at d3
  refine FunDet.intro h0 (d3.mono ?_)
  have wus := wt_vsWVs_le (VsWFit.bnd hus hpN hdN) (show us.length ≤ N + 1 by omega)
  have wA := wt_vsWVs_le (VsWFit.bnd hA.1 hpN hdN) (show A.length ≤ N + 1 by omega)
  have wI := wt_vsWVs_le (VsWFit.bnd hIf hpN hdN) (show (vsWImg p d A us).length ≤ N + 1 by omega)
  have wK := wt_vsWVs_le (VsWFit.bnd hKf hpN hl) (show (vsWKer p (vsWImg p d A us)).length ≤ N + 1 by
    omega)
  have hCf := GI.Proved.vsWCut_fit (p := p) (d := d) (us := us) (A := A) (by omega)
  have wC := wt_vsWVs_le (VsWFit.bnd hCf hpN hdN) (show (vsWCut p d us A).length ≤ N + 1 by
    simp only [vsWCut, List.length_map]; omega)
  have wp := wt_nat_le p
  have wd := wt_nat_le d
  have wX := wt_list4_le (.nat p) (.nat d) (vsWVs us) (vsWVs A)
  have wX2 := wt_list4_le (.nat p) (.nat d) (vsWVs A) (vsWVs us)
  have wX3 := wt_list4_le (.nat p) (.nat d) (vsWVs us) (vsWVs (vsWKer p (vsWImg p d A us)))
  have w2 := wt_list2_le (.nat p) (vsWVs (vsWImg p d A us))
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by omega) _
  omega

end GI.Impl
