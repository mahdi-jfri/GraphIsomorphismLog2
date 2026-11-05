module

public import Workspace.Impl.VsBFld0
public import Workspace.Impl.VsBSolve
public import Workspace.Impl.VsQChunk
public import Workspace.Impl.VsWProgMC
public import Workspace.Impl.VsWProgComp

@[expose] public section

/-!
# Building `τ` in the case `T = 0`

On `[p, 0_D, Lb, a, u]` the program forms the images `Lb_k m` of `m = a`, solves
`∑ c_k Lb_k m = u`, and returns the carried matrix `∑ c_k Lb_k`
(`vsQE p D 0 (vsWM p D (vsBCombL p D c Lb))`).

* `vsB0TauE`, `vsB0Tau_spec`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

/-- On `[[p, z, a], M]`: the row `a M + z`. -/
def vsB0ImgE (row : ℕ) : Expr :=
  .call row (mk2 (mk3 (.get (arg 0) (.nat 0)) (arg 1) (.get (arg 0) (.nat 1))) (.get (arg 0) (.nat 2)))

/-- On `[c, M]`: the flattened `M`. -/
def vsB0FlatE (fl : ℕ) : Expr := .call fl (arg 1)

/-- On `[p, 0_D, Lb, a, u]`: the carried `τ`. -/
def vsB0TauE (mI sv mF rp row ch : ℕ) : Expr :=
  .letE (.call mI (mk2 (mk3 (arg 0) (arg 1) (arg 3)) (arg 2)))
  (.letE (.call sv (mk3 (arg 0) (.var 1) (arg 4)))
  (.letE (.call mF (mk2 (.nat 0) (arg 2)))
  (.letE (.call rp (mk2 (.arith .mul (.length (arg 1)) (.length (arg 1))) (.nat 0)))
  (.letE (.call row (mk2 (mk3 (arg 0) (.var 3) (.var 4)) (.var 2)))
  (mk4 (arg 0) (arg 1) (.nat 0) (.call ch (mk3 (.length (arg 1)) (.length (arg 1)) (.var 5))))))))

/-- The layout of the `τ` program. -/
structure VsB0TAt (P : Program) (f mI fI mF fF sv rp mm fl ch : ℕ) : Prop where
  f0 : P.funs[f]? = some (vsB0TauE mI sv mF rp (mm + 3) ch)
  mI : P.HasAt mI (mapFuns mI fI)
  fI : P.funs[fI]? = some (vsB0ImgE (mm + 3))
  mF : P.HasAt mF (mapFuns mF fF)
  fF : P.funs[fF]? = some (vsB0FlatE fl)
  sv : P.HasAt sv (vsBSolveFuns sv)
  rp : P.HasAt rp (replicateFuns rp)
  mm : P.HasAt mm (vsFMatMulFuns mm)
  fl : P.HasAt fl (vsWFlatFuns fl)
  ch : P.HasAt ch (vsQChunkFuns ch)

theorem vsQChunk_natList (k m : ℕ) (xs : List ℕ) :
    (vsQChunk (Val.nat 0) k m (xs.map Val.nat)).map Val.list = (vsQChunk 0 k m xs).map natList := by
  simp only [vsQChunk, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, natList, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases xs[i * k + j]? <;> rfl

/-- The images `Lb_k m`. -/
def vsB0Imgs (p D : ℕ) (Lb : List (List (List ℕ))) (a : List ℕ) : List (List ℕ) :=
  Lb.map fun M => vsFRowMul p a M (vsWZ D)

/-- The matrix `τ` as stored rows. -/
def vsB0TauL (p D : ℕ) (Lb : List (List (List ℕ))) (a u : List ℕ) : List (List ℕ) :=
  vsBCombL p D (vsBSolveL p (vsB0Imgs p D Lb a) u) Lb

set_option maxHeartbeats 8000000 in
/-- **Building `τ`.** -/
theorem vsB0Tau_spec {P : Program} {f mI fI mF fF sv rp mm fl ch : ℕ}
    (H : VsB0TAt P f mI fI mF fF sv rp mm fl ch) {p N D : ℕ} (hp : p.Prime) (hpN : p ≤ N)
    (hDD : D * D + 1 ≤ N) {Lb : List (List (List ℕ))} (hsq : ∀ M ∈ Lb, VsWSq p D M)
    (hLl : Lb.length + 1 ≤ N) {a u : List ℕ} (ha : ∀ y ∈ a, y < p) (hal : a.length ≤ N)
    (hDa : D ≤ a.length) (hu : VsWFit p D [u])
    (hsp : vsWV p D u ∈ vsWSp p D (vsB0Imgs p D Lb a)) :
    FunDet P f (.list [.nat p, natList (vsWZ D), vsFMatsVal Lb, natList a, natList u])
      (vsQE p D 0 (vsWM p D (vsB0TauL p D Lb a u))) (10 ^ 12 * (N + 1) ^ 6) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 := hp.pos
  have hDN : D ≤ N := by nlinarith
  have hDDN : D * D ≤ N := by omega
  -- the blocks
  have hr : P.funs[mm + 3]? = some (vsFRowF (mm + 4)) :=
    H.mm.get (j := 3) (by rw [vsFMatMulFuns_length]; omega)
  have hfo : P.HasAt (mm + 4) (foldlFuns (mm + 4) (mm + 7)) := H.mm.block 4 rfl
  have hst : P.funs[mm + 7]? = some (vsFMulStepF (mm + 8)) :=
    H.mm.get (j := 7) (by rw [vsFMatMulFuns_length]; omega)
  have hl : P.HasAt (mm + 8) (vsLinFuns (mm + 8)) := H.mm.block 8 rfl
  set zD := natList (vsWZ D)
  set A := Val.list [.nat p, zD, vsFMatsVal Lb, natList a, natList u]
  set imgs := vsB0Imgs p D Lb a
  -- weights
  have wz : zD.wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wLb := wt_vsWMats_le hpN hDN hsq (by omega)
  have wa := wt_natList_le_sq (B := N) (xs := a) (fun y hy => (ha y hy).le.trans hpN) hal
  have wu := wt_natList_le_sq (B := N) (xs := u) (fun y hy => ((hu u (by simp)).1 y hy).le.trans hpN)
    (by rw [(hu u (by simp)).2]; omega)
  have wp := wt_nat_le p
  have wA : A.wt ≤ 200 * (N + 1) ^ 4 := by
    have := wt_list_le [.nat p, zD, vsFMatsVal Lb, natList a, natList u]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    have q1 : N + 1 ≤ (N + 1) ^ 4 := Nat.le_self_pow (by omega) _
    have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have := Nat.one_le_pow 2 (N + 1) (by omega)
    show (Val.list _).wt ≤ _
    omega
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q45 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q56 : (N + 1) ^ 5 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have ar : ∀ rest k v, [Val.nat p, zD, vsFMatsVal Lb, natList a, natList u][k]? = some v →
      Det P (A :: rest) (arg k) v (2 * A.wt + k + 5) := fun rest k v hv =>
    Det.arg' (vs := [Val.nat p, zD, vsFMatsVal Lb, natList a, natList u]) (rest := rest) hv
  -- step 1: the images
  have himg : ∀ M ∈ Lb, FunDet P fI (.list [.list [.nat p, zD, natList a], vsWVs M])
      (natList (vsFRowMul p a M (vsWZ D))) (5 * 10 ^ 6 * (N + 1) ^ 4) := by
    intro M hM
    have hMs := hsq M hM
    set c := Val.list [.nat p, zD, natList a]
    have g0 := Det.arg' (P := P) (rest := []) (vs := [c, vsWVs M]) (j := 0) rfl
    have g1 := Det.arg' (P := P) (rest := []) (vs := [c, vsWVs M]) (j := 1) rfl
    have dc := fun k v (hv : [Val.nat p, zD, natList a][k]? = some v) => Det.get' g0 (Det.nat k) hv
    have drow := Det.call (Det.mk2 (Det.mk3 (dc 0 _ rfl) g1 (dc 1 _ rfl)) (dc 2 _ rfl))
      (vsFRow_spec hr hfo hst hl hp0 hpN (N := N) (a := a) (z := vsWZ D) (Bm := M)
        ⟨ha, hal, fun y hy => by simp [vsWZ] at hy; omega, by simp [vsWZ]; omega,
          fun r hr y hy => ((hMs.1 r hr).1 y hy).le.trans hpN,
          fun r hr => (hMs.1 r hr).2.le.trans hDN,
          fun r hr => by simp [vsWZ, (hMs.1 r hr).2], by rw [hMs.2]; exact hDa⟩)
    refine FunDet.intro H.fI (drow.mono ?_)
    have wM := wt_vsWVs_le (VsWFit.bnd hMs.1 hpN hDN) (by rw [hMs.2]; omega)
    have wc := wt_list3_le (.nat p) zD (natList a)
    have w2 := wt_list2_le c (vsWVs M)
    have w3 := wt_list3_le (.nat p) (vsWVs M) zD
    have w2' := wt_list2_le (.list [.nat p, vsWVs M, zD]) (natList a)
    have hfit := vsFRowMul_fit (d := D) hp0 a M
    have wo := wt_natList_le_sq (B := N) (xs := vsFRowMul p a M (vsWZ D))
      (fun y hy => ((hfit _ (by simp)).1 y hy).le.trans hpN) (by rw [(hfit _ (by simp)).2]; omega)
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2
    have ec : (vsFMatCtx p M (vsWZ D)).wt = (Val.list [.nat p, vsWVs M, zD]).wt := rfl
    have ec' : c.wt = (Val.list [.nat p, zD, natList a]).wt := rfl
    omega
  have dI := Det.call (Det.mk2 (Det.mk3 (ar [] 0 _ rfl) (ar [] 1 _ rfl) (ar [] 3 _ rfl)) (ar [] 2 _ rfl))
    (vsQ_map H.mI Lb vsWVs (fun M => natList (vsFRowMul p a M (vsWZ D))) vsWVs_injective
      (c := .list [.nat p, zD, natList a]) himg)
  have eI : Val.list (Lb.map fun M => natList (vsFRowMul p a M (vsWZ D))) = vsWVs imgs := by
    simp [vsWVs, imgs, vsB0Imgs, List.map_map, Function.comp_def]
  rw [eI] at dI
  have hIfit : VsWFit p D imgs := fun r hr => by
    obtain ⟨M, -, rfl⟩ := List.mem_map.mp hr
    exact vsFRowMul_fit hp0 a M _ (List.mem_singleton_self _)
  have hIl : imgs.length = Lb.length := List.length_map _
  have wI := wt_vsWVs_le (VsWFit.bnd hIfit hpN hDN) (by omega)
  -- step 2: the coefficients
  set c := vsBSolveL p imgs u
  have hc := vsBSolve_comb hp hIfit hu hsp
  have dS := Det.call (Det.mk3 (ar [vsWVs imgs] 0 _ rfl) (Det.var' (P := P) (env := [A, vsWVs imgs]) (i := 1) rfl)
    (ar [vsWVs imgs] 4 _ rfl)) (vsBSolve_spec H.sv hp hpN hDN hIfit (by omega) hu hsp)
  have wc := wt_natList_le_sq (B := N) (xs := c) (fun y hy => (hc.1 y hy).le.trans hpN)
    (by rw [hc.2.1]; omega)
  -- step 3: the flattened matrices
  have hflat : ∀ M ∈ Lb, FunDet P fF (.list [.nat 0, vsWVs M]) (natList M.flatten)
      (2 * 10 ^ 6 * (N + 1) ^ 4) := by
    intro M hM
    have g1 := Det.arg' (P := P) (rest := []) (vs := [.nat 0, vsWVs M]) (j := 1) rfl
    refine FunDet.intro H.fF ((Det.call g1 (vsWFlat_spec H.fl hpN hDDN (hsq M hM))).mono ?_)
    have wM := wt_vsWVs_le (VsWFit.bnd (hsq M hM).1 hpN hDN) (by rw [(hsq M hM).2]; omega)
    have w2 := wt_list2_le (.nat 0) (vsWVs M)
    have := wt_nat_le 0
    have hfl : ∀ y ∈ M.flatten, y ≤ N := fun y hy => by
      obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
      exact ((hsq M hM).1 r hr).1 y hy |>.le.trans hpN
    have hfll : M.flatten.length ≤ N := by
      rw [List.length_flatten]
      have : (M.map List.length).sum = D * D := by
        rw [List.map_congr_left (g := fun _ => D) fun r hr => ((hsq M hM).1 r hr).2]
        simp [(hsq M hM).2]
      omega
    have wo := wt_natList_le_sq hfl hfll
    omega
  set E2 := [A, vsWVs imgs, natList c]
  have dF := Det.call (Det.mk2 (Det.nat (P := P) (env := E2) 0) (ar [vsWVs imgs, natList c] 2 _ rfl))
    (vsQ_map H.mF Lb vsWVs (fun M => natList M.flatten) vsWVs_injective (c := .nat 0) hflat)
  set fls := Lb.map List.flatten
  have eF : Val.list (Lb.map fun M => natList M.flatten) = vsWVs fls := by
    simp [vsWVs, fls, List.map_map, Function.comp_def]
  rw [eF] at dF
  have hFfit : VsWFit p (D * D) fls := fun r hr => by
    obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hr
    refine ⟨fun y hy => ?_, ?_⟩
    · obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
      exact ((hsq M hM).1 r hr).1 y hy
    · rw [List.length_flatten]
      rw [List.map_congr_left (g := fun _ => D) fun r hr => ((hsq M hM).1 r hr).2]
      simp [(hsq M hM).2]
  have hFl : fls.length = Lb.length := List.length_map _
  have wF := wt_vsWVs_le (VsWFit.bnd hFfit hpN hDDN) (by omega)
  -- step 4: the zero vector of length `D²`
  set E3 := [A, vsWVs imgs, natList c, vsWVs fls]
  have dzl := Det.length (ar [vsWVs imgs, natList c, vsWVs fls] 1 zD rfl)
  have dDD := Det.arith (op := .mul) dzl dzl
  simp only [List.length_map, vsWZ, List.length_replicate] at dDD
  have dZ := vsWZero_det H.rp dDD (N := N) (by simp [GI.Machine.BinOp.eval]; omega)
  simp only [GI.Machine.BinOp.eval] at dZ
  -- step 5: the combination
  set E4 := [A, vsWVs imgs, natList c, vsWVs fls, natList (vsWZ (D * D))]
  have dR := Det.call (Det.mk2 (Det.mk3 (ar [vsWVs imgs, natList c, vsWVs fls, natList (vsWZ (D * D))] 0 _ rfl)
      (Det.var' (P := P) (env := E4) (i := 3) rfl) (Det.var' (P := P) (env := E4) (i := 4) rfl))
      (Det.var' (P := P) (env := E4) (i := 2) rfl))
    (vsFRow_spec hr hfo hst hl hp0 hpN (N := N) (a := c) (z := vsWZ (D * D)) (Bm := fls)
      ⟨hc.1, by rw [hc.2.1]; omega, fun y hy => by simp [vsWZ] at hy; omega, by simp [vsWZ]; omega,
        fun r hr y hy => ((hFfit r hr).1 y hy).le.trans hpN, fun r hr => (hFfit r hr).2.le.trans hDDN,
        fun r hr => by simp [vsWZ, (hFfit r hr).2], by rw [hc.2.1, hFl, hIl]; omega⟩)
  set tf := vsFRowMul p c fls (vsWZ (D * D))
  have htf : VsWFit p (D * D) [tf] := vsFRowMul_fit (d := D * D) hp0 c fls
  have htfl : tf.length = D * D := (htf _ (by simp)).2
  have wtf := wt_natList_le_sq (B := N) (xs := tf) (fun y hy => ((htf _ (by simp)).1 y hy).le.trans hpN)
    (by omega)
  -- step 6: cutting into rows
  set E5 := [A, vsWVs imgs, natList c, vsWVs fls, natList (vsWZ (D * D)), natList tf]
  have dzl5 := Det.length (ar [vsWVs imgs, natList c, vsWVs fls, natList (vsWZ (D * D)), natList tf]
    1 zD rfl)
  simp only [List.length_map, vsWZ, List.length_replicate] at dzl5
  have dC := Det.call (Det.mk3 dzl5 dzl5 (Det.var' (P := P) (env := E5) (i := 5) rfl))
    (vsQChunk_spec H.ch (k := D) (m := D) (N := N) (vs := tf.map Val.nat) (W := 5 * (N + 1) ^ 2)
      (by simp [htfl]) hDN hDN wtf)
  rw [vsQChunk_natList] at dC
  have dout := Det.mk4 (ar [vsWVs imgs, natList c, vsWVs fls, natList (vsWZ (D * D)), natList tf]
    0 _ rfl) (ar [vsWVs imgs, natList c, vsWVs fls, natList (vsWZ (D * D)), natList tf] 1 _ rfl)
    (Det.nat 0) dC
  have eout : Val.list [.nat p, zD, .nat 0, .list ((vsQChunk 0 D D tf).map natList)] =
      vsQE p D 0 (vsWM p D (vsB0TauL p D Lb a u)) := by
    have hsqT := vsBComb_sq hp0 D c Lb
    have e1 : vsQL (vsWM p D (vsB0TauL p D Lb a u))ᵀ = vsB0TauL p D Lb a u := by
      rw [vsWM, transpose_transpose]
      exact (vsQL_of_sq (vsWSq_vsFSq hsqT)).symm
    rw [vsQE, e1]
    rfl
  rw [eout] at dout
  have dall := Det.letE dI (Det.letE dS (Det.letE dF (Det.letE dZ (Det.letE dR dout))))
  refine FunDet.intro H.f0 (dall.mono ?_)
  -- the cost
  have hsqT := vsBComb_sq hp0 D c Lb
  have wT := wt_vsWVs_le (VsWFit.bnd hsqT.1 hpN hDN) (by rw [hsqT.2]; omega)
  have eT : (Val.list ((vsQChunk 0 D D tf).map natList)).wt = (vsWVs (vsB0TauL p D Lb a u)).wt := rfl
  have wE := wt_list4_le (.nat p) zD (.nat 0) (.list ((vsQChunk 0 D D tf).map natList))
  have eE : (vsQE p D 0 (vsWM p D (vsB0TauL p D Lb a u))).wt =
      (Val.list [.nat p, zD, .nat 0, .list ((vsQChunk 0 D D tf).map natList)]).wt := by rw [eout]
  have wZ : (natList (vsWZ (D * D))).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have k1 := vsW_mapCost (N := N) (n := Lb.length) (B := 5 * 10 ^ 6 * (N + 1) ^ 4) (c := 5 * 10 ^ 6) (k := 4)
    (W := (Val.list [.list [.nat p, zD, natList a], .list (Lb.map vsWVs)]).wt +
      (Val.list (Lb.map fun M => natList (vsFRowMul p a M (vsWZ D)))).wt) (by omega) le_rfl (by
      rw [eI]
      have w1 := wt_list3_le (.nat p) zD (natList a)
      have w2 := wt_list2_le (.list [.nat p, zD, natList a]) (.list (Lb.map vsWVs))
      have eL : (vsFMatsVal Lb).wt = (Val.list (Lb.map vsWVs)).wt := rfl
      omega)
  have k2 := vsW_mapCost (N := N) (n := Lb.length) (B := 2 * 10 ^ 6 * (N + 1) ^ 4) (c := 2 * 10 ^ 6) (k := 4)
    (W := (Val.list [.nat 0, .list (Lb.map vsWVs)]).wt +
      (Val.list (Lb.map fun M => natList M.flatten)).wt) (by omega) le_rfl (by
      rw [eF]
      have w2 := wt_list2_le (.nat 0) (.list (Lb.map vsWVs))
      have eL : (vsFMatsVal Lb).wt = (Val.list (Lb.map vsWVs)).wt := rfl
      have := wt_nat_le 0
      omega)
  rw [eI] at k1
  rw [eF] at k2
  have e5 : (N + 1) ^ (4 + 1) = (N + 1) ^ 5 := rfl
  rw [e5] at k1 k2
  have e6 : 10 ^ 8 * (N + 1) ^ 4 * (5 * (N + 1) ^ 2 + (N + 1) ^ 2) = 6 * 10 ^ 8 * (N + 1) ^ 6 := by ring
  have ex1 : (natList (vsBSolveL p imgs u)).wt = (natList c).wt := rfl
  have ey1 : (Val.list [Val.nat D, Val.nat D, natList tf]).wt =
    (Val.list [Val.nat D, Val.nat D, Val.list (List.map Val.nat tf)]).wt := rfl
  have ex2 : (vsWVs (vsBCombL p D c Lb)).wt = (vsWVs (vsB0TauL p D Lb a u)).wt := rfl
  have wsv := wt_list3_le (.nat p) (vsWVs imgs) (natList u)
  have wrc := wt_list3_le (.nat p) (vsWVs fls) (natList (vsWZ (D * D)))
  have wr2 := wt_list2_le (.list [.nat p, vsWVs fls, natList (vsWZ (D * D))]) (natList c)
  have ech : (vsFMatCtx p fls (vsWZ (D * D))).wt = (Val.list [.nat p, vsWVs fls, natList (vsWZ (D * D))]).wt := rfl
  have wch := wt_list3_le (.nat D) (.nat D) (.list (tf.map Val.nat))
  have ech2 : (Val.list (tf.map Val.nat)).wt = (natList tf).wt := rfl
  have wi1 := wt_list3_le (.nat p) zD (natList a)
  have wi2 := wt_list2_le (.list [.nat p, zD, natList a]) (vsFMatsVal Lb)
  have wf2 := wt_list2_le (.nat 0) (vsFMatsVal Lb)
  have wdd := wt_nat_le (D * D); have wd := wt_nat_le D
  have w2dd := wt_list2_le (.nat (D * D)) (.nat 0)
  have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3; have := wt_nat_le 4
  have hq6 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have eLb : (vsFMatsVal Lb).wt = (Val.list (Lb.map vsWVs)).wt := rfl
  clear_value zD A imgs c fls tf
  omega

end GI.Impl
