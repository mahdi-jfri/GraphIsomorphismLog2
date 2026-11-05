module

public import Workspace.Impl.VsQPhi
public import Workspace.Proved.VsWBasic

@[expose] public section

/-!
# Applying `φ(t)⁻¹` to a vector

The driver replaces the target `y` by `φ(t)⁻¹ y` for a coset representative `t`. The program
`vsQAppE` inverts the permutation `t`, asks the matrix program for `vsQE (φ(t⁻¹))` and multiplies
the row vector `y` by the stored rows of `φ(t⁻¹)ᵀ` (`vsQApp_spec`). `vsQApp_vsWV` says that the
result denotes `φ(t)⁻¹ y`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The image `φ(t⁻¹) y`, as the product program computes it. -/
noncomputable def vsQApp (I : VecStabInst) (t : Perm (Fin I.n)) (y : List ℕ) : List ℕ :=
  vsFRowMul I.p y (vsQL (vsQPhi I t⁻¹)ᵀ) (vsWZ I.d)

theorem vsQApp_fit {t : Perm (Fin I.n)} {y : List ℕ} (hy : VsWFit I.p I.d [y]) :
    VsWFit I.p I.d [vsQApp I t y] := by
  have hp := I.prime.pos
  intro u hu
  rw [List.mem_singleton] at hu
  subst hu
  refine ⟨fun z hz => vsFMulAcc_foldl_lt hp y _ (acc := (0, vsWZ I.d)) (fun z hz => ?_) z hz, ?_⟩
  · simp only [vsWZ] at hz
    rw [List.eq_of_mem_replicate hz]; exact hp
  · rw [vsQApp, vsFRowMul, vsFMulAcc_foldl_length]; simp [vsWZ]

theorem vsQApp_vsWV {t : Perm (Fin I.n)} (y : List ℕ) :
    vsWV I.p I.d (vsQApp I t y) = (vsQPhi I t⁻¹).mulVec (vsWV I.p I.d y) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hsq := vsQL_sq (vsQPhi I t⁻¹)ᵀ
  rw [vsQApp, vsWV_img hsq.len (fun r hr => (hsq.rows r hr).2.le)]
  simp only [vsWLin, vsWM, vsFMatrix_vsQL, transpose_transpose, Matrix.toLin'_apply]

/-- On `[Γ, t, y]`: `φ(t⁻¹) y`. -/
def vsQAppE (inv phi row : ℕ) : Expr :=
  .letE (.call phi (mk2 (arg 0) (.call inv (arg 1))))
    (.call row (mk2 (mk3 (.get (.var 1) (.nat 0)) (.get (.var 1) (.nat 3)) (.get (.var 1) (.nat 1)))
      (arg 2)))

/-- The cost of `vsQAppE`. -/
def vsQAppCost (Cφ N : ℕ) : ℕ := Cφ + 10 ^ 8 * (N + 1) ^ 6

set_option maxHeartbeats 2000000 in
/-- **Applying `φ(t)⁻¹`.** -/
theorem vsQApp_spec {P : Program} {f inv phi mm Cφ N : ℕ}
    (hf : P.funs[f]? = some (vsQAppE inv phi (mm + 3))) (hinv : P.HasAt inv (invFuns inv))
    (hmm : P.HasAt mm (vsFMatMulFuns mm))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hsz : VsQSz I.p I.d (vsQExp I) N) (hn : I.n ≤ N) (hΓ : (vsQGam I).wt ≤ N)
    {t : Perm (Fin I.n)} (ht : t ∈ gens I.gs) {y : List ℕ} (hy : VsWFit I.p I.d [y]) :
    FunDet P f (.list [vsQGam I, encPerm t, natList y]) (natList (vsQApp I t y))
      (vsQAppCost Cφ N) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hp := I.prime.pos
  set M := vsQPhi I t⁻¹ with hM
  set a := Val.list [vsQGam I, encPerm t, natList y] with ha
  set E := vsQE I.p I.d (vsQExp I) M with hE
  have hyl := (hy y (by simp)).2
  have hyp := (hy y (by simp)).1
  -- the matrix
  have d0 := Det.arg' (P := P) (vs := [vsQGam I, encPerm t, natList y]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [vsQGam I, encPerm t, natList y]) (rest := []) (j := 1) rfl
  have dinv := Det.call d1 (inv_spec hinv t)
  have dE := Det.call (Det.mk2 d0 dinv) (hphi t⁻¹ (Subgroup.inv_mem _ ht))
  have dR := Det.call (Det.mk2 (Det.mk3
      (Det.get' (Det.var' (P := P) (env := [a, E]) (i := 1) rfl) (Det.nat 0) rfl)
      (Det.get' (Det.var' (P := P) (env := [a, E]) (i := 1) rfl) (Det.nat 3) rfl)
      (Det.get' (Det.var' (P := P) (env := [a, E]) (i := 1) rfl) (Det.nat 1) rfl))
      (Det.arg' (P := P) (vs := [vsQGam I, encPerm t, natList y]) (rest := [E]) (j := 2) rfl))
      (vsFRow_spec (hmm.get (j := 3) (by rw [vsFMatMulFuns_length]; omega)) (hmm.block 4 rfl)
        (hmm.get (j := 7) (by rw [vsFMatMulFuns_length]; omega)) (hmm.block 8 rfl) hp hsz.pN
        (N := N) (a := y) (Bm := vsQL Mᵀ) (z := List.replicate I.d 0) ⟨hyp, by rw [hyl]; exact hsz.dN,
          fun z hz => by rw [List.eq_of_mem_replicate hz]; exact hp, by simp [hsz.dN],
          fun r hr z hz => (((vsQL_sq Mᵀ).rows r hr).1 z hz).le.trans hsz.pN,
          fun r hr => (((vsQL_sq Mᵀ).rows r hr).2).trans_le hsz.dN,
          fun r hr => by simp [((vsQL_sq Mᵀ).rows r hr).2],
          by rw [(vsQL_sq Mᵀ).len, hyl]⟩)
  apply FunDet.intro hf
  refine (Det.letE dE dR).mono ?_
  -- the cost
  have wE := wt_vsQE_le hsz M
  have wt1 := wt_encPerm_le t
  have wt2 := wt_encPerm_le t⁻¹
  have wy : (natList y).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun z hz => (hyp z hz).le.trans hsz.pN) (by rw [hyl]; exact hsz.dN)
  have wL := wt_vsQL_le hsz Mᵀ
  have wz := wt_zero_le hsz
  have wR : (natList (vsFRowMul I.p y (vsQL Mᵀ) (List.replicate I.d 0))).wt ≤ 5 * (N + 1) ^ 2 := by
    apply wt_natList_le_sq
    · intro z hz
      exact (vsFMulAcc_foldl_lt hp _ _ (fun z hz => by
        rw [List.eq_of_mem_replicate hz]; exact hp) z hz).le.trans hsz.pN
    · rw [vsFRowMul, vsFMulAcc_foldl_length]; simp [hsz.dN]
  have hR : vsQApp I t y = vsFRowMul I.p y (vsQL Mᵀ) (List.replicate I.d 0) := rfl
  have wa := wt_list3_le (vsQGam I) (encPerm t) (natList y)
  have w2 := wt_list2_le (vsQGam I) (encPerm t⁻¹)
  have wc := wt_list3_le (.nat I.p) (.list ((vsQL Mᵀ).map natList)) (natList (List.replicate I.d 0))
  have wc2 := wt_list2_le (vsFMatCtx I.p (vsQL Mᵀ) (List.replicate I.d 0)) (natList y)
  have ec : vsFMatCtx I.p (vsQL Mᵀ) (List.replicate I.d 0) =
      .list [.nat I.p, .list ((vsQL Mᵀ).map natList), natList (List.replicate I.d 0)] := rfl
  have wp := wt_nat_le I.p
  have wE' : E.wt ≤ 100 * (N + 1) ^ 3 := wE
  have hn1 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hn4 : (I.n + 1) ^ 4 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hpN := hsz.pN
  simp only [vsQAppCost, invK] at *
  rw [ec] at wc2
  have wE2 := wt_vsQE_le hsz (vsQPhi I t⁻¹)
  have eE : (vsQE I.p I.d (vsQExp I) M).wt = (Val.list [.nat I.p, natList (List.replicate I.d 0),
      .nat (vsQExp I), .list ((vsQL Mᵀ).map natList)]).wt := rfl
  omega

end GI.Impl
