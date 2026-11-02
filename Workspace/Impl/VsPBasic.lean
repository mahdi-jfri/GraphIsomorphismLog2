import Workspace.Impl.VsQApp
import Workspace.Impl.VsWProgCo
import Workspace.Impl.VsWProgMC

/-!
# Basic programs on local matrices

Local matrices are stored as in `Proved/VsWBasic.lean`: the stored list `A` of a local matrix `M` holds the
rows of `Mᵀ` (`GI.Proved.vsWM`).

* `vsPLocE`, `vsPLoc_spec`: on `[Γ, fr, g]` the stored local matrix
  `vsPLocL I ws' cs g = vsWLoc p d ws' cs (vsQL (φ g)ᵀ)` of a permutation `g ∈ G`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The stored local matrix of `g`. -/
noncomputable def vsPLocL (I : VecStabInst) (ws' cs : List (List ℕ)) (g : Perm (Fin I.n)) :
    List (List ℕ) :=
  vsWLoc I.p I.d ws' cs (vsQL (vsQPhi I g)ᵀ)

theorem vsPLocL_sq {ws' cs : List (List ℕ)} (g : Perm (Fin I.n)) :
    VsWSq I.p cs.length (vsPLocL I ws' cs g) :=
  vsWLoc_fit I.prime.pos ws' cs _

/-- On `[Γ, fr, g]`: the stored local matrix of `g`. -/
def vsPLocE (phi loc : ℕ) : Expr :=
  .letE (.call phi (mk2 (arg 0) (arg 2))) (.call loc (mk2 (arg 1) (.get (.var 1) (.nat 3))))

/-- The cost of `vsPLocE`. -/
def vsPLocCost (Cφ N : ℕ) : ℕ := Cφ + 10 ^ 11 * (N + 1) ^ 5

set_option maxHeartbeats 1000000 in
/-- **The local matrix of a permutation.** -/
theorem vsPLoc_spec {P : Program} {f phi loc Cφ N : ℕ}
    (hf : P.funs[f]? = some (vsPLocE phi loc)) (hloc : P.HasAt loc (vsWLocFuns loc))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hsz : VsQSz I.p I.d (vsQExp I) N) (hΓ : (vsQGam I).wt ≤ N) (hn : I.n ≤ N)
    {ws' cs : List (List ℕ)} (H : VsWFrOK I.p N I.d ws' cs)
    {g : Perm (Fin I.n)} (hg : g ∈ gens I.gs) :
    FunDet P f (.list [vsQGam I, vsWFrVal I.p I.d ws' cs, encPerm g])
      (vsWVs (vsPLocL I ws' cs g)) (vsPLocCost Cφ N) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  set a := Val.list [vsQGam I, vsWFrVal I.p I.d ws' cs, encPerm g] with ha
  have d0 := Det.arg' (P := P) (vs := [vsQGam I, vsWFrVal I.p I.d ws' cs, encPerm g]) (rest := [])
    (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [vsQGam I, vsWFrVal I.p I.d ws' cs, encPerm g]) (rest := [vsQE I.p I.d (vsQExp I) (vsQPhi I g)])
    (j := 1) rfl
  have d2 := Det.arg' (P := P) (vs := [vsQGam I, vsWFrVal I.p I.d ws' cs, encPerm g]) (rest := [])
    (j := 2) rfl
  have dE := Det.call (Det.mk2 d0 d2) (hphi g hg)
  have hsq := vsQL_sq (vsQPhi I g)ᵀ
  have hA : VsWSq I.p I.d (vsQL (vsQPhi I g)ᵀ) := ⟨fun r hr => hsq.rows r hr, hsq.len⟩
  have dA := Det.get' (Det.var' (P := P) (env := [a, vsQE I.p I.d (vsQExp I) (vsQPhi I g)]) (i := 1) rfl) (Det.nat 3)
    (show [Val.nat I.p, natList (List.replicate I.d 0), .nat (vsQExp I),
      .list ((vsQL (vsQPhi I g)ᵀ).map natList)][3]? = some (vsWVs (vsQL (vsQPhi I g)ᵀ)) from rfl)
  have dL := Det.call (Det.mk2 d1 dA) (vsWLoc_spec hloc H hA)
  apply FunDet.intro hf
  refine (Det.letE dE dL).mono ?_
  -- the cost
  have hfr := wt_vsWFrVal_le H
  have wE := wt_vsQE_le hsz (vsQPhi I g)
  have wg := wt_encPerm_le g
  have wL := wt_vsQL_le hsz (vsQPhi I g)ᵀ
  have hLf := vsPLocL_sq (I := I) (ws' := ws') (cs := cs) g
  have wR := wt_vsWVs_le (N := N) (us := vsPLocL I ws' cs g)
    (VsWFit.bnd hLf.1 H.hpN (by have := H.hl; omega)) (by rw [hLf.2]; have := H.hl; omega)
  have wa := wt_list3_le (vsQGam I) (vsWFrVal I.p I.d ws' cs) (encPerm g)
  have w2 := wt_list2_le (vsQGam I) (encPerm g)
  have w3 := wt_list2_le (vsWFrVal I.p I.d ws' cs) (vsWVs (vsQL (vsQPhi I g)ᵀ))
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have eA : (vsWVs (vsQL (vsQPhi I g)ᵀ)).wt = (Val.list ((vsQL (vsQPhi I g)ᵀ).map natList)).wt := rfl
  have eQ : (Val.list [Val.nat I.p, natList (List.replicate I.d 0), Val.nat (vsQExp I),
      Val.list (List.map natList (vsQL (vsQPhi I g)ᵀ))]).wt =
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)).wt := rfl
  simp only [vsPLocCost, vsPLocL] at *
  omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved

/-! ### Equality of stored matrices -/

theorem vsP_flatten_inj {D : ℕ} {A B : List (List ℕ)} (hA : ∀ r ∈ A, r.length = D)
    (hB : ∀ r ∈ B, r.length = D) (hl : A.length = B.length) (h : A.flatten = B.flatten) :
    A = B := by
  induction A generalizing B with
  | nil => cases B with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons a A ih =>
    cases B with
    | nil => simp at hl
    | cons b B =>
      simp only [List.flatten_cons] at h
      have ha := hA a (by simp)
      have hb := hB b (by simp)
      have e1 : a = b := by
        have := congrArg (List.take D) h
        rwa [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega),
          List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at this
      subst e1
      rw [ih (fun r hr => hA r (by simp [hr])) (fun r hr => hB r (by simp [hr]))
        (by simpa using hl) (List.append_cancel_left h)]

/-- On `[A, B]` (stored matrices): `1` if they are equal, else `0`. -/
def vsPEqE (fl eq : ℕ) : Expr := .call eq (mk2 (.call fl (arg 0)) (.call fl (arg 1)))

/-- The equality program at base `b` (12 functions). -/
def vsPEqFuns (b : ℕ) : List Expr := [vsPEqE (b + 1) (b + 9)] ++ vsWFlatFuns (b + 1) ++ eqNatsFuns (b + 9)

theorem vsPEqFuns_length (b : ℕ) : (vsPEqFuns b).length = 12 := rfl

/-- **Equality of stored matrices.** -/
theorem vsPEq_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsPEqFuns b)) {p N D : ℕ}
    (hpN : p ≤ N) (hDD : D * D ≤ N) {A B : List (List ℕ)} (hA : VsWSq p D A) (hB : VsWSq p D B) :
    FunDet P b (.list [vsWVs A, vsWVs B]) (boolVal (decide (A = B))) (10 ^ 8 * (N + 1) ^ 4) := by
  have h0 : P.funs[b]? = some (vsPEqE (b + 1) (b + 9)) := h.get (j := 0) (by simp [vsPEqFuns])
  have hfl : P.HasAt (b + 1) (vsWFlatFuns (b + 1)) := h.block 1 rfl
  have heq : P.HasAt (b + 9) (eqNatsFuns (b + 9)) := h.block 9 rfl
  have a0 := Det.arg' (P := P) (vs := [vsWVs A, vsWVs B]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [vsWVs A, vsWVs B]) (rest := []) (j := 1) rfl
  have dA := Det.call a0 (vsWFlat_spec hfl hpN hDD hA)
  have dB := Det.call a1 (vsWFlat_spec hfl hpN hDD hB)
  have dE := Det.call (Det.mk2 dA dB) (eqNats_spec heq A.flatten B.flatten)
  have hdec : decide (A.flatten = B.flatten) = decide (A = B) := by
    refine Bool.decide_congr ⟨fun e => ?_, fun e => by rw [e]⟩
    exact vsP_flatten_inj (fun r hr => (hA.1 r hr).2) (fun r hr => (hB.1 r hr).2)
      (by rw [hA.2, hB.2]) e
  rw [hdec] at dE
  refine FunDet.intro h0 (dE.mono ?_)
  have hDN : D ≤ N := le_trans (Nat.le_mul_self D) hDD
  have fA := vsWFlat_take hA A.length
  have fB := vsWFlat_take hB B.length
  rw [List.take_length] at fA fB
  have wA := wt_natList_le_sq (fun y hy => (fA.1 y hy).le.trans hpN) (fA.2.trans hDD)
  have wB := wt_natList_le_sq (fun y hy => (fB.1 y hy).le.trans hpN) (fB.2.trans hDD)
  have wVA := wt_vsWVs_le (VsWFit.bnd hA.1 hpN hDN) (show A.length ≤ N + 1 by rw [hA.2]; omega)
  have wVB := wt_vsWVs_le (VsWFit.bnd hB.1 hpN hDN) (show B.length ≤ N + 1 by rw [hB.2]; omega)
  have w2 := wt_list2_le (vsWVs A) (vsWVs B)
  have w3 := wt_list2_le (natList A.flatten) (natList B.flatten)
  have wb := wt_boolVal_le (decide (A = B))
  have hK : loopModK = 1000 := rfl
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hl : A.flatten.length + 1 ≤ N + 1 := by omega
  have hm : loopModK * (A.flatten.length + 1) *
      ((Val.list [natList A.flatten, natList B.flatten]).wt + A.flatten.length + 4) ≤
      1000 * (N + 1) * (30 * (N + 1) ^ 2) := by
    rw [hK]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hl) (by omega)
  have e : 1000 * (N + 1) * (30 * (N + 1) ^ 2) = 30000 * (N + 1) ^ 3 := by ring
  omega

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved

/-! ### Membership of a stored matrix in a span of stored matrices -/

/-- On `[p, rows, z, A]`: `1` if the sifted flattened `A` is the zero vector `z`, else `0`. -/
def vsPInLE (fl sft eq : ℕ) : Expr :=
  .call eq (mk2 (.get (.call sft (mk3 (arg 0) (arg 1) (mk2 (.call fl (arg 3)) .nil))) (.nat 0))
    (arg 2))

/-- The membership program at base `b` (24 functions). -/
def vsPInLFuns (b : ℕ) : List Expr :=
  [vsPInLE (b + 1) (b + 9) (b + 21)] ++ vsWFlatFuns (b + 1) ++ vsSiftFuns (b + 9) (b + 12) ++
    [vsSiftStepF (b + 13)] ++ vsLinFuns (b + 13) ++ eqNatsFuns (b + 21)

theorem vsPInLFuns_length (b : ℕ) : (vsPInLFuns b).length = 24 := rfl

/-- **Membership test.** -/
theorem vsPInL_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsPInLFuns b)) {p N D : ℕ}
    (hp : 0 < p) (hpN : p ≤ N) (hDD : D * D ≤ N) {rows : List VsRow}
    (hr : ∀ r ∈ rows, VsRowFits N (D * D) 0 r) (hrl : rows.length ≤ N)
    {A : List (List ℕ)} (hA : VsWSq p D A) :
    FunDet P b (.list [.nat p, .list (rows.map VsRow.val), natList (vsWZ (D * D)), vsWVs A])
      (boolVal (decide ((vsSift p rows (A.flatten, [])).1 = vsWZ (D * D))))
      (10 ^ 8 * (N + 1) ^ 4) := by
  have h0 : P.funs[b]? = some (vsPInLE (b + 1) (b + 9) (b + 21)) :=
    h.get (j := 0) (by simp [vsPInLFuns])
  have hfl : P.HasAt (b + 1) (vsWFlatFuns (b + 1)) := h.block 1 rfl
  have hsf : P.HasAt (b + 9) (vsSiftFuns (b + 9) (b + 12)) := h.block 9 rfl
  have hst : P.funs[b + 12]? = some (vsSiftStepF (b + 13)) :=
    h.get (j := 12) (by rw [vsPInLFuns_length]; omega)
  have hl : P.HasAt (b + 13) (vsLinFuns (b + 13)) := h.block 13 rfl
  have heq : P.HasAt (b + 21) (eqNatsFuns (b + 21)) := h.block 21 rfl
  have hDN : D ≤ N := le_trans (Nat.le_mul_self D) hDD
  set vs := [Val.nat p, .list (rows.map VsRow.val), natList (vsWZ (D * D)), vsWVs A]
  have a k {v : Val} (hv : vs[k]? = some v) := Det.arg' (P := P) (rest := []) (vs := vs) (j := k) hv
  have fA := vsWFlat_take hA A.length
  rw [List.take_length] at fA
  have dF := Det.call (a 3 rfl) (vsWFlat_spec hfl hpN hDD hA)
  have dpair := Det.mk2 dF (Det.nil (P := P) (env := [.list vs]))
  have ep : Val.list [natList A.flatten, .list []] = vsPairVal (A.flatten, []) := rfl
  rw [ep] at dpair
  have hP : VsPairFits p N (A.flatten, []) :=
    ⟨fun y hy => fA.1 y hy, by simp, fA.2.trans hDD, by simp⟩
  have hr' : ∀ r ∈ rows, VsRowFits N (A.flatten, ([] : List ℕ)).1.length
      (A.flatten, ([] : List ℕ)).2.length r := by
    intro r hr0
    have e1 : (A.flatten, ([] : List ℕ)).1.length = D * D := by
      simp only
      rw [GI.Proved.vsFA_flatten_length (fun r hr => (hA.1 r hr).2), hA.2]
    rw [e1]; exact hr r hr0
  have dS := Det.call (Det.mk3 (a 0 rfl) (a 1 rfl) dpair) (vsSift_spec hsf hst hl hp hpN hP hr' hrl)
  have dX := Det.get' dS (Det.nat 0)
    (show [natList (vsSift p rows (A.flatten, [])).1, natList (vsSift p rows (A.flatten, [])).2][0]?
      = some (natList (vsSift p rows (A.flatten, [])).1) from rfl)
  have dE := Det.call (Det.mk2 dX (a 2 rfl))
    (eqNats_spec heq (vsSift p rows (A.flatten, [])).1 (vsWZ (D * D)))
  refine FunDet.intro h0 (dE.mono ?_)
  -- the cost
  have HS := vsSift_fits hp rows hP
  have wS := wt_vsPairVal_le hpN HS.hx HS.ht HS.lx HS.lt
  have wX := wt_natList_le_sq (fun y hy => (HS.hx y hy).le.trans hpN) HS.lx
  have wF := wt_natList_le_sq (fun y hy => (fA.1 y hy).le.trans hpN) (fA.2.trans hDD)
  have wz : (natList (vsWZ (D * D))).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp [vsWZ] at hy; omega) (by simp [vsWZ]; omega)
  have wR := wt_vsRows_le hr (by omega)
  have wVA := wt_vsWVs_le (VsWFit.bnd hA.1 hpN hDN) (show A.length ≤ N + 1 by rw [hA.2]; omega)
  have w4 := wt_list4_le (.nat p) (.list (rows.map VsRow.val)) (natList (vsWZ (D * D))) (vsWVs A)
  have w2 := wt_list2_le (natList A.flatten) (.list [])
  have w3 := wt_list3_le (.nat p) (.list (rows.map VsRow.val)) (vsPairVal (A.flatten, []))
  have w5 := wt_list2_le (natList (vsSift p rows (A.flatten, [])).1) (natList (vsWZ (D * D)))
  have wb := wt_boolVal_le (decide ((vsSift p rows (A.flatten, [])).1 = vsWZ (D * D)))
  have wp := wt_nat_le p
  have wn : (Val.list []).wt ≤ 5 := by simp
  have hK : loopModK = 1000 := rfl
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hlx : (vsSift p rows (A.flatten, [])).1.length + 1 ≤ N + 1 := by have := HS.lx; omega
  have hm : loopModK * ((vsSift p rows (A.flatten, [])).1.length + 1) *
      ((Val.list [natList (vsSift p rows (A.flatten, [])).1, natList (vsWZ (D * D))]).wt +
        (vsSift p rows (A.flatten, [])).1.length + 4) ≤
      1000 * (N + 1) * (30 * (N + 1) ^ 2) := by
    rw [hK]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hlx) (by omega)
  have e : 1000 * (N + 1) * (30 * (N + 1) ^ 2) = 30000 * (N + 1) ^ 3 := by ring
  have ev : (Val.list vs).wt = (Val.list [Val.nat p, .list (rows.map VsRow.val),
      natList (vsWZ (D * D)), vsWVs A]).wt := rfl
  have ew : (vsPairVal (A.flatten, [])).wt = (Val.list [natList A.flatten, .list []]).wt := rfl
  have eS : (vsPairVal (vsSift p rows (A.flatten, []))).wt =
      (Val.list [natList (vsSift p rows (A.flatten, [])).1,
        natList (vsSift p rows (A.flatten, [])).2]).wt := rfl
  omega

end GI.Impl
