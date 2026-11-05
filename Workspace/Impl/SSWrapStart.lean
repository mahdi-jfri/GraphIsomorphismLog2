module

public import Workspace.Impl.SSWrapBase

@[expose] public section

/-!
# The start of the wrappers

`ssStartF` builds the table from the group and the base (`ssStartF_spec`). `ssStSiftF` takes
`[encGroup gs, encPerm x]`, builds the table for the base `[0, …, n-1]`, and sifts `x`
(`ssStSiftF_spec`). The membership and constructive membership wrappers use it.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- On `[encGroup gs, ssEncB B]`: the encoded table `ssBuild B gs`. -/
def ssStartF (core : ℕ) : Expr :=
  .call core (mk4 (.get (arg 0) (.nat 0)) (arg 1) (.get (arg 0) (.nat 1))
    (.arith .mul (.length (arg 1)) (.get (arg 0) (.nat 0))))

theorem ss_two_core {X c : ℕ} (hc : c ≤ 10 ^ 8 * (X + 1) ^ 4) :
    c + 300 * (10 * X + 10 + 1) ≤ 2 * (10 ^ 8 * (X + 1) ^ 4) := by
  have h : X + 1 ≤ (X + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  generalize (X + 1) ^ 4 = Q at *
  linarith

/-- Weights below `ssW Y` for the base and the generators. -/
theorem ss_start_wts {B : List (Fin n)} {gs : List (Perm (Fin n))} {Y : ℕ}
    (hY : n + B.length + gs.length + 2 ≤ Y) :
    (ssEncB B).wt ≤ ssW Y ∧ (Val.list ((1 :: gs).map encPerm)).wt ≤ ssW Y ∧
      n + 2 ≤ ssW Y ∧ B.length * n + 2 ≤ ssW Y ∧ B.length + 2 ≤ ssW Y := by
  have hc := ss_ctx_wt hY
  obtain ⟨hMM, -, hn4, -⟩ := ss_W_facts hY
  have hmem : ∀ v ∈ [Val.nat n, ssEncB B, .list ((1 :: gs).map encPerm), .nat (B.length * n)],
      v.wt ≤ ssW Y := fun v hv => (le_of_lt (wt_le_wt_list hv)).trans hc
  have hM := Nat.le_mul_self (B.length * n)
  have hn : n + 1 ≤ (n + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  obtain ⟨-, -, -, hY3, hZ⟩ := ss_Y_facts hY
  have hZW := ssZ_le_ssW Y
  refine ⟨hmem _ (by simp), hmem _ (by simp), by omega, by omega, by omega⟩

/-- **The start.** -/
theorem ssStartF_spec {P : Program} {f b : ℕ} (hf : P.funs[f]? = some (ssStartF (b + 46)))
    (hP : SsCoreAt P b) {B : List (Fin n)} {gs : List (Perm (Fin n))} {Y : ℕ}
    (hY : n + B.length + gs.length + 2 ≤ Y) :
    FunDet P f (.list [encGroup gs, ssEncB B]) (ssEncSt (ssBuild B gs)) (2 * ssCoreCost Y) := by
  obtain ⟨hBw, hgw, hnW, hMW, hLW⟩ := ss_start_wts hY
  have hc := ss_ctx_wt hY
  have hs := ss_st_wt (ssBuild_spec (B := B) (gs := gs)).1 hY
  have hG : (Val.list [.nat n, .list ((1 :: gs).map encPerm)]).wt ≤ ssW Y :=
    (ss_encGroup_small hY).wt_le_ssW
  set W := 10 * ssW Y + 10 with hW
  clear_value W
  have hBe : ssEncB B = .list ((B.map Fin.val).map Val.nat) := rfl
  have hBL : ((B.map Fin.val).map Val.nat).length = B.length := by simp
  set a := Val.list [.list [.nat n, .list ((1 :: gs).map encPerm)], ssEncB B] with ha
  have haW : a.wt ≤ W := (st_wt_list2 hG hBw).trans (by omega)
  have dG : StDC P [a] (arg 0) (.list [.nat n, .list ((1 :: gs).map encPerm)]) 3 0 W :=
    StDC.arg rfl haW (by omega) (by omega)
  have d0 : StDC P [a] (.get (arg 0) (.nat 0)) (.nat n) 5 0 W :=
    StDC.get (x := 0) (v := .nat n) dG (StDC.nat 0 (by omega)) rfl
      ((wt_nat_le _).trans (by omega))
  have d1 : StDC P [a] (arg 1) (.list ((B.map Fin.val).map Val.nat)) 3 0 W :=
    StDC.arg (j := 1) rfl haW (by omega) (by rw [← hBe]; omega)
  have dL : StDC P [a] (.length (arg 1)) (.nat B.length) 4 0 W := by
    have := StDC.length d1 (by rw [hBL]; omega)
    rwa [hBL] at this
  have d2 : StDC P [a] (.get (arg 0) (.nat 1)) (.list ((1 :: gs).map encPerm)) 5 0 W :=
    StDC.get (x := 1) (v := .list ((1 :: gs).map encPerm)) dG (StDC.nat 1 (by omega)) rfl
      (by omega)
  have dM : StDC P [a] (.arith .mul (.length (arg 1)) (.get (arg 0) (.nat 0)))
      (.nat (B.length * n)) 10 0 W :=
    StDC.arith dL d0 rfl ((wt_nat_le _).trans (by omega))
  have dA := StDC.mk4 d0 d1 d2 dM (by rw [← hBe]; show (ssCtx B gs).wt ≤ W; omega) (by omega)
  rw [← hBe] at dA
  have dC := StDC.call dA (ssCoreF_spec hP hY) (by omega)
  refine StDC.funDet hf dC (ss_cost_fin2 (by norm_num) ?_)
  unfold ssCoreCost
  rw [hW]
  simpa only [Nat.zero_add] using ss_two_core (X := ssW Y) le_rfl

/-- On `[encGroup gs, encPerm x]`: the table `st` for the base `[0, …, n-1]` and the result of
sifting `x`, as `[ssEncSt st, ssEncAcc (ssSift …)]`. -/
def ssStSiftF (range start sift : ℕ) : Expr :=
  .letE (.get (arg 0) (.nat 0))
    (.letE (.call range (.var 1))
      (.letE (.call start (mk2 (arg 0) (.var 2)))
        (mk2 (.var 3) (.call sift (mk3 (mk3 (.var 1) (.var 2) (.get (.var 3) (.nat 0))) (.var 1)
          (mk3 (arg 1) .nil (.nat 0)))))))

theorem ss_stsift_cost {X r s : ℕ} (hr : r ≤ 1000 * (X + 1) * (3 * X + 1))
    (hs : s ≤ 10 ^ 6 * (X + 1) ^ 2) :
    r + 2 * (10 ^ 8 * (X + 1) ^ 4) + s + 300 * (10 * X + 10 + 1) ≤
      4 * (10 ^ 8 * (X + 1) ^ 4) := by
  have h1 : (X + 1) * (3 * X + 1) ≤ 3 * (X + 1) ^ 2 := by nlinarith
  have h2 : (X + 1) ^ 2 ≤ (X + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  rw [Nat.mul_assoc] at hr
  generalize (X + 1) * (3 * X + 1) = A at *
  generalize (X + 1) ^ 2 = Q2 at *
  generalize (X + 1) ^ 4 = Q4 at *
  linarith

/-- **Build and sift.** -/
theorem ssStSiftF_spec {P : Program} {f rb sf b : ℕ}
    (hf : P.funs[f]? = some (ssStSiftF rb sf (b + 25))) (hr : P.HasAt rb (rangeFuns rb))
    (hs : P.funs[sf]? = some (ssStartF (b + 46))) (hP : SsCoreAt P b)
    {gs : List (Perm (Fin n))} (x : Perm (Fin n)) {Y : ℕ} (hY : n + n + gs.length + 2 ≤ Y) :
    FunDet P f (.list [encGroup gs, encPerm x])
      (.list [ssEncSt (ssBuild (List.finRange n) gs),
        ssEncAcc (ssSift (List.finRange n) (ssBuild (List.finRange n) gs).1 x)])
      (4 * ssCoreCost Y) := by
  have hY' : n + (List.finRange n).length + gs.length + 2 ≤ Y := by
    rw [List.length_finRange]; exact hY
  obtain ⟨hBw, hgw, hnW, hMW, hLW⟩ := ss_start_wts hY'
  rw [ssEncB_finRange] at hBw
  have hst := ssStartF_spec hs hP hY'
  rw [ssEncB_finRange] at hst
  have hinv := (ssBuild_spec (B := List.finRange n) (gs := gs)).1
  have hsm := ssInv_small hinv hY'
  have hsw := ss_st_wt hinv hY'
  obtain ⟨-, hTY, -, hY3, hZ⟩ := ss_Y_facts hY'
  have hZW := ssZ_le_ssW Y
  have hG : (Val.list [.nat n, .list ((1 :: gs).map encPerm)]).wt ≤ ssW Y :=
    (ss_encGroup_small hY').wt_le_ssW
  have hxw : (encPerm x).wt ≤ ssW Y := (ssSmall_encPerm x (by omega)).wt_le_ssW
  generalize hst0 : ssBuild (List.finRange n) gs = st at hst hinv hsm hsw
  obtain ⟨T, prog⟩ := st
  have hlen : T.length = (List.finRange n).length * n := hinv.len
  have hsift := ssSiftLoop_spec hP.gen.insAt.siftAt (List.finRange n) T hlen
    (by rw [List.length_finRange]; omega) hsm.idx x
  rw [show ssSiftCtx (List.finRange n) T = .list [.nat n, natList (List.range n), ssEncTab T] by
    rw [ssSiftCtx, ssEncB_finRange], List.length_finRange] at hsift
  have facts := ssSift_acc_facts (List.finRange n) T hsm.idx x (List.finRange n).length
  have hfold : (List.range (List.finRange n).length).foldl (ssSiftStep (List.finRange n) T)
    (x, [], 0) = ssSift (List.finRange n) T x := rfl
  rw [hfold, List.length_finRange] at facts
  rw [List.length_finRange] at hlen hTY
  have hctx := (ssSmall_ctx (Z := ssZ Y) (List.finRange n) T hsm.idx (by
    rw [hlen, List.length_finRange]; omega)).wt_le_ssW
  rw [ssSiftCtx, ssEncB_finRange] at hctx
  have hacc0 := (ssSmall_acc (Z := ssZ Y) (x, [], 0) (by simp) (by simp) (by simp; omega)).wt_le_ssW
  have hR := (ssSmall_acc (Z := ssZ Y) (ssSift (List.finRange n) T x) facts.2.1
    (facts.2.2.trans (by omega)) (by have := facts.1; omega)).wt_le_ssW
  set W := 10 * ssW Y + 10 with hW
  clear_value W
  set a := Val.list [.list [.nat n, .list ((1 :: gs).map encPerm)], encPerm x] with ha
  have haW : a.wt ≤ W := (st_wt_list2 hG hxw).trans (by omega)
  have dG : ∀ rest, StDC P (a :: rest) (arg 0) (.list [.nat n, .list ((1 :: gs).map encPerm)])
      3 0 W := fun rest => StDC.arg rfl haW (by omega) (by omega)
  have dn : StDC P [a] (.get (arg 0) (.nat 0)) (.nat n) 5 0 W :=
    StDC.get (x := 0) (v := .nat n) (dG []) (StDC.nat 0 (by omega)) rfl
      ((wt_nat_le _).trans (by omega))
  have hnw : (Val.nat n).wt ≤ W := (wt_nat_le _).trans (by omega)
  have hrange : FunDet P rb (.nat n) (natList (List.range n))
      (1000 * (ssW Y + 1) * (3 * ssW Y + 1)) :=
    (range_spec hr n).mono fun w c ⟨hw, hc⟩ => ⟨hw, hc.trans (by
      rw [hw]; unfold loopModK
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
        (by have := wt_nat_le n; omega))⟩
  have dR : StDC P [a, .nat n] (.call rb (.var 1)) (natList (List.range n)) (1 + 1)
      (0 + 1000 * (ssW Y + 1) * (3 * ssW Y + 1)) W :=
    StDC.call (StDC.var' rfl hnw) hrange (by omega)
  have dS : StDC P [a, .nat n, natList (List.range n)] (.call sf (mk2 (arg 0) (.var 2)))
      (ssEncSt (T, prog)) (3 + 1 + 3 + 1) (0 + 0 + 2 * ssCoreCost Y) W :=
    StDC.call (StDC.mk2 (dG _) (StDC.var' rfl (by omega))
      ((st_wt_list2 hG hBw).trans (by omega)) (by omega)) hst (by omega)
  set env3 := [a, .nat n, natList (List.range n), ssEncSt (T, prog)] with henv3
  have dT : StDC P env3 (.get (.var 3) (.nat 0)) (ssEncTab T) 3 0 W :=
    StDC.get (x := 0) (v := ssEncTab T)
      (StDC.var' (v := .list [ssEncTab T, ssEncProg prog]) rfl (by
        show (ssEncSt (T, prog)).wt ≤ W; omega)) (StDC.nat 0 (by omega)) rfl (by
      have : (ssEncTab T).wt < (ssEncSt (T, prog)).wt := wt_le_wt_list (by simp)
      omega)
  have dV1 : StDC P env3 (.var 1) (.nat n) 1 0 W := StDC.var' rfl hnw
  have dctx := StDC.mk3 dV1 (StDC.var' (i := 2) rfl (by omega)) dT (by omega) (by omega)
  have dacc := StDC.mk3 (P := P) (StDC.arg (j := 1) (v := encPerm x) rfl haW (by omega) (by omega))
    (StDC.nil (env := env3) (by omega)) (StDC.nat 0 (by omega))
    (show (ssEncAcc (x, [], 0)).wt ≤ W by omega) (by omega)
  have dSf := StDC.call (StDC.mk3 dctx dV1 dacc
    ((st_wt_list3 hctx ((wt_nat_le _).trans (by omega)) hacc0).trans (by omega)) (by omega))
    hsift (by omega)
  have dFin := StDC.mk2 (StDC.var' (i := 3) (env := env3) rfl (by
    show (ssEncSt (T, prog)).wt ≤ W; omega)) dSf ((st_wt_list2 hsw hR).trans (by omega))
    (by omega)
  refine StDC.funDet hf (StDC.letE dn (StDC.letE dR (StDC.letE dS dFin
    ((st_wt_list2 hsw hR).trans (by omega))) ((st_wt_list2 hsw hR).trans (by omega)))
    ((st_wt_list2 hsw hR).trans (by omega))) (ss_cost_fin2 (by norm_num) ?_)
  have := ss_stsift_cost (X := ssW Y) (r := 1000 * (ssW Y + 1) * (3 * ssW Y + 1))
    (s := ssSiftCost Y) le_rfl le_rfl
  unfold ssCoreCost
  rw [hW]
  simp only [Nat.zero_add, Nat.add_zero]
  rw [← Nat.add_assoc]
  exact this

end GI.Impl
