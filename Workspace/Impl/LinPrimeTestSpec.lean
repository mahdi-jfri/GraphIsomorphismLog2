module

public import Workspace.Impl.LinPrimeTest

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang
open GI.Machine (BinOp)

theorem linPrimeTest_all (n : ℕ) (hn : 2 ≤ n) :
    ((List.range n).map Val.nat).all (linPrimeTestPred n) = decide n.Prime := by
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
  constructor
  · intro h
    refine Nat.prime_def_lt'.mpr ⟨hn, ?_⟩
    intro j hj hjn hd
    have hh := h (.nat j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hjn, rfl⟩)
    simp only [linPrimeTestPred, decide_eq_true_eq, Nat.not_lt.mpr hj, false_or] at hh
    exact hh (Nat.mod_eq_zero_of_dvd hd)
  · intro hp v hv
    obtain ⟨j, hjn, rfl⟩ := List.mem_map.mp hv
    simp only [linPrimeTestPred, decide_eq_true_eq]
    by_cases hj : j < 2
    · exact Or.inl hj
    · exact Or.inr (fun he => (Nat.prime_def_lt'.mp hp).2 j (by omega)
        (List.mem_range.mp hjn) (Nat.dvd_of_mod_eq_zero he))

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 5000 in
theorem linPrimeTest_spec {P : Program} {b : ℕ} (h : linPrimeTestAt P b) (n : ℕ) :
    FunDet P b (.nat n) (boolVal (decide n.Prime)) (linPrimeTestCost n) := by
  let xs := (List.range n).map Val.nat
  let rv := Val.list xs
  have wn := wt_nat_le n
  have wzero : (Val.nat 0).wt = 2 := rfl
  have wrv : rv.wt ≤ 10 * (n + 1) ^ 2 := by
    have hh := linWtList (vs := xs) (B := n + 2) (by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
      exact (wt_nat_le j).trans (by have := List.mem_range.mp hj; omega))
    simp only [xs, List.length_map, List.length_range] at hh
    dsimp only [rv]
    nlinarith only [hh]
  have hr : FunDet P (b + 1) (.nat n) rv (100000 * (n + 1) ^ 3) :=
    FunAll.mono (range_spec h.range n) (fun out cost ho => by
      obtain ⟨rfl, hc⟩ := ho
      refine ⟨rfl, ?_⟩
      change cost ≤ loopModK * (n + 1) * ((Val.nat n).wt + n + rv.wt + 1) at hc
      have hh := Nat.mul_le_mul_left (loopModK * (n + 1))
        (show (Val.nat n).wt + n + rv.wt + 1 ≤ n + 2 + n + 10 * (n + 1) ^ 2 + 1 by omega)
      unfold loopModK at hc hh
      nlinarith only [hc, hh])
  have wa : (Val.list [.nat n, rv]).wt ≤ 100 * (n + 1) ^ 2 := by
    have hh := wt_list2_le (.nat n) rv
    nlinarith only [hh, wn, wrv]
  have hall : FunDet P (b + 4) (.list [.nat n, rv]) (boolVal (xs.all (linPrimeTestPred n)))
      (1000000 * (n + 1) ^ 3) := by
    have hs := GI.Lang.all_spec h.all (q := linPrimeTestPred n) (B := fun _ => 10000 * (n + 1)) (by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
      exact linPrimeTestCell_spec h.cell n j (List.mem_range.mp hj))
    refine hs.mono fun out cost ho => ⟨ho.1, ?_⟩
    have hc := ho.2
    simp only [List.map_const', List.sum_replicate, List.length_map, List.length_range,
      smul_eq_mul] at hc
    change cost ≤ n * (10000 * (n + 1)) +
      loopModK * (n + 1) * ((Val.list [.nat n, rv]).wt + n + 4) at hc
    have hh := Nat.mul_le_mul_left (loopModK * (n + 1))
      (show (Val.list [.nat n, rv]).wt + n + 4 ≤ 100 * (n + 1) ^ 2 + n + 4 by omega)
    unfold loopModK at hc hh
    nlinarith only [hc, hh]
  have dr := Det.call (Det.var' (P := P) (env := [.nat n]) (i := 0) rfl) hr
  have dn := Det.var' (P := P) (env := [.nat n, rv]) (i := 0) rfl
  have dv := Det.var' (P := P) (env := [.nat n, rv]) (i := 1) rfl
  have wout := wt_boolVal_le (decide n.Prime)
  apply FunDet.intro h.entry
  by_cases hn : 2 ≤ n
  · have ht := Det.arith' (op := .lt) (Det.nat 1) dn (z := 1) (by simp [BinOp.eval]; omega)
    have ha := hall
    rw [linPrimeTest_all n hn] at ha
    have dc := Det.call (Det.mk2 dn dv) ha
    refine (Det.letE dr (Det.ite_pos (e := .nat 0) ht (by decide : 1 ≠ 0) dc)).mono ?_
    have warg := wt_list2_le (.nat n) rv
    unfold linPrimeTestCost
    dsimp only [rv, xs] at *
    nlinarith only [wn, wrv, wa, wout, warg]
  · have hnp : ¬ n.Prime := fun hp => hn hp.two_le
    have ht := Det.arith' (op := .lt) (Det.nat 1) dn (z := 0) (by simp [BinOp.eval]; omega)
    have dd := Det.ite_zero (t := .call (b + 4) (mk2 (.var 0) (.var 1))) ht (Det.nat 0)
    have hout : boolVal (decide n.Prime) = .nat 0 := by simp [hnp, boolVal]
    rw [hout]
    refine (Det.letE dr dd).mono ?_
    unfold linPrimeTestCost
    dsimp only [rv, xs] at *
    nlinarith only [wn, wrv, wzero]

end GI.Impl
