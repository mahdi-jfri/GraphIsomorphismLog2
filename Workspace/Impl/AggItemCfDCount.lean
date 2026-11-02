import Workspace.Impl.AggItemCfDMath
import Workspace.Lang.Lib.OrbitT

/-!
# Counting colors by their encoded weight

Colors need not be small numbers in the object-stage contract. Equality
and counting still have polynomial cost: a color's bit length is paid for
by the input table. These are weight-based bounds for the existing
language programs, without a change to their computation.
-/

set_option maxRecDepth 2000

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp)

/-- Equality of two colors, with cost charged by their encoded weights. -/
theorem itCfD_eq_spec {P : Program} {f : ℕ}
    (hf : P.funs[f]? = some eqTestF) (j y : ℕ) :
    FunDet P f (.list [.nat j, .nat y]) (boolVal (natEq j (.nat y)))
      (10 * (Val.list [.nat j, .nat y]).wt + 100) := by
  refine FunDet.intro hf ((Det.arith' (Det.arg' (rest := []) (j := 1) rfl)
    (Det.arg' (j := 0) rfl) (z := (natEq j (.nat y)).toNat) ?_).mono ?_)
  · simp only [BinOp.eval, natEq_nat]
    by_cases hij : y = j <;> simp [hij]
  · have hjw : (Val.nat j).wt < (Val.list [.nat j, .nat y]).wt := wt_le_wt_list (by simp)
    have hyw : (Val.nat y).wt < (Val.list [.nat j, .nat y]).wt := wt_le_wt_list (by simp)
    have hn := wt_nat_le (natEq j (.nat y)).toNat
    have := Bool.toNat_le (natEq j (.nat y))
    omega

/-- Counting uses the existing `countFuns` and allows arbitrary numeric colors. -/
theorem itCfD_count_spec {P : Program} {b : ℕ} (h : P.HasAt b (countFuns b))
    (xs : List ℕ) (j : ℕ) {N : ℕ} (hN : (Val.list [.nat j, natList xs]).wt ≤ N) :
    FunDet P b (.list [.nat j, natList xs]) (.nat (xs.count j))
      (10 ^ 6 * (N + 1) ^ 3) := by
  have hentry : P.funs[b]? = some (countEntry (b + 1)) := by
    simpa [countFuns] using h 0 (by simp [countFuns])
  have hfl : P.HasAt (b + 1) (filterFuns (b + 1) (b + 4)) := by
    simpa using h.left.right
  have htest : P.funs[b + 4]? = some eqTestF := by
    simpa [countFuns, filterFuns, loopFuns, Nat.add_assoc] using h 4
      (by simp [countFuns, filterFuns, loopFuns])
  have hjw : (Val.nat j).wt < (Val.list [.nat j, natList xs]).wt := wt_le_wt_list (by simp)
  have hxw : (natList xs).wt < (Val.list [.nat j, natList xs]).wt := wt_le_wt_list (by simp)
  have hl : xs.length < (natList xs).wt := by
    have := length_lt_wt_list (xs.map Val.nat); simpa [natList] using this
  have hT : ∀ x ∈ xs.map Val.nat, FunDet P (b + 4) (.list [.nat j, x])
      (boolVal (natEq j x)) (1000 * (N + 1)) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have hyw : (Val.nat y).wt < (natList xs).wt :=
      wt_le_wt_list (List.mem_map.2 ⟨y, hy, rfl⟩)
    have hw := wt_list2_le (.nat j) (.nat y)
    exact (itCfD_eq_spec htest j y).mono (by omega)
  have hF := filter_spec hfl (c := .nat j) (xs := xs.map Val.nat) hT
  rw [filter_natEq] at hF
  have hfilw : (natList (xs.filter fun x => decide (x = j))).wt ≤ 5 * (N + 1) ^ 2 := by
    have hw := wt_list_le_of ((xs.filter fun x => decide (x = j)).map Val.nat) (c := N) (by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
      have hx' := List.mem_of_mem_filter hx
      have hw : (Val.nat x).wt < (natList xs).wt :=
        wt_le_wt_list (List.mem_map.2 ⟨x, hx', rfl⟩)
      omega)
    have hlf : (xs.filter fun x => decide (x = j)).length ≤ N :=
      (List.length_filter_le _ _).trans (by omega)
    simp only [List.length_map] at hw
    have hm := Nat.mul_le_mul_right (2 * N + 1) hlf
    change (natList (xs.filter fun x => decide (x = j))).wt ≤ _ at hw
    nlinarith
  have hF' : FunDet P (b + 1) (.list [.nat j, natList xs])
      (natList (xs.filter fun x => decide (x = j)))
      (((xs.map Val.nat).map fun _ => 1000 * (N + 1)).sum +
        loopModK * ((xs.map Val.nat).length + 1) *
          ((Val.list [.nat j, natList xs]).wt + (xs.map Val.nat).length +
            (natList (xs.filter fun x => decide (x = j))).wt + 1)) :=
    hF.mono fun w c ⟨hw, hc⟩ => ⟨hw, by subst hw; exact hc⟩
  refine FunDet.intro hentry ((Det.length (Det.call
    (Det.var' (P := P) (env := [.list [.nat j, natList xs]]) (i := 0) rfl) hF')).post
    fun c hc => ?_)
  have hlen : ((xs.filter fun x => decide (x = j)).map Val.nat).length = xs.count j := by
    rw [List.length_map, count_eq_filter]
  refine ⟨by rw [hlen], ?_⟩
  have hcount := List.count_le_length (a := j) (l := xs)
  have hcntw := wt_nat_le (xs.count j)
  simp only [List.map_map, Function.comp_def, List.map_const', List.sum_replicate,
    smul_eq_mul, List.length_map] at hc
  have hm1 : xs.length * (1000 * (N + 1)) ≤ 1000 * (N + 1) ^ 2 := by
    have := Nat.mul_le_mul_right (1000 * (N + 1)) (show xs.length ≤ N + 1 by omega)
    nlinarith
  have hm2 : loopModK * (xs.length + 1) *
      ((Val.list [.nat j, natList xs]).wt + xs.length +
        (natList (xs.filter fun x => decide (x = j))).wt + 1) ≤
      8000 * (N + 1) ^ 3 := by
    have hm := Nat.mul_le_mul (Nat.mul_le_mul_left loopModK
      (show xs.length + 1 ≤ N + 1 by omega))
      (show (Val.list [.nat j, natList xs]).wt + xs.length +
        (natList (xs.filter fun x => decide (x = j))).wt + 1 ≤ 8 * (N + 1) ^ 2 by
        have : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
        omega)
    calc _ ≤ loopModK * (N + 1) * (8 * (N + 1) ^ 2) := hm
         _ = _ := by unfold loopModK; ring
  have hp23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hp13 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  rw [count_eq_filter] at hc
  simp only [natList] at hc hN hm2 hfilw hxw hl
  have hnlen : xs.length ≤ N := by omega
  have hcountN : xs.count j ≤ N := hcount.trans hnlen
  omega

end GI.Impl
