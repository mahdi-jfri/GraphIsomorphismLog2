module

public import Workspace.Impl.JohnFold

@[expose] public section

/-!
# The output

The function at `98` computes `johnOut` (`john_mapOut_spec`). For each point `x`, it filters the
numbers `t` below the length of `Λ` by the test `Λ[t][x] = 1`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ} {lam : List (List ℕ)}

/-- The test of the output for the point `x`. -/
def johnQO (lam : List (List ℕ)) (x : ℕ) (w : Val) : Bool :=
  decide ((lam.getD (johnNatOf w) []).getD x 0 = 1)

/-- The numbers `t` of the output for the point `x`. -/
def johnOutRow (lam : List (List ℕ)) (x : ℕ) : List ℕ :=
  (List.range lam.length).filter fun t => decide ((lam.getD t []).getD x 0 = 1)

/-- **The test `Λ[t][x] = 1`.** -/
theorem john_outP_spec (ha : JohnAccOK n lam) {x t : ℕ} (hx : x < n) (ht : t < lam.length) :
    FunDet johnProgram 105 (.list [.list [.list (lam.map natList), .nat x], .nat t])
      (boolVal (johnQO lam x (.nat t))) (2000 * (n + 1) ^ 2) := by
  set c := Val.list [.list (lam.map natList), .nat x]
  set a := Val.list [c, .nat t]
  have hc : Det johnProgram [a] (arg 0) c (2 * a.wt + 5) := Det.arg' rfl
  have hL := Det.get' hc (Det.nat 0)
    (show [Val.list (lam.map natList), .nat x][0]? = some (.list (lam.map natList)) from rfl)
  have hX := Det.get' hc (Det.nat 1)
    (show [Val.list (lam.map natList), .nat x][1]? = some (.nat x) from rfl)
  have hT : Det johnProgram [a] (arg 1) (.nat t) (2 * a.wt + 6) := Det.arg' rfl
  have hent := ha.ent lam[t] (List.getElem_mem ht)
  have hxl : x < lam[t].length := by rw [hent.1]; exact hx
  have g1 := Det.get' hL hT (show (lam.map natList)[t]? = some (natList lam[t]) by simp [ht])
  have g2 := Det.get' g1 hX (show (lam[t].map Val.nat)[x]? = some (.nat lam[t][x]) by simp [hxl])
  have h := Det.arith (op := .eq) g2 (Det.nat (P := johnProgram) (env := [a]) 1)
  have hv : Val.nat (BinOp.eval .eq lam[t][x] 1) = boolVal (johnQO lam x (.nat t)) := by
    simp only [boolVal, johnQO, johnNatOf, BinOp.eval, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem ht, List.getElem?_eq_getElem hxl, Option.getD_some]
    by_cases e : lam[t][x] = 1 <;> simp [e]
  rw [hv] at h
  refine FunDet.intro john_at_outP.single (h.mono ?_)
  have wa := john_wt_acc ha
  have wt1 : (natList lam[t]).wt < (Val.list (lam.map natList)).wt :=
    wt_le_wt_list (List.mem_map_of_mem (List.getElem_mem ht))
  have e1 := wt_list2_le (Val.list (lam.map natList)) (.nat x)
  have e2 := wt_list2_le c (.nat t)
  have ec : c.wt = (Val.list [.list (lam.map natList), .nat x]).wt := rfl
  have ea : a.wt = (Val.list [c, .nat t]).wt := rfl
  have hb : lam[t][x] ≤ 1 := hent.2 _ (List.getElem_mem hxl)
  have w1 := wt_nat_le x; have w2 := wt_nat_le t; have w3 := wt_nat_le lam[t][x]
  have w4 := wt_nat_le 0; have w5 := wt_nat_le 1
  have w9 : (boolVal (johnQO lam x (.nat t))).wt ≤ 3 := wt_boolVal_le _
  have hlen := ha.len
  have y0 := john_le_sq n
  omega

/-- **The filter of the output for the point `x`.** -/
theorem john_filterOut_spec (ha : JohnAccOK n lam) {x : ℕ} (hx : x < n) :
    FunDet johnProgram 102
      (.list [.list [.list (lam.map natList), .nat x], natList (List.range lam.length)])
      (natList (johnOutRow lam x)) (1000000 * (n + 1) ^ 3) := by
  have hF := filter_spec john_at_filterOut (c := .list [.list (lam.map natList), .nat x])
    (xs := (List.range lam.length).map Val.nat) (q := johnQO lam x)
    (B := fun _ => 2000 * (n + 1) ^ 2) (by
      intro v hv
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
      exact john_outP_spec ha hx (List.mem_range.mp ht))
  have e : Val.list (((List.range lam.length).map Val.nat).filter (johnQO lam x)) =
      natList (johnOutRow lam x) := by
    simp only [natList, johnOutRow, List.filter_map]
    rfl
  refine hF.mono ?_
  rintro w cost ⟨rfl, hc⟩
  refine ⟨e, hc.trans ?_⟩
  rw [e]
  have hlen := ha.len
  have hsum := john_sum_le (l := (List.range lam.length).map Val.nat)
    (f := fun _ => 2000 * (n + 1) ^ 2) (B := 2000 * (n + 1) ^ 2) fun _ _ => le_rfl
  simp only [List.length_map, List.length_range] at hsum
  have wa := john_wt_acc ha
  have wR : (natList (List.range lam.length)).wt ≤ 5 * (n + 1) ^ 2 :=
    wt_natList_le_sq (fun v hv => by simp only [List.mem_range] at hv; omega) (by simpa using hlen)
  have wB : (natList (johnOutRow lam x)).wt ≤ 5 * (n + 1) ^ 2 :=
    wt_natList_le_sq (fun v hv => by
        simp only [johnOutRow, List.mem_filter, List.mem_range] at hv; omega)
      (by simp only [johnOutRow]; exact (List.length_filter_le _ _).trans (by simpa using hlen))
  have e1 := wt_list2_le (Val.list (lam.map natList)) (.nat x)
  have e2 := wt_list2_le (.list [.list (lam.map natList), .nat x])
    (natList (List.range lam.length))
  have hRn : natList (List.range lam.length) = Val.list ((List.range lam.length).map Val.nat) :=
    rfl
  rw [hRn] at e2 wR
  have w1 := wt_nat_le x
  have y0 := john_le_sq n
  set A := (Val.list [.list [.list (lam.map natList), .nat x],
    .list ((List.range lam.length).map Val.nat)]).wt
  have hA : A + lam.length + (natList (johnOutRow lam x)).wt + 1 ≤ 200 * (n + 1) ^ 2 := by
    omega
  have p1 : lam.length * (2000 * (n + 1) ^ 2) ≤ 2000 * (n + 1) ^ 3 := by
    calc lam.length * (2000 * (n + 1) ^ 2) ≤ (n + 1) * (2000 * (n + 1) ^ 2) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 2000 * (n + 1) ^ 3 := by ring
  have p2 : loopModK * (lam.length + 1) * (A + lam.length + (natList (johnOutRow lam x)).wt + 1) ≤
      1000 * (200 * (n + 1) ^ 3) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc (lam.length + 1) * (A + lam.length + (natList (johnOutRow lam x)).wt + 1) ≤
          (n + 1) * (200 * (n + 1) ^ 2) := Nat.mul_le_mul (by omega) hA
      _ = 200 * (n + 1) ^ 3 := by ring
  simp only [List.length_map, List.length_range]
  omega

/-- **The output for the point `x`.** -/
theorem john_outF_spec (ha : JohnAccOK n lam) {x : ℕ} (hx : x < n) :
    FunDet johnProgram 101
      (.list [.list [.list (lam.map natList), natList (List.range lam.length)], .nat x])
      (natList (johnOutRow lam x)) (2000000 * (n + 1) ^ 3) := by
  set c := Val.list [.list (lam.map natList), natList (List.range lam.length)]
  set a := Val.list [c, .nat x]
  have hc : Det johnProgram [a] (arg 0) c (2 * a.wt + 5) := Det.arg' rfl
  have hL := Det.get' hc (Det.nat 0)
    (show [Val.list (lam.map natList), natList (List.range lam.length)][0]? =
      some (.list (lam.map natList)) from rfl)
  have hR := Det.get' hc (Det.nat 1)
    (show [Val.list (lam.map natList), natList (List.range lam.length)][1]? =
      some (natList (List.range lam.length)) from rfl)
  have hX : Det johnProgram [a] (arg 1) (.nat x) (2 * a.wt + 6) := Det.arg' rfl
  have hcall := Det.call (Det.mk2 (Det.mk2 hL hX) hR) (john_filterOut_spec ha hx)
  refine FunDet.intro john_at_outF.single (hcall.mono ?_)
  have hlen := ha.len
  have wa := john_wt_acc ha
  have wR : (natList (List.range lam.length)).wt ≤ 5 * (n + 1) ^ 2 :=
    wt_natList_le_sq (fun v hv => by simp only [List.mem_range] at hv; omega) (by simpa using hlen)
  have e1 := wt_list2_le (Val.list (lam.map natList)) (natList (List.range lam.length))
  have e2 := wt_list2_le c (.nat x)
  have e3 := wt_list2_le (Val.list (lam.map natList)) (.nat x)
  have e4 := wt_list2_le (.list [.list (lam.map natList), .nat x]) (natList (List.range lam.length))
  have ec : c.wt = (Val.list [.list (lam.map natList), natList (List.range lam.length)]).wt := rfl
  have ea : a.wt = (Val.list [c, .nat x]).wt := rfl
  have w1 := wt_nat_le x; have w4 := wt_nat_le 0; have w5 := wt_nat_le 1
  have wB : (natList (johnOutRow lam x)).wt ≤ 5 * (n + 1) ^ 2 :=
    wt_natList_le_sq (fun v hv => by
        simp only [johnOutRow, List.mem_filter, List.mem_range] at hv; omega)
      (by simp only [johnOutRow]; exact (List.length_filter_le _ _).trans (by simpa using hlen))
  have y0 := john_le_sq n
  have y23 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := john_pow_le (by omega) (by omega)
  omega

/-- **The output.** -/
theorem john_mapOut_spec (ha : JohnAccOK n lam) :
    FunDet johnProgram 98
      (.list [.list [.list (lam.map natList), natList (List.range lam.length)],
        natList (List.range n)])
      (.list ((johnOut n lam).map natList)) (10000000 * (n + 1) ^ 4) := by
  have hT := john_tab john_at_mapOut
    (c := .list [.list (lam.map natList), natList (List.range lam.length)])
    (n := n) (B := 2000000 * (n + 1) ^ 3) (G := fun x => natList (johnOutRow lam x))
    fun x hx => john_outF_spec ha hx
  have e : (List.range n).map (fun x => natList (johnOutRow lam x)) =
      (johnOut n lam).map natList := by
    simp only [johnOut, johnOutRow, List.map_map]
    rfl
  rw [e] at hT
  refine hT.mono ?_
  have hlen := ha.len
  have wa := john_wt_acc ha
  have wR : (natList (List.range lam.length)).wt ≤ 5 * (n + 1) ^ 2 :=
    wt_natList_le_sq (fun v hv => by simp only [List.mem_range] at hv; omega) (by simpa using hlen)
  have wRn := john_wt_Rn n
  have wO := john_wt_list_le (vs := (johnOut n lam).map natList) (B := 5 * (n + 1) ^ 2) (by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hv
    exact wt_natList_le_sq (fun v hv => by simp only [List.mem_filter, List.mem_range] at hv; omega)
      ((List.length_filter_le _ _).trans (by simpa using hlen)))
  simp only [List.length_map, johnOut, List.length_range] at wO
  have e0 : (Val.list ((johnOut n lam).map natList)).wt =
      (Val.list (((List.range n).map fun x => (List.range lam.length).filter
        fun t => decide ((lam.getD t []).getD x 0 = 1)).map natList)).wt := rfl
  have e1 := wt_list2_le (Val.list (lam.map natList)) (natList (List.range lam.length))
  have e2 := wt_list2_le (.list [.list (lam.map natList), natList (List.range lam.length)])
    (natList (List.range n))
  have y0 := john_le_sq n
  have p0 : n * (2 * (5 * (n + 1) ^ 2) + 1) ≤ 11 * (n + 1) ^ 3 := by
    calc _ ≤ (n + 1) * (11 * (n + 1) ^ 2) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  set A := (Val.list [.list [.list (lam.map natList), natList (List.range lam.length)],
    natList (List.range n)]).wt
  have y23 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := john_pow_le (by omega) (by omega)
  have hA : A + (Val.list ((johnOut n lam).map natList)).wt + 1 ≤ 200 * (n + 1) ^ 3 := by omega
  have p1 : n * (2000000 * (n + 1) ^ 3) ≤ 2000000 * (n + 1) ^ 4 := by
    calc n * (2000000 * (n + 1) ^ 3) ≤ (n + 1) * (2000000 * (n + 1) ^ 3) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 2000000 * (n + 1) ^ 4 := by ring
  have p2 : mapK * (n + 1) * (A + (Val.list ((johnOut n lam).map natList)).wt + 1) ≤
      1000 * (200 * (n + 1) ^ 4) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc (n + 1) * (A + (Val.list ((johnOut n lam).map natList)).wt + 1) ≤
          (n + 1) * (200 * (n + 1) ^ 3) := Nat.mul_le_mul_left _ hA
      _ = 200 * (n + 1) ^ 4 := by ring
  omega

end GI.Impl
