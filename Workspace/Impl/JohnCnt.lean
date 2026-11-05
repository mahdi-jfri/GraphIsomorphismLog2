module

public import Workspace.Impl.JohnOut

@[expose] public section

/-!
# The counts of row `0`

The function at `48` maps `johnCntF` over the row: for each entry `j`, the number of entries equal
to `j` (`john_mapCnt_spec`). It computes `johnCnt`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

/-- **The count of one entry.** -/
theorem john_cntF_spec {row : List ℕ} {B j : ℕ} (hB : ∀ x ∈ row, x ≤ B) (hl : row.length ≤ B)
    (hj : j ≤ B) :
    FunDet johnProgram 51 (.list [natList row, .nat j]) (.nat (row.count j))
      (countK * (B + 1) ^ 3 + 200 * (B + 1) ^ 2) := by
  set a := Val.list [natList row, .nat j]
  have h0 : Det johnProgram [a] (arg 0) (natList row) (2 * a.wt + 5) := Det.arg' rfl
  have h1 : Det johnProgram [a] (arg 1) (.nat j) (2 * a.wt + 6) := Det.arg' rfl
  have hcall := Det.call (Det.mk2 h1 h0) (count_spec john_at_count hB hj hl)
  refine FunDet.intro john_at_cntF.single (hcall.mono ?_)
  have wr := wt_natList_le_sq hB hl
  have e1 := wt_list2_le (natList row) (.nat j)
  have e2 := wt_list2_le (.nat j) (natList row)
  have ea : a.wt = (Val.list [natList row, .nat j]).wt := rfl
  have w1 := wt_nat_le j
  have w2 := wt_nat_le (row.count j)
  have hc : row.count j ≤ B := (List.count_le_length).trans hl
  have y0 := john_le_sq B
  omega

theorem john_wt_list_nat {xs : List ℕ} : Val.list (xs.map Val.nat) = natList xs := rfl

/-- **The counts of the row.** -/
theorem john_mapCnt_spec {row : List ℕ} {B : ℕ} (hB : ∀ x ∈ row, x ≤ B) (hl : row.length ≤ B) :
    FunDet johnProgram 48 (.list [natList row, natList row]) (natList (johnCnt row))
      (countK * (B + 1) ^ 4 + 2000000 * (B + 1) ^ 3) := by
  have hM := map_spec john_at_mapCnt (c := natList row) (xs := row.map Val.nat)
    (R := fun x w => ∃ j, x = .nat j ∧ w = .nat (row.count j))
    (B := fun _ => countK * (B + 1) ^ 3 + 200 * (B + 1) ^ 2) (by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      exact FunAll.mono (john_cntF_spec hB hl (hB j hj)) fun w c h => ⟨⟨j, rfl, h.1⟩, h.2⟩)
  refine hM.mono fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have hws' : ws = row.map fun j => .nat (row.count j) :=
    forall₂_map_eq (fun a _ w hR => by
      obtain ⟨j, hj, rfl⟩ := hR
      cases hj
      rfl) hws
  subst hws'
  have e : Val.list (row.map fun j => Val.nat (row.count j)) = natList (johnCnt row) := by
    simp [natList, johnCnt, List.map_map, Function.comp_def]
  refine ⟨e, ?_⟩
  rw [e] at hc
  refine hc.trans ?_
  have hsum : ((row.map Val.nat).map fun _ => countK * (B + 1) ^ 3 + 200 * (B + 1) ^ 2).sum ≤
      (row.map Val.nat).length * (countK * (B + 1) ^ 3 + 200 * (B + 1) ^ 2) :=
    john_sum_le fun _ _ => le_rfl
  rw [List.length_map] at hsum
  have wr := wt_natList_le_sq hB hl
  have wc : (natList (johnCnt row)).wt ≤ 5 * (B + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by
        simp only [johnCnt, List.mem_map] at hx
        obtain ⟨j, -, rfl⟩ := hx
        exact (List.count_le_length).trans hl)
      (by simpa [johnCnt] using hl)
  have e2 := wt_list2_le (natList row) (natList row)
  rw [john_wt_list_nat]
  simp only [List.length_map]
  have y0 := john_le_sq B
  have p1 : row.length * (countK * (B + 1) ^ 3 + 200 * (B + 1) ^ 2) ≤
      countK * (B + 1) ^ 4 + 200 * (B + 1) ^ 3 := by
    calc _ ≤ (B + 1) * (countK * (B + 1) ^ 3 + 200 * (B + 1) ^ 2) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have p2 : mapK * (row.length + 1) * ((Val.list [natList row, natList row]).wt +
      (natList (johnCnt row)).wt + 1) ≤ 1000 * (200 * (B + 1) ^ 3) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc _ ≤ (B + 1) * (200 * (B + 1) ^ 2) := Nat.mul_le_mul (by omega) (by omega)
      _ = 200 * (B + 1) ^ 3 := by ring
  omega

end GI.Impl
