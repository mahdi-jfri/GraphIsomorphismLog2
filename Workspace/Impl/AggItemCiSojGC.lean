import Workspace.Impl.AggItemCiSojGuard

/-! # Comparing rectangle sides by their literal three-color counts -/

set_option maxRecDepth 2048

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val)

variable {q : ℕ}

/-- Counting a tabulated color is the size of its actual color class. -/
theorem itcs_count_card (f : Fin q → ℕ) (s : ℕ) :
    (acpLabs f).count s = (Finset.univ.filter fun a => f a = s).card := by
  classical
  rw [ac_card_filter, acpLabs, List.count, List.countP_map, List.countP_eq_length_filter]
  congr 1

/-- The left-side color count is the actual left-side size. -/
theorem itcs_count_left (W R : Finset (Fin q)) : (acpLabs (itcsSide W R)).count 2 = W.card := by
  rw [itcs_count_card]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, itcs_side_left]

/-- For disjoint sides the right-side count is the right-side size. -/
theorem itcs_count_right {W R : Finset (Fin q)} (hd : Disjoint W R) :
    (acpLabs (itcsSide W R)).count 1 = R.card := by
  rw [itcs_count_card]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, itcs_side_right hd]

/-- On `[source sides, target sides]`, compare the left and right counts. -/
def itcsGuardF (cnt : ℕ) : Expr :=
  let count (i v : ℕ) := Expr.call cnt (mk2 (.nat v) (arg i))
  .arith .mul (.arith .eq (count 0 2) (count 1 2)) (.arith .eq (count 0 1) (count 1 1))

/-- A weight budget for the two three-color tables. -/
def itcsGuardW (q : ℕ) : ℕ := 100 * (q + 1) ^ 2

/-- Cost of the four counts and the two comparisons. -/
def itcsGuardC (q : ℕ) : ℕ := 100 * (itcsGuardW q + 1) + 4 * countK * (q + 3) ^ 3

open Classical in
/-- The finite side-size guard as a program. -/
theorem itcs_guard_prog {Pg : Program} {f cnt : ℕ}
    (hf : Pg.funs[f]? = some (itcsGuardF cnt)) (hc : Pg.HasAt cnt (countFuns cnt))
    (W R W' R' : Finset (Fin q)) (hd : Disjoint W R) (hd' : Disjoint W' R') :
    FunDet Pg f (.list [encFun (itcsSide W R), encFun (itcsSide W' R')])
      (boolVal (decide (W.card = W'.card ∧ R.card = R'.card))) (itcsGuardC q) := by
  let src := itcsSide W R
  let tgt := itcsSide W' R'
  let Bw := itcsGuardW q
  have hle (U V : Finset (Fin q)) (a : Fin q) : itcsSide U V a ≤ 2 := by
    unfold itcsSide
    split_ifs <;> omega
  have sx := wt_encFun_le src (hle W R)
  have sy := wt_encFun_le tgt (hle W' R')
  have hq1 : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hi : (Val.list [encFun src, encFun tgt]).wt ≤ Bw := by
    have h := wt_list2_le (encFun src) (encFun tgt)
    dsimp only [Bw, itcsGuardW]
    omega
  let env : List Val := [.list [encFun src, encFun tgt]]
  have cnt {i v : ℕ} {lab : Fin q → ℕ}
      (hi' : [encFun src, encFun tgt][i]? = some (encFun lab)) (hii : i ≤ 1)
      (hl : ∀ a, lab a ≤ 2) (hv : v ≤ 2) :
      StDC Pg env (.call cnt (mk2 (.nat v) (arg i))) (.nat ((acpLabs lab).count v))
        8 (countK * (q + 3) ^ 3) Bw := by
    have tab := StDC.arg (P := Pg) (rest := []) hi' hi (by dsimp [Bw, itcsGuardW]; omega)
      ((st_wt_mem (List.mem_of_getElem? hi')).trans hi)
    have hlw := wt_encFun_le lab hl
    have call := StDC.call (cb := countK * (q + 3) ^ 3) (StDC.mk2 (StDC.nat v (by dsimp [Bw, itcsGuardW]; omega)) tab
      (by have hh := wt_list2_le (.nat v) (encFun lab)
          have hn := wt_nat_le v
          dsimp [Bw, itcsGuardW]
          omega) (by dsimp [Bw, itcsGuardW]; omega))
      (by simpa only [acp_encFun, Nat.add_assoc] using
        (count_spec hc (B := q + 2) (xs := acpLabs lab) (j := v)
          (fun a ha => by obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha; exact (hl i).trans (by omega))
          (by omega) (by simp [acp_labs_length])))
      ((wt_nat_le _).trans (by
        have hh : (acpLabs lab).count v ≤ q := acp_count_le lab v
        dsimp [Bw, itcsGuardW]
        omega))
    exact call.mono (by omega) (by omega)
  have cl := cnt (i := 0) (v := 2) rfl (by omega) (hle W R) (by omega)
  have dl := cnt (i := 1) (v := 2) rfl (by omega) (hle W' R') (by omega)
  have cr := cnt (i := 0) (v := 1) rfl (by omega) (hle W R) (by omega)
  have dr := cnt (i := 1) (v := 1) rfl (by omega) (hle W' R') (by omega)
  simp only [src, tgt, itcs_count_left, itcs_count_right hd, itcs_count_right hd'] at cl dl cr dr
  have el := StDC.arith' cl dl (op := .eq)
    (z := if W.card = W'.card then 1 else 0) rfl (by split_ifs <;> dsimp [Bw, itcsGuardW] <;> omega)
  have er := StDC.arith' cr dr (op := .eq)
    (z := if R.card = R'.card then 1 else 0) rfl (by split_ifs <;> dsimp [Bw, itcsGuardW] <;> omega)
  have mul := StDC.arith' el er (op := .mul)
    (z := (decide (W.card = W'.card ∧ R.card = R'.card)).toNat)
    (by by_cases hW : W.card = W'.card <;> by_cases hR : R.card = R'.card
        <;> simp [Machine.BinOp.eval, hW, hR])
    (by cases decide (W.card = W'.card ∧ R.card = R'.card) <;> simp <;> dsimp [Bw, itcsGuardW] <;> omega)
  exact StDC.funDet hf mul (by dsimp only [itcsGuardC, Bw]; simp only [Nat.mul_assoc]; omega)

/-- Polynomial round bound for the rectangle guard. -/
theorem itcs_guard_pbu : PBU fun _ W _ => itcsGuardC (2 * W + 3) := by
  simp only [itcsGuardC, itcsGuardW, countK]
  norm_poly

end GI.Impl
