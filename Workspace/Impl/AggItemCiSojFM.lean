import Workspace.Impl.AggItemCiSojMK
import Workspace.Impl.AggItemCiSojFG

/-! # Constructing the pointwise-fixing marker coloring -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {q : ℕ}

/-- Give each left-side point its own color and color the other points zero. -/
def itcsFixFrom (lab : Fin q → ℕ) (a : Fin q) : ℕ := if lab a = 2 then a.val + 1 else 0

/-- The table represents precisely the pointwise-fixing subgroup used by `leftGroup`. -/
theorem itcs_fix_from_side (W R : Finset (Fin q)) :
    itcsFixFrom (itcsSide W R) = itcsFixColor W := by
  funext a
  simp only [itcsFixFrom,itcsFixColor,itcs_side_left]

/-- Literal marker-color entry on `[side table,a]`. -/
def itcsFixMarkF : Expr :=
  .ite (.arith .eq (.get (arg 0) (arg 1)) (.nat 2))
    (.arith .add (arg 1) (.nat 1)) (.nat 0)

/-- The marker entry uses the same bounded three-color table as the side indicators. -/
theorem itcs_fix_marker {Pg : Program} {f : ℕ}
    (hf : Pg.funs[f]? = some itcsFixMarkF) (lab : Fin q → ℕ)
    (hl : ∀ a, lab a ≤ 2) (a : Fin q) :
    FunDet Pg f (.list [encFun lab, .nat a]) (.nat (itcsFixFrom lab a))
      (30 * (itcsMarkW q + 1)) := by
  classical
  let Bw := itcsMarkW q
  have hw := wt_encFun_le lab hl
  have ha := wt_nat_le (a : ℕ)
  have haq := a.isLt
  have wi : (Val.list [encFun lab,.nat a]).wt ≤ Bw := by
    have hh := wt_list2_le (encFun lab) (.nat a)
    dsimp only [Bw,itcsMarkW]
    omega
  let env : List Val := [.list [encFun lab,.nat a]]
  have tab : StDC Pg env (arg 0) (encFun lab) 3 0 Bw :=
    StDC.arg rfl wi (by dsimp [Bw,itcsMarkW]; omega) (by dsimp [Bw,itcsMarkW]; omega)
  have ai : StDC Pg env (arg 1) (.nat a) 3 0 Bw :=
    StDC.arg rfl wi (by dsimp [Bw,itcsMarkW]; omega) (by dsimp [Bw,itcsMarkW]; omega)
  have value := StDC.get tab ai (encFun_getElem? lab a)
    ((wt_nat_le _).trans (by have := hl a; dsimp [Bw,itcsMarkW]; omega))
  have test := StDC.arith' value (StDC.nat 2 (by dsimp [Bw,itcsMarkW]; omega)) (op := .eq)
    (z := if lab a = 2 then 1 else 0) rfl (by split_ifs <;> dsimp [Bw,itcsMarkW] <;> omega)
  have add := StDC.arith' ai (StDC.nat 1 (by dsimp [Bw,itcsMarkW]; omega)) (op := .add)
    (z := a.val + 1) rfl (by dsimp [Bw,itcsMarkW]; omega)
  have wo : (Val.nat (itcsFixFrom lab a)).wt ≤ Bw := by
    apply (wt_nat_le _).trans
    unfold itcsFixFrom
    split_ifs <;> dsimp [Bw,itcsMarkW] <;> omega
  have body : StDC Pg env itcsFixMarkF (.nat (itcsFixFrom lab a)) 25 0 Bw := by
    unfold itcsFixFrom at wo ⊢
    by_cases hh : lab a = 2
    · simp only [if_pos hh] at test wo ⊢
      exact (StDC.ite (nt := 5) (ne := 1) (Et := 0) (Ee := 0) test (fun _ => add)
        (fun h => by omega) wo).mono (by omega) (by omega)
    · simp only [if_neg hh] at test wo ⊢
      exact (StDC.ite (nt := 5) (ne := 1) (Et := 0) (Ee := 0) test (fun h => by omega)
        (fun _ => StDC.nat 0 (by dsimp [Bw,itcsMarkW]; omega)) wo).mono (by omega) (by omega)
  exact StDC.funDet hf body (by dsimp only [Bw]; omega)

/-- Cost of the full marker table. -/
def itcsFixMarkC (q : ℕ) : ℕ :=
  q * (30 * (itcsMarkW q + 1)) + mapK * (q + 1) * (18 * q + 8 + 22 * (q + 1) ^ 2)

/-- Every marker color is at most the label degree. -/
theorem itcs_fix_from_le (lab : Fin q → ℕ) (a : Fin q) : itcsFixFrom lab a ≤ q := by
  unfold itcsFixFrom
  split_ifs
  · exact a.isLt
  · exact Nat.zero_le _

/-- The actual table map for the even pointwise-fixing subgroup. -/
theorem itcs_fix_mark_table {Pg : Program} {mp f : ℕ}
    (hm : Pg.HasAt mp (mapFuns mp f)) (hf : Pg.funs[f]? = some itcsFixMarkF)
    (lab : Fin q → ℕ) (hl : ∀ a,lab a ≤ 2) :
    FunDet Pg mp (.list [encFun lab,natList (List.range q)])
      (encFun (itcsFixFrom lab)) (itcsFixMarkC q) := by
  have hh := it_tab hm (itcsFixFrom lab) (itcs_fix_from_le lab)
    (fun a => itcs_fix_marker hf lab hl a)
  refine hh.mono ?_
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  have hw := wt_encFun_le lab hl
  omega

/-- Polynomial round bound for the pointwise marker map. -/
theorem itcs_fix_mark_pbu : PBU fun _ W _ => itcsFixMarkC (2 * W + 3) := by
  simp only [itcsFixMarkC,itcsMarkW,mapK]
  norm_poly

end GI.Impl
