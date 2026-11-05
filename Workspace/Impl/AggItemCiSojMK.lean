module

public import Workspace.Impl.AggItemCiSojSD

@[expose] public section

/-! # Constructing rectangle-side indicators from the three-color table -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {q : ℕ}

/-- On `[side colors, a]`, test one of the three side colors. -/
def itcsMarkF (v : ℕ) : Expr := .arith .eq (.get (arg 0) (arg 1)) (.nat v)

/-- A common entry weight budget. -/
def itcsMarkW (q : ℕ) : ℕ := 100 * (q + 10)

/-- Cost of the full indicator table. -/
def itcsMarkC (q : ℕ) : ℕ :=
  q * (20 * (itcsMarkW q + 1)) + mapK * (q + 1) * (18 * q + 8 + 22 * (q + 1) ^ 2)

/-- The literal indicator entry program. -/
theorem itcs_mark_spec {Pg : Program} {f v : ℕ}
    (hf : Pg.funs[f]? = some (itcsMarkF v)) (lab : Fin q → ℕ)
    (hl : ∀ a, lab a ≤ 2) (hv : v ≤ 2) (a : Fin q) :
    FunDet Pg f (.list [encFun lab, .nat a]) (boolVal (decide (lab a = v)))
      (20 * (itcsMarkW q + 1)) := by
  let Bw := itcsMarkW q
  have hw := wt_encFun_le lab hl
  have ha := wt_nat_le (a : ℕ)
  have haq := a.isLt
  have wi : (Val.list [encFun lab, .nat a]).wt ≤ Bw := by
    have hh := wt_list2_le (encFun lab) (.nat a)
    dsimp only [Bw, itcsMarkW]
    omega
  let env : List Val := [.list [encFun lab, .nat a]]
  have tab : StDC Pg env (arg 0) (encFun lab) 3 0 Bw :=
    StDC.arg rfl wi (by dsimp [Bw,itcsMarkW]; omega) (by dsimp [Bw,itcsMarkW]; omega)
  have ai : StDC Pg env (arg 1) (.nat a) 3 0 Bw :=
    StDC.arg rfl wi (by dsimp [Bw,itcsMarkW]; omega) (by dsimp [Bw,itcsMarkW]; omega)
  have value := StDC.get tab ai (encFun_getElem? lab a)
    ((wt_nat_le _).trans (by have := hl a; dsimp [Bw,itcsMarkW]; omega))
  have test := StDC.arith' value (StDC.nat v (by dsimp [Bw,itcsMarkW]; omega)) (op := .eq)
    (z := (decide (lab a = v)).toNat)
    (by by_cases hh : lab a = v <;> simp [Machine.BinOp.eval_eq,hh])
    (by cases decide (lab a = v) <;> simp <;> dsimp [Bw,itcsMarkW] <;> omega)
  exact StDC.funDet hf test (by dsimp only [Bw]; omega)

/-- The map builds exactly the indicator of the selected color class. -/
theorem itcs_mark_table {Pg : Program} {mp f v : ℕ}
    (hm : Pg.HasAt mp (mapFuns mp f)) (hf : Pg.funs[f]? = some (itcsMarkF v))
    (lab : Fin q → ℕ) (hl : ∀ a, lab a ≤ 2) (hv : v ≤ 2) (hq : 1 ≤ q) :
    FunDet Pg mp (.list [encFun lab, natList (List.range q)])
      (encFun fun a => (decide (lab a = v)).toNat) (itcsMarkC q) := by
  have hb (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
  have hm' := it_tab hm (fun a => (decide (lab a = v)).toNat)
    (fun a => (hb _).trans hq)
    (fun a => itcs_mark_spec hf lab hl hv a)
  refine hm'.mono ?_
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  have hw := wt_encFun_le lab hl
  omega

/-- Polynomial round bound for the side indicators. -/
theorem itcs_mark_pbu : PBU fun _ W _ => itcsMarkC (2 * W + 3) := by
  simp only [itcsMarkC,itcsMarkW,mapK]
  norm_poly

end GI.Impl
