module

public import Workspace.Impl.LinIntSlpTrace
public import Workspace.Impl.LinMapEncoded

@[expose] public section

/-! A shared-entry SLP interpreter for any group with encoded multiplication
and inversion programs. Full affine transformations are one application. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linGroupSlpTable {G : Type*} (enc : G → Val) (xs : List G) : Val := .list (xs.map enc)

def linGroupSlpStepF (mul inv : ℕ) : Expr :=
  .ite (.arith .eq (.get (arg 2) (.nat 0)) (.nat 0))
    (.get (arg 0) (.get (arg 2) (.nat 1)))
    (.ite (.arith .eq (.get (arg 2) (.nat 0)) (.nat 1))
      (.call inv (.get (arg 1) (.get (arg 2) (.nat 1))))
      (.call mul (mk2 (.get (arg 1) (.get (arg 2) (.nat 1)))
        (.get (arg 1) (.get (arg 2) (.nat 2))))))

def linGroupSlpStepCost (W B C : ℕ) : ℕ := 100000 * (W + B + C + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linGroupSlpStep_spec {G : Type*} [Group G] {P : Program} {f mul inv B C : ℕ}
    (hf : P.funs[f]? = some (linGroupSlpStepF mul inv)) (enc : G → Val)
    (hB : ∀ x, (enc x).wt ≤ B)
    (hm : ∀ x y, FunDet P mul (.list [enc x, enc y]) (enc (x * y)) C)
    (hi : ∀ x, FunDet P inv (enc x) (enc x⁻¹) C)
    (gs acc : List G) (ins : SlpInstr) (x : G) (hx : linSlpStep gs acc ins = some x) :
    FunDet P f (.list [linGroupSlpTable enc gs, linGroupSlpTable enc acc, encSlpInstr ins])
      (enc x) (linGroupSlpStepCost
        (Val.list [linGroupSlpTable enc gs, linGroupSlpTable enc acc, encSlpInstr ins]).wt B C) := by
  let a := Val.list [linGroupSlpTable enc gs, linGroupSlpTable enc acc, encSlpInstr ins]
  let W := a.wt
  have wg : (linGroupSlpTable enc gs).wt < W := wt_le_wt_list (by simp [W, a])
  have wa : (linGroupSlpTable enc acc).wt < W := wt_le_wt_list (by simp [W, a])
  have wi : (encSlpInstr ins).wt < W := wt_le_wt_list (by simp [W, a])
  have da (j : ℕ) {v : Val} (hv : [linGroupSlpTable enc gs, linGroupSlpTable enc acc, encSlpInstr ins][j]? = some v) :=
    Det.arg' (P := P) (vs := [linGroupSlpTable enc gs, linGroupSlpTable enc acc, encSlpInstr ins])
      (rest := []) (j := j) hv
  have get {xs : List G} {y : G} {j : ℕ} {e idx : Expr} {ce ci : ℕ}
      (de : Det P [a] e (linGroupSlpTable enc xs) ce) (dj : Det P [a] idx (.nat j) ci)
      (hj : xs[j]? = some y) :
      Det P [a] (.get e idx) (enc y) (ce + ci + (enc y).wt + 1) :=
    Det.get' de dj (by simp only [linGroupSlpTable, List.getElem?_map, hj, Option.map_some])
  have w0 : (Val.nat 0).wt = 2 := by decide
  have w1 : (Val.nat 1).wt = 3 := by decide
  have w2 : (Val.nat 2).wt = 4 := by decide
  cases ins with
  | gen j =>
    have hj : gs[j]? = some x := hx
    have wj : (Val.nat j).wt < W :=
      (wt_le_wt_list (by simp : Val.nat j ∈ [.nat 0, .nat j])).trans wi
    have dj := Det.get' (da 2 rfl) (Det.nat 1) rfl
    have dt := Det.arith' (op := .eq) (Det.get' (da 2 rfl) (Det.nat 0) rfl) (Det.nat 0)
      (show GI.Machine.BinOp.eval .eq 0 0 = 1 from rfl)
    have dd := get (da 0 rfl) dj hj
    apply FunDet.intro hf
    refine (Det.ite_pos dt (by decide) dd).mono ?_
    have wx := hB x
    unfold linGroupSlpStepCost
    dsimp only [W, a, encSlpInstr] at *
    omega
  | inv j =>
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
    have wj : (Val.nat j).wt < W :=
      (wt_le_wt_list (by simp : Val.nat j ∈ [.nat 1, .nat j])).trans wi
    have dj := Det.get' (da 2 rfl) (Det.nat 1) rfl
    have dy := get (da 1 rfl) dj hy
    have dc := Det.call dy (hi y)
    have dt := Det.arith' (op := .eq) (Det.get' (da 2 rfl) (Det.nat 0) rfl) (Det.nat 0)
      (show GI.Machine.BinOp.eval .eq 1 0 = 0 from rfl)
    have dt1 := Det.arith' (op := .eq) (Det.get' (da 2 rfl) (Det.nat 0) rfl) (Det.nat 1)
      (show GI.Machine.BinOp.eval .eq 1 1 = 1 from rfl)
    apply FunDet.intro hf
    refine (Det.ite_zero dt (Det.ite_pos dt1 (by decide) dc)).mono ?_
    have wy := hB y
    have wz := hB y⁻¹
    unfold linGroupSlpStepCost
    dsimp only [W, a, encSlpInstr] at *
    omega
  | mul j k =>
    obtain ⟨y, hy⟩ : ∃ y, acc[j]? = some y := by
      cases hh : acc[j]? with
      | none => simp [linSlpStep, hh] at hx
      | some y => exact ⟨y, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z, acc[k]? = some z := by
      cases hh : acc[k]? with
      | none => simp [linSlpStep, hy, hh] at hx
      | some z => exact ⟨z, rfl⟩
    have he : x = y * z := by simpa [linSlpStep, hy, hz] using hx.symm
    subst x
    have wj : (Val.nat j).wt < W :=
      (wt_le_wt_list (by simp : Val.nat j ∈ [.nat 2, .nat j, .nat k])).trans wi
    have wk : (Val.nat k).wt < W :=
      (wt_le_wt_list (by simp : Val.nat k ∈ [.nat 2, .nat j, .nat k])).trans wi
    have dj := Det.get' (da 2 rfl) (Det.nat 1) rfl
    have dk := Det.get' (da 2 rfl) (Det.nat 2) rfl
    have dc := Det.call (Det.mk2 (get (da 1 rfl) dj hy) (get (da 1 rfl) dk hz)) (hm y z)
    have dt := Det.arith' (op := .eq) (Det.get' (da 2 rfl) (Det.nat 0) rfl) (Det.nat 0)
      (show GI.Machine.BinOp.eval .eq 2 0 = 0 from rfl)
    have dt1 := Det.arith' (op := .eq) (Det.get' (da 2 rfl) (Det.nat 0) rfl) (Det.nat 1)
      (show GI.Machine.BinOp.eval .eq 2 1 = 0 from rfl)
    apply FunDet.intro hf
    refine (Det.ite_zero dt (Det.ite_zero dt1 dc)).mono ?_
    have wy := hB y
    have wz := hB z
    have wyz := hB (y * z)
    have warg := wt_list2_le (enc y) (enc z)
    unfold linGroupSlpStepCost
    dsimp only [W, a, encSlpInstr] at *
    omega

end GI.Impl
