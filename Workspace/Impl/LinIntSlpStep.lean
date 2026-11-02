import Workspace.Impl.LinExponents
import Workspace.Lang.Lib.LinIntVector

/-! Evaluate one checked SLP instruction as an integer exponent vector.
The arithmetic functions below are proved programs, not primitives. -/
namespace GI.Impl
open GI.Cited GI.Lang

/-- The table of exponent vectors stored by the language interpreter. -/
def linSlpTable {t : ℕ} (xs : List (Multiplicative (Fin t → ℤ))) : Val :=
  .list (xs.map fun x => linVecVal (Multiplicative.toAdd x))

/-- Input [generator-vectors,previous-entries,instruction]. -/
def linSlpStepF (add scale : ℕ) : Expr :=
  .ite (.arith .eq (.get (arg 2) (.nat 0)) (.nat 0))
    (.get (arg 0) (.get (arg 2) (.nat 1)))
    (.ite (.arith .eq (.get (arg 2) (.nat 0)) (.nat 1))
      (.call scale (mk2 linIntMinusOneE (.get (arg 1) (.get (arg 2) (.nat 1)))))
      (.call add (mk2 (.get (arg 1) (.get (arg 2) (.nat 1)))
        (.get (arg 1) (.get (arg 2) (.nat 2))))))

def linSlpStepCost (W t : ℕ) : ℕ :=
  10000 * (W + t + linVectorScaleCost (10 * (W + 100)) t +
    linVectorBinaryCost (10 * (W + 100)) t (20 * (10 * (W + 100) + 2)) + 1)

/-- Reading a valid table entry uses exactly the corresponding exponent vector. -/
theorem linSlpGet {P : Program} {env : List Val} {e i : Expr} {t j : ℕ}
    {xs : List (Multiplicative (Fin t → ℤ))} {x : Multiplicative (Fin t → ℤ)} {ce ci : ℕ}
    (de : Det P env e (linSlpTable xs) ce) (di : Det P env i (.nat j) ci)
    (hx : xs[j]? = some x) :
    Det P env (.get e i) (linVecVal (Multiplicative.toAdd x))
      (ce + ci + (linVecVal (Multiplicative.toAdd x)).wt + 1) :=
  Det.get' de di (by simp only [List.getElem?_map, hx, Option.map_some])

set_option maxHeartbeats 1000000 in
theorem linSlpStep_spec {P : Program} {f add scale ib t : ℕ}
    (hf : P.funs[f]? = some (linSlpStepF add scale)) (hi : linIntSpec P ib)
    (ha : P.HasAt add (linVectorBinaryFuns add (ib + 11)))
    (hs : P.HasAt scale (linVectorScaleFuns scale ib))
    (gs acc : List (Multiplicative (Fin t → ℤ))) (ins : SlpInstr)
    (x : Multiplicative (Fin t → ℤ)) (hx : linSlpStep gs acc ins = some x) :
    FunDet P f (.list [linSlpTable gs, linSlpTable acc, encSlpInstr ins])
      (linVecVal (Multiplicative.toAdd x))
      (linSlpStepCost (Val.list [linSlpTable gs, linSlpTable acc, encSlpInstr ins]).wt t) := by
  let a := Val.list [linSlpTable gs, linSlpTable acc, encSlpInstr ins]
  let W := a.wt
  have wg : (linSlpTable gs).wt < W := wt_le_wt_list (by simp)
  have wa : (linSlpTable acc).wt < W := wt_le_wt_list (by simp)
  have wi : (encSlpInstr ins).wt < W := wt_le_wt_list (by simp)
  have darg (j : ℕ) {v : Val} (hv : [linSlpTable gs, linSlpTable acc, encSlpInstr ins][j]? = some v) :=
    Det.arg' (P := P) (vs := [linSlpTable gs, linSlpTable acc, encSlpInstr ins]) (rest := []) (j := j) hv
  have wtentry {xs : List (Multiplicative (Fin t → ℤ))} {v : Multiplicative (Fin t → ℤ)}
      (hxs : (linSlpTable xs).wt < W) (hv : v ∈ xs) : (linVecVal (Multiplicative.toAdd v)).wt < W :=
    (wt_le_wt_list (List.mem_map.mpr ⟨v, hv, rfl⟩)).trans hxs
  have wn0 : (Val.nat 0).wt = 2 := rfl
  have wn1 : (Val.nat 1).wt = 3 := rfl
  have wn2 : (Val.nat 2).wt = 4 := rfl
  cases ins with
  | gen j =>
    have wj : (Val.nat j).wt < W := (wt_le_wt_list (by simp : Val.nat j ∈ [Val.nat 0, Val.nat j])).trans wi
    have hx' : gs[j]? = some x := hx
    have wx := wtentry wg (List.mem_of_getElem? hx')
    have dj := Det.get' (darg 2 rfl) (Det.nat 1) rfl
    have dt := Det.arith' (op := .eq) (Det.get' (darg 2 rfl) (Det.nat 0) rfl)
      (Det.nat 0) (by rfl : GI.Machine.BinOp.eval .eq 0 0 = 1)
    have dx := linSlpGet (darg 0 rfl) dj hx'
    apply FunDet.intro hf
    refine (Det.ite_pos dt (by decide : 1 ≠ 0) dx).mono ?_
    unfold linSlpStepCost
    simp only [W, a, encSlpInstr] at *
    omega
  | inv j =>
    have wj : (Val.nat j).wt < W := (wt_le_wt_list (by simp : Val.nat j ∈ [Val.nat 1, Val.nat j])).trans wi
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
    have wy := wtentry wa (List.mem_of_getElem? hy)
    have wd := wt_list2_le (encInt (-1)) (linVecVal (Multiplicative.toAdd y))
    have wn : (encInt (-1)).wt ≤ 100 := by decide
    have wc : (Val.list [encInt (-1), linVecVal (Multiplicative.toAdd y)]).wt ≤ 10 * (W + 100) := by omega
    have hm := (linVectorScale_spec hi hs (-1) (Multiplicative.toAdd y)).mono
      (linVectorScaleCost_mono wc le_rfl)
    have we := hm.wt_lt.le
    have dj := Det.get' (darg 2 rfl) (Det.nat 1) rfl
    have dx := linSlpGet (darg 1 rfl) dj hy
    have dm := Det.call (Det.mk2
      (show Det P [a] linIntMinusOneE (encInt (-1)) _ from Det.mk2 (Det.nat 1) (Det.mk1 (Det.nat 1))) dx) hm
    have dt := Det.arith' (op := .eq) (Det.get' (darg 2 rfl) (Det.nat 0) rfl)
      (Det.nat 0) (by rfl : GI.Machine.BinOp.eval .eq 1 0 = 0)
    have dt1 := Det.arith' (op := .eq) (Det.get' (darg 2 rfl) (Det.nat 0) rfl)
      (Det.nat 1) (by rfl : GI.Machine.BinOp.eval .eq 1 1 = 1)
    have heq : (fun i => (-1 : ℤ) * Multiplicative.toAdd y i) = Multiplicative.toAdd y⁻¹ := by funext i; simp
    rw [heq] at dm we
    apply FunDet.intro hf
    refine (Det.ite_zero dt (Det.ite_pos dt1 (by decide : 1 ≠ 0) dm)).mono ?_
    unfold linSlpStepCost
    simp only [W, a, encSlpInstr] at *
    have wz0 : (Val.nat 0).wt = 2 := rfl
    have wz1 : (Val.nat 1).wt = 3 := rfl
    have wnil : (Val.list []).wt = 4 := rfl
    have wb1 : (Val.list [.nat 1]).wt ≤ 20 := by decide
    norm_num [encInt, Nat.bits] at *
    omega
  | mul j k =>
    have wj : (Val.nat j).wt < W := (wt_le_wt_list (by simp : Val.nat j ∈ [Val.nat 2, Val.nat j, Val.nat k])).trans wi
    have wk : (Val.nat k).wt < W := (wt_le_wt_list (by simp : Val.nat k ∈ [Val.nat 2, Val.nat j, Val.nat k])).trans wi
    obtain ⟨y, hy⟩ : ∃ y, acc[j]? = some y := by
      cases he : acc[j]? with
      | none => simp [linSlpStep, he] at hx
      | some y => exact ⟨y, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z, acc[k]? = some z := by
      cases he : acc[k]? with
      | none => simp [linSlpStep, hy, he] at hx
      | some z => exact ⟨z, rfl⟩
    have he : y * z = x := by simpa [linSlpStep, hy, hz] using hx
    subst x
    have wy := wtentry wa (List.mem_of_getElem? hy)
    have wz := wtentry wa (List.mem_of_getElem? hz)
    have wd := wt_list2_le (linVecVal (Multiplicative.toAdd y)) (linVecVal (Multiplicative.toAdd z))
    have wc : (Val.list [linVecVal (Multiplicative.toAdd y), linVecVal (Multiplicative.toAdd z)]).wt ≤ 10 * (W + 100) := by omega
    have hm := (linVectorAdd_spec hi ha (Multiplicative.toAdd y) (Multiplicative.toAdd z)).mono
      (linVectorBinaryCost_mono wc le_rfl (by omega : 20 * ((Val.list [linVecVal (Multiplicative.toAdd y), linVecVal (Multiplicative.toAdd z)]).wt + 2) ≤ 20 * (10 * (W + 100) + 2)))
    have we := hm.wt_lt.le
    have we2 : (linVecVal (Multiplicative.toAdd (y * z))).wt ≤ _ := we
    have dj := Det.get' (darg 2 rfl) (Det.nat 1) rfl
    have dk := Det.get' (darg 2 rfl) (Det.nat 2) rfl
    have dm := Det.call (Det.mk2 (linSlpGet (darg 1 rfl) dj hy) (linSlpGet (darg 1 rfl) dk hz)) hm
    have dt := Det.arith' (op := .eq) (Det.get' (darg 2 rfl) (Det.nat 0) rfl)
      (Det.nat 0) (by rfl : GI.Machine.BinOp.eval .eq 2 0 = 0)
    have dt1 := Det.arith' (op := .eq) (Det.get' (darg 2 rfl) (Det.nat 0) rfl)
      (Det.nat 1) (by rfl : GI.Machine.BinOp.eval .eq 2 1 = 0)
    apply FunDet.intro hf
    refine (Det.ite_zero dt (Det.ite_zero dt1 dm)).mono ?_
    unfold linSlpStepCost
    simp only [W, a, encSlpInstr] at *
    have wz0 : (Val.nat 0).wt = 2 := rfl
    have wz1 : (Val.nat 1).wt = 3 := rfl
    omega

end GI.Impl

namespace GI.Impl
open GI.Lang

theorem linSlpStepCost_mono {W V : ℕ} (h : W ≤ V) (t : ℕ) :
    linSlpStepCost W t ≤ linSlpStepCost V t := by
  have hs := linVectorScaleCost_mono (show 10 * (W + 100) ≤ 10 * (V + 100) by omega) (le_refl t)
  have ha := linVectorBinaryCost_mono (show 10 * (W + 100) ≤ 10 * (V + 100) by omega) (le_refl t)
    (show 20 * (10 * (W + 100) + 2) ≤ 20 * (10 * (V + 100) + 2) by omega)
  unfold linSlpStepCost
  omega
end GI.Impl
