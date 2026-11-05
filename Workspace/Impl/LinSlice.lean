module

public import Workspace.Lang.Lib.LinIntVector
public import Workspace.Lang.Lib.LinIntTake
public import Workspace.Impl.GenNormPoly

@[expose] public section

/-! Copy a bounded slice of an encoded list. This extracts the common
translation coefficients from the last block of a Hermite solution. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linSliceStep : Expr := .snoc (arg 2)
  (.get (.get (arg 0) (.nat 2)) (.arith .add (.get (arg 0) (.nat 0)) (arg 1)))
def linSliceFuns (b : ℕ) : List Expr := loopFuns b (arg 1) .nil linSliceStep
theorem linSliceFuns_length (b : ℕ) : (linSliceFuns b).length = 3 := rfl
def linSliceCost (W : ℕ) : ℕ := 1000000 * (W + 1) ^ 3

set_option maxHeartbeats 1000000 in
theorem linSlice_spec {P : Program} {b : ℕ} (h : P.HasAt b (linSliceFuns b))
    (xs : List Val) (offset count : ℕ) (hx : offset + count ≤ xs.length) :
    let a := Val.list [.nat offset, .nat count, .list xs]
    FunDet P b a (.list ((xs.drop offset).take count)) (linSliceCost a.wt) := by
  let a := Val.list [.nat offset, .nat count, .list xs]
  let W := a.wt
  let ys := xs.drop offset
  have wx : (Val.list xs).wt < W := wt_le_wt_list (by simp [a, W])
  have hl := length_lt_wt_list xs
  have ho : offset ≤ W := by omega
  have hn : count ≤ W := by omega
  have hlen : count ≤ ys.length := by simp [ys]; omega
  have hacc (i : ℕ) : (Val.list (ys.take i)).wt ≤ W :=
    (wt_list_sublist ((List.take_sublist i ys).trans (List.drop_sublist offset xs))).trans wx.le
  have dk := Det.arg' (P := P) (vs := [.nat offset, .nat count, .list xs])
    (rest := []) (j := 1) rfl
  have hs := loopBdd_spec h dk Det.nil (by dsimp [a, W] at *; omega)
    (Inv := fun i acc => acc = .list (ys.take i)) (M := W) (D := fun _ => 10000 * (W + 1))
    (by simp) (fun i acc _ he => he ▸ hacc i) (fun i acc hi he => ?_)
  · refine hs.mono fun out cost ho => ⟨ho.1, ?_⟩
    have hc := ho.2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, loopModK] at hc
    have hmul := Nat.mul_le_mul_right (10000 * (W + 1)) hn
    have hctrl := Nat.mul_le_mul (Nat.mul_le_mul_left 1000 (Nat.add_le_add_right hn 1))
      (by omega : W + count + W + 1 ≤ 3 * W + 1)
    change cost ≤ linSliceCost W
    unfold linSliceCost
    nlinarith
  · subst he
    have hi' : i < xs.length - offset := by
      have := hi.trans_le hlen
      simpa only [ys, List.length_drop] using this
    have hxi : offset + i < xs.length := by omega
    have dorig := Det.arg' (P := P) (vs := [a, .nat i, .list (ys.take i)])
      (rest := []) (j := 0) rfl
    have di := Det.arg' (P := P) (vs := [a, .nat i, .list (ys.take i)])
      (rest := []) (j := 1) rfl
    have da := Det.arg' (P := P) (vs := [a, .nat i, .list (ys.take i)])
      (rest := []) (j := 2) rfl
    have doff := Det.get' dorig (Det.nat 0) rfl
    have dlist := Det.get' dorig (Det.nat 2) rfl
    have dix := Det.arith' (op := .add) doff di (z := offset + i) rfl
    have de := Det.get' dlist dix (List.getElem?_eq_getElem hxi)
    have dr := Det.snoc da de
    have heq : ys.take (i + 1) = ys.take i ++ [xs[offset + i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simpa [ys] using hi')]
      simp [ys, List.getElem_drop, Nat.add_comm]
    refine dr.post fun cost hc => ⟨?_, ?_⟩
    · change Val.list (ys.take i ++ [xs[offset + i]]) = Val.list (ys.take (i + 1))
      rw [heq]
    · suffices hcost : cost ≤ 10000 * (W + 1) from hcost.trans (Nat.le_add_right _ _)
      have wi := wt_nat_le i
      have wstep := wt_list3_le a (.nat i) (.list (ys.take i))
      have wa := hacc i
      have wb := hacc (i + 1)
      rw [heq] at wb
      have we := wt_getElem_lt xs (offset + i) hxi
      have woff := wt_nat_le offset
      dsimp only [a, W] at *
      omega

theorem linSlice_vec_value {r c offset : ℕ} (z : Fin r → ℤ) (hc : offset + c ≤ r) :
    (Val.list ((((List.finRange r).map fun i => encInt (z i)).drop offset).take c)) =
      linVecVal (fun i : Fin c => z ⟨offset + i.val, by omega⟩) := by
  apply congrArg Val.list
  apply List.ext_getElem (by simp [linVecVal]; omega)
  intro i hi hj
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_finRange]
  rfl

theorem linSlice_vec_spec {P : Program} {b r c offset : ℕ}
    (h : P.HasAt b (linSliceFuns b)) (z : Fin r → ℤ) (hc : offset + c ≤ r) :
    FunDet P b (.list [.nat offset, .nat c, linVecVal z])
      (linVecVal (fun i : Fin c => z ⟨offset + i.val, by omega⟩))
      (linSliceCost (Val.list [.nat offset, .nat c, linVecVal z]).wt) := by
  have hs := linSlice_spec h ((List.finRange r).map fun i => encInt (z i)) offset c
    (by simpa using hc)
  rw [linSlice_vec_value z hc] at hs
  exact hs

theorem linSliceCost_poly : PBU (fun _ W _ => linSliceCost W) := by
  unfold linSliceCost
  norm_poly

end GI.Impl
