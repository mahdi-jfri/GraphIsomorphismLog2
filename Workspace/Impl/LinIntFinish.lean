import Workspace.Impl.LinIntLift

/-! The deterministic part of the rectangular row solver: copy the Hermite
block, substitute, zero-extend and lift. -/
namespace GI.Impl
open GI.Cited GI.Lang Matrix

/-- Input [r,U,H,w]; the column count is the length of w. -/
def linHermiteFinishF (take tri lift : ℕ) : Expr :=
  .letE (.call take (mk2 (.length (arg 3)) (arg 2)))
    (.letE (.call tri (mk2 (.var 1) (arg 3)))
      (.call lift (mk3 (arg 0) (arg 1) (.var 2))))

def linHermiteFinishArg (W : ℕ) : ℕ := 10 * (W + 1)
def linHermiteFinishLiftArg (W r c B C : ℕ) : ℕ := 10 * (W + r + linTriCost c B C + 1)
def linHermiteFinishCost (W r c B C : ℕ) : ℕ :=
  1000 * (W + r + linTakeCost (linHermiteFinishArg W) + linTriCost c B C +
    linHermiteLiftCost (linHermiteFinishLiftArg W r c B C) r + 1)

/-- The copied prefix is exactly the square block used by the pure solver. -/
theorem linHermiteBlock_value {r c : ℕ} (hcr : c ≤ r) (H : Matrix (Fin r) (Fin c) ℤ) :
    encIntMatrix (linHermiteBlock hcr H) = .list
      (((List.finRange r).map fun i => linVecVal (H i)).take c) := by
  rw [linTakeFinMap hcr]
  rfl

set_option maxHeartbeats 1000000 in
theorem linHermiteFinish_spec {P : Program} {f take tri lift : ℕ}
    {TI : linTriIndices} {LI : linLiftIndices}
    (hf : P.funs[f]? = some (linHermiteFinishF take tri lift))
    (ht : P.HasAt take (linTakeFuns take))
    (htri : linTriInstalled P TI) (htriF : P.funs[tri]? = some (linTriUpperF tri TI))
    (hl : linLiftInstalled P LI) (hlF : P.funs[lift]? = some (linHermiteLiftF LI))
    {r c : ℕ} (hcr : c ≤ r) (U : Matrix (Fin r) (Fin r) ℤ)
    (H : Matrix (Fin r) (Fin c) ℤ) (w : Fin c → ℤ)
    (B C : ℕ) (hH : EntriesBits B H) (hw : ∀ i, (w i).natAbs < 2 ^ C) :
    FunDet P f (.list [.nat r, encIntMatrix U, encIntMatrix H, linVecVal w])
      (linTriVal (linHermiteSolve hcr U H w))
      (linHermiteFinishCost (Val.list [.nat r, encIntMatrix U, encIntMatrix H, linVecVal w]).wt r c B C) := by
  let a := Val.list [.nat r, encIntMatrix U, encIntMatrix H, linVecVal w]
  let W := a.wt
  let block := linHermiteBlock hcr H
  let s := linUpperSolve c block w
  have wm : (encIntMatrix H).wt < W := wt_le_wt_list (by simp)
  have wu : (encIntMatrix U).wt < W := wt_le_wt_list (by simp)
  have ww : (linVecVal w).wt < W := wt_le_wt_list (by simp)
  have wr : (Val.nat r).wt < W := wt_le_wt_list (by simp)
  have wc : c < W := by
    have hh := length_lt_wt_list ((List.finRange c).map fun i => encInt (w i))
    simp only [List.length_map, List.length_finRange] at hh
    exact hh.trans ww
  have wtarg := wt_list2_le (.nat c) (encIntMatrix H)
  have wcn := wt_nat_le c
  have wtake : (Val.list [.nat c, encIntMatrix H]).wt ≤ linHermiteFinishArg W := by
    unfold linHermiteFinishArg; omega
  have ht0 := linTake_spec ht ((List.finRange r).map fun i => linVecVal (H i)) c (by simpa using hcr)
  rw [← linHermiteBlock_value hcr H] at ht0
  have ht1 := ht0.mono (linTakeCost_mono wtake)
  have wb := ht1.wt_lt.le
  have hts := linTriUpper_spec htri htriF c block w B C (fun i j => hH _ _) hw
  have wta := wt_list2_le (encIntMatrix block) (linVecVal w)
  have ws : (linTriVal s).wt ≤ linTriCost c B C := hts.wt_lt.le
  have wla := wt_list3_le (.nat r) (encIntMatrix U) (linTriVal s)
  have wlift : (Val.list [.nat r, encIntMatrix U, linTriVal s]).wt ≤ linHermiteFinishLiftArg W r c B C := by
    unfold linHermiteFinishLiftArg; omega
  have hls := (linHermiteLift_spec hl hlF hcr U s).mono (linHermiteLiftCost_mono wlift r)
  have wo := hls.wt_lt.le
  have darg (j : ℕ) (rest : List Val) {z : Val}
      (hz : [.nat r, encIntMatrix U, encIntMatrix H, linVecVal w][j]? = some z) :=
    Det.arg' (P := P) (vs := [.nat r, encIntMatrix U, encIntMatrix H, linVecVal w]) (rest := rest) (j := j) hz
  have dl := Det.length (darg 3 [] rfl)
  simp only [List.length_map, List.length_finRange] at dl
  have dt := Det.call (Det.mk2 dl (darg 2 [] rfl)) ht1
  have ds := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, encIntMatrix block]) (i := 1) rfl)
    (darg 3 [encIntMatrix block] rfl)) hts
  have df := Det.call (Det.mk3 (darg 0 [encIntMatrix block, linTriVal s] rfl)
    (darg 1 [encIntMatrix block, linTriVal s] rfl)
    (Det.var' (P := P) (env := [a, encIntMatrix block, linTriVal s]) (i := 2) rfl)) hls
  apply FunDet.intro hf
  refine (Det.letE dt (Det.letE ds df)).mono ?_
  change _ ≤ linHermiteFinishCost W r c B C
  unfold linHermiteFinishCost
  simp only [linHermiteSolve, block, s, W, a] at *
  omega

end GI.Impl

namespace GI.Impl
open GI.Lang

theorem linHermiteFinishCost_mono {W V : ℕ} (h : W ≤ V) (r c B C : ℕ) :
    linHermiteFinishCost W r c B C ≤ linHermiteFinishCost V r c B C := by
  have ht : linTakeCost (linHermiteFinishArg W) ≤ linTakeCost (linHermiteFinishArg V) :=
    linTakeCost_mono (by unfold linHermiteFinishArg; omega)
  have hl := linHermiteLiftCost_mono
    (show linHermiteFinishLiftArg W r c B C ≤ linHermiteFinishLiftArg V r c B C by
      unfold linHermiteFinishLiftArg; omega) r
  unfold linHermiteFinishCost
  omega
end GI.Impl
