import Workspace.Impl.LinObjectVectorRow
import Workspace.Impl.LinObjectLiftCost
import Workspace.Impl.LinObjectOffsetRow

/-! Build one piece of a basis configuration. Integer coordinates are
lifted to an actual word of A and applied with the existing list shift. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linObjectBasisPieceF (row word shift : ℕ) : Expr :=
  .letE (.call row (mk4 (arg 1)
    (.arith .sub (.length (.get (arg 0) (.nat 1))) (.nat 1)) (arg 2) (arg 3)))
    (.letE (.call word (mk2 (arg 0) (.var 1))) (.call shift (mk2 (.var 2) (arg 4))))

def linObjectBasisPieceFuns (b shift : ℕ) : List Expr :=
  [linObjectBasisPieceF (b + 1) (b + 10) shift] ++ linObjectVectorRowFuns (b + 1) ++ linPermWordFuns (b + 10)

theorem linObjectBasisPieceFuns_length (b shift : ℕ) : (linObjectBasisPieceFuns b shift).length = 33 := by
  simp [linObjectBasisPieceFuns, linObjectVectorRowFuns_length, linPermWordFuns_length]

structure linObjectBasisPieceAt (P : Program) (b shift : ℕ) : Prop where
  entry : P.funs[b]? = some (linObjectBasisPieceF (b + 1) (b + 10) shift)
  row : P.HasAt (b + 1) (linObjectVectorRowFuns (b + 1))
  word : linPermWordAt P (b + 10)

theorem linObjectBasisPieceAt_of {P : Program} {b shift : ℕ}
    (h : P.HasAt b (linObjectBasisPieceFuns b shift)) : linObjectBasisPieceAt P b shift where
  entry := (h.block (gs := [linObjectBasisPieceF (b + 1) (b + 10) shift]) 0 rfl).single
  row := h.block 1 rfl
  word := linPermWordAt_of (h.block 10 rfl)

def linObjectBasisPieceRowBudget (W : ℕ) : ℕ := linObjectVectorRowCost (100 * (W + 1))
def linObjectBasisPieceWordArg (W : ℕ) : ℕ := 100 * (W + linObjectBasisPieceRowBudget W + 1)
def linObjectBasisPieceWordBudget (W : ℕ) : ℕ := linPermWordCost (linObjectBasisPieceWordArg W)
def linObjectBasisPieceCost (W C : ℕ) : ℕ :=
  1000000 * (W + linObjectBasisPieceRowBudget W + linObjectBasisPieceWordBudget W + C + 1)

theorem linObjectVectorRowCost_mono {W V : ℕ} (h : W ≤ V) :
    linObjectVectorRowCost W ≤ linObjectVectorRowCost V := by
  unfold linObjectVectorRowCost linObjectVectorRowBudget linObjectVectorRowCellCost
    linTabulateCost linTabulateRangeCost linMapBudget
  gcongr

theorem linObjectBasisPieceCost_poly : PBU (fun _ W C => linObjectBasisPieceCost W C) := by
  have hr : PBU (fun _ W _ => linObjectBasisPieceRowBudget W) :=
    linPoly_subst (f := fun _ W _ => linObjectVectorRowCost W) linObjectVectorRowCost_poly
      (PBU.const 0) (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  have hw : PBU (fun _ W _ => linObjectBasisPieceWordBudget W) :=
    linPoly_subst (f := fun _ W _ => linPermWordCost W) linPermWordCost_poly
      (PBU.const 0) (PBU.smul 100 (PBU.addc (PBU.add PBU.W hr) 1)) (PBU.const 0)
  exact PBU.smul 1000000 (PBU.addc (PBU.add (PBU.add (PBU.add PBU.W hr) hw) PBU.B) 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linObjectBasisPiece_spec {P : Program} {b shift n p C : ℕ}
    (h : linObjectBasisPieceAt P b shift) (as : List (Equiv.Perm (Fin n)))
    (z : Fin (as.length * p) → ℤ) (i : Fin p) (piece : Val)
    (out : Equiv.Perm (Fin n) → Val)
    (hshift : ∀ a, FunDet P shift (.list [encPerm a, piece]) (out a) C) :
    let input := Val.list [encGroup as, .nat p, .nat i, linVecVal z, piece]
    FunDet P b input (out (linGroupWord (fun j => as.get j) (linObjectUnflatten p as.length z i)))
      (linObjectBasisPieceCost input.wt C) := by
  let input := Val.list [encGroup as, .nat p, .nat i, linVecVal z, piece]
  let W := input.wt
  let localz := linObjectUnflatten p as.length z i
  let g := linGroupWord (fun j => as.get j) localz
  let RB := linObjectBasisPieceRowBudget W
  let WB := linObjectBasisPieceWordBudget W
  have wa : (encGroup as).wt < W := wt_le_wt_list (by simp [input, W])
  have wp : (Val.nat p).wt < W := wt_le_wt_list (by simp [input, W])
  have wi : (Val.nat i).wt < W := wt_le_wt_list (by simp [input, W])
  have wz : (linVecVal z).wt < W := wt_le_wt_list (by simp [input, W])
  have ws : piece.wt < W := wt_le_wt_list (by simp [input, W])
  have wt : as.length ≤ W := by
    have hh := length_lt_wt_list ((1 :: as).map encPerm)
    have hw : (Val.list ((1 :: as).map encPerm)).wt < (encGroup as).wt :=
      wt_le_wt_list (by simp [encGroup, encPerms])
    simp only [List.length_map, List.length_cons] at hh
    omega
  have wrarg : (Val.list [.nat p, .nat as.length, .nat i, linVecVal z]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list4_le (.nat p) (.nat as.length) (.nat i) (linVecVal z)
    have ht := wt_nat_le as.length
    omega
  have hr := (linObjectVectorRow_spec h.row z i).mono (linObjectVectorRowCost_mono wrarg)
  have wr : (linVecVal localz).wt ≤ RB := hr.wt_lt.le
  have wwarg : (Val.list [encGroup as, linVecVal localz]).wt ≤ linObjectBasisPieceWordArg W := by
    have hh := wt_list2_le (encGroup as) (linVecVal localz)
    unfold linObjectBasisPieceWordArg
    dsimp only [RB] at *
    omega
  have hw := (linPermWord_spec h.word as localz).mono (linPermWordCost_mono wwarg)
  have wg : (encPerm g).wt ≤ WB := hw.wt_lt.le
  have darg (k : ℕ) {v : Val}
      (hv : [encGroup as, .nat p, .nat i, linVecVal z, piece][k]? = some v) :=
    Det.arg' (P := P) (vs := [encGroup as, .nat p, .nat i, linVecVal z, piece]) (rest := []) (j := k) hv
  have da := darg 0 rfl
  have dt := Det.arith' (op := .sub) (Det.length (Det.get' da (Det.nat 1) rfl)) (Det.nat 1)
    (z := as.length) (by simp)
  have dr := Det.call (Det.mk4 (darg 1 rfl) dt (darg 2 rfl) (darg 3 rfl)) hr
  apply FunAll.intro h.entry
  apply EvalAll.letE dr
  intro v cr hv
  obtain ⟨rfl, hcr⟩ := hv
  have da' := Det.arg' (P := P) (vs := [encGroup as, .nat p, .nat i, linVecVal z, piece])
    (rest := [linVecVal localz]) (j := 0) rfl
  have dw := Det.call (Det.mk2 da' (Det.var' (P := P) (env := [input, linVecVal localz]) (i := 1) rfl)) hw
  apply EvalAll.letE dw
  intro v cw hv
  obtain ⟨rfl, hcw⟩ := hv
  have ds := Det.call (Det.mk2 (Det.var' (P := P)
    (env := [input, linVecVal localz, encPerm g]) (i := 2) rfl)
    (Det.arg' (P := P) (vs := [encGroup as, .nat p, .nat i, linVecVal z, piece])
      (rest := [linVecVal localz, encPerm g]) (j := 4) rfl)) (hshift g)
  refine ds.post fun cost hc => ⟨rfl, ?_⟩
  have wo := (hshift g).wt_lt.le
  have wh := wt_list4_le (.nat p) (.nat as.length) (.nat i) (linVecVal z)
  have ww := wt_list2_le (encGroup as) (linVecVal localz)
  have wsa := wt_list2_le (encPerm g) piece
  have ht := wt_nat_le as.length
  have wi1 : (Val.nat 1).wt = 3 := rfl
  have wraw : (Val.list ((1 :: as).map encPerm)).wt < (encGroup as).wt :=
    wt_le_wt_list (by simp [encGroup, encPerms])
  change _ ≤ linObjectBasisPieceCost W C
  unfold linObjectBasisPieceCost
  dsimp only [input, W, RB, WB, localz, g, encGroup, encPerms,
    linObjectBasisPieceRowBudget, linObjectBasisPieceWordBudget] at *
  simp only [List.length_map, List.length_cons] at *
  omega

end GI.Impl
