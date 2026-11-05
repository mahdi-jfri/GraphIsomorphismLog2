module

public import Workspace.Impl.LinCoordinatePrep

@[expose] public section

/-! A concrete self-contained layout for the deterministic cyclic-row preparation.
Only GroupOrder is external, at a parameter primitive index. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linPrepLayout (b : ℕ) : linPrepIndices :=
  ⟨b + 1, b + 2, b + 3, b + 8, b + 11, b + 14, b + 4, b + 17,
    b + 5, b + 21, b + 24, b + 27, b + 6, b + 7⟩

def linCoordinatePrepFuns (b jo : ℕ) : List Expr :=
  let I := linPrepLayout b
  [linCoordinatePrepF I, linPrefixOrderF I.pf I.ratio, linPrefixF I.tail I.take I.append,
    linOrderRatioF jo, linPermPowF I.power I.comp, linAssignF I.rep I.units,
    linIntEncodeF I.bits, linBitsEncodeF I.bits] ++
    linTailFuns I.tail ++ linTakeFuns I.take ++ appendFuns I.append ++ composeFuns I.comp ++
    replicateFuns I.rep ++ linAssignUnitFuns I.units I.basis ++ linBasisFuns I.basis

theorem linCoordinatePrepFuns_length (b jo : ℕ) : (linCoordinatePrepFuns b jo).length = 30 := rfl

theorem linCoordinatePrepAt_of {P : Program} {b jo : ℕ} {ho : GroupOrder}
    (h : P.HasAt b (linCoordinatePrepFuns b jo))
    (hj : P.prims[jo]? = some (groupOrderPrim ho)) :
    linPrepAt P (linPrepLayout b) jo ho where
  order := by simpa [linPrepLayout] using
    (h.block (gs := [linPrefixOrderF (b + 2) (b + 3)]) 1 rfl).single
  pf := by simpa [linPrepLayout] using
    (h.block (gs := [linPrefixF (b + 8) (b + 11) (b + 14)]) 2 rfl).single
  ratio := by simpa [linPrepLayout] using (h.block (gs := [linOrderRatioF jo]) 3 rfl).single
  tail := h.block 8 rfl
  take := h.block 11 rfl
  append := h.block 14 rfl
  power := by simpa [linPrepLayout] using
    (h.block (gs := [linPermPowF (b + 4) (b + 17)]) 4 rfl).single
  comp := h.block 17 rfl
  assign := by simpa [linPrepLayout] using
    (h.block (gs := [linAssignF (b + 21) (b + 24)]) 5 rfl).single
  rep := h.block 21 rfl
  units := h.block 24 rfl
  basis := h.block 27 rfl
  encode := by simpa [linPrepLayout] using (h.block (gs := [linIntEncodeF (b + 7)]) 6 rfl).single
  bits := by simpa [linPrepLayout] using (h.block (gs := [linBitsEncodeF (b + 7)]) 7 rfl).single
  ordPrim := hj

theorem linCoordinatePrep_entry {P : Program} {b jo : ℕ}
    (h : P.HasAt b (linCoordinatePrepFuns b jo)) :
    P.funs[b]? = some (linCoordinatePrepF (linPrepLayout b)) :=
  (h.block (gs := [linCoordinatePrepF (linPrepLayout b)]) 0 rfl).single

end GI.Impl
