import Workspace.Impl.LinObjectOffsetRows
import Workspace.Impl.LinObjectOffsetCert
import Workspace.Impl.LinObjectFlattenCoords
import Workspace.Impl.LinPolyEnvelope

/-! Collect all local offsets and their integer exponent vectors. The
table is computed by the abelian zero-fuel transporter, not an oracle. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linObjectOffsetsF (app table slice rows coords flat range : ℕ) : Expr :=
  .letE (.call app (mk2 (arg 2) (arg 3)))
    (.letE (.call table (mk3 (arg 0) (arg 1) (.var 1)))
      (.letE (.call slice (mk3 (.nat 0) (.length (arg 2)) (.var 2)))
        (.letE (.call rows (mk2 (mk2 (.length (arg 2)) (.length (arg 3))) (.var 3)))
          (.letE (.call coords (mk2 (arg 0) (.var 4)))
            (.letE (.call range (.length (arg 2)))
              (.letE (.call range (.arith .sub (.length (.get (arg 0) (.nat 1))) (.nat 1)))
                (.call flat (mk3 (.var 6) (.var 7) (.var 5)))))))))

def linObjectOffsetsFuns (b jsci jder jmem jm : ℕ) : List Expr :=
  [linObjectOffsetsF (b + 1) (b + 4) (b + 102) (b + 105) (b + 119) (b + 164) (b + 173)] ++
    appendFuns (b + 1) ++ linObjectPairTableFuns (b + 4) jsci jder jmem ++ linSliceFuns (b + 102) ++
    linObjectOffsetRowsFuns (b + 105) ++ linElementListFuns (b + 119) jm ++
    linObjectFlattenCoordsFuns (b + 164) ++ rangeFuns (b + 173)

theorem linObjectOffsetsFuns_length (b jsci jder jmem jm : ℕ) :
    (linObjectOffsetsFuns b jsci jder jmem jm).length = 176 := by
  simp only [linObjectOffsetsFuns, List.length_append, List.length_cons, List.length_nil,
    linObjectPairTableFuns_length, linObjectOffsetRowsFuns_length, linElementListFuns_length,
    linObjectFlattenCoordsFuns_length]
  rfl

structure linObjectOffsetsAt (P : Program) (b jsci jder jmem jm : ℕ)
    (hsci : SolvableCosetIntersection) (hder : DerivedSubgroup) (hmem : Membership)
    (hm : ConstructiveMembership) : Prop where
  entry : P.funs[b]? = some
    (linObjectOffsetsF (b + 1) (b + 4) (b + 102) (b + 105) (b + 119) (b + 164) (b + 173))
  append : P.HasAt (b + 1) (appendFuns (b + 1))
  table : linObjectPairTableAt P (b + 4) jsci jder jmem hsci hder hmem
  slice : P.HasAt (b + 102) (linSliceFuns (b + 102))
  rows : P.HasAt (b + 105) (linObjectOffsetRowsFuns (b + 105))
  coords : linElementListAt P (b + 119) jm hm
  flat : P.HasAt (b + 164) (linObjectFlattenCoordsFuns (b + 164))
  range : P.HasAt (b + 173) (rangeFuns (b + 173))

set_option maxHeartbeats 2000000 in
theorem linObjectOffsetsAt_of {P : Program} {b jsci jder jmem jm : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    {hm : ConstructiveMembership} (h : P.HasAt b (linObjectOffsetsFuns b jsci jder jmem jm))
    (hs : P.prims[jsci]? = some (solvableCosetIntersectionPrim hsci))
    (hd : P.prims[jder]? = some (derivedSubgroupPrim hder))
    (hmem' : P.prims[jmem]? = some (membershipPrim hmem))
    (hm' : P.prims[jm]? = some (linMembershipPrim hm)) :
    linObjectOffsetsAt P b jsci jder jmem jm hsci hder hmem hm where
  entry := (h.block (gs := [linObjectOffsetsF (b + 1) (b + 4) (b + 102) (b + 105)
    (b + 119) (b + 164) (b + 173)]) 0 rfl).single
  append := h.block 1 rfl
  table := linObjectPairTableAt_of (h.block 4 rfl) hs hd hmem'
  slice := h.block 102 rfl
  rows := h.block 105 rfl
  coords := linElementListAt_of (h.block 119 rfl) hm'
  flat := h.block 164 rfl
  range := h.block 173 rfl

end GI.Impl
