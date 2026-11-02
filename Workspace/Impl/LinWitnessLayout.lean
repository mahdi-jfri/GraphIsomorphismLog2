import Workspace.Impl.LinCoordinateWitness

namespace GI.Impl
open GI.Cited GI.Lang

/-- Witness entry, membership, exponent value, instruction step, shared table,
integer arithmetic, vector addition, and scalar multiplication. -/
def linCoordinateWitnessFuns (b jm : ℕ) : List Expr :=
  [linCoordinateWitnessF (b + 1) (b + 2), linMembershipF jm,
    linSlpValueF (b + 4), linSlpStepF (b + 25) (b + 28)] ++
    linSlpFuns (b + 4) (b + 3) ++ linIntFuns (b + 7) ++
    linVectorBinaryFuns (b + 25) ((b + 7) + 11) ++ linVectorScaleFuns (b + 28) (b + 7)

theorem linCoordinateWitnessFuns_length (b jm : ℕ) :
    (linCoordinateWitnessFuns b jm).length = 31 := rfl

structure linWitnessAt (P : Program) (b jm : ℕ) (hm : ConstructiveMembership) : Prop where
  entry : P.funs[b]? = some (linCoordinateWitnessF (b + 1) (b + 2))
  member : P.funs[b + 1]? = some (linMembershipF jm)
  exponent : P.funs[b + 2]? = some (linSlpValueF (b + 4))
  step : P.funs[b + 3]? = some (linSlpStepF (b + 25) (b + 28))
  table : P.HasAt (b + 4) (linSlpFuns (b + 4) (b + 3))
  ints : linIntSpec P (b + 7)
  add : P.HasAt (b + 25) (linVectorBinaryFuns (b + 25) ((b + 7) + 11))
  scale : P.HasAt (b + 28) (linVectorScaleFuns (b + 28) (b + 7))
  prim : P.prims[jm]? = some (linMembershipPrim hm)

theorem linCoordinateWitnessAt_of {P : Program} {b jm : ℕ} {hm : ConstructiveMembership}
    (h : P.HasAt b (linCoordinateWitnessFuns b jm))
    (hj : P.prims[jm]? = some (linMembershipPrim hm)) : linWitnessAt P b jm hm where
  entry := (h.block (gs := [linCoordinateWitnessF (b + 1) (b + 2)]) 0 rfl).single
  member := (h.block (gs := [linMembershipF jm]) 1 rfl).single
  exponent := (h.block (gs := [linSlpValueF (b + 4)]) 2 rfl).single
  step := (h.block (gs := [linSlpStepF (b + 25) (b + 28)]) 3 rfl).single
  table := h.block 4 rfl
  ints := linInt_spec (h.block 7 rfl)
  add := h.block 25 rfl
  scale := h.block 28 rfl
  prim := hj

end GI.Impl
