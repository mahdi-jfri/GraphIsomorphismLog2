import Workspace.Impl.LinIntSolverCost

/-! A relocatable function list for the full integer row solver: Hermite,
triangular substitution, padding, and multiplication by the row multiplier. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linRowSystemTri (b : ℕ) : linTriIndices :=
  ⟨b + 40, b + 7, b + 8, b + 11, b + 12, b + 16, b + 19, b + 22⟩

def linRowSystemLift (b : ℕ) : linLiftIndices :=
  ⟨b + 26, b + 27, b + 22, b + 30, b + 33, b + 37, b + 40⟩

def linRowSystemPrefixFuns (b jh : ℕ) : List Expr :=
  [linRowSolverF (b + 1) (b + 2), linHermiteF jh,
    linHermiteFinishF (b + 3) (b + 6) (b + 25)] ++ linTakeFuns (b + 3) ++
    [linTriUpperF (b + 6) (linRowSystemTri b), linIntExactF ((b + 40) + 14) ((b + 40) + 15)] ++
    linTailFuns (b + 8) ++ [linTrimF (b + 8) (b + 12)] ++ linTrimMapFuns (b + 12) (b + 8) ++
    linVectorScaleFuns (b + 16) (b + 40) ++ linVectorBinaryFuns (b + 19) ((b + 40) + 12) ++
    appendFuns (b + 22) ++ [linHermiteLiftF (linRowSystemLift b), linPadF (b + 27) (b + 22)] ++
    replicateFuns (b + 27) ++ linRowMulFuns (b + 30) (b + 33) (b + 37) ++
    linColumnFuns (b + 33) ++ linDotLoopFuns (b + 37) (b + 40)

theorem linRowSystemPrefixFuns_length (b jh : ℕ) : (linRowSystemPrefixFuns b jh).length = 40 := rfl

def linRowSystemFuns (b jh : ℕ) : List Expr :=
  linRowSystemPrefixFuns b jh ++ linIntFuns (b + 40)

theorem linRowSystemFuns_length (b jh : ℕ) : (linRowSystemFuns b jh).length = 58 := rfl

structure linRowSystemAt (P : Program) (b jh : ℕ) : Prop where
  entry : P.funs[b]? = some (linRowSolverF (b + 1) (b + 2))
  hermite : P.funs[b + 1]? = some (linHermiteF jh)
  finish : P.funs[b + 2]? = some (linHermiteFinishF (b + 3) (b + 6) (b + 25))
  take : P.HasAt (b + 3) (linTakeFuns (b + 3))
  tri : linTriInstalled P (linRowSystemTri b)
  triEntry : P.funs[b + 6]? = some (linTriUpperF (b + 6) (linRowSystemTri b))
  lift : linLiftInstalled P (linRowSystemLift b)
  liftEntry : P.funs[b + 25]? = some (linHermiteLiftF (linRowSystemLift b))

set_option maxHeartbeats 2000000 in
theorem linRowSystemAt_of {P : Program} {b jh : ℕ}
    (h : P.HasAt b (linRowSystemFuns b jh)) : linRowSystemAt P b jh := by
  have hintBlock : P.HasAt (b + 40) (linIntFuns (b + 40)) := by
    simpa only [linRowSystemPrefixFuns_length] using
      (Program.HasAt.right (A := linRowSystemPrefixFuns b jh) (B := linIntFuns (b + 40)) h)
  have hints := linInt_spec hintBlock
  refine ⟨(h.block (gs := [linRowSolverF (b + 1) (b + 2)]) 0 rfl).single,
    (h.block (gs := [linHermiteF jh]) 1 rfl).single,
    (h.block (gs := [linHermiteFinishF (b + 3) (b + 6) (b + 25)]) 2 rfl).single,
    h.block 3 rfl, ?_,
    (h.block (gs := [linTriUpperF (b + 6) (linRowSystemTri b)]) 6 rfl).single, ?_,
    (h.block (gs := [linHermiteLiftF (linRowSystemLift b)]) 25 rfl).single⟩
  · refine ⟨hints, ?_, h.block 8 rfl,
      (h.block (gs := [linTrimF (b + 8) (b + 12)]) 11 rfl).single,
      h.block 12 rfl, h.block 16 rfl, h.block 19 rfl, h.block 22 rfl⟩
    exact (h.block (gs := [linIntExactF ((b + 40) + 14) ((b + 40) + 15)]) 7 rfl).single
  · exact ⟨(h.block (gs := [linPadF (b + 27) (b + 22)]) 26 rfl).single,
      h.block 27 rfl, h.block 22 rfl, h.block 30 rfl, h.block 33 rfl, h.block 37 rfl, hints⟩

theorem linRowSystem_spec (hH : HermiteFullRank) {P : Program} {b jh : ℕ}
    (h : linRowSystemAt P b jh) (hj : P.prims[jh]? = some (linHermitePrim hH))
    (I : FullRankInst) (w : Fin I.c → ℤ) :
    FunAll P b (.list [fullRankInput I, linVecVal w]) (fun out cost =>
      linRowAnswer I.A w out ∧
        cost ≤ linRowSolverCost hH I (Val.list [fullRankInput I, linVecVal w]).wt) :=
  linRowSolver_spec hH h.entry h.hermite hj h.finish h.take h.tri h.triEntry h.lift h.liftEntry I w

theorem linRowSystem_spec_poly (hH : HermiteFullRank) :
    ∃ K D : ℕ, ∀ {P : Program} {b jh : ℕ}, linRowSystemAt P b jh →
      P.prims[jh]? = some (linHermitePrim hH) → ∀ (I : FullRankInst) (w : Fin I.c → ℤ),
        FunAll P b (.list [fullRankInput I, linVecVal w]) (fun out cost =>
          linRowAnswer I.A w out ∧ cost ≤ K * ((Val.list [fullRankInput I, linVecVal w]).wt + 1) ^ D) := by
  obtain ⟨K, D, hKD⟩ := linRowSolverCost_poly hH
  exact ⟨K, D, fun h hj I w => (linRowSystem_spec hH h hj I w).mono fun out cost ho =>
    ⟨ho.1, ho.2.trans (hKD I w)⟩⟩

end GI.Impl
