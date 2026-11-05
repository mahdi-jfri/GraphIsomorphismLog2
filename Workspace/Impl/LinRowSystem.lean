module

public import Workspace.Impl.LinIntSolverCost

@[expose] public section

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

theorem linRowSystemPrefixFuns_length (b jh : ℕ) : (linRowSystemPrefixFuns b jh).length = 40 := by
  simp only [linRowSystemPrefixFuns, List.length_append]
  rfl

def linRowSystemFuns (b jh : ℕ) : List Expr :=
  linRowSystemPrefixFuns b jh ++ linIntFuns (b + 40)

theorem linRowSystemFuns_length (b jh : ℕ) : (linRowSystemFuns b jh).length = 58 := by
  simp only [linRowSystemFuns, List.length_append, linRowSystemPrefixFuns_length]
  rfl

structure linRowSystemAt (P : Program) (b jh : ℕ) : Prop where
  entry : P.funs[b]? = some (linRowSolverF (b + 1) (b + 2))
  hermite : P.funs[b + 1]? = some (linHermiteF jh)
  finish : P.funs[b + 2]? = some (linHermiteFinishF (b + 3) (b + 6) (b + 25))
  take : P.HasAt (b + 3) (linTakeFuns (b + 3))
  tri : linTriInstalled P (linRowSystemTri b)
  triEntry : P.funs[b + 6]? = some (linTriUpperF (b + 6) (linRowSystemTri b))
  lift : linLiftInstalled P (linRowSystemLift b)
  liftEntry : P.funs[b + 25]? = some (linHermiteLiftF (linRowSystemLift b))

private theorem spd_linRow_peel {P : Program} {b N n N' : ℕ} {A B : List Expr}
    (h : P.HasAt (b + N) (A ++ B)) (hl : A.length = n) (hN : N + n = N') :
    P.HasAt (b + N) A ∧ P.HasAt (b + N') B := by
  refine ⟨h.left, ?_⟩
  have h2 := h.right
  rw [hl, Nat.add_assoc, hN] at h2
  exact h2

private theorem spd_linRow_cons {P : Program} {b N N' : ℕ} {e : Expr} {B : List Expr}
    (h : P.HasAt (b + N) (e :: B)) (hN : N + 1 = N') :
    P.funs[b + N]? = some e ∧ P.HasAt (b + N') B := by
  have h' : P.HasAt (b + N) ([e] ++ B) := h
  obtain ⟨h1, h2⟩ := spd_linRow_peel h' rfl hN
  exact ⟨h1.single, h2⟩

theorem linRowSystemAt_of {P : Program} {b jh : ℕ}
    (h : P.HasAt b (linRowSystemFuns b jh)) : linRowSystemAt P b jh := by
  have hintBlock : P.HasAt (b + 40) (linIntFuns (b + 40)) := by
    simpa only [linRowSystemPrefixFuns_length] using
      (Program.HasAt.right (A := linRowSystemPrefixFuns b jh) (B := linIntFuns (b + 40)) h)
  have hints := linInt_spec hintBlock
  have hp : P.HasAt (b + 0) (linRowSystemPrefixFuns b jh) := h.left
  unfold linRowSystemPrefixFuns at hp
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hp
  obtain ⟨h0, hp⟩ := spd_linRow_cons (N' := 1) hp rfl
  obtain ⟨h1, hp⟩ := spd_linRow_cons (N' := 2) hp rfl
  obtain ⟨h2, hp⟩ := spd_linRow_cons (N' := 3) hp rfl
  obtain ⟨h3, hp⟩ := spd_linRow_peel (N' := 6) hp rfl rfl
  obtain ⟨h6, hp⟩ := spd_linRow_cons (N' := 7) hp rfl
  obtain ⟨h7, hp⟩ := spd_linRow_cons (N' := 8) hp rfl
  obtain ⟨h8, hp⟩ := spd_linRow_peel (N' := 11) hp rfl rfl
  obtain ⟨h11, hp⟩ := spd_linRow_cons (N' := 12) hp rfl
  obtain ⟨h12, hp⟩ := spd_linRow_peel (N' := 16) hp rfl rfl
  obtain ⟨h16, hp⟩ := spd_linRow_peel (N' := 19) hp rfl rfl
  obtain ⟨h19, hp⟩ := spd_linRow_peel (N' := 22) hp rfl rfl
  obtain ⟨h22, hp⟩ := spd_linRow_peel (N' := 25) hp rfl rfl
  obtain ⟨h25, hp⟩ := spd_linRow_cons (N' := 26) hp rfl
  obtain ⟨h26, hp⟩ := spd_linRow_cons (N' := 27) hp rfl
  obtain ⟨h27, hp⟩ := spd_linRow_peel (N' := 30) hp rfl rfl
  obtain ⟨h30, hp⟩ := spd_linRow_peel (N' := 33) hp rfl rfl
  obtain ⟨h33, h37⟩ := spd_linRow_peel (N' := 37) hp rfl rfl
  rw [Nat.add_zero] at h0
  exact ⟨h0, h1, h2, h3, ⟨hints, h7, h8, h11, h12, h16, h19, h22⟩, h6,
    ⟨h26, h27, h22, h30, h33, h37, hints⟩, h25⟩

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
