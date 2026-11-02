import Workspace.Impl.AggCmpFind
import Workspace.Impl.AggCmpWt
import Workspace.Impl.AggCertMvBase

/-!
# The move program of the comparison phase: the moves without new groups

This file writes the part of the move function `mv` of the loop `cpLoopBody`
(`AggCertLoop.lean`) that needs no new group computation, as a `GI.Lang` program. Its argument is
a program state `[kst, u]` with `kst = [par, j, o, cache, acc, fl]` (`AggCmpRep.lean`); it reads
entries with `cpKf`, `cpPf` (`AggCertProg.lean`).

The data of the phase is `par = [sv, [k, q], ⟨ps⟩, ⟨fx⟩, ⟨fy⟩, ⟨logs⟩, ⟨tuples⟩, n, N]`
(`cmParV`): the first six entries are those of the hand-over `cmSt`, then the test tuples in the
order of the phase, `n = |dom|` and the number `N` of tuples.

The functions, at base `b`:

* `b`: dispatch on `fl` (`cmMvF`);
* `b + 1`: the start of a pair, or the end of the phase at index `N²` (`cmPairF`): the output
  `cmOutV` from `par` and `acc`;
* `b + 2`: stage `j` (`cmStageF`): at `j = n` the end of the pair (push `o ≠ []`); an empty
  coset moves to `j + 1`; else the call (`b + 4`);
* `b + 3`: the answer (`cmAnsF`): `u = []` gives no representative; `u = [x, ⟨gs⟩]` gives the coset
  `(gs, a₀ x)` (`compose`), looked up in the cache (`cmFind`); a hit gives the cached
  representative, a miss appends the new value.

The start of a pair (`b + 5`, the first coset) and the call (`b + 4`) are not written in this file.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)

/-- **The data of the phase.** -/
noncomputable def cmParV {k q κ : ℕ} (sv : Val) (ps fx fy : GPairs k q) (logs : List (CmLog k q))
    (tt : List (TestTuple q κ)) (n : ℕ) : Val :=
  .list [sv, .list [.nat k, .nat q], .list (ps.map pairV), .list (fx.map pairV),
    .list (fy.map pairV), .list (logs.map cmLogV), .list (tt.map stTT), .nat n, .nat tt.length]

section Funs

variable (b : ℕ)

/-- Base indices of the library modules. -/
def cmComp : ℕ := b + 16
def cmFind : ℕ := b + 20

/-- The state value after a move with no call: `[2, [kst', []]]`. -/
def cmRetE (kst : Expr) : Expr := mk2 (.nat 2) (mk2 kst .nil)

/-- **The output of the phase**: `[sv, [k, q], ⟨ps⟩, ⟨fx⟩, ⟨fy⟩, [⟨tuples⟩, ⟨acc⟩]]`. -/
def cmOutE : Expr :=
  Expr.mkList [cpPf 0, cpPf 1, cpPf 2, cpPf 3, cpPf 4, mk2 (cpPf 6) (cpKf 4)]

/-- **The move function**: dispatch on `fl`. -/
def cmMvF : Expr :=
  .ite (.arith .eq (cpKf 5) (.nat 0)) (.call (b + 1) (.var 0))
    (.ite (.arith .eq (cpKf 5) (.nat 1)) (.call (b + 2) (.var 0)) (.call (b + 3) (.var 0)))

/-- **The start of a pair, or the end of the phase.** -/
def cmPairF : Expr :=
  .ite (.arith .lt (.length (cpKf 4)) (.arith .mul (cpPf 8) (cpPf 8)))
    (.call (b + 5) (.var 0))
    (mk2 (.nat 0) cmOutE)

/-- **Stage `j`.** -/
def cmStageF : Expr :=
  .ite (.arith .eq (cpKf 1) (cpPf 7))
    (cmRetE (Expr.mkList [cpKf 0, cpKf 1, cpKf 2, cpKf 3, .snoc (cpKf 4) (.length (cpKf 2)),
      .nat 0]))
    (.ite (.length (cpKf 2))
      (.call (b + 4) (.var 0))
      (cmRetE (Expr.mkList [cpKf 0, .arith .add (cpKf 1) (.nat 1), cpKf 2, cpKf 3, cpKf 4,
        cpKf 5])))

/-- The answer `u`. -/
def cmU : Expr := .get (.var 0) (.nat 1)

/-- **The answer of a call.** -/
def cmAnsF : Expr :=
  .ite (.length cmU)
    (.letE (.call (cmComp b) (mk2 (.get (cpKf 2) (.nat 0)) (.get cmU (.nat 0))))
      (.letE (.call (cmFind b) (mk2 (mk2 (.get cmU (.nat 1)) (.var 1)) (cpKf 3)))
        (.ite (.arith .lt (.var 2) (.length (cpKf 3)))
          (cmRetE (Expr.mkList [cpKf 0, .arith .add (cpKf 1) (.nat 1),
            mk1 (.get (.get (cpKf 3) (.var 2)) (.nat 1)), cpKf 3, cpKf 4, .nat 1]))
          (cmRetE (Expr.mkList [cpKf 0, .arith .add (cpKf 1) (.nat 1), mk1 (.var 1),
            .snoc (cpKf 3) (mk2 (.get cmU (.nat 1)) (.var 1)), cpKf 4, .nat 1])))))
    (cmRetE (Expr.mkList [cpKf 0, .arith .add (cpKf 1) (.nat 1), .nil, cpKf 3, cpKf 4, .nat 1]))

end Funs

open GI.Cited (Membership) in
/-- **Where the moves without new groups and their modules sit.** -/
structure CmMvAt0 (P : Program) (b jm : ℕ) : Prop where
  mv : P.funs[b]? = some (cmMvF b)
  pair : P.funs[b + 1]? = some (cmPairF b)
  stage : P.funs[b + 2]? = some (cmStageF b)
  ans : P.funs[b + 3]? = some (cmAnsF b)
  comp : P.HasAt (cmComp b) (composeFuns (cmComp b))
  find : P.HasAt (cmFind b) (cmFindFuns (cmFind b) jm)

end GI.Impl
