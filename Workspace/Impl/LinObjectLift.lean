import Workspace.Impl.LinObjectQuotientBuild
import Workspace.Impl.LinObjectLiftMath
import Workspace.Impl.LinRowSystem
import Workspace.Impl.LinSlice
import Workspace.Impl.LinPermWord

/-! Solve the common-translation equation and lift its final coefficient
block to an actual element of `A`. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linObjectLiftPositiveF (build neg solve slice word : ℕ) : Expr :=
  .letE (.call build (arg 1))
    (.letE (.call neg (mk2 linIntMinusOneE (arg 2)))
      (.letE (.call solve (mk2 (mk3 (.length (.var 1)) (.length (arg 2)) (.var 1)) (.var 2)))
        (.ite (.isNat (.var 3)) (.nat 0)
          (.letE (.call slice (mk3
            (.arith .mul (.length (.get (arg 1) (.nat 0))) (.length (.get (arg 1) (.nat 2))))
            (.length (.get (arg 1) (.nat 1))) (.get (.var 3) (.nat 1))))
            (.letE (.call word (mk2 (arg 0) (.var 4))) (mk2 (.nat 1) (.var 5)))))))

def linObjectLiftF (positive : ℕ) : Expr :=
  .ite (.length (arg 2)) (.call positive (.var 0))
    (mk2 (.nat 1) (.get (.get (arg 0) (.nat 1)) (.nat 0)))

def linObjectLiftPrefixFuns (b : ℕ) : List Expr :=
  [linObjectLiftF (b + 1), linObjectLiftPositiveF (b + 2) (b + 43) (b + 46) (b + 104) (b + 107)] ++
    linObjectQuotientBuildFuns (b + 2) ++ linVectorScaleFuns (b + 43) (b + 86)

theorem linObjectLiftPrefixFuns_length (b : ℕ) : (linObjectLiftPrefixFuns b).length = 46 := by
  simp only [linObjectLiftPrefixFuns, List.length_append, List.length_cons, List.length_nil,
    linObjectQuotientBuildFuns_length]
  rfl

def linObjectLiftFuns (b jh : ℕ) : List Expr :=
  linObjectLiftPrefixFuns b ++ linRowSystemFuns (b + 46) jh ++
    linSliceFuns (b + 104) ++ linPermWordFuns (b + 107)

theorem linObjectLiftFuns_length (b jh : ℕ) : (linObjectLiftFuns b jh).length = 130 := by
  simp only [linObjectLiftFuns, List.length_append, linObjectLiftPrefixFuns_length,
    linRowSystemFuns_length, linSliceFuns_length, linPermWordFuns_length]

structure linObjectLiftAt (P : Program) (b jh : ℕ) : Prop where
  entry : P.funs[b]? = some (linObjectLiftF (b + 1))
  positive : P.funs[b + 1]? = some
    (linObjectLiftPositiveF (b + 2) (b + 43) (b + 46) (b + 104) (b + 107))
  build : linObjectQuotientBuildAt P (b + 2)
  neg : P.HasAt (b + 43) (linVectorScaleFuns (b + 43) (b + 86))
  solve : linRowSystemAt P (b + 46) jh
  slice : P.HasAt (b + 104) (linSliceFuns (b + 104))
  word : linPermWordAt P (b + 107)

set_option maxHeartbeats 2000000 in
theorem linObjectLiftAt_of {P : Program} {b jh : ℕ}
    (h : P.HasAt b (linObjectLiftFuns b jh)) : linObjectLiftAt P b jh := by
  have hp : P.HasAt b (linObjectLiftPrefixFuns b) := h.left.left.left
  have hr : P.HasAt (b + 46) (linRowSystemFuns (b + 46) jh) := by
    simpa only [linObjectLiftPrefixFuns_length] using
      (Program.HasAt.right (A := linObjectLiftPrefixFuns b) (B := linRowSystemFuns (b + 46) jh)
        h.left.left)
  have hs : P.HasAt (b + 104) (linSliceFuns (b + 104)) := by
    simpa only [List.length_append, linObjectLiftPrefixFuns_length, linRowSystemFuns_length,
      Nat.add_assoc, Nat.reduceAdd] using
      (Program.HasAt.right (A := linObjectLiftPrefixFuns b ++ linRowSystemFuns (b + 46) jh)
        (B := linSliceFuns (b + 104)) h.left)
  have hw : P.HasAt (b + 107) (linPermWordFuns (b + 107)) := by
    simpa only [List.length_append, linObjectLiftPrefixFuns_length, linRowSystemFuns_length,
      linSliceFuns_length, Nat.add_assoc, Nat.reduceAdd] using
      (Program.HasAt.right (A := (linObjectLiftPrefixFuns b ++ linRowSystemFuns (b + 46) jh) ++
        linSliceFuns (b + 104)) (B := linPermWordFuns (b + 107)) h)
  exact ⟨(hp.block (gs := [linObjectLiftF (b + 1)]) 0 rfl).single,
    (hp.block (gs := [linObjectLiftPositiveF (b + 2) (b + 43) (b + 46) (b + 104) (b + 107)]) 1 rfl).single,
    linObjectQuotientBuildAt_of (hp.block 2 rfl), hp.block 43 rfl,
    linRowSystemAt_of hr, hs, linPermWordAt_of hw⟩

end GI.Impl
