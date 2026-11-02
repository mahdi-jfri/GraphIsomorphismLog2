import Workspace.Impl.LinWreathChoiceGens

/-! A vector transporter with the target stabilizer, for the next fiber of the
paper's affine filtration. The two vector calls use one parameter primitive. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linVectorTarget (I : VecStabInst) (w : Fin I.d → ZMod I.p) : VecStabInst := { I with v := w }

def linVectorTransportOut (I : VecStabInst) (w : Fin I.d → ZMod I.p) (out : Val) : Prop :=
  (out = .list [] ∧ ¬∃ g : gens I.gs, (I.φ g).val.mulVec I.v = w) ∨
    ∃ (g : gens I.gs) (sv : Val), out = .list [encPerm g.val, sv] ∧
      (I.φ g).val.mulVec I.v = w ∧ GensVal I.n sv (vecStabSub (linVectorTarget I w))

private def linVectorSource (i : ℕ) : Expr := .get (arg 0) (.nat i)

def linVectorTransportF (stab choice j : ℕ) : Expr :=
  .letE (.call stab (.var 0))
    (.letE (.call choice (mk2 (.get (linVectorSource 0) (.nat 0)) (.var 1)))
      (.ite (.length (.var 2))
        (mk2 (.get (.var 2) (.nat 0))
          (.prim j (mk4 (linVectorSource 0) (linVectorSource 1) (linVectorSource 2) (arg 1))))
        .nil))

def linVectorTransportFuns (b j : ℕ) : List Expr :=
  [linVectorTransportF (b + 1) (b + 73) j] ++
    linWreathStabFuns (b + 1) j ++ linWreathChoiceGensFuns (b + 73)

theorem linVectorTransportFuns_length (b j : ℕ) : (linVectorTransportFuns b j).length = 96 := rfl

structure linVectorTransportAt (P : Program) (b j : ℕ) (h : VectorStabilizer) : Prop where
  entry : P.funs[b]? = some (linVectorTransportF (b + 1) (b + 73) j)
  stab : linWreathStabAt P (b + 1) j h
  choice : linWreathChoiceGensAt P (b + 73)
  prim : P.prims[j]? = some (vectorStabilizerPrim h)

theorem linVectorTransportAt_of (h : VectorStabilizer) {P : Program} {b j : ℕ}
    (hp : P.HasAt b (linVectorTransportFuns b j))
    (hj : P.prims[j]? = some (vectorStabilizerPrim h)) : linVectorTransportAt P b j h where
  entry := (hp.block (gs := [linVectorTransportF (b + 1) (b + 73) j]) 0 rfl).single
  stab := linWreathStabAt_of h (hp.block 1 rfl) hj
  choice := linWreathChoiceGensAt_of (hp.block 73 rfl)
  prim := hj

end GI.Impl
