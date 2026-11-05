module

public import Workspace.Impl.TermGlueLabNDef
public import Workspace.Impl.TermGlueLabPAlign

@[expose] public section

/-!
# The driver of the label program: links between the programs' strings and the terminal's

The label programs of steps 2 and 3 work with the rows `tmRowStr S E (.inl i)` of
`x` and with the target `y'` aligned by the program's own lift `y` of `τ`. Step 6 and the
contract lemmas speak of `rowTuple I.e S.x` and of `tmGLAlign I τ` (aligned by `rowLift`).

* `tmGLN_rowX`: the two forms of the rows of `x` agree (by definition of `RowForm.ofPure`).
* `tmGLN_lab_align`: the label of the target aligned by any blockwise lift `y` of `τ` is the
  label of `tmGLAlign I τ`. This is the first coordinate of `tmGLP_align_any`.
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Paper Equiv

attribute [local instance] stringRAct

variable {Ω C : Type} {Pp : Params} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}

theorem tmGLN_rowX (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {m : ℕ} (h0 : 0 < m)
    (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E)
    (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
    (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
    (hqα : (S.N : ℝ) ^ Pp.α < L.q) :
    (fun i => tmRowStr S E (.inl i)) =
      @id (Fin L.q → Fin m → C) (rowTuple (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).e S.x) :=
  rfl

theorem tmGLN_lab_align {I : RowTerminal Pp S L} {r τ : Perm I.B} (hτ : τ ∈ tmGlRes I r)
    {rep : Set (I.B → C) → (I.B → C)} (hrep : TmGLRep I.Nb (rowTuple I.e S.x) rep)
    {y : Fin L.q → Perm I.B} (hy : cleanRowPerm I.e y ∈ S.domGroup) (hy0 : y I.i0 = τ) :
    tmGLLab I.Nb I.φ (rowTuple I.e S.x) rep (rowAct (fun i => (y i)⁻¹) 1 (rowTuple I.e S.y)) =
      tmGLLab I.Nb I.φ (rowTuple I.e S.x) rep (tmGLAlign I τ) :=
  congrArg Prod.fst (tmGLP_align_any hτ hrep hy hy0)

end GI.Impl
