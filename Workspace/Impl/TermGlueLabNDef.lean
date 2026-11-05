module

public import Workspace.Impl.TermGlueLabSCall
public import Workspace.Impl.TermGlueLabPStep5

@[expose] public section

/-!
# The driver of the label program: the results of step 5 and of the vector program

Proof of Theorem A.23. The driver of the nonempty label part runs step 5 once,
then the vector program on step 5's context, then step 6 on both. Step 6 (`tmGLS6F`) calls a
step-5 function itself (index `s5`). The driver points that index at the trampoline
`tmGLNIdF`, which returns its input. So step 6 reads the step-5 output that the driver
computed, and the vectors and the items use the same coordinates `[t, U, V, d]`. (Step 5 is
not deterministic: the cited Hermite and Smith forms may return any valid `U`, `V`.)

This file states what the driver needs from step 5 and from the vector program, in the forms
of the step-6 call lemmas `tmGLS_call'` (some type repeats) and `tmGLS_call` (all types
distinct, orientation coordinate in front).

* `TmGLNS5Res`: the step-5 output is `[ctx, items]`. The context holds `t`, `U`, `V` and the
  moduli, with `0 < D i i`, and some coordinates `Ev` of the torsor group with
  `Ev(class of z) = z V mod D` (`tmGLPE_g`). The items are the contract items `tmGLAffItem` of
  `tmGLS_call'`, or, when all types are distinct, those of `tmGLS_call` with moduli
  `Fin.cons 2 (tmGLQMod D)` (the `2` is the orientation coordinate).
* `TmGLNVecRes`: for every such context and every `Ev` as above, the two vectors are
  `Ev(p_{y'})` and `Ev(p_x)`, the label points of the aligned target and of `x`.

In the plain case `TmGLNS5Res` follows from `tmGLPStep5_spec` and `tmGLP_step5_s5Out`.
The vectors are the content of `tmGLS_lab_vec` and `tmGLS_pt_vec`.
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Lang Equiv
open GI.Cited (Val encPerm encGroup encIntMatrix gens)
open scoped Pointwise

attribute [local instance] stringRAct
set_option backward.isDefEq.respectTransparency false

/-- **The trampoline**: return the input. Step 6 calls it in place of step 5. -/
def tmGLNIdF : Expr := .var 0

theorem tmGLN_id_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some tmGLNIdF) (v : Val) :
    FunDet P f v v (v.wt + 1) :=
  FunDet.intro hf (Det.var' (P := P) (env := [v]) (i := 0) rfl)

variable {Ω C : Type} {Pp : Params} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}
  (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {m : ℕ} (h0 : 0 < m)
  (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E)
  (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
    (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
  (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
  (hqα : (S.N : ℝ) ^ Pp.α < L.q)

local notation "𝕀" => tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα
set_option quotPrecheck false in
local notation "𝕩" => @id (Fin L.q → Fin m → C) (rowTuple (𝕀).e S.x)
set_option quotPrecheck false in
local notation "ℕb" => @id (Subgroup (Perm (Fin m))) (𝕀).Nb
set_option quotPrecheck false in
local notation "ℍb" => @id (Subgroup (Perm (Fin m))) (𝕀).Hb

/-- The context of the orientation case: the moduli carry the `2` in front. -/
def tmGLNOCtx {t : ℕ} (U V : Matrix (Fin t) (Fin t) ℤ) (d : Fin t → ℤ) : Val :=
  .list [.nat t, encIntMatrix U, encIntMatrix V, linVecVal (Fin.cons 2 d : Fin (t + 1) → ℤ)]

/-- **The result of step 5 for fixed data** `U`, `V`, `D` and items `ws`: the body of
`TmGLNS5Res`. -/
abbrev TmGLNS5At (σN gs : List (Perm (Fin m))) (hgs : gens gs ≤ Aut ℍb (types ℕb (𝕩)))
    (U V D : Matrix (Fin σN.length) (Fin σN.length) ℤ) (ws : List Val) (o5 : Val) : Prop :=
    (∀ i, 0 < D i i) ∧
    ((¬ (types ℕb (𝕩)).Nodup ∧
      o5 = .list [tmGLPMCtx U V (fun i => D i i), .list ws] ∧
      ∃ Ev : Additive (tmGLV ℕb (𝕀).φ (𝕩)) ≃+ tmGLVec (tmGLQMod D),
        (∀ z, Ev (tmGLPg ℕb (𝕀).φ (𝕩) (fun i => σN[i.val]'i.isLt) z) =
          tmGLQMap V D z) ∧
        ws = gs.attach.map fun g => tmGLAffItem gs (tmGLQMod D)
          (tmGLρE Ev (tmGLlam ((𝕀).normalizes : GI.Multicoset.Normalizes ℍb ℕb) (tmGL_kerI 𝕀)
            hgs (𝕀).Nb_le))
          (tmGLcE Ev (tmGLo (tmGLPRep ℕb (𝕩) (𝕀).i0) (rowLift (𝕀).e (𝕀).i0)))
          ⟨g.1, Subgroup.subset_closure g.2⟩) ∨
    ((types ℕb (𝕩)).Nodup ∧
      o5 = .list [tmGLNOCtx U V (fun i => D i i), .list ws] ∧
      ∃ (E : Additive (tmGLV ℕb (𝕀).φ (𝕩)) ≃+ tmGLVec (tmGLQMod D))
        (Ev : Additive (tmGLV ℕb (𝕀).φ (𝕩) × ℤˣ) ≃+
          tmGLVec (Fin.cons 2 (tmGLQMod D) : Fin (σN.length + 1) → ℕ)),
        (∀ z, E (tmGLPg ℕb (𝕀).φ (𝕩) (fun i => σN[i.val]'i.isLt) z) =
          tmGLQMap V D z) ∧
        (∀ p, Ev (Additive.ofMul p) = tmGLPCons 2 (tmGLQMod D)
          (tmGLPUnits (Additive.ofMul p.2), E (Additive.ofMul p.1))) ∧
        ws = gs.attach.map fun g => tmGLAffItem gs (Fin.cons 2 (tmGLQMod D))
          (tmGLρE Ev (tmGLlamO ((𝕀).normalizes : GI.Multicoset.Normalizes ℍb ℕb)
            (tmGL_kerI 𝕀) hgs (𝕀).Nb_le))
          (tmGLcE Ev (tmGLoO (tmGLPRep ℕb (𝕩) (𝕀).i0) (rowLift (𝕀).e (𝕀).i0)))
          ⟨g.1, Subgroup.subset_closure g.2⟩))

/-- **The result of step 5** at the row terminal `I`, for the supplement generators `gs`, with
the first-row representatives `tmGLPRep` (row `i0`). -/
def TmGLNS5Res (σN gs : List (Perm (Fin m))) (o5 : Val) : Prop :=
  ∃ (hgs : gens gs ≤ Aut ℍb (types ℕb (𝕩)))
    (U V D : Matrix (Fin σN.length) (Fin σN.length) ℤ) (ws : List Val),
    TmGLNS5At hnat hq h0 E hP htr hcard hsN hN hqα σN gs hgs U V D ws o5

/-- **The result of the vector program** for the context `[t, U, V, d]` of a step-5 result:
for every coordinate map `Ev` that reads classes through `V` and `D`, `[vv, ww]` are the
vectors of the label points of `y'` and `x`. -/
def TmGLNVecRes (σN : List (Perm (Fin m))) (τ : Perm (Fin m))
    (V D : Matrix (Fin σN.length) (Fin σN.length) ℤ) (vv ww : Val) : Prop :=
    (¬ (types ℕb (𝕩)).Nodup →
      ∀ Ev : Additive (tmGLV ℕb (𝕀).φ (𝕩)) ≃+ tmGLVec (tmGLQMod D),
        (∀ z, Ev (tmGLPg ℕb (𝕀).φ (𝕩) (fun i => σN[i.val]'i.isLt) z) =
          tmGLQMap V D z) →
        vv = linVecVal (tmGLVecZ (Ev (Additive.ofMul (tmGLLab ℕb (𝕀).φ (𝕩)
          (tmGLPRep ℕb (𝕩) (𝕀).i0) (@id (Fin L.q → Fin m → C) (tmGLAlign 𝕀 τ)))))) ∧
        ww = linVecVal (tmGLVecZ (Ev (Additive.ofMul (tmGLLab ℕb (𝕀).φ (𝕩)
          (tmGLPRep ℕb (𝕩) (𝕀).i0) (𝕩)))))) ∧
    ((types ℕb (𝕩)).Nodup →
      ∀ (E : Additive (tmGLV ℕb (𝕀).φ (𝕩)) ≃+ tmGLVec (tmGLQMod D))
        (Ev : Additive (tmGLV ℕb (𝕀).φ (𝕩) × ℤˣ) ≃+
          tmGLVec (Fin.cons 2 (tmGLQMod D) : Fin (σN.length + 1) → ℕ)),
        (∀ z, E (tmGLPg ℕb (𝕀).φ (𝕩) (fun i => σN[i.val]'i.isLt) z) =
          tmGLQMap V D z) →
        (∀ p, Ev (Additive.ofMul p) = tmGLPCons 2 (tmGLQMod D)
          (tmGLPUnits (Additive.ofMul p.2), E (Additive.ofMul p.1))) →
        vv = linVecVal (tmGLVecZ (Ev (Additive.ofMul (tmGLPt ℕb (𝕀).φ (𝕩)
          (tmGLPRep ℕb (𝕩) (𝕀).i0) (@id (Fin L.q → Fin m → C) (tmGLAlign 𝕀 τ)))))) ∧
        ww = linVecVal (tmGLVecZ (Ev (Additive.ofMul (tmGLPt ℕb (𝕀).φ (𝕩)
          (tmGLPRep ℕb (𝕩) (𝕀).i0) (𝕩))))))

end GI.Impl
