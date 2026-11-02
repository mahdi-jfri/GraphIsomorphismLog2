import Workspace.Impl.TermGlueLabSOut

/-!
# The answer of the label step is the label coset (step 6, the mathematics)

Proof of Theorem A.23: "Adjoining `N` lifts the resulting label stabilizer and
transporter back to `D`." `tmGLS_lab_ans` reads the result of the output program
(`TmGLSOutRes`, from `tmGLSOut_spec`) as a canonical answer of the label coset `tmGlLab I r`:

* if the affine answer is `[]`, the transporter in the supplement is empty, and so is the label
  coset (`tmGL_lab_out_empty`);
* if the affine answer is `[t, gens L]`, the label coset is `t τ · τ⁻¹ (L ⊔ N) τ`
  (`tmGL_lab_out`), and the output `[t τ, τ⁻¹ hs τ]` with `⟨hs⟩ = ⟨L⟩ ⊔ N` is this coset.

The terminal is the one of `TmGLPNeSpec`: `I = (RowForm.ofPure …).rowTerminal …`, with
`B = Fin m` (`tmGLSI`).
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Lang Equiv
open GI.Cited (Val encPerm encGroup gens)
open scoped Pointwise

variable {Ω C : Type}

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}

/-- The row terminal of the label step, with rows `Fin m`. -/
noncomputable abbrev tmGLSI (P : Params) (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {m : ℕ}
    (h0 : 0 < m) (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E)
    (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
    (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
    (hqα : (S.N : ℝ) ^ P.α < L.q) : RowTerminal P S L :=
  (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P htr hcard hsN hN hqα

/-- The label transporter in a subgroup `Sg`: `{s ∈ Sg | F_s p_x = p_{y'}}`. -/
def tmGLSTrans (I : RowTerminal P S L) (rep : Set (I.B → C) → (I.B → C)) (τ : Perm I.B)
    (Sg : Subgroup (Perm I.B)) : Set (Perm I.B) :=
  {s | s ∈ Sg ∧ tmGLF I.normalizes (tmGL_kerI I) rep (rowLift I.e I.i0) s
    (tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (rowTuple I.e S.x)) =
    tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (tmGLAlign I τ)}

/-- **The output is a canonical answer of the label coset.** -/
theorem tmGLS_lab_ans (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {m : ℕ} (h0 : 0 < m)
    (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E)
    (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
    (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
    (hqα : (S.N : ℝ) ^ P.α < L.q) {σN gs : List (Perm (Fin m))}
    (hσN : gens σN = (tmGLSI P hnat hq h0 E hP htr hcard hsN hN hqα).Nb) {r τ : Perm (Fin m)}
    (hτ : τ ∈ tmGlRes (tmGLSI P hnat hq h0 E hP htr hcard hsN hN hqα) r)
    (hSN : gens gs ⊔ (tmGLSI P hnat hq h0 E hP htr hcard hsN hN hqα).Nb =
      Aut (tmGLSI P hnat hq h0 E hP htr hcard hsN hN hqα).Hb
        (types (tmGLSI P hnat hq h0 E hP htr hcard hsN hN hqα).Nb
          (rowTuple (tmGLSI P hnat hq h0 E hP htr hcard hsN hN hqα).e S.x)) ⊓
        tmRad (tmGLSI P hnat hq h0 E hP htr hcard hsN hN hqα))
    {rep : Set (Fin m → C) → (Fin m → C)}
    (hrep : TmGLRep (tmGLSI P hnat hq h0 E hP htr hcard hsN hN hqα).Nb
      (rowTuple (tmGLSI P hnat hq h0 E hP htr hcard hsN hN hqα).e S.x) rep)
    {u w : Val}
    (hu : TmGLAffOut m u (tmGLSTrans (tmGLSI P hnat hq h0 E hP htr hcard hsN hN hqα) rep τ
      (gens gs)))
    (hw : TmGLSOutRes σN τ u w) :
    AnsC (Equiv.refl (Fin m)) w (tmGlLab (tmGLSI P hnat hq h0 E hP htr hcard hsN hN hqα) r) := by
  set I := tmGLSI P hnat hq h0 E hP htr hcard hsN hN hqα
  rcases hu with ⟨rfl, hT⟩ | ⟨t', L', rfl, hT⟩
  · -- no transporter
    rcases hw with ⟨-, rfl⟩ | ⟨t, L, hs, hu, -⟩
    · exact Or.inl ⟨rfl, tmGL_lab_out_empty hrep hτ hSN hT⟩
    · cases hu
  · rcases hw with ⟨hu, -⟩ | ⟨t, L, hs, hu, rfl, hl, hg⟩
    · cases hu
    · simp only [Val.list.injEq, List.cons.injEq, and_true] at hu
      obtain ⟨h1, h2⟩ := hu
      have e1 := encPerm_injective h1
      subst e1
      have e2 := encGroup_injective h2
      subst e2
      have hlab := tmGL_lab_out hrep hτ hSN hT
      refine Or.inr ⟨t' * τ, hs.map fun x => τ⁻¹ * x * τ, rfl, by simpa using hl, ?_⟩
      have hc : gens (hs.map fun x => τ⁻¹ * x * τ) =
          (gens hs).map (MulAut.conj τ⁻¹).toMonoidHom := by
        have := sup_gens_conj τ⁻¹ hs
        simpa only [inv_inv] using this
      rw [tmCs_toFin_refl, hlab, hc, hg, hσN]
      rfl

end GI.Impl
