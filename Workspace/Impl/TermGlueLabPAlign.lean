module

public import Workspace.Impl.TermGlueLabRT

@[expose] public section

/-!
# Any blockwise lift of `τ` gives the same aligned label point

Step 3 of the label program. Proof of Theorem A.23: "Choose a blockwise lift
`k(τ) ∈ K` of `τ N`, and put `y' = y^{k(τ)^{-1}}`." The program's lift (the lift program,
`tmGLPL1_spec`) need not be the lift `rowLift` that `tmGLAlign` uses. Two lifts of `τ` differ
by a blockwise element of `G|_dom` that is trivial at `i0`, hence by a zero-sum `N`-tuple
(Theorem A.18, `tmGL_blockwise`), and a zero-sum tuple keeps the label and the orientation
(`tmGL_lab_zero`). So the label point of `y'` does not depend on the lift (`tmGLP_align_any`).
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Paper Equiv Equiv.Perm

variable {Ω C : Type}

section RT

attribute [local instance] stringRAct

variable {P : Params} {S : State Ω C} {L : GiantLabels S} {I : RowTerminal P S L}

/-- The inverse of a zero-sum tuple is zero-sum. -/
theorem tmGLP_zero_inv {Q : Type*} [Group Q] {N : Subgroup Q} {A : Type*} [CommGroup A]
    {φ : N →* A} {q : ℕ} {μ : Fin q → Q} (hμ : TmGLZero N φ μ) :
    TmGLZero N φ fun i => (μ i)⁻¹ := by
  refine ⟨fun i => N.inv_mem (hμ.1 i), ?_⟩
  rw [Finset.prod_congr rfl fun i _ => phiT_inv (hμ.1 i), Finset.prod_inv_distrib, hμ.2, inv_one]

/-- **Two blockwise lifts of `h` differ by a zero-sum tuple**: if `cleanRowPerm y ∈ G|_dom`
and `y_{i0} = h`, then `y = k(h) ν` with `ν = k(h)⁻¹ y` zero-sum. -/
theorem tmGLP_lift_zero {h : Perm I.B} (hh : h ∈ I.Hb) {y : Fin L.q → Perm I.B}
    (hy : cleanRowPerm I.e y ∈ S.domGroup) (hy0 : y I.i0 = h) :
    TmGLZero I.Nb I.φ ((rowLift I.e I.i0 h)⁻¹ * y) ∧
      ∀ i, y i = rowLift I.e I.i0 h i * ((rowLift I.e I.i0 h)⁻¹ * y) i := by
  obtain ⟨hk, hk0⟩ := rowLift_spec I.e I.i0 hh
  have hG : cleanRowPerm I.e ((rowLift I.e I.i0 h)⁻¹ * y) ∈ S.domGroup := by
    rw [map_mul, map_inv]; exact S.domGroup.mul_mem (S.domGroup.inv_mem hk) hy
  have h0 : ((rowLift I.e I.i0 h)⁻¹ * y) I.i0 ∈ I.Nb := by
    show (rowLift I.e I.i0 h I.i0)⁻¹ * y I.i0 ∈ I.Nb
    rw [hk0, hy0, inv_mul_cancel]; exact I.Nb.one_mem
  exact ⟨tmGL_blockwise I hG h0, fun i => by simp⟩

/-- **The aligned label point does not depend on the lift of `τ`.** -/
theorem tmGLP_align_any {r τ : Perm I.B} (hτ : τ ∈ tmGlRes I r)
    {rep : Set (I.B → C) → (I.B → C)} (hrep : TmGLRep I.Nb (rowTuple I.e S.x) rep)
    {y : Fin L.q → Perm I.B} (hy : cleanRowPerm I.e y ∈ S.domGroup) (hy0 : y I.i0 = τ) :
    tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (rowAct (fun i => (y i)⁻¹) 1 (rowTuple I.e S.y)) =
      tmGLPt I.Nb I.φ (rowTuple I.e S.x) rep (tmGLAlign I τ) := by
  have hτH : τ ∈ I.Hb := hτ.1.1
  obtain ⟨hk, hk0⟩ := rowLift_spec I.e I.i0 hτH
  set k := rowLift I.e I.i0 τ with hkdef
  -- `μ = k⁻¹ y` is a zero-sum tuple
  have hμG : cleanRowPerm I.e (k⁻¹ * y) ∈ S.domGroup := by
    rw [map_mul, map_inv]; exact S.domGroup.mul_mem (S.domGroup.inv_mem hk) hy
  have hμ0 : (k⁻¹ * y) I.i0 ∈ I.Nb := by
    show (k I.i0)⁻¹ * y I.i0 ∈ I.Nb
    rw [hk0, hy0, inv_mul_cancel]; exact I.Nb.one_mem
  have hμ : TmGLZero I.Nb I.φ (k⁻¹ * y) := tmGL_blockwise I hμG hμ0
  -- `ν_i = k_i μ_i⁻¹ k_i⁻¹` is zero-sum
  have hcls : ∀ i, τ⁻¹⁻¹ * (k i)⁻¹ ∈ I.Nb :=
    tmGL_cls_inv I.normalizes hτH (I.lift_mem hτH)
  have hν := tmGL_conj_zero I.normalizes (tmGL_kerI I) (I.Hb.inv_mem hτH) (e := fun i => (k i)⁻¹)
    hcls (tmGLP_zero_inv hμ) 1
  have hrow : rowAct (fun i => (y i)⁻¹) 1 (rowTuple I.e S.y) =
      rowAct (fun i => ((k i)⁻¹)⁻¹ * ((k⁻¹ * y) i)⁻¹ * (k i)⁻¹) 1 (tmGLAlign I τ) := by
    rw [tmGLAlign, ← rowAct_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply, Pi.inv_apply, ← hkdef]
    group
  have hz := tmGL_align_types hτ
  obtain ⟨h1, h2⟩ := tmGL_lab_zero hrep hz hν
  simp only [Perm.one_apply] at h1 h2
  rw [hrow]
  exact Prod.ext h1 h2

end RT

end GI.Impl
