module

public import Workspace.Impl.TermGlueLabPStep5
public import Workspace.Impl.TermGlueLabS6

@[expose] public section

/-!
# Step 5 meets the interface of step 6

Step 6 (`TermGlueLabS6.lean`) reads the step-5 result through
`TmGLS5Out modV items w`: `w = [[c0, c1, c2, modV], items]` with `modV = linVecVal (tmGLModZ m)`
and `items` the `tmGLAffItem` list. `tmGLP_step5_s5Out` shows that the result of
`tmGLPStep5_spec` (`TmGLPStep5Out`) has this form, with `m = tmGLQMod D` and the items of the
contract's `ρ = tmGLρE E' (tmGLlam …)`, `c = tmGLcE E' (tmGLo (tmGLPRep N x j0) k)`, for every
coordinate map `E'` with `E'(class of z) = z V mod D` (`tmGLPE_g`).

This is the case where some type repeats (no orientation coordinate). In the case where all
types are distinct the moduli are `Fin.cons 2 (tmGLQMod D)`; that block is handled elsewhere.
-/

namespace GI.Impl

open GI.Multicoset Equiv
open GI.Algorithm (State)
open GI.Cited (Val encPerm encGroup encIntMatrix gens)
open GI.Lang (linVecVal)

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω]
variable {N H : Subgroup (Perm (Fin n))} {A : Type*} [CommGroup A] {φ : N →* A}

/-- The moduli vector of the context is the moduli value of the affine input. -/
theorem tmGLP_modV {t : ℕ} {D : Matrix (Fin t) (Fin t) ℤ} (hpos : ∀ i, 0 < D i i) :
    linVecVal (fun i => D i i) = linVecVal (tmGLModZ (tmGLQMod D)) := by
  congr 1
  funext i
  simp only [tmGLModZ, tmGLQMod]
  exact (Int.toNat_of_nonneg (hpos i).le).symm

variable {Ω₀ C₀ : Type} {S : State Ω₀ C₀} {L : GI.Algorithm.GiantLabels S}

/-- **The step-5 result in the form step 6 reads.** -/
theorem tmGLP_step5_s5Out (hn : Normalizes H N) (hker : TmGLKer N H φ) (hNH : N ≤ H)
    {k : Perm (Fin n) → Fin L.q → Perm (Fin n)} (hk : TmGLLift N H φ k)
    (E : Fin n × Fin L.q ≃ S.dom) (i0 j0 : Fin L.q) {x : Fin L.q → Ω}
    (hyk : ∀ h ∈ H, ∀ y : Fin L.q → Perm (Fin n), GI.Paper.cleanRowPerm E y ∈ S.domGroup →
      y i0 = h → ∃ ν, TmGLZero N φ ν ∧ ∀ i, y i = k h i * ν i)
    {σS σN bs : List (Perm (Fin n))} (hN : gens σN = N)
    {gs : List (Perm (Fin n))} (hgs : gens gs ≤ Aut H (types N x)) {w : Val}
    (hw : TmGLPStep5Out E i0 σS σN bs x gs w) :
    ∃ (M : Matrix (Fin σN.length) (Fin σN.length) ℤ) (Z : Matrix (Fin bs.length) (Fin σN.length) ℤ)
      (U V D : Matrix (Fin σN.length) (Fin σN.length) ℤ),
      linPermPresentation σS σN M ∧
      (∀ j : Fin bs.length, TmGLPCoordOf σN (bs[j.val]'j.isLt) (Z j)) ∧ IsUnit V.det ∧
      (∀ i, 0 < D i i) ∧
      (∀ w, (∃ y, Matrix.vecMul y (tmGLQStack M Z) = w) ↔ ∀ i, D i i ∣ (Matrix.vecMul w V) i) ∧
      U * V = 1 ∧ V * U = 1 ∧
      ∀ (E' : Additive (tmGLV N φ x) ≃+ tmGLVec (tmGLQMod D)),
        (∀ z, E' (tmGLPg N φ x (fun i => σN[i.val]) z) = tmGLQMap V D z) →
        TmGLS5Out (linVecVal (tmGLModZ (tmGLQMod D)))
          (gs.attach.map fun g => tmGLAffItem gs (tmGLQMod D) (tmGLρE E' (tmGLlam hn hker hgs hNH))
            (tmGLcE E' (tmGLo (tmGLPRep N x j0) k)) ⟨g.1, Subgroup.subset_closure g.2⟩) w := by
  obtain ⟨M, Z, U, V, D, ws, rfl, hMp, hZ, hV, hpos, hrel, hUV, hVU, hws⟩ := hw
  refine ⟨M, Z, U, V, D, hMp, hZ, hV, hpos, hrel, hUV, hVU, fun E' hE' => ?_⟩
  refine ⟨.nat σN.length, encIntMatrix U, encIntMatrix V, ?_⟩
  have hitems := tmGLP_items_eq (F := fun g => tmGLAffItem gs (tmGLQMod D)
      (tmGLρE E' (tmGLlam hn hker hgs hNH)) (tmGLcE E' (tmGLo (tmGLPRep N x j0) k)) g)
    (fun g hg w hgw => tmGLP_gen_item hn hker hNH hk E i0 j0 hyk hN hpos hUV E' hE' hgs
      ⟨g, Subgroup.subset_closure hg⟩ hgw) hws
  rw [← hitems, ← tmGLP_modV hpos]
  rfl

end GI.Impl
