import Workspace.Proved.VsBFldA

/-!
# The translation chain of the field line

On `H₁ = ker Λ` the affine action on local coordinates is a translation,
`c ↦ c + f(h)` with `f(h) = vsBAlpha s h 0`, and `f` is a homomorphism. The chain over the
coordinates `j < D` (stage `j` sees `f(h)_j`) is a descent in the sense of `Impl/VsBDesc.lean`.

* `vsBAlpha_lin`: `vsBAlpha s h a = Λ(h) a + f(h)` on `H`.
* `vsBH1`: the subgroup `H₁`; `vsBf_mul`: `f` is additive on it.
* `vsBAj`, `vsBTj`, `vsB_descHypB`.
-/

open Matrix

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv

variable {I : VecStabInst} {s : VsQSt I} (hs : VsQStOK s)
include hs

/-- The affine action is linear plus a translation. -/
theorem vsBAlpha_lin {h : Perm (Fin I.n)} (hh : h ∈ gens s.hs) (a : Fin (vsQD s) → ZMod I.p) :
    vsBAlpha s h a = (vsQLam s h) *ᵥ a + vsBAlpha s h 0 := by
  set x := vsWV I.p I.d s.x
  have h0 : vsBAlpha s h 0 = vsBCo s ((vsQPhi I h) *ᵥ x - x) := by
    rw [vsBAlpha, map_zero, add_zero]
  have hW : (vsQPhi I h) *ᵥ x - x ∈ vsQSp I s.ws := hs.prob.cx h hh
  apply vsBCo_eq hs
  have e : (vsQPhi I h) *ᵥ (x + vsQComb s a) - x - vsQComb s ((vsQLam s h) *ᵥ a + vsBAlpha s h 0) =
      ((vsQPhi I h) *ᵥ x - x - vsQComb s (vsBCo s ((vsQPhi I h) *ᵥ x - x))) +
      ((vsQPhi I h) *ᵥ (vsQComb s a) - vsQComb s ((vsQLam s h) *ᵥ a)) := by
    rw [h0, map_add, mulVec_add]; abel
  rw [e]
  exact add_mem (vsBCo_sub hs hW) (vsQLam_comb hs hh a)

omit hs in
/-- The subgroup `H₁ = ker Λ`. -/
noncomputable def vsBH1 (hs : VsQStOK s) : Subgroup (Perm (Fin I.n)) where
  carrier := {h | h ∈ gens s.hs ∧ vsQLam s h = 1}
  one_mem' := ⟨one_mem _, vsQLam_one hs⟩
  mul_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    exact ⟨mul_mem ha hb, by rw [vsQLam_mul hs ha hb, ha1, hb1, one_mul]⟩
  inv_mem' := by
    rintro a ⟨ha, ha1⟩
    refine ⟨inv_mem ha, ?_⟩
    have := vsB_lam_inv' hs ha
    rwa [ha1, mul_one] at this

theorem vsBH1_le : vsBH1 hs ≤ gens s.hs := fun _ h => h.1

/-- On `H₁` the action is a translation. -/
theorem vsBAlpha_H1 {h : Perm (Fin I.n)} (hh : h ∈ vsBH1 hs) (a : Fin (vsQD s) → ZMod I.p) :
    vsBAlpha s h a = a + vsBAlpha s h 0 := by
  rw [vsBAlpha_lin hs hh.1, hh.2, one_mulVec]

theorem vsBf_mul {g h : Perm (Fin I.n)} (hg : g ∈ vsBH1 hs) (hh : h ∈ vsBH1 hs) :
    vsBAlpha s (g * h) 0 = vsBAlpha s g 0 + vsBAlpha s h 0 := by
  rw [(vsBAlpha_act hs).mul g hg.1 h hh.1, vsBAlpha_H1 hs hg, add_comm]

omit hs in
/-- The action of coordinate stage `j`. -/
noncomputable def vsBAj (s : VsQSt I) (j : ℕ) (h : Perm (Fin I.n)) (y : ZMod I.p) : ZMod I.p :=
  y + (if hj : j < vsQD s then vsBAlpha s h 0 ⟨j, hj⟩ else 0)

omit hs in
/-- The point of coordinate stage `j` seen by a translation. -/
noncomputable def vsBTj (s : VsQSt I) (j : ℕ) (u : Multiplicative (Fin (vsQD s) → ZMod I.p)) :
    ZMod I.p :=
  if hj : j < vsQD s then (Multiplicative.toAdd u) ⟨j, hj⟩ else 0

omit hs in
/-- The map `ψ = f` on `H₁`. -/
noncomputable def vsBPsiB (s : VsQSt I) (h : Perm (Fin I.n)) :
    Multiplicative (Fin (vsQD s) → ZMod I.p) :=
  Multiplicative.ofAdd (vsBAlpha s h 0)

theorem vsBAj_act (j : ℕ) : VsQPAct (vsBH1 hs) (vsBAj s j) where
  one y := by
    have := (vsBAlpha_act hs).one 0
    simp [vsBAj, this]
  mul g hg h hh y := by
    simp only [vsBAj, vsBf_mul hs hg hh]
    split_ifs
    · simp only [Pi.add_apply]; abel
    · simp

/-- **The translation chain is a descent.** -/
theorem vsB_descHypB :
    VsBDescHyp (vsBAj s) 0 (vsBH1 hs) (vsBPsiB s) (vsBTj s) (List.range (vsQD s)) where
  act j _ := vsBAj_act hs j
  hom g hg h hh := by
    simp only [vsBPsiB, vsBf_mul hs hg hh, ← ofAdd_add]
  aT j _ h _ := by simp [vsBAj, vsBTj, vsBPsiB]
  kerT j _ a b := by
    simp only [vsBTj, toAdd_mul, toAdd_inv, toAdd_one]
    split_ifs
    · simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
      rw [neg_add_eq_sub, sub_eq_zero]
    · simp
  fin a ha := by
    apply Multiplicative.toAdd.injective
    funext j
    have := ha j (List.mem_range.mpr j.2)
    simpa [vsBTj, j.2] using this

end GI.Proved
