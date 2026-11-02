import Workspace.Proved.VsBComb
import Workspace.Proved.VsBFldC
import Workspace.Proved.VsQAlg

/-!
# The mathematics of the case `T = 0`

With `T = f(H₁) = 0` and a generator `g₀` with `f(g₀) ≠ 0`, solve `(Λ(g₀) - 1) m = f(g₀)`. Then
`f(h) = (Λ(h) - 1) m` on `H`, the solutions are the `h` with `Λ(h) m = t + m`, and the stabilizer
is `H₁`. If `u = t + m ≠ 0`, the element `τ ∈ L` with `τ m = u` is found by solving with the images
`Lb_k m`, which span everything.
-/

open Matrix

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv

variable {I : VecStabInst}

theorem vsWLin_mem_sp {p d : ℕ} {A : List (List ℕ)} (hA : A.length = d) (v : Fin d → ZMod p) :
    vsWLin p d A v ∈ vsWSp p d A := by
  rw [vsWLin_apply hA, ← vsWComb_range]
  exact LinearMap.mem_range_self _ _

theorem vsWLin_comb {p d : ℕ} {A : List (List ℕ)} (hA : A.length = d) (a : List ℕ) :
    vsWLin p d A (vsWV p d a) = ∑ i : Fin A.length, vsF p a i • vsWV p d A[i] := by
  rw [vsWLin_apply hA, vsWComb_apply]
  rfl

section

variable {s : VsQSt I} (hs : VsQStOK s)
include hs

/-- An element of `L` that kills no nonzero vector is onto. -/
theorem vsB_surj (hdom : VsBDom s) {X : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)}
    (hX : X ∈ vsBLamA s) (hX0 : X ≠ 0) (v : Fin (vsQD s) → ZMod I.p) : ∃ w, X *ᵥ w = v := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  have hinj := (hdom X hX).resolve_left hX0
  have hi : Function.Injective (Matrix.toLin' X) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hw
    exact (Submodule.mem_bot _).mpr (hinj w hw)
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.mp hi) v
  exact ⟨w, by rwa [Matrix.toLin'_apply] at hw⟩

omit hs in
theorem vsB_lamL_wM (g : Perm (Fin I.n)) : vsWM I.p (vsQD s) (vsQL (vsQLam s g)ᵀ) = vsQLam s g := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  rw [vsWM, vsFMatrix_vsQL, transpose_transpose]

/-- The stored `Λ(g) - 1`. -/
noncomputable def vsBR (s : VsQSt I) (g : Perm (Fin I.n)) : List (List ℕ) :=
  vsWSubC I.p 1 (vsQL (vsQLam s g)ᵀ)

omit hs in
theorem vsBR_sq (g : Perm (Fin I.n)) : VsWSq I.p (vsQD s) (vsBR s g) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have := vsQL_sq (p := I.p) (vsQLam s g)ᵀ
  exact vsWSubC_fit I.prime.pos ⟨this.2, this.1⟩

omit hs in
theorem vsBR_wM (g : Perm (Fin I.n)) : vsWM I.p (vsQD s) (vsBR s g) = vsQLam s g - 1 := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have := vsQL_sq (p := I.p) (vsQLam s g)ᵀ
  rw [vsBR, vsWSubC_matrix I.prime.pos I.prime.one_lt.le ⟨this.2, this.1⟩, vsB_lamL_wM]
  simp

theorem vsB0_m_sp (hdom : VsBDom s) (hT : ∀ k ∈ vsBH1 hs, vsBAlpha s k 0 = 0) {g₀ : Perm (Fin I.n)}
    (hg₀ : g₀ ∈ gens s.hs) (hne : vsBAlpha s g₀ 0 ≠ 0) :
    vsWV I.p (vsQD s) (vsQVec (vsBAlpha s g₀ 0)) ∈ vsWSp I.p (vsQD s) (vsBR s g₀) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hX : vsQLam s g₀ - 1 ∈ vsBLamA s := sub_mem (vsB_lam_mem hs hg₀) (one_mem _)
  have hX0 : vsQLam s g₀ - 1 ≠ 0 := by
    intro h0
    exact hne (hT g₀ ⟨hg₀, sub_eq_zero.mp h0⟩)
  obtain ⟨w, hw⟩ := vsB_surj hs hdom hX hX0 (vsBAlpha s g₀ 0)
  rw [vsWV_vsQVec, ← hw]
  have := vsWLin_mem_sp (p := I.p) (vsBR_sq (s := s) g₀).2 w
  rwa [vsWLin, Matrix.toLin'_apply, vsBR_wM] at this

theorem vsB0_m {g₀ : Perm (Fin I.n)} {a : List ℕ}
    (ha : ∑ i : Fin (vsBR s g₀).length, vsF I.p a i • vsWV I.p (vsQD s) (vsBR s g₀)[i] =
      vsWV I.p (vsQD s) (vsQVec (vsBAlpha s g₀ 0))) :
    (vsQLam s g₀ - 1) *ᵥ vsWV I.p (vsQD s) a = vsBAlpha s g₀ 0 := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have h := vsWLin_comb (p := I.p) (vsBR_sq (s := s) g₀).2 a
  rw [ha, vsWV_vsQVec, vsWLin, Matrix.toLin'_apply, vsBR_wM] at h
  exact h

omit hs in
/-- The vectors `X m` for `X` in the span of stored matrices lie in the span of the `Lb_k m`. -/
theorem vsB_apply_span {Lb : List (List (List ℕ))} (hsq : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M) (a : List ℕ)
    {X : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)}
    (hX : X ∈ Submodule.span (ZMod I.p) {X | ∃ M ∈ Lb, vsWM I.p (vsQD s) M = X}) :
    X *ᵥ vsWV I.p (vsQD s) a ∈ vsWSp I.p (vsQD s) (Lb.map fun M => vsFRowMul I.p a M (vsWZ (vsQD s))) := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨M, hM, rfl⟩ := hX
    apply Submodule.subset_span
    refine ⟨vsFRowMul I.p a M (vsWZ (vsQD s)), List.mem_map_of_mem hM, ?_⟩
    rw [vsWV_img (hsq M hM).2 (fun r hr => ((hsq M hM).1 r hr).2.le), vsWLin, Matrix.toLin'_apply]
  | zero => rw [zero_mulVec]; exact zero_mem _
  | add X Y _ _ hX hY => rw [add_mulVec]; exact add_mem hX hY
  | smul c X _ hX => rw [smul_mulVec]; exact Submodule.smul_mem _ c hX

/-- **The images span everything** (on a field line, for `m ≠ 0`). -/
theorem vsB0_imgs_top (hdom : VsBDom s) (hD : 1 ≤ vsQD s)
    (hspan : ∀ v, ∃ X ∈ vsBLamA s, X *ᵥ vsBe0 s hD = v) {Lb : List (List (List ℕ))}
    (hLb : ∀ X, X ∈ Submodule.span (ZMod I.p) {X | ∃ M ∈ Lb, vsWM I.p (vsQD s) M = X} ↔ X ∈ vsBLamA s)
    (hsq : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M) {a : List ℕ} (hm : vsWV I.p (vsQD s) a ≠ 0) :
    vsWSp I.p (vsQD s) (Lb.map fun M => vsFRowMul I.p a M (vsWZ (vsQD s))) = ⊤ := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  set m := vsWV I.p (vsQD s) a
  set B := (vsBLamA s).map (Matrix.toLinAlgEquiv' : _ ≃ₐ[ZMod I.p] _).toAlgHom
  have hF : ∀ b ∈ B, b = 0 ∨ ∀ v, b v = 0 → v = 0 := by
    rintro _ ⟨X, hX, rfl⟩
    rcases hdom X hX with h | h
    · left; simp [h]
    · right; intro v hv; exact h v (by simpa [Matrix.toLinAlgEquiv'_apply] using hv)
  have hsp : Submodule.map (LinearMap.applyₗ (vsBe0 s hD)) (Subalgebra.toSubmodule B) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨X, hX, rfl⟩ := hspan v
    exact ⟨Matrix.toLinAlgEquiv' X, ⟨X, hX, rfl⟩, by simp [Matrix.toLinAlgEquiv'_apply]⟩
  set W := Submodule.map (LinearMap.applyₗ m) (Subalgebra.toSubmodule B)
  have hW : ∀ b ∈ B, ∀ w ∈ W, b w ∈ W := by
    rintro _ ⟨X, hX, rfl⟩ _ ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
    refine ⟨Matrix.toLinAlgEquiv' (X * Y), ⟨X * Y, mul_mem hX hY, rfl⟩, ?_⟩
    simp [Matrix.toLinAlgEquiv'_apply, mulVec_mulVec]
  have hW0 : W ≠ ⊥ := by
    intro h
    have : m ∈ W := ⟨Matrix.toLinAlgEquiv' 1, ⟨1, one_mem _, rfl⟩, by simp [Matrix.toLinAlgEquiv'_apply]⟩
    rw [h, Submodule.mem_bot] at this
    exact hm this
  have htop := vsFSpin_irred B hF hsp W hW hW0
  rw [eq_top_iff, ← htop]
  rintro _ ⟨_, ⟨X, hX, rfl⟩, rfl⟩
  have := vsB_apply_span hsq a ((hLb X).mpr hX)
  simpa [Matrix.toLinAlgEquiv'_apply] using this

omit hs in
/-- **The element `τ`.** -/
theorem vsB0_tau {Lb : List (List (List ℕ))}
    (hLb : ∀ X, X ∈ Submodule.span (ZMod I.p) {X | ∃ M ∈ Lb, vsWM I.p (vsQD s) M = X} ↔ X ∈ vsBLamA s)
    (hsq : ∀ M ∈ Lb, VsWSq I.p (vsQD s) M) (a c u : List ℕ)
    (hc : ∑ k : Fin (Lb.map fun M => vsFRowMul I.p a M (vsWZ (vsQD s))).length,
      vsF I.p c k • vsWV I.p (vsQD s) (Lb.map fun M => vsFRowMul I.p a M (vsWZ (vsQD s)))[k] =
      vsWV I.p (vsQD s) u) :
    vsWM I.p (vsQD s) (vsBCombL I.p (vsQD s) c Lb) ∈ vsBLamA s ∧
      vsWM I.p (vsQD s) (vsBCombL I.p (vsQD s) c Lb) *ᵥ vsWV I.p (vsQD s) a = vsWV I.p (vsQD s) u := by
  rw [vsBComb_wM c hsq]
  refine ⟨(hLb _).mp (Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ (Submodule.subset_span ?_)), ?_⟩
  · have hk' := Finset.mem_range.mp hk
    exact ⟨Lb.getD k [], by rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem hk', rfl⟩
  · rw [← hc, Matrix.sum_mulVec]
    rw [← Fin.sum_univ_eq_sum_range (fun k => (((c.getD k 0 : ℕ) : ZMod I.p) • vsWM I.p (vsQD s) (Lb.getD k []))
      *ᵥ vsWV I.p (vsQD s) a) Lb.length]
    have hl : (Lb.map fun M => vsFRowMul I.p a M (vsWZ (vsQD s))).length = Lb.length := List.length_map _
    refine Fintype.sum_equiv (finCongr hl.symm) _ _ fun k => ?_
    simp only [finCongr_apply, Fin.coe_cast, smul_mulVec, vsF_apply]
    congr 1
    simp only [Fin.getElem_fin, Fin.coe_cast, List.getElem_map]
    rw [List.getD_eq_getElem _ _ k.2,
      vsWV_img (hsq _ (List.getElem_mem k.2)).2 (fun r hr => ((hsq _ (List.getElem_mem k.2)).1 r hr).2.le),
      vsWLin, Matrix.toLin'_apply]

end

end GI.Proved
