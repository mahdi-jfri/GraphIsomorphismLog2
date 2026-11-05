module

public import Workspace.Impl.TermJPair

@[expose] public section

/-!
# The `J`-correction and the output coset (group theory of `TermJSpec`)

This is the mathematics of the last paragraph of the proof of Theorem A.23: "Finally lift the
surviving quotient representative and correct it by the constructed `J`-transporter. … For
automorphism generators, lift each generator of the surviving quotient stabilizer and make the
same correction; adjoin `Aut_J(x)`. These generators map onto the exact quotient stabilizer and
contain its full kernel, so the output is the complete isomorphism coset."

The setting is abstract: a group `G' ≤ Sym(B × [q])` all of whose elements are pairs of one class
modulo `N` (`hG`), and the piece `T'` of one radical coset (`hT`). In the application `G'` is
the domain group (`tmJG`), `T'` is `tmJP '' tmCosetT I r` (`tmJ_mem_T`).

* `tmJ_correct_pre`, `tmJ_correct`: **the correction.** Let `h` be a label element, `g ∈ G'` of
  class `h` (a lift of `h`), and `z` a pair of class `h` carrying `X` to `Y` (built from the
  local transporters). If some element of `G'` of class `h` carries `X` to `Y`, then
  `z⁻¹ g ∈ Aut_{N≀Sym}(X) · J` (the precondition of the factorization), and for every
  factorization `z⁻¹ g = a j` the element `z a` lies in `G'`, carries `X` to `Y`, and has class
  `h`. Here `J = G' ∩ N ≀ Sym(q)`.
* `tmJ_coset_eq`: **the output coset.** If `t₀` is a corrected lift of the label representative
  `h₀`, `t_u` a corrected lift of `h₀ u` for each generator `u` of the label group, and `ks`
  generates `Aut_J(X)`, then `T' = t₀ ⟨t₀⁻¹ t_u, ks⟩`.
-/

namespace GI.Impl

open Equiv Equiv.Perm

variable {B : Type} {q : ℕ}

/-- The stabilizer of a string on `B × [q]`. -/
def tmJStab {C : Type} (X : B × Fin q → C) : Subgroup (Perm (B × Fin q)) where
  carrier := {σ | X ∘ σ = X}
  one_mem' := rfl
  mul_mem' := by
    rintro σ τ (hσ : X ∘ σ = X) (hτ : X ∘ τ = X)
    change X ∘ (σ ∘ τ) = X
    rw [← Function.comp_assoc, hσ, hτ]
  inv_mem' := by
    rintro σ (hσ : X ∘ σ = X)
    change X ∘ ⇑(σ⁻¹) = X
    conv_lhs => rw [← hσ]
    funext a
    simp

theorem mem_tmJStab {C : Type} {X : B × Fin q → C} {σ : Perm (B × Fin q)} :
    σ ∈ tmJStab X ↔ X ∘ σ = X := Iff.rfl

theorem tmJ_iso_inv {C : Type} {X Y : B × Fin q → C} {z : Perm (B × Fin q)} (hz : Y ∘ z = X) :
    X ∘ ⇑(z⁻¹) = Y := by
  rw [← hz]; funext a; simp

theorem tmJ_iso_mul_stab {C : Type} {X Y : B × Fin q → C} {z a : Perm (B × Fin q)}
    (hz : Y ∘ z = X) (ha : X ∘ a = X) : Y ∘ (z * a) = X := by
  change Y ∘ (z ∘ a) = X
  rw [← Function.comp_assoc, hz, ha]

theorem tmJ_iso_inv_mul {C : Type} {X Y : B × Fin q → C} {z t : Perm (B × Fin q)}
    (hz : Y ∘ z = X) (ht : Y ∘ t = X) : X ∘ (z⁻¹ * t) = X := by
  change X ∘ (⇑(z⁻¹) ∘ t) = X
  rw [← Function.comp_assoc, tmJ_iso_inv hz, ht]

section Correct

variable {H N : Subgroup (Perm B)} (hn : GI.Multicoset.Normalizes H N) {C : Type}
  {X Y : B × Fin q → C} (G' : Subgroup (Perm (B × Fin q)))

include hn

/-- **The precondition of the correcting factorization.** -/
theorem tmJ_correct_pre {h : Perm B} (hh : h ∈ H) {z g t : Perm (B × Fin q)}
    (hz : Y ∘ z = X) (hzc : z ∈ tmJCls N h) (hg : g ∈ G') (hgc : g ∈ tmJCls N h)
    (ht : t ∈ G') (htY : Y ∘ t = X) (htc : t ∈ tmJCls N h) :
    ∃ a ∈ tmJW N ⊓ tmJStab X, ∃ j ∈ G' ⊓ tmJW N, z⁻¹ * g = a * j := by
  refine ⟨z⁻¹ * t, ⟨?_, tmJ_iso_inv_mul hz htY⟩, t⁻¹ * g, ⟨G'.mul_mem (G'.inv_mem ht) hg, ?_⟩,
    by group⟩
  · have := tmJCls_mul hn (H.inv_mem hh) (tmJCls_inv hn hh hzc) htc
    rw [mul_inv_cancel] at this
    exact tmJCls_one_iff.1 this
  · have := tmJCls_mul hn (H.inv_mem hh) (tmJCls_inv hn hh htc) hgc
    rw [mul_inv_cancel] at this
    exact tmJCls_one_iff.1 this

/-- **The correction**: for a factorization `z⁻¹ g = a j`, the element `z a = g j⁻¹`. -/
theorem tmJ_correct {h : Perm B} (hh : h ∈ H) {z g a j : Perm (B × Fin q)}
    (hz : Y ∘ z = X) (hg : g ∈ G') (hgc : g ∈ tmJCls N h)
    (ha : a ∈ tmJW N ⊓ tmJStab X) (hj : j ∈ G' ⊓ tmJW N) (hf : z⁻¹ * g = a * j) :
    z * a ∈ G' ∧ Y ∘ (z * a) = X ∧ z * a ∈ tmJCls N h := by
  have e : z * a = g * j⁻¹ := by
    have : a = z⁻¹ * g * j⁻¹ := by rw [hf]; group
    rw [this]; group
  refine ⟨by rw [e]; exact G'.mul_mem hg (G'.inv_mem hj.1), tmJ_iso_mul_stab hz ha.2, ?_⟩
  rw [e]
  have hj' : j⁻¹ ∈ tmJCls N 1 := tmJCls_one_iff.2 ((tmJW N).inv_mem hj.2)
  have := tmJCls_mul hn hh hgc hj'
  rwa [one_mul] at this

/-- **A lift from a factorization**: if the constant pair `(h; 1)` is `g w` with `w ∈ N ≀ Sym(q)`,
then `g` has class `h`. -/
theorem tmJ_lift_cls {h : Perm B} {g w : Perm (B × Fin q)} (hw : w ∈ tmJW N)
    (hf : tmJP ((fun _ => h : Fin q → Perm B), (1 : Perm (Fin q))) = g * w) (hh : h ∈ H) :
    g ∈ tmJCls N h := by
  have e : g = tmJP ((fun _ => h : Fin q → Perm B), (1 : Perm (Fin q))) * w⁻¹ := by
    rw [hf]; group
  have := tmJCls_mul hn hh (tmJ_const_mem N h) (tmJCls_one_iff.2 ((tmJW N).inv_mem hw))
  rw [one_mul] at this
  rw [e]; exact this

end Correct

section Coset

variable {H N : Subgroup (Perm B)} (hn : GI.Multicoset.Normalizes H N) {C : Type}
  {X Y : B × Fin q → C} (G' : Subgroup (Perm (B × Fin q)))

/-- The automorphisms of `X` in `G'` whose class lies in `R`. -/
def tmJAutR (R : Subgroup (Perm B)) (hRH : R ≤ H) : Subgroup (Perm (B × Fin q)) where
  carrier := {a | a ∈ G' ∧ X ∘ a = X ∧ ∃ x ∈ R, a ∈ tmJCls N x}
  one_mem' := ⟨G'.one_mem, rfl, 1, R.one_mem, (1, 1), tmJP_one, fun _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hXa, x, hx, hac⟩ ⟨hb, hXb, y, hy, hbc⟩
    refine ⟨G'.mul_mem ha hb, (tmJStab X).mul_mem hXa hXb, y * x, R.mul_mem hy hx,
      tmJCls_mul hn (hRH hx) hac hbc⟩
  inv_mem' := by
    rintro a ⟨ha, hXa, x, hx, hac⟩
    exact ⟨G'.inv_mem ha, (tmJStab X).inv_mem hXa, x⁻¹, R.inv_mem hx, tmJCls_inv hn (hRH hx) hac⟩

include hn in
/-- **The output coset** (Theorem A.23: "These generators map onto the exact quotient stabilizer
and contain its full kernel, so the output is the complete isomorphism coset"). -/
theorem tmJ_coset_eq (R : Subgroup (Perm B)) (hRH : R ≤ H) {r : Perm B} (hr : r ∈ H) (T' : Set (Perm (B × Fin q)))
    (hT : ∀ σ, σ ∈ T' ↔ σ ∈ G' ∧ Y ∘ σ = X ∧ ∃ x ∈ R, σ ∈ tmJCls N (x * r))
    (Lab : Set (Perm B)) (h0 : Perm B) (U : List (Perm B))
    (hLab : Lab = (h0 * ·) '' (Subgroup.closure {u | u ∈ U} : Set (Perm B)))
    (hLR : ∀ h ∈ Lab, ∃ x ∈ R, h = x * r)
    (hTL : ∀ t ∈ T', ∃ h ∈ Lab, t ∈ tmJCls N h)
    (t0 : Perm (B × Fin q)) (ht0 : t0 ∈ T') (ht0c : t0 ∈ tmJCls N h0)
    (tu : Perm B → Perm (B × Fin q)) (htu : ∀ u ∈ U, tu u ∈ T' ∧ tu u ∈ tmJCls N (h0 * u))
    (ks : List (Perm (B × Fin q)))
    (hks : Subgroup.closure {k | k ∈ ks} = G' ⊓ tmJW N ⊓ tmJStab X) :
    T' = (t0 * ·) '' (Subgroup.closure ({a | ∃ u ∈ U, a = t0⁻¹ * tu u} ∪ {k | k ∈ ks}) :
      Set (Perm (B × Fin q))) := by
  set A := tmJAutR (X := X) hn G' R hRH
  have hh0L : h0 ∈ Lab := by rw [hLab]; exact ⟨1, Subgroup.one_mem _, mul_one h0⟩
  have hLH : ∀ h ∈ Lab, h ∈ H := by
    intro h hh; obtain ⟨x, hx, rfl⟩ := hLR h hh; exact H.mul_mem (hRH hx) hr
  have hh0 : h0 ∈ H := hLH _ hh0L
  have hUH : ∀ u ∈ U, u ∈ H := by
    intro u hu
    have : h0 * u ∈ Lab := by rw [hLab]; exact ⟨u, Subgroup.subset_closure hu, rfl⟩
    have := H.mul_mem (H.inv_mem hh0) (hLH _ this)
    rwa [inv_mul_cancel_left] at this
  have hclH : Subgroup.closure {u | u ∈ U} ≤ H := (Subgroup.closure_le _).2 hUH
  obtain ⟨hG0, hY0, x0, hx0, hc0⟩ := (hT t0).1 ht0
  -- The generators lie in `A`.
  have hgensA : Subgroup.closure ({a | ∃ u ∈ U, a = t0⁻¹ * tu u} ∪ {k | k ∈ ks}) ≤ A := by
    rw [Subgroup.closure_le]
    rintro a (⟨u, hu, rfl⟩ | hk)
    · obtain ⟨htuT, htuc⟩ := htu u hu
      obtain ⟨hGu, hYu, xu, hxu, hcu⟩ := (hT _).1 htuT
      refine ⟨G'.mul_mem (G'.inv_mem hG0) hGu, tmJ_iso_inv_mul hY0 hYu, xu * x0⁻¹,
        R.mul_mem hxu (R.inv_mem hx0), ?_⟩
      have := tmJCls_mul hn (H.inv_mem (H.mul_mem (hRH hx0) hr)) (tmJCls_inv hn
        (H.mul_mem (hRH hx0) hr) hc0) hcu
      rwa [show xu * r * (x0 * r)⁻¹ = xu * x0⁻¹ by group] at this
    · have : a ∈ G' ⊓ tmJW N ⊓ tmJStab X := by rw [← hks]; exact Subgroup.subset_closure hk
      exact ⟨this.1.1, this.2, 1, R.one_mem, tmJCls_one_iff.2 this.1.2⟩
  ext σ
  constructor
  · intro hσ
    obtain ⟨hGσ, hYσ, -⟩ := (hT σ).1 hσ
    obtain ⟨h, hhL, hσc⟩ := hTL σ hσ
    rw [hLab] at hhL
    obtain ⟨u, hu, rfl⟩ := hhL
    -- an element `b` of the generated group of class `h₀ u h₀⁻¹`
    have key : ∀ v ∈ Subgroup.closure {u | u ∈ U}, ∃ b ∈ Subgroup.closure
        ({a | ∃ u ∈ U, a = t0⁻¹ * tu u} ∪ {k | k ∈ ks}), b ∈ tmJCls N (h0 * v * h0⁻¹) := by
      intro v hv
      induction hv using Subgroup.closure_induction with
      | mem v hv =>
        refine ⟨t0⁻¹ * tu v, Subgroup.subset_closure (Or.inl ⟨v, hv, rfl⟩), ?_⟩
        have := tmJCls_mul hn (H.inv_mem hh0) (tmJCls_inv hn hh0 ht0c) (htu v hv).2
        rwa [show h0 * v * h0⁻¹ = h0 * v * h0⁻¹ from rfl] at this
      | one =>
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        rw [mul_one, mul_inv_cancel]
        exact tmJCls_one_iff.2 (Subgroup.one_mem _)
      | mul v w hv hw ihv ihw =>
        obtain ⟨b, hb, hbc⟩ := ihv
        obtain ⟨b', hb', hbc'⟩ := ihw
        refine ⟨b' * b, Subgroup.mul_mem _ hb' hb, ?_⟩
        have hwH : h0 * w * h0⁻¹ ∈ H := H.mul_mem (H.mul_mem hh0 (hclH hw)) (H.inv_mem hh0)
        have := tmJCls_mul hn hwH hbc' hbc
        rwa [show h0 * v * h0⁻¹ * (h0 * w * h0⁻¹) = h0 * (v * w) * h0⁻¹ by group] at this
      | inv v hv ihv =>
        obtain ⟨b, hb, hbc⟩ := ihv
        refine ⟨b⁻¹, Subgroup.inv_mem _ hb, ?_⟩
        have hvH : h0 * v * h0⁻¹ ∈ H := H.mul_mem (H.mul_mem hh0 (hclH hv)) (H.inv_mem hh0)
        have := tmJCls_inv hn hvH hbc
        rwa [show (h0 * v * h0⁻¹)⁻¹ = h0 * v⁻¹ * h0⁻¹ by group] at this
    obtain ⟨b, hb, hbc⟩ := key u hu
    have hac : t0⁻¹ * σ ∈ tmJCls N (h0 * u * h0⁻¹) := by
      have := tmJCls_mul hn (H.inv_mem hh0) (tmJCls_inv hn hh0 ht0c) hσc
      rwa [show h0 * u * h0⁻¹ = h0 * u * h0⁻¹ from rfl] at this
    have hcH : h0 * u * h0⁻¹ ∈ H := H.mul_mem (H.mul_mem hh0 (hclH hu)) (H.inv_mem hh0)
    have hbA := hgensA hb
    have hker : b⁻¹ * (t0⁻¹ * σ) ∈ G' ⊓ tmJW N ⊓ tmJStab X := by
      refine ⟨⟨G'.mul_mem (G'.inv_mem hbA.1) (G'.mul_mem (G'.inv_mem hG0) hGσ), ?_⟩,
        (tmJStab X).mul_mem ((tmJStab X).inv_mem hbA.2.1) (tmJ_iso_inv_mul hY0 hYσ)⟩
      have := tmJCls_mul hn (H.inv_mem hcH) (tmJCls_inv hn hcH hbc) hac
      rw [mul_inv_cancel] at this
      exact tmJCls_one_iff.1 this
    rw [← hks] at hker
    refine ⟨t0⁻¹ * σ, ?_, by group⟩
    have : t0⁻¹ * σ = b * (b⁻¹ * (t0⁻¹ * σ)) := by group
    rw [this]
    refine Subgroup.mul_mem _ hb ?_
    exact Subgroup.closure_mono Set.subset_union_right hker
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨haG, haX, x, hx, hac⟩ := hgensA ha
    refine (hT _).2 ⟨G'.mul_mem hG0 haG, tmJ_iso_mul_stab hY0 haX, x * x0, R.mul_mem hx hx0, ?_⟩
    have := tmJCls_mul hn (H.mul_mem (hRH hx0) hr) hc0 hac
    rw [mul_assoc]; exact this

end Coset

end GI.Impl
