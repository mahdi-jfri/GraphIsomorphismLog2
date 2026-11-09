module

public import Workspace.Degree.GraphStep
public import Workspace.Degree.Class
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Perm.Closure
public import Mathlib.Data.Fintype.Option

/-!
# The group of the slots

Lemma 9.1 of the paper.

* `gammaHat_pi`: a finite power of a group of `Γ̂_d` lies in `Γ̂_d`.
* `gammaHat_slotGroup`: if `A ∈ Γ̂_D` then `W(A) ∈ Γ̂_D`.
* `slotLift`, `slotSwaps`, `closure_slotGens`: generators of `W(A)`.
-/

@[expose] public section

namespace GI.Degree

open Equiv

/-- A finite power of a group of `Γ̂_d` lies in `Γ̂_d`. -/
theorem gammaHat_pi {d : ℕ} {G : Type} [Group G] (hG : GammaHat d G) (ι : Type) [Finite ι] :
    GammaHat d (ι → G) := by
  induction ι using Finite.induction_empty_option with
  | @of_equiv α β e h =>
    let φ : (β → G) →* (α → G) :=
      { toFun := fun f a => f (e a)
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine h.of_injective φ fun f g hfg => ?_
    funext b
    have := congrFun hfg (e.symm b)
    simpa [φ] using this
  | h_empty =>
    exact (hG.subgroup ⊥).of_injective
      ((1 : (PEmpty → G) →* (⊥ : Subgroup G))) fun f g _ => funext fun a => nomatch a
  | @h_option α _ h =>
    let φ : (Option α → G) →* G :=
      { toFun := fun f => f none
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hφ : Function.Surjective φ := fun g => ⟨fun _ => g, rfl⟩
    refine GammaHat.of_normal φ.ker ?_ ?_
    · let ψ : φ.ker →* (α → G) :=
        { toFun := fun f a => (f : Option α → G) (some a)
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      refine h.of_injective ψ fun f g hfg => Subtype.ext (funext fun o => ?_)
      cases o with
      | none =>
        have h1 : (f : Option α → G) none = 1 := f.2
        have h2 : (g : Option α → G) none = 1 := g.2
        rw [h1, h2]
      | some a => exact congrFun hfg a
    · exact hG.of_injective (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toMonoidHom
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ).injective

variable {V : Type} {D : ℕ}

/-- The homomorphism `π` from `W(A)` to `A`, read through the slot number `z`. -/
theorem slotGroup_unique {A : Subgroup (Perm V)} {f : Perm (V × Fin D)} (z : Fin D) {a b : Perm V}
    (ha : ∀ s, (f s).1 = a s.1) (hb : ∀ s, (f s).1 = b s.1) : a = b :=
  Equiv.ext fun u => (ha (u, z)).symm.trans (hb (u, z))

/-- The lift of `a`. -/
def slotLift (D : ℕ) : Perm V →* Perm (V × Fin D) where
  toFun a := a.prodCongr (Equiv.refl _)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem slotLift_apply (a : Perm V) (s : V × Fin D) : slotLift D a s = (a s.1, s.2) := rfl

theorem slotLift_mem {A : Subgroup (Perm V)} {a : Perm V} (ha : a ∈ A) :
    slotLift D a ∈ slotGroup D A := ⟨a, ha, fun _ => rfl⟩

/-- The action of `f ∈ W(A)` on the vertices. -/
noncomputable def slotPi (A : Subgroup (Perm V)) (f : slotGroup D A) : A :=
  ⟨f.2.choose, f.2.choose_spec.1⟩

theorem slotPi_spec (A : Subgroup (Perm V)) (f : slotGroup D A) (s : V × Fin D) :
    ((f : Perm (V × Fin D)) s).1 = (slotPi A f : Perm V) s.1 :=
  f.2.choose_spec.2 s

/-- `π` as a homomorphism. -/
noncomputable def slotHom (z : Fin D) (A : Subgroup (Perm V)) : slotGroup D A →* A :=
  MonoidHom.mk' (slotPi A) fun f g => by
    refine Subtype.ext (slotGroup_unique (A := A) z (f := ((f * g : slotGroup D A) : Perm _))
      (slotPi_spec A (f * g)) fun s => ?_)
    have h1 := slotPi_spec A g s
    have h2 := slotPi_spec A f ((g : Perm (V × Fin D)) s)
    rw [h1] at h2
    exact h2

theorem slotHom_surjective (z : Fin D) (A : Subgroup (Perm V)) :
    Function.Surjective (slotHom z A) := by
  intro a
  refine ⟨⟨slotLift D (a : Perm V), slotLift_mem a.2⟩, Subtype.ext ?_⟩
  exact (slotGroup_unique (A := A) z (f := slotLift D (a : Perm V))
    (fun s => rfl) (slotPi_spec A ⟨slotLift D (a : Perm V), slotLift_mem a.2⟩)).symm

/-- A slot permutation over the identity is a family of permutations of `Fin D`. -/
theorem slot_kernel_fst (z : Fin D) (A : Subgroup (Perm V)) {f : slotGroup D A}
    (hf : f ∈ (slotHom z A).ker) (s : V × Fin D) : ((f : Perm (V × Fin D)) s).1 = s.1 := by
  have h1 : slotPi A f = 1 := hf
  have h2 := slotPi_spec A f s
  rw [h1] at h2
  exact h2

/-- The family of a permutation that keeps each fiber. -/
def fiberPerm (f : Perm (V × Fin D)) (hf : ∀ s, (f s).1 = s.1) (u : V) : Perm (Fin D) where
  toFun i := (f (u, i)).2
  invFun i := (f⁻¹ (u, i)).2
  left_inv i := by
    have h1 : (f (u, i)).1 = u := hf _
    have h3 : (u, (f (u, i)).2) = f (u, i) := Prod.ext h1.symm rfl
    show (f⁻¹ (u, (f (u, i)).2)).2 = i
    rw [h3]
    simp
  right_inv i := by
    have hi : (f (f⁻¹ (u, i))) = (u, i) := f.apply_symm_apply _
    have h1 : (f⁻¹ (u, i)).1 = u := by
      have := hf (f⁻¹ (u, i))
      rw [hi] at this
      exact this.symm
    have h3 : (u, (f⁻¹ (u, i)).2) = f⁻¹ (u, i) := Prod.ext h1.symm rfl
    show (f (u, (f⁻¹ (u, i)).2)).2 = i
    rw [h3, hi]

theorem fiberPerm_apply {f : Perm (V × Fin D)} (hf : ∀ s, (f s).1 = s.1) (u : V) (i : Fin D) :
    f (u, i) = (u, fiberPerm f hf u i) :=
  Prod.ext (hf _) rfl

/-- **`W(A)` lies in `Γ̂_D`.** -/
theorem gammaHat_slotGroup [Finite V] (z : Fin D) {A : Subgroup (Perm V)} (hA : GammaHat D A) :
    GammaHat D (slotGroup D A) := by
  refine GammaHat.of_normal (slotHom z A).ker ?_ ?_
  · let ψ : (slotHom z A).ker →* (V → Perm (Fin D)) :=
      { toFun := fun f => fiberPerm (f : slotGroup D A) (slot_kernel_fst z A f.2)
        map_one' := by
          funext u
          exact Equiv.ext fun i => rfl
        map_mul' := fun f g => by
          funext u
          refine Equiv.ext fun i => ?_
          have h1 := fiberPerm_apply (slot_kernel_fst z A g.2) u i
          show (((f : slotGroup D A) : Perm (V × Fin D))
            (((g : slotGroup D A) : Perm (V × Fin D)) (u, i))).2 =
            (((f : slotGroup D A) : Perm (V × Fin D))
              (u, fiberPerm _ (slot_kernel_fst z A g.2) u i)).2
          rw [h1] }
    refine (gammaHat_pi (gammaHat_perm D) V).of_injective ψ fun f g hfg => ?_
    refine Subtype.ext (Subtype.ext (Equiv.ext fun s => ?_))
    obtain ⟨u, i⟩ := s
    rw [fiberPerm_apply (slot_kernel_fst z A f.2), fiberPerm_apply (slot_kernel_fst z A g.2)]
    have := congrFun hfg u
    exact congrArg (fun σ : Perm (Fin D) => (u, σ i)) this
  · exact hA.of_injective
      (QuotientGroup.quotientKerEquivOfSurjective _ (slotHom_surjective z A)).toMonoidHom
      (QuotientGroup.quotientKerEquivOfSurjective _ (slotHom_surjective z A)).injective

section Gens

variable [DecidableEq V]

/-- The permutation of the slots of the vertex `u` given by `σ`. -/
def fiberHom (u : V) : Perm (Fin D) →* Perm (V × Fin D) where
  toFun σ :=
    { toFun := fun s => if s.1 = u then (s.1, σ s.2) else s
      invFun := fun s => if s.1 = u then (s.1, σ⁻¹ s.2) else s
      left_inv := fun s => by obtain ⟨v, l⟩ := s; by_cases h : v = u <;> simp [h]
      right_inv := fun s => by obtain ⟨v, l⟩ := s; by_cases h : v = u <;> simp [h] }
  map_one' := by ext s <;> simp
  map_mul' σ τ := by
    ext s
    · by_cases h : s.1 = u <;> simp [h, Perm.mul_apply]
    · by_cases h : s.1 = u <;> simp [h, Perm.mul_apply]

theorem fiberHom_swap (u : V) (i j : Fin D) :
    fiberHom u (swap i j) = swap (u, i) (u, j) := by
  ext ⟨v, l⟩ : 1
  by_cases h : v = u
  · subst h
    simp only [fiberHom, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, if_true]
    by_cases h1 : l = i
    · simp [h1]
    · by_cases h2 : l = j
      · simp [h2]
      · rw [swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne (by simp [h1]) (by simp [h2])]
  · have h1 : (v, l) ≠ (u, i) := fun e => h (congrArg Prod.fst e)
    have h2 : (v, l) ≠ (u, j) := fun e => h (congrArg Prod.fst e)
    simp only [fiberHom, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, h, if_false]
    rw [swap_apply_of_ne_of_ne h1 h2]

/-- The transpositions of the slots of a fiber with the slot number `z`. -/
def slotSwaps (z : Fin D) : Set (Perm (V × Fin D)) := {g | ∃ s : V × Fin D, g = swap (s.1, z) s}

/-- All permutations of one fiber lie in the group of the transpositions. -/
theorem fiberHom_mem (z : Fin D) (u : V) (σ : Perm (Fin D)) :
    fiberHom u σ ∈ Subgroup.closure (slotSwaps (V := V) z) := by
  have hstar : ∀ i, fiberHom u (swap z i) ∈ Subgroup.closure (slotSwaps (V := V) z) := fun i => by
    rw [fiberHom_swap]
    exact Subgroup.subset_closure ⟨(u, i), rfl⟩
  have hsw : ∀ τ : Perm (Fin D), τ.IsSwap →
      fiberHom u τ ∈ Subgroup.closure (slotSwaps (V := V) z) := by
    rintro τ ⟨i, j, hij, rfl⟩
    by_cases hi : i = z
    · subst hi
      exact hstar j
    by_cases hj : j = z
    · subst hj
      rw [swap_comm]
      exact hstar i
    have e : swap i j = swap z i * swap z j * swap z i := by
      have := swap_mul_swap_mul_swap (x := j) (y := z) (z := i) hj hij.symm
      rw [swap_comm j z] at this
      exact this.symm
    rw [e, map_mul, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hstar i) (hstar j)) (hstar i)
  have htop : Subgroup.closure {σ : Perm (Fin D) | σ.IsSwap} = ⊤ := Perm.closure_isSwap
  have hσ : σ ∈ Subgroup.closure {σ : Perm (Fin D) | σ.IsSwap} := htop ▸ Subgroup.mem_top σ
  induction hσ using Subgroup.closure_induction with
  | mem x hx => exact hsw x hx
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

/-- All permutations that keep each fiber lie in the group of the transpositions. -/
theorem fiberwise_mem [Fintype V] (z : Fin D) (f : Perm (V × Fin D)) (hf : ∀ s, (f s).1 = s.1) :
    f ∈ Subgroup.closure (slotSwaps (V := V) z) := by
  suffices h : ∀ (S : Finset V) (f : Perm (V × Fin D)), (∀ s, (f s).1 = s.1) →
      (∀ s, s.1 ∉ S → f s = s) → f ∈ Subgroup.closure (slotSwaps (V := V) z) from
    h Finset.univ f hf (fun s hs => absurd (Finset.mem_univ _) hs)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro f _ h
    have : f = 1 := Equiv.ext fun s => h s (by simp)
    rw [this]
    exact Subgroup.one_mem _
  | insert u S hu ih =>
    intro f hf h
    set σ := fiberPerm f hf u with hσ
    have e : f = fiberHom u σ * (fiberHom u σ)⁻¹ * f := by simp
    rw [e, mul_assoc]
    refine Subgroup.mul_mem _ (fiberHom_mem z u σ) (ih _ ?_ ?_)
    · intro s
      have h1 : ∀ t : V × Fin D, ((fiberHom u σ)⁻¹ t).1 = t.1 := fun t => by
        have h2 : ∀ t : V × Fin D, (fiberHom u σ t).1 = t.1 := fun t => by
          by_cases c : t.1 = u <;> simp [fiberHom, c]
        have := h2 ((fiberHom u σ)⁻¹ t)
        simpa using this.symm
      rw [Perm.mul_apply, h1, hf]
    · rintro ⟨v, l⟩ hv
      by_cases c : v = u
      · subst c
        rw [Perm.mul_apply, Perm.inv_eq_iff_eq]
        have : fiberHom v σ (v, l) = (v, σ l) := by simp [fiberHom]
        rw [this]
        exact fiberPerm_apply hf v l
      · have hv' : v ∉ insert u S := by simp [c]; exact hv
        have h3 := h (v, l) hv'
        rw [Perm.mul_apply, h3, Perm.inv_eq_iff_eq]
        simp [fiberHom, c]

/-- **The generators of `W(A)`.** -/
theorem closure_slotGens [Fintype V] (z : Fin D) (S : Set (Perm V)) :
    Subgroup.closure (slotLift D '' S ∪ slotSwaps z) = slotGroup D (Subgroup.closure S) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g (⟨a, ha, rfl⟩ | ⟨s, rfl⟩)
    · exact slotLift_mem (Subgroup.subset_closure ha)
    · refine ⟨1, Subgroup.one_mem _, fun t => ?_⟩
      by_cases h1 : t = (s.1, z)
      · simp [h1]
      by_cases h2 : t = s
      · simp [h2]
      rw [swap_apply_of_ne_of_ne h1 h2]
      rfl
  · rintro f ⟨a, ha, hfa⟩
    set W₀ := Subgroup.closure (slotLift D '' S ∪ slotSwaps z) with hW
    have key : ∀ a ∈ Subgroup.closure S, slotLift D a ∈ W₀ := fun a ha => by
      induction ha using Subgroup.closure_induction with
      | mem x hx => exact Subgroup.subset_closure (Or.inl ⟨x, hx, rfl⟩)
      | one => simp
      | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
      | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx
    have hle : Subgroup.closure (slotSwaps (V := V) z) ≤ W₀ :=
      Subgroup.closure_mono Set.subset_union_right
    have hk : ((slotLift D a)⁻¹ * f) ∈ Subgroup.closure (slotSwaps (V := V) z) := by
      refine fiberwise_mem z _ fun s => ?_
      have h2 : ∀ t : V × Fin D, ((slotLift D a)⁻¹ t).1 = a⁻¹ t.1 := fun t => by
        rw [← map_inv]
        rfl
      rw [Perm.mul_apply, h2, hfa]
      simp
    have e : f = slotLift D a * ((slotLift D a)⁻¹ * f) := by simp
    rw [e]
    exact Subgroup.mul_mem _ (key a ha) (hle hk)

end Gens

end GI.Degree
