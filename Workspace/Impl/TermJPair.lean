import Workspace.Impl.TermJ

/-!
# Pairs as permutations of `B × [q]` (the algebra behind `TermJSpec`)

A pair `(d, π)`, with `d : [q] → Sym(B)` and `π ∈ Sym(q)`, acts on `B × [q]` by
`(c, i) ↦ (d_i⁻¹ c, π i)` (`tmJP`, the same map as `tmJPerm` of `TermJ.lean`). This file
collects its algebra:

* `tmJP_mul`: `(d, π)(d', π') = (i ↦ d'_i d_{π' i}, π π')`, so the pairs with coordinates in a
  subgroup `K` form a subgroup `tmJW K` (the wreath product `K ≀ Sym(q)` in this action);
* `tmJP_inv`, `tmJP_injective`;
* `tmJD H N`: the pairs whose coordinates all lie in one coset `hN` with `h ∈ H`. It normalizes
  `tmJW N` when `N` is normalized by `H` (`tmJD_normalizes_W`). Every group used by the
  `J`-step lies in `tmJD H N`;
* `tmJ_mem_iso`: the pair carries the row tuple `x` to `y` (`x_i^{d_i} = y_{π i}`) exactly when
  `Y ∘ σ = X` for the strings `X (c, i) = x_i c`, `Y (c, i) = y_i c` on `B × [q]`.
-/

namespace GI.Impl

open Equiv Equiv.Perm

variable {B : Type} {q : ℕ}

/-- **A pair as a permutation of `B × [q]`**: `(c, i) ↦ (d_i⁻¹ c, π i)`. -/
def tmJP (p : (Fin q → Perm B) × Perm (Fin q)) : Perm (B × Fin q) where
  toFun a := ((p.1 a.2)⁻¹ a.1, p.2 a.2)
  invFun b := (p.1 (p.2.symm b.2) b.1, p.2.symm b.2)
  left_inv a := by
    obtain ⟨c, i⟩ := a
    simp only [Equiv.symm_apply_apply, Prod.mk.injEq, and_true]
    exact (p.1 i).apply_symm_apply c
  right_inv b := by
    obtain ⟨c, i⟩ := b
    simp only [Equiv.apply_symm_apply, Prod.mk.injEq, and_true]
    exact (p.1 (p.2.symm i)).symm_apply_apply c

@[simp] theorem tmJP_apply (p : (Fin q → Perm B) × Perm (Fin q)) (a : B × Fin q) :
    tmJP p a = ((p.1 a.2)⁻¹ a.1, p.2 a.2) := rfl

theorem tmJPerm_eq_tmJP {m : ℕ} (p : (Fin q → Perm (Fin m)) × Perm (Fin q)) :
    tmJPerm p = tmJP p := rfl

theorem tmJSet_eq_image {m : ℕ} (T : Set ((Fin q → Perm (Fin m)) × Perm (Fin q))) :
    tmJSet T = tmJP '' T := rfl

/-- The product of two pairs. -/
theorem tmJP_mul (p p' : (Fin q → Perm B) × Perm (Fin q)) :
    tmJP p * tmJP p' = tmJP (fun i => p'.1 i * p.1 (p'.2 i), p.2 * p'.2) := by
  ext ⟨c, i⟩ <;> simp [mul_inv_rev]

theorem tmJP_one : tmJP ((1 : Fin q → Perm B), (1 : Perm (Fin q))) = 1 := by
  ext ⟨c, i⟩ <;> simp

/-- The inverse of a pair. -/
theorem tmJP_inv (p : (Fin q → Perm B) × Perm (Fin q)) :
    (tmJP p)⁻¹ = tmJP (fun i => (p.1 (p.2⁻¹ i))⁻¹, p.2⁻¹) := by
  rw [inv_eq_iff_mul_eq_one, tmJP_mul, ← tmJP_one]
  congr 1
  ext1
  · funext i
    simp only [Pi.one_apply]
    group
  · simp

/-- **A pair is determined by its permutation** (when `B` is nonempty). -/
theorem tmJP_injective [Nonempty B] : Function.Injective (tmJP (B := B) (q := q)) := by
  intro p p' h
  obtain ⟨b⟩ := ‹Nonempty B›
  have h2 : p.2 = p'.2 := by
    ext i
    have := congrArg (fun σ : Perm (B × Fin q) => (σ (b, i)).2) h
    simpa using congrArg Fin.val this
  have h1 : p.1 = p'.1 := by
    funext i
    have : (p.1 i)⁻¹ = (p'.1 i)⁻¹ := by
      ext c
      have := congrArg (fun σ : Perm (B × Fin q) => (σ (c, i)).1) h
      simpa using congrArg (fun z => z) this
    simpa using congrArg (·⁻¹) this
  exact Prod.ext h1 h2

/-! ### The wreath products in this action -/

/-- **The pairs with coordinates in `K`**: the wreath product `K ≀ Sym(q)` acting on `B × [q]`. -/
def tmJW (K : Subgroup (Perm B)) : Subgroup (Perm (B × Fin q)) where
  carrier := {σ | ∃ p : (Fin q → Perm B) × Perm (Fin q), (∀ i, p.1 i ∈ K) ∧ tmJP p = σ}
  one_mem' := ⟨(1, 1), fun _ => K.one_mem, tmJP_one⟩
  mul_mem' := by
    rintro _ _ ⟨p, hp, rfl⟩ ⟨p', hp', rfl⟩
    exact ⟨_, fun i => K.mul_mem (hp' i) (hp _), (tmJP_mul p p').symm⟩
  inv_mem' := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨_, fun i => K.inv_mem (hp _), (tmJP_inv p).symm⟩

theorem mem_tmJW {K : Subgroup (Perm B)} {σ : Perm (B × Fin q)} :
    σ ∈ tmJW K ↔ ∃ p : (Fin q → Perm B) × Perm (Fin q), (∀ i, p.1 i ∈ K) ∧ tmJP p = σ :=
  Iff.rfl

/-- **The pairs of one class modulo `N`**: all coordinates in one coset `h N`, `h ∈ H`. -/
def tmJD (H N : Subgroup (Perm B)) (hn : GI.Multicoset.Normalizes H N) :
    Subgroup (Perm (B × Fin q)) where
  carrier := {σ | ∃ h ∈ H, ∃ p : (Fin q → Perm B) × Perm (Fin q), (∀ i, h⁻¹ * p.1 i ∈ N) ∧
    tmJP p = σ}
  one_mem' := ⟨1, H.one_mem, (1, 1), fun _ => by simp, tmJP_one⟩
  mul_mem' := by
    rintro _ _ ⟨h, hh, p, hp, rfl⟩ ⟨h', hh', p', hp', rfl⟩
    refine ⟨h' * h, H.mul_mem hh' hh, _, fun i => ?_, (tmJP_mul p p').symm⟩
    -- `(h' h)⁻¹ d'_i d_j = h⁻¹ (h'⁻¹ d'_i) h · h⁻¹ d_j`
    have e : (h' * h)⁻¹ * (p'.1 i * p.1 (p'.2 i)) =
        (h⁻¹ * (h'⁻¹ * p'.1 i) * h⁻¹⁻¹) * (h⁻¹ * p.1 (p'.2 i)) := by group
    rw [e]
    exact N.mul_mem (hn _ (H.inv_mem hh) _ (hp' i)) (hp _)
  inv_mem' := by
    rintro _ ⟨h, hh, p, hp, rfl⟩
    refine ⟨h⁻¹, H.inv_mem hh, _, fun i => ?_, (tmJP_inv p).symm⟩
    -- `h (d_j)⁻¹ = h (h⁻¹ d_j)⁻¹ h⁻¹`
    have e : h⁻¹⁻¹ * (p.1 (p.2⁻¹ i))⁻¹ = h * (h⁻¹ * p.1 (p.2⁻¹ i))⁻¹ * h⁻¹ := by group
    rw [e]
    exact hn _ hh _ (N.inv_mem (hp _))

theorem mem_tmJD {H N : Subgroup (Perm B)} {hn : GI.Multicoset.Normalizes H N}
    {σ : Perm (B × Fin q)} :
    σ ∈ tmJD (q := q) H N hn ↔ ∃ h ∈ H, ∃ p : (Fin q → Perm B) × Perm (Fin q),
      (∀ i, h⁻¹ * p.1 i ∈ N) ∧ tmJP p = σ :=
  Iff.rfl

theorem tmJW_le_tmJD {H N : Subgroup (Perm B)} (hn : GI.Multicoset.Normalizes H N) :
    tmJW (q := q) N ≤ tmJD H N hn := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨1, H.one_mem, p, fun i => by simp [hp i], rfl⟩

/-- **`N ≀ Sym(q)` is normalized by the pairs of one class.** The conjugate of `(ν, ρ)` by `(d, π)`
has coordinates `d_a⁻¹ ν_a' d_b` with `d_a, d_b ∈ h N`. -/
theorem tmJD_normalizes_W {H N : Subgroup (Perm B)}
    (hn : GI.Multicoset.Normalizes H N) {g : Perm (B × Fin q)} (hg : g ∈ tmJD H N hn)
    {w : Perm (B × Fin q)} (hw : w ∈ tmJW N) : g * w * g⁻¹ ∈ tmJW N := by
  obtain ⟨h, hh, p, hp, rfl⟩ := hg
  obtain ⟨p', hp', rfl⟩ := hw
  rw [tmJP_inv, tmJP_mul, tmJP_mul]
  refine ⟨_, fun i => ?_, rfl⟩
  simp only
  -- `d_a⁻¹ ν d_b = (h⁻¹ d_a)⁻¹ (h⁻¹ ν h) (h⁻¹ d_b)`
  set a := p.1 (p.2⁻¹ i)
  set b := p.1 (p'.2 (p.2⁻¹ i))
  set ν := p'.1 (p.2⁻¹ i)
  have e : a⁻¹ * (ν * b) = (h⁻¹ * a)⁻¹ * (h⁻¹ * ν * h⁻¹⁻¹) * (h⁻¹ * b) := by group
  rw [e]
  exact N.mul_mem (N.mul_mem (N.inv_mem (hp _)) (hn _ (H.inv_mem hh) _ (hp' _))) (hp _)


/-! ### The class of a pair modulo `N` -/

/-- **The pairs of class `h` modulo `N`**: every coordinate lies in `h N`. -/
def tmJCls (N : Subgroup (Perm B)) (h : Perm B) : Set (Perm (B × Fin q)) :=
  {σ | ∃ p : (Fin q → Perm B) × Perm (Fin q), tmJP p = σ ∧ ∀ i, h⁻¹ * p.1 i ∈ N}

theorem tmJCls_one_iff {N : Subgroup (Perm B)} {σ : Perm (B × Fin q)} :
    σ ∈ tmJCls N 1 ↔ σ ∈ tmJW N := by
  constructor
  · rintro ⟨p, rfl, hp⟩; exact ⟨p, fun i => by simpa using hp i, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, rfl, fun i => by simpa using hp i⟩

theorem tmJCls_mem_D {H N : Subgroup (Perm B)} {hn : GI.Multicoset.Normalizes H N} {h : Perm B}
    (hh : h ∈ H) {σ : Perm (B × Fin q)} (hσ : σ ∈ tmJCls N h) : σ ∈ tmJD H N hn := by
  obtain ⟨p, rfl, hp⟩ := hσ
  exact ⟨h, hh, p, hp, rfl⟩

/-- **Classes multiply in reverse order**: `σ ∈ h N`, `σ' ∈ h' N` give `σ σ' ∈ h' h N`. -/
theorem tmJCls_mul {H N : Subgroup (Perm B)} (hn : GI.Multicoset.Normalizes H N) {h h' : Perm B}
    (hh : h ∈ H) {σ σ' : Perm (B × Fin q)} (hσ : σ ∈ tmJCls N h) (hσ' : σ' ∈ tmJCls N h') :
    σ * σ' ∈ tmJCls N (h' * h) := by
  obtain ⟨p, rfl, hp⟩ := hσ
  obtain ⟨p', rfl, hp'⟩ := hσ'
  refine ⟨_, (tmJP_mul p p').symm, fun i => ?_⟩
  have e : (h' * h)⁻¹ * (p'.1 i * p.1 (p'.2 i)) =
      (h⁻¹ * (h'⁻¹ * p'.1 i) * h⁻¹⁻¹) * (h⁻¹ * p.1 (p'.2 i)) := by group
  rw [e]
  exact N.mul_mem (hn _ (H.inv_mem hh) _ (hp' i)) (hp _)

theorem tmJCls_inv {H N : Subgroup (Perm B)} (hn : GI.Multicoset.Normalizes H N) {h : Perm B}
    (hh : h ∈ H) {σ : Perm (B × Fin q)} (hσ : σ ∈ tmJCls N h) : σ⁻¹ ∈ tmJCls N h⁻¹ := by
  obtain ⟨p, rfl, hp⟩ := hσ
  refine ⟨_, (tmJP_inv p).symm, fun i => ?_⟩
  have e : h⁻¹⁻¹ * (p.1 (p.2⁻¹ i))⁻¹ = h * (h⁻¹ * p.1 (p.2⁻¹ i))⁻¹ * h⁻¹ := by group
  rw [e]
  exact hn _ hh _ (N.inv_mem (hp _))

/-- A pair of class `h` is of class `h n` for `n ∈ N`. -/
theorem tmJCls_mul_right {N : Subgroup (Perm B)} {h n : Perm B} (hnN : n ∈ N)
    {σ : Perm (B × Fin q)} (hσ : σ ∈ tmJCls N h) : σ ∈ tmJCls N (h * n) := by
  obtain ⟨p, rfl, hp⟩ := hσ
  refine ⟨p, rfl, fun i => ?_⟩
  have e : (h * n)⁻¹ * p.1 i = n⁻¹ * (h⁻¹ * p.1 i) := by group
  rw [e]; exact N.mul_mem (N.inv_mem hnN) (hp i)

/-- **Two classes of one pair agree modulo `N`** (when `B` and `[q]` are nonempty). -/
theorem tmJCls_unique [Nonempty B] {N : Subgroup (Perm B)} (i0 : Fin q) {h h' : Perm B}
    {σ : Perm (B × Fin q)} (hσ : σ ∈ tmJCls N h) (hσ' : σ ∈ tmJCls N h') : h⁻¹ * h' ∈ N := by
  obtain ⟨p, rfl, hp⟩ := hσ
  obtain ⟨p', he, hp'⟩ := hσ'
  rw [tmJP_injective he] at hp'
  have e : h⁻¹ * h' = (h⁻¹ * p.1 i0) * (h'⁻¹ * p.1 i0)⁻¹ := by group
  rw [e]; exact N.mul_mem (hp i0) (N.inv_mem (hp' i0))

/-- The constant pair `(h, …, h; 1)` is of class `h`. -/
theorem tmJ_const_mem (N : Subgroup (Perm B)) (h : Perm B) :
    tmJP ((fun _ => h : Fin q → Perm B), (1 : Perm (Fin q))) ∈ tmJCls N h :=
  ⟨_, rfl, fun _ => by simp⟩

/-! ### Strings on `B × [q]` -/

/-- The string on `B × [q]` of a row tuple: `X (c, i) = x_i c`. -/
def tmJStr {C : Type} (x : Fin q → B → C) : B × Fin q → C := fun a => x a.2 a.1

/-- **The pair carries `x` to `y` exactly when `Y ∘ σ = X`.** -/
theorem tmJ_mem_iso {C : Type} (x y : Fin q → B → C) (p : (Fin q → Perm B) × Perm (Fin q)) :
    tmJStr y ∘ tmJP p = tmJStr x ↔ ∀ i, x i ∘ p.1 i = y (p.2 i) := by
  constructor
  · intro h i
    funext c
    have := congrFun h (p.1 i c, i)
    simpa [tmJStr] using this.symm
  · intro h
    funext ⟨c, i⟩
    have := congrFun (h i) ((p.1 i)⁻¹ c)
    simp only [Function.comp_apply, Perm.apply_inv_self] at this
    simp [tmJStr, this]

end GI.Impl
