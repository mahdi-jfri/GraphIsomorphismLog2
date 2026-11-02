import Workspace.Impl.TermJ

/-!
# Pairs as permutations: classes, `N ≀ Sym(q)`, totals and string stabilizers

The label coset of Theorem A.23 (`TermGlueLabSpec`). A pair `(d, π)` of row
coordinates `d : Fin q → Sym(B)` and a row permutation `π` is the permutation
`tmGLP (d, π) : (c, i) ↦ (d_i⁻¹ c, π i)` of `B × Fin q`; for `B = Fin m` it is
`tmJPerm` (`tmGLP_eq`). This file collects its algebra.

* `tmGL_mul`, `tmGL_inv`, `tmGL_one`: products and inverses of pairs. Coordinates multiply as
  `(d, π) (d', π') = (i ↦ d'_i d_{π' i}, π π')`.
* `tmGLCls N h σ`: `σ` is a pair with every coordinate in `h N` ("its coordinate actions differ
  from the common `h` by elements of `N`", proof of Theorem A.23). Classes multiply in reverse
  order (`tmGLCls_mul`), and invert (`tmGLCls_inv`).
* `tmGLGam hn hK`: the pairs with a class in `K` (for `N ≤ K ≤ H`); `tmGLW N = N ≀ Sym(q)`, the
  pairs of class `1`.
* `tmGLStr x`: the string on `B × Fin q` of a row tuple `x`; `tmGLAut Y`: its stabilizer.
  A pair carries `x` to `y` row by row exactly when `Y ∘ σ = X` (`tmGL_str_comp`).
* `tmGLTot`: the total label `∏ φ(d_i)` of a pair of `N`-coordinates; it is multiplicative
  (`tmGLTot_mul`).
-/

namespace GI.Impl

open Equiv GI.Multicoset

variable {B : Type} {q : ℕ}

/-! ### Products of pairs -/

/-- **A pair as a permutation of `B × Fin q`**: `(c, i) ↦ (d_i⁻¹ c, π i)`. -/
def tmGLP (p : (Fin q → Perm B) × Perm (Fin q)) : Perm (B × Fin q) where
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

@[simp] theorem tmGLP_apply (p : (Fin q → Perm B) × Perm (Fin q)) (a : B × Fin q) :
    tmGLP p a = ((p.1 a.2)⁻¹ a.1, p.2 a.2) := rfl

theorem tmGLP_eq {m : ℕ} (p : (Fin q → Perm (Fin m)) × Perm (Fin q)) : tmGLP p = tmJPerm p := rfl

theorem tmGL_mul (d d' : Fin q → Perm B) (π π' : Perm (Fin q)) :
    tmGLP (d, π) * tmGLP (d', π') = tmGLP (fun i => d' i * d (π' i), π * π') := by
  ext ⟨c, i⟩ <;> simp [mul_inv_rev]

theorem tmGL_one : (tmGLP ((1 : Fin q → Perm B), (1 : Perm (Fin q)))) = 1 := by
  ext ⟨c, i⟩ <;> simp

theorem tmGL_inv (d : Fin q → Perm B) (π : Perm (Fin q)) :
    (tmGLP (d, π))⁻¹ = tmGLP (fun i => (d (π⁻¹ i))⁻¹, π⁻¹) := by
  rw [inv_eq_iff_mul_eq_one, tmGL_mul]
  ext ⟨c, i⟩ <;> simp

/-- Pairs are determined by their permutation (rows are nonempty). -/
theorem tmGL_injective [Nonempty B] {p p' : (Fin q → Perm B) × Perm (Fin q)}
    (h : tmGLP p = tmGLP p') : p = p' := by
  obtain ⟨b⟩ := ‹Nonempty B›
  obtain ⟨d, π⟩ := p
  obtain ⟨d', π'⟩ := p'
  have h2 : π = π' := by
    refine Equiv.ext fun i => ?_
    have := congrArg (fun σ : Perm (B × Fin q) => (σ (b, i)).2) h
    simpa using this
  subst h2
  have h1 : d = d' := by
    funext i
    have : (d i)⁻¹ = (d' i)⁻¹ := by
      refine Equiv.ext fun c => ?_
      have := congrArg (fun σ : Perm (B × Fin q) => (σ (c, i)).1) h
      simpa using this
    exact inv_injective this
  rw [h1]

/-! ### Classes -/

/-- `σ` is a pair whose coordinates all lie in `h N`. -/
def tmGLCls (N : Subgroup (Perm B)) (h : Perm B) (σ : Perm (B × Fin q)) : Prop :=
  ∃ d π, σ = tmGLP (d, π) ∧ ∀ i, h⁻¹ * d i ∈ N

variable {N H : Subgroup (Perm B)}

theorem tmGLCls_one : tmGLCls (q := q) N 1 1 :=
  ⟨1, 1, tmGL_one.symm, fun _ => by simp⟩

theorem tmGLCls_mul (hn : Normalizes H N) {h h' : Perm B} (hh : h ∈ H)
    {σ τ : Perm (B × Fin q)} (hσ : tmGLCls N h σ) (hτ : tmGLCls N h' τ) :
    tmGLCls N (h' * h) (σ * τ) := by
  obtain ⟨d, π, rfl, hd⟩ := hσ
  obtain ⟨d', π', rfl, hd'⟩ := hτ
  refine ⟨_, _, tmGL_mul d d' π π', fun i => ?_⟩
  have e : (h' * h)⁻¹ * (d' i * d (π' i)) = (h⁻¹ * (h'⁻¹ * d' i) * h) * (h⁻¹ * d (π' i)) := by
    group
  rw [e]
  exact N.mul_mem (hn.inv hh (hd' i)) (hd (π' i))

theorem tmGLCls_inv (hn : Normalizes H N) {h : Perm B} (hh : h ∈ H)
    {σ : Perm (B × Fin q)} (hσ : tmGLCls N h σ) : tmGLCls N h⁻¹ σ⁻¹ := by
  obtain ⟨d, π, rfl, hd⟩ := hσ
  refine ⟨_, _, tmGL_inv d π, fun i => ?_⟩
  have e : h⁻¹⁻¹ * (d (π⁻¹ i))⁻¹ = h * (h⁻¹ * d (π⁻¹ i))⁻¹ * h⁻¹ := by group
  rw [e]
  exact hn h hh _ (N.inv_mem (hd _))

/-- The class is unique modulo `N`. -/
theorem tmGLCls_unique [Nonempty B] (hq : 0 < q) {h h' : Perm B}
    {σ : Perm (B × Fin q)} (hσ : tmGLCls N h σ) (hσ' : tmGLCls N h' σ) : h⁻¹ * h' ∈ N := by
  obtain ⟨d, π, rfl, hd⟩ := hσ
  obtain ⟨d', π', he, hd'⟩ := hσ'
  have := tmGL_injective he
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  have e : h⁻¹ * h' = (h⁻¹ * d ⟨0, hq⟩) * (h'⁻¹ * d ⟨0, hq⟩)⁻¹ := by group
  rw [e]
  exact N.mul_mem (hd _) (N.inv_mem (hd' _))

/-- A class may be changed within its `N`-coset. -/
theorem tmGLCls_of_mem {h h' : Perm B} (hhh : h⁻¹ * h' ∈ N)
    {σ : Perm (B × Fin q)} (hσ : tmGLCls N h σ) : tmGLCls N h' σ := by
  obtain ⟨d, π, rfl, hd⟩ := hσ
  refine ⟨d, π, rfl, fun i => ?_⟩
  have e : h'⁻¹ * d i = (h⁻¹ * h')⁻¹ * (h⁻¹ * d i) := by group
  rw [e]
  exact N.mul_mem (N.inv_mem hhh) (hd i)

/-- **The pairs with a class in `K`**, for `N ≤ K ≤ H` with `H` normalizing `N`. -/
def tmGLGam (hn : Normalizes H N) {K : Subgroup (Perm B)} (hK : K ≤ H) :
    Subgroup (Perm (B × Fin q)) where
  carrier := {σ | ∃ h ∈ K, tmGLCls N h σ}
  one_mem' := ⟨1, K.one_mem, tmGLCls_one⟩
  mul_mem' := by
    rintro σ τ ⟨h, hh, hσ⟩ ⟨h', hh', hτ⟩
    exact ⟨h' * h, K.mul_mem hh' hh, tmGLCls_mul hn (hK hh) hσ hτ⟩
  inv_mem' := by
    rintro σ ⟨h, hh, hσ⟩
    exact ⟨h⁻¹, K.inv_mem hh, tmGLCls_inv hn (hK hh) hσ⟩

theorem mem_tmGLGam (hn : Normalizes H N) {K : Subgroup (Perm B)} (hK : K ≤ H)
    {σ : Perm (B × Fin q)} : σ ∈ tmGLGam hn hK ↔ ∃ h ∈ K, tmGLCls N h σ := Iff.rfl

theorem tmGLGam_mono (hn : Normalizes H N) {K K' : Subgroup (Perm B)} (hK : K ≤ H)
    (hK' : K' ≤ H) (hKK : K ≤ K') : tmGLGam (q := q) hn hK ≤ tmGLGam hn hK' := by
  rintro σ ⟨h, hh, hσ⟩
  exact ⟨h, hKK hh, hσ⟩

/-- **`N ≀ Sym(q)`**: the pairs of class `1`, that is, with all coordinates in `N`. -/
def tmGLW (N : Subgroup (Perm B)) : Subgroup (Perm (B × Fin q)) where
  carrier := {σ | tmGLCls N 1 σ}
  one_mem' := tmGLCls_one
  mul_mem' := by
    rintro σ τ ⟨d, π, rfl, hd⟩ ⟨d', π', rfl, hd'⟩
    refine ⟨_, _, tmGL_mul d d' π π', fun i => ?_⟩
    simp only [inv_one, one_mul] at hd hd' ⊢
    exact N.mul_mem (hd' i) (hd _)
  inv_mem' := by
    rintro σ ⟨d, π, rfl, hd⟩
    refine ⟨_, _, tmGL_inv d π, fun i => ?_⟩
    simp only [inv_one, one_mul] at hd ⊢
    exact N.inv_mem (hd _)

theorem mem_tmGLW {σ : Perm (B × Fin q)} :
    σ ∈ tmGLW N ↔ ∃ d π, σ = tmGLP (d, π) ∧ ∀ i, d i ∈ N := by
  change tmGLCls N 1 σ ↔ _
  simp [tmGLCls]

theorem tmGLW_le_gam (hn : Normalizes H N) {K : Subgroup (Perm B)} (hK : K ≤ H) :
    tmGLW (q := q) N ≤ tmGLGam hn hK :=
  fun _ hσ => ⟨1, K.one_mem, hσ⟩

/-- A pair with a class normalizes `N ≀ Sym(q)`. -/
theorem tmGLW_conj (hn : Normalizes H N) {h : Perm B} (hh : h ∈ H)
    {σ τ : Perm (B × Fin q)} (hσ : tmGLCls N h σ) (hτ : τ ∈ tmGLW N) :
    σ * τ * σ⁻¹ ∈ tmGLW N := by
  have hτ' : tmGLCls N 1 τ := hτ
  have h1 := tmGLCls_mul hn H.one_mem hτ' (tmGLCls_inv hn hh hσ)
  have h2 := tmGLCls_mul hn hh hσ h1
  change tmGLCls N 1 _
  rw [mul_assoc]
  exact tmGLCls_of_mem (by simp) h2

/-! ### Strings on `B × Fin q` and their stabilizers -/

variable {C : Type}

/-- The string of a row tuple: `X(c, i) = x_i c`. -/
def tmGLStr (x : Fin q → B → C) : B × Fin q → C := fun a => x a.2 a.1

/-- **A pair carries the rows of `x` to those of `y`** (`x_i ∘ d_i = y_{π i}`) exactly when its
permutation carries the string `X` to `Y` (`Y ∘ σ = X`). -/
theorem tmGL_str_comp (x y : Fin q → B → C) (d : Fin q → Perm B) (π : Perm (Fin q)) :
    tmGLStr y ∘ tmGLP (d, π) = tmGLStr x ↔ ∀ i, x i ∘ d i = y (π i) := by
  constructor
  · intro h i
    funext c
    have := congrFun h (d i c, i)
    simpa [tmGLStr] using this.symm
  · intro h
    funext ⟨c, i⟩
    have := congrFun (h i) ((d i)⁻¹ c)
    simp only [Function.comp, Perm.apply_inv_self] at this
    simp [tmGLStr, this]

/-- **The stabilizer of a string** `Y` on `B × Fin q`: `{σ | Y ∘ σ = Y}`. -/
def tmGLAut (Y : B × Fin q → C) : Subgroup (Perm (B × Fin q)) where
  carrier := {σ | Y ∘ σ = Y}
  one_mem' := by simp
  mul_mem' := by
    intro σ τ hσ hτ
    change Y ∘ ⇑(σ * τ : Perm (B × Fin q)) = Y
    rw [Perm.coe_mul, ← Function.comp_assoc, hσ, hτ]
  inv_mem' := by
    intro σ hσ
    change Y ∘ ⇑(σ⁻¹ : Perm (B × Fin q)) = Y
    funext a
    have := congrFun hσ (σ⁻¹ a)
    simp only [Function.comp, Perm.apply_inv_self] at this
    simp only [Function.comp]
    exact this.symm

theorem mem_tmGLAut {Y : B × Fin q → C} {σ : Perm (B × Fin q)} :
    σ ∈ tmGLAut Y ↔ Y ∘ σ = Y := Iff.rfl

/-- The transporters `X → Y` form a right coset of `Aut(Y)`: if `Y ∘ σ₀ = X` and `Y ∘ σ = X`,
then `σ σ₀⁻¹ ∈ Aut(Y)`. -/
theorem tmGL_trans_aut {X Y : B × Fin q → C} {σ σ₀ : Perm (B × Fin q)}
    (h0 : Y ∘ σ₀ = X) (h : Y ∘ σ = X) : σ * σ₀⁻¹ ∈ tmGLAut Y := by
  change Y ∘ ⇑(σ * σ₀⁻¹ : Perm (B × Fin q)) = Y
  funext a
  have := congrFun h0 (σ₀⁻¹ a)
  simp only [Function.comp, Perm.apply_inv_self] at this
  simp only [Function.comp, Perm.coe_mul]
  rw [show Y (σ (σ₀⁻¹ a)) = X (σ₀⁻¹ a) from congrFun h _, ← this]

theorem tmGL_aut_trans {X Y : B × Fin q → C} {σ₀ a : Perm (B × Fin q)}
    (h0 : Y ∘ σ₀ = X) (ha : a ∈ tmGLAut Y) : Y ∘ (a * σ₀) = X := by
  rw [Perm.coe_mul, ← Function.comp_assoc, mem_tmGLAut.mp ha, h0]

/-! ### Totals -/

variable {A : Type} [CommGroup A] (φ : N →* A)

/-- The total label `∏ φ(d_i)` of a coordinate tuple. -/
noncomputable def tmGLTot (d : Fin q → Perm B) : A := ∏ i, phiT N φ (d i)

variable {φ} in
theorem tmGLTot_mul {d d' : Fin q → Perm B} (hd : ∀ i, d i ∈ N) (hd' : ∀ i, d' i ∈ N)
    (π' : Perm (Fin q)) :
    tmGLTot φ (fun i => d' i * d (π' i)) = tmGLTot φ d' * tmGLTot φ d := by
  unfold tmGLTot
  rw [Finset.prod_congr rfl fun i _ => phiT_mul (hd' i) (hd (π' i)), Finset.prod_mul_distrib,
    Equiv.prod_comp π' (fun i => phiT N φ (d i))]

end GI.Impl
