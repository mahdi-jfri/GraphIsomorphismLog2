module

public import Workspace.Impl.TermJProgPair

@[expose] public section

/-!
# The local transporter of a class (the mathematics)

Setting: subgroups `H, N` of `Sym(m)` with `H` normalizing `N = ⟨σN⟩`, a permutation `h`, and
sets `A (a, j)` that are the cosets `Iso_H(x_a, y_j)`. The local test of `(a, j)` asks for
an element `u ∈ A (a, j)` with `h⁻¹ u ∈ N` (`tmJLTest`).

* `tmJL_ans`: an answer on `Fin m` with the trivial numbering is empty or a coset `g ⟨gs⟩`;
* `tmJL_test_iff`: for `A (a, j) = g ⟨gs⟩` the test is the membership `g⁻¹ h ∈ ⟨gs, σN⟩`;
* `tmJL_fac_pre`, `tmJL_fac`: such a membership factors as `g⁻¹ h = s n`, and `g s` is then the
  wanted element;
* `tmJL_rect`, `tmJL_match`: the tests have the rectangle property, so the matching by ranks
  (`tmJMatchO`) is a bijection along tests that pass.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv
open GI.Cited (Val encPerm encPerms encGroup gens)
open scoped Pointwise

variable {m q : ℕ}

/-- The trivial numbering does not move a set of permutations. -/
theorem tmJL_toFin_refl (S : Set (Perm (Fin m))) : toFin (Equiv.refl (Fin m)) '' S = S := by
  have e : ∀ σ : Perm (Fin m), toFin (Equiv.refl (Fin m)) σ = σ := fun σ => by
    ext; simp [toFin, Equiv.permCongrHom]
  ext u
  simp [e]

/-- **An answer on `Fin m`** is empty, or a coset `g ⟨gs⟩` with at most `m²` generators. -/
theorem tmJL_ans {v : Val} {S : Set (Perm (Fin m))} (h : AnsC (Equiv.refl (Fin m)) v S) :
    (v = .list [] ∧ S = ∅) ∨ ∃ (g : Perm (Fin m)) (gs : List (Perm (Fin m))),
      v = .list [encPerm g, encGroup gs] ∧ gs.length ≤ m ^ 2 ∧
        S = g • (gens gs : Set (Perm (Fin m))) := by
  rcases h with h | ⟨g, gs, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨g, gs, h1, h2, by rw [← h3, tmJL_toFin_refl]⟩

theorem tmJL_mem_coset {g u : Perm (Fin m)} {gs : List (Perm (Fin m))} :
    u ∈ g • (gens gs : Set (Perm (Fin m))) ↔ ∃ s ∈ gens gs, u = g * s := by
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩

/-- The generators of a coset inside `H` lie in `H`. -/
theorem tmJL_gs_mem {H : Subgroup (Perm (Fin m))} {g : Perm (Fin m)}
    {gs : List (Perm (Fin m))} (hS : g • (gens gs : Set (Perm (Fin m))) ⊆ H) :
    ∀ s ∈ gs, s ∈ H := by
  intro s hs
  have hg : g ∈ H := hS (tmJL_mem_coset.2 ⟨1, Subgroup.one_mem _, (mul_one g).symm⟩)
  have hgs : g * s ∈ H := hS (tmJL_mem_coset.2 ⟨s, Subgroup.subset_closure hs, rfl⟩)
  have := H.mul_mem (H.inv_mem hg) hgs
  rwa [inv_mul_cancel_left] at this

section Test

variable (N : Subgroup (Perm (Fin m))) (h : Perm (Fin m))

/-- **The local test** of a set: some element lies in the class `h N`. -/
def tmJLTest (S : Set (Perm (Fin m))) : Prop := ∃ u ∈ S, h⁻¹ * u ∈ N

variable {N}

/-- The generators of a coset inside `H` normalize `N`. -/
theorem tmJL_norm {H : Subgroup (Perm (Fin m))} (hn : GI.Multicoset.Normalizes H N)
    {σN : List (Perm (Fin m))} (hσN : gens σN = N) {gs : List (Perm (Fin m))}
    (hgs : ∀ s ∈ gs, s ∈ H) :
    GI.Lang.Normalizes (gens gs) (gens σN) := by
  have hle : gens gs ≤ H := (Subgroup.closure_le H).2 fun s hs => hgs s hs
  intro s hs x hx
  rw [hσN] at hx ⊢
  exact hn s (hle hs) x hx

/-- **A membership in `⟨gs, σN⟩` factors** as `s n` with `s ∈ ⟨gs⟩`, `n ∈ ⟨σN⟩`. -/
theorem tmJL_fac_iff {H : Subgroup (Perm (Fin m))} (hn : GI.Multicoset.Normalizes H N)
    {σN : List (Perm (Fin m))} (hσN : gens σN = N) {gs : List (Perm (Fin m))}
    (hgs : ∀ s ∈ gs, s ∈ H) {x : Perm (Fin m)} :
    x ∈ gens (gs ++ σN) ↔ ∃ s ∈ gens gs, ∃ n ∈ gens σN, x = s * n :=
  tmJ_mem_closure_append (fun s hs y hy => tmJL_norm hn hσN hgs s (Subgroup.subset_closure hs) y hy)

/-- **The local test is a Membership test.** -/
theorem tmJL_test_iff {H : Subgroup (Perm (Fin m))} (hn : GI.Multicoset.Normalizes H N)
    {σN : List (Perm (Fin m))} (hσN : gens σN = N) {g : Perm (Fin m)}
    {gs : List (Perm (Fin m))} (hgs : ∀ s ∈ gs, s ∈ H) :
    tmJLTest N h (g • (gens gs : Set (Perm (Fin m)))) ↔ g⁻¹ * h ∈ gens (gs ++ σN) := by
  rw [tmJL_fac_iff hn hσN hgs, hσN]
  constructor
  · rintro ⟨u, hu, hun⟩
    obtain ⟨s, hs, rfl⟩ := tmJL_mem_coset.1 hu
    exact ⟨s, hs, (h⁻¹ * (g * s))⁻¹, N.inv_mem hun, by group⟩
  · rintro ⟨s, hs, n, hn', he⟩
    refine ⟨g * s, tmJL_mem_coset.2 ⟨s, hs, rfl⟩, ?_⟩
    have : h⁻¹ * (g * s) = n⁻¹ := by
      have h1 : h = g * (s * n) := by rw [← he]; group
      rw [h1]; group
    rw [this]; exact N.inv_mem hn'

/-- **The local element from a factorization** `g⁻¹ h = s n`. -/
theorem tmJL_fac {g s n : Perm (Fin m)} {gs : List (Perm (Fin m))} (hs : s ∈ gens gs)
    (hn : n ∈ N) (he : g⁻¹ * h = s * n) :
    g * s ∈ g • (gens gs : Set (Perm (Fin m))) ∧ h⁻¹ * (g * s) ∈ N := by
  refine ⟨tmJL_mem_coset.2 ⟨s, hs, rfl⟩, ?_⟩
  have : g * s = h * n⁻¹ := by
    have h1 : h = g * (s * n) := by rw [← he]; group
    rw [h1]; group
  rw [this, inv_mul_cancel_left]; exact N.inv_mem hn

variable {C : Type} {H : Subgroup (Perm (Fin m))} {x y : Fin q → Fin m → C}
  {A : Fin q × Fin q → Set (Perm (Fin m))}

/-- **The local tests have the rectangle property.** -/
theorem tmJL_rect (hAdef : ∀ a j, A (a, j) = {u | u ∈ H ∧ x a ∘ ⇑u = y j}) {a a' j j' : Fin q}
    (h1 : tmJLTest N h (A (a, j))) (h2 : tmJLTest N h (A (a', j)))
    (h3 : tmJLTest N h (A (a, j'))) : tmJLTest N h (A (a', j')) := by
  obtain ⟨u1, hu1, hn1⟩ := h1
  obtain ⟨u2, hu2, hn2⟩ := h2
  obtain ⟨u3, hu3, hn3⟩ := h3
  rw [hAdef] at hu1 hu2 hu3
  refine ⟨u2 * u1⁻¹ * u3, ?_, ?_⟩
  · rw [hAdef]
    refine ⟨H.mul_mem (H.mul_mem hu2.1 (H.inv_mem hu1.1)) hu3.1, ?_⟩
    have e1 : x a' ∘ ⇑(u2 * u1⁻¹) = x a := by
      rw [Perm.coe_mul, ← Function.comp_assoc, hu2.2, ← hu1.2]; funext c; simp
    rw [← hu3.2, Perm.coe_mul, ← Function.comp_assoc, e1]
  · have e : h⁻¹ * (u2 * u1⁻¹ * u3) = (h⁻¹ * u2) * (h⁻¹ * u1)⁻¹ * (h⁻¹ * u3) := by group
    rw [e]
    exact N.mul_mem (N.mul_mem hn2 (N.inv_mem hn1)) hn3

variable (N A)

/-- The 0/1 matrix of the local tests. -/
noncomputable def tmJLMat : Fin q → Fin q → Bool := fun a j => by
  classical exact decide (tmJLTest N h (A (a, j)))

variable {N A}

theorem tmJLMat_iff {a j : Fin q} : tmJLMat N h A a j = true ↔ tmJLTest N h (A (a, j)) := by
  unfold tmJLMat
  classical
  simp

/-- **The matching by ranks** passes the local tests. -/
theorem tmJL_match (hAdef : ∀ a j, A (a, j) = {u | u ∈ H ∧ x a ∘ ⇑u = y j})
    (hmatch : ∃ π : Perm (Fin q), ∀ a, tmJLTest N h (A (a, π a))) :
    ∃ σ : Perm (Fin q), ∀ a, tmJMatchO (tmJLMat N h A) a = some (σ a) ∧
      tmJLTest N h (A (a, σ a)) := by
  obtain ⟨π, hπ⟩ := hmatch
  obtain ⟨σ, hσ⟩ := tmJMatch_spec (M := tmJLMat N h A)
    (fun a a' j j' h1 h2 h3 => (tmJLMat_iff h).2 (tmJL_rect h hAdef ((tmJLMat_iff h).1 h1)
      ((tmJLMat_iff h).1 h2) ((tmJLMat_iff h).1 h3))) π (fun a => (tmJLMat_iff h).2 (hπ a))
  exact ⟨σ, fun a => ⟨(hσ a).1, (tmJLMat_iff h).1 (hσ a).2⟩⟩

end Test

end GI.Impl
