module

public import Workspace.Impl.TermCosetLink

@[expose] public section

/-!
# Reading `N`-transporters from the stored coset table: the mathematics

Steps 2 and 3 of the label program. Proof of Theorem A.23: "For a later `h`
carrying type `a` to type `c`, the known membership in `N Iso_H(z_a, z_c)`, together with
constructive factorization in the normalized product `N Aut_H(z_a)`, supplies the required
local `N`-transporter in polynomial time. Thus computing offsets in different radical cosets
makes no new string-isomorphism calls." The model stores the cosets `Iso_H(x_j, y_l)`, so the
step reads them as follows.

Let `Z` be a row string and `w ∈ H` with `Z^w = y_l`, and let the stored coset be
`Iso_H(x_j, y_l) = g ⟨A⟩`. Then `Z` lies in the `N`-orbit of `x_j` exactly when
`g⁻¹ w ∈ ⟨A⟩ N` (`tmGLP_rel_iff`), and a factorization `g⁻¹ w = a m` with `a ∈ ⟨A⟩`, `m ∈ N`
gives the `N`-transporter `w m⁻¹ w⁻¹` from `x_j` to `Z` (`tmGLP_rel_out`).

Both uses of the label program are of this form:

* the aligned rows `y'_i = y_i^{k_i(τ)⁻¹}`: `Z = y'_i`, `w = k_i(τ)`, `l = i`;
* the transporters `t_a(s)`: `Z = x_j^s`, `w = s⁻¹ g_{jl}` for a stored `g_{jl} ∈ Iso_H(x_j, y_l)`.
-/

namespace GI.Impl

open GI.Multicoset Equiv
open GI.Cited (gens)

variable {n : ℕ} {Ω : Type*} [RAct (Perm (Fin n)) Ω]

section Rel

variable {H N : Subgroup (Perm (Fin n))} {X0 Y Z : Ω} {g w : Perm (Fin n)}
  {A : List (Perm (Fin n))}

/-- The stored coset lies in `H`: `g ∈ H` and `⟨A⟩ ≤ H`. -/
theorem tmGLP_rel_le (hI : Iso H X0 Y = (fun k => g * k) '' (gens A : Set (Perm (Fin n)))) :
    g ∈ H ∧ gens A ≤ H := by
  have hg : g ∈ Iso H X0 Y := by rw [hI]; exact ⟨1, (gens A).one_mem, mul_one g⟩
  refine ⟨hg.1, fun k hk => ?_⟩
  have hgk : g * k ∈ Iso H X0 Y := by rw [hI]; exact ⟨k, hk, rfl⟩
  have := H.mul_mem (H.inv_mem hg.1) hgk.1
  simpa using this

/-- **The transporter from a factorization**: if `g⁻¹ w = a m` with `a ∈ ⟨A⟩` and `m ∈ N`,
then `w m⁻¹ w⁻¹ ∈ N` carries `x_j` to `Z`. -/
theorem tmGLP_rel_out (hn : Normalizes H N)
    (hI : Iso H X0 Y = (fun k => g * k) '' (gens A : Set (Perm (Fin n)))) (hw : w ∈ H)
    (hZ : Z ↼ w = Y) {a m : Perm (Fin n)} (ha : a ∈ gens A) (hm : m ∈ N)
    (he : g⁻¹ * w = a * m) : w * m⁻¹ * w⁻¹ ∈ N ∧ X0 ↼ (w * m⁻¹ * w⁻¹) = Z := by
  refine ⟨hn w hw _ (N.inv_mem hm), ?_⟩
  -- `g a = w m⁻¹` lies in the stored coset
  have hga : g * a ∈ Iso H X0 Y := by rw [hI]; exact ⟨a, ha, rfl⟩
  have e : g * a = w * m⁻¹ := by
    have : a = g⁻¹ * w * m⁻¹ := by rw [he]; group
    rw [this]; group
  rw [e] at hga
  have h1 : X0 ↼ (w * m⁻¹ * w⁻¹) ↼ w = Z ↼ w := by
    rw [act_act, show w * m⁻¹ * w⁻¹ * w = w * m⁻¹ by group, hga.2, hZ]
  have h2 := congrArg (fun t => t ↼ w⁻¹) h1
  simpa only [act_act_inv] using h2

/-- **The test**: `Z` is in the `N`-orbit of `x_j` exactly when `g⁻¹ w ∈ ⟨A⟩ N`. -/
theorem tmGLP_rel_iff (hNH : N ≤ H) (hn : Normalizes H N)
    (hI : Iso H X0 Y = (fun k => g * k) '' (gens A : Set (Perm (Fin n)))) (hw : w ∈ H)
    (hZ : Z ↼ w = Y) :
    (∃ x ∈ N, X0 ↼ x = Z) ↔ ∃ a ∈ gens A, ∃ m ∈ N, g⁻¹ * w = a * m := by
  constructor
  · rintro ⟨x, hx, hxZ⟩
    -- `x w ∈ Iso_H(x_j, y_l) = g ⟨A⟩`
    have hxw : x * w ∈ Iso H X0 Y := ⟨H.mul_mem (hNH hx) hw, by rw [← act_act, hxZ, hZ]⟩
    rw [hI] at hxw
    obtain ⟨k, hk, hke⟩ := hxw
    refine ⟨k, hk, w⁻¹ * x⁻¹ * w, hn.inv hw (N.inv_mem hx), ?_⟩
    have : g⁻¹ = k * w⁻¹ * x⁻¹ := by
      have h1 : g = x * w * k⁻¹ := by rw [show x * w = g * k from hke.symm]; group
      rw [h1]; group
    rw [this]; group
  · rintro ⟨a, ha, m, hm, he⟩
    exact ⟨_, (tmGLP_rel_out hn hI hw hZ ha hm he).1, (tmGLP_rel_out hn hI hw hZ ha hm he).2⟩

/-- The empty coset: no element of `N` carries `x_j` to `Z`. -/
theorem tmGLP_rel_empty (hNH : N ≤ H) (hI : Iso H X0 Y = ∅) (hw : w ∈ H) (hZ : Z ↼ w = Y) :
    ∀ x ∈ N, X0 ↼ x ≠ Z := by
  intro x hx hxZ
  have hxw : x * w ∈ Iso H X0 Y := ⟨H.mul_mem (hNH hx) hw, by rw [← act_act, hxZ, hZ]⟩
  rw [hI] at hxw
  exact hxw

/-- **The product group**: `g⁻¹ w ∈ ⟨A, 1, σN⟩` exactly when `g⁻¹ w ∈ ⟨A⟩ N`, when `⟨A⟩`
normalizes `N = ⟨σN⟩`. -/
theorem tmGLP_rel_gens {σN : List (Perm (Fin n))} (hn : Normalizes (gens A) (gens σN))
    (x : Perm (Fin n)) :
    x ∈ gens (A ++ 1 :: σN) ↔ ∃ a ∈ gens A, ∃ m ∈ gens σN, x = a * m := by
  constructor
  · intro hx
    refine closure_mem_mul hn (fun γ hγ => ?_) x hx
    rcases List.mem_append.1 hγ with h | h
    · exact ⟨γ, Subgroup.subset_closure h, 1, (gens σN).one_mem, by simp⟩
    · rcases List.mem_cons.1 h with rfl | h
      · exact ⟨1, (gens A).one_mem, 1, (gens σN).one_mem, by simp⟩
      · exact ⟨1, (gens A).one_mem, γ, Subgroup.subset_closure h, by simp⟩
  · rintro ⟨a, ha, m, hm, rfl⟩
    have hA : gens A ≤ gens (A ++ 1 :: σN) :=
      Subgroup.closure_mono fun γ hγ => List.mem_append_left _ hγ
    have hN : gens σN ≤ gens (A ++ 1 :: σN) :=
      Subgroup.closure_mono fun γ hγ => List.mem_append_right _ (List.mem_cons_of_mem _ hγ)
    exact Subgroup.mul_mem _ (hA ha) (hN hm)

end Rel

end GI.Impl
