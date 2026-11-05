module

public import Workspace.Impl.TermJYoung
public import Workspace.Impl.LinCoordinateCertificate
public import Workspace.MulticosetTerminal

@[expose] public section

/-!
# Labels of pairs in `A = N/N*` (math for the paper's zero-sum route)

Proof of Theorem A.23: the label of a pair `(d, π)` with all `d_i ∈ N` is `lab = ∏ φ(d_i)` in
the abelian group `A = N/N*`. A pair lies in `J` exactly when its label is `1` and its top is
even (`InJ`). This file has the generic facts used by the zero-sum correction and by the
generators of `Aut_J(x)`:

* `tmJ_cert_ker`: a presentation certificate gives the exact kernel of the coordinate map;
* `tmJLab_mul`, `tmJLab_inv`, `tmJLab_loc`, `tmJLab_sw`: the label is a homomorphism on pairs
  with coordinates in `N`; a local generator has the label of its entry; a lifted transposition
  of two different rows has label `1`;
* `tmJLab_eq_one_iff`: two maps `N → A`, `N → A'` with the same kernel give the same pairs of
  label `1`;
* `tmJ_even_gens`: if odd involutions `T` generate `W`, then `t₀ t` (`t ∈ T`) generate the even
  part (Schreier's lemma for index two, in the form needed here).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Multicoset

/-! ### The kernel of a presented coordinate map -/

/-- A presentation certificate gives the kernel of the coordinate map exactly. -/
theorem tmJ_cert_ker {t : ℕ} {Q : Type*} [AddCommGroup Q] {M : Matrix (Fin t) (Fin t) ℤ}
    {f : (Fin t → ℤ) →ₗ[ℤ] Q} (h : linPresentationCertificate M f) (v : Fin t → ℤ) :
    f v = 0 ↔ v ∈ linRelations M := by
  obtain ⟨hM, hf, hrel, hcard⟩ := h
  constructor
  · intro hv
    have e := linPresentationEquiv_mk M hM f hf hrel hcard v
    rw [hv, ← map_zero (linPresentationEquiv M hM f hf hrel hcard)] at e
    have := (linPresentationEquiv M hM f hf hrel hcard).injective e
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  · intro hv
    exact hrel hv

/-! ### Labels of pairs -/

variable {B : Type} {q : ℕ} (N : Subgroup (Perm B)) {A : Type*} [CommGroup A] (φ : N →* A)

/-- The label `∏ φ(d_i)` of the coordinates of a pair. -/
noncomputable def tmJLab (d : Fin q → Perm B) : A := ∏ i, phiT N φ (d i)

variable {N φ}

theorem tmJLab_one : tmJLab N φ (1 : Fin q → Perm B) = 1 := by
  simp [tmJLab, phiT_one]

/-- The label of a product of pairs (`tmJP_mul`) is the product of the labels. -/
theorem tmJLab_mul {d d' : Fin q → Perm B} (π' : Perm (Fin q)) (hd : ∀ i, d i ∈ N)
    (hd' : ∀ i, d' i ∈ N) :
    tmJLab N φ (fun i => d' i * d (π' i)) = tmJLab N φ d' * tmJLab N φ d := by
  unfold tmJLab
  rw [Finset.prod_congr rfl fun i _ => phiT_mul (hd' i) (hd (π' i)), Finset.prod_mul_distrib]
  congr 1
  exact Equiv.prod_comp π' (fun i => phiT N φ (d i))

/-- The label of an inverse pair (`tmJP_inv`) is the inverse label. -/
theorem tmJLab_inv {d : Fin q → Perm B} (π : Perm (Fin q)) (hd : ∀ i, d i ∈ N) :
    tmJLab N φ (fun i => (d (π⁻¹ i))⁻¹) = (tmJLab N φ d)⁻¹ := by
  unfold tmJLab
  rw [Finset.prod_congr rfl fun i _ => phiT_inv (hd (π⁻¹ i)), Finset.prod_inv_distrib]
  congr 1
  exact Equiv.prod_comp π⁻¹ (fun i => phiT N φ (d i))

/-- A local generator has the label of its entry. -/
theorem tmJLab_loc (a : Fin q) (g : Perm B) :
    tmJLab N φ (Pi.mulSingle a g) = phiT N φ g := by
  unfold tmJLab
  rw [Finset.prod_eq_single a]
  · simp
  · intro b _ hb; simp [hb, phiT_one]
  · simp

/-- A lifted transposition of two different rows has label `1`. -/
theorem tmJLab_sw {a a' : Fin q} (haa : a ≠ a') {b : Perm B} (hb : b ∈ N) :
    tmJLab N φ (tmJSwD a a' b) = 1 := by
  classical
  unfold tmJLab tmJSwD
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a'),
    ← Finset.prod_erase_mul _ _ (Finset.mem_erase.2 ⟨haa, Finset.mem_univ a⟩)]
  rw [Finset.prod_eq_one]
  · simp only [Function.update_self, Function.update_of_ne haa, Pi.mulSingle_eq_same, one_mul]
    rw [phiT_inv hb, mul_inv_cancel]
  · intro i hi
    simp only [Finset.mem_erase] at hi
    rw [Function.update_of_ne hi.2.1, Pi.mulSingle_eq_of_ne hi.1, phiT_one]

/-- The ordered product of the coordinates. -/
def tmJProd (d : Fin q → Perm B) : Perm B := ((List.finRange q).map d).prod

theorem tmJProd_mem {d : Fin q → Perm B} (hd : ∀ i, d i ∈ N) : tmJProd d ∈ N := by
  unfold tmJProd
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact hd i

/-- The label is the image of the ordered product. -/
theorem tmJLab_eq_prod {d : Fin q → Perm B} (hd : ∀ i, d i ∈ N) :
    tmJLab N φ d = phiT N φ (tmJProd d) := by
  unfold tmJLab tmJProd
  rw [Fin.prod_univ_def]
  have key : ∀ l : List (Fin q), (∀ i ∈ l, d i ∈ N) →
      (l.map fun i => phiT N φ (d i)).prod = phiT N φ ((l.map d).prod) := by
    intro l
    induction l with
    | nil => intro _; simp [phiT_one]
    | cons i l ih =>
      intro hl
      simp only [List.map_cons, List.prod_cons]
      rw [ih fun j hj => hl j (List.mem_cons_of_mem _ hj), phiT_mul (hl i (List.mem_cons_self))]
      apply Subgroup.list_prod_mem
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact hl j (List.mem_cons_of_mem _ hj)
  rw [← key _ fun i _ => hd i]

/-- **Two maps with the same kernel give the same pairs of label `1`.** -/
theorem tmJLab_eq_one_iff {A' : Type*} [CommGroup A'] {φ' : N →* A'}
    (hk : ∀ n : N, φ n = 1 ↔ φ' n = 1) {d : Fin q → Perm B} (hd : ∀ i, d i ∈ N) :
    tmJLab N φ d = 1 ↔ tmJLab N φ' d = 1 := by
  rw [tmJLab_eq_prod hd, tmJLab_eq_prod hd]
  have hp := tmJProd_mem hd
  simp only [phiT, dif_pos hp]
  exact hk _

/-! ### The even part of a group generated by odd involutions -/

theorem tmJ_units_cases (u : ℤˣ) : u = 1 ∨ u = -1 := Int.units_eq_one_or u

/-- **Schreier's lemma for index two**, for generators that are odd involutions: the products
`t₀ s` generate the even part. -/
theorem tmJ_even_gens {G : Type*} [Group G] (χ : G →* ℤˣ) {S : List G} {t0 : G} (ht0 : t0 ∈ S)
    (hS : ∀ s ∈ S, s * s = 1 ∧ χ s = -1) :
    Subgroup.closure {g | ∃ s ∈ S, g = t0 * s} = Subgroup.closure {s | s ∈ S} ⊓ χ.ker := by
  set K := Subgroup.closure {g | ∃ s ∈ S, g = t0 * s}
  have hinv : ∀ s ∈ S, s⁻¹ = s := fun s hs => inv_eq_of_mul_eq_one_right (hS s hs).1
  have hK : ∀ s ∈ S, t0 * s ∈ K ∧ s * t0 ∈ K := by
    intro s hs
    have h1 : t0 * s ∈ K := Subgroup.subset_closure ⟨s, hs, rfl⟩
    refine ⟨h1, ?_⟩
    have := K.inv_mem h1
    rwa [mul_inv_rev, hinv s hs, hinv t0 ht0] at this
  have hm1 : (-1 : ℤˣ) ≠ 1 := by decide
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
  · rintro g ⟨s, hs, rfl⟩
    refine ⟨Subgroup.mul_mem _ (Subgroup.subset_closure ht0) (Subgroup.subset_closure hs), ?_⟩
    show χ (t0 * s) = 1
    rw [map_mul, (hS t0 ht0).2, (hS s hs).2]; decide
  · rintro g ⟨hg, hgk⟩
    have key : ∀ x ∈ Subgroup.closure {s | s ∈ S},
        (χ x = 1 → x ∈ K) ∧ (χ x = -1 → x * t0 ∈ K) := by
      intro x hx
      induction hx using Subgroup.closure_induction_right with
      | one => exact ⟨fun _ => K.one_mem, fun h => absurd h.symm (by rw [map_one]; exact hm1)⟩
      | mul_right x _ s hs ih =>
        have hs1 := (hS s hs).2
        rcases tmJ_units_cases (χ x) with hx | hx
        · refine ⟨fun h => ?_, fun _ => ?_⟩
          · rw [map_mul, hx, hs1] at h; exact absurd h (by decide)
          · rw [mul_assoc]; exact K.mul_mem (ih.1 hx) (hK s hs).2
        · refine ⟨fun _ => ?_, fun h => ?_⟩
          · have e : x * s = x * t0 * (t0 * s) := by
              rw [mul_assoc x t0, ← mul_assoc t0 t0, (hS t0 ht0).1, one_mul]
            rw [e]; exact K.mul_mem (ih.2 hx) (hK s hs).1
          · rw [map_mul, hx, hs1] at h; exact absurd h (by decide)
      | mul_inv_cancel x _ s hs ih =>
        rw [hinv s hs]
        have hs1 := (hS s hs).2
        rcases tmJ_units_cases (χ x) with hx | hx
        · refine ⟨fun h => ?_, fun _ => ?_⟩
          · rw [map_mul, hx, hs1] at h; exact absurd h (by decide)
          · rw [mul_assoc]; exact K.mul_mem (ih.1 hx) (hK s hs).2
        · refine ⟨fun _ => ?_, fun h => ?_⟩
          · have e : x * s = x * t0 * (t0 * s) := by
              rw [mul_assoc x t0, ← mul_assoc t0 t0, (hS t0 ht0).1, one_mul]
            rw [e]; exact K.mul_mem (ih.2 hx) (hK s hs).1
          · rw [map_mul, hx, hs1] at h; exact absurd h (by decide)
    exact (key g hg).1 hgk

/-! ### Generators of a kernel -/

/-- **Generators of a kernel.** Let `F` and `Ψ` be homomorphisms on `Λ`. If `S₁ ⊆ ker F`
generates a group containing `ker Ψ`, `S₂ ⊆ ker F`, and the `Ψ`-image of `ker F` lies in the
`Ψ`-image of the closure of `S₂`, then `S₁ ∪ S₂` generates `ker F`. -/
theorem tmJ_ker_gens {Λ V A' : Type*} [Group Λ] [Group V] [Group A'] (F : Λ →* A') (Ψ : Λ →* V)
    (S₁ S₂ : Set Λ) (h₁ : S₁ ⊆ F.ker) (h₂ : S₂ ⊆ F.ker) (hΨ : Ψ.ker ≤ Subgroup.closure S₁)
    (him : ∀ x ∈ F.ker, ∃ y ∈ Subgroup.closure S₂, Ψ y = Ψ x) :
    Subgroup.closure (S₁ ∪ S₂) = F.ker := by
  refine le_antisymm ((Subgroup.closure_le _).2 (Set.union_subset h₁ h₂)) fun x hx => ?_
  obtain ⟨y, hy, hyx⟩ := him x hx
  have hxy : x * y⁻¹ ∈ Ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, mul_inv_cancel]
  have e : x = x * y⁻¹ * y := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.closure_mono Set.subset_union_left (hΨ hxy))
    (Subgroup.closure_mono Set.subset_union_right hy)

end GI.Impl
