import Workspace.Impl.AggRectSpec

/-!
# Generators of the permitted label group

Lemma A.27 queries the group `H = π⁻¹(P)` with
`P = (Sym W × Sym R × Sym Y) ∩ Alt(Γ)`, `Y = Γ \ (W ∪ R)` (`permitted W R`). The program obtains
`H` from the cited **Preimage** task, which needs generators of `P`. This file gives them.

Call two labels *of one part* when they lie in the same one of the three parts `W`, `R`, `Y`.
Fix two labels `w₀ ≠ w₁` of `W` (here `|W| ≥ 3`). The generators are `t₀ · (a b)` for all labels
`a ≠ b` of one part, with `t₀ = (w₀ w₁)` (`rcRGen`); for the other pairs `(a, b)` the list holds
the identity.

Why they generate `P` (`rcR_closure_gens`):
* every permutation that keeps the three parts is a product of transpositions inside the parts
  (`rcR_sides_le`, induction on the support: `(a σ(a)) σ` fixes `a` and moves fewer points);
* an even product of such transpositions `t₁ ⋯ t_{2n}` is a product of the pairs
  `t_{2i-1} t_{2i} = (t₀ t_{2i-1})⁻¹ (t₀ t_{2i})`. The proof (`rcR_even_mem`) shows by induction
  on a word that every element `σ` of the group of the transpositions has `σ ∈ K` or `t₀ σ ∈ K`,
  for the group `K` of the generators; conjugation by `t₀` keeps `K`, since it sends `t₀ t` to
  `t t₀ = (t₀ t)⁻¹`. An even `σ` cannot have `t₀ σ ∈ K ≤ Alt(Γ)`.
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Rectangle
open GI.Cited (gens)
open scoped Pointwise

variable {q : ℕ}

/-- Two labels lie in one of the parts `W`, `R`, `Γ \ (W ∪ R)`. -/
def rcRSame (W R : Finset (Fin q)) (a b : Fin q) : Prop := (a ∈ W ↔ b ∈ W) ∧ (a ∈ R ↔ b ∈ R)

instance (W R : Finset (Fin q)) (a b : Fin q) : Decidable (rcRSame W R a b) := by
  unfold rcRSame; infer_instance

/-- The generator of the pair `(a, b)`: `(w₀ w₁)(a b)` for labels `a ≠ b` of one part, and `1`
otherwise. -/
def rcRGen (W R : Finset (Fin q)) (w₀ w₁ a b : Fin q) : Perm (Fin q) :=
  if a ≠ b ∧ rcRSame W R a b then swap w₀ w₁ * swap a b else 1

/-- The list of the generators, over all pairs `(a, b)`. -/
def rcRGens (W R : Finset (Fin q)) (w₀ w₁ : Fin q) : List (Perm (Fin q)) :=
  (List.finRange q).flatMap fun a => (List.finRange q).map fun b => rcRGen W R w₀ w₁ a b

theorem rcR_mem_gens {W R : Finset (Fin q)} {w₀ w₁ : Fin q} {σ : Perm (Fin q)} :
    σ ∈ rcRGens W R w₀ w₁ ↔ ∃ a b, rcRGen W R w₀ w₁ a b = σ := by
  simp [rcRGens]

/-! ### Membership in the side stabilizer -/

theorem rcR_sides_iff {W R : Finset (Fin q)} {σ : Perm (Fin q)} :
    σ ∈ sides W R ↔ (∀ a, σ a ∈ W ↔ a ∈ W) ∧ (∀ a, σ a ∈ R ↔ a ∈ R) := by
  have key : ∀ T : Finset (Fin q), σ • (T : Set (Fin q)) = T ↔ ∀ a, σ a ∈ T ↔ a ∈ T := by
    intro T
    constructor
    · intro he a
      have hm : σ • a ∈ σ • (T : Set (Fin q)) ↔ a ∈ (T : Set (Fin q)) := Set.smul_mem_smul_set_iff
      rw [he] at hm
      exact hm
    · intro h
      ext a
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      have := h (σ⁻¹ a)
      simp only [Perm.smul_def, Finset.mem_coe]
      rw [← this, Perm.apply_inv_self]
  exact Iff.and (key W) (key R)

theorem rcR_swap_sides {W R : Finset (Fin q)} {a b : Fin q} (h : rcRSame W R a b) :
    swap a b ∈ sides W R := by
  refine rcR_sides_iff.2 ⟨fun x => ?_, fun x => ?_⟩
  · rcases eq_or_ne x a with rfl | hxa
    · rw [swap_apply_left]; exact h.1.symm
    rcases eq_or_ne x b with rfl | hxb
    · rw [swap_apply_right]; exact h.1
    rw [swap_apply_of_ne_of_ne hxa hxb]
  · rcases eq_or_ne x a with rfl | hxa
    · rw [swap_apply_left]; exact h.2.symm
    rcases eq_or_ne x b with rfl | hxb
    · rw [swap_apply_right]; exact h.2
    rw [swap_apply_of_ne_of_ne hxa hxb]

/-- The transpositions inside the parts. -/
def rcRSwaps (W R : Finset (Fin q)) : Set (Perm (Fin q)) :=
  {σ | ∃ a b, a ≠ b ∧ rcRSame W R a b ∧ σ = swap a b}

/-- **A permutation keeping the parts is a product of transpositions inside the parts.** -/
theorem rcR_sides_le (W R : Finset (Fin q)) : sides W R ≤ Subgroup.closure (rcRSwaps W R) := by
  suffices h : ∀ n, ∀ σ : Perm (Fin q), σ ∈ sides W R → σ.support.card = n →
      σ ∈ Subgroup.closure (rcRSwaps W R) from fun σ hσ => h _ σ hσ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ hσ hn
    by_cases h1 : σ = 1
    · rw [h1]; exact Subgroup.one_mem _
    obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
      by_contra hc
      push_neg at hc
      exact h1 (Perm.ext hc)
    have hsame : rcRSame W R a (σ a) :=
      ⟨((rcR_sides_iff.1 hσ).1 a).symm, ((rcR_sides_iff.1 hσ).2 a).symm⟩
    have hτ : swap a (σ a) * σ ∈ sides W R := (sides W R).mul_mem (rcR_swap_sides hsame) hσ
    have hlt := card_support_swap_mul ha
    have hmem := ih _ (hn ▸ hlt) _ hτ rfl
    have he : σ = swap a (σ a) * (swap a (σ a) * σ) := by rw [← mul_assoc, swap_mul_self, one_mul]
    rw [he]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨a, σ a, ha.symm, hsame, rfl⟩) hmem

/-! ### The even part -/

section Even

variable {W R : Finset (Fin q)} {w₀ w₁ : Fin q}

theorem rcR_gen_mem_alt (hw : w₀ ≠ w₁) (a b : Fin q) :
    rcRGen W R w₀ w₁ a b ∈ alternatingGroup (Fin q) := by
  unfold rcRGen
  split_ifs with h
  · rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hw, sign_swap h.1]; rfl
  · exact Subgroup.one_mem _

theorem rcR_gen_sides (hw : rcRSame W R w₀ w₁) (a b : Fin q) :
    rcRGen W R w₀ w₁ a b ∈ sides W R := by
  unfold rcRGen
  split_ifs with h
  · exact (sides W R).mul_mem (rcR_swap_sides hw) (rcR_swap_sides h.2)
  · exact Subgroup.one_mem _

/-- The group of the generators. -/
abbrev rcRK (W R : Finset (Fin q)) (w₀ w₁ : Fin q) : Subgroup (Perm (Fin q)) :=
  gens (rcRGens W R w₀ w₁)

theorem rcR_gen_memK (a b : Fin q) : rcRGen W R w₀ w₁ a b ∈ rcRK W R w₀ w₁ :=
  Subgroup.subset_closure (rcR_mem_gens.2 ⟨a, b, rfl⟩)

/-- `t₀ (a b) ∈ K` for a transposition `(a b)` inside a part. -/
theorem rcR_t0_swap_mem {σ : Perm (Fin q)} (hσ : σ ∈ rcRSwaps W R) :
    swap w₀ w₁ * σ ∈ rcRK W R w₀ w₁ := by
  obtain ⟨a, b, hab, hs, rfl⟩ := hσ
  have := rcR_gen_memK (W := W) (R := R) (w₀ := w₀) (w₁ := w₁) a b
  unfold rcRGen at this
  rwa [if_pos ⟨hab, hs⟩] at this

/-- Conjugation by `t₀` keeps `K`. -/
theorem rcR_conj_mem {x : Perm (Fin q)} (hx : x ∈ rcRK W R w₀ w₁) :
    swap w₀ w₁ * x * swap w₀ w₁ ∈ rcRK W R w₀ w₁ := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, b, rfl⟩ := rcR_mem_gens.1 hy
    unfold rcRGen
    split_ifs with h
    · -- `t₀ (t₀ (a b)) t₀ = (a b) t₀ = (t₀ (a b))⁻¹`
      have e : swap w₀ w₁ * (swap w₀ w₁ * swap a b) * swap w₀ w₁ =
          (swap w₀ w₁ * swap a b)⁻¹ := by
        rw [← mul_assoc, swap_mul_self, one_mul, mul_inv_rev, swap_inv, swap_inv]
      rw [e]
      refine Subgroup.inv_mem _ ?_
      have := rcR_gen_memK (W := W) (R := R) (w₀ := w₀) (w₁ := w₁) a b
      unfold rcRGen at this
      rwa [if_pos h] at this
    · rw [mul_one, swap_mul_self]; exact Subgroup.one_mem _
  | one => rw [mul_one, swap_mul_self]; exact Subgroup.one_mem _
  | mul y z _ _ hy hz =>
    have e : swap w₀ w₁ * (y * z) * swap w₀ w₁ =
        (swap w₀ w₁ * y * swap w₀ w₁) * (swap w₀ w₁ * z * swap w₀ w₁) := by
      simp only [mul_assoc, swap_mul_self_mul]
    rw [e]; exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
    have e : swap w₀ w₁ * y⁻¹ * swap w₀ w₁ = (swap w₀ w₁ * y * swap w₀ w₁)⁻¹ := by
      simp only [mul_inv_rev, swap_inv, mul_assoc]
    rw [e]; exact Subgroup.inv_mem _ hy

/-- Every element `σ` of the group of the transpositions has `σ ∈ K` or `t₀ σ ∈ K`. -/
theorem rcR_dich {σ : Perm (Fin q)} (hσ : σ ∈ Subgroup.closure (rcRSwaps W R)) :
    σ ∈ rcRK W R w₀ w₁ ∨ swap w₀ w₁ * σ ∈ rcRK W R w₀ w₁ := by
  set t := swap w₀ w₁ with ht
  set K := rcRK W R w₀ w₁ with hK
  -- from `t x ∈ K`: `x t = t (t x) t ∈ K`
  have hright : ∀ x, t * x ∈ K → x * t ∈ K := fun x hx => by
    have := rcR_conj_mem hx
    rwa [← mul_assoc, ht, swap_mul_self, one_mul] at this
  induction hσ using Subgroup.closure_induction with
  | mem y hy => exact Or.inr (rcR_t0_swap_mem hy)
  | one => exact Or.inl (Subgroup.one_mem _)
  | mul y z _ _ hy hz =>
    rcases hy with hy | hy <;> rcases hz with hz | hz
    · exact Or.inl (K.mul_mem hy hz)
    · -- `t y z = (t y t)(t z)`
      right
      have e : t * (y * z) = (t * y * t) * (t * z) := by
        rw [ht]; simp only [mul_assoc, swap_mul_self_mul]
      rw [e]; exact K.mul_mem (rcR_conj_mem hy) hz
    · right
      rw [← mul_assoc]; exact K.mul_mem hy hz
    · -- `y z = (y t)(t z)`
      left
      have e : y * z = (y * t) * (t * z) := by
        rw [ht]; simp only [mul_assoc, swap_mul_self_mul]
      rw [e]; exact K.mul_mem (hright y hy) hz
  | inv y _ hy =>
    rcases hy with hy | hy
    · exact Or.inl (K.inv_mem hy)
    · -- `t y⁻¹ = t (y⁻¹ t) t` and `y⁻¹ t = (t y)⁻¹`
      right
      have h1 : y⁻¹ * t ∈ K := by
        have := K.inv_mem hy
        rwa [mul_inv_rev, ht, swap_inv] at this
      have := rcR_conj_mem h1
      rwa [mul_assoc, mul_assoc, ht, swap_mul_self, mul_one] at this

theorem rcR_K_le_alt (hw : w₀ ≠ w₁) : rcRK W R w₀ w₁ ≤ alternatingGroup (Fin q) := by
  refine (Subgroup.closure_le _).2 fun σ hσ => ?_
  obtain ⟨a, b, rfl⟩ := rcR_mem_gens.1 hσ
  exact rcR_gen_mem_alt hw a b

/-- **The generators generate the permitted group** (as permutations of the labels). -/
theorem rcR_closure_gens (hd : Disjoint W R) (hw0 : w₀ ∈ W) (hw1 : w₁ ∈ W) (hw : w₀ ≠ w₁) :
    rcRK W R w₀ w₁ = (permitted W R).map (alternatingGroup (Fin q)).subtype := by
  have hsame : rcRSame W R w₀ w₁ := ⟨iff_of_true hw0 hw1,
    iff_of_false (Finset.disjoint_left.1 hd hw0) (Finset.disjoint_left.1 hd hw1)⟩
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 fun σ hσ => ?_
    obtain ⟨a, b, rfl⟩ := rcR_mem_gens.1 hσ
    exact ⟨⟨_, rcR_gen_mem_alt hw a b⟩, rcR_gen_sides hsame a b, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hx : (p : Perm (Fin q)) ∈ Subgroup.closure (rcRSwaps W R) := rcR_sides_le W R hp
    rcases rcR_dich (w₀ := w₀) (w₁ := w₁) hx with h | h
    · exact h
    · exfalso
      have h1 := rcR_K_le_alt hw h
      rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hw, p.2.out] at h1
      exact absurd h1 (by decide)

end Even

end GI.Impl
