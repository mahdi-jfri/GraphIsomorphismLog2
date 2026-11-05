module

public import Mathlib

@[expose] public section

/-!
# A counting lemma

If `a` maps a finite type into `T`, hits every point of `T`, and the weights `g ∘ a` add up to
at most the weights of `T` (all positive), then `a` is injective (`vsH_inj_of_sum`).
-/

namespace GI.Proved

theorem vsH_inj_of_sum {α β : Type*} [Fintype α] [DecidableEq β] (a : α → β) (T : Finset β)
    (g : β → ℕ) (hmap : ∀ i, a i ∈ T) (hsurj : ∀ b ∈ T, ∃ i, a i = b) (hpos : ∀ b ∈ T, 0 < g b)
    (hle : ∑ i, g (a i) ≤ ∑ b ∈ T, g b) : Function.Injective a := by
  classical
  intro i j hij
  by_contra hne
  have hfib : ∑ i, g (a i) = ∑ b ∈ T, (Finset.univ.filter fun k => a k = b).card * g b := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := T) (g := a)
      (fun k _ => hmap k)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2]), Finset.sum_const,
      smul_eq_mul]
  have h1 : ∀ b ∈ T, 1 ≤ (Finset.univ.filter fun k => a k = b).card := by
    intro b hb
    obtain ⟨k, hk⟩ := hsurj b hb
    exact Finset.card_pos.2 ⟨k, by simp [hk]⟩
  have h2 : 2 ≤ (Finset.univ.filter fun k => a k = a i).card := by
    have : {i, j} ⊆ Finset.univ.filter fun k => a k = a i := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> simp [hij]
    have := Finset.card_le_card this
    rwa [Finset.card_pair hne] at this
  have hgt : ∑ b ∈ T, g b < ∑ b ∈ T, (Finset.univ.filter fun k => a k = b).card * g b := by
    apply Finset.sum_lt_sum
    · intro b hb
      exact Nat.le_mul_of_pos_left _ (h1 b hb)
    · refine ⟨a i, hmap i, ?_⟩
      have := hpos (a i) (hmap i)
      nlinarith
  omega

end GI.Proved
