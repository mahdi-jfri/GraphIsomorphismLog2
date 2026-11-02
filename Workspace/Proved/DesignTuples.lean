import Workspace.Cited.CoherentConfig
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Tuples and counts for the Design Lemma

Two kinds of facts used in the proof of the Design Lemma (`Workspace/Proved/DesignLemma.lean`).

* Identities between the padded tuples `(x, z, …, z)` and `(x, z₁, z₂, …, z₂)` of
  `GI.Cited.padTuple` and `GI.Cited.padTuple₂`.
* `designCount`: in a coherent configuration, tuples of the same color give the same counts of
  points `z` that satisfy two conditions, each on the color of a tuple obtained by putting `z`
  at one position and then reordering by a map `τ`. This is how coherence is used for the
  design counts in the large clique lemma.
-/

namespace GI.Proved

open Finset GI.Cited

variable {n k ℓ : ℕ}

/-! ### Padded tuples -/

theorem designPad₂_self (x : Fin ℓ → Fin n) (p : Fin n) :
    (padTuple₂ x p p : Fin k → Fin n) = padTuple x p := by
  funext i
  simp only [padTuple, padTuple₂]
  split_ifs <;> rfl

/-- When `ℓ + 1 = k`, the tuple `(x, a, b, …, b)` has no `b` entry. -/
theorem designPad₂_full (x : Fin ℓ → Fin n) (a b : Fin n) (h : k ≤ ℓ + 1) :
    (padTuple₂ x a b : Fin k → Fin n) = padTuple x a := by
  funext i
  have := i.isLt
  simp only [padTuple, padTuple₂]
  split_ifs <;> first | rfl | omega

/-- Putting `z` at position `ℓ` of `(x, q, …, q)` gives `(x, z, q, …, q)`. -/
theorem designUpdate_pad (x : Fin ℓ → Fin n) (q z : Fin n) (h : ℓ < k) :
    Function.update (padTuple x q : Fin k → Fin n) ⟨ℓ, h⟩ z = padTuple₂ x z q := by
  funext i
  simp only [Function.update_apply, padTuple, padTuple₂, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/-- Putting `z` at position `ℓ` of `(x, q, q', …, q')` gives `(x, z, q', …, q')`. -/
theorem designUpdate_pad₂ (x : Fin ℓ → Fin n) (q q' z : Fin n) (h : ℓ < k) :
    Function.update (padTuple₂ x q q' : Fin k → Fin n) ⟨ℓ, h⟩ z = padTuple₂ x z q' := by
  funext i
  simp only [Function.update_apply, padTuple₂, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/-- The reordering that reads `(x, q, z, q', …, q')` as `(x, z, q, …, q)`: it fixes the
first `ℓ` positions, sends position `ℓ` to `ℓ + 1` and every later position to `ℓ`. -/
def designSwapMap (ℓ : ℕ) (h : ℓ + 1 < k) : Fin k → Fin k := fun i =>
  if i.val < ℓ then i else if i.val = ℓ then ⟨ℓ + 1, h⟩ else ⟨ℓ, by omega⟩

/-- Putting `z` at position `ℓ + 1` of `(x, q, q', …, q')` and reordering by
`designSwapMap` gives `(x, z, q, …, q)`. -/
theorem designUpdate_pad₂_succ (x : Fin ℓ → Fin n) (q q' z : Fin n) (h : ℓ + 1 < k) :
    Function.update (padTuple₂ x q q' : Fin k → Fin n) ⟨ℓ + 1, h⟩ z ∘ designSwapMap ℓ h =
      padTuple₂ x z q := by
  funext i
  simp only [Function.comp_apply, designSwapMap]
  by_cases h1 : i.val < ℓ
  · rw [if_pos h1, Function.update_of_ne (fun e => by
      have := congrArg Fin.val e; simp only at this; omega)]
    simp only [padTuple₂, dif_pos h1]
  · rw [if_neg h1]
    by_cases h2 : i.val = ℓ
    · rw [if_pos h2, Function.update_self]
      simp only [padTuple₂, dif_neg h1, if_pos h2]
    · rw [if_neg h2, Function.update_of_ne (fun e => by
        have := congrArg Fin.val e; simp only at this; omega)]
      simp [padTuple₂, h1, h2]

/-- The reordering that keeps the first `ℓ` positions and sends every later position to `ℓ`. -/
def designProj (ℓ : ℕ) (h : ℓ < k) : Fin k → Fin k := fun i =>
  if i.val < ℓ then i else ⟨ℓ, h⟩

/-- Reading `(x, p, q, …, q)` by `designProj` gives `(x, p, …, p)`. -/
theorem designPad₂_proj (x : Fin ℓ → Fin n) (p q : Fin n) (h : ℓ < k) :
    (padTuple₂ x p q : Fin k → Fin n) ∘ designProj ℓ h = padTuple x p := by
  funext i
  simp only [Function.comp_apply, designProj]
  by_cases h1 : i.val < ℓ
  · simp only [if_pos h1, padTuple, padTuple₂, dif_pos h1]
  · simp [h1, padTuple, padTuple₂]

/-- `(x, z₁, z₂, …, z₂)` for `x : Fin (ℓ + 1) → Fin n` written as `(init x, last x, …)`. -/
theorem designPad_snoc (x : Fin ℓ → Fin n) (z w : Fin n) :
    (padTuple (Fin.snoc (α := fun _ => Fin n) x z) w : Fin k → Fin n) = padTuple₂ x z w := by
  funext i
  simp only [padTuple, padTuple₂]
  by_cases h1 : i.val < ℓ
  · have h2 : i.val < ℓ + 1 := by omega
    rw [dif_pos h2, dif_pos h1]
    have : (⟨i.val, h2⟩ : Fin (ℓ + 1)) = Fin.castSucc ⟨i.val, h1⟩ := rfl
    rw [this, Fin.snoc_castSucc]
  · rw [dif_neg h1]
    by_cases h2 : i.val = ℓ
    · have h3 : i.val < ℓ + 1 := by omega
      rw [dif_pos h3, if_pos h2]
      have : (⟨i.val, h3⟩ : Fin (ℓ + 1)) = Fin.last ℓ := Fin.ext h2
      rw [this, Fin.snoc_last]
    · have h3 : ¬ i.val < ℓ + 1 := by omega
      rw [dif_neg h3, if_neg h2]

/-- A transposition of two points that `x` avoids swaps the last two entries. -/
theorem designSwap_pad₂ (x : Fin ℓ → Fin n) (u v : Fin n) (hx : ∀ i, x i ≠ u ∧ x i ≠ v) :
    Equiv.swap u v ∘ (padTuple₂ x u v : Fin k → Fin n) = padTuple₂ x v u := by
  funext i
  simp only [Function.comp_apply, padTuple₂]
  split_ifs with h1
  · exact Equiv.swap_apply_of_ne_of_ne (hx _).1 (hx _).2
  · exact Equiv.swap_apply_left u v
  · exact Equiv.swap_apply_right u v

/-! ### Counts in a coherent configuration -/

variable {c : (Fin k → Fin n) → ℕ}

/-- Coherence for an arbitrary condition on the vector of colors `i ↦ c(t_i(z))`. -/
theorem designCountP (hcoh : IsCoherent c) {t t' : Fin k → Fin n} (h : c t = c t')
    (P : (Fin k → ℕ) → Prop) [DecidablePred P] :
    (univ.filter fun z => P fun i => c (Function.update t i z)).card =
      (univ.filter fun z => P fun i => c (Function.update t' i z)).card := by
  classical
  set f : Fin n → Fin k → ℕ := fun z i => c (Function.update t i z) with hf
  set f' : Fin n → Fin k → ℕ := fun z i => c (Function.update t' i z) with hf'
  have key : ∀ b, (univ.filter fun z => f z = b).card = (univ.filter fun z => f' z = b).card := by
    intro b
    have := hcoh t t' h b
    simpa only [hf, hf', funext_iff] using this
  set K := (univ.image f ∪ univ.image f').filter P
  have hfib : ∀ g : Fin n → Fin k → ℕ, (∀ z, g z ∈ univ.image f ∪ univ.image f') →
      (univ.filter fun z => P (g z)).card =
        ∑ b ∈ K, (univ.filter fun z => g z = b).card := by
    intro g hg
    rw [card_eq_sum_card_fiberwise (f := g) (t := K)]
    · refine sum_congr rfl fun b hb => ?_
      have hPb := (mem_filter.mp hb).2
      congr 1
      ext z
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro e
        exact ⟨e ▸ hPb, e⟩
    · intro z hz
      exact mem_filter.mpr ⟨hg z, (mem_filter.mp hz).2⟩
  rw [hfib f (fun z => mem_union_left _ (mem_image_of_mem f (mem_univ z))),
    hfib f' (fun z => mem_union_right _ (mem_image_of_mem f' (mem_univ z)))]
  exact sum_congr rfl fun b _ => key b

/-- **Two-condition counts.** If `c t = c t'`, then the number of `z` with
`c(t_{i₁}(z) ∘ τ₁) = j₁` and `c(t_{i₂}(z) ∘ τ₂) = j₂` is the same for `t` and `t'`. Here
`t_i(z)` is `t` with its `i`-th entry replaced by `z`. -/
theorem designCount (hconf : IsConfiguration c) (hcoh : IsCoherent c)
    {t t' : Fin k → Fin n} (h : c t = c t') (i₁ i₂ : Fin k) (τ₁ τ₂ : Fin k → Fin k)
    (j₁ j₂ : ℕ) :
    (univ.filter fun z => c (Function.update t i₁ z ∘ τ₁) = j₁ ∧
        c (Function.update t i₂ z ∘ τ₂) = j₂).card =
      (univ.filter fun z => c (Function.update t' i₁ z ∘ τ₁) = j₁ ∧
        c (Function.update t' i₂ z ∘ τ₂) = j₂).card := by
  classical
  let P : (Fin k → ℕ) → Prop := fun κ =>
    (∃ s, c s = κ i₁ ∧ c (s ∘ τ₁) = j₁) ∧ (∃ s, c s = κ i₂ ∧ c (s ∘ τ₂) = j₂)
  have hP : ∀ t : Fin k → Fin n,
      (univ.filter fun z => c (Function.update t i₁ z ∘ τ₁) = j₁ ∧
        c (Function.update t i₂ z ∘ τ₂) = j₂) =
      univ.filter fun z => P fun i => c (Function.update t i z) := by
    intro t
    ext z
    simp only [mem_filter, mem_univ, true_and, P]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨_, rfl, h1⟩, ⟨_, rfl, h2⟩⟩
    · rintro ⟨⟨s₁, e₁, h1⟩, ⟨s₂, e₂, h2⟩⟩
      exact ⟨(hconf.2 _ _ e₁ τ₁).symm.trans h1, (hconf.2 _ _ e₂ τ₂).symm.trans h2⟩
  rw [hP t, hP t']
  exact designCountP hcoh h P

end GI.Proved
