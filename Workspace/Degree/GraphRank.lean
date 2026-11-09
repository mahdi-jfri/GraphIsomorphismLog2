module

public import Workspace.Degree.GraphTab

/-!
# Matching the levels of two graphs

Given level functions `lX` and `lY`, the map `rhoN lX lY` sends the `c`-th point of level `t` of
`X` (in the order of `Fin n`) to the `c`-th point of level `t` of `Y`.

* `rhoN_lt`: if some permutation `g` has `lY (g u) = lX u` for all `u`, every value is a point.
* `rhoPerm`: if every value is a point, the map is a permutation that keeps levels.
-/

@[expose] public section

namespace GI.Degree

open Equiv

variable {n : ℕ}

open Classical in
/-- The number of points of the level of `u` before `u`. -/
noncomputable def idx (ℓ : Fin n → ℕ) (u : Fin n) : ℕ :=
  ((List.finRange n).filter fun u' => decide (ℓ u' = ℓ u ∧ u' < u)).length

open Classical in
/-- The image of `u`, or `n`. -/
noncomputable def rhoN (lX lY : Fin n → ℕ) (u : Fin n) : ℕ :=
  (List.finRange n).findIdx fun y => decide (lY y = lX u ∧ idx lY y = idx lX u)

open Classical in
theorem idx_eq_card (ℓ : Fin n → ℕ) (u : Fin n) :
    idx ℓ u = (Finset.univ.filter fun u' => ℓ u' = ℓ u ∧ u' < u).card := by
  rw [idx, ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _), List.toFinset_filter]
  congr 1
  ext x
  simp

theorem idx_lt_of_lt {ℓ : Fin n → ℕ} {a b : Fin n} (hl : ℓ a = ℓ b) (hab : a < b) :
    idx ℓ a < idx ℓ b := by
  classical
  rw [idx_eq_card, idx_eq_card]
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1.trans hl, hx.2.trans hab⟩
  · have := h (show a ∈ Finset.univ.filter fun u' => ℓ u' = ℓ b ∧ u' < b by simp [hl, hab])
    simp at this

theorem idx_inj {ℓ : Fin n → ℕ} {a b : Fin n} (hl : ℓ a = ℓ b) (hi : idx ℓ a = idx ℓ b) :
    a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hi (idx_lt_of_lt hl h).ne
  · exact h
  · exact absurd hi (idx_lt_of_lt hl.symm h).ne'

theorem idx_lt_card (ℓ : Fin n → ℕ) (u : Fin n) :
    idx ℓ u < (Finset.univ.filter fun u' => ℓ u' = ℓ u).card := by
  classical
  rw [idx_eq_card]
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.1
  · have := h (show u ∈ Finset.univ.filter fun u' => ℓ u' = ℓ u by simp)
    simp at this

/-- Every number below the size of a level is the index of a point of the level. -/
theorem exists_idx (ℓ : Fin n → ℕ) (t : ℕ) {c : ℕ}
    (hc : c < (Finset.univ.filter fun u' => ℓ u' = t).card) :
    ∃ u, ℓ u = t ∧ idx ℓ u = c := by
  classical
  set N := (Finset.univ.filter fun u' => ℓ u' = t).card with hN
  let f : {u // ℓ u = t} → Fin N := fun x => ⟨idx ℓ x.1, by
    have := idx_lt_card ℓ x.1
    rwa [x.2] at this⟩
  have hf : Function.Injective f := fun x y h => by
    have : idx ℓ x.1 = idx ℓ y.1 := congrArg Fin.val h
    exact Subtype.ext (idx_inj (x.2.trans y.2.symm) this)
  have hcard : Fintype.card {u // ℓ u = t} = Fintype.card (Fin N) := by
    rw [Fintype.card_fin, Fintype.card_subtype]
  obtain ⟨x, hx⟩ := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩).2 ⟨c, hc⟩
  exact ⟨x.1, x.2, congrArg Fin.val hx⟩

/-- **A map that keeps levels makes every value a point.** -/
theorem rhoN_lt {lX lY : Fin n → ℕ} {g : Perm (Fin n)} (hg : ∀ u, lY (g u) = lX u) (u : Fin n) :
    rhoN lX lY u < n := by
  classical
  have hc : (Finset.univ.filter fun y => lY y = lX u).card =
      (Finset.univ.filter fun u' => lX u' = lX u).card := by
    refine (Finset.card_bij (fun y _ => g.symm y) (fun y hy => ?_) (fun a _ b _ h => g.symm.injective h)
      (fun x hx => ⟨g x, ?_, by simp⟩))
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [← hg, apply_symm_apply, hy]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [hg, hx]
  have h1 := idx_lt_card lX u
  rw [← hc] at h1
  obtain ⟨y, hy1, hy2⟩ := exists_idx lY (lX u) h1
  obtain ⟨hi, -⟩ := findIdx_finRange (fun y => lY y = lX u ∧ idx lY y = idx lX u) ⟨y, hy1, hy2⟩
  unfold rhoN
  convert hi

/-- **The levels match by a permutation.** -/
theorem exists_rhoPerm {lX lY : Fin n → ℕ} (h : ∀ u, rhoN lX lY u < n) :
    ∃ ρ : Perm (Fin n), ∀ u, (ρ u : ℕ) = rhoN lX lY u ∧ lY (ρ u) = lX u := by
  classical
  have hq : ∀ u, lY ⟨_, h u⟩ = lX u ∧ idx lY ⟨_, h u⟩ = idx lX u := fun u => by
    have hu : rhoN lX lY u < (List.finRange n).length := by
      simpa only [List.length_finRange] using h u
    have := List.findIdx_getElem (xs := List.finRange n) (w := hu)
    simp only [decide_eq_true_eq] at this
    have e : (List.finRange n)[rhoN lX lY u]'hu = ⟨_, h u⟩ := by
      ext
      simp
    rw [← e]
    exact this
  let f : Fin n → Fin n := fun u => ⟨_, h u⟩
  have hf : Function.Injective f := fun a b hab => by
    have h1 := (hq a).1
    have h2 := (hq b).1
    have h3 := (hq a).2
    have h4 := (hq b).2
    change f a = f b at hab
    have e1 : lX a = lX b := by
      rw [← h1, ← h2]
      exact congrArg lY hab
    have e2 : idx lX a = idx lX b := by
      rw [← h3, ← h4]
      exact congrArg (idx lY) hab
    exact idx_inj e1 e2
  let ρ := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
  exact ⟨ρ, fun u => ⟨rfl, (hq u).1⟩⟩

end GI.Degree
