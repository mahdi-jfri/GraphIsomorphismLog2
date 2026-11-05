module

public import Workspace.Impl.AggRectRepGens

@[expose] public section

/-!
# The support of a point-stabilizer image

Corollary A.25 and Lemma A.26 find the kernel-orbit quotient from one point: "Fix `x ∈ Ω` and
compute `P = φ(G_x)`. … In the nontrivial proper cases its support is either its unique fixed
point, its two fixed points, or its unique orbit of size two; the other orbit has size `m - 1` or
`m - 2`. These data identify the case in polynomial time."

This file proves the facts about `P` that the program reads. For a subgroup `P` of the label
permutations, the *small points* are the labels whose `P`-orbit has at most two points, in
increasing order (`rcRSmall`). For the three stabilizers in `Alt(Γ)` (`q ≥ 8`):

* the pointwise stabilizer of `a ≠ b` (ordered pairs): the small points are `a, b`, and they lie
  in different orbits;
* the setwise stabilizer of `{a, b}` (unordered pairs): the small points are `a, b`, and they lie
  in one orbit;
* the stabilizer of `a` (single labels): the only small point is `a`.

The other orbits are large because `Alt(Γ)` moves any label outside a set `F` with
`|F| + 4 ≤ q` to any other while fixing `F` pointwise (`rcR_alt_move`).
-/

namespace GI.Impl

open Equiv Equiv.Perm

variable {q : ℕ}

/-! ### Moves in the alternating group -/

/-- `Alt(Γ)` moves `c` to `d` while fixing `F` pointwise, for `c, d ∉ F` and `|F| + 4 ≤ q`. -/
theorem rcR_alt_move (F : Finset (Fin q)) (hF : F.card + 4 ≤ q) {c d : Fin q} (hc : c ∉ F)
    (hd : d ∉ F) :
    ∃ σ ∈ alternatingGroup (Fin q), (∀ x ∈ F, σ x = x) ∧ σ c = d := by
  classical
  rcases eq_or_ne c d with rfl | hcd
  · exact ⟨1, Subgroup.one_mem _, fun _ _ => rfl, rfl⟩
  obtain ⟨u, hu⟩ := GI.NaturalGiant.exists_outside (insert c (insert d F)) (by
    have := Finset.card_insert_le c (insert d F)
    have := Finset.card_insert_le d F
    simp only [Fintype.card_fin]; omega)
  obtain ⟨v, hv⟩ := GI.NaturalGiant.exists_outside (insert u (insert c (insert d F))) (by
    have := Finset.card_insert_le u (insert c (insert d F))
    have := Finset.card_insert_le c (insert d F)
    have := Finset.card_insert_le d F
    simp only [Fintype.card_fin]; omega)
  simp only [Finset.mem_insert, not_or] at hu hv
  refine ⟨swap u v * swap c d, ?_, fun x hx => ?_, ?_⟩
  · rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (Ne.symm hv.1), sign_swap hcd]; rfl
  · have hxc : x ≠ c := fun h => hc (h ▸ hx)
    have hxd : x ≠ d := fun h => hd (h ▸ hx)
    have hxu : x ≠ u := fun h => hu.2.2 (h ▸ hx)
    have hxv : x ≠ v := fun h => hv.2.2.2 (h ▸ hx)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxc hxd, swap_apply_of_ne_of_ne hxu hxv]
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hu.2.1)
      (Ne.symm hv.2.2.1)]

/-- `Alt(Γ)` swaps two labels `a ≠ b` (for `q ≥ 4`). -/
theorem rcR_alt_swap {a b : Fin q} (hab : a ≠ b) (hq : 4 ≤ q) :
    ∃ σ ∈ alternatingGroup (Fin q), σ a = b ∧ σ b = a := by
  classical
  obtain ⟨u, hu⟩ := GI.NaturalGiant.exists_outside ({a, b} : Finset (Fin q)) (by
    have := Finset.card_le_two (a := a) (b := b); simp only [Fintype.card_fin]; omega)
  obtain ⟨v, hv⟩ := GI.NaturalGiant.exists_outside ({u, a, b} : Finset (Fin q)) (by
    have := Finset.card_le_three (a := u) (b := a) (c := b); simp only [Fintype.card_fin]; omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu hv
  refine ⟨swap u v * swap a b, ?_, ?_, ?_⟩
  · rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (Ne.symm hv.1), sign_swap hab]; rfl
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hu.2) (Ne.symm hv.2.2)]
  · rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm hu.1) (Ne.symm hv.2.1)]

/-! ### Orbits and small points -/

open Classical in
/-- The orbit of a label under a group of label permutations. -/
noncomputable def rcROrb (P : Subgroup (Perm (Fin q))) (c : Fin q) : Finset (Fin q) :=
  Finset.univ.filter fun d => ∃ σ ∈ P, σ c = d

theorem rcR_mem_orb {P : Subgroup (Perm (Fin q))} {c d : Fin q} :
    d ∈ rcROrb P c ↔ ∃ σ ∈ P, σ c = d := by
  classical
  simp [rcROrb]

open Classical in
/-- **The small points**: the labels whose orbit has at most two points, in increasing order. -/
noncomputable def rcRSmall (P : Subgroup (Perm (Fin q))) : List (Fin q) :=
  (List.finRange q).filter fun c => decide ((rcROrb P c).card ≤ 2)

theorem rcR_mem_small {P : Subgroup (Perm (Fin q))} {c : Fin q} :
    c ∈ rcRSmall P ↔ (rcROrb P c).card ≤ 2 := by
  classical
  simp [rcRSmall]

/-- A label outside `F` has an orbit of at least `q - |F|` points, if the group contains the
elements of `Alt(Γ)` that fix `F` pointwise. -/
theorem rcR_orb_large (P : Subgroup (Perm (Fin q))) (F : Finset (Fin q)) (hF : F.card + 4 ≤ q)
    (hP : ∀ σ ∈ alternatingGroup (Fin q), (∀ x ∈ F, σ x = x) → σ ∈ P) {c : Fin q} (hc : c ∉ F) :
    2 < (rcROrb P c).card := by
  classical
  have hsub : Finset.univ \ F ⊆ rcROrb P c := by
    intro d hd
    rw [Finset.mem_sdiff] at hd
    obtain ⟨σ, hσ, hfix, hσc⟩ := rcR_alt_move F hF hc hd.2
    exact rcR_mem_orb.2 ⟨σ, hP σ hσ hfix, hσc⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ F), Finset.card_univ, Fintype.card_fin]
    at h1
  omega

theorem rcR_filter_pw (p : Fin q → Bool) : ((List.finRange q).filter p).Pairwise (· < ·) :=
  (List.sortedLT_iff_pairwise.1 (List.sortedLT_finRange q)).filter _

/-- A list of labels in increasing order with exactly the members `a < b` is `[a, b]`. -/
theorem rcR_filter_two {p : Fin q → Bool} {a b : Fin q} (hab : a < b)
    (hp : ∀ c, p c = true ↔ c = a ∨ c = b) : (List.finRange q).filter p = [a, b] := by
  have hs2 : [a, b].Pairwise (· < ·) := by simp [hab]
  refine List.Pairwise.eq_of_mem_iff (rcR_filter_pw p) hs2 fun c => ?_
  simp [hp]

/-- A list of labels in increasing order with exactly the member `a` is `[a]`. -/
theorem rcR_filter_one {p : Fin q → Bool} {a : Fin q} (hp : ∀ c, p c = true ↔ c = a) :
    (List.finRange q).filter p = [a] := by
  have hs2 : [a].Pairwise (· < ·) := by simp
  refine List.Pairwise.eq_of_mem_iff (rcR_filter_pw p) hs2 fun c => ?_
  simp [hp]

/-- The increasing list of two distinct labels. -/
def rcRPair (a b : Fin q) : List (Fin q) := if a < b then [a, b] else [b, a]

theorem rcR_filter_pair {p : Fin q → Bool} {a b : Fin q} (hab : a ≠ b)
    (hp : ∀ c, p c = true ↔ c = a ∨ c = b) : (List.finRange q).filter p = rcRPair a b := by
  unfold rcRPair
  split_ifs with h
  · exact rcR_filter_two h hp
  · exact rcR_filter_two (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hab)) fun c => by
      rw [hp, or_comm]

section Stabilizers

variable {a b : Fin q}

/-- The pointwise stabilizer of `a, b` in `Alt(Γ)`, as label permutations. -/
def rcRPt (a b : Fin q) : Subgroup (Perm (Fin q)) where
  carrier := {σ | σ ∈ alternatingGroup (Fin q) ∧ σ a = a ∧ σ b = b}
  one_mem' := ⟨Subgroup.one_mem _, rfl, rfl⟩
  mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, by
    simp [Perm.mul_apply, hx.2.1, hy.2.1], by simp [Perm.mul_apply, hx.2.2, hy.2.2]⟩
  inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, by
    rw [Perm.inv_eq_iff_eq]; exact hx.2.1.symm, by rw [Perm.inv_eq_iff_eq]; exact hx.2.2.symm⟩

/-- The setwise stabilizer of `{a, b}` in `Alt(Γ)`, as label permutations. -/
def rcRSet (a b : Fin q) : Subgroup (Perm (Fin q)) where
  carrier := {σ | σ ∈ alternatingGroup (Fin q) ∧ ((σ a = a ∧ σ b = b) ∨ (σ a = b ∧ σ b = a))}
  one_mem' := ⟨Subgroup.one_mem _, Or.inl ⟨rfl, rfl⟩⟩
  mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, by
    simp only [Perm.mul_apply]
    rcases hy.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hx.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      simp_all⟩
  inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, by
    simp only [Perm.inv_eq_iff_eq]
    rcases hx.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩⟩

/-- The stabilizer of `a` in `Alt(Γ)`, as label permutations. -/
def rcROne (a : Fin q) : Subgroup (Perm (Fin q)) where
  carrier := {σ | σ ∈ alternatingGroup (Fin q) ∧ σ a = a}
  one_mem' := ⟨Subgroup.one_mem _, rfl⟩
  mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, by
    simp [Perm.mul_apply, hx.2, hy.2]⟩
  inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, by
    rw [Perm.inv_eq_iff_eq]; exact hx.2.symm⟩

theorem rcR_mem_pt {σ : Perm (Fin q)} :
    σ ∈ rcRPt a b ↔ σ ∈ alternatingGroup (Fin q) ∧ σ a = a ∧ σ b = b := Iff.rfl

theorem rcR_mem_set {σ : Perm (Fin q)} :
    σ ∈ rcRSet a b ↔ σ ∈ alternatingGroup (Fin q) ∧ ((σ a = a ∧ σ b = b) ∨ (σ a = b ∧ σ b = a)) :=
  Iff.rfl

theorem rcR_mem_one {σ : Perm (Fin q)} :
    σ ∈ rcROne a ↔ σ ∈ alternatingGroup (Fin q) ∧ σ a = a := Iff.rfl

theorem rcR_orb_fixed {P : Subgroup (Perm (Fin q))} {c : Fin q} (h : ∀ σ ∈ P, σ c = c) :
    rcROrb P c = {c} := by
  ext d
  rw [rcR_mem_orb, Finset.mem_singleton]
  constructor
  · rintro ⟨σ, hσ, rfl⟩; exact h σ hσ
  · rintro rfl; exact ⟨1, P.one_mem, rfl⟩

/-- **The small points of the pointwise stabilizer** of `a ≠ b` are `a, b`. -/
theorem rcR_small_pt (hab : a ≠ b) (hq : 8 ≤ q) : rcRSmall (rcRPt a b) = rcRPair a b := by
  classical
  refine rcR_filter_pair hab fun c => ?_
  simp only [decide_eq_true_eq]
  constructor
  · intro hc
    by_contra hne
    push Not at hne
    refine absurd hc (not_le.2 (rcR_orb_large (rcRPt a b) {a, b} (by
      have := Finset.card_le_two (a := a) (b := b); omega) (fun σ hσ hfix => rcR_mem_pt.2 ⟨hσ, hfix a (by simp),
        hfix b (by simp)⟩) (by simp [hne.1, hne.2])))
  · rintro (rfl | rfl)
    · rw [rcR_orb_fixed fun σ hσ => (rcR_mem_pt.1 hσ).2.1]; simp
    · rw [rcR_orb_fixed fun σ hσ => (rcR_mem_pt.1 hσ).2.2]; simp

/-- The orbit of `a` under the setwise stabilizer of `{a, b}` is `{a, b}`. -/
theorem rcR_orb_set (hab : a ≠ b) (hq : 4 ≤ q) : rcROrb (rcRSet a b) a = {a, b} := by
  ext d
  rw [rcR_mem_orb, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rcases hσ.2 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro (rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, rfl⟩
    · obtain ⟨σ, hσ, h1, h2⟩ := rcR_alt_swap hab hq
      exact ⟨σ, ⟨hσ, Or.inr ⟨h1, h2⟩⟩, h1⟩

/-- **The small points of the setwise stabilizer** of `{a, b}` are `a, b`. -/
theorem rcR_small_set (hab : a ≠ b) (hq : 8 ≤ q) : rcRSmall (rcRSet a b) = rcRPair a b := by
  classical
  refine rcR_filter_pair hab fun c => ?_
  simp only [decide_eq_true_eq]
  constructor
  · intro hc
    by_contra hne
    push Not at hne
    refine absurd hc (not_le.2 (rcR_orb_large (rcRSet a b) {a, b} (by
      have := Finset.card_le_two (a := a) (b := b); omega) (fun σ hσ hfix => rcR_mem_set.2 ⟨hσ, Or.inl
        ⟨hfix a (by simp), hfix b (by simp)⟩⟩) (by simp [hne.1, hne.2])))
  · rintro (rfl | rfl)
    · rw [rcR_orb_set hab (by omega), Finset.card_pair hab]
    · have e : rcRSet c a = rcRSet a c := by
        ext σ
        show σ ∈ alternatingGroup (Fin q) ∧ _ ↔ σ ∈ alternatingGroup (Fin q) ∧ _
        constructor <;> rintro ⟨h0, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
        all_goals first
          | exact ⟨h0, Or.inl ⟨h2, h1⟩⟩
          | exact ⟨h0, Or.inr ⟨h2, h1⟩⟩
      rw [← e, rcR_orb_set (Ne.symm hab) (by omega), Finset.card_pair (Ne.symm hab)]

/-- **The small point of the stabilizer** of `a` is `a`. -/
theorem rcR_small_one (hq : 8 ≤ q) : rcRSmall (rcROne a) = [a] := by
  classical
  refine rcR_filter_one fun c => ?_
  simp only [decide_eq_true_eq]
  constructor
  · intro hc
    by_contra hne
    refine absurd hc (not_le.2 (rcR_orb_large (rcROne a) {a} (by simp; omega)
      (fun σ hσ hfix => rcR_mem_one.2 ⟨hσ, hfix a (by simp)⟩) (by simp [hne])))
  · rintro rfl
    rw [rcR_orb_fixed fun σ hσ => (rcR_mem_one.1 hσ).2]; simp

/-- Under the pointwise stabilizer, `b` is not in the orbit of `a`. -/
theorem rcR_pt_not_mem (hab : a ≠ b) : b ∉ rcROrb (rcRPt a b) a := by
  rw [rcR_orb_fixed fun σ hσ => (rcR_mem_pt.1 hσ).2.1, Finset.mem_singleton]
  exact Ne.symm hab

/-- Under the setwise stabilizer, `b` is in the orbit of `a`. -/
theorem rcR_set_mem (hab : a ≠ b) (hq : 4 ≤ q) : b ∈ rcROrb (rcRSet a b) a := by
  rw [rcR_orb_set hab hq]; simp

end Stabilizers

end GI.Impl
