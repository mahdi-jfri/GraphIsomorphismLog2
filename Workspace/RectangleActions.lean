module

public import Workspace.PairActions

@[expose] public section

namespace GI.Rectangle

open Equiv Equiv.Perm
open scoped Pointwise

variable {α : Type*} [Fintype α] [DecidableEq α]

def sides (W R : Finset α) : Subgroup (Perm α) :=
  MulAction.stabilizer (Perm α) (W : Set α) ⊓ MulAction.stabilizer (Perm α) (R : Set α)

def permitted (W R : Finset α) : Subgroup (alternatingGroup α) :=
  (sides W R).comap (alternatingGroup α).subtype

omit [Fintype α] [DecidableEq α] in
theorem cross_ne {W R : Finset α} (hd : Disjoint W R) {a b : α}
    (ha : a ∈ W) (hb : b ∈ R) : a ≠ b := by
  intro h
  subst b
  exact Finset.disjoint_left.mp hd ha hb

omit [Fintype α] in
theorem swap_left_mem {W R : Finset α} (hd : Disjoint W R) {a b : α}
    (ha : a ∈ W) (hb : b ∈ W) : swap a b ∈ sides W R := by
  constructor
  · exact Equiv.swap_mem_stabilizer.mpr (by simp [ha, hb])
  · have haR : a ∉ R := fun h => Finset.disjoint_left.mp hd ha h
    have hbR : b ∉ R := fun h => Finset.disjoint_left.mp hd hb h
    exact Equiv.swap_mem_stabilizer.mpr (by simp [haR, hbR])

omit [Fintype α] in
theorem swap_right_mem {W R : Finset α} (hd : Disjoint W R) {a b : α}
    (ha : a ∈ R) (hb : b ∈ R) : swap a b ∈ sides W R := by
  have h := swap_left_mem hd.symm ha hb
  exact ⟨h.2, h.1⟩

/-- Actual even side-preserving permutations act transitively on the
rectangle. Parity is corrected inside W while fixing the prescribed image. -/
theorem exists_permitted_pair_map {W R : Finset α} (hd : Disjoint W R)
    (hW : 3 ≤ W.card) {a a' b b' : α}
    (ha : a ∈ W) (ha' : a' ∈ W) (hb : b ∈ R) (hb' : b' ∈ R) :
    ∃ g : permitted W R, (g.val : Perm α) a = a' ∧ (g.val : Perm α) b = b' := by
  let t : Perm α := swap a a' * swap b b'
  have ht : t ∈ sides W R := (sides W R).mul_mem
    (swap_left_mem hd ha ha') (swap_right_mem hd hb hb')
  have hta : t a = a' := by
    change swap a a' (swap b b' a) = a'
    rw [swap_apply_of_ne_of_ne (cross_ne hd ha hb) (cross_ne hd ha hb'), swap_apply_left]
  have htb : t b = b' := by
    change swap a a' (swap b b' b) = b'
    rw [swap_apply_left,
      swap_apply_of_ne_of_ne (Ne.symm (cross_ne hd ha hb')) (Ne.symm (cross_ne hd ha' hb'))]
  have htwo : 1 < (W.erase a').card := by
    rw [Finset.card_erase_of_mem ha']
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp htwo
  simp only [Finset.mem_erase] at hu hv
  by_cases heven : sign t = 1
  · exact ⟨⟨⟨t, heven⟩, ht⟩, hta, htb⟩
  · have hsign : sign t = -1 := (Int.units_eq_one_or (sign t)).resolve_left heven
    have hc : swap u v * t ∈ alternatingGroup α := by
      rw [mem_alternatingGroup, sign_mul, sign_swap huv, hsign]
      simp
    refine ⟨⟨⟨swap u v * t, hc⟩,
      (sides W R).mul_mem (swap_left_mem hd hu.2 hv.2) ht⟩, ?_, ?_⟩
    · change swap u v (t a) = a'
      rw [hta, swap_apply_of_ne_of_ne (Ne.symm hu.1) (Ne.symm hv.1)]
    · change swap u v (t b) = b'
      rw [htb, swap_apply_of_ne_of_ne
        (Ne.symm (cross_ne hd hu.2 hb')) (Ne.symm (cross_ne hd hv.2 hb'))]

theorem left_mem_iff (W R : Finset α) (g : permitted W R) (a : α) :
    (g.val : Perm α) a ∈ W ↔ a ∈ W := by
  have he : (g.val : Perm α) • (W : Set α) = W := g.property.1
  have hm : (g.val : Perm α) • a ∈ (g.val : Perm α) • (W : Set α) ↔ a ∈ (W : Set α) :=
    Set.smul_mem_smul_set_iff
  rw [he] at hm
  exact hm

theorem right_mem_iff (W R : Finset α) (g : permitted W R) (a : α) :
    (g.val : Perm α) a ∈ R ↔ a ∈ R := by
  have he : (g.val : Perm α) • (R : Set α) = R := g.property.2
  have hm : (g.val : Perm α) • a ∈ (g.val : Perm α) • (R : Set α) ↔ a ∈ (R : Set α) :=
    Set.smul_mem_smul_set_iff
  rw [he] at hm
  exact hm

end GI.Rectangle
