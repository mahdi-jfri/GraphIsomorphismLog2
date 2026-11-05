module

public import Mathlib

@[expose] public section

/-!
# The derived series of a solvable permutation group

`vsPDer C i` is the `i`-th derived subgroup of `C` (as subgroups of `Perm (Fin n)`). If `C` lies
in a solvable group, every nontrivial term has a proper derived subgroup, so the orders at least
halve, and the term with index `n² + 1` is trivial (`vsPDer_bot`).
-/

namespace GI.Proved

open Equiv

variable {n : ℕ}

/-- The derived series of `C`. -/
def vsPDer (C : Subgroup (Perm (Fin n))) : ℕ → Subgroup (Perm (Fin n))
  | 0 => C
  | i + 1 => ⁅vsPDer C i, vsPDer C i⁆

theorem vsPDer_succ (C : Subgroup (Perm (Fin n))) (i : ℕ) :
    vsPDer C (i + 1) = ⁅vsPDer C i, vsPDer C i⁆ := rfl

theorem vsP_commutator_le_self (K : Subgroup (Perm (Fin n))) : ⁅K, K⁆ ≤ K :=
  (Subgroup.commutator_le).2 fun a ha b hb => by
    rw [commutatorElement_def]; exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem vsPDer_succ_le (C : Subgroup (Perm (Fin n))) (i : ℕ) : vsPDer C (i + 1) ≤ vsPDer C i :=
  vsP_commutator_le_self _

theorem vsPDer_le (C : Subgroup (Perm (Fin n))) : ∀ i, vsPDer C i ≤ C
  | 0 => le_rfl
  | i + 1 => (vsPDer_succ_le C i).trans (vsPDer_le C i)

/-- In a solvable group, a nontrivial subgroup has a proper derived subgroup. -/
theorem vsP_commutator_lt {G K : Subgroup (Perm (Fin n))} (hG : Group.IsSolvable G) (hK : K ≤ G)
    (hne : K ≠ ⊥) : ⁅K, K⁆ < K := by
  set K' := K.subgroupOf G
  have hK' : K' ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hK hx⟩ : G) ∈ K' := by rw [Subgroup.mem_subgroupOf]; exact hx
    rw [h, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  have hlt := Group.IsSolvable.commutator_lt_of_ne_bot hK'
  have hmap : K'.map G.subtype = K := by
    rw [Subgroup.subgroupOf_map_subtype]; exact inf_eq_left.2 hK
  have := (Subgroup.map_lt_map_iff_of_injective G.subtype_injective).2 hlt
  rwa [Subgroup.map_commutator, hmap] at this

/-- The orders halve along the nontrivial part of the series. -/
theorem vsPDer_card {G C : Subgroup (Perm (Fin n))} (hG : Group.IsSolvable G) (hC : C ≤ G) :
    ∀ i, vsPDer C i ≠ ⊥ → Nat.card (vsPDer C i) * 2 ^ i ≤ Nat.card C
  | 0, _ => by simp [vsPDer]
  | i + 1, h => by
    have hi : vsPDer C i ≠ ⊥ := fun h0 => h (eq_bot_iff.2 (h0 ▸ vsPDer_succ_le C i))
    have ih := vsPDer_card hG hC i hi
    have hlt := vsP_commutator_lt hG ((vsPDer_le C i).trans hC) hi
    rw [← vsPDer_succ] at hlt
    have hidx : (vsPDer C (i + 1)).relIndex (vsPDer C i) ≠ 1 := by
      intro h1
      rw [Subgroup.relIndex_eq_one] at h1
      exact hlt.ne (le_antisymm (vsPDer_succ_le C i) h1)
    have hidx0 : (vsPDer C (i + 1)).relIndex (vsPDer C i) ≠ 0 := Subgroup.index_ne_zero_of_finite
    have e1 := Subgroup.relIndex_mul_index (vsPDer_succ_le C i)
    have e2 := Subgroup.card_mul_index (vsPDer C (i + 1))
    have e3 := Subgroup.card_mul_index (vsPDer C i)
    have hK0 : (vsPDer C i).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hmul : Nat.card (vsPDer C (i + 1)) * (vsPDer C (i + 1)).relIndex (vsPDer C i) =
        Nat.card (vsPDer C i) := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hK0)
      rw [mul_assoc, e1, e2, e3]
    have : Nat.card (vsPDer C (i + 1)) * 2 ≤ Nat.card (vsPDer C i) := by
      rw [← hmul]; exact Nat.mul_le_mul_left _ (by omega)
    calc Nat.card (vsPDer C (i + 1)) * 2 ^ (i + 1) = (Nat.card (vsPDer C (i + 1)) * 2) * 2 ^ i := by
          ring
      _ ≤ Nat.card (vsPDer C i) * 2 ^ i := Nat.mul_le_mul_right _ this
      _ ≤ Nat.card C := ih

/-- **The series ends.** -/
theorem vsPDer_bot {G C : Subgroup (Perm (Fin n))} (hG : Group.IsSolvable G) (hC : C ≤ G) :
    vsPDer C (n * n + 1) = ⊥ := by
  by_contra h
  have h1 := vsPDer_card hG hC _ h
  have h2 : 1 ≤ Nat.card (vsPDer C (n * n + 1)) := Nat.card_pos
  have h3 : Nat.card C ≤ n.factorial := by
    have := Subgroup.card_le_card_group C
    rwa [Nat.card_perm, Nat.card_fin] at this
  have h4 : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
  have h5 : n ^ n ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le n
  have h6 : (2 ^ n) ^ n = 2 ^ (n * n) := by rw [← pow_mul]
  have h7 : 2 ^ (n * n) < 2 ^ (n * n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have : 2 ^ (n * n + 1) ≤ Nat.card (vsPDer C (n * n + 1)) * 2 ^ (n * n + 1) :=
    Nat.le_mul_of_pos_left _ h2
  omega

theorem vsPDer_subgroupOf_succ {G C : Subgroup (Perm (Fin n))} (hC : C ≤ G) (i : ℕ) :
    (vsPDer C (i + 1)).subgroupOf G = ⁅(vsPDer C i).subgroupOf G, (vsPDer C i).subgroupOf G⁆ := by
  apply Subgroup.map_injective G.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left ((vsPDer_le C (i + 1)).trans hC), inf_of_le_left ((vsPDer_le C i).trans hC),
    vsPDer_succ]

theorem vsPDer_map_card {G C : Subgroup (Perm (Fin n))} {M : Type*} [Group M]
    (φ : G →* M) (hG : Group.IsSolvable φ.range) (hC : C ≤ G) :
    ∀ i, ((vsPDer C i).subgroupOf G).map φ.rangeRestrict ≠ ⊥ →
      Nat.card (((vsPDer C i).subgroupOf G).map φ.rangeRestrict) * 2 ^ i ≤
        Nat.card ((C.subgroupOf G).map φ.rangeRestrict)
  | 0, _ => by simp [vsPDer]
  | i + 1, h => by
    have : Finite φ.range := Set.Finite.to_subtype (Set.finite_range φ)
    let D := fun k => ((vsPDer C k).subgroupOf G).map φ.rangeRestrict
    have hle : D (i + 1) ≤ D i :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono G (vsPDer_succ_le C i))
    have hi : D i ≠ ⊥ := fun h0 => h (eq_bot_iff.2 (h0 ▸ hle))
    have ih := vsPDer_map_card φ hG hC i hi
    have hcomm : D (i + 1) = ⁅D i, D i⁆ := by
      dsimp only [D]
      rw [vsPDer_subgroupOf_succ hC i, Subgroup.map_commutator]
    have hlt : D (i + 1) < D i := by
      rw [hcomm]
      exact Group.IsSolvable.commutator_lt_of_ne_bot hi
    have hidx : (D (i + 1)).relIndex (D i) ≠ 1 := by
      intro h1
      rw [Subgroup.relIndex_eq_one] at h1
      exact hlt.ne (le_antisymm hle h1)
    have e1 := Subgroup.relIndex_mul_index hle
    have e2 := Subgroup.card_mul_index (D (i + 1))
    have e3 := Subgroup.card_mul_index (D i)
    have hK0 : (D i).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hmul : Nat.card (D (i + 1)) * (D (i + 1)).relIndex (D i) = Nat.card (D i) := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hK0)
      rw [mul_assoc, e1, e2, e3]
    have hidx0 : (D (i + 1)).relIndex (D i) ≠ 0 := Subgroup.index_ne_zero_of_finite
    have : Nat.card (D (i + 1)) * 2 ≤ Nat.card (D i) := by
      rw [← hmul]; exact Nat.mul_le_mul_left _ (by omega)
    calc Nat.card (D (i + 1)) * 2 ^ (i + 1) = (Nat.card (D (i + 1)) * 2) * 2 ^ i := by ring
      _ ≤ Nat.card (D i) * 2 ^ i := Nat.mul_le_mul_right _ this
      _ ≤ Nat.card (D 0) := ih

/-- **The linear image of the derived series ends.** -/
theorem vsPDer_map_bot {G C : Subgroup (Perm (Fin n))} {M : Type*} [Group M]
    (φ : G →* M) (hG : Group.IsSolvable φ.range) (hC : C ≤ G)
    {g : Perm (Fin n)} (hg : g ∈ vsPDer C (n * n + 1)) :
    φ ⟨g, hC (vsPDer_le C (n * n + 1) hg)⟩ = 1 := by
  suffices hbot : ((vsPDer C (n * n + 1)).subgroupOf G).map φ.rangeRestrict = ⊥ by
    have hmem : φ.rangeRestrict ⟨g, hC (vsPDer_le C (n * n + 1) hg)⟩ ∈
        ((vsPDer C (n * n + 1)).subgroupOf G).map φ.rangeRestrict :=
      ⟨⟨g, hC (vsPDer_le C (n * n + 1) hg)⟩, hg, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  by_contra h
  have : Finite φ.range := Set.Finite.to_subtype (Set.finite_range φ)
  have h1 := vsPDer_map_card φ hG hC (n * n + 1) h
  have h2 : 1 ≤ Nat.card (((vsPDer C (n * n + 1)).subgroupOf G).map φ.rangeRestrict) :=
    Nat.card_pos
  have h3a : Nat.card ((C.subgroupOf G).map φ.rangeRestrict) ≤ Nat.card φ.range :=
    Subgroup.card_le_card_group _
  have h3b : Nat.card φ.range ≤ Nat.card G := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).symm.toEquiv,
      Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have h3c : Nat.card G ≤ n.factorial := by
    have := Subgroup.card_le_card_group G
    rwa [Nat.card_perm, Nat.card_fin] at this
  have h4 : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
  have h5 : n ^ n ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le n
  have h6 : (2 ^ n) ^ n = 2 ^ (n * n) := by rw [← pow_mul]
  have h7 : 2 ^ (n * n) < 2 ^ (n * n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have : 2 ^ (n * n + 1) ≤
      Nat.card (((vsPDer C (n * n + 1)).subgroupOf G).map φ.rangeRestrict) * 2 ^ (n * n + 1) :=
    Nat.le_mul_of_pos_left _ h2
  omega

end GI.Proved
