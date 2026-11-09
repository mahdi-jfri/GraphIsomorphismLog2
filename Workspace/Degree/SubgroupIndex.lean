module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Subgroups of a product of perfect groups

Let `G = T_1 × ⋯ × T_b` with each `T_i` perfect, and let `f_i` be a lower bound for the index of
every proper subgroup of `T_i`. If a subgroup `S ≤ G` contains no `T_i`, then
`∏ f_i ≤ |G : S|²` (`GI.Degree.prod_le_index_sq`).

*Proof.* List the coordinates in order. `|S|` is the product over `i` of the size of the projection
to `T_i` of the part of `S` on coordinates `≤ i`. Call this projection `A_i`. It is also the product
of the sizes of the projections `B_i` of the part of `S` on coordinates `≥ i`. If `A_i = B_i = T_i`
then `S` contains all commutators of `T_i`, because an element of the first part and one of the
second overlap only at `i`. So one of `A_i, B_i` is proper, and `|A_i| |B_i| f_i ≤ |T_i|²`.
-/

@[expose] public section

namespace GI.Degree

open scoped commutatorElement

/-- If `B` is the part of `A` in the kernel of `φ`, then `|A| = |B| |φ(A)|`. -/
theorem card_eq_mul_card_map {G H : Type*} [Group G] [Group H] (A B : Subgroup G) (φ : G →* H)
    (h : ∀ x, x ∈ B ↔ x ∈ A ∧ φ x = 1) :
    Nat.card A = Nat.card B * Nat.card (A.map φ) := by
  let ρ : A →* H := φ.comp A.subtype
  have h1 : Nat.card ρ.ker = Nat.card B := by
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, (h _).2 ⟨x.1.2, x.2⟩⟩,
      fun x => ⟨⟨x.1, ((h _).1 x.2).1⟩, ((h _).1 x.2).2⟩, fun _ => rfl, fun _ => rfl⟩
  have h2 : ρ.range = A.map φ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have h3 := ρ.ker.card_mul_index
  rw [Subgroup.index_ker, h2, h1] at h3
  exact h3.symm

variable {b : ℕ} {T : Fin b → Type*} [∀ i, Group (T i)]

/-- The elements supported on coordinates below `k`. -/
def lowPart (T : Fin b → Type*) [∀ i, Group (T i)] (k : ℕ) : Subgroup (∀ i, T i) where
  carrier := {x | ∀ i : Fin b, k ≤ i.val → x i = 1}
  mul_mem' := fun ha hb i hi => by simp [ha i hi, hb i hi]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun ha i hi => by simp [ha i hi]

/-- The elements supported on coordinates at or above `k`. -/
def highPart (T : Fin b → Type*) [∀ i, Group (T i)] (k : ℕ) : Subgroup (∀ i, T i) where
  carrier := {x | ∀ i : Fin b, i.val < k → x i = 1}
  mul_mem' := fun ha hb i hi => by simp [ha i hi, hb i hi]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun ha i hi => by simp [ha i hi]

/-- The projection to coordinate `i` of the part of `S` on coordinates up to `i`. -/
def lowProj (S : Subgroup (∀ i, T i)) (i : Fin b) : Subgroup (T i) :=
  (S ⊓ lowPart T (i.val + 1)).map (Pi.evalMonoidHom T i)

/-- The projection to coordinate `i` of the part of `S` on coordinates from `i` on. -/
def highProj (S : Subgroup (∀ i, T i)) (i : Fin b) : Subgroup (T i) :=
  (S ⊓ highPart T i.val).map (Pi.evalMonoidHom T i)

theorem card_low_succ (S : Subgroup (∀ i, T i)) (i : Fin b) :
    Nat.card (S ⊓ lowPart T (i.val + 1) : Subgroup _) =
      Nat.card (S ⊓ lowPart T i.val : Subgroup _) * Nat.card (lowProj S i) := by
  refine card_eq_mul_card_map _ _ (Pi.evalMonoidHom T i) fun x => ?_
  constructor
  · rintro ⟨hS, hl⟩
    exact ⟨⟨hS, fun j hj => hl j (by omega)⟩, hl i le_rfl⟩
  · rintro ⟨⟨hS, hl⟩, h1⟩
    refine ⟨hS, fun j hj => ?_⟩
    by_cases h : i.val + 1 ≤ j.val
    · exact hl j h
    · have : j = i := Fin.ext (by omega)
      subst this
      exact h1

theorem card_high_succ (S : Subgroup (∀ i, T i)) (i : Fin b) :
    Nat.card (S ⊓ highPart T i.val : Subgroup _) =
      Nat.card (S ⊓ highPart T (i.val + 1) : Subgroup _) * Nat.card (highProj S i) := by
  refine card_eq_mul_card_map _ _ (Pi.evalMonoidHom T i) fun x => ?_
  constructor
  · rintro ⟨hS, hl⟩
    exact ⟨⟨hS, fun j hj => hl j (by omega)⟩, hl i (by omega)⟩
  · rintro ⟨⟨hS, hl⟩, h1⟩
    refine ⟨hS, fun j hj => ?_⟩
    by_cases h : j.val < i.val
    · exact hl j h
    · have : j = i := Fin.ext (by omega)
      subst this
      exact h1

theorem card_eq_prod_lowProj (S : Subgroup (∀ i, T i)) :
    Nat.card S = ∏ i : Fin b, Nat.card (lowProj S i) := by
  let a : ℕ → ℕ := fun j => if h : j < b then Nat.card (lowProj S ⟨j, h⟩) else 1
  have key : ∀ k, k ≤ b → Nat.card (S ⊓ lowPart T k : Subgroup _) = ∏ j ∈ Finset.range k, a j := by
    intro k
    induction k with
    | zero =>
      intro _
      have : (S ⊓ lowPart T 0 : Subgroup _) = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨-, hx⟩
        exact funext fun i => hx i (Nat.zero_le _)
      rw [this]
      simp
    | succ k ih =>
      intro hk
      rw [Finset.prod_range_succ, ← ih (by omega), card_low_succ S ⟨k, by omega⟩]
      simp [a, show k < b by omega]
  have hS : (S ⊓ lowPart T b : Subgroup _) = S := by
    apply inf_eq_left.mpr
    intro x _ i hi
    exact absurd i.2 (by omega)
  have := key b le_rfl
  rw [hS] at this
  rw [this, ← Fin.prod_univ_eq_prod_range a b]
  exact Finset.prod_congr rfl fun i _ => by simp [a]

theorem card_eq_prod_highProj (S : Subgroup (∀ i, T i)) :
    Nat.card S = ∏ i : Fin b, Nat.card (highProj S i) := by
  let a : ℕ → ℕ := fun j => if h : j < b then Nat.card (highProj S ⟨j, h⟩) else 1
  have key : ∀ k, k ≤ b →
      Nat.card (S ⊓ highPart T k : Subgroup _) * ∏ j ∈ Finset.range k, a j = Nat.card S := by
    intro k
    induction k with
    | zero =>
      intro _
      have : (S ⊓ highPart T 0 : Subgroup _) = S := inf_eq_left.mpr fun x _ i hi => absurd hi (by omega)
      rw [this]
      simp
    | succ k ih =>
      intro hk
      rw [Finset.prod_range_succ, ← ih (by omega), card_high_succ S ⟨k, by omega⟩]
      simp only [a, show k < b by omega, dite_true]
      ring
  have hS : (S ⊓ highPart T b : Subgroup _) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨-, hx⟩
    exact funext fun i => hx i i.2
  have := key b le_rfl
  rw [hS] at this
  simp only [Subgroup.card_bot, one_mul] at this
  rw [← this, ← Fin.prod_univ_eq_prod_range a b]
  exact Finset.prod_congr rfl fun i _ => by simp [a]

/-- If both projections at `i` are onto, then `S` contains the commutators of `T i`. -/
theorem commutator_le_comap_single [DecidableEq (Fin b)] (S : Subgroup (∀ i, T i)) (i : Fin b)
    (hA : lowProj S i = ⊤) (hB : highProj S i = ⊤) :
    ⁅(⊤ : Subgroup (T i)), (⊤ : Subgroup (T i))⁆ ≤ S.comap (MonoidHom.mulSingle T i) := by
  rw [Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨s, ⟨hs, hsl⟩, hsx⟩ : x ∈ lowProj S i := hA ▸ Subgroup.mem_top x
  obtain ⟨s', ⟨hs', hsh⟩, hsy⟩ : y ∈ highProj S i := hB ▸ Subgroup.mem_top y
  have hc : ⁅s, s'⁆ ∈ S := by
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem hs hs') (S.inv_mem hs)) (S.inv_mem hs')
  have heq : MonoidHom.mulSingle T i ⁅x, y⁆ = ⁅s, s'⁆ := by
    funext j
    have hj : (⁅s, s'⁆ : ∀ i, T i) j = ⁅s j, s' j⁆ := rfl
    rw [hj]
    rcases lt_trichotomy j.val i.val with h | h | h
    · have hne : j ≠ i := fun e => by simp [e] at h
      rw [hsh j h, commutatorElement_one_right]
      exact Pi.mulSingle_eq_of_ne hne _
    · have e : j = i := Fin.ext h
      subst e
      simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
      rw [← hsx, ← hsy]
      rfl
    · have hne : j ≠ i := fun e => by simp [e] at h
      rw [hsl j (by omega), commutatorElement_one_left]
      exact Pi.mulSingle_eq_of_ne hne _
  rw [Subgroup.mem_comap, heq]
  exact hc

/-- **Index of a subgroup containing no factor.** -/
theorem prod_le_index_sq [∀ i, Finite (T i)] (S : Subgroup (∀ i, T i)) (f : Fin b → ℕ)
    (hperf : ∀ i, ⁅(⊤ : Subgroup (T i)), (⊤ : Subgroup (T i))⁆ = ⊤)
    (hf : ∀ i, ∀ A : Subgroup (T i), A ≠ ⊤ → f i ≤ A.index)
    (hS : ∀ i, ¬ ∀ t : T i, MonoidHom.mulSingle T i t ∈ S) :
    ∏ i, f i ≤ S.index ^ 2 := by
  classical
  have hone : ∀ i, Nat.card (lowProj S i) * Nat.card (highProj S i) * f i ≤
      Nat.card (T i) * Nat.card (T i) := by
    intro i
    by_cases hA : lowProj S i = ⊤
    · have hB : highProj S i ≠ ⊤ := by
        intro hB
        have h := commutator_le_comap_single S i hA hB
        rw [hperf i] at h
        exact hS i fun t => h (Subgroup.mem_top t)
      calc _ = Nat.card (lowProj S i) * (Nat.card (highProj S i) * f i) := by ring
        _ ≤ Nat.card (T i) * (Nat.card (highProj S i) * (highProj S i).index) := by
          gcongr
          · exact Subgroup.card_le_card_group _
          · exact hf i _ hB
        _ = _ := by rw [Subgroup.card_mul_index]
    · calc _ = (Nat.card (lowProj S i) * f i) * Nat.card (highProj S i) := by ring
        _ ≤ (Nat.card (lowProj S i) * (lowProj S i).index) * Nat.card (T i) := by
          gcongr
          · exact hf i _ hA
          · exact Subgroup.card_le_card_group _
        _ = _ := by rw [Subgroup.card_mul_index]
  have hprod := Finset.prod_le_prod (s := Finset.univ) fun i _ => hone i
  simp only [Finset.prod_mul_distrib] at hprod
  rw [← card_eq_prod_lowProj, ← card_eq_prod_highProj, ← Nat.card_pi, ← S.card_mul_index] at hprod
  have hpos : 0 < Nat.card S * Nat.card S := Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc _ ≤ _ := hprod
    _ = _ := by ring

/-- `GI.Degree.prod_le_index_sq` for any finite index type. -/
theorem prod_le_index_sq' {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ι → Type*}
    [∀ i, Group (T i)] [∀ i, Finite (T i)] (S : Subgroup (∀ i, T i)) (f : ι → ℕ)
    (hperf : ∀ i, ⁅(⊤ : Subgroup (T i)), (⊤ : Subgroup (T i))⁆ = ⊤)
    (hf : ∀ i, ∀ A : Subgroup (T i), A ≠ ⊤ → f i ≤ A.index)
    (hS : ∀ i, ¬ ∀ t : T i, MonoidHom.mulSingle T i t ∈ S) :
    ∏ i, f i ≤ S.index ^ 2 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let T' : Fin (Fintype.card ι) → Type _ := fun j => T (e.symm j)
  let Φ : (∀ i, T i) ≃* (∀ j, T' j) :=
    { Equiv.piCongrLeft' T e with
      map_mul' := fun _ _ => rfl }
  have hΦ : ∀ x j, Φ x j = x (e.symm j) := fun _ _ => rfl
  have hsing : ∀ j (t : T' j), Φ (MonoidHom.mulSingle T (e.symm j) t) =
      MonoidHom.mulSingle T' j t := by
    intro j t
    funext j'
    rw [hΦ]
    by_cases h : j' = j
    · subst h
      simp [T']
    · have hne : e.symm j' ≠ e.symm j := fun h' => h (e.symm.injective h')
      simp only [MonoidHom.mulSingle_apply]
      rw [Pi.mulSingle_eq_of_ne hne, Pi.mulSingle_eq_of_ne h]
  have h := prod_le_index_sq (T := T') (S.map (Φ : (∀ i, T i) →* ∀ j, T' j)) (fun j => f (e.symm j))
    (fun j => hperf _) (fun j A hA => hf _ A hA) (fun j hall => hS (e.symm j) fun t => by
      obtain ⟨x, hx, hxe⟩ := hall t
      have : x = MonoidHom.mulSingle T (e.symm j) t := Φ.injective (by rw [hsing]; exact hxe)
      exact this ▸ hx)
  rw [Subgroup.index_map_equiv, Equiv.prod_comp e.symm f] at h
  exact h

/-- The index of a preimage is at most the index of the subgroup. -/
theorem index_comap_le' {G G' : Type*} [Group G] [Group G'] (f : G' →* G) (S : Subgroup G)
    [Finite (G ⧸ S)] : (S.comap f).index ≤ S.index := by
  refine Nat.card_le_card_of_injective (fun q : G' ⧸ S.comap f => ((f q.out : G) : G ⧸ S)) ?_
  intro a b h
  have h1 : (f a.out)⁻¹ * f b.out ∈ S := QuotientGroup.eq.1 h
  rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
  refine QuotientGroup.eq.2 ?_
  rw [Subgroup.mem_comap, map_mul, map_inv]
  exact h1

end GI.Degree
