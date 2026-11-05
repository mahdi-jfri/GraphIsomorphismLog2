module

public import Workspace.Proved.SolvOrderPrimitive
public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.Algebra.Group.Pointwise.Set.Card

@[expose] public section

/-!
# Dixon's bound on the order of a solvable permutation group

**Theorem** (Dixon 1967; see Dixon–Mortimer, *Permutation Groups*, Theorem 5.8A). A solvable
subgroup `G` of `Sym(α)` with `|α| = n ≥ 1` has `|G| ≤ 24^{(n-1)/3}`. We state it as
`|G|^3 ≤ 24^{n-1}` (`GI.Proved.solvOrder_bound`).

*Proof*, by strong induction on `n`.
* If `G` is not transitive, an orbit `s` and its complement are both invariant and nonempty.
  `G` embeds in the product of its restrictions to `s` and to the complement, and the exponents
  add up to at most `n - 1`.
* If `G` is transitive with a block `B` of size `m`, `1 < m < n`, let `k` be the number of
  translates of `B`, so `mk = n`. The action on the translates has image of order at most
  `24^{(k-1)/3}`. Its kernel embeds in the product of its restrictions to the `k` translates,
  each of order at most `24^{(m-1)/3}`.
* If `G` is primitive, `GI.Proved.solvPrim_card_le` and `GI.Proved.solv_numeric` give the bound.
-/

namespace GI.Proved

open MulAction Pointwise

universe u

/-- The restriction of an action to an invariant set. -/
def solvRes {H α : Type*} [Group H] [MulAction H α] (s : Set α)
    (hs : ∀ (h : H) (x : α), h • x ∈ s ↔ x ∈ s) : H →* Equiv.Perm s where
  toFun h :=
    { toFun := fun x => ⟨h • x.1, (hs h x).2 x.2⟩
      invFun := fun x => ⟨h⁻¹ • x.1, (hs h⁻¹ x).2 x.2⟩
      left_inv := fun x => Subtype.ext (inv_smul_smul h x.1)
      right_inv := fun x => Subtype.ext (smul_inv_smul h x.1) }
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [mul_smul]

theorem solvRes_apply {H α : Type*} [Group H] [MulAction H α] (s : Set α)
    (hs : ∀ (h : H) (x : α), h • x ∈ s ↔ x ∈ s) (h : H) (x : s) :
    ((solvRes s hs h) x : α) = h • (x : α) := rfl

/-- The induction hypothesis: the bound holds on every smaller nonempty finite type. -/
def SolvOrderIH (n : ℕ) : Prop :=
  ∀ (β : Type u) [Finite β], 1 ≤ Nat.card β → Nat.card β < n →
    ∀ G : Subgroup (Equiv.Perm β), IsSolvable G → Nat.card G ^ 3 ≤ 24 ^ (Nat.card β - 1)

/-- The induction hypothesis applied to the image of a solvable group. -/
theorem SolvOrderIH.range {n : ℕ} (ih : SolvOrderIH.{u} n) {H : Type*} [Group H] [Group.IsSolvable H]
    {β : Type u} [Finite β] (hβ : 1 ≤ Nat.card β) (hβn : Nat.card β < n)
    (ρ : H →* Equiv.Perm β) : Nat.card ρ.range ^ 3 ≤ 24 ^ (Nat.card β - 1) :=
  ih β hβ hβn ρ.range (solvable_of_surjective ρ.rangeRestrict_surjective)

/-- The intransitive step. -/
theorem solvOrder_intransitive {α : Type u} [Finite α] (ih : SolvOrderIH.{u} (Nat.card α))
    (G : Subgroup (Equiv.Perm α)) [Group.IsSolvable G] (s : Set α)
    (hs : ∀ (g : G) (x : α), g • x ∈ s ↔ x ∈ s) (hne : s.Nonempty) (hne' : sᶜ.Nonempty) :
    Nat.card G ^ 3 ≤ 24 ^ (Nat.card α - 1) := by
  have hs' : ∀ (g : G) (x : α), g • x ∈ sᶜ ↔ x ∈ sᶜ := fun g x => not_congr (hs g x)
  let ρ₁ := solvRes s hs
  let ρ₂ := solvRes sᶜ hs'
  have hsum : Nat.card s + Nat.card (sᶜ : Set α) = Nat.card α := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_add_ncard_compl]
  have h1 : 1 ≤ Nat.card s := by
    rw [Nat.card_coe_set_eq]; exact Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (Set.toFinite _)).mpr hne).ne'
  have h2 : 1 ≤ Nat.card (sᶜ : Set α) := by
    rw [Nat.card_coe_set_eq]; exact Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (Set.toFinite _)).mpr hne').ne'
  have hb1 := ih.range h1 (by omega) ρ₁
  have hb2 := ih.range h2 (by omega) ρ₂
  have hinj : Function.Injective (fun g : G => (ρ₁.rangeRestrict g, ρ₂.rangeRestrict g)) := by
    intro g h hgh
    simp only [Prod.mk.injEq] at hgh
    apply eq_of_smul_eq_smul (α := α)
    intro x
    by_cases hx : x ∈ s
    · have := congrArg (fun p : ρ₁.range => ((p : Equiv.Perm s) ⟨x, hx⟩ : α)) hgh.1
      exact this
    · have := congrArg (fun p : ρ₂.range => ((p : Equiv.Perm (sᶜ : Set α)) ⟨x, hx⟩ : α)) hgh.2
      exact this
  have hcard : Nat.card G ≤ Nat.card ρ₁.range * Nat.card ρ₂.range := by
    rw [← Nat.card_prod]; exact Nat.card_le_card_of_injective _ hinj
  calc Nat.card G ^ 3 ≤ (Nat.card ρ₁.range * Nat.card ρ₂.range) ^ 3 := Nat.pow_le_pow_left hcard 3
    _ = Nat.card ρ₁.range ^ 3 * Nat.card ρ₂.range ^ 3 := mul_pow _ _ _
    _ ≤ 24 ^ (Nat.card s - 1) * 24 ^ (Nat.card (sᶜ : Set α) - 1) := Nat.mul_le_mul hb1 hb2
    _ = 24 ^ (Nat.card s - 1 + (Nat.card (sᶜ : Set α) - 1)) := (pow_add _ _ _).symm
    _ ≤ 24 ^ (Nat.card α - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The kernel of the action on the translates of a block fixes each translate. -/
theorem solvKer_mem_iff {α : Type u} (G : Subgroup (Equiv.Perm α)) (B : Set α)
    (k : (MulAction.toPermHom G (orbit G B)).ker) (C : orbit G B) (x : α) :
    k • x ∈ C.1 ↔ x ∈ C.1 := by
  have hk : (k : G) • C = C := by
    have := congrArg (fun p : Equiv.Perm (orbit G B) => p C) k.property
    exact this
  have hk' : (k : G) • (C.1 : Set α) = C.1 := congrArg Subtype.val hk
  change (k : G) • x ∈ C.1 ↔ x ∈ C.1
  conv_lhs => rw [← hk']
  exact Set.smul_mem_smul_set_iff

/-- The imprimitive step. -/
theorem solvOrder_imprimitive {α : Type u} [Finite α] (ih : SolvOrderIH.{u} (Nat.card α))
    (G : Subgroup (Equiv.Perm α)) [Group.IsSolvable G] [IsPretransitive G α] (B : Set α)
    (hB : IsBlock G B) (hBnt : ¬ IsTrivialBlock B) :
    Nat.card G ^ 3 ≤ 24 ^ (Nat.card α - 1) := by
  classical
  rw [IsTrivialBlock, not_or] at hBnt
  obtain ⟨hBs, hBu⟩ := hBnt
  have hBnt' : B.Nontrivial := Set.not_subsingleton_iff.mp hBs
  have hBne : B.Nonempty := hBnt'.nonempty
  set m := B.ncard with hm
  have hm2 : 1 < m := (Set.one_lt_ncard_iff_nontrivial).mpr hBnt'
  have hmn : m < Nat.card α := Set.ncard_lt_card hBu
  let Ω := orbit G B
  have hmk : m * Nat.card Ω = Nat.card α := by
    rw [Nat.card_coe_set_eq]; exact hB.ncard_block_mul_ncard_orbit_eq hBne
  set k := Nat.card Ω with hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hmk; omega
    · exact h
  have hkn : k < Nat.card α := by
    rw [← hmk]; exact lt_mul_left (by omega) hm2
  let φ := MulAction.toPermHom G Ω
  have hφ := ih.range hk1 hkn φ
  let K := φ.ker
  haveI : Group.IsSolvable K := solvable_of_solvable_injective K.subtype_injective
  let ψ : ∀ C : Ω, K →* Equiv.Perm C.1 := fun C => solvRes C.1 (fun x v => solvKer_mem_iff G B x C v)
  have hCcard : ∀ C : Ω, Nat.card C.1 = m := by
    intro C
    obtain ⟨g, hg⟩ := C.2
    rw [Nat.card_coe_set_eq, ← hg]
    exact Set.ncard_smul_set _ _
  have hψ : ∀ C : Ω, Nat.card (ψ C).range ^ 3 ≤ 24 ^ (m - 1) := by
    intro C
    have h := ih.range (β := C.1) (by rw [hCcard]; omega) (by rw [hCcard]; exact hmn) (ψ C)
    rwa [hCcard] at h
  letI : Fintype Ω := Fintype.ofFinite Ω
  have hinj : Function.Injective (fun x : K => fun C : Ω => (ψ C).rangeRestrict x) := by
    intro x y hxy
    apply eq_of_smul_eq_smul (α := α)
    intro v
    obtain ⟨b, hb⟩ := hBne
    obtain ⟨g, rfl⟩ := exists_smul_eq G b v
    let C : Ω := ⟨g • B, mem_orbit B g⟩
    have hv : g • b ∈ C.1 := Set.smul_mem_smul_set hb
    have := congrArg (fun p : (ψ C).range => ((p : Equiv.Perm C.1) ⟨g • b, hv⟩ : α))
      (congrFun hxy C)
    exact this
  have hK : Nat.card K ≤ ∏ C : Ω, Nat.card (ψ C).range := by
    rw [← Nat.card_pi]; exact Nat.card_le_card_of_injective _ hinj
  have hK3 : Nat.card K ^ 3 ≤ (24 ^ (m - 1)) ^ k := by
    calc Nat.card K ^ 3 ≤ (∏ C : Ω, Nat.card (ψ C).range) ^ 3 := Nat.pow_le_pow_left hK 3
      _ = ∏ C : Ω, Nat.card (ψ C).range ^ 3 := (Finset.prod_pow _ _ _).symm
      _ ≤ ∏ _C : Ω, 24 ^ (m - 1) := Finset.prod_le_prod' (fun C _ => hψ C)
      _ = (24 ^ (m - 1)) ^ k := by
        rw [Finset.prod_const, Finset.card_univ, hk, Nat.card_eq_fintype_card]
  have hG : Nat.card G = Nat.card φ.range * Nat.card K := by
    rw [← Subgroup.card_mul_index K, Subgroup.index_ker, mul_comm]
  have hexp : k - 1 + (m - 1) * k = Nat.card α - 1 := by
    rw [Nat.sub_mul, one_mul, mul_comm m k] at *
    have : k ≤ k * m := Nat.le_mul_of_pos_right k (by omega)
    omega
  calc Nat.card G ^ 3 = Nat.card φ.range ^ 3 * Nat.card K ^ 3 := by rw [hG, mul_pow]
    _ ≤ 24 ^ (k - 1) * (24 ^ (m - 1)) ^ k := Nat.mul_le_mul hφ hK3
    _ = 24 ^ (Nat.card α - 1) := by rw [← pow_mul, ← pow_add, hexp]

theorem solvOrder_bound_aux : ∀ (n : ℕ) (α : Type u) [Finite α], Nat.card α = n → 1 ≤ n →
    ∀ G : Subgroup (Equiv.Perm α), IsSolvable G → Nat.card G ^ 3 ≤ 24 ^ (n - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro α _ hα hn G hG
  haveI : Group.IsSolvable G := hG
  subst hα
  have ih' : SolvOrderIH.{u} (Nat.card α) := fun β _ h1 hlt G hG => ih _ hlt β rfl h1 G hG
  by_cases hnt : Nontrivial G
  swap
  · rw [not_nontrivial_iff_subsingleton] at hnt
    rw [Nat.card_unique, one_pow]
    exact Nat.one_le_pow _ _ (by norm_num)
  by_cases ht : IsPretransitive G α
  swap
  · have hex : ∃ a b : α, ∀ g : G, g • a ≠ b := by
      by_contra h
      push Not at h
      exact ht ⟨fun a b => h a b⟩
    obtain ⟨a, b, hab⟩ := hex
    refine solvOrder_intransitive ih' G (orbit G a) ?_ ⟨a, mem_orbit_self a⟩ ⟨b, ?_⟩
    · intro g x
      rw [← orbit_eq_iff, orbit_smul, orbit_eq_iff]
    · rintro ⟨g, hg⟩
      exact hab g hg
  by_cases hp : IsPreprimitive G α
  · have h1 := solvPrim_card_le (G := G) (V := α)
    calc Nat.card G ^ 3 ≤ (Nat.card α * solvB (Nat.card α) (Nat.card α) 1) ^ 3 :=
          Nat.pow_le_pow_left h1 3
      _ ≤ 24 ^ (Nat.card α - 1) := solv_numeric _ hn
  · have hex : ∃ B : Set α, IsBlock G B ∧ ¬ IsTrivialBlock B := by
      by_contra h
      push Not at h
      exact hp { toIsPretransitive := ht, isTrivialBlock_of_isBlock := fun hB => h _ hB }
    obtain ⟨B, hB, hBnt⟩ := hex
    exact solvOrder_imprimitive ih' G B hB hBnt

/-- **Dixon's order bound.** A solvable subgroup `G ≤ Sym(α)` with `|α| ≥ 1` has
`|G|^3 ≤ 24^{|α| - 1}`. -/
theorem solvOrder_bound {α : Type u} [Finite α] (hα : 1 ≤ Nat.card α)
    (G : Subgroup (Equiv.Perm α)) (hG : IsSolvable G) :
    Nat.card G ^ 3 ≤ 24 ^ (Nat.card α - 1) :=
  solvOrder_bound_aux _ α rfl hα G hG

end GI.Proved
