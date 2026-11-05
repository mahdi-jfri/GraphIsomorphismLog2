module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Nat.Squarefree

@[expose] public section

/-!
# Nonabelian finite simple groups have order at least 34

The proof of Lemma A.21 uses "every `|T_i| ≥ 60`" only through
`2 · 24^{1/3} < √|T_i|`, which holds as soon as `|T_i| ≥ 34`. We prove the bound `34` without
the classification:

* `Sym(k)` is solvable for `k ≤ 4` (orders `1, 1, 2, 6` are squarefree, and
  `S_4 ⊵ A_4 ⊵ V_4`);
* so every proper subgroup of a nonabelian simple group has index at least `5`;
* Sylow's theorems then exclude every order below `34` except `30`, and a group of squarefree
  order such as `30` is solvable (mathlib's Z-groups).
-/

namespace GI.SmallSimple

open Equiv

theorem isSolvable_of_pGroup {G : Type*} [Group G] [Finite G] {p n : ℕ} (hp : p.Prime)
    (h : Nat.card G = p ^ n) : Group.IsSolvable G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := (IsPGroup.of_card h).isNilpotent
  infer_instance

theorem isSolvable_alternatingGroup_four {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Nat.card α = 4) : Group.IsSolvable (alternatingGroup α) := by
  haveI : Nontrivial α := by
    rw [← Finite.one_lt_card_iff_nontrivial, hα]; norm_num
  haveI := alternatingGroup.normal_kleinFour hα
  have hV := alternatingGroup.kleinFour_card_of_card_eq_four hα
  have hA : Nat.card (alternatingGroup α) = 12 := by
    have h2 := two_mul_nat_card_alternatingGroup (α := α)
    rw [Nat.card_perm, hα] at h2
    have : (4 : ℕ).factorial = 24 := rfl
    omega
  have hQ : Nat.card (alternatingGroup α ⧸ alternatingGroup.kleinFour α) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (alternatingGroup.kleinFour α)
    rw [hA, hV] at h
    omega
  haveI : Group.IsSolvable (alternatingGroup.kleinFour α) :=
    isSolvable_of_pGroup (p := 2) (n := 2) Nat.prime_two (by rw [hV]; norm_num)
  haveI : Group.IsSolvable (alternatingGroup α ⧸ alternatingGroup.kleinFour α) :=
    isSolvable_of_pGroup (p := 3) (n := 1) Nat.prime_three (by rw [hQ]; norm_num)
  refine solvable_of_ker_le_range (alternatingGroup.kleinFour α).subtype
    (QuotientGroup.mk' (alternatingGroup.kleinFour α)) ?_
  intro x hx
  rw [QuotientGroup.ker_mk'] at hx
  exact ⟨⟨x, hx⟩, rfl⟩

theorem squarefree_six : Squarefree 6 :=
  (Nat.squarefree_mul (m := 2) (n := 3) (by decide)).mpr
    ⟨Nat.prime_two.prime.squarefree, Nat.prime_three.prime.squarefree⟩

theorem squarefree_factorial_le_three (k : ℕ) (hk : k ≤ 3) : Squarefree k.factorial := by
  interval_cases k
  · exact squarefree_one
  · exact squarefree_one
  · exact Nat.prime_two.prime.squarefree
  · exact squarefree_six

/-- `Sym(α)` is solvable when `|α| ≤ 4`. -/
theorem isSolvable_perm_of_card_le_four {α : Type*} [Finite α] (hα : Nat.card α ≤ 4) :
    Group.IsSolvable (Perm α) := by
  classical
  letI := Fintype.ofFinite α
  rcases Nat.lt_or_ge (Nat.card α) 4 with h | h
  · have hsq : Squarefree (Nat.card (Perm α)) := by
      rw [Nat.card_perm]
      exact squarefree_factorial_le_three _ (by omega)
    haveI := IsZGroup.of_squarefree hsq
    infer_instance
  · have h4 : Nat.card α = 4 := le_antisymm hα h
    haveI := isSolvable_alternatingGroup_four h4
    haveI : Group.IsSolvable ℤˣ := isSolvable_of_comm (fun a b => mul_comm a b)
    refine solvable_of_ker_le_range (alternatingGroup α).subtype Perm.sign ?_
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem squarefree_thirty : Squarefree 30 :=
  (Nat.squarefree_mul (m := 6) (n := 5) (by decide)).mpr
    ⟨squarefree_six, Nat.prime_five.prime.squarefree⟩

variable {T : Type*} [Group T] [Finite T]

/-- Every proper subgroup of a nonabelian finite simple group has index at least `5`. -/
theorem five_le_index [IsSimpleGroup T] (hT : ¬ ∀ x y : T, x * y = y * x) {H : Subgroup T}
    (hH : H ≠ ⊤) : 5 ≤ H.index := by
  by_contra hlt
  push Not at hlt
  let φ := MulAction.toPermHom T (T ⧸ H)
  have hker : φ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      apply hH
      rw [← Subgroup.normalCore_eq_ker] at h
      exact eq_top_iff.mpr (h ▸ Subgroup.normalCore_le H)
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  haveI : Finite (T ⧸ H) := inferInstance
  haveI : Group.IsSolvable (Perm (T ⧸ H)) :=
    isSolvable_perm_of_card_le_four (by rw [← Subgroup.index]; omega)
  haveI : Group.IsSolvable T := solvable_of_solvable_injective hinj
  exact hT (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance)

/-- The arithmetic part: for each order `n < 34` other than `30`, a prime `p` such that no
divisor `d ≥ 5` of the `p'`-part is `1` modulo `p`. -/
theorem small_orders (n : ℕ) (hn : n < 34) (h2 : 2 ≤ n) (h30 : n ≠ 30) :
    ∃ p k m : ℕ, p.Prime ∧ n = p ^ k * m ∧ 1 ≤ k ∧ ¬ p ∣ m ∧
      ∀ d ∈ m.divisors, d % p = 1 → d < 5 := by
  interval_cases n
  all_goals first
    | exact (h30 rfl).elim
    | exact ⟨2, 1, 1, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨3, 1, 1, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨2, 2, 1, by decide, rfl, by decide, by decide, by decide⟩
    | exact ⟨5, 1, 1, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨3, 1, 2, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨7, 1, 1, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨2, 3, 1, by decide, rfl, by decide, by decide, by decide⟩
    | exact ⟨3, 2, 1, by decide, rfl, by decide, by decide, by decide⟩
    | exact ⟨5, 1, 2, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨11, 1, 1, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨3, 1, 4, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨13, 1, 1, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨7, 1, 2, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨5, 1, 3, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨2, 4, 1, by decide, rfl, by decide, by decide, by decide⟩
    | exact ⟨17, 1, 1, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨3, 2, 2, by decide, rfl, by decide, by decide, by decide⟩
    | exact ⟨19, 1, 1, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨5, 1, 4, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨7, 1, 3, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨11, 1, 2, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨23, 1, 1, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨3, 1, 8, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨5, 2, 1, by decide, rfl, by decide, by decide, by decide⟩
    | exact ⟨13, 1, 2, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨3, 3, 1, by decide, rfl, by decide, by decide, by decide⟩
    | exact ⟨7, 1, 4, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨29, 1, 1, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨31, 1, 1, by decide, rfl, le_rfl, by decide, by decide⟩
    | exact ⟨2, 5, 1, by decide, rfl, by decide, by decide, by decide⟩
    | exact ⟨11, 1, 3, by decide, rfl, le_rfl, by decide, by decide⟩

/-- **A nonabelian finite simple group has order at least `34`.** -/
theorem thirtyfour_le_card [IsSimpleGroup T] (hT : ¬ ∀ x y : T, x * y = y * x) :
    34 ≤ Nat.card T := by
  by_contra hlt
  push Not at hlt
  have h2 : 2 ≤ Nat.card T := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  by_cases h30 : Nat.card T = 30
  · have hsq : Squarefree (Nat.card T) := by rw [h30]; exact squarefree_thirty
    haveI := IsZGroup.of_squarefree hsq
    exact hT (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance)
  obtain ⟨p, k, m, hp, hnm, hk, hpm, hd⟩ := small_orders _ hlt h2 h30
  haveI : Fact p.Prime := ⟨hp⟩
  have hpn : p ∣ Nat.card T := hnm ▸ Dvd.dvd.mul_right (dvd_pow_self p (by omega)) m
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := T)
  -- the number of Sylow `p`-subgroups divides `m` and is `1` modulo `p`
  have hidx : P.index ∣ m := by
    have h1 : P.index ∣ p ^ k * m := hnm ▸ (P : Subgroup T).index_dvd_card
    have hcop : Nat.Coprime P.index (p ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr
        (Sylow.not_dvd_index P))))
    exact hcop.dvd_of_dvd_mul_left h1
  have hnp_dvd : Nat.card (Sylow p T) ∣ m := (P.card_dvd_index).trans hidx
  have hnp_mod : Nat.card (Sylow p T) % p = 1 := by
    have h := card_sylow_modEq_one p T
    rw [Nat.ModEq, Nat.one_mod_eq_one.mpr hp.ne_one] at h
    exact h
  have hm0 : m ≠ 0 := by rintro rfl; simp at hnm; omega
  have hnp_lt : Nat.card (Sylow p T) < 5 :=
    hd _ (Nat.mem_divisors.mpr ⟨hnp_dvd, hm0⟩) hnp_mod
  rw [Sylow.card_eq_index_normalizer P] at hnp_lt
  by_cases hN : Subgroup.normalizer (P : Set T) = ⊤
  · -- `P` is normal, so it is trivial or everything
    haveI : (P : Subgroup T).Normal := Subgroup.normalizer_eq_top_iff.mp hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup T) with h | h
    · exact P.ne_bot_of_dvd_card hpn h
    · have hPg : IsPGroup p T := by
        have := P.isPGroup'
        rw [h] at this
        exact this.of_equiv Subgroup.topEquiv
      haveI := hPg.isNilpotent
      exact hT (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance)
  · exact absurd (five_le_index hT hN) (by omega)

end GI.SmallSimple
