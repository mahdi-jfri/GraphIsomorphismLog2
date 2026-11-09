module

public import Workspace.Degree.MarotiFacts
public import Workspace.Proved.SolvOrder
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# GNS Lemma 2.2

A subgroup of `Sym(n)` in `Γ̂_d`, for `d ≥ 6`, has order at most `d^(n-1)`
(`GI.Degree.card_le_pow`). We use the class `Γ̂_d` in place of GNS's condition that no alternating
composition factor has degree above `d`, since this is the form the paper uses.

*Proof*, by strong induction on `n`, as for Dixon's bound in `Workspace/Proved/SolvOrder.lean`.
Orbits and blocks reduce to primitive groups. A primitive group of degree `n ≤ d` has order at most
`n! ≤ d^(n-1)`. For `n > d` we use Maróti's theorem. If the group is a Johnson product with
parameters `m, k, r`, then `m ≤ d`, the coordinate group has order at most `d^(r-1)` by induction,
and `|G| ≤ d^(r-1) (m!)^r ≤ d^(m r - 1)`, with `m r ≤ m^r ≤ n`. In the other cases `|G| ≤ 6^(n-1)`
by arithmetic.
-/

@[expose] public section

namespace GI.Degree

open Equiv MulAction Pointwise GI.Proved

/-! ### Arithmetic -/

theorem pow_log_le_six_pow {n : ℕ} (hn : 7 ≤ n) :
    n ^ (1 + Nat.log 2 n) ≤ 6 ^ (n - 1) := by
  rcases Nat.lt_or_ge n 64 with hlt | hge
  · interval_cases n <;> decide +kernel
  · set L := Nat.log 2 n with hL
    have hL6 : 6 ≤ L := Nat.le_log_of_pow_le (by norm_num) (by omega)
    have h1 : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have h2 : 2 ^ L ≤ n := Nat.pow_log_le_self 2 (by omega)
    have h3 : (L + 1) ^ 2 + 1 ≤ 2 ^ L := by
      clear_value L
      clear h1 h2 hL
      induction L, hL6 using Nat.le_induction with
      | base => norm_num
      | succ m hm ih =>
        rw [pow_succ 2 m]
        nlinarith
    calc n ^ (1 + L) ≤ (2 ^ (L + 1)) ^ (1 + L) := Nat.pow_le_pow_left h1.le _
      _ = 2 ^ ((L + 1) ^ 2) := by rw [← pow_mul]; congr 1; ring
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 6 ^ (n - 1) := Nat.pow_le_pow_left (by norm_num) _

theorem pow_seven_le_six_pow {n : ℕ} (hn : 11 ≤ n) : n ^ 7 ≤ 6 ^ (n - 1) := by
  rcases Nat.lt_or_ge n 64 with hlt | hge
  · interval_cases n <;> norm_num
  · refine le_trans (Nat.pow_le_pow_right (by omega) ?_) (pow_log_le_six_pow (by omega))
    have : 6 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by omega)
    omega

theorem factorial_le_pow_pred {n d : ℕ} (hn : n ≤ d) (h1 : 1 ≤ n) :
    n.factorial ≤ d ^ (n - 1) := by
  induction n, h1 using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Nat.factorial_succ, Nat.add_sub_cancel]
    have hm' : m = m - 1 + 1 := by omega
    calc (m + 1) * m.factorial ≤ d * d ^ (m - 1) := Nat.mul_le_mul hn (ih (by omega))
      _ = d ^ m := by rw [← pow_succ', ← hm']

theorem le_choose {m k : ℕ} (hk : 1 ≤ k) (hkm : k < m) : m ≤ m.choose k := by
  induction m generalizing k with
  | zero => omega
  | succ m ih =>
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.choose_succ_succ]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have h1 := ih hj (by omega)
      have h2 : 1 ≤ m.choose j.succ := Nat.choose_pos (by omega)
      omega

/-! ### The induction -/

/-- The induction hypothesis: the bound holds on every smaller nonempty finite type. -/
def OrderIH (d n : ℕ) : Prop :=
  ∀ (β : Type) [Finite β], 1 ≤ Nat.card β → Nat.card β < n →
    ∀ G : Subgroup (Perm β), GammaHat d G → Nat.card G ≤ d ^ (Nat.card β - 1)

/-- The induction hypothesis applied to the image of a group in the class. -/
theorem OrderIH.range {d n : ℕ} (ih : OrderIH d n) {H : Type*} [Group H] (hH : GammaHat d H)
    {β : Type} [Finite β] (hβ : 1 ≤ Nat.card β) (hβn : Nat.card β < n)
    (ρ : H →* Perm β) : Nat.card ρ.range ≤ d ^ (Nat.card β - 1) :=
  ih β hβ hβn ρ.range (hH.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective)

/-- The intransitive step. -/
theorem order_intransitive {d : ℕ} (hd : 1 ≤ d) {α : Type} [Finite α]
    (ih : OrderIH d (Nat.card α)) (G : Subgroup (Perm α)) (hG : GammaHat d G) (s : Set α)
    (hs : ∀ (g : G) (x : α), g • x ∈ s ↔ x ∈ s) (hne : s.Nonempty) (hne' : sᶜ.Nonempty) :
    Nat.card G ≤ d ^ (Nat.card α - 1) := by
  have hs' : ∀ (g : G) (x : α), g • x ∈ sᶜ ↔ x ∈ sᶜ := fun g x => not_congr (hs g x)
  let ρ₁ := solvRes s hs
  let ρ₂ := solvRes sᶜ hs'
  have hsum : Nat.card s + Nat.card (sᶜ : Set α) = Nat.card α := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_add_ncard_compl]
  have h1 : 1 ≤ Nat.card s := by
    rw [Nat.card_coe_set_eq]
    exact Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (Set.toFinite _)).mpr hne).ne'
  have h2 : 1 ≤ Nat.card (sᶜ : Set α) := by
    rw [Nat.card_coe_set_eq]
    exact Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (Set.toFinite _)).mpr hne').ne'
  have hb1 := ih.range hG h1 (by omega) ρ₁
  have hb2 := ih.range hG h2 (by omega) ρ₂
  have hinj : Function.Injective (fun g : G => (ρ₁.rangeRestrict g, ρ₂.rangeRestrict g)) := by
    intro g h hgh
    simp only [Prod.mk.injEq] at hgh
    apply eq_of_smul_eq_smul (α := α)
    intro x
    by_cases hx : x ∈ s
    · exact congrArg (fun p : ρ₁.range => ((p : Perm s) ⟨x, hx⟩ : α)) hgh.1
    · exact congrArg (fun p : ρ₂.range => ((p : Perm (sᶜ : Set α)) ⟨x, hx⟩ : α)) hgh.2
  have hcard : Nat.card G ≤ Nat.card ρ₁.range * Nat.card ρ₂.range := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective _ hinj
  calc Nat.card G ≤ Nat.card ρ₁.range * Nat.card ρ₂.range := hcard
    _ ≤ d ^ (Nat.card s - 1) * d ^ (Nat.card (sᶜ : Set α) - 1) := Nat.mul_le_mul hb1 hb2
    _ = d ^ (Nat.card s - 1 + (Nat.card (sᶜ : Set α) - 1)) := (pow_add _ _ _).symm
    _ ≤ d ^ (Nat.card α - 1) := Nat.pow_le_pow_right hd (by omega)

/-- The imprimitive step. -/
theorem order_imprimitive {d : ℕ} {α : Type} [Finite α] (ih : OrderIH d (Nat.card α))
    (G : Subgroup (Perm α)) (hG : GammaHat d G) [IsPretransitive G α] (B : Set α)
    (hB : IsBlock G B) (hBnt : ¬ IsTrivialBlock B) :
    Nat.card G ≤ d ^ (Nat.card α - 1) := by
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
    rw [Nat.card_coe_set_eq]
    exact hB.ncard_block_mul_ncard_orbit_eq hBne
  set k := Nat.card Ω with hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hmk
      omega
    · exact h
  have hkn : k < Nat.card α := by
    rw [← hmk]
    exact lt_mul_left (by omega) hm2
  let φ := MulAction.toPermHom G Ω
  have hφ := ih.range hG hk1 hkn φ
  let K := φ.ker
  have hKc : GammaHat d K := hG.subgroup K
  let ψ : ∀ C : Ω, K →* Perm C.1 :=
    fun C => solvRes C.1 (fun x v => solvKer_mem_iff G B x C v)
  have hCcard : ∀ C : Ω, Nat.card C.1 = m := by
    intro C
    obtain ⟨g, hg⟩ := C.2
    rw [Nat.card_coe_set_eq, ← hg]
    exact Set.ncard_smul_set _ _
  have hψ : ∀ C : Ω, Nat.card (ψ C).range ≤ d ^ (m - 1) := by
    intro C
    have h := ih.range hKc (β := C.1) (by rw [hCcard]; omega) (by rw [hCcard]; exact hmn) (ψ C)
    rwa [hCcard] at h
  let _ : Fintype Ω := Fintype.ofFinite Ω
  have hinj : Function.Injective (fun x : K => fun C : Ω => (ψ C).rangeRestrict x) := by
    intro x y hxy
    apply eq_of_smul_eq_smul (α := α)
    intro v
    obtain ⟨b, hb⟩ := hBne
    obtain ⟨g, rfl⟩ := exists_smul_eq G b v
    let C : Ω := ⟨g • B, mem_orbit B g⟩
    have hv : g • b ∈ C.1 := Set.smul_mem_smul_set hb
    exact congrArg (fun p : (ψ C).range => ((p : Perm C.1) ⟨g • b, hv⟩ : α)) (congrFun hxy C)
  have hK : Nat.card K ≤ ∏ C : Ω, Nat.card (ψ C).range := by
    rw [← Nat.card_pi]
    exact Nat.card_le_card_of_injective _ hinj
  have hK' : Nat.card K ≤ (d ^ (m - 1)) ^ k := by
    calc Nat.card K ≤ ∏ C : Ω, Nat.card (ψ C).range := hK
      _ ≤ ∏ _C : Ω, d ^ (m - 1) := Finset.prod_le_prod (fun C _ => hψ C)
      _ = (d ^ (m - 1)) ^ k := by
        rw [Finset.prod_const, Finset.card_univ, hk, Nat.card_eq_fintype_card]
  have hGc : Nat.card G = Nat.card φ.range * Nat.card K := by
    rw [← Subgroup.card_mul_index K, Subgroup.index_ker, mul_comm]
  have hexp : k - 1 + (m - 1) * k = Nat.card α - 1 := by
    rw [Nat.sub_mul, one_mul, mul_comm m k] at *
    have : k ≤ k * m := Nat.le_mul_of_pos_right k (by omega)
    omega
  calc Nat.card G = Nat.card φ.range * Nat.card K := hGc
    _ ≤ d ^ (k - 1) * (d ^ (m - 1)) ^ k := Nat.mul_le_mul hφ hK'
    _ = d ^ (Nat.card α - 1) := by rw [← pow_mul, ← pow_add, hexp]

/-- A Johnson product in `Γ̂_d` obeys the bound. -/
theorem order_johnson {d : ℕ} (hd : 1 ≤ d) {α : Type} [Finite α] (ih : OrderIH d (Nat.card α))
    (G : Subgroup (Perm α)) (hG : GammaHat d G) {m k r : ℕ} (e : α ≃ JohnsonTuple m k r)
    (hm : 5 ≤ m) (hk : 1 ≤ k) (hkm : 2 * k < m) (hr : 1 ≤ r) (hS : WreathStructure G e) :
    Nat.card G ≤ d ^ (Nat.card α - 1) := by
  have h2 : k < m := by omega
  have hmd : m ≤ d := alternating_section_le hS hk h2 hr hm hG
  have hcardα : Nat.card α = m.choose k ^ r := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_pi, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Fintype.card_finset_len, Fintype.card_fin]
  have hmr : m * r ≤ Nat.card α := by
    have h3 : r ≤ m ^ (r - 1) := by
      have : r - 1 < m ^ (r - 1) := Nat.lt_pow_self (by omega)
      omega
    calc m * r ≤ m * m ^ (r - 1) := Nat.mul_le_mul_left _ h3
      _ = m ^ r := by rw [← pow_succ', Nat.sub_add_cancel hr]
      _ ≤ m.choose k ^ r := Nat.pow_le_pow_left (le_choose hk h2) r
      _ = Nat.card α := hcardα.symm
  have hrn : r < Nat.card α := by
    nlinarith
  have hK := ih.range (β := Fin r) hG (by simpa using hr) (by simpa using hrn)
    (wreathPerm hS hk h2)
  rw [Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin] at hK
  have hF := factorial_le_pow_pred hmd (by omega)
  calc Nat.card G ≤ Nat.card (wreathPerm hS hk h2).range * m.factorial ^ r :=
        card_le_range_mul hS hk h2
    _ ≤ d ^ (r - 1) * (d ^ (m - 1)) ^ r := Nat.mul_le_mul hK (Nat.pow_le_pow_left hF r)
    _ = d ^ (r - 1 + (m - 1) * r) := by rw [← pow_mul, ← pow_add]
    _ ≤ d ^ (Nat.card α - 1) := by
      refine Nat.pow_le_pow_right hd ?_
      have h3 : (m - 1) * r = m * r - r := by rw [Nat.sub_mul, one_mul]
      have h4 : r ≤ m * r := Nat.le_mul_of_pos_left r (by omega)
      omega

/-- The primitive step. -/
theorem order_primitive {d : ℕ} (hd : 6 ≤ d) {α : Type} [Finite α] [Nontrivial α]
    (ih : OrderIH d (Nat.card α)) (G : Subgroup (Perm α)) (hG : GammaHat d G)
    (hp : IsPreprimitive G α) : Nat.card G ≤ d ^ (Nat.card α - 1) := by
  have h2 : 2 ≤ Nat.card α := Finite.one_lt_card
  rcases Nat.lt_or_ge d (Nat.card α) with hlt | hle
  · have hsix : 6 ^ (Nat.card α - 1) ≤ d ^ (Nat.card α - 1) := Nat.pow_le_pow_left hd _
    rcases marotiFull G hp with ⟨m, k, r, e, hm, hk, hkm, hr, hS⟩ | ⟨hc, h11⟩ | hc
    · exact order_johnson (by omega) ih G hG e hm hk hkm hr hS
    · exact (hc.trans (pow_seven_le_six_pow h11)).trans hsix
    · exact (hc.le.trans (pow_log_le_six_pow (by omega))).trans hsix
  · refine le_trans ?_ (factorial_le_pow_pred hle (by omega))
    calc Nat.card G ≤ Nat.card (Perm α) := Subgroup.card_le_card_group G
      _ = (Nat.card α).factorial := Nat.card_perm

theorem card_le_pow_aux {d : ℕ} (hd : 6 ≤ d) (n : ℕ) : ∀ (α : Type) [Finite α], Nat.card α = n →
    1 ≤ n → ∀ G : Subgroup (Perm α), GammaHat d G → Nat.card G ≤ d ^ (n - 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro α _ hα hn G hG
  subst hα
  have ih' : OrderIH d (Nat.card α) := fun β _ h1 hlt G hG => ih _ hlt β rfl h1 G hG
  by_cases hnt : Nontrivial G
  swap
  · rw [not_nontrivial_iff_subsingleton] at hnt
    rw [Nat.card_unique]
    exact Nat.one_le_pow _ _ (by omega)
  by_cases ht : IsPretransitive G α
  swap
  · have hex : ∃ a b : α, ∀ g : G, g • a ≠ b := by
      by_contra h
      push Not at h
      exact ht ⟨fun a b => h a b⟩
    obtain ⟨a, b, hab⟩ := hex
    refine order_intransitive (by omega) ih' G hG (orbit G a) ?_ ⟨a, mem_orbit_self a⟩ ⟨b, ?_⟩
    · intro g x
      rw [← orbit_eq_iff, orbit_smul, orbit_eq_iff]
    · rintro ⟨g, hg⟩
      exact hab g hg
  by_cases hp : IsPreprimitive G α
  · have : Nontrivial α := by
      obtain ⟨g, hg⟩ := exists_ne (1 : G)
      by_contra hs
      rw [not_nontrivial_iff_subsingleton] at hs
      exact hg (Subtype.ext (Equiv.ext fun x => Subsingleton.elim _ _))
    exact order_primitive hd ih' G hG hp
  · have hex : ∃ B : Set α, IsBlock G B ∧ ¬ IsTrivialBlock B := by
      by_contra h
      push Not at h
      exact hp { toIsPretransitive := ht, isTrivialBlock_of_isBlock := fun hB => h _ hB }
    obtain ⟨B, hB, hBnt⟩ := hex
    exact order_imprimitive ih' G hG B hB hBnt

/-- **GNS Lemma 2.2.** For `d ≥ 6`, a subgroup of `Sym(n)` in `Γ̂_d` has order at most `d^(n-1)`. -/
theorem card_le_pow {d : ℕ} (hd : 6 ≤ d) {α : Type} [Finite α] [Nonempty α]
    (G : Subgroup (Perm α)) (hG : GammaHat d G) : Nat.card G ≤ d ^ (Nat.card α - 1) :=
  card_le_pow_aux hd _ α rfl Nat.card_pos G hG

end GI.Degree
