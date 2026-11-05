module

public import Workspace.BochertIndex
public import Workspace.AlternatingSections
public import Mathlib.Data.Nat.Choose.Bounds
public import Workspace.DiagonalCarrier
public import Workspace.RectangleLeftCap

@[expose] public section

/-!
# Alternating-section width of a primitive nongiant group

A primitive group `P ≤ Sym(D)` that does not contain `Alt(D)` has
alternating-section width at most `(N+2)|D|/(2N)`, i.e. a little above `|D|/2`,
once `|D| ≥ 4·4^N + 8`.

This replaces the paper's use of Cameron--Maróti in Lemma A.12 ("Apply
Cameron--Maróti only as a structural bound"): the lemma needs only width at most
`β q` with a fixed `β > 1/2`. The proof uses Bochert's bound
`[Sym(D) : P] ≥ ⌊(|D|+1)/2⌋!` (`GI.Bochert.factorial_le_index_of_isPreprimitive`,
proved without CFSG) and the factorial order of an alternating section.
-/

namespace GI.PrimitiveWidth

open Equiv
open scoped Pointwise

/-- The numerical core: `2 d! < t! h!` with `h = ⌊(d+1)/2⌋` when `t` exceeds
`(N+2)d/(2N)`, `t ≤ d`, `N ≥ 4`, and `d ≥ 4·4^N + 8`. -/
theorem factorial_gap {d t N : ℕ} (hN : 4 ≤ N) (hd : 4 * 4 ^ N + 8 ≤ d)
    (ht : (N + 2) * d < 2 * N * t) (htd : t ≤ d) :
    2 * d.factorial < t.factorial * ((d + 1) / 2).factorial := by
  obtain ⟨j, rfl⟩ : ∃ j, d = t + j := ⟨d - t, by omega⟩
  obtain ⟨h, hh⟩ : ∃ h, h = (t + j + 1) / 2 := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = (t + j) / 4 := ⟨_, rfl⟩
  rw [← hh]
  -- `2 N j < (N - 2) d`, so `2 j < d`.
  have hNj : 2 * N * j + (N + 2) * (t + j) < 2 * N * (t + j) := by nlinarith
  have hjh : j ≤ h := by
    by_contra hc
    have h2 : t + j < 2 * j := by omega
    nlinarith
  obtain ⟨m, hm⟩ : ∃ m, m = max j e := ⟨_, rfl⟩
  have hmh : m ≤ h := by rw [hm]; exact max_le hjh (by omega)
  -- `d! ≤ 2^d t! j!`
  have hchoose : (t + j).factorial = (t + j).choose t * (t.factorial * j.factorial) := by
    rw [← Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right t j), Nat.add_sub_cancel_left]
    ring
  have hc2 : (t + j).choose t ≤ 2 ^ (t + j) := Nat.choose_le_two_pow _ t
  -- `m! (m+1)^(h-m) ≤ h!` and `j! ≤ m!`
  have hfac : m.factorial * (m + 1) ^ (h - m) ≤ h.factorial := by
    have := Nat.factorial_mul_pow_le_factorial (m := m) (n := h - m)
    rwa [Nat.add_sub_cancel' hmh] at this
  have hjm : j.factorial ≤ m.factorial := Nat.factorial_le (by rw [hm]; exact le_max_left _ _)
  -- `2^(d+1) < (m+1)^(h-m)`
  have hbase : 2 ^ (2 * N) ≤ m + 1 := by
    have h4 : 4 ^ N ≤ e := by omega
    have h2 : 2 ^ (2 * N) = 4 ^ N := by rw [pow_mul]; norm_num
    have : e ≤ m := by rw [hm]; exact le_max_right _ _
    omega
  have hexp : t + j + 2 ≤ 2 * N * (h - m) := by
    rcases le_total j e with hj4 | hj4
    · have hm' : m = e := by rw [hm]; exact max_eq_right hj4
      rw [hm']
      have h2 : e ≤ h - e := by omega
      have h3 : 8 * e ≤ 2 * N * (h - e) := by nlinarith
      omega
    · have hm' : m = j := by rw [hm]; exact max_eq_left hj4
      rw [hm']
      obtain ⟨g, hg⟩ : ∃ g, g = h - j := ⟨_, rfl⟩
      have hhj : h = j + g := by omega
      rw [← hg]
      have h2h : t + j ≤ 2 * h := by omega
      rw [hhj] at h2h
      have hmul : N * (t + j) ≤ N * (2 * (j + g)) := Nat.mul_le_mul_left N h2h
      nlinarith
  have hpow : 2 ^ (t + j + 1) < (m + 1) ^ (h - m) := by
    calc 2 ^ (t + j + 1) < 2 ^ (2 * N * (h - m)) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ = (2 ^ (2 * N)) ^ (h - m) := by rw [pow_mul]
      _ ≤ (m + 1) ^ (h - m) := Nat.pow_le_pow_left hbase _
  have htpos := Nat.factorial_pos t
  have hjpos := Nat.factorial_pos j
  calc 2 * (t + j).factorial ≤ 2 * (2 ^ (t + j) * (t.factorial * j.factorial)) := by
        rw [hchoose]; exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hc2)
    _ = 2 ^ (t + j + 1) * (t.factorial * j.factorial) := by ring
    _ < (m + 1) ^ (h - m) * (t.factorial * j.factorial) :=
        Nat.mul_lt_mul_of_pos_right hpow (Nat.mul_pos htpos hjpos)
    _ ≤ (m + 1) ^ (h - m) * (t.factorial * m.factorial) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hjm)
    _ = t.factorial * (m.factorial * (m + 1) ^ (h - m)) := by ring
    _ ≤ t.factorial * h.factorial := Nat.mul_le_mul_left _ hfac

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A primitive group `P ≤ Sym(D)` not containing `Alt(D)` has every alternating
section of degree at most `(N+2)|D|/(2N)`, for `N ≥ 4` and `|D| ≥ 4·4^N + 8`. -/
theorem primitive_cap {P : Subgroup (Perm D)} (hP : MulAction.IsPreprimitive P D)
    (halt : ¬ alternatingGroup D ≤ P) {N : ℕ} (hN : 4 ≤ N)
    (hd : 4 * 4 ^ N + 8 ≤ Fintype.card D) :
    SectionCaps.Cap P ((N + 2) * Fintype.card D / (2 * N)) := by
  intro U t ht q onto
  set d := Fintype.card D
  by_contra hlt
  push Not at hlt
  have hlt' : (N + 2) * d < 2 * N * t := by
    rwa [Nat.div_lt_iff_lt_mul (by omega), mul_comm t] at hlt
  -- A section of degree `t` inside `Sym(D)` has `t ≤ d`.
  have htd : t ≤ d := SectionCaps.subgroup SectionCaps.permutations P U t ht q onto
  -- `t!/2 ≤ |U| ≤ |P|` and `|P| [Sym D : P] = d!` with `[Sym D : P] ≥ ⌊(d+1)/2⌋!`.
  have hsurj := Nat.card_le_card_of_surjective q onto
  have hU : Nat.card U ≤ Nat.card P := Subgroup.card_le_of_le (le_refl _) |>.trans
    (by exact Nat.card_le_card_of_injective U.subtype Subtype.val_injective)
  have hidx := GI.Bochert.factorial_le_index_of_isPreprimitive hP halt
  have hlag : Nat.card P * P.index = d.factorial := by
    rw [Subgroup.card_mul_index, Nat.card_perm, Nat.card_eq_fintype_card]
  haveI : Nontrivial (Fin t) := Fintype.one_lt_card_iff_nontrivial.mp (by simp; omega)
  have halt2 := two_mul_card_alternatingGroup (α := Fin t)
  rw [Fintype.card_perm, Fintype.card_fin, ← Nat.card_eq_fintype_card] at halt2
  have hcardD : Nat.card D = d := Nat.card_eq_fintype_card
  rw [hcardD] at hidx
  have hgap := factorial_gap hN hd hlt' htd
  have key : t.factorial * ((d + 1) / 2).factorial ≤ 2 * d.factorial := by
    calc t.factorial * ((d + 1) / 2).factorial
        = 2 * Nat.card (alternatingGroup (Fin t)) * ((d + 1) / 2).factorial := by rw [halt2]
      _ ≤ 2 * Nat.card P * P.index := by
        apply Nat.mul_le_mul (Nat.mul_le_mul_left 2 (hsurj.trans hU)) hidx
      _ = 2 * d.factorial := by rw [mul_assoc, hlag]
  omega

/-! ### Imprimitive groups -/

omit [Fintype D] [DecidableEq D] in
/-- Two points sent into a block by the same element lie in the same translate for
every element. -/
theorem block_same {P : Subgroup (Perm D)} {B : Set D} (hB : MulAction.IsBlock P B)
    {g : P} {x y : D} (hx : g • x ∈ B) (hy : g • y ∈ B) (h : P) :
    h • x ∈ B ↔ h • y ∈ B := by
  have key : ∀ {x y : D}, g • x ∈ B → g • y ∈ B → h • x ∈ B → h • y ∈ B := by
    intro x y hx hy hhx
    have e : (h * g⁻¹) • (g • x) ∈ B := by rwa [smul_smul, inv_mul_cancel_right]
    have hk := MulAction.isBlock_iff_smul_eq_of_mem.mp hB hx e
    have hm : (h * g⁻¹) • (g • y) ∈ (h * g⁻¹) • B := Set.smul_mem_smul_set hy
    rw [hk, smul_smul, inv_mul_cancel_right] at hm
    exact hm
  exact ⟨key hx hy, key hy hx⟩

/-- A transitive but imprimitive group `P ≤ Sym(D)` embeds in `Sym(u) ≀ Sym(v)` with
`uv = |D|` and `u, v ≥ 2`, so its alternating-section width is at most `|D|/2`. -/
theorem imprimitive_cap {P : Subgroup (Perm D)} [MulAction.IsPretransitive P D]
    (hnp : ¬ MulAction.IsPreprimitive P D) : SectionCaps.Cap P (Fintype.card D / 2) := by
  classical
  -- A nontrivial block `B`.
  obtain ⟨B, hB, hBnt⟩ : ∃ B : Set D, MulAction.IsBlock P B ∧ ¬ MulAction.IsTrivialBlock B := by
    by_contra hc
    push Not at hc
    exact hnp ⟨fun hB => hc _ hB⟩
  simp only [MulAction.IsTrivialBlock, not_or] at hBnt
  obtain ⟨hns, hnu⟩ := hBnt
  -- The partition into translates of `B`: `x ~ y` when every element sends both or
  -- neither into `B`.
  let p : GI.InvariantPartition P :=
    { setoid :=
        { r := fun x y => ∀ g : P, g • x ∈ B ↔ g • y ∈ B
          iseqv := ⟨fun _ _ => Iff.rfl, fun h g => (h g).symm, fun h h' g => (h g).trans (h' g)⟩ }
      preserved := by
        intro h x y hxy g
        have := hxy (g * h)
        simpa only [mul_smul, Subgroup.smul_def, Equiv.Perm.smul_def] using this }
  -- Every class is a translate `g⁻¹ • B`, of size `|B|`.
  have hclass : ∀ x : D, ∃ g : P, g • x ∈ B ∧ ∀ y, p.setoid.r y x ↔ g • y ∈ B := by
    intro x
    obtain ⟨b, hb⟩ : B.Nonempty := by
      by_contra he
      exact hns (Set.not_nonempty_iff_eq_empty.mp he ▸ Set.subsingleton_empty)
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P x b
    refine ⟨g, hg ▸ hb, fun y => ⟨fun hyx => (hyx g).mpr (hg ▸ hb), fun hy h =>
      (block_same hB hy (hg ▸ hb) h)⟩⟩
  have hfiber : ∀ x : D, Fintype.card {y : D // (⟦y⟧ : Quotient p.setoid) = ⟦x⟧} =
      Fintype.card B := by
    intro x
    obtain ⟨g, -, hg⟩ := hclass x
    apply Fintype.card_congr
    exact
      { toFun := fun y => ⟨g • y.val, (hg y.val).mp (Quotient.exact y.property)⟩
        invFun := fun z => ⟨g⁻¹ • z.val, Quotient.sound ((hg _).mpr (by
          rw [smul_inv_smul]; exact z.property))⟩
        left_inv := fun y => Subtype.ext (inv_smul_smul g y.val)
        right_inv := fun z => Subtype.ext (smul_inv_smul g z.val) }
  have hfiber' : ∀ c : Quotient p.setoid,
      Fintype.card {y : D // (⟦y⟧ : Quotient p.setoid) = c} = Fintype.card B := by
    intro c
    induction c using Quotient.inductionOn with
    | h x => exact hfiber x
  -- `|D| = (number of classes) · |B|`.
  have hcount : Fintype.card D = Fintype.card (Quotient p.setoid) * Fintype.card B := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (fun y : D => (⟦y⟧ : Quotient p.setoid))),
      Fintype.card_sigma]
    simp only [hfiber', Finset.sum_const, Finset.card_univ, smul_eq_mul]
  -- `|B| ≥ 2` since `B` is not a subsingleton.
  have hB2 : 2 ≤ Fintype.card B := by
    obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hns
    have : 1 < Fintype.card B :=
      Fintype.one_lt_card_iff.mpr ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
    omega
  -- At least two classes, since `B ≠ D`.
  have hk2 : 2 ≤ Fintype.card (Quotient p.setoid) := by
    obtain ⟨z, hz⟩ : ∃ z, z ∉ B := by
      by_contra h
      push Not at h
      exact hnu (Set.eq_univ_of_forall h)
    obtain ⟨a, ha⟩ : B.Nonempty := by
      by_contra he
      exact hns (Set.not_nonempty_iff_eq_empty.mp he ▸ Set.subsingleton_empty)
    have hne : (⟦z⟧ : Quotient p.setoid) ≠ ⟦a⟧ := by
      intro h
      have := (Quotient.exact h) 1
      simp only [one_smul] at this
      exact hz (this.mpr ha)
    have : 1 < Fintype.card (Quotient p.setoid) := Fintype.one_lt_card_iff.mpr ⟨_, _, hne⟩
    omega
  have hcap := GI.Carrier.partition_cap p (u := Fintype.card B) (fun c => (hfiber' c).le)
  apply SectionCaps.mono hcap
  apply max_le
  · rw [hcount, Nat.le_div_iff_mul_le (by norm_num)]
    exact Nat.mul_le_mul_left _ hB2
  · rw [hcount, Nat.le_div_iff_mul_le (by norm_num), mul_comm]
    exact Nat.mul_le_mul_right _ hk2

end GI.PrimitiveWidth
