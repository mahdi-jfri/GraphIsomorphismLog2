module

public import Workspace.SupportIndexGap
public import Workspace.PairComplement
public import Workspace.AlternatingSubsetTransitive

@[expose] public section

/-!
# Orbit and index lemmas for Lemma A.24

Setwise stabilizers of subsets in `Alt(α)` and their indices, small invariant
subsets of intransitive subgroups, and the minimum-index fact applied to the
embedded alternating group `Alt(c) ≤ Alt(α)`.
-/

namespace GI.SupportThresholds

open Equiv Equiv.Perm
open scoped Pointwise

attribute [local instance 2000] Subtype.fintype

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Binomial coefficients -/

/-- `choose m` increases on `[0, m/2]`. -/
theorem choose_le_choose_of_le_half {m i j : ℕ} (hij : i ≤ j) (hj : 2 * j ≤ m) :
    m.choose i ≤ m.choose j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem six_mul_choose_three (m : ℕ) : 6 * m.choose 3 = m * (m - 1) * (m - 2) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose m 3
  simp only [Nat.descFactorial, Nat.factorial, Nat.sub_zero] at h
  rw [← h]
  ring_nf

theorem two_mul_choose_two (m : ℕ) : 2 * m.choose 2 = m * (m - 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose m 2
  simp only [Nat.descFactorial, Nat.factorial, Nat.sub_zero] at h
  rw [← h]
  ring_nf

/-! ### Setwise stabilizers of subsets -/

/-- The index of the setwise stabilizer of `D` in `Alt(α)` is `C(m, |D|)`. -/
theorem index_setStabilizer (h3 : 3 ≤ Fintype.card α) (D : Finset α) :
    (MulAction.stabilizer (alternatingGroup α) D).index =
      (Fintype.card α).choose D.card := by
  rw [MulAction.index_stabilizer]
  have horbit : MulAction.orbit (alternatingGroup α) D =
      ↑(Finset.powersetCard D.card (Finset.univ : Finset α)) := by
    ext t
    simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · rintro ⟨g, rfl⟩
      change ((g : Perm α) • D).card = D.card
      exact Finset.card_smul_finset _ _
    · intro ht
      obtain ⟨p, hp⟩ := GI.AlternatingActions.exists_alternating_finset_eq h3 D t ht.symm
      exact ⟨p, hp⟩
  rw [horbit, Set.ncard_coe_finset, Finset.card_powersetCard, Finset.card_univ]

theorem mem_setStabilizer_singleton (a : α) (g : alternatingGroup α) :
    g ∈ MulAction.stabilizer (alternatingGroup α) ({a} : Finset α) ↔ (g : Perm α) a = a := by
  rw [MulAction.mem_stabilizer_iff]
  change (g : Perm α) • ({a} : Finset α) = {a} ↔ _
  rw [Finset.smul_finset_singleton, Finset.singleton_inj]
  rfl

theorem setStabilizer_singleton (a : α) :
    MulAction.stabilizer (alternatingGroup α) ({a} : Finset α) =
      MulAction.stabilizer (alternatingGroup α) a := by
  ext g
  rw [mem_setStabilizer_singleton, MulAction.mem_stabilizer_iff]
  rfl

theorem setStabilizer_pair (a b : α) (hab : a ≠ b) :
    MulAction.stabilizer (alternatingGroup α) ({a, b} : Finset α) = GI.Pairs.setwise a b hab := by
  ext g
  rw [GI.Pairs.mem_setwise, MulAction.mem_stabilizer_iff]
  change (g : Perm α) • ({a, b} : Finset α) = {a, b} ↔ _
  have hpair : (g : Perm α) • ({a, b} : Finset α) = {g.val a, g.val b} := by
    simp [Finset.smul_finset_def]
  rw [hpair, ← Finset.coe_inj]
  simp only [Finset.coe_pair, Set.pair_eq_pair_iff]

/-- A subset stabilized setwise by every element of `P`. -/
theorem le_setStabilizer_of_invariant (P : Subgroup (alternatingGroup α)) (D : Finset α)
    (hD : ∀ g ∈ P, ∀ x ∈ D, (g : Perm α) x ∈ D) :
    P ≤ MulAction.stabilizer (alternatingGroup α) D := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  change (g : Perm α) • D = D
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.mp hy
    exact hD g hg x hx
  · rw [Finset.card_smul_finset]

/-- An intransitive subgroup of `Alt(α)` stabilizes a nonempty subset of at
most half the points: one of its orbits, or the complement of one. -/
theorem exists_small_invariant (P : Subgroup (alternatingGroup α))
    (hP : ¬ MulAction.IsPretransitive (P.map (alternatingGroup α).subtype) α) :
    ∃ D : Finset α, 0 < D.card ∧ 2 * D.card ≤ Fintype.card α ∧
      P ≤ MulAction.stabilizer (alternatingGroup α) D := by
  classical
  have hnot : ∃ x y : α, ∀ g ∈ P, (g : Perm α) x ≠ y := by
    by_contra hn
    push Not at hn
    apply hP
    constructor
    intro x y
    obtain ⟨g, hg, hgx⟩ := hn x y
    exact ⟨⟨(g : Perm α), g, hg, rfl⟩, hgx⟩
  obtain ⟨x, y, hxy⟩ := hnot
  let O : Finset α := Finset.univ.filter fun z => ∃ g ∈ P, (g : Perm α) x = z
  have hxO : x ∈ O := Finset.mem_filter.mpr ⟨Finset.mem_univ _, 1, P.one_mem, rfl⟩
  have hyO : y ∉ O := by
    intro hy
    obtain ⟨g, hg, hgx⟩ := (Finset.mem_filter.mp hy).2
    exact hxy g hg hgx
  have hOinv : ∀ g ∈ P, ∀ z ∈ O, (g : Perm α) z ∈ O := by
    intro g hg z hz
    obtain ⟨h, hh, rfl⟩ := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, g * h, P.mul_mem hg hh, rfl⟩
  have hOcinv : ∀ g ∈ P, ∀ z ∈ Oᶜ, (g : Perm α) z ∈ Oᶜ := by
    intro g hg z hz
    rw [Finset.mem_compl] at hz ⊢
    intro hgz
    apply hz
    have := hOinv g⁻¹ (P.inv_mem hg) _ hgz
    change (g : Perm α).symm ((g : Perm α) z) ∈ O at this
    rwa [Equiv.symm_apply_apply] at this
  have hOc : Oᶜ.card + O.card = Fintype.card α := by
    rw [Finset.card_compl]; have := Finset.card_le_univ O; omega
  by_cases hsmall : 2 * O.card ≤ Fintype.card α
  · exact ⟨O, Finset.card_pos.mpr ⟨x, hxO⟩, hsmall, le_setStabilizer_of_invariant P O hOinv⟩
  · refine ⟨Oᶜ, Finset.card_pos.mpr ⟨y, Finset.mem_compl.mpr hyO⟩, by omega,
      le_setStabilizer_of_invariant P Oᶜ hOcinv⟩

/-! ### The embedded alternating group `Alt(c)` and the minimum-index fact -/

theorem mem_extend_range (c : Finset α) (g : alternatingGroup α) :
    g ∈ (GI.AlternatingSimple.extend c).range ↔ ∀ x, x ∉ c → (g : Perm α) x = x := by
  constructor
  · rintro ⟨p, rfl⟩ x hx
    exact ofSubtype_apply_of_not_mem p.val hx
  · intro hg
    have hpres : ∀ x : α, x ∈ c ↔ g.val x ∈ c := by
      intro x
      constructor
      · intro hx
        by_contra hgx
        have h2 : g.val x = x := g.val.injective (hg _ hgx)
        exact hgx (by rw [h2]; exact hx)
      · intro hgx
        by_contra hx
        rw [hg x hx] at hgx
        exact hx hgx
    have hsupp : ∀ x : α, g.val x ≠ x → x ∈ c := by
      intro x hx
      by_contra hc
      exact hx (hg x hc)
    let p : alternatingGroup c :=
      ⟨subtypePerm g.val (fun x => (hpres x).symm), by
        rw [mem_alternatingGroup, sign_subtypePerm g.val (fun x => (hpres x).symm) hsupp]
        exact g.property⟩
    refine ⟨p, Subtype.ext ?_⟩
    exact ofSubtype_subtypePerm (fun x => (hpres x).symm) hsupp

theorem extend_apply_coe (c : Finset α) (p : alternatingGroup c) (x : c) :
    ((GI.AlternatingSimple.extend c p : alternatingGroup α) : Perm α) x = (p : Perm c) x :=
  ofSubtype_apply_coe _ x

/-- **Minimum-index fact** for `T = Alt(c)` embedded in `Alt(α)`, `|c| ≥ 5`:
a subgroup `Q` with `[T : T ∩ Q] < |c|` contains `T`. -/
theorem extend_range_le_of_relIndex_lt (c : Finset α) (hc : 5 ≤ c.card)
    (Q : Subgroup (alternatingGroup α))
    (h : Q.relIndex (GI.AlternatingSimple.extend c).range < c.card) :
    (GI.AlternatingSimple.extend c).range ≤ Q := by
  set T := (GI.AlternatingSimple.extend c).range
  rw [← Subgroup.subgroupOf_eq_top]
  by_contra hne
  have hcard : Fintype.card c = c.card := by simp
  haveI : IsSimpleGroup (alternatingGroup c) :=
    GI.AlternatingSimple.isSimple (by rw [hcard]; exact hc)
  let e : alternatingGroup c ≃* T :=
    MonoidHom.ofInjective (GI.AlternatingSimple.extend_injective c)
  haveI : IsSimpleGroup T := e.symm.isSimpleGroup
  have hle := card_le_factorial_index (Q.subgroupOf T) hne
  have hT : Nat.card T = Nat.card (alternatingGroup c) := (Nat.card_congr e.toEquiv).symm
  haveI : Nontrivial c := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have h2 : 2 * Nat.card (alternatingGroup c) = c.card.factorial := by
    rw [Nat.card_eq_fintype_card, two_mul_card_alternatingGroup, Fintype.card_perm, hcard]
  change Nat.card T ≤ (Q.relIndex T).factorial at hle
  -- `|c|!/2 ≤ k!` with `k < |c|` is impossible.
  set r := c.card
  set k := Q.relIndex T
  have hk : k.factorial ≤ (r - 1).factorial := Nat.factorial_le (by omega)
  have hr : r.factorial = r * (r - 1).factorial := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    rw [Nat.factorial_succ]; congr 1; omega
  have hpos := Nat.factorial_pos (r - 1)
  have : r * (r - 1).factorial ≤ 2 * (r - 1).factorial := by omega
  nlinarith

end GI.SupportThresholds
