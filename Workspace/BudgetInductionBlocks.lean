import Workspace.BudgetInductionBasic
import Workspace.BlockPartition
import Workspace.EqualFibers

namespace GI.BudgetInduction

open scoped Pointwise

variable {V : Type*} {H : Subgroup (Equiv.Perm V)}

/-- The preserved partition is constructed from translates of an actual
nonempty block of a transitive action. -/
def partitionOfBlock [MulAction.IsPretransitive H V] {B : Set V}
    (hB : MulAction.IsBlock H B) (hne : B.Nonempty) : InvariantPartition H where
  setoid :=
    { r := fun x y => ∃ g : H, x ∈ g • B ∧ y ∈ g • B
      iseqv :=
        { refl := by
            intro x
            obtain ⟨b, hb⟩ := hne
            obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq H b x
            exact ⟨g, Set.smul_mem_smul_set hb, Set.smul_mem_smul_set hb⟩
          symm := by rintro x y ⟨g, hx, hy⟩; exact ⟨g, hy, hx⟩
          trans := by
            rintro x y z ⟨g, hx, hy⟩ ⟨h, hy', hz⟩
            have he := hB.smul_eq_smul_of_nonempty ⟨y, hy, hy'⟩
            exact ⟨g, hx, he.symm ▸ hz⟩ } }
  preserved := by
    rintro h x y ⟨g, hx, hy⟩
    refine ⟨h * g, ?_, ?_⟩
    · change h • x ∈ (h * g) • B
      simpa only [mul_smul] using (Set.smul_mem_smul_set hx : h • x ∈ h • (g • B))
    · change h • y ∈ (h * g) • B
      simpa only [mul_smul] using (Set.smul_mem_smul_set hy : h • y ∈ h • (g • B))

theorem partitionOfBlock_label_iff [MulAction.IsPretransitive H V] {B : Set V}
    (hB : MulAction.IsBlock H B) {a : V} (ha : a ∈ B) (x : V) :
    (partitionOfBlock hB ⟨a, ha⟩).blockCover.label x =
      (partitionOfBlock hB ⟨a, ha⟩).blockCover.label a ↔ x ∈ B := by
  rw [InvariantPartition.same_block_iff]
  change (∃ g : H, x ∈ g • B ∧ a ∈ g • B) ↔ x ∈ B
  constructor
  · rintro ⟨g, hx, hag⟩
    have he : g • B = (1 : H) • B :=
      hB.smul_eq_smul_of_nonempty ⟨a, hag, by simpa using ha⟩
    simpa only [he, one_smul] using hx
  · intro hx
    exact ⟨1, by simpa using hx, by simpa using ha⟩

variable [Fintype V]

/-- Equal sizes and exact degree factorization follow from actual fiber
transport under the transitive source action. -/
theorem blockCover_card_factorization {B : Type*} [Fintype B]
    [MulAction.IsPretransitive H V] (c : BlockCover H B)
    (hsurj : Function.Surjective c.label) (a : V)
    [Fintype {x : V // c.label x = c.label a}] :
    Fintype.card B * Fintype.card {x : V // c.label x = c.label a} = Fintype.card V := by
  letI : MulAction H B := MulAction.compHom B c.project
  have heq : ∀ (h : H) (x : V), c.label (h • x) = h • c.label x := c.equivariant
  have ht : ∀ b d : B, ∃ h : H, h • b = d :=
    equivariant_quotient_transitive c.label hsurj heq (MulAction.exists_smul_eq H)
  simpa only [Nat.card_eq_fintype_card] using
    equal_fiber_card_factorization c.label heq ht (c.label a)

theorem blockCover_smaller_degrees {B : Type*} [Fintype B]
    [MulAction.IsPretransitive H V] (c : BlockCover H B)
    (hsurj : Function.Surjective c.label) (a : V)
    [Fintype {x : V // c.label x = c.label a}]
    (hb : 2 ≤ Fintype.card B)
    (hf : 2 ≤ Fintype.card {x : V // c.label x = c.label a}) :
    Fintype.card B < Fintype.card V ∧
      Fintype.card {x : V // c.label x = c.label a} < Fintype.card V := by
  have he := blockCover_card_factorization c hsurj a
  constructor <;> nlinarith

theorem sigma_blockCover {cutoff : ℕ} {C : ℝ} (hcutoff : 5 ≤ cutoff)
    (hC : 128 ≤ C)
    (ih : ∀ m < Fintype.card V, ∀ b : Fin m,
      (sigma cutoff b ⊤ : ℝ) ≤ degreeAllowance C m)
    {B : Type*} [Fintype B] [MulAction.IsPretransitive H V]
    (c : BlockCover H B) (hsurj : Function.Surjective c.label) (a : V)
    [Fintype {x : V // c.label x = c.label a}]
    (hb : 2 ≤ Fintype.card B)
    (hf : 2 ≤ Fintype.card {x : V // c.label x = c.label a}) :
    (sigma cutoff a H : ℝ) ≤ degreeAllowance C (Fintype.card V) := by
  have hsmaller := blockCover_smaller_degrees c hsurj a hb hf
  have htop := sigma_le_of_smaller_degree hcutoff ih hsmaller.1 c.project.range (c.label a)
  have hlocal := sigma_le_of_smaller_degree hcutoff ih hsmaller.2
    (c.localProject a).range (c.localBase a)
  have hsplit := c.sigma_block_le hcutoff a
  have hsplitR : (sigma cutoff a H : ℝ) ≤
      sigma cutoff (c.label a) c.project.range +
        sigma cutoff (c.localBase a) (c.localProject a).range := by exact_mod_cast hsplit
  have hsum := allowance_mul hC hb hf
  rw [blockCover_card_factorization c hsurj a] at hsum
  exact hsplitR.trans ((add_le_add htop hlocal).trans hsum)

/-- An actual nontrivial block gives at least two blocks and at least two
points in the active fiber; neither cardinal assertion is an input. -/
theorem partitionOfBlock_card_bounds [MulAction.IsPretransitive H V] {B : Set V}
    (hB : MulAction.IsBlock H B) {a : V} (ha : a ∈ B)
    (hnt : ¬ MulAction.IsTrivialBlock B) :
    let p := partitionOfBlock hB ⟨a, ha⟩
    2 ≤ Nat.card (Quotient p.setoid) ∧
      2 ≤ Nat.card {x : V // p.blockCover.label x = p.blockCover.label a} := by
  classical
  dsimp only
  let p := partitionOfBlock hB ⟨a, ha⟩
  letI : Fintype (Quotient p.setoid) := Fintype.ofFinite _
  letI : Fintype {x : V // p.blockCover.label x = p.blockCover.label a} := Fintype.ofFinite _
  have hnotall : B ≠ Set.univ := fun h => hnt (Or.inr h)
  have hnotss : ¬ B.Subsingleton := fun h => hnt (Or.inl h)
  obtain ⟨x, hx⟩ : ∃ x, x ∉ B := by
    by_contra hn
    push Not at hn
    exact hnotall (Set.eq_univ_of_forall hn)
  have hne : p.blockCover.label x ≠ p.blockCover.label a :=
    fun he => hx ((partitionOfBlock_label_iff hB ha x).mp he)
  letI : Nontrivial (Quotient p.setoid) := ⟨⟨_, _, hne⟩⟩
  letI : Nontrivial {x : V // p.blockCover.label x = p.blockCover.label a} := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    apply hnotss
    intro x hx y hy
    exact congrArg Subtype.val (@Subsingleton.elim _ hs
      ⟨x, (partitionOfBlock_label_iff hB ha x).mpr hx⟩
      ⟨y, (partitionOfBlock_label_iff hB ha y).mpr hy⟩)
  constructor <;> rw [Nat.card_eq_fintype_card] <;> exact Fintype.one_lt_card

/-- The entire imprimitive induction case. Failure of the standard Mathlib
primitive predicate produces the required block and both smaller actions. -/
theorem sigma_imprimitive {cutoff : ℕ} {C : ℝ} (hcutoff : 5 ≤ cutoff)
    (hC : 128 ≤ C)
    (ih : ∀ m < Fintype.card V, ∀ b : Fin m,
      (sigma cutoff b ⊤ : ℝ) ≤ degreeAllowance C m)
    (H : Subgroup (Equiv.Perm V)) [MulAction.IsPretransitive H V] (a : V)
    (hn : ¬ MulAction.IsPreprimitive H V) :
    (sigma cutoff a H : ℝ) ≤ degreeAllowance C (Fintype.card V) := by
  classical
  have hnot : ¬ ∀ (B : Set V), a ∈ B → MulAction.IsBlock H B → MulAction.IsTrivialBlock B := by
    intro hh
    exact hn (MulAction.IsPreprimitive.of_isTrivialBlock_base a (fun ha hb => hh _ ha hb))
  push Not at hnot
  obtain ⟨B, ha, hB, hnt⟩ := hnot
  let p := partitionOfBlock hB ⟨a, ha⟩
  letI : Fintype (Quotient p.setoid) := Fintype.ofFinite _
  letI : Fintype {x : V // p.blockCover.label x = p.blockCover.label a} := Fintype.ofFinite _
  have hc := partitionOfBlock_card_bounds hB ha hnt
  change 2 ≤ Nat.card (Quotient p.setoid) ∧
    2 ≤ Nat.card {x : V // p.blockCover.label x = p.blockCover.label a} at hc
  simp only [Nat.card_eq_fintype_card] at hc
  exact sigma_blockCover hcutoff hC ih p.blockCover p.label_surjective a hc.1 hc.2

end GI.BudgetInduction
