import Workspace.Impl.AggItemCfMath
import Workspace.Impl.AggItemCiPartT
import Workspace.Impl.AggItemStepWt

/-!
# Cases 2b and 3: the colored partitions of a branch

The objects of Cases 2b and 3 that are colored partitions are the vertex-class partitions of
outcome (a) of the Design Lemma: in Case 3 the object `designOut col t` is `classPart (skel₁ col x)`
for a prefix `x` of `t` (`itci_designOut_part`), and the object `orbitalOut` of Case 2b is never a
colored partition (`itci_orbitalOut_part`). So two partitions of a branch are
`classPart fX`, `classPart fY` with colors below `2 q^κ` (`itci_objOf_part`), and their values
weigh at most `itciVB` of the input weight (`itci_partV_wt`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring skel₁)

variable {Ω C : Type} {k q : ℕ}

theorem itci_designOut_part {κ ℓ : ℕ} {col : (Fin κ → Fin q) → ℕ} {t : Fin ℓ → Fin q}
    {z : ColPart (Fin q)} (h : designOut col t = .part z) :
    ∃ (m : ℕ) (x : Fin m → Fin q), z = classPart (skel₁ col x) := by
  unfold designOut at h
  split_ifs at h with h1 h2
  unfold designAt at h
  split_ifs at h
  cases h
  exact ⟨_, _, rfl⟩

theorem itci_orbitalOut_part {ℓ : ℕ} {R : Refiner2 q} {H : Subgroup (Perm (Fin q))}
    {t : Fin ℓ → Fin q} {z : ColPart (Fin q)} : orbitalOut R H t ≠ .part z := by
  unfold orbitalOut orbitalAt
  split_ifs <;> simp

section Ctx

variable {S : State Ω C} {L : SuppliedLabels S} {e : Ω ≃ Fin k} {c : C → ℕ} {K : ItSCtx k S L}

/-- **The partitions of a branch, one side at a time**: vertex-class partitions with colors
below `2 q^κ`. -/
theorem itci_objOf_sides (hK : K.OK e c) (hc : K.case = .twoB ∨ K.case = .three)
    {b : Fin (P₀.κ + 1) → Fin L.q} {oX oY : CfgOut L.q} (h : ItCfObjOf K b oX oY) :
    (∀ z, oX = .part z → ∃ f : Fin L.q → ℕ, z = classPart f ∧ ∀ a, f a < 2 * L.q ^ P₀.κ) ∧
      ∀ z, oY = .part z → ∃ f : Fin L.q → ℕ, z = classPart f ∧ ∀ a, f a < 2 * L.q ^ P₀.κ := by
  obtain ⟨Ag, hAg, ho, -, -⟩ := h
  rcases hc with hc | hc
  · rw [itCf_out_twoB hK hAg hc b rfl] at ho
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · rw [hz] at ho; exact absurd (Prod.mk.inj ho).1 itci_orbitalOut_part
    · rw [hz] at ho; exact absurd (Prod.mk.inj ho).2 itci_orbitalOut_part
  · rw [itCf_out_three hK hAg hc b] at ho
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · rw [hz] at ho
      obtain ⟨_, x, rfl⟩ := itci_designOut_part (Prod.mk.inj ho).1
      exact ⟨_, rfl, fun a => hK.dlt _⟩
    · rw [hz] at ho
      obtain ⟨_, x, rfl⟩ := itci_designOut_part (Prod.mk.inj ho).2
      exact ⟨_, rfl, fun a => hK.dlt' _⟩

/-- **The partitions of a branch** are vertex-class partitions with colors below `2 q^κ`. -/
theorem itci_objOf_part (hK : K.OK e c) (hc : K.case = .twoB ∨ K.case = .three)
    {b : Fin (P₀.κ + 1) → Fin L.q} {zX zY : ColPart (Fin L.q)}
    (h : ItCfObjOf K b (.part zX) (.part zY)) :
    ∃ fX fY : Fin L.q → ℕ, zX = classPart fX ∧ zY = classPart fY ∧
      (∀ a, fX a < 2 * L.q ^ P₀.κ) ∧ ∀ a, fY a < 2 * L.q ^ P₀.κ := by
  obtain ⟨h1, h2⟩ := itci_objOf_sides hK hc h
  obtain ⟨fX, rfl, hX⟩ := h1 zX rfl
  obtain ⟨fY, rfl, hY⟩ := h2 zY rfl
  exact ⟨fX, fY, rfl, rfl, hX, hY⟩

end Ctx

/-! ### Weights -/

/-- The bound on the colors' value of a partition, in `Q ≥ q` with `q^κ ≤ Q^64`. -/
def itciMB (Q : ℕ) : ℕ := Q * (4 * Q ^ 64 + 5) + 4

/-- The bound on the value of a partition. -/
def itciVB (Q : ℕ) : ℕ := 2 * (3 + (Q * (2 * (7 * Q + 4) + 1) + 4) + itciMB Q) + 7

theorem itci_col_wt {f : Fin q → ℕ} {κ Q : ℕ} (hf : ∀ a, f a < 2 * q ^ κ) (hq : q ≤ Q)
    (hp : q ^ κ ≤ Q ^ 64) : (encFun f).wt ≤ itciMB Q := by
  have h := wt_encFun_le f (B := 2 * Q ^ 64) (fun a => by have := hf a; omega)
  unfold itciMB
  have : q * (2 * (2 * Q ^ 64) + 5) ≤ Q * (4 * Q ^ 64 + 5) :=
    Nat.mul_le_mul hq (by omega)
  omega

theorem itci_blk_wt (z : ColPart (Fin q)) {Q : ℕ} (hq : q ≤ Q) :
    (itCfBlkV z).wt ≤ Q * (2 * (7 * Q + 4) + 1) + 4 := by
  classical
  unfold itCfBlkV
  have h := wt_list_le_of ((List.finRange q).map fun a => encFun fun b =>
      if b ∈ z.blk a then 1 else 0) (c := 7 * Q + 4) (fun v hv => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hv
    have := wt_encFun_le (fun b => if b ∈ z.blk a then 1 else 0) (B := 1)
      (fun b => by dsimp only; split_ifs <;> omega)
    have : q * (2 * 1 + 5) ≤ 7 * Q := by omega
    omega)
  simp only [List.length_map, List.length_finRange] at h
  have : q * (2 * (7 * Q + 4) + 1) ≤ Q * (2 * (7 * Q + 4) + 1) := Nat.mul_le_mul_right _ hq
  omega

/-- **The value of a partition with small colors.** -/
theorem itci_partV_wt {f : Fin q → ℕ} {κ Q : ℕ} (hf : ∀ a, f a < 2 * q ^ κ) (hq : q ≤ Q)
    (hp : q ^ κ ≤ Q ^ 64) : (itCfOutV (.part (classPart f))).wt ≤ itciVB Q := by
  show (Val.list [.nat 1, itCfBlkV (classPart f), encFun f]).wt ≤ _
  unfold itciVB
  have h1 := wt_list3_le (.nat 1) (itCfBlkV (classPart f)) (encFun f)
  have h2 := itci_blk_wt (classPart f) hq
  have h3 := itci_col_wt hf hq hp
  have h4 := wt_nat_le 1
  omega

/-! ### Kinds -/

/-- **The kind of an object** is the first entry of its value: `0`, `1` (partition) or `2`
(pair configuration). -/
theorem itci_kind (o : CfgOut q) : ∃ (t : ℕ) (xs : List Val), itCfOutV o = .list (.nat t :: xs) ∧
    (t = 2 ↔ ∃ X x₀, o = .pair X x₀) ∧ (t = 1 ↔ ∃ z, o = .part z) := by
  cases o with
  | none => exact ⟨0, [], rfl, by simp, by simp⟩
  | part z => exact ⟨1, _, rfl, by simp, by simp⟩
  | pair X x₀ => exact ⟨2, _, rfl, by simp, by simp⟩

theorem itci_none_wt : (itCfOutV (q := q) .none).wt ≤ 9 := by
  have := wt_list1_le (Val.nat 0); have := wt_nat_le 0
  show (Val.list [.nat 0]).wt ≤ 9; omega

/-- **The script of objects of different kinds**, or of two empty objects, is the empty
result. -/
theorem itci_sb_none {S : State Ω C} {L : GiantLabels S} (e : Ω ≃ Fin k) {oX oY : CfgOut L.q}
    (h2 : ¬ ((∃ X x₀, oX = .pair X x₀) ∧ ∃ Y y₀, oY = .pair Y y₀))
    (h1 : ¬ ((∃ z, oX = .part z) ∧ ∃ z, oY = .part z)) (ch : ItCfCh S L) :
    itCfSb e oX oY ch = .done ⟨[], []⟩ := by
  cases oX <;> cases oY <;> simp_all [itCfSb, cfgOutItem, AuxItem.script]

/-- **The script of two partitions** is that of their overcoset item. -/
theorem itci_sb_part {S : State Ω C} {L : GiantLabels S} (e : Ω ≃ Fin k)
    (zX zY : ColPart (Fin L.q)) (ch : ItCfCh S L) :
    itCfSb e (.part zX) (.part zY) ch = (objItem (P := P₀) zX zY : AuxItem P₀ S L).script := rfl

end GI.Impl
