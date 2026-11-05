module

public import Workspace.Cited.DesignLemma
public import Workspace.Proved.DesignFisher
public import Workspace.Proved.DesignTuples

@[expose] public section

/-!
# The large clique lemma

We prove the Design Lemma (`GI.Cited.DesignLemma`) by contradiction, so we assume that both of
its outcomes fail. `DesignCtx` collects the hypotheses together with these two failures.

For `x ∈ Γ^ℓ`, `designDom c α x` is the set of points whose class in the vertex coloring
`z ↦ c(x, z, …, z)` has at least `α n` points. Since `α n > n/2`, it is one color class
(`designDom_eq`). Since outcome (a) fails, it is nonempty for `ℓ < k`. Since outcome (b) fails,
the pair coloring `(z₁, z₂) ↦ c(x, z₁, z₂, …, z₂)` is constant on its pairs of distinct points
for `ℓ + 1 < k` (`designClique`).

The main result here is the large clique lemma ([H, Lemma 5.2]) in the form we need,
`designTwin`: for `z` outside `designDom c α x`, the coloring `w ↦ c(x, z, w, …, w)` is constant
on `designDom c α x`. It is the only result of this file used later, with the basic facts
about `designDom`.
-/

namespace GI.Proved

open Finset GI.Cited

variable {n k ℓ : ℕ} {c : (Fin k → Fin n) → ℕ} {α : ℝ}

/-- The hypotheses of the Design Lemma, together with the failure of both of its outcomes. -/
structure DesignCtx (n k : ℕ) (c : (Fin k → Fin n) → ℕ) (α : ℝ) : Prop where
  hk : 2 ≤ k
  hkn : 2 * k ≤ n
  hα : 1 / 2 < α
  conf : IsConfiguration c
  coh : IsCoherent c
  notA : ∀ ℓ < k, ∀ x : Fin ℓ → Fin n, ∃ j : ℕ,
    α * n ≤ ((univ.filter fun z => skel₁ c x z = j).card : ℝ)
  notB : ∀ ℓ, ℓ + 1 < k → ∀ x : Fin ℓ → Fin n, ∀ j : ℕ,
    α * n ≤ ((univ.filter fun z => skel₁ c x z = j).card : ℝ) →
    ∀ u v w y : Fin n, skel₁ c x u = j → skel₁ c x v = j → skel₁ c x w = j →
      skel₁ c x y = j → u ≠ v → w ≠ y → skel₂ c x u v = skel₂ c x w y

/-- The points whose class in `z ↦ c(x, z, …, z)` has at least `α n` points. -/
noncomputable def designDom (c : (Fin k → Fin n) → ℕ) (α : ℝ) (x : Fin ℓ → Fin n) : Finset (Fin n) :=
  univ.filter fun z => α * n ≤ ((univ.filter fun z' => skel₁ c x z' = skel₁ c x z).card : ℝ)

/-- Two sets with at least `α n > n/2` points each meet. -/
theorem designMeet (hα : 1 / 2 < α) {A B : Finset (Fin n)} (hA : α * n ≤ (A.card : ℝ))
    (hB : α * n ≤ (B.card : ℝ)) (hne : A.Nonempty) : (A ∩ B).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at h
  have hcard : A.card + B.card ≤ n := by
    rw [← card_union_of_disjoint h]
    simpa using card_le_univ (A ∪ B)
  have hcard' : (A.card : ℝ) + B.card ≤ n := by exact_mod_cast hcard
  obtain ⟨a, _⟩ := hne
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt
  nlinarith

/-- The size of `{a ∈ s : P a}`, counted on the subtype of `s`, when `P` implies `a ∈ s`. -/
theorem designCard_subtype {β : Type*} [Fintype β] (s : Finset β) (P : β → Prop)
    [DecidablePred P] (hP : ∀ a, P a → a ∈ s) :
    (univ.filter fun a : s => P a.1).card = (univ.filter P).card := by
  have : (univ.filter fun a : s => P a.1).map (Function.Embedding.subtype _) =
      univ.filter P := by
    ext a
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro h
      exact ⟨⟨a, hP a h⟩, h, rfl⟩
  rw [← this, card_map]

section

variable (H : DesignCtx n k c α)
include H

/-- Points of `designDom c α x` have the same color. -/
theorem designDom_eq (x : Fin ℓ → Fin n) {z z' : Fin n} (hz : z ∈ designDom c α x)
    (hz' : z' ∈ designDom c α x) : skel₁ c x z = skel₁ c x z' := by
  simp only [designDom, mem_filter, mem_univ, true_and] at hz hz'
  obtain ⟨a, ha⟩ := designMeet H.hα hz hz' ⟨z, by simp⟩
  simp only [mem_inter, mem_filter, mem_univ, true_and] at ha
  rw [← ha.1, ha.2]

omit H in
/-- A point with the color of a point of `designDom c α x` is in it. -/
theorem designDom_of (x : Fin ℓ → Fin n) {z z' : Fin n} (hz : z ∈ designDom c α x)
    (h : skel₁ c x z' = skel₁ c x z) : z' ∈ designDom c α x := by
  simp only [designDom, mem_filter, mem_univ, true_and] at hz ⊢
  rw [h]
  exact hz

omit H in
/-- `designDom c α x` has at least `α n` points if it is nonempty. -/
theorem designDom_card (x : Fin ℓ → Fin n) {z : Fin n} (hz : z ∈ designDom c α x) :
    α * n ≤ ((designDom c α x).card : ℝ) := by
  have hsub : (univ.filter fun z' => skel₁ c x z' = skel₁ c x z) ⊆ designDom c α x := by
    intro z' hz'
    exact designDom_of x hz (mem_filter.mp hz').2
  have h1 := card_le_card hsub
  have h2 : α * n ≤ ((univ.filter fun z' => skel₁ c x z' = skel₁ c x z).card : ℝ) := by
    simpa [designDom] using hz
  calc α * n ≤ _ := h2
    _ ≤ _ := by exact_mod_cast h1

/-- `designDom c α x` is nonempty for `ℓ < k`, since outcome (a) fails. -/
theorem designDom_nonempty {x : Fin ℓ → Fin n} (hℓ : ℓ < k) : ∃ z, z ∈ designDom c α x := by
  obtain ⟨j, hj⟩ := H.notA ℓ hℓ x
  have hn : (0 : ℝ) < α * n := by
    have : (4 : ℝ) ≤ n := by exact_mod_cast (by have := H.hk; have := H.hkn; omega : 4 ≤ n)
    have := H.hα
    nlinarith
  have hpos : 0 < (univ.filter fun z => skel₁ c x z = j).card := by
    have : (0 : ℝ) < ((univ.filter fun z => skel₁ c x z = j).card : ℝ) := lt_of_lt_of_le hn hj
    exact_mod_cast this
  obtain ⟨z, hz⟩ := card_pos.mp hpos
  have hzj := (mem_filter.mp hz).2
  refine ⟨z, ?_⟩
  simp only [designDom, mem_filter, mem_univ, true_and]
  rw [hzj]
  exact hj

/-- The pair coloring is constant on pairs of distinct points of `designDom c α x`, since
outcome (b) fails. -/
theorem designClique {x : Fin ℓ → Fin n} (hℓ : ℓ + 1 < k) {u v w y : Fin n}
    (hu : u ∈ designDom c α x) (hv : v ∈ designDom c α x) (hw : w ∈ designDom c α x)
    (hy : y ∈ designDom c α x) (huv : u ≠ v) (hwy : w ≠ y) :
    skel₂ c x u v = skel₂ c x w y := by
  have hj : α * n ≤ ((univ.filter fun z => skel₁ c x z = skel₁ c x u).card : ℝ) := by
    simpa [designDom] using hu
  exact H.notB ℓ hℓ x _ hj u v w y rfl (designDom_eq H x hv hu) (designDom_eq H x hw hu)
    (designDom_eq H x hy hu) huv hwy

/-- **The large clique lemma** ([H, Lemma 5.2], the form we need). Let `ℓ + 1 < k` and
`z ∉ designDom c α x`. Then `w ↦ c(x, z, w, …, w)` is constant on `designDom c α x`.

Suppose not, and let `i = c(x, z, w, …, w)` for some `w` in `C = designDom c α x`. For `z'`
in the class `D` of `z`, the blocks `{q ∈ C : c(x, z', q, …, q) = i}` form a design on `C`:
by coherence every point is in `r` blocks and every two distinct points are in `l` blocks, and
`l < r` since `z` gives a block that contains `w` but not some `w' ∈ C`. Fisher's inequality
(`designFisher`) gives `|C| ≤ |D|`. But `C` and `D` are disjoint classes and `|C| > n/2`. -/
theorem designTwin (hℓ : ℓ + 1 < k) (x : Fin ℓ → Fin n) {z : Fin n}
    (hz : z ∉ designDom c α x) {w w' : Fin n} (hw : w ∈ designDom c α x)
    (hw' : w' ∈ designDom c α x) : skel₂ c x z w = skel₂ c x z w' := by
  classical
  by_contra hne
  have hℓ' : ℓ < k := by omega
  set i := skel₂ c x z w with hi
  set C := designDom c α x with hC
  set D := univ.filter fun z' => skel₁ c x z' = skel₁ c x z with hD
  -- A point `z'` with `c(x, z', q, …, q) = i` is in the class `D` of `z`.
  have hBD : ∀ z' q, skel₂ c x z' q = i → z' ∈ D := by
    intro z' q e
    have := H.conf.2 _ _ e (designProj ℓ hℓ')
    simp only [designPad₂_proj] at this
    change z' ∈ univ.filter (fun z' => skel₁ c x z' = skel₁ c x z)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, this⟩
  set r := (univ.filter fun z' => skel₂ c x z' w = i).card with hr
  set l := (univ.filter fun z' => skel₂ c x z' w = i ∧ skel₂ c x z' w' = i).card with hl
  -- Every point of `C` is in `r` blocks.
  have hrq : ∀ q ∈ C, (univ.filter fun z' => skel₂ c x z' q = i).card = r := by
    intro q hq
    have e : c (padTuple x q) = c (padTuple x w) := designDom_eq H x hq hw
    have := designCount H.conf H.coh e ⟨ℓ, hℓ'⟩ ⟨ℓ, hℓ'⟩ id id i i
    simp only [Function.comp_id, and_self, designUpdate_pad] at this
    exact this
  -- Every two distinct points of `C` are together in `l` blocks.
  have hww' : w ≠ w' := fun e => hne (by rw [hi, e])
  have hlq : ∀ q ∈ C, ∀ q' ∈ C, q ≠ q' →
      (univ.filter fun z' => skel₂ c x z' q = i ∧ skel₂ c x z' q' = i).card = l := by
    intro q hq q' hq' hqq
    have e : c (padTuple₂ x q q') = c (padTuple₂ x w w') :=
      designClique H hℓ hq hq' hw hw' hqq hww'
    have := designCount H.conf H.coh e ⟨ℓ + 1, hℓ⟩ ⟨ℓ, hℓ'⟩ (designSwapMap ℓ hℓ) id i i
    simp only [Function.comp_id, designUpdate_pad₂, designUpdate_pad₂_succ] at this
    exact this
  -- The block of `z` contains `w` but not `w'`, so `l < r`.
  have hlr : l < r := by
    apply card_lt_card
    rw [Finset.ssubset_iff_of_subset (fun a ha => by
      simp only [mem_filter, mem_univ, true_and] at ha ⊢; exact ha.1)]
    refine ⟨z, by simp [hi], ?_⟩
    simp only [mem_filter, mem_univ, true_and, not_and]
    exact fun _ e => hne (by rw [e])
  -- Fisher's inequality.
  have hF := designFisher (ι := C) (κ := D) (fun z' q => skel₂ c x z'.1 q.1 = i) r l hlr
    (fun q => by
      rw [designCard_subtype D (fun z' => skel₂ c x z' q.1 = i) (fun z' e => hBD z' q.1 e)]
      exact hrq q.1 q.2)
    (fun q q' hqq => by
      rw [designCard_subtype D (fun z' => skel₂ c x z' q.1 = i ∧ skel₂ c x z' q'.1 = i)
        (fun z' e => hBD z' q.1 e.1)]
      exact hlq q.1 q.2 q'.1 q'.2 (fun e => hqq (Subtype.ext e)))
  simp only [Fintype.card_coe] at hF
  -- But `C` and `D` are disjoint, and both have more than `n/2` points.
  have hCcard := designDom_card x hw
  have hDcard : α * n ≤ (D.card : ℝ) := le_trans hCcard (by exact_mod_cast hF)
  obtain ⟨a, ha⟩ := designMeet H.hα hCcard hDcard ⟨w, hw⟩
  rw [mem_inter] at ha
  exact hz (designDom_of x ha.1 (mem_filter.mp ha.2).2.symm)

end

end GI.Proved
