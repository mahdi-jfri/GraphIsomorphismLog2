module

public import Workspace.Impl.TermJPair

@[expose] public section

/-!
# A type matching read off from a 0/1 matrix (the matching of the `J`-step)

The local transporters of one label element `h` give a 0/1 matrix `M a j` ("row `x_a` has a
transporter to `y_j` in the class `h N`"). It has the *rectangle property*: `M a j`, `M a' j`
and `M a j'` give `M a' j'` (compose the transporters). The paper chooses "a prescribed type
matching `σ`"; here one is read off by ranks:

* the **rank** of a row `a` is the number of earlier rows equal to it;
* `tmJMatch M a` is the column of row `a` with index `rank a` among the columns of row `a`.

`tmJMatch_spec`: if the matrix has the rectangle property and some bijection `π*` has
`M a (π* a)` for all `a`, then `tmJMatch` is a bijection with `M a (tmJMatch a)` for all `a`.
Rows of one type are equal, have the same columns, and get distinct ranks; the class of a row
has as many columns as rows (through `π*`), so the rank is in range.
-/

namespace GI.Impl

variable {q : ℕ} (M : Fin q → Fin q → Bool)

/-- The columns of row `a`, in increasing order. -/
def tmJCols (a : Fin q) : List (Fin q) := (List.finRange q).filter (M a)

/-- The rank of row `a`: the number of earlier rows equal to it. -/
def tmJRank (a : Fin q) : ℕ := ((List.finRange q).filter (fun a' => decide (a' < a) &&
  decide (M a' = M a))).length

/-- The matched column of row `a` (or `0`-default when out of range). -/
def tmJMatchO (a : Fin q) : Option (Fin q) := (tmJCols M a)[tmJRank M a]?

theorem tmJCols_nodup (a : Fin q) : (tmJCols M a).Nodup :=
  (List.nodup_finRange q).filter _

theorem mem_tmJCols {a j : Fin q} : j ∈ tmJCols M a ↔ M a j = true := by
  simp [tmJCols]

theorem tmJRank_eq_card (a : Fin q) :
    tmJRank M a = (Finset.univ.filter (fun a' => a' < a ∧ M a' = M a)).card := by
  unfold tmJRank
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange q).filter _)]
  congr 1
  ext a'
  simp

theorem tmJCols_length (a : Fin q) :
    (tmJCols M a).length = (Finset.univ.filter (fun j => M a j = true)).card := by
  unfold tmJCols
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange q).filter _)]
  congr 1
  ext j
  simp

variable {M}

/-- **The matching.** -/
theorem tmJMatch_spec
    (hrect : ∀ a a' j j', M a j = true → M a' j = true → M a j' = true → M a' j' = true)
    (π : Equiv.Perm (Fin q)) (hπ : ∀ a, M a (π a) = true) :
    ∃ σ : Equiv.Perm (Fin q), ∀ a, tmJMatchO M a = some (σ a) ∧ M a (σ a) = true := by
  -- rows sharing a column are equal
  have hrow : ∀ a a' j, M a j = true → M a' j = true → M a' = M a := by
    intro a a' j h1 h2
    funext j'
    apply Bool.eq_iff_iff.2
    exact ⟨fun h => hrect a' a j j' h2 h1 h, fun h => hrect a a' j j' h1 h2 h⟩
  -- the rank is in range
  have hlt : ∀ a, tmJRank M a < (tmJCols M a).length := by
    intro a
    rw [tmJRank_eq_card, tmJCols_length]
    have h1 : (Finset.univ.filter (fun a' => a' < a ∧ M a' = M a)).card <
        (Finset.univ.filter (fun a' => M a' = M a)).card := by
      apply Finset.card_lt_card
      refine ⟨fun a' ha' => ?_, fun h => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha' ⊢; exact ha'.2
      · have := h (show a ∈ Finset.univ.filter (fun a' => M a' = M a) by simp)
        simp at this
    have h2 : (Finset.univ.filter (fun a' => M a' = M a)).card ≤
        (Finset.univ.filter (fun j => M a j = true)).card := by
      apply Finset.card_le_card_of_injOn π
      · intro a' ha'
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha' ⊢
        rw [← ha']; exact hπ a'
      · intro a1 _ a2 _ h; exact π.injective h
    omega
  set f : Fin q → Fin q := fun a => (tmJCols M a)[tmJRank M a]'(hlt a)
  have hfM : ∀ a, M a (f a) = true := fun a =>
    (mem_tmJCols M).1 (List.getElem_mem _)
  -- rows of the same class have distinct ranks
  have hrank : ∀ a a', M a' = M a → a < a' → tmJRank M a < tmJRank M a' := by
    intro a a' he hlt'
    rw [tmJRank_eq_card, tmJRank_eq_card]
    apply Finset.card_lt_card
    refine ⟨fun b hb => ?_, fun h => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact ⟨hb.1.trans hlt', hb.2.trans he.symm⟩
    · have := h (show a ∈ Finset.univ.filter (fun b => b < a' ∧ M b = M a') by
        simp [hlt', he])
      simp at this
  have hinj : Function.Injective f := by
    intro a a' h
    have he : M a' = M a := hrow a a' (f a) (hfM a) (by rw [h]; exact hfM a')
    have hc : tmJCols M a' = tmJCols M a := by simp [tmJCols, he]
    have hr : tmJRank M a = tmJRank M a' := by
      have h' : (tmJCols M a)[tmJRank M a]'(hlt a) =
          (tmJCols M a)[tmJRank M a']'(by rw [← hc]; exact hlt a') := by
        change f a = _
        rw [h]
        simp only [f]
        congr 1
      exact (List.Nodup.getElem_inj_iff (tmJCols_nodup M a)).1 h'
    rcases lt_trichotomy a a' with hlt' | heq | hgt
    · exact absurd hr (hrank a a' he hlt').ne
    · exact heq
    · exact absurd hr.symm (hrank a' a he.symm hgt).ne
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.1 hinj
  refine ⟨Equiv.ofBijective f hbij, fun a => ⟨?_, hfM a⟩⟩
  simp [tmJMatchO, f, List.getElem?_eq_getElem (hlt a)]

end GI.Impl
