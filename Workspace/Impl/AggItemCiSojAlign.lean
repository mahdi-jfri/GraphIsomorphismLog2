module

public import Workspace.Impl.AggItemCiSojMath

@[expose] public section

/-!
# A fixed even alignment of the two rectangles

Order the three parts by their colors and then by label. The existing coloring
alignment matches equal positions. If it is odd, compose it with the first
nontrivial same-color transposition. The left side has at least three points, so
such a transposition exists. This fixes the alignment function used by the model.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Rectangle Equiv Equiv.Perm Finset

variable {q : ℕ}

/-- Colors of the two sides and the omitted labels. -/
def itcsSide (W R : Finset (Fin q)) (a : Fin q) : ℕ :=
  if a ∈ W then 2 else if a ∈ R then 1 else 0

@[simp] theorem itcs_side_left (W R : Finset (Fin q)) (a : Fin q) :
    itcsSide W R a = 2 ↔ a ∈ W := by
  unfold itcsSide
  split_ifs <;> simp_all

/-- Disjointness identifies the right-side color. -/
theorem itcs_side_right {W R : Finset (Fin q)} (hd : Disjoint W R) (a : Fin q) :
    itcsSide W R a = 1 ↔ a ∈ R := by
  unfold itcsSide
  by_cases ha : a ∈ W
  · have hn : a ∉ R := disjoint_left.1 hd ha
    simp [ha, hn]
  · simp [ha]

/-- Equal side sizes imply equal counts in the three-color encoding. -/
theorem itcs_side_counts {W R W' R' : Finset (Fin q)}
    (hd : Disjoint W R) (hd' : Disjoint W' R') (hW : W.card = W'.card)
    (hR : R.card = R'.card) (h3 : 3 ≤ W.card) :
    ItciCnt (itcsSide W R) (itcsSide W' R') := by
  obtain ⟨g, hgW, hgR⟩ := exists_even_alignment hd hd' hW hR (by omega)
  apply itci_cnt_of_map (σ := (g : Perm (Fin q)))
  intro a
  have hWa : (g : Perm (Fin q)) a ∈ W' ↔ a ∈ W := by
    change (g : Perm (Fin q)) a ∈ (W' : Set (Fin q)) ↔ a ∈ (W : Set (Fin q))
    rw [← hgW]
    exact (g : Perm (Fin q)).injective.mem_set_image
  have hRa : (g : Perm (Fin q)) a ∈ R' ↔ a ∈ R := by
    change (g : Perm (Fin q)) a ∈ (R' : Set (Fin q)) ↔ a ∈ (R : Set (Fin q))
    rw [← hgR]
    exact (g : Perm (Fin q)).injective.mem_set_image
  simp only [itcsSide, hWa, hRa]

/-- At least two left points have the same side color, so the center scan succeeds. -/
theorem itcs_side_odd {W R : Finset (Fin q)} (h3 : 3 ≤ W.card) :
    ∃ a, itciOt (itcsSide W R) = some a := by
  have hn : itciOt (itcsSide W R) ≠ none := by
    intro hn
    have hinj := itci_inj_of_c ((itciOt_spec (itcsSide W R)).1 hn)
    obtain ⟨a, ha⟩ := card_pos.1 (by omega : 0 < W.card)
    obtain ⟨b, hb, hba⟩ := exists_mem_ne (by omega : 1 < W.card) a
    exact hba (hinj (by simp [itcsSide, ha, hb]))
  cases he : itciOt (itcsSide W R) with
  | none => exact False.elim (hn he)
  | some a => exact ⟨a, rfl⟩

open Classical in
/-- The alignment and its fixed parity correction, both computed by the coloring programs. -/
noncomputable def itcsAlign (W R W' R' : Finset (Fin q)) : Perm (Fin q) :=
  let al := itciAl (itcsSide W R) (itcsSide W' R')
  if sign al = 1 then al else
    match itciOt (itcsSide W R) with
    | some a => al * itciTr (itcsSide W R) a
    | none => al

/-- The fixed alignment is even whenever the left side has at least three points. -/
theorem itcs_align_sign {W R W' R' : Finset (Fin q)} (h3 : 3 ≤ W.card) :
    sign (itcsAlign W R W' R') = 1 := by
  classical
  obtain ⟨a, ha⟩ := itcs_side_odd (R := R) h3
  have hne := (itciOt_spec (itcsSide W R)).2 a ha
  unfold itcsAlign
  dsimp only
  split_ifs with hs
  · exact hs
  · rw [ha, Perm.sign_mul, (itp_sign_cases _).resolve_left hs, itciTr, Perm.sign_swap hne]
    decide

/-- The alignment preserves the side colors, including its parity correction. -/
theorem itcs_align_colors {W R W' R' : Finset (Fin q)}
    (hc : ItciCnt (itcsSide W R) (itcsSide W' R')) (a : Fin q) :
    itcsSide W' R' (itcsAlign W R W' R' a) = itcsSide W R a := by
  classical
  have hal := itci_al_apply hc
  unfold itcsAlign
  dsimp only
  split_ifs
  · exact hal a
  · cases itciOt (itcsSide W R) with
    | none => exact hal a
    | some b =>
      rw [Perm.mul_apply, hal, itciTr]
      exact itp_swap_lab (itciC_f b) a

/-- Color preservation maps both sides onto their targets. -/
theorem itcs_align_images {W R W' R' : Finset (Fin q)}
    (hd : Disjoint W R) (hd' : Disjoint W' R')
    (hc : ItciCnt (itcsSide W R) (itcsSide W' R')) :
    itcsAlign W R W' R' '' (W : Set (Fin q)) = W' ∧
      itcsAlign W R W' R' '' (R : Set (Fin q)) = R' := by
  have hleft (a : Fin q) : itcsAlign W R W' R' a ∈ W' ↔ a ∈ W := by
    rw [← itcs_side_left W' R', itcs_align_colors hc, itcs_side_left]
  have hright (a : Fin q) : itcsAlign W R W' R' a ∈ R' ↔ a ∈ R := by
    rw [← itcs_side_right hd', itcs_align_colors hc, itcs_side_right hd]
  constructor
  · ext a
    constructor
    · rintro ⟨b, hb, rfl⟩; exact (hleft b).2 hb
    · intro ha
      refine ⟨(itcsAlign W R W' R').symm a, ?_, Equiv.apply_symm_apply _ _⟩
      exact (hleft _).1 (by simpa using ha)
  · ext a
    constructor
    · rintro ⟨b, hb, rfl⟩; exact (hright b).2 hb
    · intro ha
      refine ⟨(itcsAlign W R W' R').symm a, ?_, Equiv.apply_symm_apply _ _⟩
      exact (hright _).1 (by simpa using ha)

/-- This is the alignment property required by `SojChoice`, including its full coset. -/
theorem itcs_align_spec {W R W' R' : Finset (Fin q)}
    (hd : Disjoint W R) (hd' : Disjoint W' R') (hW : W.card = W'.card)
    (hR : R.card = R'.card) (h3 : 3 ≤ W.card) :
    IsAlign W R W' R' ⟨itcsAlign W R W' R', itcs_align_sign h3⟩ := by
  obtain ⟨hIW, hIR⟩ := itcs_align_images hd hd' (itcs_side_counts hd hd' hW hR h3)
  refine ⟨hIW, hIR, ?_, fun g => alignment_coset _ hIW hIR g⟩
  simp only [Finset.coe_compl, Finset.coe_union,
    Set.image_compl_eq (itcsAlign W R W' R').bijective, Set.image_union, hIW, hIR]

end GI.Impl
