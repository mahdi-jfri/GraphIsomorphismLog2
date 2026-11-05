module

public import Workspace.Impl.AggItemCiSojAlign
public import Workspace.Impl.AggItemCiSojSq

@[expose] public section

/-!
# Fixed implication and alignment choices

For the imprimitive branch, scan ordered pairs of fiber indices and take the first
whose color components have the required sizes. Together with the fixed alignment
and the certificate function of `RcCertSpec`, this gives one `SojChoice` function
for all branches. The scan is on pair indices, not on possible partitions.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.CoherentEntrance GI.PairRefinement Equiv Finset

variable {q : ℕ}

/-- The component-size test expressed in the labels held by the program. -/
theorem itcs_imp_sizes (X : PairCfg q) (a b : Fin X.fiber.card) :
    ImpPair X a b ↔ a ≠ b ∧ ∀ x ∈ X.fiber,
      2 ≤ itpSz (itcsLab X (X.col (X.emb rfl a) (X.emb rfl b))) x ∧
      2 * itpSz (itcsLab X (X.col (X.emb rfl a) (X.emb rfl b))) x ≤ X.fiber.card := by
  have hs (x : Fin X.fiber.card) :
      itpSz (itcsLab X (X.col (X.emb rfl a) (X.emb rfl b))) (X.emb rfl x) =
        (colorComponent X.coloring false (X.coloring (false, a, b)) x).card := by
    change (itpBlk _ _).card = _
    rw [itcs_lab_blk, X.comp_emb (X.col_mem_vals a b) false x, Finset.card_map]
    rfl
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun x hx => ?_⟩
    obtain ⟨i, rfl⟩ := X.exists_emb rfl hx
    rw [hs]
    exact h i
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun x => ?_⟩
    rw [← hs]
    exact h _ (X.emb_mem rfl x)

open Classical in
/-- Indices that pass the imprimitive-pair test. -/
noncomputable def itcsImpIndices (X : PairCfg q) : Finset (Fin (X.fiber.card * X.fiber.card)) :=
  univ.filter fun t => ImpPair X ((itciPE X.fiber.card).symm t).1
    ((itciPE X.fiber.card).symm t).2

/-- A valid imprimitive pair has an index in the scan. -/
theorem itcs_imp_indices_ne (X : PairCfg q) (h : ∃ a b, ImpPair X a b) :
    (itcsImpIndices X).Nonempty := by
  classical
  obtain ⟨a, b, hab⟩ := h
  exact ⟨itciPE X.fiber.card (a, b), by
    simp only [itcsImpIndices, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
    exact hab⟩

/-- The first passing index fixes the imprimitive pair. -/
noncomputable def itcsImp (X : PairCfg q) (h : ∃ a b, ImpPair X a b) :
    {p : Fin X.fiber.card × Fin X.fiber.card // ImpPair X p.1 p.2} := by
  classical
  let t := (itcsImpIndices X).min' (itcs_imp_indices_ne X h)
  exact ⟨(itciPE X.fiber.card).symm t,
    (Finset.mem_filter.1 (Finset.min'_mem _ (itcs_imp_indices_ne X h))).2⟩

/-- The selected pair has the least passing index, matching a forward finite scan. -/
theorem itcs_imp_first (X : PairCfg q) (h : ∃ a b, ImpPair X a b)
    (a b : Fin X.fiber.card) (hab : ImpPair X a b) :
    itciPE X.fiber.card (itcsImp X h).1 ≤ itciPE X.fiber.card (a, b) := by
  classical
  change itciPE X.fiber.card ((itciPE X.fiber.card).symm _) ≤ _
  rw [Equiv.apply_symm_apply]
  exact Finset.min'_le _ _ (by
    simp only [itcsImpIndices, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
    exact hab)

/-- All first-rectangle choices are now fixed functions. The only external choice
is the single certificate function supplied by the certificate program contract. -/
noncomputable def itcsChoices (cf : RcCertFn) : SojChoice where
  cert := cf
  align W R W' R' hd hd' hW hR h3 :=
    ⟨⟨itcsAlign W R W' R', itcs_align_sign h3⟩, itcs_align_spec hd hd' hW hR h3⟩
  imp := itcsImp

@[simp] theorem itcs_choices_cert (cf : RcCertFn) : @SojChoice.cert (itcsChoices cf) = @cf := rfl

@[simp] theorem itcs_choices_imp (cf : RcCertFn) : @SojChoice.imp (itcsChoices cf) = @itcsImp := rfl

end GI.Impl
