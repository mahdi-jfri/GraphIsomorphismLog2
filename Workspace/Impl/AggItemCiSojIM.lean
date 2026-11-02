import Workspace.Impl.AggItemCiSojPart

/-!
# Rejecting a target whose interior component is a singleton

The source imprimitive blocks all have at least two points. A partition map
preserves block sizes and the interior color. Hence an interior singleton in the
target makes the model's partition item empty. The program may test this before
calling Case 1's size-colored partition program.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm

variable {q : ℕ}

/-- Any transporter of the imprimitive partitions preserves each interior block size. -/
theorem itcs_imp_target (X Y : PairCfg q) (v : ℕ)
    (hX : ∀ a ∈ X.fiber, 2 ≤ (X.comp v a).card)
    {σ : Perm (Fin q)} (hσ : σ • X.impPart v = Y.impPart v) :
    ∀ a ∈ Y.fiber, 2 ≤ (Y.comp v a).card := by
  classical
  intro a ha
  have hc := congrArg (fun z : ColPart (Fin q) => z.col a) hσ
  have hb := congrArg (fun z : ColPart (Fin q) => z.blk a) hσ
  have hx : σ⁻¹ a ∈ X.fiber := by
    simpa only [ColPart.smul_col, PairCfg.impPart, if_pos ha, ite_eq_left_iff,
      zero_ne_one, imp_false, not_not] using hc
  have hb' : (X.comp v (σ⁻¹ a)).map σ.toEmbedding = Y.comp v a := by
    simpa only [ColPart.smul_blk, PairCfg.impPart, if_pos ha, if_pos hx] using hb
  rw [← hb', Finset.card_map]
  exact hX _ hx

/-- The exact item is empty when the target's interior-size check fails. -/
theorem itcs_imp_reject {Ω C : Type} {P : Params} {S : State Ω C} {L : GiantLabels S}
    (X Y : PairCfg L.q) (v : ℕ)
    (hX : ∀ a ∈ X.fiber, 2 ≤ (X.comp v a).card)
    (hY : ¬ ∀ a ∈ Y.fiber, 2 ≤ (Y.comp v a).card) :
    (objItem (P := P) (X.impPart v) (Y.impPart v) : AuxItem P S L).script =
      Script.done ⟨[], []⟩ := by
  classical
  have hn : ¬ ∃ σ : alternatingGroup (Fin L.q), σ.val • X.impPart v = Y.impPart v := by
    rintro ⟨σ, hσ⟩
    exact hY (itcs_imp_target X Y v hX hσ)
  simp only [objItem, dif_neg hn, AuxItem.script]

end GI.Impl
