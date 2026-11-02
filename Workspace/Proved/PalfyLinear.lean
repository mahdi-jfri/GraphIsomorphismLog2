import Workspace.Proved.PalfyHard

/-!
# Order of solvable completely reducible linear groups

`GI.Proved.palfyLinear`: let `K` be a finite field with `q` elements, `V` a nonzero finite
`K`-space, and `H ≤ GL_K(V)` solvable and completely reducible. Then
`24 q^6 |H|^3 ≤ |V|^69`. In particular `|H| ≤ |V|^69` (`GI.Proved.palfyLinear_card`).
This is a polynomial bound of the kind proved by Pálfy and Wolf (1982), with a worse exponent.

*Proof.* Induction on `|V|`, and for fixed `|V|` on `|V| - q` (the field may grow).
* If `H` has an invariant subspace `W ≠ 0, V`, take an invariant complement `W'`. The
  restrictions to `W` and `W'` are completely reducible, `H` embeds in their product, and
  `|V| = |W| |W'|` (`GI.Proved.palfy_card_le_split`). The bound multiplies, with the extra factor
  `24 q^6 ≥ 1` to spare.
* Otherwise `H` is irreducible. If every abelian subgroup normalized by `H` is scalar, use
  `GI.Proved.palfy_hard`. Otherwise take such an `A` that is not scalar and let `R = K[A]`.
  If `R` has an idempotent other than `0, 1`, use `GI.Proved.palfy_imprimitive`. If not, `R` is a
  field (`GI.Proved.palfy_isField`), larger than `K`, and `GI.Proved.palfy_field_step` applies.
-/

namespace GI.Proved

/-- The exponent in the linear bound. -/
def palfyE : ℕ := 69

theorem palfy_linear_aux : ∀ (n d : ℕ) (K V : Type) [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [Finite V] [Nontrivial V], Nat.card V = n → Nat.card V - Nat.card K = d →
    ∀ H : Subgroup (Module.End K V)ˣ, IsSolvable H → palfyCR H →
      24 * Nat.card K ^ 6 * Nat.card H ^ 3 ≤ Nat.card V ^ palfyE := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro K V _ _ _ _ _ _ hn hd H hs hcr
  -- the two induction hypotheses
  have ihV : PalfyIH K palfyE n := by
    intro W _ _ _ _ hW G hG hGcr
    exact ihn _ hW _ K W rfl rfl G hG hGcr
  have ihF : PalfyIH2 palfyE n (Nat.card K) := by
    intro L _ _ W _ _ _ _ hW hL G hG hGcr
    have hLW := palfy_card_field_le L W
    exact ihd _ (by omega) L W hW rfl G hG hGcr
  by_cases hred : ∃ W : Submodule K V, palfyInv H W ∧ W ≠ ⊥ ∧ W ≠ ⊤
  · -- reducible
    obtain ⟨W, hW, hW0, hWt⟩ := hred
    obtain ⟨W', hW', hc⟩ := hcr W hW
    obtain ⟨hcard, hVc⟩ := palfy_card_le_split hW hW' hc
    haveI : Nontrivial W := (Submodule.nontrivial_iff_ne_bot).mpr hW0
    haveI : Nontrivial W' := (Submodule.nontrivial_iff_ne_bot).mpr (fun h => hWt (by
      have := hc.sup_eq_top
      rwa [h, sup_bot_eq] at this))
    have h1 : 1 < Nat.card W := Finite.one_lt_card
    have h2 : 1 < Nat.card W' := Finite.one_lt_card
    have hWlt : Nat.card W < Nat.card V := by rw [hVc]; nlinarith
    have hW'lt : Nat.card W' < Nat.card V := by rw [hVc]; nlinarith
    haveI := hs
    have b1 := ihV W (hn ▸ hWlt) _ (palfyResGrp_solvable H W hW) (palfyCR_res hcr hW)
    have b2 := ihV W' (hn ▸ hW'lt) _ (palfyResGrp_solvable H W' hW') (palfyCR_res hcr hW')
    set c := 24 * Nat.card K ^ 6
    have hc1 : 1 ≤ c := Nat.mul_pos (by norm_num) (pow_pos Nat.card_pos 6)
    calc c * Nat.card H ^ 3
        ≤ c * (Nat.card (palfyResGrp H W hW) * Nat.card (palfyResGrp H W' hW')) ^ 3 := by
          gcongr
      _ = (c * Nat.card (palfyResGrp H W hW) ^ 3) * Nat.card (palfyResGrp H W' hW') ^ 3 := by
          ring
      _ ≤ (c * Nat.card (palfyResGrp H W hW) ^ 3) *
          (c * Nat.card (palfyResGrp H W' hW') ^ 3) := by
          gcongr
          exact Nat.le_mul_of_pos_left _ hc1
      _ ≤ Nat.card W ^ palfyE * Nat.card W' ^ palfyE := Nat.mul_le_mul b1 b2
      _ = Nat.card V ^ palfyE := by rw [hVc, mul_pow]
  push Not at hred
  have hH : palfyIrr H := by
    intro W hW
    by_cases h0 : W = ⊥
    · exact Or.inl h0
    · exact Or.inr (hred W hW h0)
  haveI := hs
  by_cases hab : palfyAbSc H
  · exact palfy_hard hab
  -- a non-scalar abelian normal subgroup
  unfold palfyAbSc at hab
  push Not at hab
  obtain ⟨A, hAH, hAc, a, ha, hna⟩ := hab
  have hR := palfyAdj_alg hAH hAc
  by_cases hid : ∃ f ∈ palfyAdj A, IsIdempotentElem f ∧ f ≠ 0 ∧ f ≠ 1
  · obtain ⟨f, hfR, hf, hf0, hf1⟩ := hid
    exact palfy_imprimitive (hn ▸ ihV) hH hR hfR hf hf0 hf1
  push Not at hid
  have hF : IsField (palfyAdj A) := palfy_isField hH hR (fun e he hidem => by
    by_cases h0 : e = 0
    · exact Or.inl h0
    · exact Or.inr (hid e he hidem h0))
  have hne : palfyAdj A ≠ ⊥ := by
    intro hbot
    apply hna
    have : (a : Module.End K V) ∈ (⊥ : Subalgebra K (Module.End K V)) := hbot ▸ palfyAdj_mem ha
    obtain ⟨k, hk⟩ := Algebra.mem_bot.mp this
    exact ⟨k, hk⟩
  exact palfy_field_step (hn ▸ ihF) hH hAH hAc hF hne

/-- **Pálfy–Wolf type bound.** A solvable completely reducible linear group `H` on a nonzero
finite vector space `V` over a finite field `K` satisfies `24 |K|^6 |H|^3 ≤ |V|^69`. -/
theorem palfyLinear (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [Finite V] [Nontrivial V] (H : Subgroup (Module.End K V)ˣ) (hs : IsSolvable H)
    (hcr : palfyCR H) :
    24 * Nat.card K ^ 6 * Nat.card H ^ 3 ≤ Nat.card V ^ palfyE :=
  palfy_linear_aux _ _ K V rfl rfl H hs hcr

/-- `|H| ≤ |V|^69` for a solvable completely reducible linear group `H` on a nonzero finite
vector space `V`. -/
theorem palfyLinear_card (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [Finite V] [Nontrivial V] (H : Subgroup (Module.End K V)ˣ) (hs : IsSolvable H)
    (hcr : palfyCR H) : Nat.card H ≤ Nat.card V ^ palfyE := by
  have h := palfyLinear K V H hs hcr
  have hpos : 0 < Nat.card H := Nat.card_pos
  calc Nat.card H ≤ Nat.card H ^ 3 := Nat.le_self_pow (by norm_num) _
    _ ≤ 24 * Nat.card K ^ 6 * Nat.card H ^ 3 :=
      Nat.le_mul_of_pos_left _ (by have : 0 < Nat.card K := Nat.card_pos; positivity)
    _ ≤ _ := h

end GI.Proved
