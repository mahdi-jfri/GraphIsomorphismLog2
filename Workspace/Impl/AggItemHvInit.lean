import Workspace.Impl.AggItemHvCase

/-!
# Case 2a: the facts behind the init program

The init program of Case 2a computes `τ₀`, `t`, a group value of `K`, the twisted colors and
generators of `A`. This file proves the facts that turn its outputs into `ItHvKept`:

* `itHv_tw_choice`: the twist. If `C = Φᶜ` has at least two points, `t` is a lift of the paired
  transposition `(a b)(c d)` with `a, b` the two smallest points of `Φ` and `c, d` the two
  first points of `C` (`it_hv_tw_of`). Otherwise `t = 1` (`it_hv_tw_one`).
* `itHv_A_pairs`: the pairs of `itHvAL Φ fx` are graph pairs of `A = certLift ⊓ π⁻¹(Alt(Φ) ×
  Alt(C))`, since `Φ` is invariant under the label group of `F_x` (`it_hv_dom_inv`).
* `itHv_A_gens`: their first parts generate `A` on positions (`it_hv_fst_gens`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup)

variable {Ω C : Type} {k : ℕ}

section Init

variable {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- **The twist chosen by the program.** Let `a :: b :: rest` be the sorted list of `Φ` with
`q < 2 |Φ|`, and let `a₁` lift `(a b)(c d)` with `c, d` the first two points outside `Φ`. With
the flag `fl = [2 ≤ |Φᶜ|]`, the twist is the lift `a₁` if `fl = 1` and `1` if `fl = 0`. -/
theorem itHv_tw_choice {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    {Φ : Finset (Fin L.q)} (hd : L.q < 2 * Φ.card) (hq : 2 ≤ L.q) {a b : Fin L.q}
    {rest : List (Fin L.q)} (hs : Φ.sort (· ≤ ·) = a :: b :: rest) {a₁ : Perm (Fin k)}
    (ha₁ : (a₁, swap a b * itHvCD Φ hq) ∈ Subgroup.closure {p | p ∈ ps}) :
    ItHvTw L Φ ((toFin e).symm (if (if 1 < L.q - Φ.card then 1 else 0) = 0 then 1 else a₁)) := by
  have hmem : ∀ x, x ∈ Φ.sort (· ≤ ·) ↔ x ∈ Φ := fun x => Finset.mem_sort _
  have ha : a ∈ Φ := (hmem a).1 (by rw [hs]; simp)
  have hb : b ∈ Φ := (hmem b).1 (by rw [hs]; simp)
  have hab : a ≠ b := by
    have hn := Finset.sort_nodup Φ (· ≤ ·)
    rw [hs] at hn
    intro h
    rw [h] at hn
    simp at hn
  have hcC : Φᶜ.card = L.q - Φ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  by_cases h2 : 1 < L.q - Φ.card
  · rw [if_pos h2, if_neg one_ne_zero]
    have hc := itHv_posInv_not_mem hd ⟨0, by omega⟩ (by rw [hcC]; show 0 < L.q - Φ.card; omega)
    have hd' := itHv_posInv_not_mem hd ⟨1, by omega⟩ (by rw [hcC]; show 1 < L.q - Φ.card; omega)
    have hcd : (itpPosE (itHvLab Φ))⁻¹ ⟨0, by omega⟩ ≠ (itpPosE (itHvLab Φ))⁻¹ ⟨1, by omega⟩ := by
      intro h
      have := (itpPosE (itHvLab Φ))⁻¹.injective h
      simp at this
    exact it_hv_tw_of hps ha hb hab hc hd' hcd ha₁
  · rw [if_neg h2, if_pos rfl, map_one]
    exact it_hv_tw_one (by omega)

/-- **The pairs of `A`**: `itHvAL Φ fx` are graph pairs of `F ⊓ π⁻¹(Alt(Φ) × Alt(C))` when
`fx` are graph pairs of `F` and `Φ` is the dominant set of the label group of `F`. -/
theorem itHv_A_pairs {F : Subgroup (Perm Ω)} {fx : List (Perm (Fin k) × Perm (Fin L.q))}
    (hfx : PairGens e L F fx) :
    PairGens e L (F ⊓ L.lift (GI.Rectangle.evenSides (domSet (gens (fx.map Prod.snd)))
      (domSet (gens (fx.map Prod.snd)))ᶜ)) (itHvAL (domSet (gens (fx.map Prod.snd))) fx) :=
  it_hvAL_pairGens hfx fun _ hσ a => it_hv_dom_inv _ hσ a

/-- The pairs of `fx` keep `Φ`, so `it_hvA_spec` applies. -/
theorem itHv_fx_inv (fx : List (Perm (Fin k) × Perm (Fin L.q))) :
    ∀ s ∈ fx, ∀ a, s.2 a ∈ domSet (gens (fx.map Prod.snd)) ↔ a ∈ domSet (gens (fx.map Prod.snd)) :=
  fun _ hs a => it_hv_dom_inv _ (Subgroup.subset_closure (List.mem_map_of_mem hs)) a

/-- **The generators of `A` on positions** are the first parts of `itHvAL Φ fx`. -/
theorem itHv_A_gens {F : Subgroup (Perm Ω)} (hF : F ≤ S.G)
    {fx : List (Perm (Fin k) × Perm (Fin L.q))} (hfx : PairGens e L F fx) :
    gens ((itHvAL (domSet (gens (fx.map Prod.snd))) fx).map Prod.fst) =
      groupFin e (F ⊓ L.lift (GI.Rectangle.evenSides (domSet (gens (fx.map Prod.snd)))
        (domSet (gens (fx.map Prod.snd)))ᶜ)) :=
  it_hv_fst_gens (inf_le_left.trans hF) (itHv_A_pairs hfx)

/-- The dominant set is large once it has a point. -/
theorem itHv_dom_big {H : Subgroup (Perm (Fin L.q))} (h2 : 2 ≤ (domSet H).card) :
    L.q < 2 * (domSet H).card :=
  domSet_card_lt (Finset.card_pos.1 (by omega))

end Init

end GI.Impl
