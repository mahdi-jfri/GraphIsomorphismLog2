module

public import Workspace.FullFactorStrip

@[expose] public section

namespace GI.PrimitiveProducts

variable {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]

/-- Quantitative Scott bound, proved without a diagonal-partition
classification: a subdirect subgroup containing no full coordinate
factor has at most the square root of the product order. -/
theorem subdirect_card_square_le_fin (nonabelian : ∃ x y : S, x * y ≠ y * x) :
    ∀ n : ℕ, ∀ H : Subgroup (Fin n → S), Subdirect H → NoFullFactors H →
      Nat.card H ^ 2 ≤ Nat.card S ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H hsub hno
    rcases n with _ | n
    · have hc : Nat.card H = 1 := Nat.card_unique
      rw [hc]
      simp
    rcases n with _ | n
    · apply (hno 0 ?_).elim
      intro s
      obtain ⟨h, hh⟩ := hsub 0 s
      change h.val 0 = s at hh
      have he : h.val = Pi.mulSingle 0 s := by
        funext i
        rw [Fin.eq_zero i, Pi.mulSingle_eq_same]
        exact hh
      exact he ▸ h.property
    · let L := tailImage H
      have hL : Subdirect L := tailImage_subdirect H hsub
      have hc : Nat.card H = Nat.card L := card_eq_tailImage H hsub hno
      by_cases hNL : NoFullFactors L
      · calc
          Nat.card H ^ 2 = Nat.card L ^ 2 := congrArg (fun k : ℕ => k ^ 2) hc
          _ ≤ Nat.card S ^ (n + 1) := ih (n + 1) (by omega) L hL hNL
          _ ≤ Nat.card S ^ (n + 1 + 1) := by
            rw [pow_succ]
            calc
              Nat.card S ^ (n + 1) = Nat.card S ^ (n + 1) * 1 := (Nat.mul_one _).symm
              _ ≤ Nat.card S ^ (n + 1) * Nat.card S :=
                Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr (Nat.card_pos (α := S)))
      · obtain ⟨i, hi⟩ := Classical.not_forall.mp hNL
        have hi : HasFullFactor L i := Classical.not_not.mp hi
        let e := Equiv.swap (0 : Fin (n + 1)) i
        let L' := L.map (coordinateRelabel S e).toMonoidHom
        have hL' : Subdirect L' := subdirect_relabel L e hL
        have hzero : HasFullFactor L' 0 := by
          have h := (hasFullFactor_relabel L e i).mpr hi
          simpa only [e, Equiv.swap_apply_right] using h
        have onlyZero : ∀ j, HasFullFactor L' j → j = 0 := by
          intro j hj
          obtain ⟨k, rfl⟩ := e.surjective j
          have hk := (hasFullFactor_relabel L e k).mp hj
          have hki : k = i := tailImage_full_factor_unique H hsub hno nonabelian k i hk hi
          rw [hki]
          exact Equiv.swap_apply_right 0 i
        let M := tailImage L'
        have hM : Subdirect M := tailImage_subdirect L' hL'
        have hNM : NoFullFactors M := tailImage_noFull_of_unique_first L' hzero onlyZero
        have hbound := ih n (by omega) M hM hNM
        have hcL : Nat.card L = Nat.card L' :=
          Nat.card_congr ((coordinateRelabel S e).subgroupMap L).toEquiv
        have hcH : Nat.card H = Nat.card S * Nat.card M :=
          hc.trans (hcL.trans (card_eq_mul_tailImage L' hzero))
        calc
          Nat.card H ^ 2 = (Nat.card S * Nat.card M) ^ 2 := congrArg (fun k : ℕ => k ^ 2) hcH
          _ = Nat.card S ^ 2 * Nat.card M ^ 2 := Nat.mul_pow _ _ _
          _ ≤ Nat.card S ^ 2 * Nat.card S ^ n := Nat.mul_le_mul_left _ hbound
          _ = Nat.card S ^ (n + 1 + 1) := by
            rw [← pow_add]
            congr 1
            omega

theorem subdirect_card_square_le {I : Type*} [Fintype I] [DecidableEq I]
    (nonabelian : ∃ x y : S, x * y ≠ y * x) (H : Subgroup (I → S))
    (hsub : Subdirect H) (hno : NoFullFactors H) :
    Nat.card H ^ 2 ≤ Nat.card S ^ Nat.card I := by
  let e := Fintype.equivFin I
  let K := H.map (coordinateRelabel S e).toMonoidHom
  have h := subdirect_card_square_le_fin nonabelian (Fintype.card I) K
    (subdirect_relabel H e hsub) (noFullFactors_relabel H e hno)
  have hc : Nat.card H = Nat.card K :=
    Nat.card_congr ((coordinateRelabel S e).subgroupMap H).toEquiv
  have hI : Nat.card I = Fintype.card I := Nat.card_eq_fintype_card
  simpa only [← hc, hI] using h

/-- The ambient product order is bounded by the square of the actual
subgroup index, ready to be identified with a physical action degree. -/
theorem subdirect_ambient_card_le_index_sq {I : Type*} [Fintype I] [DecidableEq I]
    (nonabelian : ∃ x y : S, x * y ≠ y * x) (H : Subgroup (I → S))
    (hsub : Subdirect H) (hno : NoFullFactors H) : Nat.card (I → S) ≤ H.index ^ 2 := by
  have h := subdirect_card_square_le nonabelian H hsub hno
  rw [← Nat.card_fun] at h
  have he := H.index_mul_card
  have hp : 0 < Nat.card H := Nat.card_pos
  have hle : Nat.card H ≤ H.index := by nlinarith
  calc
    Nat.card (I → S) = H.index * Nat.card H := he.symm
    _ ≤ H.index * H.index := Nat.mul_le_mul_left _ hle
    _ = H.index ^ 2 := (pow_two _).symm

end GI.PrimitiveProducts
