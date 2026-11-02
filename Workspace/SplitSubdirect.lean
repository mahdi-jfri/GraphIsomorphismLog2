import Workspace.TailFactorUniqueness

namespace GI.PrimitiveProducts

variable {S : Type*} [Group S] {n : ℕ}

def splitImage (H : Subgroup (Fin (n + 1) → S)) : Subgroup (S × (Fin n → S)) :=
  H.map (tupleSplit S n).toMonoidHom

def tailImage (H : Subgroup (Fin (n + 1) → S)) : Subgroup (Fin n → S) :=
  (splitImage H).map (MonoidHom.snd S (Fin n → S))

theorem splitImage_mem (H : Subgroup (Fin (n + 1) → S)) (x : Fin (n + 1) → S) :
    tupleSplit S n x ∈ splitImage H ↔ x ∈ H := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact (tupleSplit S n).injective he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem splitImage_head_surjective (H : Subgroup (Fin (n + 1) → S)) (hH : Subdirect H) :
    Function.Surjective (Prod.fst ∘ (splitImage H).subtype) := by
  intro s
  obtain ⟨h, hh⟩ := hH 0 s
  exact ⟨⟨tupleSplit S n h.val, ⟨h.val, h.property, rfl⟩⟩, hh⟩

theorem tailImage_subdirect (H : Subgroup (Fin (n + 1) → S)) (hH : Subdirect H) :
    Subdirect (tailImage H) := by
  intro i s
  obtain ⟨h, hh⟩ := hH i.succ s
  exact ⟨⟨(tupleSplit S n h.val).2,
    ⟨tupleSplit S n h.val, ⟨h.val, h.property, rfl⟩, rfl⟩⟩, hh⟩

theorem splitImage_no_full_first (H : Subgroup (Fin (n + 1) → S))
    (hH : NoFullFactors H) : ¬ ∀ s : S, (s, 1) ∈ splitImage H := by
  intro hf
  apply hH 0
  intro s
  apply (splitImage_mem H (Pi.mulSingle 0 s)).mp
  rw [tupleSplit_single_zero]
  exact hf s

theorem splitImage_no_full_tail (H : Subgroup (Fin (n + 1) → S))
    (hH : NoFullFactors H) (i : Fin n) : ¬ ∀ s : S, (1, Pi.mulSingle i s) ∈ splitImage H := by
  intro hf
  apply hH i.succ
  intro s
  apply (splitImage_mem H (Pi.mulSingle i.succ s)).mp
  rw [tupleSplit_single_succ]
  exact hf s

theorem splitImage_first_kernel_eq_bot [IsSimpleGroup S]
    (H : Subgroup (Fin (n + 1) → S)) (hsub : Subdirect H) (hno : NoFullFactors H) :
    (splitImage H).goursatFst = ⊥ :=
  goursatFst_eq_bot_of_no_full_first (splitImage H) (splitImage_head_surjective H hsub)
    (splitImage_no_full_first H hno)

theorem card_eq_tailImage [IsSimpleGroup S]
    (H : Subgroup (Fin (n + 1) → S)) (hsub : Subdirect H) (hno : NoFullFactors H) :
    Nat.card H = Nat.card (tailImage H) := by
  calc
    Nat.card H = Nat.card (splitImage H) :=
      Nat.card_congr ((tupleSplit S n).subgroupMap H).toEquiv
    _ = Nat.card (tailImage H) :=
      card_eq_secondProjection (splitImage H) (splitImage_first_kernel_eq_bot H hsub hno)

theorem tailImage_full_factor_unique [Finite S] [IsSimpleGroup S]
    (H : Subgroup (Fin (n + 1) → S)) (hsub : Subdirect H) (hno : NoFullFactors H)
    (nonabelian : ∃ x y : S, x * y ≠ y * x) (i j : Fin n)
    (hi : HasFullFactor (tailImage H) i) (hj : HasFullFactor (tailImage H) j) : i = j :=
  at_most_one_full_tail_factor (splitImage H) (splitImage_first_kernel_eq_bot H hsub hno)
    (splitImage_no_full_tail H hno) nonabelian i j hi hj

end GI.PrimitiveProducts

#print axioms GI.PrimitiveProducts.splitImage_mem
#print axioms GI.PrimitiveProducts.splitImage_head_surjective
#print axioms GI.PrimitiveProducts.tailImage_subdirect
#print axioms GI.PrimitiveProducts.splitImage_no_full_first
#print axioms GI.PrimitiveProducts.splitImage_no_full_tail
#print axioms GI.PrimitiveProducts.splitImage_first_kernel_eq_bot
#print axioms GI.PrimitiveProducts.card_eq_tailImage
#print axioms GI.PrimitiveProducts.tailImage_full_factor_unique
