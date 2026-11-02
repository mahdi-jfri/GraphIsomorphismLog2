import Workspace.SplitSubdirect

namespace GI.PrimitiveProducts

variable {S T : Type*} [Group S] [Group T]

theorem mem_of_full_first (H : Subgroup (S × T))
    (full : ∀ s : S, (s, 1) ∈ H) (s : S) (t : T)
    (ht : t ∈ H.map (MonoidHom.snd S T)) : (s, t) ∈ H := by
  obtain ⟨x, hx, hxt⟩ := ht
  have hp := H.mul_mem (full (s * x.1⁻¹)) hx
  change ((s * x.1⁻¹) * x.1, 1 * x.2) ∈ H at hp
  change x.2 = t at hxt
  simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul, hxt] using hp

/-- A contained full first factor splits off as an actual direct product
with the actual tail image. -/
def fullFactorProductEquiv (H : Subgroup (S × T))
    (full : ∀ s : S, (s, 1) ∈ H) : H ≃* S × H.map (MonoidHom.snd S T) where
  toFun h := (h.val.1, ⟨h.val.2, ⟨h.val, h.property, rfl⟩⟩)
  invFun p := ⟨(p.1, p.2.val), mem_of_full_first H full p.1 p.2.val p.2.property⟩
  left_inv h := Subtype.ext (Prod.eta h.val)
  right_inv _ := Prod.ext rfl (Subtype.ext rfl)
  map_mul' _ _ := rfl

theorem card_full_first (H : Subgroup (S × T)) (full : ∀ s : S, (s, 1) ∈ H) :
    Nat.card H = Nat.card S * Nat.card (H.map (MonoidHom.snd S T)) := by
  rw [Nat.card_congr (fullFactorProductEquiv H full).toEquiv, Nat.card_prod]

variable {n : ℕ}

theorem splitImage_full_first (H : Subgroup (Fin (n + 1) → S)) (full : HasFullFactor H 0) :
    ∀ s : S, (s, 1) ∈ splitImage H := by
  intro s
  exact ⟨Pi.mulSingle 0 s, full s, tupleSplit_single_zero n s⟩

theorem card_eq_mul_tailImage (H : Subgroup (Fin (n + 1) → S)) (full : HasFullFactor H 0) :
    Nat.card H = Nat.card S * Nat.card (tailImage H) := by
  calc
    Nat.card H = Nat.card (splitImage H) :=
      Nat.card_congr ((tupleSplit S n).subgroupMap H).toEquiv
    _ = Nat.card S * Nat.card (tailImage H) :=
      card_full_first (splitImage H) (splitImage_full_first H full)

theorem tailImage_noFull_of_unique_first (H : Subgroup (Fin (n + 1) → S))
    (full : HasFullFactor H 0) (onlyZero : ∀ i, HasFullFactor H i → i = 0) :
    NoFullFactors (tailImage H) := by
  intro i hi
  have hs : HasFullFactor H i.succ := by
    intro s
    apply (splitImage_mem H (Pi.mulSingle i.succ s)).mp
    rw [tupleSplit_single_succ]
    exact mem_of_full_first (splitImage H) (splitImage_full_first H full)
      1 (Pi.mulSingle i s) (hi s)
  exact Fin.succ_ne_zero i (onlyZero i.succ hs)

end GI.PrimitiveProducts

#print axioms GI.PrimitiveProducts.mem_of_full_first
#print axioms GI.PrimitiveProducts.fullFactorProductEquiv
#print axioms GI.PrimitiveProducts.card_full_first
#print axioms GI.PrimitiveProducts.splitImage_full_first
#print axioms GI.PrimitiveProducts.card_eq_mul_tailImage
#print axioms GI.PrimitiveProducts.tailImage_noFull_of_unique_first
