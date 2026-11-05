module

public import Workspace.SubdirectGraphProjection
public import Workspace.CoordinateFactors

@[expose] public section

namespace GI.PrimitiveProducts

variable {S I : Type*} [Group S] [Finite S] [IsSimpleGroup S] [DecidableEq I]

/-- A full coordinate factor in the tail must map onto the missing simple
factor: a trivial map would put that coordinate factor in the original
subgroup, and every other map is injective by simplicity. -/
theorem projection_factor_surjective (H : Subgroup (S × (I → S)))
    (hk : H.goursatFst = ⊥)
    (noTail : ∀ i : I, ¬ ∀ s : S, (1, Pi.mulSingle i s) ∈ H)
    (i : I) (hi : HasFullFactor (H.map (MonoidHom.snd S (I → S))) i) :
    Function.Surjective ((projectionGraphHom H hk).comp
      (factorInclusion (H.map (MonoidHom.snd S (I → S))) i hi)) := by
  let f := (projectionGraphHom H hk).comp
    (factorInclusion (H.map (MonoidHom.snd S (I → S))) i hi)
  apply Finite.surjective_of_injective
  apply f.ker_eq_bot_iff.mp
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · apply (noTail i ?_).elim
    intro s
    have hs : f s = 1 := by
      change s ∈ f.ker
      rw [ht]
      exact Subgroup.mem_top s
    have hp := projectionGraphHom_pair_mem H hk
      (factorInclusion (H.map (MonoidHom.snd S (I → S))) i hi s)
    change (f s, Pi.mulSingle i s) ∈ H at hp
    simpa only [hs] using hp

/-- Deleting one coordinate can create at most one full coordinate factor.
Two such factors would give commuting surjective images in a nonabelian
simple group. -/
theorem at_most_one_full_tail_factor (H : Subgroup (S × (I → S)))
    (hk : H.goursatFst = ⊥)
    (noTail : ∀ i : I, ¬ ∀ s : S, (1, Pi.mulSingle i s) ∈ H)
    (nonabelian : ∃ x y : S, x * y ≠ y * x)
    (i j : I) (hi : HasFullFactor (H.map (MonoidHom.snd S (I → S))) i)
    (hj : HasFullFactor (H.map (MonoidHom.snd S (I → S))) j) : i = j := by
  by_contra hne
  let L := H.map (MonoidHom.snd S (I → S))
  let f := projectionGraphHom H hk
  let fi := f.comp (factorInclusion L i hi)
  let fj := f.comp (factorInclusion L j hj)
  obtain ⟨x, y, hxy⟩ := nonabelian
  obtain ⟨s, hs⟩ := projection_factor_surjective H hk noTail i hi x
  obtain ⟨t, ht⟩ := projection_factor_surjective H hk noTail j hj y
  have hc : Commute (fi s) (fj t) := (factorInclusion_commute L i j hi hj hne s t).map f
  change fi s = x at hs
  change fj t = y at ht
  rw [hs, ht] at hc
  exact hxy hc

end GI.PrimitiveProducts
