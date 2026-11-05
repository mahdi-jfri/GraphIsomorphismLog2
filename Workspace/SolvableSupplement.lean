module

public import Mathlib.GroupTheory.Frattini
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace GI

variable {G Q : Type*} [Group G] [Group Q]

/-- A minimal subgroup surjecting onto a quotient has its kernel in its
Frattini subgroup. This is a statement about the actual homomorphism. -/
theorem minimal_surjection_kernel_le_frattini
    (φ : G →* Q) (S : Subgroup G) (hS : S.map φ = ⊤)
    (minimal : ∀ T : Subgroup G, T.map φ = ⊤ → T ≤ S → S = T) :
    (φ.comp S.subtype).ker ≤ frattini S := by
  let ψ := φ.comp S.subtype
  have hψ : Function.Surjective ψ := by
    apply MonoidHom.range_eq_top.mp
    simpa only [ψ, MonoidHom.range_comp, Subgroup.range_subtype] using hS
  unfold frattini Order.radical
  refine le_iInf fun M => le_iInf fun hM => ?_
  by_contra hn
  have hsup : M ⊔ ψ.ker = ⊤ := hM.2 (M ⊔ ψ.ker)
    (lt_of_le_of_ne le_sup_left (by
      intro he
      have hle : ψ.ker ≤ M ⊔ ψ.ker := le_sup_right
      rw [← he] at hle
      exact hn hle))
  have hk : ψ.ker.map ψ = ⊥ := (Subgroup.map_eq_bot_iff ψ.ker).mpr le_rfl
  have hm : M.map ψ = ⊤ := by
    have h := congrArg (fun T : Subgroup S => T.map ψ) hsup
    simpa only [Subgroup.map_sup, hk, sup_bot_eq,
      Subgroup.map_top_of_surjective ψ hψ] using h
  have he : S = M.map S.subtype := minimal (M.map S.subtype)
    (by simpa only [Subgroup.map_map] using hm)
    (by rintro _ ⟨s, _, rfl⟩; exact s.property)
  have htop : M = ⊤ := by
    apply Subgroup.map_injective S.subtype_injective
    rw [← he]
    exact (Subgroup.range_subtype S).symm.trans (MonoidHom.range_eq_map S.subtype)
  exact hM.1 htop

/-- The existence assertion behind the solvable-supplement reduction. The
polynomial-time construction is a separate obligation. -/
theorem exists_solvable_surjective_subgroup [Finite G] [Group.IsSolvable Q]
    (φ : G →* Q) (onto : Function.Surjective φ) :
    ∃ S : Subgroup G, Group.IsSolvable S ∧ S.map φ = ⊤ := by
  classical
  let candidates : Set (Subgroup G) := {S | S.map φ = ⊤}
  have hnonempty : candidates.Nonempty :=
    ⟨⊤, Subgroup.map_top_of_surjective φ onto⟩
  obtain ⟨S, hS, hmin'⟩ := Set.Finite.exists_minimalFor id candidates
    (Set.toFinite candidates) hnonempty
  have hmin : ∀ T : Subgroup G, T.map φ = ⊤ → T ≤ S → S = T :=
    fun T hT hTS => le_antisymm (hmin' hT hTS) hTS
  have hk := minimal_surjection_kernel_le_frattini φ S hS hmin
  haveI : Group.IsNilpotent (frattini S) := frattini_nilpotent
  have hs : Group.IsSolvable S := solvable_of_ker_le_range (frattini S).subtype
    (φ.comp S.subtype) (by simpa only [Subgroup.range_subtype] using hk)
  exact ⟨S, hs, hS⟩

/-- Every normal subgroup with solvable quotient has a solvable supplement. -/
theorem exists_solvable_supplement [Finite G] (N : Subgroup G) [N.Normal]
    [Group.IsSolvable (G ⧸ N)] : ∃ S : Subgroup G, Group.IsSolvable S ∧ S ⊔ N = ⊤ := by
  obtain ⟨S, hs, hS⟩ := exists_solvable_surjective_subgroup
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  refine ⟨S, hs, ?_⟩
  have hr : S.map (QuotientGroup.mk' N) = (QuotientGroup.mk' N).range :=
    hS.trans (MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)).symm
  have h := Subgroup.map_eq_range_iff.mp hr
  simpa only [codisjoint_iff, QuotientGroup.ker_mk'] using h

end GI
