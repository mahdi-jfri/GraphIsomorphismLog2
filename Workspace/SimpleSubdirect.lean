module

public import Mathlib.GroupTheory.Goursat
public import Mathlib.GroupTheory.Subgroup.Simple
public import Workspace.RadicalSocleStructure

@[expose] public section

namespace GI.PrimitiveProducts

variable {S T : Type*} [Group S] [Group T]

theorem eq_top_of_goursatFst_eq_top (H : Subgroup (S × T))
    (onto : Function.Surjective (Prod.snd ∘ H.subtype)) (hker : H.goursatFst = ⊤) :
    H = ⊤ := by
  apply top_le_iff.mp
  rintro ⟨s, t⟩ _
  obtain ⟨h, hh⟩ := onto t
  change h.val.2 = t at hh
  have hk : (s * h.val.1⁻¹, 1) ∈ H := Subgroup.mem_goursatFst.mp (by
    rw [hker]
    exact Subgroup.mem_top _)
  have hp := H.mul_mem hk h.property
  change ((s * h.val.1⁻¹) * h.val.1, 1 * h.val.2) ∈ H at hp
  simpa only [Prod.mk_mul_mk, mul_assoc, inv_mul_cancel, mul_one, one_mul, hh] using hp

theorem eq_top_of_goursatSnd_eq_top (H : Subgroup (S × T))
    (onto : Function.Surjective (Prod.fst ∘ H.subtype)) (hker : H.goursatSnd = ⊤) :
    H = ⊤ := by
  apply top_le_iff.mp
  rintro ⟨s, t⟩ _
  obtain ⟨h, hh⟩ := onto s
  change h.val.1 = s at hh
  have hk : (1, h.val.2⁻¹ * t) ∈ H := Subgroup.mem_goursatSnd.mp (by
    rw [hker]
    exact Subgroup.mem_top _)
  have hp := H.mul_mem h.property hk
  change (h.val.1 * 1, h.val.2 * (h.val.2⁻¹ * t)) ∈ H at hp
  simpa only [Prod.mk_mul_mk, mul_inv_cancel_left, mul_one, hh] using hp

theorem fst_injective_of_goursatSnd_eq_bot (H : Subgroup (S × T))
    (hker : H.goursatSnd = ⊥) : Function.Injective (Prod.fst ∘ H.subtype) := by
  change Function.Injective ((MonoidHom.fst S T).comp H.subtype)
  apply (injective_iff_map_eq_one _).mpr
  intro h hh
  change h.val.1 = 1 at hh
  have hk : h.val.2 ∈ H.goursatSnd := Subgroup.mem_goursatSnd.mpr (by
    simpa only [← hh, Prod.mk.eta] using h.property)
  rw [hker, Subgroup.mem_bot] at hk
  exact Subtype.ext (Prod.ext hh hk)

theorem snd_injective_of_goursatFst_eq_bot (H : Subgroup (S × T))
    (hker : H.goursatFst = ⊥) : Function.Injective (Prod.snd ∘ H.subtype) := by
  change Function.Injective ((MonoidHom.snd S T).comp H.subtype)
  apply (injective_iff_map_eq_one _).mpr
  intro h hh
  change h.val.2 = 1 at hh
  have hk : h.val.1 ∈ H.goursatFst := Subgroup.mem_goursatFst.mpr (by
    simpa only [← hh, Prod.mk.eta] using h.property)
  rw [hker, Subgroup.mem_bot] at hk
  exact Subtype.ext (Prod.ext hk hh)

/-- The concrete two-factor Goursat alternative. A subgroup surjecting
onto two simple factors is either the whole product or the graph of an
actual group isomorphism. No quotient identification is assumed. -/
theorem simple_subdirect_eq_top_or_graph [IsSimpleGroup S] [IsSimpleGroup T]
    (H : Subgroup (S × T))
    (onto₁ : Function.Surjective (Prod.fst ∘ H.subtype))
    (onto₂ : Function.Surjective (Prod.snd ∘ H.subtype)) :
    H = ⊤ ∨ ∃ e : S ≃* T, H = e.toMonoidHom.graph := by
  letI := Subgroup.normal_goursatFst onto₁
  letI := Subgroup.normal_goursatSnd onto₂
  rcases (inferInstance : H.goursatFst.Normal).eq_bot_or_eq_top with hf | hf
  · rcases (inferInstance : H.goursatSnd.Normal).eq_bot_or_eq_top with hs | hs
    · exact Or.inr (Subgroup.exists_mulEquiv_eq_graph
        ⟨fst_injective_of_goursatSnd_eq_bot H hs, onto₁⟩
        ⟨snd_injective_of_goursatFst_eq_bot H hf, onto₂⟩)
    · exact Or.inl (eq_top_of_goursatSnd_eq_top H onto₁ hs)
  · exact Or.inl (eq_top_of_goursatFst_eq_top H onto₂ hf)

theorem simple_center_eq_bot [IsSimpleGroup S]
    (nonabelian : ∃ x y : S, x * y ≠ y * x) : Subgroup.center S = ⊥ := by
  rcases (inferInstance : (Subgroup.center S).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · obtain ⟨x, y, hxy⟩ := nonabelian
    have hy : y ∈ Subgroup.center S := by rw [ht]; exact Subgroup.mem_top _
    exact (hxy ((Subgroup.mem_center_iff.mp hy) x)).elim

end GI.PrimitiveProducts
