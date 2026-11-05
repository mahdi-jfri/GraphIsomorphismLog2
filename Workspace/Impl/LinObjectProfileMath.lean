module

public import Workspace.Impl.LinObjectCorrectedAut
public import Workspace.Impl.LinAffineCoset

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Multicoset

variable {G Ω : Type*} [Group G] [RAct G Ω]

theorem linObjectTargetCover (B : Subgroup G) (τ : G) : linSourceConjugate B τ = conjR B τ := by
  ext g
  constructor
  · rintro ⟨b,hb,rfl⟩
    change τ*(τ⁻¹*b*τ⁻¹⁻¹)*τ⁻¹ ∈ B
    simpa only [SetLike.mem_coe,inv_inv,mul_inv_cancel_left,mul_assoc,mul_inv_cancel,mul_one] using hb
  · intro hg
    refine ⟨τ*g*τ⁻¹,hg,?_⟩
    change τ⁻¹*(τ*g*τ⁻¹)*τ⁻¹⁻¹ = g
    group

theorem linObjectTargetCover_props (H A B : Subgroup G) (hAH : A ≤ H)
    (hn : Normalizes H A) (hAB : A ≤ B) (hBH : B ≤ H) (τ : G) (hτ : τ ∈ H) :
    A ≤ conjR B τ ∧ conjR B τ ≤ H := by
  constructor
  · intro a ha
    exact hAB (hn τ hτ a ha)
  · intro g hg
    have hh := H.mul_mem (H.mul_mem (H.inv_mem hτ) (hBH hg)) hτ
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_one] using hh

/-- Every actual transporter gives a point of the affine fiber, and each
point of that fiber lifts to an actual transporter. -/
theorem linObjectProfile_nonempty {V : Type*} (H A B : Subgroup G) (X Y : Ω)
    (τ : G) (hτ : τ ∈ H) (hAH : A ≤ H) (hBH : B ≤ H)
    (c : conjR B τ → V) (target : V)
    (hP4 : ∀ h ∈ Iso H X Y,h*τ⁻¹ ∈ B)
    (hlift : ∀ g : conjR B τ,c g = target ↔ ∃ a ∈ A,(X ↼ (τ*g.val)) ↼ a = Y) :
    (Iso H X Y).Nonempty ↔ ∃ g,c g = target := by
  constructor
  · rintro ⟨t,ht⟩
    have hg : τ⁻¹*t ∈ conjR B τ := by
      change τ*(τ⁻¹*t)*τ⁻¹ ∈ B
      simpa only [mul_inv_cancel_left] using hP4 t ht
    refine ⟨⟨τ⁻¹*t,hg⟩,(hlift _).mpr ⟨1,A.one_mem,?_⟩⟩
    simpa only [mul_inv_cancel_left,act_one] using ht.2
  · rintro ⟨g,hg⟩
    obtain ⟨a,ha,he⟩ := (hlift g).mp hg
    have hgH : g.val ∈ H := by
      have hh := H.mul_mem (H.mul_mem (H.inv_mem hτ) (hBH g.property)) hτ
      simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_one] using hh
    exact ⟨τ*g.val*a,H.mul_mem (H.mul_mem hτ hgH) (hAH ha),by rwa [← act_act]⟩

/-- After a transporter is found, every target automorphism occurs in
its affine answer's zero subgroup. -/
theorem linObjectProfile_coverage {V : Type*} [Zero V]
    (H B L : Subgroup G) (X Y : Ω) (τ t : G) (ht : t ∈ Iso H X Y)
    (hP4 : ∀ h ∈ Iso H X Y,h*τ⁻¹ ∈ B) (hP5 : Aut H X ≤ B)
    (c : conjR B τ → V) (hL : ∀ g : conjR B τ,g.val ∈ L ↔ c g = 0)
    (hzero : ∀ g : conjR B τ,g.val ∈ Aut H Y → c g = 0) : Aut H Y ≤ L := by
  intro g hg
  have hc := linObjectAut_target_cover H B X Y τ t ht (hP4 t ht) hP5 hg
  exact (hL ⟨g,hc⟩).mpr (hzero ⟨g,hc⟩ hg)

end GI.Impl
