module

public import Workspace.Impl.LinObjectLiftGroup
public import Workspace.MulticosetTransport
public import Workspace.Impl.TermGlue

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Multicoset

variable {G Ω : Type*} [Group G] [RAct G Ω]

/-- A profile cover also contains the target stabilizer once a transporter
has been found. -/
theorem linObjectAut_target_cover (H B : Subgroup G) (X Y : Ω) (τ t : G)
    (ht : t ∈ Iso H X Y) (hcover : t * τ⁻¹ ∈ B) (hsource : Aut H X ≤ B) :
    Aut H Y ≤ conjR B τ := by
  intro g hg
  have hh : t * g * t⁻¹ ∈ Aut H X := by
    refine ⟨H.mul_mem (H.mul_mem ht.1 hg.1) (H.inv_mem ht.1),?_⟩
    rw [← act_act,← act_act,ht.2,hg.2]
    exact (iso_inv ht).2
  have hb := hsource hh
  have hc := B.mul_mem (B.mul_mem (B.inv_mem hcover) hb) hcover
  change τ * g * τ⁻¹ ∈ B
  convert hc using 1 <;> group

/-- The answer convention is a left coset of the target stabilizer. -/
theorem linObjectIso_leftCoset (H : Subgroup G) (X Y : Ω) (t : G) (ht : t ∈ Iso H X Y) :
    Iso H X Y = (fun g => t*g) '' (Aut H Y : Set G) := by
  ext g
  constructor
  · intro hg
    refine ⟨t⁻¹*g,?_,by group⟩
    exact iso_comp (iso_inv ht) hg
  · rintro ⟨a,ha,rfl⟩
    exact iso_comp ht ha

/-- Correction preserves the image modulo A. This generator argument
is carried out inside H so that A need only be normal in H. -/
theorem linObjectCorrectedAut_eq {ι : Type*} (H A : Subgroup G) (hAH : A ≤ H)
    (hA : Normalizes H A) (Y : Ω) (original corrected : ι → G)
    (hOH : ∀ i, original i ∈ H) (hCH : ∀ i, corrected i ∈ H)
    (hcover : Aut H Y ≤ Subgroup.closure (Set.range original))
    (hcorrect : ∀ i, corrected i ∈ Aut H Y)
    (hdiff : ∀ i, (original i)⁻¹ * corrected i ∈ A) :
    Subgroup.closure (Set.range corrected) ⊔ Aut A Y = Aut H Y := by
  letI : (A.subgroupOf H).Normal := normal_of_normalizes hA
  let π := QuotientGroup.mk' (A.subgroupOf H)
  let S := (Aut H Y).subgroupOf H
  let K := (Aut A Y).subgroupOf H
  let orig : ι → H := fun i => ⟨original i,hOH i⟩
  let corr : ι → H := fun i => ⟨corrected i,hCH i⟩
  have hS : S ≤ Subgroup.closure (Set.range orig) := by
    intro x hx
    have hpre : Subgroup.closure (Set.range original) ≤
        (Subgroup.closure (Set.range orig)).map H.subtype := by
      apply (Subgroup.closure_le _).mpr
      rintro g ⟨i,rfl⟩
      exact ⟨orig i,Subgroup.subset_closure ⟨i,rfl⟩,rfl⟩
    obtain ⟨y,hy,he⟩ := hpre (hcover hx)
    have he' : y = x := Subtype.ext he
    exact he' ▸ hy
  have hKS : K ≤ S := fun x hx => ⟨hAH hx.1,hx.2⟩
  have hk : π.ker ⊓ S ≤ K := by
    intro x hx
    exact ⟨(QuotientGroup.eq_one_iff x).mp hx.1,hx.2.2⟩
  have hcc : ∀ i, corr i ∈ S := hcorrect
  have hi : ∀ i, π (corr i) = π (orig i) := by
    intro i
    apply QuotientGroup.eq.mpr
    change (corrected i)⁻¹ * original i ∈ A
    simpa only [mul_inv_rev,inv_inv] using A.inv_mem (hdiff i)
  have he := linObjectCorrectedGenerators_eq π orig corr S K hS hKS hk hcc hi
  have hm := congrArg (fun T : Subgroup H => T.map H.subtype) he
  have hcorr : (Subgroup.closure (Set.range corr)).map H.subtype = Subgroup.closure (Set.range corrected) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image,Set.mem_range]
    constructor
    · rintro ⟨y,⟨i,rfl⟩,rfl⟩; exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩; exact ⟨corr i,⟨i,rfl⟩,rfl⟩
  have hmapK : K.map H.subtype = Aut A Y := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact hy
    · intro hx; exact ⟨⟨x,hAH hx.1⟩,hx,rfl⟩
  have hmapS : S.map H.subtype = Aut H Y := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact hy
    · intro hx; exact ⟨⟨x,hx.1⟩,hx,rfl⟩
  change (Subgroup.closure (Set.range corr) ⊔ K).map H.subtype = S.map H.subtype at hm
  rwa [Subgroup.map_sup,hcorr,hmapK,hmapS] at hm

end GI.Impl
