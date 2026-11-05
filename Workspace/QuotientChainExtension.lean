module

public import Workspace.QuotientImage
public import Workspace.BudgetInductionSolvable

@[expose] public section

namespace GI.QuotientExtension

variable {G Q : Type*} [Group G] [Group Q]
variable {H L : Subgroup G} {k : ℕ}

theorem restricted_range (p : G →* Q) (H : Subgroup G) :
    (p.comp H.subtype).range = H.map p := by
  ext x
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, h.property, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩

theorem restricted_lower_image (p : G →* Q) (hle : L ≤ H) :
    (L.comap H.subtype).map (p.comp H.subtype) = L.map p := by
  ext x
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hle hh⟩, hh, rfl⟩

noncomputable def imageStep (p : G →* Q) (s : AlternatingQuotientStep H L k)
    (kills : (p.comp H.subtype).ker ≤ s.quotient.ker) :
    AlternatingQuotientStep (H.map p) (L.map p) k := by
  have hs := QuotientImage.step (p.comp H.subtype) s.quotient (L.comap H.subtype)
    s.onto s.kernel kills
  rw [restricted_range, restricted_lower_image p s.lower] at hs
  exact hs

def kernelStep (p : G →* Q) (s : AlternatingQuotientStep H L k)
    (onto : Function.Surjective (s.quotient.comp (p.comp H.subtype).ker.subtype)) :
    AlternatingQuotientStep (H ⊓ p.ker) (L ⊓ p.ker) k where
  lower := inf_le_inf s.lower le_rfl
  quotient := s.quotient.comp (Subgroup.inclusion inf_le_left)
  onto := by
    intro z
    obtain ⟨h, hh⟩ := onto z
    exact ⟨⟨h.val.val, h.val.property, h.property⟩, hh⟩
  kernel h := by
    change s.quotient (Subgroup.inclusion inf_le_left h) = 1 ↔
      (h : G) ∈ L ∧ (h : G) ∈ p.ker
    exact (s.kernel _).trans ⟨fun hl => ⟨hl, h.property.2⟩, fun hl => hl.1⟩

/-- Every actual alternating quotient is realized in either the actual
restricted homomorphism kernel or the actual image. -/
theorem step_split (p : G →* Q) (hk : 5 ≤ k) (s : AlternatingQuotientStep H L k) :
    Nonempty (AlternatingQuotientStep (H ⊓ p.ker) (L ⊓ p.ker) k) ∨
      Nonempty (AlternatingQuotientStep (H.map p) (L.map p) k) := by
  let f := p.comp H.subtype
  letI := AlternatingSimple.isSimple_fin hk
  have hn : (f.ker.map s.quotient).Normal :=
    (inferInstance : f.ker.Normal).map s.quotient s.onto
  rcases hn.eq_bot_or_eq_top with hb | ht
  · right
    refine ⟨imageStep p s ?_⟩
    intro h hh
    have hm : s.quotient h ∈ f.ker.map s.quotient := ⟨h, hh, rfl⟩
    simpa only [hb, Subgroup.mem_bot, MonoidHom.mem_ker] using hm
  · left
    refine ⟨kernelStep p s ?_⟩
    intro z
    have hz : z ∈ f.ker.map s.quotient := by rw [ht]; exact Subgroup.mem_top z
    obtain ⟨h, hh, hz⟩ := hz
    exact ⟨⟨h, hh⟩, hz⟩

/-- Whole hereditary chains split coherently, preserving every subgroup
restriction. Each mark is charged exactly once. -/
theorem chain_split (p : G →* Q) {cutoff w : ℕ} (hcutoff : 5 ≤ cutoff)
    (chain : QuotientChain cutoff H w) :
    ∃ u v, w = u + v ∧ QuotientChain cutoff (H ⊓ p.ker) u ∧
      QuotientChain cutoff (H.map p) v := by
  induction chain with
  | stop H => exact ⟨0, 0, rfl, .stop _, .stop _⟩
  | restrict hle _ ih =>
    obtain ⟨u, v, hw, hu, hv⟩ := ih
    exact ⟨u, v, hw, .restrict (inf_le_inf hle le_rfl) hu,
      .restrict (Subgroup.map_mono hle) hv⟩
  | @mark H L w k hk s _ ih =>
    obtain ⟨u, v, hw, hu, hv⟩ := ih
    rcases step_split p (hcutoff.trans hk) s with hsk | hsi
    · obtain ⟨sk⟩ := hsk
      exact ⟨u + k, v, by omega, .mark hk sk hu,
        .restrict (Subgroup.map_mono s.lower) hv⟩
    · obtain ⟨si⟩ := hsi
      exact ⟨u, v + k, by omega, .restrict (inf_le_inf s.lower le_rfl) hu,
        .mark hk si hv⟩

theorem chain_map_of_injective (p : G →* Q) (hinj : Function.Injective p)
    {cutoff w : ℕ} (chain : QuotientChain cutoff H w) :
    QuotientChain cutoff (H.map p) w := by
  induction chain with
  | stop H => exact .stop _
  | restrict hle _ ih => exact .restrict (Subgroup.map_mono hle) ih
  | mark hk s _ ih =>
    apply QuotientChain.mark hk (imageStep p s ?_) ih
    intro h hh
    have hh1 : h = 1 := Subtype.ext (hinj (by simpa using hh))
    change s.quotient h = 1
    rw [hh1, map_one]

theorem chain_subgroupOf {K : Subgroup G} {cutoff w : ℕ}
    (chain : QuotientChain cutoff H w) (hle : H ≤ K) :
    QuotientChain cutoff (H.subgroupOf K) w := by
  induction chain with
  | stop H => exact .stop _
  | restrict hHL _ ih =>
    exact .restrict (Subgroup.comap_mono hHL) (ih (hHL.trans hle))
  | @mark H L w k hk s _ ih =>
    let e := Subgroup.subgroupOfEquivOfLe hle
    let step : AlternatingQuotientStep (H.subgroupOf K) (L.subgroupOf K) k :=
      { lower := Subgroup.comap_mono s.lower
        quotient := s.quotient.comp e.toMonoidHom
        onto := s.onto.comp e.surjective
        kernel := fun h => s.kernel (e h) }
    exact .mark hk step (ih (s.lower.trans hle))

end GI.QuotientExtension
