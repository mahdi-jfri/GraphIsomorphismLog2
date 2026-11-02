import Workspace.JohnsonAnchors

namespace GI.Johnson

open scoped Pointwise

variable {V α : Type*} [DecidableEq α]

/-- A chain in the natural action whose marked basepoint may be any of the
fixed anchors. Unlike separate per-anchor budgets, this retains shared orbits. -/
inductive AnchoredChain (cutoff : ℕ) (anchors : Finset α) :
    Subgroup (Equiv.Perm α) → ℕ → Prop
  | stop (H) : AnchoredChain cutoff anchors H 0
  | restrict {H L w} : L ≤ H → AnchoredChain cutoff anchors L w →
      AnchoredChain cutoff anchors H w
  | mark {H L w k a} : a ∈ anchors → cutoff ≤ k → VisibleStep a H L k →
      AnchoredChain cutoff anchors L w → AnchoredChain cutoff anchors H (w + k)

omit [DecidableEq α] in
theorem AnchoredChain.toQuotientChain {cutoff w : ℕ} {anchors : Finset α}
    {H : Subgroup (Equiv.Perm α)} (h : AnchoredChain cutoff anchors H w) :
    QuotientChain cutoff H w := by
  induction h with
  | stop H => exact .stop H
  | restrict hle _ ih => exact .restrict hle ih
  | mark _ hk s _ ih =>
      exact .mark hk ⟨s.lower, s.quotient, s.onto, s.kernel⟩ ih

/-- An actual subset representation of the source permutation action.
The injective label rules out invisible changes to a source vertex. -/
structure JohnsonCover (H : Subgroup (Equiv.Perm V)) (α : Type*) [DecidableEq α] where
  project : H →* Equiv.Perm α
  label : V ↪ Finset α
  equivariant : ∀ (h : H) (x : V),
    label ((h : Equiv.Perm V) x) = project h • label x

namespace JohnsonCover

variable {H L : Subgroup (Equiv.Perm V)}

def restrict (c : JohnsonCover H α) (hle : L ≤ H) : JohnsonCover L α where
  project := c.project.comp (Subgroup.inclusion hle)
  label := c.label
  equivariant l x := c.equivariant (Subgroup.inclusion hle l) x

theorem project_injective (c : JohnsonCover H α) : Function.Injective c.project := by
  intro h g heq
  apply Subtype.ext
  ext x
  apply c.label.injective
  rw [c.equivariant, c.equivariant, heq]

theorem restrict_range_le (c : JohnsonCover H α) (hle : L ≤ H) :
    (c.restrict hle).project.range ≤ c.project.range := by
  rintro p ⟨l, rfl⟩
  exact ⟨Subgroup.inclusion hle l, rfl⟩

def anchorStabilizer (c : JohnsonCover H α) (a : V) : Subgroup H := by
  letI : MulAction H α := MulAction.compHom α c.project
  exact MulAction.stabilizer H (c.label a)

def anchorProject (c : JohnsonCover H α) (a : V) :
    c.anchorStabilizer a →* Equiv.Perm (c.label a) := by
  letI : MulAction H α := MulAction.compHom α c.project
  exact anchorAction (c.label a)

def anchorInclusion (c : JohnsonCover H α) (hle : L ≤ H) (a : V) :
    (c.restrict hle).anchorStabilizer a →* c.anchorStabilizer a where
  toFun h := ⟨Subgroup.inclusion hle h.val, h.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem restrict_anchor_range_le (c : JohnsonCover H α) (hle : L ≤ H) (a : V) :
    ((c.restrict hle).anchorProject a).range ≤ (c.anchorProject a).range := by
  rintro p ⟨l, rfl⟩
  exact ⟨c.anchorInclusion hle a l, rfl⟩

theorem natural_kernel_range (c : JohnsonCover H α) {a : V} {k : ℕ}
    (s : VisibleStep a H L k) :
    s.quotient.ker.map c.project = (c.restrict s.lower).project.range := by
  ext p
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, (s.kernel h).mp hh⟩, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ⟨Subgroup.inclusion s.lower l, (s.kernel _).mpr l.property, rfl⟩

theorem anchor_kernel_range (c : JohnsonCover H α) {a : V} {k : ℕ}
    (s : VisibleStep a H L k) :
    (s.quotient.comp (c.anchorStabilizer a).subtype).ker.map (c.anchorProject a) =
      ((c.restrict s.lower).anchorProject a).range := by
  ext p
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨⟨⟨h.val, (s.kernel h.val).mp hh⟩, h.property⟩, rfl⟩
  · rintro ⟨l, rfl⟩
    refine ⟨c.anchorInclusion s.lower a l, ?_, rfl⟩
    exact (s.kernel _).mpr l.val.property

/-- A marked subset-action step is realized either on the fixed anchors or
as a natural-action mark at an anchor, with the actual next subgroup image. -/
theorem visible_step_split (c : JohnsonCover H α) {a : V} {k : ℕ}
    (hk : 5 ≤ k) (s : VisibleStep a H L k) :
    Nonempty (AlternatingQuotientStep (c.anchorProject a).range
      ((c.restrict s.lower).anchorProject a).range k) ∨
    ∃ x ∈ c.label a, Nonempty (VisibleStep x c.project.range (c.restrict s.lower).project.range k) := by
  letI : MulAction H α := MulAction.compHom α c.project
  have hv : ∀ h : H, (∀ g : H, h • (g • c.label a) = g • c.label a) → s.quotient h = 1 := by
    intro h hh
    apply s.visible h
    intro g
    apply c.label.injective
    rw [c.equivariant, c.equivariant]
    exact hh g
  have ht : ∀ h : H, ∃ n : H, s.quotient n = 1 ∧ n • c.label a = h • c.label a := by
    intro h
    obtain ⟨l, hl⟩ := s.transitiveKernel h
    refine ⟨Subgroup.inclusion s.lower l, (s.kernel _).mpr l.property, ?_⟩
    change c.project (Subgroup.inclusion s.lower l) • c.label a = c.project h • c.label a
    rw [← c.equivariant (Subgroup.inclusion s.lower l), ← c.equivariant h]
    exact congrArg c.label hl
  have hd := anchor_dichotomy hk s.quotient s.onto (c.label a) hv ht
  have hp : MulAction.toPermHom H α = c.project := by ext h x; rfl
  rw [hp] at hd
  change Nonempty (AlternatingQuotientStep (c.anchorProject a).range
      ((s.quotient.comp (c.anchorStabilizer a).subtype).ker.map (c.anchorProject a)) k) ∨
    ∃ x ∈ c.label a, Nonempty (VisibleStep x c.project.range (s.quotient.ker.map c.project) k) at hd
  rwa [c.anchor_kernel_range s, c.natural_kernel_range s] at hd

/-- Actual chain decomposition for the Johnson proof. Ordinary anchor-image
charges form one descending quotient chain; all other marks remain together
in one anchored natural chain. -/
theorem chain_split {cutoff w : ℕ} (hcutoff : 5 ≤ cutoff) {a : V}
    (hw : MarkedChain cutoff a H w) (c : JohnsonCover H α) :
    ∃ u v : ℕ, w = u + v ∧ QuotientChain cutoff (c.anchorProject a).range u ∧
      AnchoredChain cutoff (c.label a) c.project.range v := by
  induction hw with
  | stop H => exact ⟨0, 0, rfl, .stop _, .stop _⟩
  | restrict hle hw ih =>
      obtain ⟨u, v, heq, hq, hn⟩ := ih (c.restrict hle)
      exact ⟨u, v, heq, .restrict (c.restrict_anchor_range_le hle a) hq,
        .restrict (c.restrict_range_le hle) hn⟩
  | @mark H L w k hk s hw ih =>
      obtain ⟨u, v, heq, hq, hn⟩ := ih (c.restrict s.lower)
      rcases c.visible_step_split (hcutoff.trans hk) s with hs | ⟨x, hx, hs⟩
      · obtain ⟨sq⟩ := hs
        exact ⟨u + k, v, by omega, .mark hk sq hq,
          .restrict (c.restrict_range_le s.lower) hn⟩
      · obtain ⟨sn⟩ := hs
        exact ⟨u, v + k, by omega,
          .restrict (c.restrict_anchor_range_le s.lower a) hq, .mark hx hk sn hn⟩

theorem chain_split_anchor_bound {cutoff w : ℕ} (hcutoff : 64 ≤ cutoff) {a : V}
    (hw : MarkedChain cutoff a H w) (c : JohnsonCover H α) :
    ∃ u v : ℕ, w = u + v ∧ u ≤ 3 * ((c.label a).card - 1) ∧
      AnchoredChain cutoff (c.label a) c.project.range v := by
  obtain ⟨u, v, heq, hq, hn⟩ := c.chain_split (by omega) hw
  refine ⟨u, v, heq, ?_, hn⟩
  simpa only [Fintype.card_coe] using quotient_chain_permutation_card_bound hcutoff hq

end JohnsonCover
end GI.Johnson
