module

public import Workspace.BudgetInductionBlocks

@[expose] public section

/-! An unconditional reduction of every transitive-kernel alternating
quotient to a primitive one of no larger physical degree. This does not
assume or prove the sharp primitive bound used in A.15. -/

namespace GI.A15Work

open BudgetInduction

variable {V B : Type} [Fintype V] {k : ℕ}
variable {H L : Subgroup (Equiv.Perm V)}

theorem alternating_quotient_degree_le (hk : 5 ≤ k)
    (q : H →* alternatingGroup (Fin k)) (hq : Function.Surjective q) :
    k ≤ Fintype.card V := by
  by_contra hn
  exact no_alternating_surjection_of_small_order hk (by omega)
    (permutation_subgroup_card_le_factorial H) q hq

def stepOfTransitiveKernel (q : H →* alternatingGroup (Fin k))
    (hq : Function.Surjective q)
    (ht : ∀ x y : V, ∃ g : H, q g = 1 ∧ g.val x = y) (a : V) :
    VisibleStep a H (q.ker.map H.subtype) k where
  lower := Subgroup.map_subtype_le q.ker
  quotient := q
  onto := hq
  kernel h := by
    constructor
    · intro hh
      exact ⟨h, hh, rfl⟩
    · rintro ⟨g, hg, he⟩
      have : g = h := Subtype.ext he
      exact this ▸ hg
  transitiveKernel h := by
    obtain ⟨g, hg, hga⟩ := ht a (h.val a)
    exact ⟨⟨g.val, ⟨g, hg, rfl⟩⟩, hga⟩
  visible h hh := by
    have he : h = 1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro x
      obtain ⟨g, _, hga⟩ := ht a x
      rw [← hga]
      exact hh g
    simp [he]

/-- A transitive-kernel alternating quotient is one actual marked step.
Consequently any eventual global budget theorem gives a logarithmic
exclusion, with that budget theorem's constants rather than A.15's constants. -/
theorem transitive_alternating_quotient_le_sigma {cutoff : ℕ}
    (hcutoff : 5 ≤ cutoff) (hk : cutoff ≤ k)
    (q : H →* alternatingGroup (Fin k)) (hq : Function.Surjective q)
    (ht : ∀ x y : V, ∃ g : H, q g = 1 ∧ g.val x = y) (a : V) :
    k ≤ sigma cutoff a H := by
  have hh := sigma_bounds_chain hcutoff
    (MarkedChain.mark hk (stepOfTransitiveKernel q hq ht a) (MarkedChain.stop _))
  simpa only [zero_add] using hh

omit [Fintype V] in
theorem topImage_pretransitive [MulAction.IsPretransitive H V]
    (c : BlockCover H B) (hsurj : Function.Surjective c.label) :
    MulAction.IsPretransitive c.project.range B := by
  constructor
  intro x y
  obtain ⟨v, rfl⟩ := hsurj x
  obtain ⟨w, rfl⟩ := hsurj y
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H v w
  change h.val v = w at hh
  refine ⟨c.project.rangeRestrict h, ?_⟩
  change c.project h (c.label v) = c.label w
  rw [← c.equivariant, hh]

omit [Fintype V] in
theorem localImage_pretransitive [MulAction.IsPretransitive H V]
    (c : BlockCover H B) (a : V) :
    MulAction.IsPretransitive (c.localProject a).range
      {x : V // c.label x = c.label a} := by
  constructor
  intro x y
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H x.val y.val
  change h.val x.val = y.val at hh
  have hm : h ∈ c.stabilizer a := by
    change c.project h (c.label a) = c.label a
    calc
      c.project h (c.label a) = c.project h (c.label x.val) := congrArg _ x.property.symm
      _ = c.label (h.val x.val) := (c.equivariant h x.val).symm
      _ = c.label y.val := congrArg c.label hh
      _ = c.label a := y.property
  refine ⟨(c.localProject a).rangeRestrict ⟨h, hm⟩, ?_⟩
  exact Subtype.ext hh

omit [Fintype V] in
theorem step_kernel_transitive [MulAction.IsPretransitive H V]
    {a : V} (s : VisibleStep a H L k) :
    ∀ x y : V, ∃ g : H, s.quotient g = 1 ∧ g.val x = y := by
  haveI : MulAction.IsPretransitive L V :=
    (MulAction.isPretransitive_iff_base a).mpr (by
      intro x
      obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H a x
      obtain ⟨l, hl⟩ := s.transitiveKernel h
      exact ⟨l, hl.trans hh⟩)
  intro x y
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L x y
  exact ⟨Subgroup.inclusion s.lower l, (s.kernel _).mpr l.property, hl⟩

/-- The whole primitive action, quotient and transitive kernel are actual
constructed data. The degree is bounded by the original physical degree. -/
structure PrimitiveObstruction (k n : ℕ) where
  Domain : Type
  finite : Fintype Domain
  group : Subgroup (Equiv.Perm Domain)
  lower : Subgroup (Equiv.Perm Domain)
  base : Domain
  primitive : MulAction.IsPreprimitive group Domain
  step : VisibleStep base group lower k
  degree : @Fintype.card Domain finite ≤ n

theorem primitive_obstruction_of_step (hk : 5 ≤ k) :
    ∀ n : ℕ, ∀ (V : Type) [Fintype V], Fintype.card V = n →
      ∀ (H L : Subgroup (Equiv.Perm V)) (a : V),
        MulAction.IsPretransitive H V → VisibleStep a H L k →
        Nonempty (PrimitiveObstruction k n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ hn H L a ht s
    letI := ht
    by_cases hp : MulAction.IsPreprimitive H V
    · exact ⟨⟨V, inferInstance, H, L, a, hp, s, hn.le⟩⟩
    have hnot : ¬ ∀ (B : Set V), a ∈ B → MulAction.IsBlock H B →
        MulAction.IsTrivialBlock B := by
      intro hh
      exact hp (MulAction.IsPreprimitive.of_isTrivialBlock_base a
        (fun ha hb => hh _ ha hb))
    push Not at hnot
    obtain ⟨B, ha, hB, hnt⟩ := hnot
    let p := partitionOfBlock hB ⟨a, ha⟩
    letI : Fintype (Quotient p.setoid) := Fintype.ofFinite _
    letI : Fintype {x : V // p.blockCover.label x = p.blockCover.label a} :=
      Fintype.ofFinite _
    have hc := partitionOfBlock_card_bounds hB ha hnt
    change 2 ≤ Nat.card (Quotient p.setoid) ∧
      2 ≤ Nat.card {x : V // p.blockCover.label x = p.blockCover.label a} at hc
    simp only [Nat.card_eq_fintype_card] at hc
    have hd := blockCover_smaller_degrees p.blockCover p.label_surjective a hc.1 hc.2
    haveI : IsSimpleGroup (alternatingGroup (Fin k)) := AlternatingSimple.isSimple_fin hk
    rcases p.blockCover.visible_step_split (AlternatingSimple.nonabelian_fin hk) s
      with hst | hsl
    · obtain ⟨st⟩ := hst
      letI := topImage_pretransitive p.blockCover p.label_surjective
      obtain ⟨w⟩ := ih _ (hd.1.trans_eq hn) _ rfl _ _ (p.blockCover.label a)
        inferInstance st
      exact ⟨{ w with degree := w.degree.trans (hd.1.le.trans hn.le) }⟩
    · obtain ⟨sl⟩ := hsl
      letI := localImage_pretransitive p.blockCover a
      obtain ⟨w⟩ := ih _ (hd.2.trans_eq hn) _ rfl _ _ (p.blockCover.localBase a)
        inferInstance sl
      exact ⟨{ w with degree := w.degree.trans (hd.2.le.trans hn.le) }⟩

/-- Any actual alternating quotient above a transitive kernel produces an
actual primitive obstruction; no primitive-group theorem is an assumption. -/
theorem primitive_obstruction_of_transitive_kernel (hk : 5 ≤ k)
    (q : H →* alternatingGroup (Fin k)) (hq : Function.Surjective q)
    (ht : ∀ x y : V, ∃ g : H, q g = 1 ∧ g.val x = y) :
    Nonempty (PrimitiveObstruction k (Fintype.card V)) := by
  classical
  have hd := alternating_quotient_degree_le hk q hq
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  letI : MulAction.IsPretransitive H V := ⟨fun x y => by
    obtain ⟨g, _, hg⟩ := ht x y
    exact ⟨g, hg⟩⟩
  let a : V := Classical.choice inferInstance
  exact primitive_obstruction_of_step hk _ V rfl H _ a inferInstance
    (stepOfTransitiveKernel q hq ht a)

theorem PrimitiveObstruction.kernel_transitive {n : ℕ} (w : PrimitiveObstruction k n) :
    ∀ x y : w.Domain, ∃ g : w.group, w.step.quotient g = 1 ∧ g.val x = y := by
  letI := w.finite
  letI := w.primitive
  exact step_kernel_transitive w.step

theorem PrimitiveObstruction.quotient_not_injective {n : ℕ} (hk : 5 ≤ k)
    (w : PrimitiveObstruction k n) : ¬ Function.Injective w.step.quotient := by
  letI := w.finite
  have hd := alternating_quotient_degree_le hk w.step.quotient w.step.onto
  haveI : Nontrivial w.Domain := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne w.Domain
  obtain ⟨g, hg, hga⟩ := w.kernel_transitive x y
  intro hi
  have he : g = 1 := hi (hg.trans (map_one w.step.quotient).symm)
  exact hxy (by simpa [he] using hga)

end GI.A15Work
