module

public import Workspace.AlternatingSimple
public import Workspace.VisibleImage
public import Workspace.QuotientImage
public import Workspace.OrbitLocalization
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

@[expose] public section

namespace GI.Johnson

open scoped Pointwise

variable {H S α : Type*} [Group H] [Group S] [DecidableEq α] [MulAction H α]

/-- The actual permutation action of the setwise stabilizer on the anchors. -/
def anchorAction (T : Finset α) : MulAction.stabilizer H T →* Equiv.Perm T where
  toFun h :=
    { toFun x := ⟨(h : H) • x.val, by
        have hx := Finset.smul_mem_smul_finset (a := (h : H)) x.property
        rwa [h.property] at hx⟩
      invFun x := ⟨(h : H)⁻¹ • x.val, by
        have hx := Finset.smul_mem_smul_finset (a := (h : H)⁻¹) x.property
        have hi : (h : H)⁻¹ • T = T := h⁻¹.property
        rwa [hi] at hx⟩
      left_inv x := Subtype.ext (inv_smul_smul _ _)
      right_inv x := Subtype.ext (smul_inv_smul _ _) }
  map_one' := by ext x; exact one_smul H x.val
  map_mul' h j := by ext x; exact mul_smul (h : H) (j : H) x.val

theorem anchorAction_ker_iff (T : Finset α) (h : MulAction.stabilizer H T) :
    h ∈ (anchorAction T).ker ↔ ∀ a ∈ T, (h : H) • a = a := by
  constructor
  · intro hh a ha
    exact congrArg Subtype.val (congrArg (fun p : Equiv.Perm T => p ⟨a, ha⟩) hh)
  · intro hh
    apply Equiv.ext
    intro x
    exact Subtype.ext (hh x.val x.property)

theorem stabilizer_surjects (φ : H →* S) (onto : Function.Surjective φ) (T : Finset α)
    (transitive : ∀ h : H, ∃ n : H, φ n = 1 ∧ n • T = h • T) :
    Function.Surjective (φ.comp (MulAction.stabilizer H T).subtype) := by
  intro s
  obtain ⟨h, rfl⟩ := onto s
  obtain ⟨n, hn, hT⟩ := transitive h
  refine ⟨⟨n⁻¹ * h, ?_⟩, ?_⟩
  · change (n⁻¹ * h) • T = T
    rw [mul_smul, ← hT, inv_smul_smul]
  · change φ (n⁻¹ * h) = φ h
    simp [hn]

/-- The pointwise kernel on the natural orbit of one anchor. -/
def naturalOrbitKernel (a : α) : Subgroup H :=
  (MulAction.toPermHom H (MulAction.orbit H a)).ker

instance naturalOrbitKernel_normal (a : α) : (naturalOrbitKernel (H := H) a).Normal :=
  MonoidHom.normal_ker _

omit [DecidableEq α] in
theorem naturalOrbitKernel_iff (a : α) (h : H) :
    h ∈ naturalOrbitKernel a ↔ ∀ g : H, h • (g • a) = g • a := by
  constructor
  · intro hh g
    exact congrArg Subtype.val
      (congrArg (fun p : Equiv.Perm (MulAction.orbit H a) => p ⟨g • a, ⟨g, rfl⟩⟩) hh)
  · intro hh
    apply Equiv.ext
    intro x
    obtain ⟨g, hg⟩ := x.property
    apply Subtype.ext
    change h • x.val = x.val
    rw [← hg]
    exact hh g

theorem fixes_subset_of_pointwise (h : H) (T : Finset α)
    (fixes : ∀ a ∈ T, h • a = a) : h • T = T := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_smul_finset.mp ha
    rwa [fixes b hb]
  · intro ha
    exact Finset.mem_smul_finset.mpr ⟨a, ha, fixes a ha⟩

/-- A visible quotient of the subset-orbit action is visible on the natural
orbit of at least one actual anchor. This does not assume natural transitivity. -/
theorem localize_anchor [IsSimpleGroup S]
    (φ : H →* S) (onto : Function.Surjective φ)
    (nonabelian : ∃ s t : S, s * t ≠ t * s) (T : Finset α)
    (visible : ∀ h : H, (∀ g : H, h • (g • T) = g • T) → φ h = 1) :
    ∃ a ∈ T, naturalOrbitKernel (H := H) a ≤ φ.ker := by
  let Ks := T.toList.map (naturalOrbitKernel (H := H))
  have hn : ∀ K ∈ Ks, K.Normal := by
    intro K hK
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hK
    exact naturalOrbitKernel_normal a
  have hk : commonKernel Ks ≤ φ.ker := by
    intro h hh
    apply visible h
    intro g
    apply fixes_subset_of_pointwise
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_smul_finset.mp hx
    have hK : naturalOrbitKernel (H := H) a ∈ Ks := by
      apply List.mem_map.mpr
      exact ⟨a, by simpa using ha, rfl⟩
    exact (naturalOrbitKernel_iff a h).mp ((mem_commonKernel_iff Ks h).mp hh _ hK) g
  obtain ⟨K, hK, hzero⟩ := simple_quotient_localization φ onto nonabelian Ks hn hk
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hK
  refine ⟨a, by simpa using ha, ?_⟩
  intro h hh
  have hi := Subgroup.mem_map_of_mem φ hh
  simpa only [hzero, Subgroup.mem_bot, MonoidHom.mem_ker] using hi

/-- The pointwise-stabilizer branch of the Johnson argument yields a genuine
visible natural-action mark at an anchor. -/
theorem natural_mark {k : ℕ} (φ : H →* alternatingGroup (Fin k))
    (onto : Function.Surjective φ) (T : Finset α)
    (nonabelian : ∃ s t : alternatingGroup (Fin k), s * t ≠ t * s)
    [IsSimpleGroup (alternatingGroup (Fin k))]
    (visible : ∀ h : H, (∀ g : H, h • (g • T) = g • T) → φ h = 1)
    (pointwise_onto : Function.Surjective
      ((φ.comp (MulAction.stabilizer H T).subtype).comp (anchorAction T).ker.subtype)) :
    ∃ a ∈ T, Nonempty (VisibleStep a (MulAction.toPermHom H α).range
      (φ.ker.map (MulAction.toPermHom H α)) k) := by
  obtain ⟨a, ha, hk⟩ := localize_anchor φ onto nonabelian T visible
  have htrans : ∀ h : H, ∃ n : φ.ker, (n : H) • a = h • a := by
    intro h
    obtain ⟨p, hp⟩ := pointwise_onto (φ h)
    have hpfix : (p.val : H) • a = a :=
      (anchorAction_ker_iff T p.val).mp p.property a ha
    have hpinv : (p.val : H)⁻¹ • a = a := by
      have he := congrArg (fun x : α => (p.val : H)⁻¹ • x) hpfix
      simpa using he.symm
    refine ⟨⟨h * (p.val : H)⁻¹, ?_⟩, ?_⟩
    · change φ (h * (p.val : H)⁻¹) = 1
      change φ (p.val : H) = φ h at hp
      simp [hp]
    · change (h * (p.val : H)⁻¹) • a = h • a
      rw [mul_smul, hpinv]
  refine ⟨a, ha, ⟨VisibleImage.step (MulAction.toPermHom H α) φ φ.ker onto
    (fun _ => Iff.rfl) a htrans ?_⟩⟩
  intro h hh
  exact hk ((naturalOrbitKernel_iff a h).mpr hh)

/-- Actual one-mark Johnson anchor dichotomy. The first branch is an ordinary
quotient step on the fixed anchors; the second is a visible natural-action step.
No chain-transfer or anchor-localization conclusion is assumed. -/
theorem anchor_dichotomy {k : ℕ} (hk : 5 ≤ k)
    (φ : H →* alternatingGroup (Fin k)) (onto : Function.Surjective φ) (T : Finset α)
    (visible : ∀ h : H, (∀ g : H, h • (g • T) = g • T) → φ h = 1)
    (transitive : ∀ h : H, ∃ n : H, φ n = 1 ∧ n • T = h • T) :
    Nonempty (AlternatingQuotientStep (anchorAction (H := H) T).range
      ((φ.comp (MulAction.stabilizer H T).subtype).ker.map (anchorAction T)) k) ∨
    ∃ a ∈ T, Nonempty (VisibleStep a (MulAction.toPermHom H α).range
      (φ.ker.map (MulAction.toPermHom H α)) k) := by
  letI : IsSimpleGroup (alternatingGroup (Fin k)) := AlternatingSimple.isSimple_fin hk
  let ψ := φ.comp (MulAction.stabilizer H T).subtype
  have hψ : Function.Surjective ψ := stabilizer_surjects φ onto T transitive
  let P := (anchorAction (H := H) T).ker
  haveI : P.Normal := MonoidHom.normal_ker _
  rcases ((inferInstance : P.Normal).map ψ hψ).eq_bot_or_eq_top with hbot | htop
  · left
    refine ⟨QuotientImage.step (anchorAction T) ψ ψ.ker hψ (fun _ => Iff.rfl) ?_⟩
    intro h hh
    have hi := Subgroup.mem_map_of_mem ψ hh
    change ψ h ∈ P.map ψ at hi
    rw [hbot, Subgroup.mem_bot] at hi
    exact hi
  · right
    apply natural_mark φ onto T (AlternatingSimple.nonabelian_fin hk) visible
    intro s
    have hs : s ∈ P.map ψ := by rw [htop]; exact Subgroup.mem_top s
    obtain ⟨p, hp, hps⟩ := hs
    exact ⟨⟨p, hp⟩, hps⟩

end GI.Johnson
