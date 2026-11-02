import Workspace.Compat
import Workspace.FiniteBudget
import Mathlib.GroupTheory.GroupAction.Basic

namespace GI

namespace HomDescent

variable {A B C : Type*} [Group A] [Group B] [Group C]

theorem eq_of_eq (f : A →* B) (q : A →* C)
    (hk : f.ker ≤ q.ker) {x y : A} (h : f x = f y) : q x = q y := by
  have hf : x * y⁻¹ ∈ f.ker := by
    change f (x * y⁻¹) = 1
    simp [h]
  have hq := hk hf
  change q (x * y⁻¹) = 1 at hq
  simpa only [map_mul, map_inv, mul_inv_eq_one] using hq

/-- Factor a homomorphism through a surjection whose kernel it kills. -/
noncomputable def factor (f : A →* B) (hf : Function.Surjective f)
    (q : A →* C) (hk : f.ker ≤ q.ker) : B →* C where
  toFun b := q (Classical.choose (hf b))
  map_one' := by
    simpa using eq_of_eq f q hk (x := Classical.choose (hf 1)) (y := 1)
      (by simpa using Classical.choose_spec (hf 1))
  map_mul' b c := by
    have h := eq_of_eq f q hk (x := Classical.choose (hf (b * c)))
      (y := Classical.choose (hf b) * Classical.choose (hf c)) (by
        rw [map_mul, Classical.choose_spec (hf (b * c)),
          Classical.choose_spec (hf b), Classical.choose_spec (hf c)])
    simpa only [map_mul] using h

theorem factor_apply (f : A →* B) (hf : Function.Surjective f)
    (q : A →* C) (hk : f.ker ≤ q.ker) (a : A) :
    factor f hf q hk (f a) = q a :=
  eq_of_eq f q hk (Classical.choose_spec (hf (f a)))

theorem factor_surjective (f : A →* B) (hf : Function.Surjective f)
    (q : A →* C) (hk : f.ker ≤ q.ker) (hq : Function.Surjective q) :
    Function.Surjective (factor f hf q hk) := by
  intro c
  obtain ⟨a, rfl⟩ := hq c
  exact ⟨f a, factor_apply f hf q hk a⟩

end HomDescent

variable {V W : Type*}

/-- A permutation action obtained by restricting the original action to an
invariant embedded set containing its active point. -/
structure ActionCover (H : Subgroup (Equiv.Perm V)) (a : V) (b : W) where
  project : H →* Equiv.Perm W
  embed : W ↪ V
  base : embed b = a
  equivariant : ∀ (h : H) (w : W), embed (project h w) = (h : Equiv.Perm V) (embed w)

namespace ActionCover

variable {H L : Subgroup (Equiv.Perm V)} {a : V} {b : W}

def restrict (c : ActionCover H a b) (hle : L ≤ H) : ActionCover L a b where
  project := c.project.comp (Subgroup.inclusion hle)
  embed := c.embed
  base := c.base
  equivariant l w := c.equivariant (Subgroup.inclusion hle l) w

theorem restrict_range_le (c : ActionCover H a b) (hle : L ≤ H) :
    (c.restrict hle).project.range ≤ c.project.range := by
  rintro p ⟨l, rfl⟩
  exact ⟨Subgroup.inclusion hle l, rfl⟩

theorem project_surjective (c : ActionCover H a b) :
    Function.Surjective c.project.rangeRestrict := by
  rintro ⟨p, h⟩
  obtain ⟨h, rfl⟩ := h
  exact ⟨h, rfl⟩

theorem orbit_apply (c : ActionCover H a b) (h : H) :
    c.embed (c.project h b) = (h : Equiv.Perm V) a := by
  rw [c.equivariant, c.base]

theorem visible_kernel {k : ℕ} (c : ActionCover H a b)
    (s : VisibleStep a H L k) : c.project.rangeRestrict.ker ≤ s.quotient.ker := by
  intro h hh
  apply s.visible h
  intro g
  have hp : c.project h = 1 := congrArg Subtype.val hh
  rw [← c.orbit_apply g, ← c.equivariant]
  simp [hp]

noncomputable def quotient {k : ℕ} (c : ActionCover H a b)
    (s : VisibleStep a H L k) : c.project.range →* alternatingGroup (Fin k) :=
  HomDescent.factor c.project.rangeRestrict c.project_surjective
    s.quotient (c.visible_kernel s)

theorem quotient_apply {k : ℕ} (c : ActionCover H a b)
    (s : VisibleStep a H L k) (h : H) :
    c.quotient s (c.project.rangeRestrict h) = s.quotient h :=
  HomDescent.factor_apply _ _ _ _ h

noncomputable def visibleStep {k : ℕ} (c : ActionCover H a b)
    (s : VisibleStep a H L k) :
    VisibleStep b c.project.range (c.restrict s.lower).project.range k where
  lower := c.restrict_range_le s.lower
  quotient := c.quotient s
  onto := HomDescent.factor_surjective _ _ _ _ s.onto
  kernel := by
    intro p
    obtain ⟨h, rfl⟩ := c.project_surjective p
    rw [c.quotient_apply]
    constructor
    · intro hh
      exact ⟨⟨h, (s.kernel h).mp hh⟩, rfl⟩
    · rintro ⟨l, hl⟩
      have heq : c.project.rangeRestrict h =
          c.project.rangeRestrict (Subgroup.inclusion s.lower l) :=
        Subtype.ext hl.symm
      rw [← c.quotient_apply s h, heq, c.quotient_apply]
      exact (s.kernel _).mpr l.property
  transitiveKernel := by
    intro p
    obtain ⟨h, rfl⟩ := c.project_surjective p
    obtain ⟨l, hl⟩ := s.transitiveKernel h
    refine ⟨(c.restrict s.lower).project.rangeRestrict l, ?_⟩
    apply c.embed.injective
    change c.embed (c.project (Subgroup.inclusion s.lower l) b) =
      c.embed (c.project h b)
    simpa only [c.orbit_apply] using hl
  visible := by
    intro p hp
    obtain ⟨h, rfl⟩ := c.project_surjective p
    rw [c.quotient_apply]
    apply s.visible h
    intro g
    have heq := congrArg c.embed (hp (c.project.rangeRestrict g))
    change c.embed (c.project h (c.project g b)) = c.embed (c.project g b) at heq
    simpa only [c.equivariant, c.base] using heq

/-- Every mark survives passage to a faithful restriction of the action. -/
theorem project_chain {cutoff w : ℕ} (hw : MarkedChain cutoff a H w)
    (c : ActionCover H a b) : MarkedChain cutoff b c.project.range w := by
  induction hw with
  | stop H => exact .stop _
  | restrict hle hw ih =>
      exact .restrict (c.restrict_range_le hle) (ih (c.restrict hle))
  | mark hk s hw ih =>
      exact .mark hk (c.visibleStep s) (ih (c.restrict s.lower))

/-- The actual subgroup of the original permutation group lying over `P`. -/
def pullback (c : ActionCover H a b) (P : Subgroup (Equiv.Perm W)) :
    Subgroup (Equiv.Perm V) := (P.comap c.project).map H.subtype

theorem pullback_le (c : ActionCover H a b) (P : Subgroup (Equiv.Perm W)) :
    c.pullback P ≤ H := by
  rintro h ⟨g, _, rfl⟩
  exact g.property

theorem mem_pullback (c : ActionCover H a b) (P : Subgroup (Equiv.Perm W)) (h : H) :
    (h : Equiv.Perm V) ∈ c.pullback P ↔ c.project h ∈ P := by
  constructor
  · rintro ⟨g, hg, heq⟩
    have hh : g = h := Subtype.ext heq
    subst g
    exact hg
  · intro hh
    exact ⟨h, hh, rfl⟩

theorem pullback_range (c : ActionCover H a b) (P : Subgroup (Equiv.Perm W))
    (hP : P ≤ c.project.range) :
    (c.restrict (c.pullback_le P)).project.range = P := by
  ext p
  constructor
  · rintro ⟨l, rfl⟩
    exact (c.mem_pullback P (Subgroup.inclusion (c.pullback_le P) l)).mp l.property
  · intro hp
    obtain ⟨h, rfl⟩ := hP hp
    exact ⟨⟨h, (c.mem_pullback P h).mpr hp⟩, rfl⟩

noncomputable def liftVisibleStep {k : ℕ} (c : ActionCover H a b)
    {P : Subgroup (Equiv.Perm W)} (s : VisibleStep b c.project.range P k) :
    VisibleStep a H (c.pullback P) k where
  lower := c.pullback_le P
  quotient := s.quotient.comp c.project.rangeRestrict
  onto := s.onto.comp c.project_surjective
  kernel h := (s.kernel (c.project.rangeRestrict h)).trans (c.mem_pullback P h).symm
  transitiveKernel := by
    intro h
    obtain ⟨p, hp⟩ := s.transitiveKernel (c.project.rangeRestrict h)
    obtain ⟨l, hl⟩ := s.lower p.property
    refine ⟨⟨l, (c.mem_pullback P l).mpr ?_⟩, ?_⟩
    · rw [hl]
      exact p.property
    · have hh := congrArg c.embed hp
      change c.embed ((p : Equiv.Perm W) b) = c.embed (c.project h b) at hh
      rw [← hl, c.orbit_apply, c.orbit_apply] at hh
      exact hh
  visible := by
    intro h hh
    apply s.visible (c.project.rangeRestrict h)
    intro p
    obtain ⟨g, rfl⟩ := c.project_surjective p
    apply c.embed.injective
    change c.embed (c.project h (c.project g b)) = c.embed (c.project g b)
    simpa only [c.equivariant, c.base] using hh g

/-- Full inverse images lift every marked chain, with the same weight. -/
theorem lift_chain {cutoff w : ℕ} {K : Subgroup (Equiv.Perm W)}
    (hw : MarkedChain cutoff b K w) (c : ActionCover H a b)
    (hK : c.project.range = K) : MarkedChain cutoff a H w := by
  induction hw generalizing H with
  | stop K => exact .stop _
  | @restrict K P w hle hw ih =>
      have hP : P ≤ c.project.range := by rw [hK]; exact hle
      exact .restrict (c.pullback_le P)
        (ih (c.restrict (c.pullback_le P)) (c.pullback_range P hP))
  | @mark K P w k hk s hw ih =>
      have hP : P ≤ c.project.range := by rw [hK]; exact s.lower
      have s' : VisibleStep b c.project.range P k := by rw [hK]; exact s
      exact .mark hk (c.liftVisibleStep s')
        (ih (c.restrict (c.pullback_le P)) (c.pullback_range P hP))

theorem chain_iff {cutoff w : ℕ} (c : ActionCover H a b) :
    MarkedChain cutoff a H w ↔ MarkedChain cutoff b c.project.range w :=
  ⟨fun hw => c.project_chain hw, fun hw => c.lift_chain hw rfl⟩

theorem budget_iff {cutoff B : ℕ} (c : ActionCover H a b) :
    BudgetAtMost cutoff a H B ↔ BudgetAtMost cutoff b c.project.range B := by
  constructor <;> intro h w hw
  · exact h w (c.chain_iff.mpr hw)
  · exact h w (c.chain_iff.mp hw)

theorem sigma_eq [Fintype V] [Fintype W] (cutoff : ℕ) (c : ActionCover H a b) :
    sigma cutoff a H = sigma cutoff b c.project.range := by
  unfold sigma
  congr 1
  ext w
  exact c.chain_iff

end ActionCover

/-- The actual orbit on which the faithful image acts. -/
abbrev ActiveOrbit (H : Subgroup (Equiv.Perm V)) (a : V) := MulAction.orbit H a

def activeOrbitBase (H : Subgroup (Equiv.Perm V)) (a : V) : ActiveOrbit H a :=
  ⟨a, MulAction.mem_orbit_self a⟩

def activeOrbitCover (H : Subgroup (Equiv.Perm V)) (a : V) :
    ActionCover H a (activeOrbitBase H a) where
  project := MulAction.toPermHom H (ActiveOrbit H a)
  embed := ⟨Subtype.val, Subtype.val_injective⟩
  base := rfl
  equivariant _ _ := rfl

def faithfulOrbitImage (H : Subgroup (Equiv.Perm V)) (a : V) :
    Subgroup (Equiv.Perm (ActiveOrbit H a)) := (activeOrbitCover H a).project.range

/-- Lemma A.3: orbit restriction and full inverse image give an equivalence
of marked chains at every weight, without a structural transfer assumption. -/
theorem markedChain_faithfulOrbit_iff {cutoff w : ℕ}
    (H : Subgroup (Equiv.Perm V)) (a : V) :
    MarkedChain cutoff a H w ↔
      MarkedChain cutoff (activeOrbitBase H a) (faithfulOrbitImage H a) w :=
  (activeOrbitCover H a).chain_iff

theorem sigma_faithfulOrbit [Fintype V] (cutoff : ℕ)
    (H : Subgroup (Equiv.Perm V)) (a : V) [Fintype (ActiveOrbit H a)] :
    sigma cutoff a H =
      sigma cutoff (activeOrbitBase H a) (faithfulOrbitImage H a) :=
  (activeOrbitCover H a).sigma_eq cutoff

/-- Relabeling vertices conjugates permutations. -/
def relabelPerm (e : V ≃ W) : Equiv.Perm V ≃* Equiv.Perm W where
  toEquiv := e.permCongr
  map_mul' p q := by
    ext w
    change e (p (q (e.symm w))) = e (p (e.symm (e (q (e.symm w)))))
    rw [e.symm_apply_apply]

def relabelCover (e : V ≃ W) (H : Subgroup (Equiv.Perm V)) (a : V) :
    ActionCover H a (e a) where
  project := (relabelPerm e).toMonoidHom.comp H.subtype
  embed := e.symm.toEmbedding
  base := e.symm_apply_apply a
  equivariant h w := by
    change e.symm (e ((h : Equiv.Perm V) (e.symm w))) = (h : Equiv.Perm V) (e.symm w)
    exact e.symm_apply_apply _

theorem relabelCover_range (e : V ≃ W) (H : Subgroup (Equiv.Perm V)) (a : V) :
    (relabelCover e H a).project.range = H.map (relabelPerm e).toMonoidHom := by
  ext p
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, h.property, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩

theorem markedChain_relabel_iff {cutoff w : ℕ}
    (e : V ≃ W) (H : Subgroup (Equiv.Perm V)) (a : V) :
    MarkedChain cutoff a H w ↔
      MarkedChain cutoff (e a) (H.map (relabelPerm e).toMonoidHom) w := by
  rw [← relabelCover_range e H a]
  exact (relabelCover e H a).chain_iff

theorem sigma_relabel [Fintype V] [Fintype W] (cutoff : ℕ)
    (e : V ≃ W) (H : Subgroup (Equiv.Perm V)) (a : V) :
    sigma cutoff a H = sigma cutoff (e a) (H.map (relabelPerm e).toMonoidHom) := by
  rw [← relabelCover_range e H a]
  exact (relabelCover e H a).sigma_eq cutoff

/-- Conjugation by an element of a subgroup preserves that subgroup. -/
theorem relabel_subgroup_self (H : Subgroup (Equiv.Perm V)) (h : H) :
    H.map (relabelPerm (h : Equiv.Perm V)).toMonoidHom = H := by
  have hconj (p : Equiv.Perm V) :
      relabelPerm (h : Equiv.Perm V) p = (h : Equiv.Perm V) * p * (h : Equiv.Perm V)⁻¹ := by
    ext v
    rfl
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change relabelPerm (h : Equiv.Perm V) q ∈ H
    rw [hconj]
    exact H.mul_mem (H.mul_mem h.property hq) (H.inv_mem h.property)
  · intro hp
    refine ⟨(h : Equiv.Perm V)⁻¹ * p * (h : Equiv.Perm V),
      H.mul_mem (H.mul_mem (H.inv_mem h.property) hp) h.property, ?_⟩
    change relabelPerm (h : Equiv.Perm V) ((h : Equiv.Perm V)⁻¹ * p * (h : Equiv.Perm V)) = p
    rw [hconj]
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

theorem markedChain_basepoint_iff {cutoff w : ℕ}
    (H : Subgroup (Equiv.Perm V)) {a b : V}
    (hab : ∃ h : H, (h : Equiv.Perm V) a = b) :
    MarkedChain cutoff a H w ↔ MarkedChain cutoff b H w := by
  obtain ⟨h, rfl⟩ := hab
  simpa only [relabel_subgroup_self] using markedChain_relabel_iff (h : Equiv.Perm V) H a

theorem sigma_basepoint [Fintype V] (cutoff : ℕ)
    (H : Subgroup (Equiv.Perm V)) {a b : V}
    (hab : ∃ h : H, (h : Equiv.Perm V) a = b) :
    sigma cutoff a H = sigma cutoff b H := by
  obtain ⟨h, rfl⟩ := hab
  simpa only [relabel_subgroup_self] using sigma_relabel cutoff (h : Equiv.Perm V) H a

/-- A.3's subgroup inheritance includes faithful restriction to any subgroup
orbit whose basepoint lies in the original active orbit. -/
theorem sigma_faithfulOrbit_subgroup_le [Fintype V] {cutoff : ℕ}
    (hcutoff : 5 ≤ cutoff) {H L : Subgroup (Equiv.Perm V)} (hle : L ≤ H)
    {a b : V} (hab : ∃ h : H, (h : Equiv.Perm V) a = b)
    [Fintype (ActiveOrbit L b)] :
    sigma cutoff (activeOrbitBase L b) (faithfulOrbitImage L b) ≤ sigma cutoff a H := by
  rw [← sigma_faithfulOrbit, sigma_basepoint cutoff H hab]
  exact sigma_subgroup_mono hcutoff b hle

/-- A marked quotient pays its weight even after replacing the lower action
by its faithful action on its active orbit. -/
theorem sigma_faithfulOrbit_marked_decrease [Fintype V] {cutoff k : ℕ}
    (hcutoff : 5 ≤ cutoff) {H L : Subgroup (Equiv.Perm V)} {a : V}
    (hk : cutoff ≤ k) (s : VisibleStep a H L k) [Fintype (ActiveOrbit L a)] :
    sigma cutoff (activeOrbitBase L a) (faithfulOrbitImage L a) + k ≤ sigma cutoff a H := by
  rw [← sigma_faithfulOrbit]
  exact sigma_marked_decrease hcutoff hk s

theorem faithfulOrbitImage_transitive (H : Subgroup (Equiv.Perm V)) (a : V)
    (x y : ActiveOrbit H a) :
    ∃ p : faithfulOrbitImage H a, (p : Equiv.Perm (ActiveOrbit H a)) x = y := by
  obtain ⟨g, hg⟩ := x.property
  obtain ⟨h, hh⟩ := y.property
  refine ⟨(activeOrbitCover H a).project.rangeRestrict (h * g⁻¹), ?_⟩
  apply Subtype.ext
  change ((h * g⁻¹ : H) : Equiv.Perm V) (x : V) = (y : V)
  change (g : Equiv.Perm V) a = (x : V) at hg
  change (h : Equiv.Perm V) a = (y : V) at hh
  rw [← hg, ← hh]
  change (h : Equiv.Perm V) ((g : Equiv.Perm V)⁻¹ ((g : Equiv.Perm V) a)) = _
  rw [Equiv.Perm.inv_apply_self]

end GI
