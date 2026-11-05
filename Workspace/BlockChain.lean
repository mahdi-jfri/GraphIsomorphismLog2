module

public import Workspace.BlockOrbit
public import Workspace.VisibleImage

@[expose] public section

namespace GI

variable {V B : Type*}

/-- An actual equivariant labeling of vertices by blocks, together with the
induced permutation representation on block labels. -/
structure BlockCover (H : Subgroup (Equiv.Perm V)) (B : Type*) where
  label : V → B
  project : H →* Equiv.Perm B
  equivariant : ∀ (h : H) (x : V), label ((h : Equiv.Perm V) x) = project h (label x)

namespace BlockCover

variable {H L : Subgroup (Equiv.Perm V)}

def restrict (c : BlockCover H B) (hle : L ≤ H) : BlockCover L B where
  label := c.label
  project := c.project.comp (Subgroup.inclusion hle)
  equivariant l x := c.equivariant (Subgroup.inclusion hle l) x

theorem restrict_range_le (c : BlockCover H B) (hle : L ≤ H) :
    (c.restrict hle).project.range ≤ c.project.range := by
  rintro p ⟨l, rfl⟩
  exact ⟨Subgroup.inclusion hle l, rfl⟩

def stabilizer (c : BlockCover H B) (a : V) : Subgroup H :=
  (MulAction.stabilizer (Equiv.Perm B) (c.label a)).comap c.project

def localProject (c : BlockCover H B) (a : V) :
    c.stabilizer a →* Equiv.Perm {x : V // c.label x = c.label a} where
  toFun h :=
    { toFun x := ⟨(h.val : Equiv.Perm V) x.val, by
        rw [c.equivariant, x.property]
        exact h.property⟩
      invFun x := ⟨(h.val : Equiv.Perm V)⁻¹ x.val, by
        rw [show (h.val : Equiv.Perm V)⁻¹ = ((h.val⁻¹ : H) : Equiv.Perm V) from rfl,
          c.equivariant, x.property]
        exact h⁻¹.property⟩
      left_inv x := Subtype.ext ((h.val : Equiv.Perm V).symm_apply_apply x.val)
      right_inv x := Subtype.ext ((h.val : Equiv.Perm V).apply_symm_apply x.val) }
  map_one' := by
    apply Equiv.ext
    intro x
    rfl
  map_mul' h k := by
    apply Equiv.ext
    intro x
    rfl

def localBase (c : BlockCover H B) (a : V) : {x : V // c.label x = c.label a} :=
  ⟨a, rfl⟩

def localInclusion (c : BlockCover H B) (hle : L ≤ H) (a : V) :
    (c.restrict hle).stabilizer a →* c.stabilizer a where
  toFun l := ⟨Subgroup.inclusion hle l.val, l.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem restrict_local_range_le (c : BlockCover H B) (hle : L ≤ H) (a : V) :
    ((c.restrict hle).localProject a).range ≤ (c.localProject a).range := by
  rintro p ⟨l, rfl⟩
  exact ⟨c.localInclusion hle a l, rfl⟩

theorem restrict_top_range (c : BlockCover H B) (hle : L ≤ H) :
    (L.comap H.subtype).map c.project = (c.restrict hle).project.range := by
  ext p
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ⟨Subgroup.inclusion hle l, l.property, rfl⟩

theorem restrict_local_range (c : BlockCover H B) (hle : L ≤ H) (a : V) :
    ((L.comap H.subtype).comap (c.stabilizer a).subtype).map (c.localProject a) =
      ((c.restrict hle).localProject a).range := by
  ext p
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨⟨h.val, hh⟩, h.property⟩, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ⟨c.localInclusion hle a l, l.val.property, rfl⟩

/-- Each actual marked step is realized, with the same lower image, in the
block action or in the action of the distinguished block stabilizer. -/
theorem visible_step_split [Fintype V] {a : V} {k : ℕ}
    [IsSimpleGroup (alternatingGroup (Fin k))]
    (nonabelian : ∃ s t : alternatingGroup (Fin k), s * t ≠ t * s)
    (c : BlockCover H B) (s : VisibleStep a H L k) :
    Nonempty (VisibleStep (c.label a) c.project.range (c.restrict s.lower).project.range k) ∨
    Nonempty (VisibleStep (c.localBase a) (c.localProject a).range
      ((c.restrict s.lower).localProject a).range k) := by
  letI : MulAction H B := MulAction.compHom B c.project
  have transitive : ∀ h : H, ∃ n : H, s.quotient n = 1 ∧ n • a = h • a := by
    intro h
    obtain ⟨l, hl⟩ := s.transitiveKernel h
    exact ⟨Subgroup.inclusion s.lower l, (s.kernel _).mpr l.property, hl⟩
  have hd := visible_block_orbit_dichotomy s.quotient s.onto nonabelian
    c.label c.equivariant a s.visible transitive
  rcases hd with htop | ⟨honto, hlocal⟩
  · left
    have ht : ∀ h : H, ∃ n : L.comap H.subtype,
        c.project n (c.label a) = c.project h (c.label a) := by
      intro h
      obtain ⟨l, hl⟩ := s.transitiveKernel h
      refine ⟨⟨Subgroup.inclusion s.lower l, l.property⟩, ?_⟩
      exact (c.equivariant _ a).symm.trans ((congrArg c.label hl).trans (c.equivariant h a))
    have v := VisibleImage.step c.project s.quotient (L.comap H.subtype)
      s.onto s.kernel (c.label a) ht htop
    rw [c.restrict_top_range s.lower] at v
    exact ⟨v⟩
  · right
    let q := s.quotient.comp (c.stabilizer a).subtype
    let N := (L.comap H.subtype).comap (c.stabilizer a).subtype
    have hq : Function.Surjective q := by
      intro z
      obtain ⟨h, hh, hz⟩ := honto z
      exact ⟨⟨h, hh⟩, hz⟩
    have hk : ∀ h : c.stabilizer a, q h = 1 ↔ h ∈ N := by
      intro h
      exact s.kernel h.val
    have ht : ∀ h : c.stabilizer a, ∃ n : N,
        c.localProject a n (c.localBase a) = c.localProject a h (c.localBase a) := by
      intro h
      obtain ⟨l, hl⟩ := s.transitiveKernel h.val
      have hfix : c.project (Subgroup.inclusion s.lower l) (c.label a) = c.label a := by
        calc
          _ = c.label ((l : Equiv.Perm V) a) := (c.equivariant _ a).symm
          _ = c.label ((h.val : Equiv.Perm V) a) := congrArg c.label hl
          _ = c.project h.val (c.label a) := c.equivariant h.val a
          _ = c.label a := h.property
      refine ⟨⟨⟨Subgroup.inclusion s.lower l, hfix⟩, l.property⟩, ?_⟩
      exact Subtype.ext hl
    have hv : ∀ h : c.stabilizer a,
        (∀ g : c.stabilizer a, c.localProject a h
          (c.localProject a g (c.localBase a)) = c.localProject a g (c.localBase a)) →
        q h = 1 := by
      intro h hh
      apply hlocal h.val h.property
      intro g hg
      exact congrArg Subtype.val (hh ⟨g, hg⟩)
    have v := VisibleImage.step (c.localProject a) q N hq hk (c.localBase a) ht hv
    change VisibleStep (c.localBase a) (c.localProject a).range
      (((L.comap H.subtype).comap (c.stabilizer a).subtype).map (c.localProject a)) k at v
    rw [c.restrict_local_range s.lower a] at v
    exact ⟨v⟩

/-- The cumulative two-chain transfer. The only group-theoretic inputs left
as parameters are simplicity and noncommutativity of the alternating groups;
the chain transfer and block localization are proved here. -/
theorem chain_split_of_simple [Fintype V] {cutoff w : ℕ} {a : V}
    (simple : ∀ k : ℕ, cutoff ≤ k → IsSimpleGroup (alternatingGroup (Fin k)))
    (nonabelian : ∀ k : ℕ, cutoff ≤ k →
      ∃ s t : alternatingGroup (Fin k), s * t ≠ t * s)
    (hw : MarkedChain cutoff a H w) :
    ∀ c : BlockCover H B, ∃ u v : ℕ, u + v = w ∧
      MarkedChain cutoff (c.label a) c.project.range u ∧
      MarkedChain cutoff (c.localBase a) (c.localProject a).range v := by
  induction hw with
  | stop H =>
      intro c
      exact ⟨0, 0, rfl, .stop _, .stop _⟩
  | restrict hle _ ih =>
      intro c
      obtain ⟨u, v, huv, hu, hv⟩ := ih (c.restrict hle)
      exact ⟨u, v, huv, .restrict (c.restrict_range_le hle) hu,
        .restrict (c.restrict_local_range_le hle a) hv⟩
  | @mark H L w k hk s _ ih =>
      intro c
      obtain ⟨u, v, huv, hu, hv⟩ := ih (c.restrict s.lower)
      letI := simple k hk
      rcases c.visible_step_split (nonabelian k hk) s with hst | hsl
      · obtain ⟨st⟩ := hst
        exact ⟨u + k, v, by omega, .mark hk st hu,
          .restrict (c.restrict_local_range_le s.lower a) hv⟩
      · obtain ⟨sl⟩ := hsl
        exact ⟨u, v + k, by omega, .restrict (c.restrict_range_le s.lower) hu,
          .mark hk sl hv⟩

theorem sigma_block_le_of_simple [Fintype V] [Fintype B]
    {cutoff : ℕ} (hcutoff : 5 ≤ cutoff)
    (simple : ∀ k : ℕ, cutoff ≤ k → IsSimpleGroup (alternatingGroup (Fin k)))
    (nonabelian : ∀ k : ℕ, cutoff ≤ k →
      ∃ s t : alternatingGroup (Fin k), s * t ≠ t * s)
    (c : BlockCover H B) (a : V)
    [Fintype {x : V // c.label x = c.label a}] :
    sigma cutoff a H ≤ sigma cutoff (c.label a) c.project.range +
      sigma cutoff (c.localBase a) (c.localProject a).range := by
  obtain ⟨u, v, huv, hu, hv⟩ :=
    chain_split_of_simple simple nonabelian (sigma_achieved hcutoff a H) c
  have htop := sigma_bounds_chain hcutoff hu
  have hlocal := sigma_bounds_chain hcutoff hv
  omega

end BlockCover

end GI
