module

public import Workspace.JohnsonChains
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

namespace GI.Johnson

open scoped Pointwise

abbrev SubsetVertex (A : Type*) (t : ℕ) := {s : Finset A // s.card = t}

variable {A : Type*} [DecidableEq A]

/-- The actual action of permutations on subsets of one fixed cardinality. -/
def subsetAction (t : ℕ) : Equiv.Perm A →* Equiv.Perm (SubsetVertex A t) where
  toFun g :=
    { toFun s := ⟨g • s.val, by rw [Finset.card_smul_finset]; exact s.property⟩
      invFun s := ⟨g⁻¹ • s.val, by rw [Finset.card_smul_finset]; exact s.property⟩
      left_inv s := Subtype.ext (inv_smul_smul g s.val)
      right_inv s := Subtype.ext (smul_inv_smul g s.val) }
  map_one' := by
    apply Equiv.ext
    intro s
    exact Subtype.ext (one_smul (Equiv.Perm A) s.val)
  map_mul' g h := by
    apply Equiv.ext
    intro s
    exact Subtype.ext (mul_smul g h s.val)

@[simp] theorem subsetAction_apply (t : ℕ) (g : Equiv.Perm A) (s : SubsetVertex A t) :
    (subsetAction t g s).val = g • s.val := rfl

def subsetImage (t : ℕ) : Subgroup (Equiv.Perm (SubsetVertex A t)) :=
  (subsetAction t).range

theorem subsetAction_range_surjective (t : ℕ) :
    Function.Surjective (subsetAction (A := A) t).rangeRestrict := by
  rintro ⟨p, hp⟩
  obtain ⟨g, rfl⟩ := hp
  exact ⟨g, rfl⟩

variable [Fintype A]

/-- Every two distinct points are separated by a fixed-size nontrivial subset. -/
theorem exists_subsetVertex_separating {t : ℕ} (ht : 1 ≤ t)
    (htop : t < Fintype.card A) (x y : A) (hxy : x ≠ y) :
    ∃ s : SubsetVertex A t, x ∈ s.val ∧ y ∉ s.val := by
  have hsubset : ({x} : Finset A) ⊆ Finset.univ.erase y := by
    simp [hxy]
  have hsmall : ({x} : Finset A).card ≤ t := by simpa using ht
  have hlarge : t ≤ (Finset.univ.erase y : Finset A).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ y), Finset.card_univ]
    omega
  obtain ⟨s, hxs, hsy, hcard⟩ := Finset.exists_subsuperset_card_eq hsubset hsmall hlarge
  refine ⟨⟨s, hcard⟩, hxs (Finset.mem_singleton_self x), ?_⟩
  intro hy
  have hbad := hsy hy
  simp at hbad

theorem subsetAction_eq_one_imp {t : ℕ} (ht : 1 ≤ t)
    (htop : t < Fintype.card A) (g : Equiv.Perm A) (hg : subsetAction t g = 1) :
    g = 1 := by
  apply Equiv.ext
  intro x
  change g x = x
  by_contra hmove
  obtain ⟨s, hx, hnot⟩ := exists_subsetVertex_separating ht htop x (g x) (Ne.symm hmove)
  have hset : g • s.val = s.val :=
    congrArg (fun p : Equiv.Perm (SubsetVertex A t) => (p s).val) hg
  have hm : g x ∈ g • s.val := (Finset.smul_mem_smul_finset_iff g).mpr hx
  rw [hset] at hm
  exact hnot hm

/-- Faithfulness is proved by separating points; it is not an input premise. -/
theorem subsetAction_injective {t : ℕ} (ht : 1 ≤ t) (htop : t < Fintype.card A) :
    Function.Injective (subsetAction (A := A) t) := by
  intro g h heq
  have hone : subsetAction t (g * h⁻¹) = 1 := by
    rw [map_mul, map_inv, heq, mul_inv_cancel]
  exact mul_inv_eq_one.mp (subsetAction_eq_one_imp ht htop (g * h⁻¹) hone)

/-- The original natural symmetric group is isomorphic to its actual subset image. -/
noncomputable def subsetActionEquiv {t : ℕ} (ht : 1 ≤ t) (htop : t < Fintype.card A) :
    Equiv.Perm A ≃* subsetImage (A := A) t :=
  MulEquiv.ofBijective (subsetAction t).rangeRestrict
    ⟨fun _ _ h => subsetAction_injective ht htop (congrArg Subtype.val h),
      subsetAction_range_surjective t⟩

noncomputable def naturalProjection {t : ℕ} (ht : 1 ≤ t) (htop : t < Fintype.card A) :
    subsetImage (A := A) t →* Equiv.Perm A :=
  (subsetActionEquiv ht htop).symm.toMonoidHom

theorem naturalProjection_apply {t : ℕ} (ht : 1 ≤ t) (htop : t < Fintype.card A)
    (g : Equiv.Perm A) :
    naturalProjection ht htop ((subsetAction t).rangeRestrict g) = g :=
  (subsetActionEquiv ht htop).symm_apply_apply g

theorem naturalProjection_range {t : ℕ} (ht : 1 ≤ t) (htop : t < Fintype.card A) :
    (naturalProjection ht htop).range = ⊤ := by
  apply MonoidHom.range_eq_top.mpr
  intro g
  exact ⟨(subsetAction t).rangeRestrict g, naturalProjection_apply ht htop g⟩

/-- JohnsonCover for the concrete fixed-cardinality subset action. -/
noncomputable def fullCover {t : ℕ} (ht : 1 ≤ t) (htop : t < Fintype.card A) :
    JohnsonCover (subsetImage (A := A) t) A where
  project := naturalProjection ht htop
  label := ⟨Subtype.val, Subtype.val_injective⟩
  equivariant h s := by
    obtain ⟨g, rfl⟩ := subsetAction_range_surjective t h
    change (subsetAction t g s).val = naturalProjection ht htop
      ((subsetAction t).rangeRestrict g) • s.val
    rw [naturalProjection_apply]
    rfl

theorem fullCover_project_range {t : ℕ} (ht : 1 ≤ t) (htop : t < Fintype.card A) :
    (fullCover ht htop).project.range = ⊤ := naturalProjection_range ht htop

theorem fullCover_label_card {t : ℕ} (ht : 1 ≤ t) (htop : t < Fintype.card A)
    (s : SubsetVertex A t) : ((fullCover ht htop).label s).card = t := s.property

omit [DecidableEq A] in
theorem card_subsetVertex (t : ℕ) :
    Fintype.card (SubsetVertex A t) = Nat.choose (Fintype.card A) t :=
  Fintype.card_finset_len t

noncomputable def finCover {m t : ℕ} (ht : 1 ≤ t) (htop : t < m) :
    JohnsonCover (subsetImage (A := Fin m) t) (Fin m) :=
  fullCover ht (by simpa using htop)

theorem card_subsetVertex_fin (m t : ℕ) :
    Fintype.card (SubsetVertex (Fin m) t) = Nat.choose m t := by
  simpa only [Fintype.card_fin] using card_subsetVertex (A := Fin m) t

end GI.Johnson
