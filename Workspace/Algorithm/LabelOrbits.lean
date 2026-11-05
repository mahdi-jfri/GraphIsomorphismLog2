module

public import Workspace.Algorithm.AggregationCanon
public import Workspace.Algorithm.PartitionCap
public import Workspace.Paper.Caps

@[expose] public section

/-!
# Orbits of the ideal certificate group and the cases of the aggregation

The aggregation of [H, Section 6.2], re-proved in Section A.3 of the paper for constant-size
certificates, splits into cases by the orbits of the ideal image `π(F_x) ≤ Alt(Γ)` of the
certificate group on the labels `Γ = [q]`:

* Case 2: some orbit `Φ` has more than `q/2` points (the dominant orbit). Case 2a: the
  restriction of `π(F_x)` to `Φ` contains `Alt(Φ)` (Lemma A.11). Case 2b: it does not.
* Case 1: no orbit has more than `q/2` points, and the support has at least `q/2` points
  (Section A.3, "Case 1 and balanced colored partitions": "Then `|S| ≥ q/2` and every orbit has
  size at most `q/2`").
* Case 3: the support has fewer than `q/2` points (Section A.3, "Balance parameters": "In
  Case 3, the discarded support has size below `q/2`").

This file defines the orbits (`lorb`), the dominant orbit (`domSet`, the set of points whose
orbit has more than `q/2` points), the support, the case (`aggCase`), and proves that all of
them commute with relabeling (`lorb_conj`, `domSet_conj`, `aggCase_conj`). It also gives the
canonical colored partition of Case 1 (`labelOrbitPart`) and its cap (`labelOrbitPart_cap`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Rectangle

variable {q : ℕ}

/-! ### Orbits on the labels -/

section Orbits

variable (H : Subgroup (Perm (Fin q)))

open Classical in
/-- The orbit of a label under a group of label permutations. -/
noncomputable def lorb (a : Fin q) : Finset (Fin q) :=
  Finset.univ.filter fun b => ∃ h ∈ H, h a = b

variable {H}

theorem mem_lorb {a b : Fin q} : b ∈ lorb H a ↔ ∃ h ∈ H, h a = b := by
  classical
  simp [lorb]

theorem self_mem_lorb (a : Fin q) : a ∈ lorb H a := mem_lorb.2 ⟨1, H.one_mem, rfl⟩

theorem lorb_eq_of_mem {a b : Fin q} (hb : b ∈ lorb H a) : lorb H b = lorb H a := by
  obtain ⟨h, hh, rfl⟩ := mem_lorb.1 hb
  ext c
  rw [mem_lorb, mem_lorb]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * h, H.mul_mem hk hh, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * h⁻¹, H.mul_mem hk (H.inv_mem hh), ?_⟩
    simp [Perm.mul_apply]

theorem mem_lorb_comm {a b : Fin q} : b ∈ lorb H a ↔ a ∈ lorb H b := by
  constructor
  · intro hb; rw [lorb_eq_of_mem hb]; exact self_mem_lorb a
  · intro ha; rw [lorb_eq_of_mem ha]; exact self_mem_lorb b

/-- Two orbits that meet are equal. -/
theorem lorb_eq_of_inter {a b c : Fin q} (ha : c ∈ lorb H a) (hb : c ∈ lorb H b) :
    lorb H a = lorb H b := (lorb_eq_of_mem ha).symm.trans (lorb_eq_of_mem hb)

/-- An element of the group maps each orbit onto itself. -/
theorem apply_mem_lorb {h : Perm (Fin q)} (hh : h ∈ H) {a b : Fin q} (hb : b ∈ lorb H a) :
    h b ∈ lorb H a := by
  obtain ⟨k, hk, rfl⟩ := mem_lorb.1 hb
  exact mem_lorb.2 ⟨h * k, H.mul_mem hh hk, rfl⟩

/-- **Orbits commute with relabeling**: the orbit of `σ a` under `σ H σ⁻¹` is `σ` of the orbit
of `a` under `H`. -/
theorem lorb_conj (σ : Perm (Fin q)) (a : Fin q) :
    lorb (Canon.conjGrp σ H) (σ a) = (lorb H a).map σ.toEmbedding := by
  ext b
  rw [mem_lorb, Finset.mem_map_equiv, mem_lorb]
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨σ⁻¹ * h * σ, Canon.mem_conjGrp.1 hh, ?_⟩
    simp [Perm.mul_apply]
  · rintro ⟨h, hh, hb⟩
    refine ⟨σ * h * σ⁻¹, Canon.mem_conjGrp.2 (by simpa [mul_assoc] using hh), ?_⟩
    simp only [Perm.mul_apply, Perm.inv_apply_self, hb]
    simp

end Orbits

/-! ### The dominant orbit -/

section Dominant

variable (H : Subgroup (Perm (Fin q)))

open Classical in
/-- **The dominant orbit**: the labels whose orbit has more than `q/2` points. It is empty or
one orbit (`domSet_eq_lorb`). -/
noncomputable def domSet : Finset (Fin q) :=
  Finset.univ.filter fun b => q < 2 * (lorb H b).card

variable {H}

theorem mem_domSet {b : Fin q} : b ∈ domSet H ↔ q < 2 * (lorb H b).card := by
  classical
  simp [domSet]

/-- Two orbits with more than `q/2` points each meet. -/
theorem lorb_meet {a b : Fin q} (ha : q < 2 * (lorb H a).card) (hb : q < 2 * (lorb H b).card) :
    lorb H a = lorb H b := by
  classical
  by_contra hne
  have hdis : Disjoint (lorb H a) (lorb H b) := by
    rw [Finset.disjoint_left]
    intro c hca hcb
    exact hne (lorb_eq_of_inter hca hcb)
  have h := Finset.card_union_of_disjoint hdis
  have hle : (lorb H a ∪ lorb H b).card ≤ q := by
    simpa using Finset.card_le_univ (lorb H a ∪ lorb H b)
  omega

/-- If a label has a dominant orbit, the dominant orbit is that orbit. -/
theorem domSet_eq_lorb {a : Fin q} (ha : a ∈ domSet H) : domSet H = lorb H a := by
  have ha' := mem_domSet.1 ha
  ext b
  rw [mem_domSet]
  constructor
  · intro hb
    rw [lorb_meet ha' hb]
    exact self_mem_lorb b
  · intro hb
    rw [lorb_eq_of_mem hb]
    exact ha'

/-- **The dominant orbit commutes with relabeling.** -/
theorem domSet_conj (σ : Perm (Fin q)) :
    domSet (Canon.conjGrp σ H) = (domSet H).map σ.toEmbedding := by
  ext b
  rw [mem_domSet, Finset.mem_map_equiv, mem_domSet]
  have : b = σ (σ.symm b) := by simp
  rw [this, lorb_conj, Finset.card_map]
  simp

theorem domSet_card_lt (hne : (domSet H).Nonempty) : q < 2 * (domSet H).card := by
  obtain ⟨a, ha⟩ := hne
  rw [domSet_eq_lorb ha]
  exact mem_domSet.1 ha

/-- Every element of the group maps the dominant orbit onto itself. -/
theorem apply_mem_domSet {h : Perm (Fin q)} (hh : h ∈ H) {b : Fin q} (hb : b ∈ domSet H) :
    h b ∈ domSet H := by
  rw [domSet_eq_lorb hb]
  exact apply_mem_lorb hh (self_mem_lorb b)

/-- **The restriction to the dominant orbit contains `Alt(Φ)`** (Lemma A.11: "`π(F_x)|_Φ ≥
Alt(Φ)`"): every even permutation of `Γ` that fixes the complement of `Φ` pointwise agrees on
`Φ` with an element of the group. -/
def GiantOn (H : Subgroup (Perm (Fin q))) (Φ : Finset (Fin q)) : Prop :=
  ∀ σ : Perm (Fin q), σ ∈ alternatingGroup (Fin q) → (∀ a, a ∉ Φ → σ a = a) →
    ∃ h ∈ H, ∀ a ∈ Φ, h a = σ a

theorem giantOn_conj {H : Subgroup (Perm (Fin q))} {Φ : Finset (Fin q)} (σ : Perm (Fin q))
    (h : GiantOn H Φ) : GiantOn (Canon.conjGrp σ H) (Φ.map σ.toEmbedding) := by
  intro τ hτ hfix
  have hτ' : σ⁻¹ * τ * σ ∈ alternatingGroup (Fin q) := by
    rw [Equiv.Perm.mem_alternatingGroup] at hτ ⊢
    simp [hτ]
  have hfix' : ∀ a, a ∉ Φ → (σ⁻¹ * τ * σ) a = a := by
    intro a ha
    have : σ a ∉ Φ.map σ.toEmbedding := by
      rw [Finset.mem_map_equiv]; simpa using ha
    simp [Perm.mul_apply, hfix _ this]
  obtain ⟨k, hk, hka⟩ := h _ hτ' hfix'
  refine ⟨σ * k * σ⁻¹, Canon.mem_conjGrp.2 (by simpa [mul_assoc] using hk), fun a ha => ?_⟩
  have ha' : σ⁻¹ a ∈ Φ := by
    rw [Finset.mem_map_equiv] at ha; simpa using ha
  have := hka _ ha'
  simp only [Perm.mul_apply, Perm.apply_inv_self] at this ⊢
  rw [this]
  simp

theorem giantOn_conj_iff {H : Subgroup (Perm (Fin q))} {Φ : Finset (Fin q)} (σ : Perm (Fin q)) :
    GiantOn (Canon.conjGrp σ H) (Φ.map σ.toEmbedding) ↔ GiantOn H Φ := by
  refine ⟨fun h => ?_, giantOn_conj σ⟩
  have h' := giantOn_conj σ⁻¹ h
  have e1 : Canon.conjGrp σ⁻¹ (Canon.conjGrp σ H) = H := by
    ext g; simp only [Canon.mem_conjGrp, inv_inv]; constructor <;> intro hg <;>
      simpa [mul_assoc] using hg
  have e2 : (Φ.map σ.toEmbedding).map (σ⁻¹).toEmbedding = Φ := by
    rw [Finset.map_map]; ext a; simp
  rwa [e1, e2] at h'

end Dominant

/-! ### The support and the cases -/

section Cases

variable (H : Subgroup (Perm (Fin q)))

open Classical in
/-- The support: the labels moved by some element, i.e. with an orbit of at least two points. -/
noncomputable def suppSet : Finset (Fin q) := Finset.univ.filter fun b => (lorb H b).card ≠ 1

theorem mem_suppSet {b : Fin q} : b ∈ suppSet H ↔ (lorb H b).card ≠ 1 := by
  classical
  simp [suppSet]

theorem suppSet_conj (σ : Perm (Fin q)) :
    suppSet (Canon.conjGrp σ H) = (suppSet H).map σ.toEmbedding := by
  ext b
  rw [mem_suppSet, Finset.mem_map_equiv, mem_suppSet]
  have : b = σ (σ.symm b) := by simp
  rw [this, lorb_conj, Finset.card_map]
  simp

/-- The cases of the aggregation ([H, Section 6.2]; Section A.3). -/
inductive AggCase
  | one
  | twoA
  | twoB
  | three
  deriving DecidableEq

open Classical in
/-- **The case of the aggregation** for the ideal certificate group `H`. -/
noncomputable def aggCase : AggCase :=
  if (domSet H).Nonempty then (if GiantOn H (domSet H) then .twoA else .twoB)
  else if q ≤ 2 * (suppSet H).card then .one else .three

/-- **The case commutes with relabeling.** -/
theorem aggCase_conj (σ : Perm (Fin q)) : aggCase (Canon.conjGrp σ H) = aggCase H := by
  classical
  unfold aggCase
  simp only [domSet_conj, suppSet_conj, Finset.map_nonempty, Finset.card_map, giantOn_conj_iff]

end Cases

/-! ### Case 1: the canonical colored partition into orbits -/

section CaseOne

/-- **The colored partition of Case 1** (Section A.3: "Color ideal points by their orbit lengths
and, for a length `ℓ ≥ 2`, partition its color class into the actual `π(F_x)`-orbits"). Each
label lies in its orbit, colored by the orbit length; a fixed point is a block of its own. -/
noncomputable def labelOrbitPart (H : Subgroup (Perm (Fin q))) : ColPart (Fin q) :=
  ⟨lorb H, fun a => (lorb H a).card⟩

/-- The colored partition commutes with relabeling. -/
theorem labelOrbitPart_conj (H : Subgroup (Perm (Fin q))) (σ : Perm (Fin q)) :
    σ • labelOrbitPart H = labelOrbitPart (Canon.conjGrp σ H) := by
  ext a b
  · simp only [ColPart.smul_blk, labelOrbitPart]
    have : a = σ (σ⁻¹ a) := by simp
    conv_rhs => rw [this, lorb_conj]
  · simp only [ColPart.smul_col, labelOrbitPart]
    have : a = σ (σ⁻¹ a) := by simp
    conv_rhs => rw [this, lorb_conj, Finset.card_map]

/-- The even permutations that fix an object. -/
def evenStab {Z : Type*} [MulAction (Perm (Fin q)) Z] (z : Z) :
    Subgroup (alternatingGroup (Fin q)) :=
  (MulAction.stabilizer (Perm (Fin q)) z).comap (alternatingGroup (Fin q)).subtype

theorem mem_evenStab {Z : Type*} [MulAction (Perm (Fin q)) Z] {z : Z}
    {e : alternatingGroup (Fin q)} : e ∈ evenStab z ↔ (e : Perm (Fin q)) • z = z := Iff.rfl

/-- The even stabilizer of a colored partition has every cap of the full stabilizer. -/
theorem evenStab_cap_of {z : ColPart (Fin q)} {s : ℕ}
    (h : GI.SectionCaps.Cap (MulAction.stabilizer (Perm (Fin q)) z) s) :
    GI.SectionCaps.Cap (evenStab (q := q) z) s := by
  let f : evenStab (q := q) z →* MulAction.stabilizer (Perm (Fin q)) z :=
    { toFun := fun e => ⟨(e.val : Perm (Fin q)), e.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine GI.SectionCaps.of_injective f (fun a b hab => ?_) h
  apply Subtype.ext; apply Subtype.ext
  have := congrArg (fun w : MulAction.stabilizer (Perm (Fin q)) z => (w : Perm (Fin q))) hab
  exact this

/-- Pairwise disjoint subsets of `Fin q`, each of size `c`, number at most `q / c`. -/
theorem card_blocks_mul_le {c : ℕ} (F : Finset (Finset (Fin q)))
    (hdis : ∀ B ∈ F, ∀ B' ∈ F, B ≠ B' → Disjoint B B') (hc : ∀ B ∈ F, B.card = c) :
    F.card * c ≤ q := by
  classical
  have h := Finset.card_biUnion (s := F) (t := id) (fun B hB B' hB' hne => hdis B hB B' hB' hne)
  have hsum : ∑ B ∈ F, (id B).card = F.card * c := by
    rw [Finset.sum_congr rfl (fun B hB => (hc B hB : (id B).card = c))]
    simp
  have hle : (F.biUnion id).card ≤ q := by simpa using Finset.card_le_univ (F.biUnion id)
  omega

/-- **The cap of Case 1** (Section A.3: "Every other class is a union of `r` blocks of size `ℓ`,
with both `ℓ ≤ q/2` and `r ≤ q/2`. … Therefore the full colored-partition group has hereditary
alternating-section width at most `q/2`"). If no orbit has more than `q/2` points and the
support has at least `q/2` points, every even permutation that fixes the orbit partition lies in
a group of alternating-section width at most `q/2`. -/
theorem labelOrbitPart_cap (H : Subgroup (Perm (Fin q))) (hdom : domSet H = ∅)
    (hsupp : q ≤ 2 * (suppSet H).card) :
    GI.SectionCaps.Cap (evenStab (q := q) (labelOrbitPart H)) (q / 2) := by
  classical
  apply evenStab_cap_of
  have hsmall : ∀ a, 2 * (lorb H a).card ≤ q := by
    intro a
    by_contra h
    have : a ∈ domSet H := mem_domSet.2 (by omega)
    rw [hdom] at this
    exact Finset.notMem_empty a this
  refine colPart_cap (labelOrbitPart H) (fun a => self_mem_lorb a)
    (fun a b hb => by simp only [labelOrbitPart]; rw [lorb_eq_of_mem hb]) (fun a => ?_) (fun c => ?_)
    _ (fun σ hσ => hσ)
  · have := hsmall a
    simp only [labelOrbitPart]
    omega
  · -- the blocks of color `c` are pairwise disjoint orbits of size `c`
    set F := (Finset.univ.filter fun a => (labelOrbitPart H).col a = c).image (labelOrbitPart H).blk
    have hdis : ∀ B ∈ F, ∀ B' ∈ F, B ≠ B' → Disjoint B B' := by
      intro B hB B' hB' hne
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hB
      obtain ⟨a', -, rfl⟩ := Finset.mem_image.1 hB'
      rw [Finset.disjoint_left]
      intro d hd hd'
      exact hne (lorb_eq_of_inter hd hd')
    have hc : ∀ B ∈ F, B.card = c := by
      intro B hB
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hB
      exact (Finset.mem_filter.1 ha).2
    have hmul := card_blocks_mul_le F hdis hc
    rcases Nat.lt_or_ge c 2 with hc2 | hc2
    · -- `c ≤ 1`: the blocks are fixed points (or there are none)
      have hF : F.card ≤ (Finset.univ.filter fun a => (lorb H a).card = 1).card := by
        refine Finset.card_image_le.trans (Finset.card_le_card fun a ha => ?_)
        have h1 := (Finset.mem_filter.1 ha).2
        have h2 : 0 < (lorb H a).card := Finset.card_pos.2 ⟨a, self_mem_lorb a⟩
        simp only [labelOrbitPart] at h1
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩
      have hfix : (Finset.univ.filter fun a => (lorb H a).card = 1).card +
          (suppSet H).card = q := by
        have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
          (p := fun a : Fin q => (lorb H a).card = 1)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        have e : suppSet H = Finset.univ.filter fun a => ¬(lorb H a).card = 1 := rfl
        rw [e]; exact this
      omega
    · have : F.card * 2 ≤ q := le_trans (Nat.mul_le_mul_left _ hc2) hmul
      omega

end CaseOne

end GI.Algorithm
