import Workspace.Algorithm.OutDesign
import Workspace.Algorithm.RefineFn
import Workspace.Cited.SixTransitive
import Mathlib.SetTheory.Cardinal.Embedding

/-!
# Case 2b of the aggregation: anchors, an orbital, and its coherent refinement

Section A.3, "Aggregation and orbital colors": "In Case 2b of that aggregation, let `Φ` be the
dominant orbit of the ideal image of `F`, and let `d ≤ 5` be its maximal degree of
transitivity, using the CFSG bound stated there. Fix an ordered source tuple of `d - 1`
distinct points and branch over its at most `q^{d-1}` possible target images. On
`C = Φ \ {x₁, …, x_{d-1}}`, the resulting subgroup `U` is transitive but not two-transitive.
Choose one proper non-diagonal source orbital `𝒪 ⊂ C²`. Branch over its at most `|C|² ≤ q²`
possible target orbitals. For each branch, color the directed graph by membership in `𝒪`, and
apply the canonical coherent refinement from Helfgott's exposition to this binary coloring."

Here `H` is the ideal certificate group (`Canon.grp`) and `t` the individualized source tuple.

* `TransOn H Φ r`: `H` is transitive on the injective `r`-tuples of `Φ`; `transDeg H Φ` is the
  largest `r ≤ |Φ|` with this property (the maximal degree of transitivity `d`).
* `orbitalAt`: the anchors are `t_0, …, t_{d-2}` (`ancSet`), `U` is their pointwise stabilizer
  in `H` (`UFix`), the orbital `𝒪` is the `U`-orbit of the pair `(t_{d-1}, t_d)` (`Orb`); the
  binary coloring (`orbCol`) records membership in `C` of both points and membership in `𝒪`,
  and gives each anchor its own singleton color, read off its position in `t` (Section A.3,
  "Balance parameters": "Keep individualized labels as singleton colors"; `orbCol_anchor`);
  its canonical coherent refinement (`GI.Cited.KaryCoherentRefinement` for `k = 2`) is the pair
  configuration, with fiber the vertex class of `t_{d-1}` and source vertex `t_{d-1}`.
* `orbitalOut_smul`: every step is defined by the data, so the object commutes with relabeling.
* `orbitalAt_good`: if `t_0, …, t_d` are distinct points of `Φ`, `H` is `d`-transitive and not
  `(d+1)`-transitive on `Φ`, then the object is good. The vertex class contains `C` because `U`
  is transitive on `C` and refinement keeps the automorphisms of the binary coloring
  ("The resulting coherent configuration is homogeneous: `U` preserves the binary graph and is
  transitive, and refinement preserves all these automorphisms"); it is nontrivial because some
  pair of distinct points of `C` is outside `𝒪` (otherwise `H` would be `(d+1)`-transitive) and
  "refinement never merges their colors".
* `transDeg_le_five`: `d ≤ 5` when `H` is not giant on `Φ` and `|Φ| ≥ 6`
  (`GI.Cited.SixTransitiveContainsAlt`), so the source tuple has a bounded length.
* `exists_orbitalOut_good`: in Case 2b a good source tuple of any length `ℓ ≥ 6` exists.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Cited

variable {q ℓ : ℕ}

/-! ### Degree of transitivity -/

section Trans

/-- `H` is transitive on the injective `r`-tuples of points of `Φ`. -/
def TransOn (H : Subgroup (Perm (Fin q))) (Φ : Finset (Fin q)) (r : ℕ) : Prop :=
  ∀ a b : Fin r → Fin q, Function.Injective a → Function.Injective b → (∀ i, a i ∈ Φ) →
    (∀ i, b i ∈ Φ) → ∃ h ∈ H, ∀ i, h (a i) = b i

open Classical in
/-- **The maximal degree of transitivity** of `H` on `Φ` (at most `|Φ|`). -/
noncomputable def transDeg (H : Subgroup (Perm (Fin q))) (Φ : Finset (Fin q)) : ℕ :=
  ((Finset.range (Φ.card + 1)).filter (TransOn H Φ)).sup id

theorem transOn_zero (H : Subgroup (Perm (Fin q))) (Φ : Finset (Fin q)) : TransOn H Φ 0 :=
  fun _ _ _ _ _ _ => ⟨1, H.one_mem, fun i => i.elim0⟩

theorem transDeg_spec (H : Subgroup (Perm (Fin q))) (Φ : Finset (Fin q)) :
    TransOn H Φ (transDeg H Φ) ∧ transDeg H Φ ≤ Φ.card := by
  classical
  have hne : ((Finset.range (Φ.card + 1)).filter (TransOn H Φ)).Nonempty :=
    ⟨0, Finset.mem_filter.2 ⟨by simp, transOn_zero H Φ⟩⟩
  obtain ⟨r, hr, he⟩ := Finset.exists_mem_eq_sup _ hne id
  have hr' := Finset.mem_filter.1 hr
  unfold transDeg
  rw [he]
  exact ⟨hr'.2, by simpa [Nat.lt_succ_iff] using hr'.1⟩

theorem le_transDeg {H : Subgroup (Perm (Fin q))} {Φ : Finset (Fin q)} {r : ℕ}
    (hr : r ≤ Φ.card) (h : TransOn H Φ r) : r ≤ transDeg H Φ := by
  classical
  unfold transDeg
  exact Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨by simp; omega, h⟩)

theorem transOn_conj {H : Subgroup (Perm (Fin q))} {Φ : Finset (Fin q)} (σ : Perm (Fin q))
    {r : ℕ} (h : TransOn H Φ r) : TransOn (Canon.conjGrp σ H) (Φ.map σ.toEmbedding) r := by
  intro a b ha hb haΦ hbΦ
  have hmem : ∀ x, x ∈ Φ.map σ.toEmbedding ↔ σ⁻¹ x ∈ Φ := fun x => by
    rw [Finset.mem_map_equiv]; rfl
  obtain ⟨g, hg, hgab⟩ := h (fun i => σ⁻¹ (a i)) (fun i => σ⁻¹ (b i))
    (fun i j e => ha (σ⁻¹.injective e)) (fun i j e => hb (σ⁻¹.injective e))
    (fun i => (hmem _).1 (haΦ i)) (fun i => (hmem _).1 (hbΦ i))
  refine ⟨σ * g * σ⁻¹, Canon.mem_conjGrp.2 (by simpa [mul_assoc] using hg), fun i => ?_⟩
  have := hgab i
  simp only [Perm.mul_apply] at this ⊢
  rw [this, Perm.apply_inv_self]

theorem transOn_conj_iff {H : Subgroup (Perm (Fin q))} {Φ : Finset (Fin q)} (σ : Perm (Fin q))
    (r : ℕ) : TransOn (Canon.conjGrp σ H) (Φ.map σ.toEmbedding) r ↔ TransOn H Φ r := by
  refine ⟨fun h => ?_, transOn_conj σ⟩
  have h' := transOn_conj σ⁻¹ h
  have e1 : Canon.conjGrp σ⁻¹ (Canon.conjGrp σ H) = H := by
    ext g; simp only [Canon.mem_conjGrp, inv_inv]; constructor <;> intro hg <;>
      simpa [mul_assoc] using hg
  have e2 : (Φ.map σ.toEmbedding).map (σ⁻¹).toEmbedding = Φ := by
    rw [Finset.map_map]; ext a; simp
  rwa [e1, e2] at h'

theorem transDeg_conj (H : Subgroup (Perm (Fin q))) (Φ : Finset (Fin q)) (σ : Perm (Fin q)) :
    transDeg (Canon.conjGrp σ H) (Φ.map σ.toEmbedding) = transDeg H Φ := by
  classical
  unfold transDeg
  rw [Finset.card_map]
  congr 1
  ext r
  simp only [Finset.mem_filter, transOn_conj_iff]

/-- **Transitivity goes down**: an `r`-transitive group is `s`-transitive for `s ≤ r ≤ |Φ|`
(extend injective `s`-tuples of `Φ` to injective `r`-tuples). -/
theorem TransOn.mono {H : Subgroup (Perm (Fin q))} {Φ : Finset (Fin q)} {r s : ℕ}
    (h : TransOn H Φ r) (hsr : s ≤ r) (hr : r ≤ Φ.card) : TransOn H Φ s := by
  intro a b ha hb haΦ hbΦ
  have hcard : r ≤ Nat.card Φ := by simpa using hr
  let ea : Fin s ↪ Φ := ⟨fun i => ⟨a i, haΦ i⟩, fun i j e => ha (congrArg Subtype.val e)⟩
  let eb : Fin s ↪ Φ := ⟨fun i => ⟨b i, hbΦ i⟩, fun i j e => hb (congrArg Subtype.val e)⟩
  obtain ⟨Ea, hEa⟩ := Fin.Embedding.restrictSurjective_of_le_natCard hsr hcard ea
  obtain ⟨Eb, hEb⟩ := Fin.Embedding.restrictSurjective_of_le_natCard hsr hcard eb
  obtain ⟨g, hg, hgab⟩ := h (fun i => (Ea i).1) (fun i => (Eb i).1)
    (fun i j e => Ea.injective (Subtype.ext e)) (fun i j e => Eb.injective (Subtype.ext e))
    (fun i => (Ea i).2) (fun i => (Eb i).2)
  refine ⟨g, hg, fun i => ?_⟩
  have h1 : (Ea (Fin.castLE hsr i)).1 = a i := by
    have := congrArg (fun e : Fin s ↪ Φ => (e i).1) hEa
    simpa [ea] using this
  have h2 : (Eb (Fin.castLE hsr i)).1 = b i := by
    have := congrArg (fun e : Fin s ↪ Φ => (e i).1) hEb
    simpa [eb] using this
  rw [← h1, ← h2]
  exact hgab _

/-- **A `6`-transitive group is giant** (`GI.Cited.SixTransitiveContainsAlt`, transported from
`Fin |Φ|` to `Φ`): if `H` preserves `Φ`, `|Φ| ≥ 6` and `H` is `6`-transitive on `Φ`, then `H`
induces `Alt(Φ)` on `Φ`. -/
theorem giantOn_of_transOn_six (h6 : SixTransitiveContainsAlt) {H : Subgroup (Perm (Fin q))}
    {Φ : Finset (Fin q)} (hpres : ∀ h ∈ H, ∀ a ∈ Φ, h a ∈ Φ) (hΦ : 6 ≤ Φ.card)
    (ht : TransOn H Φ 6) : GiantOn H Φ := by
  classical
  have hiff : ∀ h ∈ H, ∀ a, a ∈ Φ ↔ h a ∈ Φ := by
    intro h hh a
    refine ⟨hpres h hh a, fun ha => ?_⟩
    have := hpres h⁻¹ (H.inv_mem hh) _ ha
    rwa [Perm.inv_apply_self] at this
  set n := Φ.card
  let e : Φ ≃ Fin n := Φ.equivFin
  let ρ : H →* Perm (Fin n) :=
    { toFun := fun h => e.permCongr ((h : Perm (Fin q)).subtypePerm fun x => (hiff h h.2 x).symm)
      map_one' := by ext i; simp
      map_mul' := fun g h => by ext i; simp [Equiv.permCongr_apply] }
  have hρ : ∀ (h : H) (a : Fin q) (ha : a ∈ Φ), ρ h (e ⟨a, ha⟩) = e ⟨(h : Perm (Fin q)) a,
      hpres h h.2 a ha⟩ := by
    intro h a ha
    simp [ρ, Equiv.permCongr_apply]
  have h6' : ∀ a b : Fin 6 ↪ Fin n, ∃ g ∈ ρ.range, ∀ i, g (a i) = b i := by
    intro a b
    obtain ⟨h, hh, hab⟩ := ht (fun i => (e.symm (a i)).1) (fun i => (e.symm (b i)).1)
      (fun i j h => a.injective (e.symm.injective (Subtype.ext h)))
      (fun i j h => b.injective (e.symm.injective (Subtype.ext h)))
      (fun i => (e.symm (a i)).2) (fun i => (e.symm (b i)).2)
    refine ⟨ρ ⟨h, hh⟩, ⟨_, rfl⟩, fun i => ?_⟩
    have := hρ ⟨h, hh⟩ _ (e.symm (a i)).2
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply] at this
    rw [this]
    have hb : (⟨h (e.symm (a i)).1, hpres h hh _ (e.symm (a i)).2⟩ : Φ) = e.symm (b i) :=
      Subtype.ext (hab i)
    rw [hb, Equiv.apply_symm_apply]
  have halt := h6 n hΦ ρ.range h6'
  intro σ hσ hfix
  have hmaps : ∀ x, x ∈ Φ ↔ σ x ∈ Φ := by
    intro x
    constructor
    · intro hx
      by_contra hσx
      have h1 := σ.injective (hfix _ hσx)
      rw [h1] at hσx
      exact hσx hx
    · intro hσx
      by_contra hx
      rw [hfix x hx] at hσx
      exact hx hσx
  let σ' : Perm Φ := subtypePerm σ fun x => (hmaps x).symm
  have hσ' : sign σ' = 1 := by
    have := sign_subtypePerm σ (p := fun x => x ∈ Φ) (fun x => (hmaps x).symm)
      (fun x hx => by by_contra h; exact hx (hfix x h))
    rw [Perm.mem_alternatingGroup] at hσ
    convert this.trans hσ using 3
  have hτ : e.permCongr σ' ∈ alternatingGroup (Fin n) := by
    rw [Perm.mem_alternatingGroup, sign_permCongr]; exact hσ'
  obtain ⟨h, hh⟩ := halt hτ
  refine ⟨h, h.2, fun a ha => ?_⟩
  have := congrArg (fun p : Perm (Fin n) => p (e ⟨a, ha⟩)) hh
  simp only at this
  rw [hρ h a ha] at this
  have h2 : e.permCongr σ' (e ⟨a, ha⟩) = e ⟨σ a, (hmaps a).1 ha⟩ := by
    simp [Equiv.permCongr_apply, σ']
  rw [h2] at this
  exact congrArg Subtype.val (e.injective this)

/-- **The degree of transitivity is at most `5`** in Case 2b ("let `d ≤ 5` be its maximal degree
of transitivity, using the CFSG bound stated there"). -/
theorem transDeg_le_five (h6 : SixTransitiveContainsAlt) {H : Subgroup (Perm (Fin q))}
    {Φ : Finset (Fin q)} (hpres : ∀ h ∈ H, ∀ a ∈ Φ, h a ∈ Φ) (hΦ : 6 ≤ Φ.card)
    (hng : ¬ GiantOn H Φ) : transDeg H Φ ≤ 5 := by
  by_contra hd
  obtain ⟨htr, hle⟩ := transDeg_spec H Φ
  exact hng (giantOn_of_transOn_six h6 hpres hΦ (htr.mono (by omega) hle))

/-- A group with one orbit `Φ` is `1`-transitive on it. -/
theorem transOn_one_of_orbit {H : Subgroup (Perm (Fin q))} {Φ : Finset (Fin q)}
    (h : ∀ a ∈ Φ, ∀ b ∈ Φ, ∃ g ∈ H, g a = b) : TransOn H Φ 1 := by
  intro a b _ _ ha hb
  obtain ⟨g, hg, hgab⟩ := h _ (ha 0) _ (hb 0)
  exact ⟨g, hg, fun i => by rw [Fin.fin_one_eq_zero i]; exact hgab⟩

/-- A group that is `|Φ|`-transitive on `Φ` induces `Sym(Φ)`, in particular `Alt(Φ)`. -/
theorem giantOn_of_transOn_card {H : Subgroup (Perm (Fin q))} {Φ : Finset (Fin q)}
    (ht : TransOn H Φ Φ.card) : GiantOn H Φ := by
  intro σ _ hfix
  have hmaps : ∀ x, x ∈ Φ → σ x ∈ Φ := by
    intro x hx
    by_contra hσx
    have h1 := σ.injective (hfix _ hσx)
    rw [h1] at hσx
    exact hσx hx
  let a : Fin Φ.card → Fin q := fun i => (Φ.equivFin.symm i).1
  obtain ⟨h, hh, hab⟩ := ht a (fun i => σ (a i))
    (fun i j e => Φ.equivFin.symm.injective (Subtype.ext e))
    (fun i j e => Φ.equivFin.symm.injective (Subtype.ext (σ.injective e)))
    (fun i => (Φ.equivFin.symm i).2) (fun i => hmaps _ (Φ.equivFin.symm i).2)
  refine ⟨h, hh, fun x hx => ?_⟩
  have := hab (Φ.equivFin ⟨x, hx⟩)
  simpa [a] using this

end Trans

/-! ### The anchored orbital and its refinement -/

section Orbital

/-- The anchors `t_0, …, t_{d-2}`. -/
noncomputable def ancSet (t : Fin ℓ → Fin q) (d : ℕ) : Finset (Fin q) :=
  (Finset.univ.filter fun i : Fin ℓ => i.val + 1 < d).image t

/-- `h ∈ U`: an element of `H` that fixes the anchors pointwise. -/
def UFix (H : Subgroup (Perm (Fin q))) (A : Finset (Fin q)) (h : Perm (Fin q)) : Prop :=
  h ∈ H ∧ ∀ a ∈ A, h a = a

/-- The orbital `𝒪`: the `U`-orbit of the pair `(u, v)`. -/
def Orb (H : Subgroup (Perm (Fin q))) (A : Finset (Fin q)) (u v a b : Fin q) : Prop :=
  ∃ h, UFix H A h ∧ h u = a ∧ h v = b

/-- The anchors `t_0, …, t_{d-2}` as a list, in the order of their positions in `t` (a value
repeated in `t` appears more than once). -/
def ancList (t : Fin ℓ → Fin q) (d : ℕ) : List (Fin q) := ((List.finRange ℓ).map t).take (d - 1)

theorem mem_ancList (t : Fin ℓ → Fin q) (d : ℕ) (a : Fin q) :
    a ∈ ancList t d ↔ a ∈ ancSet t d := by
  classical
  unfold ancList ancSet
  rw [List.mem_take_iff_getElem, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.length_map, List.length_finRange] at hi
    refine ⟨⟨i, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp; omega⟩, ?_⟩
    simp
  · rintro ⟨i, hi, rfl⟩
    have hi' := (Finset.mem_filter.1 hi).2
    exact ⟨i.val, by simp; omega, by simp⟩

open Classical in
/-- **The binary coloring** of Case 2b: membership in `C` of both points and membership in the
orbital ("color the directed graph by membership in `𝒪`"), with the anchors as singleton colors
(Section A.3, "Balance parameters": "Keep individualized labels as singleton colors"). The
diagonal pair `(a, a)` of an anchor `a` gets the color `8 + i`, where `i` is the first position
of `a` in the list `as` of the anchors. The other pairs keep the colors `0, …, 7`. The anchor's
position, not its value, gives its color, so the coloring commutes with relabeling
(`orbCol_conj`). -/
noncomputable def orbCol (H : Subgroup (Perm (Fin q))) (C A : Finset (Fin q)) (as : List (Fin q))
    (u v : Fin q) : (Fin 2 → Fin q) → ℕ := fun w =>
  if w 0 = w 1 ∧ w 0 ∈ as then 8 + as.idxOf (w 0) else
    (if w 0 ∈ C then 4 else 0) + (if w 1 ∈ C then 2 else 0) +
      (if Orb H A u v (w 0) (w 1) then 1 else 0)

/-- **Each anchor is a singleton color**: a pair with the color of the diagonal pair `(a, a)` of
an anchor `a` is that diagonal pair. -/
theorem orbCol_anchor (H : Subgroup (Perm (Fin q))) (C A : Finset (Fin q)) (as : List (Fin q))
    (u v a : Fin q) (ha : a ∈ as) (w : Fin 2 → Fin q)
    (hw : orbCol H C A as u v w = orbCol H C A as u v (fun _ => a)) : w 0 = a ∧ w 1 = a := by
  classical
  have e : orbCol H C A as u v (fun _ => a) = 8 + as.idxOf a := by
    show (if a = a ∧ a ∈ as then 8 + as.idxOf a else _) = _
    rw [if_pos ⟨rfl, ha⟩]
  rw [e] at hw
  unfold orbCol at hw
  by_cases h : w 0 = w 1 ∧ w 0 ∈ as
  · rw [if_pos h] at hw
    have e : w 0 = a := (List.idxOf_inj h.2).1 (by omega)
    exact ⟨e, h.1 ▸ e⟩
  · rw [if_neg h] at hw
    split_ifs at hw <;> omega

/-- A binary refinement: one side of the joint binary coherent refinement (`JointFn`, `k = 2`). -/
abbrev Refiner2 (q : ℕ) : Type := ((Fin 2 → Fin q) → ℕ) → ((Fin 2 → Fin q) → ℕ)

/-- The empty tuple. -/
def nilT : Fin 0 → Fin q := Fin.elim0

/-- **The refined orbital configuration**: the pair coloring of the refinement, with the
vertex class of `u` as fiber. -/
noncomputable def orbitalCfg (R : Refiner2 q) (H : Subgroup (Perm (Fin q)))
    (C A : Finset (Fin q)) (as : List (Fin q)) (u v : Fin q) : PairCfg q :=
  skelCfg (R (orbCol H C A as u v)) nilT
    (skel₁ (R (orbCol H C A as u v)) nilT u)

/-- **The object of Case 2b** for a degree `d`: anchors `t_0, …, t_{d-2}` (as singleton colors),
`C = Φ \ anchors`, the orbital of `(t_{d-1}, t_d)`, and source vertex `t_{d-1}`. -/
noncomputable def orbitalAt (R : Refiner2 q) (H : Subgroup (Perm (Fin q)))
    (t : Fin ℓ → Fin q) (d : ℕ) : CfgOut q :=
  if hd : d < ℓ then
    .pair (orbitalCfg R H (domSet H \ ancSet t d) (ancSet t d) (ancList t d) (t ⟨d - 1, by omega⟩)
      (t ⟨d, hd⟩))
      (t ⟨d - 1, by omega⟩)
  else .none

/-- **The object of Case 2b**, with `d` the maximal degree of transitivity of the ideal
certificate group on its dominant orbit. -/
noncomputable def orbitalOut (R : Refiner2 q) (H : Subgroup (Perm (Fin q)))
    (t : Fin ℓ → Fin q) : CfgOut q :=
  orbitalAt R H t (transDeg H (domSet H))

/-! #### Relabeling -/

variable (σ : Perm (Fin q))

theorem ancSet_rel (t : Fin ℓ → Fin q) (d : ℕ) :
    ancSet (σ ∘ t) d = (ancSet t d).map σ.toEmbedding := by
  classical
  unfold ancSet
  rw [Finset.map_eq_image, Finset.image_image]
  rfl

theorem orb_conj (H : Subgroup (Perm (Fin q))) (A : Finset (Fin q)) (u v a b : Fin q) :
    Orb (Canon.conjGrp σ H) (A.map σ.toEmbedding) (σ u) (σ v) a b ↔
      Orb H A u v (σ⁻¹ a) (σ⁻¹ b) := by
  constructor
  · rintro ⟨h, ⟨hH, hA⟩, hu, hv⟩
    refine ⟨σ⁻¹ * h * σ, ⟨Canon.mem_conjGrp.1 hH, fun x hx => ?_⟩, ?_, ?_⟩
    · have := hA (σ x) (Finset.mem_map_of_mem _ hx)
      simp only [Perm.mul_apply]
      change σ⁻¹ (h (σ x)) = x
      rw [this, Perm.inv_apply_self]
    · simp [Perm.mul_apply, hu]
    · simp [Perm.mul_apply, hv]
  · rintro ⟨g, ⟨hH, hA⟩, hu, hv⟩
    refine ⟨σ * g * σ⁻¹, ⟨Canon.mem_conjGrp.2 (by simpa [mul_assoc] using hH), fun x hx => ?_⟩,
      ?_, ?_⟩
    · rw [Finset.mem_map_equiv] at hx
      simp only [Perm.mul_apply]
      have := hA _ hx
      change σ (g (σ.symm x)) = x
      rw [this, Equiv.apply_symm_apply]
    · simp [Perm.mul_apply, hu]
    · simp [Perm.mul_apply, hv]

theorem ancList_rel (t : Fin ℓ → Fin q) (d : ℕ) :
    ancList (σ ∘ t) d = (ancList t d).map σ := by
  unfold ancList
  rw [List.map_take, List.map_map]

/-- Relabeling keeps the first position of a point in a list. -/
theorem idxOf_map_perm (as : List (Fin q)) (a : Fin q) :
    (as.map σ).idxOf (σ a) = as.idxOf a := by
  induction as with
  | nil => rfl
  | cons b as ih =>
    by_cases h : b = a
    · subst h
      rw [List.map_cons, List.idxOf_cons_eq _ rfl, List.idxOf_cons_eq _ rfl]
    · rw [List.map_cons, List.idxOf_cons_ne _ (fun e => h (σ.injective e)),
        List.idxOf_cons_ne _ h, ih]

theorem orbCol_conj (H : Subgroup (Perm (Fin q))) (C A : Finset (Fin q)) (as : List (Fin q))
    (u v : Fin q) :
    orbCol (Canon.conjGrp σ H) (C.map σ.toEmbedding) (A.map σ.toEmbedding) (as.map σ) (σ u)
      (σ v) = relCol σ (orbCol H C A as u v) := by
  classical
  funext w
  have e : w 0 = σ (σ.symm (w 0)) := (σ.apply_symm_apply _).symm
  have hm : w 0 ∈ as.map σ ↔ σ.symm (w 0) ∈ as := by
    rw [e, List.mem_map_of_injective σ.injective, σ.symm_apply_apply]
  have hi : (as.map σ).idxOf (w 0) = as.idxOf (σ.symm (w 0)) := by
    rw [e, idxOf_map_perm, σ.symm_apply_apply]
  have heq : w 0 = w 1 ↔ σ.symm (w 0) = σ.symm (w 1) := σ.symm.injective.eq_iff.symm
  simp only [orbCol, relCol, Function.comp, Finset.mem_map_equiv, orb_conj, hm, hi, heq]
  rfl

theorem nilT_rel : (σ ∘ nilT : Fin 0 → Fin q) = nilT := funext fun i => i.elim0

open Classical in
/-- The binary coloring of Case 2b at degree `d` (zero when `d ≥ ℓ`, where there is no object):
the input of the binary refinement. -/
noncomputable def orbColAt (H : Subgroup (Perm (Fin q))) (t : Fin ℓ → Fin q) (d : ℕ) :
    (Fin 2 → Fin q) → ℕ :=
  if hd : d < ℓ then
    orbCol H (domSet H \ ancSet t d) (ancSet t d) (ancList t d) (t ⟨d - 1, by omega⟩) (t ⟨d, hd⟩)
  else fun _ => 0

theorem orbColAt_conj (H : Subgroup (Perm (Fin q))) (t : Fin ℓ → Fin q) (d : ℕ) :
    orbColAt (Canon.conjGrp σ H) (σ ∘ t) d = relCol σ (orbColAt H t d) := by
  classical
  unfold orbColAt
  by_cases hd : d < ℓ
  · rw [dif_pos hd, dif_pos hd, domSet_conj, ancSet_rel, ancList_rel, ← Finset.map_sdiff]
    exact orbCol_conj σ H _ _ _ _ _
  · rw [dif_neg hd, dif_neg hd]
    rfl

/-- **Relabeling the refined orbital configuration.** The refiners `R` (for the first structure)
and `R'` (for the second) must carry the colorings along: `R'(σ c) = σ R(c)` for the binary
coloring `c` of the first structure. A joint refinement does this (`JointFn.carries`). -/
theorem orbitalCfg_conj (R R' : Refiner2 q) (H : Subgroup (Perm (Fin q)))
    (C A : Finset (Fin q)) (as : List (Fin q)) (u v : Fin q)
    (hR : R' (relCol σ (orbCol H C A as u v)) = relCol σ (R (orbCol H C A as u v))) :
    orbitalCfg R' (Canon.conjGrp σ H) (C.map σ.toEmbedding) (A.map σ.toEmbedding) (as.map σ)
      (σ u) (σ v) = σ • orbitalCfg R H C A as u v := by
  unfold orbitalCfg
  rw [orbCol_conj, hR, ← skelCfg_rel, nilT_rel]
  congr 1
  conv_lhs => rw [← nilT_rel σ]
  rw [skel₁_rel, Perm.inv_apply_self]

theorem orbitalAt_conj (R R' : Refiner2 q) (H : Subgroup (Perm (Fin q)))
    (t : Fin ℓ → Fin q) (d : ℕ)
    (hR : R' (relCol σ (orbColAt H t d)) = relCol σ (R (orbColAt H t d))) :
    orbitalAt R' (Canon.conjGrp σ H) (σ ∘ t) d = σ • orbitalAt R H t d := by
  classical
  unfold orbitalAt
  by_cases hd : d < ℓ
  · unfold orbColAt at hR
    rw [dif_pos hd] at hR
    rw [dif_pos hd, dif_pos hd, CfgOut.smul_pair, domSet_conj, ancSet_rel, ancList_rel,
      ← Finset.map_sdiff]
    simp only [Function.comp]
    rw [orbitalCfg_conj σ R R' _ _ _ _ _ _ hR]
  · rw [dif_neg hd, dif_neg hd, CfgOut.smul_none]

/-- The binary coloring of the object of Case 2b. -/
noncomputable def orbColOut (H : Subgroup (Perm (Fin q))) (t : Fin ℓ → Fin q) :
    (Fin 2 → Fin q) → ℕ :=
  orbColAt H t (transDeg H (domSet H))

theorem orbColOut_conj (H : Subgroup (Perm (Fin q))) (t : Fin ℓ → Fin q) :
    orbColOut (Canon.conjGrp σ H) (σ ∘ t) = relCol σ (orbColOut H t) := by
  unfold orbColOut
  rw [domSet_conj, transDeg_conj, orbColAt_conj]

/-- **The object of Case 2b commutes with relabeling** ("Every choice above is canonical"),
when the two refiners carry the binary colorings along. -/
theorem orbitalOut_conj (R R' : Refiner2 q) (H : Subgroup (Perm (Fin q)))
    (t : Fin ℓ → Fin q)
    (hR : R' (relCol σ (orbColOut H t)) = relCol σ (R (orbColOut H t))) :
    orbitalOut R' (Canon.conjGrp σ H) (σ ∘ t) = σ • orbitalOut R H t := by
  unfold orbitalOut
  unfold orbColOut at hR
  rw [domSet_conj, transDeg_conj, orbitalAt_conj σ R R' _ _ _ hR]

/-- **A joint refinement carries the binary colorings along**: with `R` the first side and `R'`
the second side of the joint refinement of `(c, σ c)`. -/
theorem joint_carries2 (J : JointFn) (c : (Fin 2 → Fin q) → ℕ) :
    J.right q 2 c (relCol σ c) = relCol σ (J.left q 2 (relCol σ c) c) := by
  have h : CarriesTo σ c (relCol σ c) := (carriesTo_iff σ _ _).2 rfl
  exact (carriesTo_iff σ _ _).1 (J.carries q 2 h)

end Orbital

/-! ### The object of Case 2b is good -/

section Good

theorem refine2_spec {R : Refiner2 q} (hR : SideOK R) (c : (Fin 2 → Fin q) → ℕ) :
    IsConfiguration (R c) ∧ IsCoherent (R c) :=
  ⟨(hR c).1, (hR c).2.1⟩

/-- Refinement never merges colors (second clause of `GI.Cited.KaryCoherentRefinement`). -/
theorem refine2_refines {R : Refiner2 q} (hR : SideOK R) (c : (Fin 2 → Fin q) → ℕ)
    {x y : Fin 2 → Fin q} (h : R c x = R c y) : c x = c y :=
  (hR c).2.2.1 x y h

/-- Refinement keeps the automorphisms of the coloring (third clause). -/
theorem refine2_inv {R : Refiner2 q} (hR : SideOK R) {c : (Fin 2 → Fin q) → ℕ}
    {h : Perm (Fin q)} (hc : relCol h c = c) (w : Fin 2 → Fin q) :
    R c (h.symm ∘ w) = R c w := by
  have hcar : CarriesTo h c c := (carriesTo_iff h c c).2 hc.symm
  have := (carriesTo_iff h _ _).1 ((hR c).2.2.2 h hcar)
  exact (congrFun this w).symm

theorem padTuple_nil_comp {k : ℕ} (f : Fin q → Fin q) (a : Fin q) :
    f ∘ (padTuple nilT a : Fin k → Fin q) = padTuple nilT (f a) := by
  funext i
  simp [padTuple]

theorem padTuple₂_nil_zero (a b : Fin q) : (padTuple₂ nilT a b : Fin 2 → Fin q) 0 = a := by
  simp [padTuple₂]

theorem padTuple₂_nil_one (a b : Fin q) : (padTuple₂ nilT a b : Fin 2 → Fin q) 1 = b := by
  simp [padTuple₂]

/-- **The object of Case 2b is good** (Section A.3, "Aggregation and orbital colors": "The
resulting coherent configuration is homogeneous … It is nontrivial"; "Balance parameters":
"`|C| ≥ δq` for `0 < δ ≤ 1/4`, above a fixed absolute base degree"). Let `Φ` be the dominant
orbit, `1 ≤ d ≤ 5`, `H` `d`-transitive and not `(d+1)`-transitive on `Φ`, `q ≥ 16`, and let
`t_0, …, t_d` be distinct points of `Φ`. -/
theorem orbitalAt_good {R : Refiner2 q} (hR : SideOK R) {H : Subgroup (Perm (Fin q))}
    {t : Fin ℓ → Fin q} {d : ℕ} (hq : 16 ≤ q) (hd : d < ℓ) (hd1 : 1 ≤ d) (hd5 : d ≤ 5)
    (hdom : q < 2 * (domSet H).card)
    (htr : TransOn H (domSet H) d) (hntr : ¬ TransOn H (domSet H) (d + 1))
    (hinj : ∀ i j : Fin ℓ, i.val ≤ d → j.val ≤ d → t i = t j → i = j)
    (hin : ∀ i : Fin ℓ, i.val ≤ d → t i ∈ domSet H) {β : ℝ} :
    (orbitalAt R H t d).Good β := by
  classical
  unfold orbitalAt
  rw [dif_pos hd]
  set Φ := domSet H with hΦdef
  set A := ancSet t d with hAdef
  set C := Φ \ A with hCdef
  set u := t ⟨d - 1, by omega⟩ with hudef
  set v := t ⟨d, hd⟩ with hvdef
  set as := ancList t d with hasdef
  set c0 := orbCol H C A as u v with hc0def
  set c' := R c0 with hc'def
  show (orbitalCfg R H C A as u v).Good deltaB ∧ u ∈ (orbitalCfg R H C A as u v).fiber
  have hpres : ∀ h ∈ H, ∀ a ∈ Φ, h a ∈ Φ := fun h hh a ha => apply_mem_domSet hh ha
  have memA : ∀ a, a ∈ A ↔ ∃ i : Fin ℓ, i.val + 1 < d ∧ t i = a := by
    intro a; simp [hAdef, ancSet]
  -- `u` and `v` lie in `C` and differ
  have hinj' : ∀ (i j : ℕ) (hi : i < ℓ) (hj : j < ℓ), i ≤ d → j ≤ d → t ⟨i, hi⟩ = t ⟨j, hj⟩ →
      i = j := fun i j hi hj h1 h2 e => Fin.mk.inj_iff.1 (hinj _ _ h1 h2 e)
  have hin' : ∀ (i : ℕ) (hi : i < ℓ), i ≤ d → t ⟨i, hi⟩ ∈ Φ := fun i hi h => hin _ h
  have hnotA : ∀ (i : ℕ) (hi : i < ℓ), i ≤ d → d ≤ i + 1 → t ⟨i, hi⟩ ∉ A := by
    intro i hi hi1 hi2 ha
    obtain ⟨j, hj, hji⟩ := (memA _).1 ha
    have := hinj' j.val i j.2 hi (by omega) hi1 hji
    omega
  have huC : u ∈ C :=
    Finset.mem_sdiff.2 ⟨hin' _ _ (by omega), hnotA _ _ (by omega) (by omega)⟩
  have hvC : v ∈ C := Finset.mem_sdiff.2 ⟨hin' _ _ le_rfl, hnotA _ _ le_rfl (by omega)⟩
  have huv : u ≠ v := by
    intro e
    have := hinj' _ _ _ _ (by omega) le_rfl e
    omega
  -- the elements of `U`
  have hUinv : ∀ h, UFix H A h → UFix H A h⁻¹ := by
    rintro h ⟨hH, hA⟩
    refine ⟨H.inv_mem hH, fun a ha => ?_⟩
    conv_lhs => rw [← hA a ha]
    simp
  have hUΦ : ∀ h, UFix H A h → ∀ a, h a ∈ Φ ↔ a ∈ Φ := by
    intro h hh a
    refine ⟨fun ha => ?_, hpres h hh.1 a⟩
    have := hpres h⁻¹ (hUinv h hh).1 _ ha
    rwa [Perm.inv_apply_self] at this
  have hUA : ∀ h, UFix H A h → ∀ a, h a ∈ A ↔ a ∈ A := by
    intro h hh a
    refine ⟨fun ha => ?_, fun ha => by rw [hh.2 a ha]; exact ha⟩
    have := hh.2 _ ha
    rw [h.injective this] at ha
    exact ha
  have hUC : ∀ h, UFix H A h → ∀ a, h a ∈ C ↔ a ∈ C := by
    intro h hh a
    simp only [hCdef, Finset.mem_sdiff, hUΦ h hh, hUA h hh]
  have hUorb : ∀ h, UFix H A h → ∀ a b, Orb H A u v (h a) (h b) ↔ Orb H A u v a b := by
    intro h hh a b
    constructor
    · rintro ⟨g, hg, hgu, hgv⟩
      refine ⟨h⁻¹ * g, ⟨H.mul_mem (hUinv h hh).1 hg.1, fun x hx => ?_⟩, ?_, ?_⟩
      · simp only [Perm.mul_apply, hg.2 x hx]
        exact (hUinv h hh).2 x hx
      · simp [Perm.mul_apply, hgu]
      · simp [Perm.mul_apply, hgv]
    · rintro ⟨g, hg, hgu, hgv⟩
      refine ⟨h * g, ⟨H.mul_mem hh.1 hg.1, fun x hx => ?_⟩, ?_, ?_⟩
      · simp only [Perm.mul_apply, hg.2 x hx]
        exact hh.2 x hx
      · simp [Perm.mul_apply, hgu]
      · simp [Perm.mul_apply, hgv]
  have hUcol : ∀ h, UFix H A h → relCol h c0 = c0 := by
    intro h hh
    funext w
    have h1 := hUC h⁻¹ (hUinv h hh) (w 0)
    have h2 := hUC h⁻¹ (hUinv h hh) (w 1)
    have h3 := hUorb h⁻¹ (hUinv h hh) (w 0) (w 1)
    have h4 : h⁻¹ (w 0) = h⁻¹ (w 1) ↔ w 0 = w 1 := h⁻¹.injective.eq_iff
    -- `h⁻¹` fixes the anchors, so it keeps the anchor colors
    have h5 : (h⁻¹ (w 0) ∈ as ∧ as.idxOf (h⁻¹ (w 0)) = as.idxOf (w 0)) ↔ w 0 ∈ as := by
      by_cases hw : w 0 ∈ as
      · have hfix := (hUinv h hh).2 _ ((mem_ancList t d _).1 hw)
        simp only [hfix, hw, and_self]
      · refine iff_of_false (fun hc => hw ?_) hw
        have hfix := hh.2 _ ((mem_ancList t d _).1 hc.1)
        rw [Perm.apply_inv_self] at hfix
        rw [hfix]; exact hc.1
    simp only [relCol, hc0def, orbCol, Function.comp]
    change (if h⁻¹ (w 0) = h⁻¹ (w 1) ∧ h⁻¹ (w 0) ∈ as then 8 + as.idxOf (h⁻¹ (w 0)) else
        (if h⁻¹ (w 0) ∈ C then 4 else 0) + (if h⁻¹ (w 1) ∈ C then 2 else 0) +
        (if Orb H A u v (h⁻¹ (w 0)) (h⁻¹ (w 1)) then 1 else 0)) = _
    by_cases hw : w 0 = w 1 ∧ w 0 ∈ as
    · have hm := h5.2 hw.2
      rw [if_pos ⟨h4.2 hw.1, hm.1⟩, if_pos hw, hm.2]
    · rw [if_neg (fun hc => hw ⟨h4.1 hc.1, h5.1 ⟨hc.2, ?_⟩⟩), if_neg hw]
      · simp only [h1, h2, h3]
      · exact (h5.2 (by
          have hfix := hh.2 _ ((mem_ancList t d _).1 hc.2)
          rw [Perm.apply_inv_self] at hfix
          rw [hfix]; exact hc.2)).2
  -- `U` is transitive on `C`
  have htrans : ∀ a ∈ C, ∃ h, UFix H A h ∧ h u = a := by
    intro a ha
    obtain ⟨haΦ, haA⟩ := Finset.mem_sdiff.1 ha
    let α : Fin d → Fin q := fun i => t ⟨i.val, by omega⟩
    let β' : Fin d → Fin q := fun i => if i.val + 1 < d then t ⟨i.val, by omega⟩ else a
    have hα : Function.Injective α := fun i j e =>
      Fin.ext (hinj' _ _ _ _ (by omega) (by omega) e)
    have hβ : Function.Injective β' := by
      intro i j e
      simp only [β'] at e
      by_cases hi : i.val + 1 < d <;> by_cases hj : j.val + 1 < d
      · rw [if_pos hi, if_pos hj] at e
        exact Fin.ext (hinj' _ _ _ _ (by omega) (by omega) e)
      · rw [if_pos hi, if_neg hj] at e
        exact absurd ((memA a).2 ⟨_, hi, e⟩) haA
      · rw [if_neg hi, if_pos hj] at e
        exact absurd ((memA a).2 ⟨_, hj, e.symm⟩) haA
      · exact Fin.ext (by omega)
    obtain ⟨h, hh, hhab⟩ := htr α β' hα hβ (fun i => hin' _ _ (by omega)) (fun i => by
      simp only [β']; split_ifs
      · exact hin' _ _ (by omega)
      · exact haΦ)
    refine ⟨h, ⟨hh, fun x hx => ?_⟩, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := (memA x).1 hx
      have := hhab ⟨i.val, by omega⟩
      simp only [α, β', if_pos hi] at this
      exact this
    · have := hhab ⟨d - 1, by omega⟩
      simp only [α, β', show ¬ (d - 1 + 1 < d) by omega, if_false] at this
      exact this
  -- `C` lies in the fiber
  have hCfib : ∀ a ∈ C, a ∈ (orbitalCfg R H C A as u v).fiber := by
    intro a ha
    obtain ⟨h, hh, rfl⟩ := htrans a ha
    unfold orbitalCfg
    rw [mem_skelCfg_fiber]
    unfold skel₁
    rw [← refine2_inv hR (hUcol h hh), padTuple_nil_comp]
    simp only [Equiv.symm_apply_apply]
    rfl
  refine ⟨skelCfg_good (refine2_spec hR c0).1 (refine2_spec hR c0).2 (by omega) nilT _ ?_ ?_,
    hCfib u huC⟩
  · -- `|C| ≥ q/4`
    have hAcard : A.card ≤ 4 := by
      have h1 : A.card ≤ (Finset.univ.filter fun i : Fin ℓ => i.val + 1 < d).card :=
        Finset.card_image_le
      have h2 : (Finset.univ.filter fun i : Fin ℓ => i.val + 1 < d).card ≤
          (Finset.range (d - 1)).card :=
        Finset.card_le_card_of_injOn (fun i => i.val)
          (fun i hi => by simp at hi; simp; omega) (fun i _ j _ h => Fin.ext h)
      simp at h2
      omega
    have hC : Φ.card - A.card ≤ C.card := Finset.le_card_sdiff A Φ
    have hCf : C.card ≤ (orbitalCfg R H C A as u v).fiber.card := Finset.card_le_card hCfib
    have h4 : q ≤ 4 * (orbitalCfg R H C A as u v).fiber.card := by omega
    change deltaB * (q : ℝ) ≤ ((orbitalCfg R H C A as u v).fiber.card : ℝ)
    unfold deltaB
    have : (q : ℝ) ≤ 4 * ((orbitalCfg R H C A as u v).fiber.card : ℝ) := by exact_mod_cast h4
    linarith
  · -- nontriviality: some pair of distinct points of `C` lies outside the orbital
    have hβ₀ : Function.Injective (fun i : Fin d => t ⟨i.val, by omega⟩) := fun i j e =>
      Fin.ext (hinj' _ _ _ _ (by omega) (by omega) e)
    have hβ₀Φ : ∀ i : Fin d, t ⟨i.val, by omega⟩ ∈ Φ := fun i => hin' _ _ (by omega)
    unfold TransOn at hntr
    push Not at hntr
    obtain ⟨a, b, ha, hb, haΦ, hbΦ, hno⟩ := hntr
    -- move the first `d` entries of `a` and of `b` to the anchors and `u`
    have hmove : ∀ a : Fin (d + 1) → Fin q, Function.Injective a → (∀ i, a i ∈ Φ) →
        ∃ h ∈ H, (∀ i : Fin d, h (a i.castSucc) = t ⟨i.val, by omega⟩) ∧
          h (a (Fin.last d)) ∈ C ∧ h (a (Fin.last d)) ≠ u := by
      intro a ha haΦ
      obtain ⟨h, hh, hhab⟩ := htr (fun i => a i.castSucc) _
        (fun i j e => Fin.castSucc_injective _ (ha e)) hβ₀ (fun i => haΦ _) hβ₀Φ
      have hne : ∀ j : Fin ℓ, j.val < d → h (a (Fin.last d)) ≠ t j := by
        intro j hj e
        have e2 := hhab ⟨j.val, hj⟩
        simp only at e2
        rw [← e2] at e
        have := ha (h.injective e)
        exact (Fin.castSucc_lt_last _).ne' this
      refine ⟨h, hh, hhab, Finset.mem_sdiff.2 ⟨hpres h hh _ (haΦ _), fun hA => ?_⟩,
        hne _ (by simp only []; omega)⟩
      obtain ⟨j, hj, e⟩ := (memA _).1 hA
      exact hne j (by omega) e.symm
    obtain ⟨h₁, hh₁, h₁a, ha'C, ha'u⟩ := hmove a ha haΦ
    obtain ⟨h₂, hh₂, h₂b, hb'C, hb'u⟩ := hmove b hb hbΦ
    have hone : ¬ Orb H A u v u (h₁ (a (Fin.last d))) ∨ ¬ Orb H A u v u (h₂ (b (Fin.last d))) := by
      by_contra hboth
      push Not at hboth
      obtain ⟨⟨k₁, hk₁, hk₁u, hk₁v⟩, ⟨k₂, hk₂, hk₂u, hk₂v⟩⟩ := hboth
      obtain ⟨i, hi⟩ := hno (h₂⁻¹ * k₂ * k₁⁻¹ * h₁)
        (H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem hh₂) hk₂.1) (H.inv_mem hk₁.1)) hh₁)
      apply hi
      -- the elements `k₁⁻¹, k₂` fix the anchors and `u`
      have hfix : ∀ k, UFix H A k → k u = u → ∀ j : Fin d, k (t ⟨j.val, by omega⟩) =
          t ⟨j.val, by omega⟩ := by
        intro k hk hku j
        by_cases hj : j.val + 1 < d
        · exact hk.2 _ ((memA _).2 ⟨_, hj, rfl⟩)
        · have : (⟨j.val, by omega⟩ : Fin ℓ) = ⟨d - 1, by omega⟩ := Fin.mk.inj_iff.2 (by omega)
          rw [this]; exact hku
      have hk₁u' : k₁⁻¹ u = u := by rw [Perm.inv_eq_iff_eq]; exact hk₁u.symm
      induction i using Fin.lastCases with
      | last =>
        simp only [Perm.mul_apply]
        rw [← hk₁v, Perm.inv_apply_self, hk₂v, Perm.inv_apply_self]
      | cast j =>
        simp only [Perm.mul_apply]
        rw [h₁a j, hfix _ (hUinv _ hk₁) hk₁u' j, hfix _ hk₂ hk₂u j, ← h₂b j, Perm.inv_apply_self]
    have hw : ∃ w ∈ C, w ≠ u ∧ ¬ Orb H A u v u w := by
      rcases hone with h | h
      · exact ⟨_, ha'C, ha'u, h⟩
      · exact ⟨_, hb'C, hb'u, h⟩
    obtain ⟨w, hwC, hwu, hwO⟩ := hw
    refine ⟨u, hCfib u huC, v, hCfib v hvC, u, hCfib u huC, w, hCfib w hwC, huv,
      fun e => hwu e.symm, fun e => ?_⟩
    unfold skel₂ at e
    have h7 := refine2_refines hR c0 e
    have hO : Orb H A u v u v := ⟨1, ⟨H.one_mem, fun _ _ => rfl⟩, rfl, rfl⟩
    have hne1 : ¬ (u = v ∧ u ∈ as) := fun h => huv h.1
    have hne2 : ¬ (u = w ∧ u ∈ as) := fun h => hwu h.1.symm
    simp only [hc0def, orbCol, padTuple₂_nil_zero, padTuple₂_nil_one, if_neg hne1, if_neg hne2,
      if_pos huC, if_pos hvC, if_pos hwC, if_pos hO, if_neg hwO] at h7
    omega

/-- **A good source tuple exists for Case 2b** (Section A.3: "Fix an ordered source tuple of
`d - 1` distinct points … Choose one proper non-diagonal source orbital"): if the dominant orbit
`Φ` is nonempty, `H` is not giant on it, `q ≥ 16` and `ℓ ≥ 6`, some tuple `t` makes the object
good. The degree `d` of transitivity is between `1` (one orbit) and `5`
(`GI.Cited.SixTransitiveContainsAlt`), so `d + 1 ≤ 6 ≤ |Φ|` distinct points of `Φ` fill the first
`d + 1` positions of `t`. -/
theorem exists_orbitalOut_good (h6 : SixTransitiveContainsAlt)
    {H : Subgroup (Perm (Fin q))} (hq : 16 ≤ q) (hℓ : 6 ≤ ℓ) (hne : (domSet H).Nonempty)
    (hng : ¬ GiantOn H (domSet H)) {β : ℝ} :
    ∃ t : Fin ℓ → Fin q, ∀ R : Refiner2 q, SideOK R → (orbitalOut R H t).Good β := by
  classical
  set Φ := domSet H with hΦdef
  have hdom : q < 2 * Φ.card := domSet_card_lt hne
  have hΦ9 : 9 ≤ Φ.card := by omega
  have hpres : ∀ h ∈ H, ∀ a ∈ Φ, h a ∈ Φ := fun h hh a ha => apply_mem_domSet hh ha
  set d := transDeg H Φ with hddef
  obtain ⟨htr, -⟩ := transDeg_spec H Φ
  have hd5 : d ≤ 5 := transDeg_le_five h6 hpres (by omega) hng
  have hd1 : 1 ≤ d := by
    refine le_transDeg (by omega) (transOn_one_of_orbit fun a ha b hb => ?_)
    have hb' : b ∈ lorb H a := by rw [← domSet_eq_lorb ha]; exact hb
    exact mem_lorb.1 hb'
  have hntr : ¬ TransOn H Φ (d + 1) := fun h => by
    have := le_transDeg (by omega) h
    omega
  -- `d + 1` distinct points of `Φ`
  let f : Fin (d + 1) → Fin q := fun i => (Φ.equivFin.symm (Fin.castLE (by omega) i)).1
  have hf : Function.Injective f := fun i j e =>
    Fin.castLE_injective _ (Φ.equivFin.symm.injective (Subtype.ext e))
  let t : Fin ℓ → Fin q := fun i => if h : i.val < d + 1 then f ⟨i.val, h⟩ else f 0
  refine ⟨t, fun R hR => ?_⟩
  unfold orbitalOut
  refine orbitalAt_good hR hq (by omega) hd1 hd5 hdom htr hntr (fun i j hi hj e => ?_)
    (fun i hi => ?_)
  · simp only [t, dif_pos (show i.val < d + 1 by omega), dif_pos (show j.val < d + 1 by omega)]
      at e
    exact Fin.ext (Fin.mk.inj_iff.1 (hf e))
  · simp only [t, dif_pos (show i.val < d + 1 by omega)]
    exact (Φ.equivFin.symm _).2

end Good

end GI.Algorithm
