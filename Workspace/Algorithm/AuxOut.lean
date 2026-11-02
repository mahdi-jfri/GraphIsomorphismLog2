import Workspace.Algorithm.OutOrbital
import Workspace.Paper.LocalCertificates
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# The object that ends Cases 2b and 3

`outPair` gives the objects of Section A.3 that end Cases 2b and 3 of the aggregation, read off
the canonical structures `X` of the source string and `Y` of the target string (ideal
certificate group, refined tuple colors, individualized tuple):

* Case 2b (the ideal certificate group has a dominant orbit on which it is not giant): the
  refined orbital configuration of `orbitalOut` (`Workspace/Algorithm/OutOrbital.lean`);
* Case 3 (no orbit has more than `q/2` points and the support has fewer than `q/2` points): the
  object of the Design Lemma, `designOut` (`Workspace/Algorithm/OutDesign.lean`);
* the other cases: no object (`outPair` is used only in Cases 2b and 3).

In Case 2b the binary colorings of `X` and `Y` are refined jointly (`JointFn`), as the paper
refines the two inputs with one palette.

`outPair_smul`: if `Y = σ X`, the object of `Y` is `σ` applied to the object of `X` ("Every
choice above is canonical, so these items commute with relabeling").

`exists_src_good`: for every state, a source tuple of length `ℓ ≥ max 6 (κ + 1)` exists on which
the object of the source string is good in Cases 2b and 3, whatever the target structure. In Case 3 this applies the Design
Lemma to the refined tuple colors, with the dominance threshold `α = 3/4`. Its twin hypothesis
(DEVIATION 8: every set of pairwise twins has fewer than `αq` points) holds: a set of at least
`κ` pairwise twins lies in one orbit of the ideal certificate group (`twin_mem_lorb`), because a
nonfull `κ`-subset would have two orderings with an empty comparison (`GI.Paper.no_large_twin`)
while the twin transpositions keep every refined color, and a full `κ`-subset carries `Alt(T)` in
the certificate group; in Case 3 every orbit has at most `q/2` points (`twins_card_lt`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Cited GI.Endpoint GI.LocalGroups GI.LocalCertificates

/-! ### The object -/

/-- **The objects that end Cases 2b and 3**, read off the canonical structures `X` (of the
source string) and `Y` (of the target string, in one branch). The case is read off `X`. In
Case 2b the binary colorings of `X` and `Y` are refined jointly (`JointFn`, `k = 2`); the
first component is the object of `X`, the second the object of `Y`. -/
noncomputable def outPair (hK : JointFn) {q κ ℓ : ℕ} (X Y : Canon q κ ℓ) : CfgOut q × CfgOut q :=
  match aggCase X.grp with
  | .twoB => (orbitalOut (hK.left q 2 (orbColOut Y.grp Y.tup)) X.grp X.tup,
      orbitalOut (hK.right q 2 (orbColOut X.grp X.tup)) Y.grp Y.tup)
  | .three => (designOut X.col X.tup, designOut Y.col Y.tup)
  | _ => (.none, .none)

theorem outPair_twoB (hK : JointFn) {q κ ℓ : ℕ} {X : Canon q κ ℓ} (Y : Canon q κ ℓ)
    (h : aggCase X.grp = .twoB) : outPair hK X Y =
      (orbitalOut (hK.left q 2 (orbColOut Y.grp Y.tup)) X.grp X.tup,
        orbitalOut (hK.right q 2 (orbColOut X.grp X.tup)) Y.grp Y.tup) := by
  unfold outPair; rw [h]

theorem outPair_three (hK : JointFn) {q κ ℓ : ℕ} {X : Canon q κ ℓ} (Y : Canon q κ ℓ)
    (h : aggCase X.grp = .three) :
    outPair hK X Y = (designOut X.col X.tup, designOut Y.col Y.tup) := by
  unfold outPair; rw [h]

/-- **The objects commute with relabeling**: if `Y = σ X`, the object of `Y` is `σ` applied to
the object of `X`. In Case 2b this is the relabeling clause of the joint refinement
(`joint_carries2`). -/
theorem outPair_smul (hK : JointFn) {q κ ℓ : ℕ} (σ : Perm (Fin q)) (X : Canon q κ ℓ) :
    (outPair hK X (σ • X)).2 = σ • (outPair hK X (σ • X)).1 := by
  cases h : aggCase X.grp with
  | twoB =>
    rw [outPair_twoB hK _ h, Canon.smul_grp, Canon.smul_tup]
    refine orbitalOut_conj σ _ _ X.grp X.tup ?_
    rw [orbColOut_conj]
    exact joint_carries2 σ hK _
  | three =>
    rw [outPair_three hK _ h, Canon.smul_col, Canon.smul_tup]
    exact designOut_smul σ X.col X.tup
  | one =>
    unfold outPair; rw [h]; rfl
  | twoA =>
    unfold outPair; rw [h]; rfl

/-! ### Twins of the refined tuple colors -/

section Twins

/-- **Permutations of pairwise twins keep every color**: a permutation that moves only points of a
set `T` of pairwise twins is a product of twin transpositions. -/
theorem twins_perm {k n : ℕ} {c : (Fin k → Fin n) → ℕ} {T : Finset (Fin n)}
    (hT : ∀ u ∈ T, ∀ v ∈ T, Twins c u v) (p : Perm T) (w : Fin k → Fin n) :
    c (ofSubtype p ∘ w) = c w := by
  induction p using swap_induction_on generalizing w with
  | one => rw [map_one]; rfl
  | swap_mul f x y _ ih =>
    rw [map_mul, ofSubtype_swap_eq, Perm.coe_mul, Function.comp_assoc]
    rw [hT x.1 x.2 y.1 y.2 (ofSubtype f ∘ w), ih]

variable {Ω C : Type} (S : State Ω C) [Fintype S.dom] [DecidableEq S.dom] {q : ℕ}
  (πd : S.domGroup →* alternatingGroup (Fin q)) (κ : ℕ)

/-- An enumeration of a finset of size `κ`. -/
noncomputable def enumT (T : Finset (Fin q)) (h : T.card = κ) : Fin κ → Fin q :=
  fun i => (T.equivFin.symm (Fin.cast h.symm i)).1

theorem enumT_injective (T : Finset (Fin q)) (h : T.card = κ) :
    Function.Injective (enumT κ T h) := fun i j e => by
  have := T.equivFin.symm.injective (Subtype.ext e)
  exact Fin.cast_injective _ this

theorem tset_enumT (T : Finset (Fin q)) (h : T.card = κ) : tset (enumT κ T h) = T := by
  ext c
  rw [mem_tset]
  constructor
  · rintro ⟨i, rfl⟩; exact (T.equivFin.symm _).2
  · intro hc
    refine ⟨Fin.cast h (T.equivFin ⟨c, hc⟩), ?_⟩
    simp [enumT]

/-- **Two tuples with the same refined color are compared** (the refinement refines the
comparison classes, `rcol_refines`). -/
theorem compareRel_of_rcol (hK : JointFn) {nm : ClassNum S κ q} {x y : S.dom → C}
    (hnm : NumOK S πd κ nm x y)
    {t₀ t₁ : Fin κ → Fin q} (h₀ : Function.Injective t₀) (h₁ : Function.Injective t₁)
    (h : rcol S πd κ hK nm x y t₁ = rcol S πd κ hK nm x y t₀) :
    CompareRel S.domGroup πd κ (x, t₀) (x, t₁) := by
  classical
  have ht := rcol_refines S πd κ hK nm x y t₁ t₀ h
  -- the numbering separates the classes of `x` (`hnm`)
  have hcls : tcls S πd κ x t₁ = tcls S πd κ x t₀ :=
    hnm (Finset.mem_coe.2 (tcls_mem_classes S πd κ x t₁))
      (Finset.mem_coe.2 (tcls_mem_classes S πd κ x t₀)) ht
  obtain ⟨hequiv, hiff, -, -⟩ := GI.Paper.noninjective_extension (C := C) S.domGroup πd κ
  have hrel : tupleRel S.domGroup πd κ (x, t₁) (x, t₀) := by
    have : (x, t₁) ∈ tcls S πd κ x t₁ := hequiv.refl _
    rw [hcls] at this
    exact this
  exact (compareRel_equivalence).symm ((hiff _ _ h₁ h₀).1 hrel)

/-- **A set of at least `κ` pairwise twins lies in one orbit of the ideal certificate group**
(Section A.3: "If all orderings of a nonfull `T` had the same color, their transporters would
realize all of `Sym(T)` on the final marked window. Its even part would force `φ_T(A_i) =
Alt(T)`, a contradiction. Thus the no-large-twin argument in Section 6.2 of Helfgott's exposition
survives"). Two twins `a, b` lie in a `κ`-subset `T'` of the twins. All orderings of `T'` have
the same refined color, hence are compared, so `T'` is full (`GI.Paper.no_large_twin`); the full
certificate of `T'` lies in the certificate group and induces `Alt(T')` on `T'`, which moves `a`
to `b`. -/
theorem twin_mem_lorb (hK : JointFn) {nm : ClassNum S κ q} {x y : S.dom → C}
    (hnm : NumOK S πd κ nm x y) (hκ : 5 ≤ κ)
    {T : Finset (Fin q)} (hT : ∀ u ∈ T, ∀ v ∈ T, Twins (rcol S πd κ hK nm x y) u v)
    (hcard : κ ≤ T.card) {a b : Fin q} (ha : a ∈ T) (hb : b ∈ T) :
    b ∈ lorb (idealGrp S πd κ x) a := by
  classical
  by_cases hab : a = b
  · rw [hab]; exact self_mem_lorb b
  -- a `κ`-subset `T'` of the twins containing `a` and `b`
  obtain ⟨T', hsub, hT'T, hT'⟩ := Finset.exists_subsuperset_card_eq
    (show {a, b} ⊆ T by intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption)
    (by rw [Finset.card_pair hab]; omega) hcard
  have haT' : a ∈ T' := hsub (by simp)
  have hbT' : b ∈ T' := hsub (by simp)
  have hT'tw : ∀ u ∈ T', ∀ v ∈ T', Twins (rcol S πd κ hK nm x y) u v :=
    fun u hu v hv => hT u (hT'T hu) v (hT'T hv)
  set t₀ := enumT κ T' hT' with ht₀
  have ht₀i : Function.Injective t₀ := enumT_injective κ T' hT'
  have hset : tset t₀ = T' := tset_enumT κ T' hT'
  -- the test set `T'` is full
  have hfull : IsFull (phiT S.domGroup πd T') x := by
    by_contra hnf
    rw [← hset] at hnf
    obtain ⟨t₁, ht₁i, hset₁, hno⟩ := GI.Paper.no_large_twin S.domGroup πd x t₀ ht₀i hnf
    apply hno
    -- `t₁ = σ ∘ t₀` for a permutation `σ` of `T'`
    have hmem₀ : ∀ i, t₀ i ∈ T' := fun i => hset ▸ mem_tset.2 ⟨i, rfl⟩
    have hmem₁ : ∀ i, t₁ i ∈ T' := fun i => hset ▸ hset₁ ▸ mem_tset.2 ⟨i, rfl⟩
    have hbij : ∀ (t : Fin κ → Fin q) (hi : Function.Injective t) (hm : ∀ i, t i ∈ T'),
        tset t = T' → Function.Bijective (fun i => (⟨t i, hm i⟩ : T')) := by
      intro t hi hm hs
      refine ⟨fun i j e => hi (congrArg Subtype.val e), fun c => ?_⟩
      obtain ⟨i, hi⟩ := mem_tset.1 (hs ▸ c.2 : c.1 ∈ tset t)
      exact ⟨i, Subtype.ext hi⟩
    let e₀ := Equiv.ofBijective _ (hbij t₀ ht₀i hmem₀ hset)
    let e₁ := Equiv.ofBijective _ (hbij t₁ ht₁i hmem₁ (hset₁.trans hset))
    let p : Perm T' := e₀.symm.trans e₁
    have hσ : ofSubtype p ∘ t₀ = t₁ := by
      funext i
      simp only [Function.comp]
      rw [ofSubtype_apply_of_mem p (hmem₀ i)]
      have : e₀.symm ⟨t₀ i, hmem₀ i⟩ = i := by
        rw [Equiv.symm_apply_eq]; rfl
      simp only [p, Equiv.trans_apply, this]
      rfl
    refine compareRel_of_rcol S πd κ hK hnm ht₀i ht₁i ?_
    rw [← hσ]
    exact twins_perm hT'tw p t₀
  -- the full certificate moves `a` to `b`
  obtain ⟨-, himg⟩ := GI.Paper.endpoint_full_certificate S.domGroup πd x T' (by omega) hfull
  haveI : MulAction.IsPretransitive (alternatingGroup T') T' :=
    alternatingGroup.isPretransitive_of_three_le_card T' (by simp; omega)
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup T')
    (⟨a, haT'⟩ : T') (⟨b, hbT'⟩ : T')
  have hσimg : σ ∈ img (phiT S.domGroup πd T') (fullCert (phiT S.domGroup πd T') x) := by
    rw [himg]; trivial
  obtain ⟨g, hgK, hgσ⟩ := (mem_img _).1 hσimg
  have hglab : lab S.domGroup πd g a = b := by
    have := phiT_apply g ⟨a, haT'⟩
    rw [hgσ] at this
    rw [← this]
    exact congrArg Subtype.val hσ
  have hgcert : (g : Perm S.dom) ∈ certGroup S πd κ x := by
    unfold certGroup
    exact (le_iSup₂ (f := fun (T : Finset (Fin q))
      (_ : T.card = κ ∧ IsFull (phiT S.domGroup πd T) x) => fullCert (phiT S.domGroup πd T) x)
      T' ⟨hT', hfull⟩) hgK
  have hgdom : (g : Perm S.dom) ∈ S.domGroup := certGroup_le S πd κ x hgcert
  refine mem_lorb.2 ⟨(πd ⟨g, hgdom⟩ : Perm (Fin q)), ?_, ?_⟩
  · exact ⟨_, ⟨⟨g, hgdom⟩, Subgroup.mem_subgroupOf.2 hgcert, rfl⟩, rfl⟩
  · rw [← lab_of_mem hgdom]; exact hglab

/-- **The twin hypothesis of the Design Lemma** (DEVIATION 8) when no orbit of the ideal
certificate group has more than `q/2` points: every set of pairwise twins of the refined tuple
colors has fewer than `3q/4` points. A set of at least `κ` twins lies in one orbit
(`twin_mem_lorb`), of at most `q/2` points; a smaller set has fewer than `κ ≤ q/2` points. -/
theorem twins_card_lt (hK : JointFn) {nm : ClassNum S κ q} {x y : S.dom → C}
    (hnm : NumOK S πd κ nm x y) (hκ : 5 ≤ κ)
    (hqκ : 2 * κ ≤ q) (hdom : domSet (idealGrp S πd κ x) = ∅) (T : Finset (Fin q))
    (hT : ∀ u ∈ T, ∀ v ∈ T, Twins (rcol S πd κ hK nm x y) u v) :
    (T.card : ℝ) < 3 / 4 * q := by
  have h2 : 2 * T.card ≤ q := by
    by_cases hc : κ ≤ T.card
    · obtain ⟨a, ha⟩ : T.Nonempty := Finset.card_pos.1 (by omega)
      have hsub : T ⊆ lorb (idealGrp S πd κ x) a := fun b hb =>
        twin_mem_lorb S πd κ hK hnm hκ hT hc ha hb
      have hle := Finset.card_le_card hsub
      have hsmall : ¬ q < 2 * (lorb (idealGrp S πd κ x) a).card := by
        intro h
        have : a ∈ domSet (idealGrp S πd κ x) := mem_domSet.2 h
        rw [hdom] at this
        exact Finset.notMem_empty a this
      omega
    · omega
  have hq : (10 : ℝ) ≤ q := by exact_mod_cast (show 10 ≤ q by omega)
  have : (2 * T.card : ℝ) ≤ q := by exact_mod_cast h2
  linarith

end Twins

/-! ### A good source tuple -/

/-- **A good source tuple exists** (Section A.3, Cases 2b and 3; Section 4.1: "We fix a bounded
source tuple, branch over its target images"). For every state, label map and string, if `κ ≥ 5`,
`q ≥ 16`, `q ≥ 2κ`, `β ≥ 3/4` and `ℓ ≥ max 6 (κ + 1)`, some source tuple `src` of length `ℓ`
makes the object of the source string good in Cases 2b and 3. Case 2b uses the CFSG bound
`GI.Cited.SixTransitiveContainsAlt` (`exists_orbitalOut_good`); Case 3 applies the Design Lemma
`GI.Cited.DesignLemma` with `α = 3/4` to the refined tuple colors (`exists_designOut_good`),
whose twin hypothesis is `twins_card_lt`. -/
theorem exists_src_good (hK : JointFn) (h6 : SixTransitiveContainsAlt)
    (hD : DesignLemma) {Ω C : Type} (fin : Finite Ω) (S : State Ω C) (L : GiantLabels S)
    (πd : S.domGroup →* alternatingGroup (Fin L.q)) {κ : ℕ} (nm : ClassNum S κ L.q)
    (hnm : ClassNum.OK fin S L πd κ nm) {β : ℝ} (hκ : 5 ≤ κ)
    (hq : 16 ≤ L.q) (hqκ : 2 * κ ≤ L.q) (hβ : 3 / 4 ≤ β) {ℓ : ℕ} (hℓ : κ < ℓ) (hℓ6 : 6 ≤ ℓ) :
    ∃ src : Fin ℓ → Fin L.q, (aggCase (structX fin S L πd hK κ nm src).grp = .twoB ∨
      aggCase (structX fin S L πd hK κ nm src).grp = .three) →
      ∀ Y : Canon L.q κ ℓ, (outPair hK (structX fin S L πd hK κ nm src) Y).1.Good β := by
  classical
  haveI := fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  have hgrp : ∀ src : Fin ℓ → Fin L.q, (structX fin S L πd hK κ nm src).grp =
      idealGrp S πd κ (dstr S S.x) := fun _ => rfl
  have hcol : ∀ src : Fin ℓ → Fin L.q, (structX fin S L πd hK κ nm src).col =
      rcol S πd κ hK nm (dstr S S.x) (dstr S S.y) := fun _ => rfl
  have htup : ∀ src : Fin ℓ → Fin L.q, (structX fin S L πd hK κ nm src).tup = src :=
    fun _ => rfl
  set H := idealGrp S πd κ (dstr S S.x) with hHdef
  set c := rcol S πd κ hK nm (dstr S S.x) (dstr S S.y) with hcdef
  simp only [hgrp]
  cases hcase : aggCase H with
  | one => exact ⟨fun _ => ⟨0, by omega⟩, fun h => by rcases h with h | h <;> cases h⟩
  | twoA => exact ⟨fun _ => ⟨0, by omega⟩, fun h => by rcases h with h | h <;> cases h⟩
  | twoB =>
    -- Case 2b: anchors and an orbital
    have hne : (domSet H).Nonempty := by
      unfold aggCase at hcase
      by_contra h
      rw [if_neg h] at hcase
      split_ifs at hcase
    have hng : ¬ GiantOn H (domSet H) := by
      unfold aggCase at hcase
      rw [if_pos hne] at hcase
      split_ifs at hcase with h
      exact h
    obtain ⟨t, ht⟩ := exists_orbitalOut_good h6 (β := β) hq hℓ6 hne hng
    refine ⟨t, fun _ Y => ?_⟩
    rw [outPair_twoB hK Y (by rw [hgrp]; exact hcase), hgrp, htup]
    exact ht _ (hK.left_ok _ _ _)
  | three =>
    -- Case 3: the Design Lemma on the refined tuple colors
    have hdom : domSet H = ∅ := by
      unfold aggCase at hcase
      by_contra hne
      rw [if_pos (Finset.nonempty_iff_ne_empty.2 hne)] at hcase
      split_ifs at hcase
    obtain ⟨hconf, hcoh⟩ := rcol_coherent S πd κ hK nm (dstr S S.x) (dstr S S.y)
    -- the class numbering separates the classes (`hnm`), as the twin bound needs
    have htw := twins_card_lt S πd κ hK (y := dstr S S.y) hnm hκ hqκ hdom
    have hdes := hD L.q κ (by omega) hqκ (3 / 4) (by norm_num) (by norm_num) c hconf hcoh
      fun T hT => htw T hT
    have hqr : (0 : ℝ) ≤ L.q := Nat.cast_nonneg _
    obtain ⟨m, hm, x, hx⟩ : ∃ m, m < κ ∧ ∃ x : Fin m → Fin L.q, Balanced c x ∨ DomSplit c x := by
      rcases hdes with ⟨m, hm, x, hx⟩ | ⟨m, hm, x, j, hj, u, v, w, y, hu, hv, hw, hy, huv, hwy, hne⟩
      · refine ⟨m, hm, x, Or.inl fun j => ?_⟩
        have h1 := hx j
        have h2 : (4 * vcard c x j : ℝ) < 3 * L.q := by unfold vcard; linarith
        exact_mod_cast h2
      · refine ⟨m, by omega, x, Or.inr ⟨hm, j, ?_, u, v, w, y, hu, hv, hw, hy, huv, hwy, hne⟩⟩
        have h2 : (3 * L.q : ℝ) ≤ 4 * vcard c x j := by unfold vcard; linarith
        unfold Dominant
        exact_mod_cast h2
    obtain ⟨t, ht⟩ := exists_designOut_good hconf hcoh hℓ hβ (by omega) hm x hx
    refine ⟨t, fun _ Y => ?_⟩
    rw [outPair_three hK Y (by rw [hgrp]; exact hcase), hcol, htup]
    exact ht

end GI.Algorithm
