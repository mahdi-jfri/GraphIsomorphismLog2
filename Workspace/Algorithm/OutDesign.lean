module

public import Workspace.Algorithm.OutSkeleton

@[expose] public section

/-!
# Case 3 of the aggregation: the object from the Design Lemma

Section A.3, Case 3 ("there is no large orbit") applies Babai's Design Lemma
(`GI.Cited.DesignLemma`, [H, Proposition 5.1]) to the refined tuple colors `c` (a `k`-ary
coherent configuration on the labels). For some individualized tuple `x` of `m < k` labels,
either

* (a) every color class of the vertex coloring `z ↦ c(x, z, …, z)` has fewer than `αq` points
  ("The analogous balanced-coloring outcome of Design has all its color classes bounded by a
  fixed fraction of `q`"), or
* (b) `m + 1 < k`, some class `C` has at least `αq` points, and the pair coloring
  `(z₁, z₂) ↦ c(x, z₁, z₂, …, z₂)` is not constant on the distinct pairs of `C` ("the vertex
  class `C` … as a nontrivial coherent configuration").

We fix `α = 3/4`, the dominant-class threshold `η` of Section 5.1 (Section A.3, "Balance
parameters": "Use the dominant-class threshold `η > 2/3`"; the Design Lemma needs `α > 1/2`).

The tuple `x` is not canonical: it is part of the individualized source tuple `t` of the branch
(Section 4.1: "We fix a bounded source tuple, branch over its target images"). The object is
read off `t` canonically (`designOut`): look at the prefixes of `t` of lengths `m = 0, 1, …, k-1`
in this order and take the first one with outcome (a) or (b). Outcome (a) gives the colored
partition into vertex classes. Outcome (b) gives the pair skeleton on the dominant class (there
is one, since two classes of more than `q/2` points would meet), with the source vertex of the
first rectangle at position `k` of `t`. Every step is defined by the data and commutes with
relabeling (`designOut_smul`).

`designOut_good`: if a prefix of `t` has outcome (a) or (b), and (in outcome (b)) position `k`
of `t` lies in the dominant class, the object is good. `exists_designOut_good`: a tuple with
these properties exists whenever some tuple `x` of length `m < k` has outcome (a) or (b).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Cited

variable {q k ℓ : ℕ}

/-! ### The outcomes -/

section Outcomes

/-- The size of the color class `j` of the vertex coloring `z ↦ c(x, z, …, z)`. -/
noncomputable def vcard (c : (Fin k → Fin q) → ℕ) {m : ℕ} (x : Fin m → Fin q) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun z => skel₁ c x z = j).card

/-- **Outcome (a)**: every vertex class has fewer than `3q/4` points. -/
def Balanced (c : (Fin k → Fin q) → ℕ) {m : ℕ} (x : Fin m → Fin q) : Prop :=
  ∀ j, 4 * vcard c x j < 3 * q

/-- A vertex class with at least `3q/4` points (a dominant color). -/
def Dominant (c : (Fin k → Fin q) → ℕ) {m : ℕ} (x : Fin m → Fin q) (j : ℕ) : Prop :=
  3 * q ≤ 4 * vcard c x j

/-- **Outcome (b)**: `m + 1 < k`, and some dominant class carries two pairs of distinct points of
different pair colors. -/
def DomSplit (c : (Fin k → Fin q) → ℕ) {m : ℕ} (x : Fin m → Fin q) : Prop :=
  m + 1 < k ∧ ∃ j, Dominant c x j ∧ ∃ u v w y : Fin q, skel₁ c x u = j ∧ skel₁ c x v = j ∧
    skel₁ c x w = j ∧ skel₁ c x y = j ∧ u ≠ v ∧ w ≠ y ∧ skel₂ c x u v ≠ skel₂ c x w y

/-- There is at most one dominant color. -/
theorem dominant_unique {c : (Fin k → Fin q) → ℕ} {m : ℕ} {x : Fin m → Fin q} (hq : 0 < q)
    {j j' : ℕ} (hj : Dominant c x j) (hj' : Dominant c x j') : j = j' := by
  classical
  by_contra hne
  have hdis : Disjoint (Finset.univ.filter fun z => skel₁ c x z = j)
      (Finset.univ.filter fun z => skel₁ c x z = j') := by
    rw [Finset.disjoint_filter]
    intro z _ h1 h2
    exact hne (h1.symm.trans h2)
  have h := Finset.card_union_of_disjoint hdis
  have hle := Finset.card_le_univ ((Finset.univ.filter fun z => skel₁ c x z = j) ∪
    (Finset.univ.filter fun z => skel₁ c x z = j'))
  rw [Fintype.card_fin] at hle
  unfold Dominant vcard at hj hj'
  omega

/-! #### Relabeling -/

variable (σ : Perm (Fin q)) (c : (Fin k → Fin q) → ℕ)

/-- The relabeled coloring `σ • c`. -/
def relCol : (Fin k → Fin q) → ℕ := fun w => c (σ.symm ∘ w)

variable {m : ℕ} (x : Fin m → Fin q)

theorem skel₁_rel (z : Fin q) : skel₁ (relCol σ c) (σ ∘ x) z = skel₁ c x (σ⁻¹ z) := by
  unfold skel₁ relCol
  congr 1
  funext i
  simp only [Function.comp, padTuple]
  split_ifs <;> simp

theorem skel₂_rel (z₁ z₂ : Fin q) :
    skel₂ (relCol σ c) (σ ∘ x) z₁ z₂ = skel₂ c x (σ⁻¹ z₁) (σ⁻¹ z₂) := by
  unfold skel₂ relCol
  congr 1
  funext i
  simp only [Function.comp, padTuple₂]
  split_ifs <;> simp

theorem vcard_rel (j : ℕ) : vcard (relCol σ c) (σ ∘ x) j = vcard c x j := by
  unfold vcard
  refine (Finset.card_equiv σ⁻¹ fun z => ?_)
  simp [skel₁_rel]

theorem balanced_rel : Balanced (relCol σ c) (σ ∘ x) ↔ Balanced c x := by
  unfold Balanced
  simp only [vcard_rel]

theorem dominant_rel (j : ℕ) : Dominant (relCol σ c) (σ ∘ x) j ↔ Dominant c x j := by
  unfold Dominant
  rw [vcard_rel]

theorem domSplit_rel : DomSplit (relCol σ c) (σ ∘ x) ↔ DomSplit c x := by
  unfold DomSplit
  refine and_congr Iff.rfl ⟨fun ⟨j, hj, u, v, w, y, h⟩ => ?_, fun ⟨j, hj, u, v, w, y, h⟩ => ?_⟩
  · refine ⟨j, (dominant_rel σ c x j).1 hj, σ⁻¹ u, σ⁻¹ v, σ⁻¹ w, σ⁻¹ y, ?_⟩
    simp only [skel₁_rel, skel₂_rel] at h
    refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_, h.2.2.2.2.2.2⟩
    · exact fun e => h.2.2.2.2.1 (σ⁻¹.injective e)
    · exact fun e => h.2.2.2.2.2.1 (σ⁻¹.injective e)
  · refine ⟨j, (dominant_rel σ c x j).2 hj, σ u, σ v, σ w, σ y, ?_⟩
    simp only [skel₁_rel, skel₂_rel, Perm.inv_apply_self]
    refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_, h.2.2.2.2.2.2⟩
    · exact fun e => h.2.2.2.2.1 (σ.injective e)
    · exact fun e => h.2.2.2.2.2.1 (σ.injective e)

end Outcomes

/-! ### The object of Case 3 -/

section Out

/-- The prefix of length `m` of `t` (entries past the end of `t` are its first entry). -/
def preT (t : Fin ℓ → Fin q) (h0 : 0 < ℓ) (m : ℕ) : Fin m → Fin q :=
  fun i => if h : i.val < ℓ then t ⟨i.val, h⟩ else t ⟨0, h0⟩

theorem preT_rel (σ : Perm (Fin q)) (t : Fin ℓ → Fin q) (h0 : 0 < ℓ) (m : ℕ) :
    preT (σ ∘ t) h0 m = σ ∘ preT t h0 m := by
  funext i
  simp only [preT, Function.comp]
  split_ifs <;> rfl

/-- **The first prefix with an outcome of the Design Lemma**: a prefix of length `m < k` with
outcome (a) or (b). -/
def Hit (c : (Fin k → Fin q) → ℕ) (t : Fin ℓ → Fin q) (h0 : 0 < ℓ) (m : ℕ) : Prop :=
  m < k ∧ (Balanced c (preT t h0 m) ∨ DomSplit c (preT t h0 m))

/-- **Case 3 keeps the individualized labels as singleton colors** (Section A.3, "Balance
parameters": "Keep individualized labels as singleton colors"). Let `c` be a configuration and
`x` a tuple of length `m < k`. The vertex class of an entry `x_i` is `{x_i}`. The reason is that
tuples of the same color have the same equality pattern, and the tuple `(x, x_i, …, x_i)` has
equal entries at positions `i` and `m`. So the colored partition and the pair skeleton of
`designAt` both have the entries of the prefix as singleton vertex classes. -/
theorem skel₁_prefix_singleton {c : (Fin k → Fin q) → ℕ} (hc : IsConfiguration c) {m : ℕ}
    (x : Fin m → Fin q) (hm : m < k) (i : Fin m) {z : Fin q}
    (h : skel₁ c x z = skel₁ c x (x i)) : z = x i := by
  have e := hc.1 _ _ h ⟨i.val, by omega⟩ ⟨m, hm⟩
  simp only [padTuple, i.isLt, dif_pos, lt_irrefl, dif_neg, not_false_eq_true] at e
  exact (e.2 trivial).symm

theorem hit_rel (σ : Perm (Fin q)) (c : (Fin k → Fin q) → ℕ) (t : Fin ℓ → Fin q) (h0 : 0 < ℓ)
    (m : ℕ) : Hit (relCol σ c) (σ ∘ t) h0 m ↔ Hit c t h0 m := by
  unfold Hit
  rw [preT_rel, balanced_rel, domSplit_rel]

open Classical in
/-- The object read off the prefix of length `m` of `t`: for outcome (a) the colored partition
into vertex classes, otherwise the pair skeleton on the dominant class (the least dominant color;
there is at most one, `dominant_unique`) with source vertex `t_k`. -/
noncomputable def designAt (c : (Fin k → Fin q) → ℕ) (t : Fin ℓ → Fin q) (hkl : k < ℓ) (m : ℕ) :
    CfgOut q :=
  if Balanced c (preT t (by omega) m) then
    .part (classPart (skel₁ c (preT t (by omega) m)))
  else if hd : ∃ j, Dominant c (preT t (by omega) m) j then
    .pair (skelCfg c (preT t (by omega) m) (Nat.find hd)) (t ⟨k, hkl⟩)
  else .none

open Classical in
/-- **The object of Case 3** ("Apply the Design Lemma"), read off the refined tuple colors `c`
and the individualized tuple `t` (of length `ℓ > k`): the first prefix of `t` with outcome (a)
or (b) of the Design Lemma (`designAt`). -/
noncomputable def designOut (c : (Fin k → Fin q) → ℕ) (t : Fin ℓ → Fin q) : CfgOut q :=
  if hkl : k < ℓ then
    if hex : ∃ m, Hit c t (by omega) m then designAt c t hkl (Nat.find hex) else .none
  else .none

theorem skelCfg_rel (σ : Perm (Fin q)) (c : (Fin k → Fin q) → ℕ) {m : ℕ} (x : Fin m → Fin q)
    (j : ℕ) : skelCfg (relCol σ c) (σ ∘ x) j = σ • skelCfg c x j := by
  ext a b
  · simp only [skelCfg, PairCfg.smul_col, skel₂_rel]
  · rfl

theorem designAt_smul (σ : Perm (Fin q)) (c : (Fin k → Fin q) → ℕ) (t : Fin ℓ → Fin q)
    (hkl : k < ℓ) (m : ℕ) : designAt (relCol σ c) (σ ∘ t) hkl m = σ • designAt c t hkl m := by
  classical
  unfold designAt
  have h0 : 0 < ℓ := by omega
  rw [preT_rel]
  by_cases hb : Balanced c (preT t h0 m)
  · rw [if_pos ((balanced_rel σ c _).2 hb), if_pos hb, CfgOut.smul_part, classPart_smul]
    congr 2
    funext a
    rw [skel₁_rel]
  rw [if_neg (fun h => hb ((balanced_rel σ c _).1 h)), if_neg hb]
  by_cases hd : ∃ j, Dominant c (preT t h0 m) j
  swap
  · have hd' : ¬ ∃ j, Dominant (relCol σ c) (σ ∘ preT t h0 m) j := by
      simpa only [dominant_rel] using hd
    rw [dif_neg hd, dif_neg hd', CfgOut.smul_none]
  have hd' : ∃ j, Dominant (relCol σ c) (σ ∘ preT t h0 m) j := by
    simpa only [dominant_rel] using hd
  rw [dif_pos hd, dif_pos hd', CfgOut.smul_pair, skelCfg_rel]
  have hj : Nat.find hd' = Nat.find hd := Nat.find_congr' (dominant_rel σ c _ _)
  rw [hj]
  rfl

/-- **The object of Case 3 commutes with relabeling.** -/
theorem designOut_smul (σ : Perm (Fin q)) (c : (Fin k → Fin q) → ℕ) (t : Fin ℓ → Fin q) :
    designOut (relCol σ c) (σ ∘ t) = σ • designOut c t := by
  classical
  unfold designOut
  by_cases hkl : k < ℓ
  swap
  · simp only [dif_neg hkl, CfgOut.smul_none]
  simp only [dif_pos hkl]
  have h0 : 0 < ℓ := by omega
  by_cases hex : ∃ m, Hit c t h0 m
  swap
  · have hex' : ¬ ∃ m, Hit (relCol σ c) (σ ∘ t) h0 m := by
      simpa only [hit_rel] using hex
    rw [dif_neg hex, dif_neg hex', CfgOut.smul_none]
  have hex' : ∃ m, Hit (relCol σ c) (σ ∘ t) h0 m := by simpa only [hit_rel] using hex
  rw [dif_pos hex, dif_pos hex']
  have hm : Nat.find hex' = Nat.find hex := Nat.find_congr' (hit_rel σ c t h0 _)
  rw [hm, designAt_smul]

open Classical in
/-- **The object read off a prefix with an outcome is good** (Section A.3, "Balance
parameters" and Case 3). Let `c` be a coherent configuration, `k < ℓ`, `β ≥ 3/4`, `q ≥ 2`, and
let the prefix of length `m` of `t` have outcome (a) or (b) (`hhit`). If in outcome (b) the
entry `t_k` lies in the dominant class (`hx₀`), the object is good: for (a) every vertex class
has fewer than `3q/4 ≤ βq` points (`classPart_cap`); for (b) the pair skeleton is coherent on
the dominant class (`skelCfg_coherent`), nontrivial, and the class has at least `3q/4 ≥ q/4`
points. -/
theorem designAt_good {c : (Fin k → Fin q) → ℕ} (hc : IsConfiguration c) (hco : IsCoherent c)
    {t : Fin ℓ → Fin q} (hkl : k < ℓ) {β : ℝ} (hβ : 3 / 4 ≤ β) (hq : 2 ≤ q) {m : ℕ}
    (hhit : Hit c t (by omega) m)
    (hx₀ : ¬ Balanced c (preT t (by omega) m) →
      ∀ j, Dominant c (preT t (by omega) m) j → skel₁ c (preT t (by omega) m) (t ⟨k, hkl⟩) = j) :
    (designAt c t hkl m).Good β := by
  classical
  have h0 : 0 < ℓ := by omega
  unfold designAt
  unfold Hit at hhit
  generalize preT t h0 m = x at hhit hx₀ ⊢
  by_cases hb : Balanced c x
  · rw [if_pos hb]
    -- outcome (a): the classes have fewer than `3q/4 ≤ βq` points
    have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
    refine classPart_cap _ (Nat.le_floor ?_) fun a => Nat.le_floor ?_
    · push_cast; nlinarith
    · have h1 := hb (skel₁ c x a)
      have h2 : (4 * (classOf (skel₁ c x) a).card : ℝ) < 3 * q := by
        have : classOf (skel₁ c x) a = Finset.univ.filter fun z => skel₁ c x z = skel₁ c x a :=
          rfl
        rw [this]
        exact_mod_cast h1
      nlinarith
  rw [if_neg hb]
  -- outcome (b)
  have hsplit : DomSplit c x := hhit.2.resolve_left hb
  obtain ⟨hmk, j₀, hj₀, u, v, w, y, hu, hv, hw, hy, huv, hwy, hne⟩ := hsplit
  have hd : ∃ j, Dominant c x j := ⟨j₀, hj₀⟩
  rw [dif_pos hd]
  have hj : Nat.find hd = j₀ := dominant_unique (by omega) (Nat.find_spec hd) hj₀
  refine ⟨?_, ?_⟩
  · rw [hj]
    refine skelCfg_good hc hco hmk x j₀ ?_ ⟨u, mem_skelCfg_fiber.2 hu, v, mem_skelCfg_fiber.2 hv,
      w, mem_skelCfg_fiber.2 hw, y, mem_skelCfg_fiber.2 hy, huv, hwy, hne⟩
    have hfib : (skelCfg c x j₀).fiber = Finset.univ.filter fun z => skel₁ c x z = j₀ := by
      ext z; rw [mem_skelCfg_fiber]; simp
    rw [hfib]
    have h1 : (3 * q : ℝ) ≤ 4 * vcard c x j₀ := by exact_mod_cast hj₀
    unfold vcard at h1
    unfold deltaB
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    nlinarith
  · rw [mem_skelCfg_fiber]
    exact hx₀ hb _ (Nat.find_spec hd)

open Classical in
/-- **The object of Case 3 is good** when some prefix of `t` of length `< k` has outcome (a) or
(b) (`hex`) and, in outcome (b) at the first such prefix, `t_k` lies in its dominant class
(`hx₀`). -/
theorem designOut_good {c : (Fin k → Fin q) → ℕ} (hc : IsConfiguration c) (hco : IsCoherent c)
    {t : Fin ℓ → Fin q} (hkl : k < ℓ) {β : ℝ} (hβ : 3 / 4 ≤ β) (hq : 2 ≤ q)
    (hex : ∃ m, Hit c t (by omega) m)
    (hx₀ : ¬ Balanced c (preT t (by omega) (Nat.find hex)) →
      ∀ j, Dominant c (preT t (by omega) (Nat.find hex)) j →
        skel₁ c (preT t (by omega) (Nat.find hex)) (t ⟨k, hkl⟩) = j) :
    (designOut c t).Good β := by
  classical
  unfold designOut
  rw [dif_pos hkl, dif_pos hex]
  exact designAt_good hc hco hkl hβ hq (Nat.find_spec hex) hx₀

/-- **A good source tuple exists for Case 3**: if some tuple `x` of length `m < k` has outcome
(a) or (b) of the Design Lemma, then some `t` of length `ℓ > k` makes the object good. Put `x`
first; if the first prefix with an outcome has outcome (b), put a point of its dominant class at
position `k` (this does not change any prefix of length `< k`). -/
theorem exists_designOut_good {c : (Fin k → Fin q) → ℕ} (hc : IsConfiguration c)
    (hco : IsCoherent c) (hkl : k < ℓ) {β : ℝ} (hβ : 3 / 4 ≤ β) (hq : 2 ≤ q) {m : ℕ}
    (hm : m < k) (x : Fin m → Fin q) (hx : Balanced c x ∨ DomSplit c x) :
    ∃ t : Fin ℓ → Fin q, (designOut c t).Good β := by
  classical
  have h0 : 0 < ℓ := by omega
  let d₀ : Fin q := ⟨0, by omega⟩
  let t₁ : Fin ℓ → Fin q := fun i => if h : i.val < m then x ⟨i.val, h⟩ else d₀
  have hpre : preT t₁ h0 m = x := by
    funext i
    simp only [preT, t₁]
    rw [dif_pos (by omega : i.val < ℓ), dif_pos i.2]
  have hex₁ : ∃ m', Hit c t₁ h0 m' := ⟨m, hm, by rw [hpre]; exact hx⟩
  by_cases hb : Balanced c (preT t₁ h0 (Nat.find hex₁))
  · exact ⟨t₁, designOut_good hc hco hkl hβ hq hex₁ fun h => absurd hb h⟩
  -- outcome (b): put a point of the dominant class at position `k`
  have hsplit : DomSplit c (preT t₁ h0 (Nat.find hex₁)) := (Nat.find_spec hex₁).2.resolve_left hb
  obtain ⟨-, j₀, hj₀, u, -, -, -, hu, -⟩ := hsplit
  let t : Fin ℓ → Fin q := Function.update t₁ ⟨k, hkl⟩ u
  have hpre' : ∀ m', m' < k → preT t h0 m' = preT t₁ h0 m' := by
    intro m' hm'
    funext i
    simp only [preT, t]
    rw [dif_pos (by omega : i.val < ℓ), dif_pos (by omega : i.val < ℓ)]
    rw [Function.update_of_ne]
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  have hhit : ∀ m', Hit c t h0 m' ↔ Hit c t₁ h0 m' := by
    intro m'
    unfold Hit
    constructor
    · rintro ⟨hm', h⟩; exact ⟨hm', by rwa [← hpre' m' hm']⟩
    · rintro ⟨hm', h⟩; exact ⟨hm', by rwa [hpre' m' hm']⟩
  have hex : ∃ m', Hit c t h0 m' := by simpa only [hhit] using hex₁
  have hfind : Nat.find hex = Nat.find hex₁ := Nat.find_congr' (hhit _)
  refine ⟨t, ?_⟩
  unfold designOut
  rw [dif_pos hkl, dif_pos hex, hfind]
  refine designAt_good hc hco hkl hβ hq ((hhit _).2 (Nat.find_spec hex₁)) fun hb' j hj => ?_
  rw [hpre' _ (Nat.find_spec hex₁).1] at hb' hj ⊢
  have ht : t ⟨k, hkl⟩ = u := Function.update_self _ _ _
  rw [ht, hu]
  exact dominant_unique (by omega) hj₀ hj

end Out

end GI.Algorithm
