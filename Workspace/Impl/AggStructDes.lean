import Workspace.Impl.AggStructCol

/-!
# The source tuple of Case 3, as a search

In Case 3 the object of the source string is `designOut c src` (`c` the refined tuple colors of
`x`). It does not depend on the target structure or on the binary refinement values, so the
program may fix `src` right after the refinement call: the first tuple in the order of `stTs`
that passes a test. Goodness itself (a cap of a stabilizer, or a good pair configuration) is not
a test a program runs. The program tests instead the two facts from which `designOut_good`
proves goodness:

* some prefix of `src` of length `m < κ` has outcome (a) or (b) of the Design Lemma (`Hit`),
* if the first such prefix has no outcome (a), the entry `src κ` lies in its dominant class.

Both are counts of vertex classes and comparisons of pair colors, read off `c` at polynomially
many tuples. This is `StDes` below.

* `stDes_good`: `StDes c src` makes the object good (`designOut_good`).
* `st_exists_des`: a tuple with `StDes` exists when some prefix has an outcome (the proof of
  `exists_designOut_good`, which builds such a tuple).
* `st_exists_des_three`: in Case 3 such a prefix exists, by the Design Lemma (the same steps as
  `exists_src_good`).
* `stSrc3`, `stSrc3_des`: the first tuple of `stTs` with `StDes` has `StDes`.
* `stSrcGood_three'`: the source tuple `stSrc3` meets `src_good` in Case 3.
-/

namespace GI.Impl

open GI.Algorithm GI.Cited Equiv Equiv.Perm

variable {q k ℓ : ℕ}

/-! ### The test -/

open Classical in
/-- **The Case 3 test** of a source tuple `t` (of length `ℓ > k`) against the colors `c`. -/
def StDes (c : (Fin k → Fin q) → ℕ) (t : Fin ℓ → Fin q) (hkl : k < ℓ) : Prop :=
  ∃ hex : ∃ m, Hit c t (by omega) m,
    ¬ Balanced c (preT t (by omega) (Nat.find hex)) →
      ∀ j, Dominant c (preT t (by omega) (Nat.find hex)) j →
        skel₁ c (preT t (by omega) (Nat.find hex)) (t ⟨k, hkl⟩) = j

/-- **The test gives a good object.** -/
theorem stDes_good {c : (Fin k → Fin q) → ℕ} (hc : IsConfiguration c) (hco : IsCoherent c)
    {t : Fin ℓ → Fin q} (hkl : k < ℓ) {β : ℝ} (hβ : 3 / 4 ≤ β) (hq : 2 ≤ q)
    (h : StDes c t hkl) : (designOut c t).Good β := by
  obtain ⟨hex, hx₀⟩ := h
  exact designOut_good hc hco hkl hβ hq hex hx₀

/-- **A tuple that passes the test exists** if some tuple `x` of length `m < k` has outcome (a)
or (b). The tuple is the one of `exists_designOut_good`. -/
theorem st_exists_des {c : (Fin k → Fin q) → ℕ} (hkl : k < ℓ) (hq : 2 ≤ q) {m : ℕ}
    (hm : m < k) (x : Fin m → Fin q) (hx : Balanced c x ∨ DomSplit c x) :
    ∃ t : Fin ℓ → Fin q, StDes c t hkl := by
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
  · exact ⟨t₁, hex₁, fun h => absurd hb h⟩
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
  refine ⟨t, hex, fun hb' j hj => ?_⟩
  rw [hfind] at hb' hj ⊢
  rw [hpre' _ (Nat.find_spec hex₁).1] at hb' hj ⊢
  have ht : t ⟨k, hkl⟩ = u := Function.update_self _ _ _
  rw [ht, hu]
  exact dominant_unique (by omega) hj₀ hj

/-! ### Existence in Case 3 -/

/-- **In Case 3 a tuple that passes the test exists**: the Design Lemma (`α = 3/4`) on the refined
colors gives a prefix with an outcome (the steps of `exists_src_good`). -/
theorem st_exists_des_three (hD : DesignLemma) {Ω C : Type} (S : State Ω C) [Fintype S.dom]
    [DecidableEq S.dom] (πd : S.domGroup →* alternatingGroup (Fin q)) {κ : ℕ} (hK : JointFn)
    (nm : ClassNum S κ q) {x y : S.dom → C} (hnm : NumOK S πd κ nm x y) (hκ : 5 ≤ κ)
    (hq : 16 ≤ q) (hqκ : 2 * κ ≤ q) (hdom : domSet (idealGrp S πd κ x) = ∅) (hkl : κ < ℓ) :
    ∃ t : Fin ℓ → Fin q, StDes (rcol S πd κ hK nm x y) t hkl := by
  classical
  set c := rcol S πd κ hK nm x y with hcdef
  obtain ⟨hconf, hcoh⟩ := rcol_coherent S πd κ hK nm x y
  have htw := twins_card_lt S πd κ hK hnm hκ hqκ hdom
  have hdes := hD q κ (by omega) hqκ (3 / 4) (by norm_num) (by norm_num) c hconf hcoh
    fun T hT => htw T hT
  have hqr : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  obtain ⟨m, hm, x, hx⟩ : ∃ m, m < κ ∧ ∃ x : Fin m → Fin q, Balanced c x ∨ DomSplit c x := by
    rcases hdes with ⟨m, hm, x, hx⟩ | ⟨m, hm, x, j, hj, u, v, w, y, hu, hv, hw, hy, huv, hwy, hne⟩
    · refine ⟨m, hm, x, Or.inl fun j => ?_⟩
      have h1 := hx j
      have h2 : (4 * vcard c x j : ℝ) < 3 * q := by unfold vcard; linarith
      exact_mod_cast h2
    · refine ⟨m, by omega, x, Or.inr ⟨hm, j, ?_, u, v, w, y, hu, hv, hw, hy, huv, hwy, hne⟩⟩
      have h2 : (3 * q : ℝ) ≤ 4 * vcard c x j := by unfold vcard; linarith
      unfold Dominant
      exact_mod_cast h2
  exact st_exists_des hkl (by omega) hm x hx

/-! ### The search -/

open Classical in
/-- **The source tuple of Case 3**: the first tuple of `stTs` that passes the test (the first
tuple if none does). -/
noncomputable def stSrc3 (c : (Fin k → Fin q) → ℕ) (hkl : k < ℓ) (hq : 0 < q) : Fin ℓ → Fin q :=
  (stTs q ℓ).getD ((stTs q ℓ).findIdx fun t => decide (StDes c t hkl)) (fun _ => ⟨0, hq⟩)

theorem stSrc3_des {c : (Fin k → Fin q) → ℕ} (hkl : k < ℓ) (hq : 0 < q)
    (hex : ∃ t : Fin ℓ → Fin q, StDes c t hkl) : StDes c (stSrc3 c hkl hq) hkl := by
  classical
  obtain ⟨t, ht⟩ := hex
  have hlt : ((stTs q ℓ).findIdx fun t => decide (StDes c t hkl)) < (stTs q ℓ).length :=
    List.findIdx_lt_length_of_exists ⟨t, mem_stTs t, by simpa using ht⟩
  have h := List.findIdx_getElem (w := hlt)
  simp only [decide_eq_true_eq] at h
  unfold stSrc3
  rw [List.getD_eq_getElem _ _ hlt]
  convert h

/-- **Case 3 with the computed tuple** `stSrc3`: the source tuple meets `src_good`. -/
theorem stSrcGood_three' (hD : DesignLemma) {Ω C : Type} (fin : Finite Ω) (S : State Ω C)
    (L : GiantLabels S) (πd : S.domGroup →* alternatingGroup (Fin L.q)) (J : JointFn) {κ : ℕ}
    (nm : ClassNum S κ L.q) (hnm : ClassNum.OK fin S L πd κ nm) {β : ℝ} (hβ : 3 / 4 ≤ β)
    (hκ : 5 ≤ κ) (hq : 16 ≤ L.q) (hqκ : 2 * κ ≤ L.q) (hkl : κ < ℓ)
    (hc : aggCase (structX fin S L πd J κ nm (stSrc3 (structX fin S L πd J κ nm
      (fun _ : Fin ℓ => (⟨0, by omega⟩ : Fin L.q))).col hkl (by omega))).grp = .three) :
    StSrcGood fin S L πd J κ nm β (stSrc3 (structX fin S L πd J κ nm
      (fun _ : Fin ℓ => (⟨0, by omega⟩ : Fin L.q))).col hkl (by omega)) := by
  haveI := fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  refine stSrcGood_three fin S L πd J κ nm _ hc ?_
  have hcol : ∀ src : Fin ℓ → Fin L.q, (structX fin S L πd J κ nm src).col =
      rcol S πd κ J nm (dstr S S.x) (dstr S S.y) := fun _ => rfl
  have hgrp : ∀ src : Fin ℓ → Fin L.q, (structX fin S L πd J κ nm src).grp =
      idealGrp S πd κ (dstr S S.x) := fun _ => rfl
  rw [hcol] at hc ⊢
  rw [hgrp] at hc
  have hdom : domSet (idealGrp S πd κ (dstr S S.x)) = ∅ := by
    unfold aggCase at hc
    by_contra hne
    rw [if_pos (Finset.nonempty_iff_ne_empty.2 hne)] at hc
    split_ifs at hc
  obtain ⟨hconf, hcoh⟩ := rcol_coherent S πd κ J nm (dstr S S.x) (dstr S S.y)
  refine stDes_good hconf hcoh hkl hβ (by omega) (stSrc3_des hkl (by omega) ?_)
  exact st_exists_des_three hD S πd J nm hnm hκ hq hqκ hdom hkl

end GI.Impl
