module

public import Workspace.Impl.VsPOrb

@[expose] public section

/-!
# The orbit list is closed after enough passes

The orbit program keeps a list of pairs `(z, key z)` with distinct keys. Suppose all elements
lie in a set `T` closed under conjugation by the generators `hs1`, and the keys of `T` lie in a
finite set `K` with `|K| < cap`. Then the list never fills up, each pass either adds a pair or
changes nothing, and after `|K|` passes no pass adds anything. At that point every conjugate
`h z h⁻¹` (`h ∈ hs1`, `z` in the list) has the key of some element of the list
(`vsPOrbit_closed`).
-/

namespace GI.Proved

open GI.Impl Equiv

variable {n : ℕ} (kf : Perm (Fin n) → List ℕ) (cap : ℕ) (hs1 : List (Perm (Fin n)))
  (T : Set (Perm (Fin n))) (K : Finset (List ℕ))

/-- The invariant: entries are `(z, kf z)` with `z ∈ T`, and the keys are distinct. -/
def VsPOInv (O : List (Perm (Fin n) × List ℕ)) : Prop :=
  (∀ p ∈ O, p.2 = kf p.1 ∧ p.1 ∈ T) ∧ (O.map Prod.snd).Nodup

variable {kf cap hs1 T K}

theorem VsPOInv.length_le (hK : ∀ z ∈ T, kf z ∈ K) {O : List (Perm (Fin n) × List ℕ)}
    (h : VsPOInv kf T O) : O.length ≤ K.card := by
  classical
  have e : (O.map Prod.snd).toFinset.card = O.length := by
    rw [List.toFinset_card_of_nodup h.2, List.length_map]
  rw [← e]
  refine Finset.card_le_card fun κ hκ => ?_
  rw [List.mem_toFinset, List.mem_map] at hκ
  obtain ⟨p, hp, rfl⟩ := hκ
  rw [(h.1 p hp).1]; exact hK _ (h.1 p hp).2

/-- **One insertion.** The list grows by a suffix, keeps the invariant, and holds the key. -/
theorem vsPOIns_inv (hK : ∀ z ∈ T, kf z ∈ K) (hcap : K.card < cap)
    {O : List (Perm (Fin n) × List ℕ)} (h : VsPOInv kf T O) {c : Perm (Fin n)} (hc : c ∈ T) :
    VsPOInv kf T (vsPOIns kf cap O c) ∧ O <+: vsPOIns kf cap O c ∧
      kf c ∈ (vsPOIns kf cap O c).map Prod.snd := by
  have hl := h.length_le hK
  unfold vsPOIns
  by_cases hnew : (O.map Prod.snd).findIdx (fun κ => decide (κ = kf c)) = O.length
  · have hlt : O.length < cap ∧ _ := ⟨by omega, hnew⟩
    rw [if_pos hlt]
    have hno : ∀ κ ∈ O.map Prod.snd, κ ≠ kf c := by
      have := List.findIdx_eq_length.mp (by rw [List.length_map]; exact hnew)
      intro κ hκ e; have := this κ hκ; simp [e] at this
    refine ⟨⟨fun p hp => ?_, ?_⟩, List.prefix_append _ _, by simp⟩
    · rcases List.mem_append.mp hp with hp | hp
      · exact h.1 p hp
      · simp at hp; subst hp; exact ⟨rfl, hc⟩
    · rw [List.map_append, List.nodup_append]
      refine ⟨h.2, by simp, ?_⟩
      intro a ha b hb e
      simp at hb; subst hb; exact hno a ha e
  · have hnot : ¬ (O.length < cap ∧
        (O.map Prod.snd).findIdx (fun κ => decide (κ = kf c)) = O.length) := fun h' => hnew h'.2
    rw [if_neg hnot]
    refine ⟨h, List.prefix_refl _, ?_⟩
    have hlt : (O.map Prod.snd).findIdx (fun κ => decide (κ = kf c)) < (O.map Prod.snd).length := by
      have := List.findIdx_le_length (p := fun κ => decide (κ = kf c)) (xs := O.map Prod.snd)
      rw [List.length_map] at this ⊢; omega
    have := List.findIdx_getElem (w := hlt)
    rw [decide_eq_true_eq] at this
    rw [← this]; exact List.getElem_mem _

/-- **The inner loop** over the generators. -/
theorem vsPOInner_inv (hK : ∀ z ∈ T, kf z ∈ K) (hcap : K.card < cap)
    (hT : ∀ h ∈ hs1, ∀ z ∈ T, h * z * h⁻¹ ∈ T) {z : Perm (Fin n)} (hz : z ∈ T) :
    ∀ (hs' : List (Perm (Fin n))), (∀ h ∈ hs', h ∈ hs1) → ∀ O, VsPOInv kf T O →
      VsPOInv kf T (hs'.foldl (fun O h => vsPOIns kf cap O (h * z * h⁻¹)) O) ∧
      O <+: hs'.foldl (fun O h => vsPOIns kf cap O (h * z * h⁻¹)) O ∧
      ∀ h ∈ hs', kf (h * z * h⁻¹) ∈
        (hs'.foldl (fun O h => vsPOIns kf cap O (h * z * h⁻¹)) O).map Prod.snd := by
  intro hs'
  induction hs' with
  | nil => intro _ O hO; exact ⟨hO, List.prefix_refl _, by simp⟩
  | cons h hs' ih =>
    intro hh O hO
    obtain ⟨i1, p1, k1⟩ := vsPOIns_inv hK hcap hO (hT h (hh h (by simp)) z hz)
    obtain ⟨i2, p2, k2⟩ := ih (fun h' hh' => hh h' (by simp [hh'])) _ i1
    refine ⟨i2, p1.trans p2, fun h' hh' => ?_⟩
    rcases List.mem_cons.mp hh' with rfl | hh'
    · exact (p2.map Prod.snd).subset k1
    · exact k2 h' hh'

/-- **One pass.** It keeps the invariant, grows the list by a suffix, and for every pair of the
old list and every generator, the key of the conjugate is present afterwards. -/
theorem vsPOPass_inv (hK : ∀ z ∈ T, kf z ∈ K) (hcap : K.card < cap)
    (hT : ∀ h ∈ hs1, ∀ z ∈ T, h * z * h⁻¹ ∈ T) :
    ∀ (L O : List (Perm (Fin n) × List ℕ)), (∀ p ∈ L, p.1 ∈ T) → VsPOInv kf T O →
      VsPOInv kf T (L.foldl (fun O' p => vsPOInner kf cap hs1 p.1 O') O) ∧
      O <+: L.foldl (fun O' p => vsPOInner kf cap hs1 p.1 O') O ∧
      ∀ p ∈ L, ∀ h ∈ hs1, kf (h * p.1 * h⁻¹) ∈
        (L.foldl (fun O' p => vsPOInner kf cap hs1 p.1 O') O).map Prod.snd := by
  intro L
  induction L with
  | nil => intro O _ hO; exact ⟨hO, List.prefix_refl _, by simp⟩
  | cons q L ih =>
    intro O hL hO
    obtain ⟨i1, p1, k1⟩ := vsPOInner_inv hK hcap hT (hL q (by simp)) hs1 (fun _ h => h) O hO
    obtain ⟨i2, p2, k2⟩ := ih _ (fun p hp => hL p (by simp [hp])) i1
    refine ⟨i2, p1.trans p2, fun p hp h hh => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (p2.map Prod.snd).subset (k1 h hh)
    · exact k2 p hp h hh

theorem vsPOPass_inv' (hK : ∀ z ∈ T, kf z ∈ K) (hcap : K.card < cap)
    (hT : ∀ h ∈ hs1, ∀ z ∈ T, h * z * h⁻¹ ∈ T) {O : List (Perm (Fin n) × List ℕ)}
    (hO : VsPOInv kf T O) :
    VsPOInv kf T (vsPOPass kf cap hs1 O) ∧ O <+: vsPOPass kf cap hs1 O ∧
      ∀ p ∈ O, ∀ h ∈ hs1, kf (h * p.1 * h⁻¹) ∈ (vsPOPass kf cap hs1 O).map Prod.snd :=
  vsPOPass_inv hK hcap hT O O (fun p hp => (hO.1 p hp).2) hO

/-- Either the `F`-th list is a fixed point of the pass, or it has more than `F` entries. -/
theorem vsPOrbit_grow (hK : ∀ z ∈ T, kf z ∈ K) (hcap : K.card < cap)
    (hT : ∀ h ∈ hs1, ∀ z ∈ T, h * z * h⁻¹ ∈ T) {y : Perm (Fin n)} (hy : y ∈ T) :
    ∀ F, VsPOInv kf T (vsPOrbit kf cap hs1 F y) ∧
      (vsPOPass kf cap hs1 (vsPOrbit kf cap hs1 F y) = vsPOrbit kf cap hs1 F y ∨
        F + 1 ≤ (vsPOrbit kf cap hs1 F y).length) := by
  intro F
  induction F with
  | zero =>
    refine ⟨⟨fun p hp => ?_, by simp [vsPOrbit]⟩, Or.inr (by simp [vsPOrbit])⟩
    simp [vsPOrbit] at hp; subst hp; exact ⟨rfl, hy⟩
  | succ F ih =>
    have e : vsPOrbit kf cap hs1 (F + 1) y = vsPOPass kf cap hs1 (vsPOrbit kf cap hs1 F y) := by
      simp only [vsPOrbit, Function.iterate_succ_apply']
    obtain ⟨i1, p1, -⟩ := vsPOPass_inv' hK hcap hT ih.1
    rw [e]
    refine ⟨i1, ?_⟩
    rcases ih.2 with hfix | hlen
    · left; rw [hfix, hfix]
    · by_cases hfix : vsPOPass kf cap hs1 (vsPOPass kf cap hs1 (vsPOrbit kf cap hs1 F y)) =
          vsPOPass kf cap hs1 (vsPOrbit kf cap hs1 F y)
      · exact Or.inl hfix
      · right
        have hne : vsPOPass kf cap hs1 (vsPOrbit kf cap hs1 F y) ≠ vsPOrbit kf cap hs1 F y := by
          intro h'; apply hfix; rw [h', h']
        have hle := p1.length_le
        have hlt : (vsPOrbit kf cap hs1 F y).length < (vsPOPass kf cap hs1 (vsPOrbit kf cap hs1 F y)).length := by
          rcases Nat.lt_or_ge (vsPOrbit kf cap hs1 F y).length
            (vsPOPass kf cap hs1 (vsPOrbit kf cap hs1 F y)).length with h' | h'
          · exact h'
          · exact absurd (p1.eq_of_length (le_antisymm hle h')).symm hne
        omega

/-- **Closure.** After at least `|K|` passes, the list contains `(y, kf y)` first, keeps the
invariant, and every conjugate of an element by a generator has the key of an element. -/
theorem vsPOrbit_closed (hK : ∀ z ∈ T, kf z ∈ K) (hcap : K.card < cap)
    (hT : ∀ h ∈ hs1, ∀ z ∈ T, h * z * h⁻¹ ∈ T) {y : Perm (Fin n)} (hy : y ∈ T) {F : ℕ}
    (hF : K.card ≤ F) :
    VsPOInv kf T (vsPOrbit kf cap hs1 F y) ∧ (y, kf y) ∈ vsPOrbit kf cap hs1 F y ∧
      ∀ p ∈ vsPOrbit kf cap hs1 F y, ∀ h ∈ hs1,
        ∃ q ∈ vsPOrbit kf cap hs1 F y, kf (h * p.1 * h⁻¹) = kf q.1 := by
  obtain ⟨hinv, hfix⟩ := vsPOrbit_grow hK hcap hT hy F
  have hfix' : vsPOPass kf cap hs1 (vsPOrbit kf cap hs1 F y) = vsPOrbit kf cap hs1 F y := by
    rcases hfix with h | h
    · exact h
    · have := hinv.length_le hK; omega
  have hpre : ∀ F, [(y, kf y)] <+: vsPOrbit kf cap hs1 F y := by
    intro F
    induction F with
    | zero => exact List.prefix_refl _
    | succ F ih =>
      have e : vsPOrbit kf cap hs1 (F + 1) y = vsPOPass kf cap hs1 (vsPOrbit kf cap hs1 F y) := by
        simp only [vsPOrbit, Function.iterate_succ_apply']
      rw [e]
      exact ih.trans (vsPOPass_inv' hK hcap hT (vsPOrbit_grow hK hcap hT hy F).1).2.1
  refine ⟨hinv, (hpre F).subset (by simp), fun p hp h hh => ?_⟩
  have := (vsPOPass_inv' hK hcap hT hinv).2.2 p hp h hh
  rw [hfix', List.mem_map] at this
  obtain ⟨q, hq, e⟩ := this
  exact ⟨q, hq, by rw [← e, (hinv.1 q hq).1]⟩

end GI.Proved
