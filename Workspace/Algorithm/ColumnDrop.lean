module

public import Workspace.Algorithm.HierInv

@[expose] public section

/-!
# Dropping trivial intervals

Section 7.1 says "Only nontrivial interval ratios occur". The split of the column step
(`towerSplit`, eq. `modular-index-split`) cuts each local interval into a lower and an upper
piece, and one of the two pieces often has ratio `1`. The implementation must not store such a
piece, because it keeps the invariant `GI.Impl.SmallInv` (every stored ratio is at least `2`),
which bounds the length of the hierarchy. So the column step stores `dropTriv hier'`: the
intervals of ratio at least `2`.

An interval of ratio at most `1` has at most one fine class in each coarse class of an orbit
(`HierInv` bounds the class counts by the ratios). So inside every orbit its two ends agree,
and removing it changes no condition of `HierInv` (`HierInv.dropTriv`). It adds `0` to `ρ` and
to `Q` (`hierRho_dropTriv`, `hierQ_dropTriv`). On a transitive domain the levels of the
hierarchy that remain agree with the old ones, so the carrier invariant passes too
(`CarrierOK.dropTriv`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

variable {Ω : Type}

/-- The intervals of ratio at least `2`, in order. -/
def dropTriv (l : List (Interval Ω)) : List (Interval Ω) := l.filter fun I => 2 ≤ I.ratio

@[simp] theorem dropTriv_nil : dropTriv ([] : List (Interval Ω)) = [] := rfl

theorem dropTriv_cons_of_le {I : Interval Ω} (l : List (Interval Ω)) (h : 2 ≤ I.ratio) :
    dropTriv (I :: l) = I :: dropTriv l := by
  simp [dropTriv, h]

theorem dropTriv_cons_of_lt {I : Interval Ω} (l : List (Interval Ω)) (h : I.ratio < 2) :
    dropTriv (I :: l) = dropTriv l := by
  simp only [dropTriv, List.filter_cons, decide_eq_true_eq]
  rw [if_neg (by omega)]

theorem dropTriv_append (l₁ l₂ : List (Interval Ω)) :
    dropTriv (l₁ ++ l₂) = dropTriv l₁ ++ dropTriv l₂ :=
  List.filter_append _ _

theorem mem_dropTriv {I : Interval Ω} {l : List (Interval Ω)} :
    I ∈ dropTriv l ↔ I ∈ l ∧ 2 ≤ I.ratio := by
  simp [dropTriv]

theorem dropTriv_length_le (l : List (Interval Ω)) : (dropTriv l).length ≤ l.length :=
  List.length_filter_le _ _

/-- A trivial interval adds `0` to `ρ`. -/
theorem hierRho_dropTriv : ∀ l : List (Interval Ω), State.hierRho (dropTriv l) = State.hierRho l
  | [] => rfl
  | I :: l => by
    by_cases h : 2 ≤ I.ratio
    · rw [dropTriv_cons_of_le l h]
      simp only [State.hierRho, List.map_cons, List.sum_cons] at *
      rw [← State.hierRho, ← State.hierRho, hierRho_dropTriv l]
    · rw [dropTriv_cons_of_lt l (by omega), hierRho_dropTriv l]
      have : GI.towerRank I.ratio = 0 := by unfold GI.towerRank; rw [if_pos (by omega)]
      simp [State.hierRho, this]

/-- A trivial interval adds `0` to `Q` (`log 0 = log 1 = 0`). -/
theorem hierQ_dropTriv : ∀ l : List (Interval Ω), State.hierQ (dropTriv l) = State.hierQ l
  | [] => rfl
  | I :: l => by
    by_cases h : 2 ≤ I.ratio
    · rw [dropTriv_cons_of_le l h]
      simp only [State.hierQ, List.map_cons, List.sum_cons] at *
      rw [← State.hierQ, ← State.hierQ, hierQ_dropTriv l]
    · rw [dropTriv_cons_of_lt l (by omega), hierQ_dropTriv l]
      have : Real.log I.ratio = 0 := by
        rcases (by omega : I.ratio = 0 ∨ I.ratio = 1) with h0 | h1
        · rw [h0, Nat.cast_zero, Real.log_zero]
        · rw [h1, Nat.cast_one, Real.log_one]
      simp [State.hierQ, this]

/-! ### The hierarchy invariant -/

/-- `f'` refines `f` on `D`, and the two agree on pairs of one orbit. -/
def OrbAgree (G : Subgroup (Perm Ω)) (D : Set Ω) (f' f : Setoid Ω) : Prop :=
  (∀ v ∈ D, ∀ w ∈ D, f'.r v w → f.r v w) ∧
    ∀ v ∈ D, ∀ w ∈ D, w ∈ orb G v → f.r v w → f'.r v w

theorem OrbAgree.refl (G : Subgroup (Perm Ω)) (D : Set Ω) (f : Setoid Ω) : OrbAgree G D f f :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem orb_symm {G : Subgroup (Perm Ω)} {v w : Ω} (h : w ∈ orb G v) : v ∈ orb G w := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g⁻¹, G.inv_mem hg, by simp⟩

theorem orb_trans {G : Subgroup (Perm Ω)} {u v w : Ω} (h₁ : v ∈ orb G u) (h₂ : w ∈ orb G v) :
    w ∈ orb G u := by
  obtain ⟨g, hg, rfl⟩ := h₁
  obtain ⟨g', hg', rfl⟩ := h₂
  exact ⟨g' * g, G.mul_mem hg' hg, rfl⟩

/-- At most one class meets `X`: any two points of `X` are related. -/
theorem rel_of_classCount_le_one [Finite Ω] {f : Setoid Ω} {X : Set Ω} (h : classCount f X ≤ 1)
    {v w : Ω} (hv : v ∈ X) (hw : w ∈ X) : f.r v w := by
  unfold classCount at h
  haveI : Subsingleton (Quotient (Setoid.comap (Subtype.val : X → Ω) f)) :=
    Finite.card_le_one_iff_subsingleton.1 h
  have := Subsingleton.elim (Quotient.mk (Setoid.comap (Subtype.val : X → Ω) f) ⟨v, hv⟩)
    (Quotient.mk (Setoid.comap (Subtype.val : X → Ω) f) ⟨w, hw⟩)
  exact (Quotient.exact this : (Setoid.comap (Subtype.val : X → Ω) f) ⟨v, hv⟩ ⟨w, hw⟩)

/-- Two fine ends that agree inside orbits give the same class counts in a class of an orbit. -/
theorem OrbAgree.classCount_eq {G : Subgroup (Perm Ω)} {D : Set Ω} {f' f : Setoid Ω}
    (h : OrbAgree G D f' f) (c : Setoid Ω) (a : Ω) :
    classCount f' (classIn G D c a) = classCount f (classIn G D c a) :=
  classCount_congr fun v hv w hw =>
    ⟨h.1 v hv.1 w hw.1, h.2 v hv.1 w hw.1 (orb_trans (orb_symm hv.2.1) hw.2.1)⟩

theorem OrbAgree.capAt {G : Subgroup (Perm Ω)} {D : Set Ω} (hD : Invariant G D)
    {f' f c : Setoid Ω} {b : ℕ} {a : Ω} (h : OrbAgree G D f' f) (hc : CapAt G D f c b a) :
    CapAt G D f' c b a := by
  intro U hU hUa t ht φ hφ hk
  refine hc U hU hUa t ht φ hφ fun u hu => hk u fun w hw => ?_
  have hu' : (u : Perm Ω) w ∈ D := (hD u (hU u.2) w).2 hw.1
  have hrel := h.2 w hw.1 _ hu' ⟨u, hU u.2, rfl⟩ (f.iseqv.symm (hu w hw))
  exact f'.iseqv.symm hrel

/-- A trivial interval: its coarse end agrees with its fine end inside orbits. -/
theorem OrbAgree.of_triv [Finite Ω] {G : Subgroup (Perm Ω)} {D : Set Ω} {f' f : Setoid Ω}
    {I : Interval Ω} (h : OrbAgree G D f' f) (hle : ∀ v ∈ D, ∀ w ∈ D, f.r v w → I.part.r v w)
    (hcount : ∀ a ∈ D, classCount f (classIn G D I.part a) ≤ I.ratio) (hr : I.ratio < 2) :
    OrbAgree G D f' I.part := by
  refine ⟨fun v hv w hw hvw => hle v hv w hw (h.1 v hv w hw hvw), fun v hv w hw hvw hI => ?_⟩
  refine h.2 v hv w hw hvw ?_
  refine rel_of_classCount_le_one (X := classIn G D I.part v) (by have := hcount v hv; omega)
    ⟨hv, ⟨1, G.one_mem, rfl⟩, I.part.iseqv.refl v⟩ ⟨hw, hvw, hI⟩

/-- **Dropping trivial intervals keeps the chain and the caps.** -/
theorem chain_caps_dropTriv [Finite Ω] {G : Subgroup (Perm Ω)} {D : Set Ω} (hD : Invariant G D) :
    ∀ {f f' : Setoid Ω} {l : List (Interval Ω)}, Chain G D f l → Caps G D f l →
      OrbAgree G D f' f →
      Chain G D f' (dropTriv l) ∧ Caps G D f' (dropTriv l) ∧
        OrbAgree G D (fineEnd f' (dropTriv l)) (fineEnd f l)
  | _, _, [], _, _, h => ⟨trivial, trivial, h⟩
  | f, f', I :: l, ⟨hinv, hle, hcount, hcap, hch⟩, ⟨hcaps, hcs⟩, h => by
    by_cases hr : 2 ≤ I.ratio
    · rw [dropTriv_cons_of_le l hr]
      obtain ⟨c1, c2, c3⟩ := chain_caps_dropTriv hD hch hcs (OrbAgree.refl G D I.part)
      refine ⟨⟨hinv, fun v hv w hw hvw => hle v hv w hw (h.1 v hv w hw hvw),
        fun a ha => (h.classCount_eq I.part a).trans_le (hcount a ha), hcap, c1⟩,
        ⟨fun a ha => h.capAt hD (hcaps a ha), c2⟩, c3⟩
    · rw [dropTriv_cons_of_lt l (by omega)]
      exact chain_caps_dropTriv hD hch hcs (h.of_triv hle hcount (by omega))

/-- **The hierarchy invariant without the trivial intervals.** -/
theorem HierInv.dropTriv [Finite Ω] {G : Subgroup (Perm Ω)} {D : Set Ω} (hD : Invariant G D)
    {l : List (Interval Ω)} (h : HierInv G D l) : HierInv G D (dropTriv l) := by
  obtain ⟨c1, c2, c3⟩ := chain_caps_dropTriv hD h.chain h.caps (OrbAgree.refl G D ⊥)
  exact ⟨c1, fun a ha w hw hwa => c3.2 a ha w hw hwa (h.top a ha w hw hwa), c2⟩

/-- On a transitive domain the remaining levels agree with the old ones, so the columns stay a
level of the hierarchy. -/
theorem ColsLevel.dropTriv [Finite Ω] {G : Subgroup (Perm Ω)} {D : Set Ω} (hD : Invariant G D)
    (htr : ∀ v ∈ D, ∀ w ∈ D, w ∈ orb G v) {l : List (Interval Ω)} (h : HierInv G D l)
    {c : Setoid Ω} (hc : ColsLevel D l c) : ColsLevel D (GI.Algorithm.dropTriv l) c := by
  obtain ⟨pre, post, rfl, hpre⟩ := hc
  have hch := (chain_append.1 h.chain).1
  have hcs := (caps_append.1 h.caps).1
  obtain ⟨-, -, hag⟩ := chain_caps_dropTriv hD hch hcs (OrbAgree.refl G D ⊥)
  refine ⟨GI.Algorithm.dropTriv pre, GI.Algorithm.dropTriv post, dropTriv_append _ _,
    fun v hv w hw => ?_⟩
  rw [← hpre v hv w hw]
  exact ⟨hag.1 v hv w hw, hag.2 v hv w hw (htr v hv w hw)⟩

/-- **The carrier invariant without the trivial intervals**, on a transitive domain. -/
theorem CarrierOK.dropTriv [Finite Ω] {G : Subgroup (Perm Ω)} {D : Set Ω} (hD : Invariant G D)
    (htr : ∀ v ∈ D, ∀ w ∈ D, w ∈ orb G v) {rows : Option (RowRecord Ω)}
    {l : List (Interval Ω)} (h : HierInv G D l) (hc : CarrierOK G D rows l) :
    CarrierOK G D rows (GI.Algorithm.dropTriv l) := fun R hR => by
  obtain ⟨c, hcR, hspec, hlev⟩ := hc R hR
  exact ⟨c, hcR, hspec, hlev.dropTriv hD htr h⟩

end GI.Algorithm
