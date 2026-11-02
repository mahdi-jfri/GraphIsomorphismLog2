import Workspace.Algorithm.ColumnInv
import Workspace.Algorithm.Expose

/-!
# The stored levels against the row partition

Section 6.2: "In the natural case, the row partition is already an interval of the retained
hierarchy." This file proves what the column step needs to expose the row interval in the
stored hierarchy (`Workspace/Algorithm/RowExpose.lean`).

Let `R` be the row partition of a row form (the fibers of the natural labels) and let `f` be a
block system of a transitive domain. Then (`low_or_high`):

* either `f` refines `R` (`Low`): each class of `f` lies in one row;
* or each class of `f` meets every row (`High`).

Indeed, the rows met by one class form a block of the action of `Alt(q)` on the rows: two
classes that meet a common row are moved onto each other by the kernel, which is transitive
on that row (the fibers of the labels are the kernel orbits). For `q ≥ 4`, `Alt(q)` has no
nontrivial blocks: a block with two rows `i, j` and without the row `r` is moved by a
3-cycle fixing `i` and sending `j` to `r` onto a block that meets it and is different.

So in a stored hierarchy `⊥ = f_0 ≤ f_1 ≤ ⋯ ≤ f_t` (the last one holds the domain) there is
one switch `J` with `f_J` low and `f_{J+1}` high. Write `t_k` for the number of `f_k`-classes
in an `f_{k+1}`-class, and `u_k` for the same count for the meets `f_k ⊓ R`. Counting the
classes of the whole domain (`classCount_mul`) gives `u_k = t_k` for `k ≠ J` and
`q u_J = t_J` (`exists_switch`): the stored interval `J` splits into the row interval of ratio
`q` and a local interval of ratio `u_J`, and the others are intersected with the rows.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Paper GI.NormalTranspose
open scoped Pointwise

variable {Ω C : Type}

/-! ### The levels of a hierarchy -/

/-- The levels of a hierarchy read from the fine end `f`: `f`, then the coarse ends, then `⊤`. -/
def levOf (f : Setoid Ω) (l : List (Interval Ω)) : ℕ → Setoid Ω
  | 0 => f
  | k + 1 => if h : k < l.length then l[k].part else ⊤

theorem levOf_succ_of_lt {f : Setoid Ω} {l : List (Interval Ω)} {k : ℕ} (h : k < l.length) :
    levOf f l (k + 1) = l[k].part := dif_pos h

theorem levOf_cons_succ (f : Setoid Ω) (I : Interval Ω) (l : List (Interval Ω)) (k : ℕ) :
    levOf f (I :: l) (k + 1) = levOf I.part l k := by
  cases k with
  | zero => simp [levOf]
  | succ k =>
    simp only [levOf, List.length_cons, List.getElem_cons_succ]
    by_cases h : k < l.length
    · rw [dif_pos (by omega), dif_pos h]
    · rw [dif_neg (by omega), dif_neg h]

/-- **The chain conditions at one index.** -/
theorem chain_getElem {G : Subgroup (Perm Ω)} {D : Set Ω} :
    ∀ (f : Setoid Ω) (l : List (Interval Ω)), Chain G D f l → ∀ (k : ℕ) (hk : k < l.length),
      (∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, l[k].part.r (g v) (g w) ↔ l[k].part.r v w) ∧
      (∀ v ∈ D, ∀ w ∈ D, (levOf f l k).r v w → l[k].part.r v w) ∧
      (∀ a ∈ D, classCount (levOf f l k) (classIn G D l[k].part a) ≤ l[k].ratio) ∧
      l[k].cap ≤ l[k].ratio
  | _, [], _, _, hk => absurd hk (by simp)
  | _, _ :: _, h, 0, _ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  | _, I :: l, h, k + 1, hk => by
    have := chain_getElem I.part l h.2.2.2.2 k (by simpa using hk)
    rw [levOf_cons_succ]
    exact this

/-- The levels are block systems. -/
theorem levOf_inv {G : Subgroup (Perm Ω)} {D : Set Ω} {l : List (Interval Ω)}
    (h : HierInv G D l) (k : ℕ) :
    ∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, (levOf ⊥ l k).r (g v) (g w) ↔ (levOf ⊥ l k).r v w := by
  cases k with
  | zero => exact fun g _ v _ w _ => g.injective.eq_iff
  | succ k =>
    by_cases hk : k < l.length
    · rw [levOf_succ_of_lt hk]; exact (chain_getElem _ _ h.chain k hk).1
    · rw [show levOf ⊥ l (k + 1) = ⊤ from dif_neg hk]; exact fun _ _ _ _ _ _ => Iff.rfl

/-- The levels are nested. -/
theorem levOf_mono {G : Subgroup (Perm Ω)} {D : Set Ω} {l : List (Interval Ω)}
    (h : HierInv G D l) (k : ℕ) (hk : k < l.length) :
    ∀ v ∈ D, ∀ w ∈ D, (levOf ⊥ l k).r v w → (levOf ⊥ l (k + 1)).r v w := by
  rw [levOf_succ_of_lt hk]
  exact (chain_getElem _ _ h.chain k hk).2.1

theorem levOf_eq_fineEnd (f : Setoid Ω) (l : List (Interval Ω)) :
    ∀ (k : ℕ), k ≤ l.length → levOf f l k = fineEnd f (l.take k)
  | 0, _ => (fineEnd_take_zero f l).symm
  | k + 1, h => by rw [levOf_succ_of_lt (by omega), fineEnd_take_succ _ _ _ (by omega)]

theorem fineEnd_eq_last : ∀ (f : Setoid Ω) (l : List (Interval Ω)) (h : 0 < l.length),
    fineEnd f l = (l[l.length - 1]'(by omega)).part
  | _, [_], _ => rfl
  | _, I :: J :: l, _ => by
    rw [fineEnd_cons, fineEnd_eq_last I.part (J :: l) (by simp)]
    simp

/-- The last level holds each orbit. -/
theorem levOf_top {G : Subgroup (Perm Ω)} {D : Set Ω} {l : List (Interval Ω)}
    (h : HierInv G D l) (hl : 0 < l.length) :
    ∀ a ∈ D, ∀ w ∈ D, w ∈ orb G a → (levOf ⊥ l l.length).r a w := by
  have : fineEnd ⊥ l = levOf ⊥ l l.length := by
    rw [fineEnd_eq_last ⊥ l hl]
    obtain ⟨m, hm⟩ : ∃ m, l.length = m + 1 := ⟨l.length - 1, by omega⟩
    simp only [hm, levOf_succ_of_lt (show m < l.length by omega)]
    congr 2
  rw [← this]
  exact h.top

/-! ### The row partition and the dichotomy -/

namespace RowForm

variable {S : State Ω C} {L : GiantLabels S} (F : RowForm S L)

/-- The row partition: the fibers of the natural row labels. -/
noncomputable def rowPart : Setoid Ω := S.domKer fun v => F.label v

theorem rowPart_iff {v w : Ω} (hv : v ∈ S.dom) (hw : w ∈ S.dom) :
    F.rowPart.r v w ↔ F.label v = F.label w := by
  rw [rowPart, State.domKer_r_of_mem _ hv hw]

theorem rowPart_inv : ∀ g ∈ S.G, ∀ v w, F.rowPart.r (g v) (g w) ↔ F.rowPart.r v w :=
  State.domKer_inv _ fun g v w h => by
    have h1 := F.natural.equivariant g v v.2
    have h2 := F.natural.equivariant g w w.2
    change F.label (S.domHom g v) = F.label (S.domHom g w)
    rw [State.domHom_apply, State.domHom_apply, h1, h2]
    exact congrArg _ h

/-- `f` refines the rows on the domain. -/
def Low (f : Setoid Ω) : Prop := ∀ v ∈ S.dom, ∀ w ∈ S.dom, f.r v w → F.label v = F.label w

/-- Every class of `f` on the domain meets every row. -/
def High (f : Setoid Ω) : Prop := ∀ v ∈ S.dom, ∀ i, ∃ w ∈ S.dom, f.r v w ∧ F.label w = i

/-- The rows met by the class of `v`. -/
def rowsOf (f : Setoid Ω) (v : Ω) : Set (Fin L.q) := {i | ∃ w ∈ S.dom, f.r v w ∧ F.label w = i}

theorem rowsOf_eq_of_rel {f : Setoid Ω} {v v' : Ω} (h : f.r v v') :
    F.rowsOf f v = F.rowsOf f v' := by
  ext i
  exact ⟨fun ⟨w, hw, hvw, hi⟩ => ⟨w, hw, Setoid.trans' _ (Setoid.symm' _ h) hvw, hi⟩,
    fun ⟨w, hw, hvw, hi⟩ => ⟨w, hw, Setoid.trans' _ h hvw, hi⟩⟩

theorem mem_rowsOf_self {f : Setoid Ω} {v : Ω} (hv : v ∈ S.dom) : F.label v ∈ F.rowsOf f v :=
  ⟨v, hv, Setoid.refl' _ _, rfl⟩

variable {f : Setoid Ω} (hf : ∀ g ∈ S.G, ∀ v ∈ S.dom, ∀ w ∈ S.dom, f.r (g v) (g w) ↔ f.r v w)
include hf

theorem rowsOf_smul (g : S.G) {v : Ω} (hv : v ∈ S.dom) :
    F.rowsOf f (g.val v) = (L.π g).val '' F.rowsOf f v := by
  ext i
  constructor
  · rintro ⟨w, hw, hvw, rfl⟩
    have hw' : g.val⁻¹ w ∈ S.dom := (S.dom_inv _ (S.G.inv_mem g.2) w).2 hw
    refine ⟨F.label (g.val⁻¹ w), ⟨_, hw', ?_, rfl⟩, ?_⟩
    · have := (hf g.val g.2 v hv _ hw').1
      simp only [Perm.apply_inv_self] at this
      exact this hvw
    · have := F.natural.equivariant g _ hw'
      simp only [Perm.apply_inv_self] at this
      exact this.symm
  · rintro ⟨_, ⟨w, hw, hvw, rfl⟩, rfl⟩
    exact ⟨g.val w, (S.dom_inv _ g.2 w).2 hw, (hf g.val g.2 v hv w hw).2 hvw,
      F.natural.equivariant g w hw⟩

/-- **The rows met by the classes form blocks**: two classes that meet a common row meet the
same rows (the kernel is transitive on each row). -/
theorem rowsOf_eq_of_meet {v v' : Ω} (hv : v ∈ S.dom) (hv' : v' ∈ S.dom) {i : Fin L.q}
    (hi : i ∈ F.rowsOf f v) (hi' : i ∈ F.rowsOf f v') : F.rowsOf f v = F.rowsOf f v' := by
  obtain ⟨w, hw, hvw, rfl⟩ := hi
  obtain ⟨w', hw', hvw', he⟩ := hi'
  obtain ⟨k, hk1, hkw⟩ := (F.natural.fibers w hw w' hw').1 he.symm
  have hkv : k.val v ∈ S.dom := (S.dom_inv _ k.2 v).2 hv
  have h1 : F.rowsOf f (k.val v) = F.rowsOf f v := by
    rw [F.rowsOf_smul hf k hv, hk1]; simp
  have h2 : f.r (k.val v) v' := by
    have := (hf k.val k.2 v hv w hw).2 hvw
    rw [hkw] at this
    exact Setoid.trans' _ this (Setoid.symm' _ hvw')
  rw [← h1, F.rowsOf_eq_of_rel h2]

/-- **The dichotomy**: a block system of a transitive domain refines the rows, or each of its
classes meets every row (`Alt(q)` has no nontrivial blocks for `q ≥ 4`). -/
theorem low_or_high (htr : S.Transitive) : F.Low f ∨ F.High f := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnl, hnh⟩ := hcon
  simp only [Low, High, not_forall, not_exists, not_and] at hnl hnh
  obtain ⟨v₁, hv₁, w₁, hw₁, hvw, hne⟩ := hnl
  obtain ⟨v, hv, r₀, hr₀⟩ := hnh
  -- The class of `v₁` misses some row: transport the missing row of `v`.
  obtain ⟨g₀, hg₀, hg₀v⟩ := htr v hv v₁ hv₁
  have hmiss : ∃ r, r ∉ F.rowsOf f v₁ := by
    refine ⟨(L.π ⟨g₀, hg₀⟩).val r₀, fun hr => ?_⟩
    rw [← hg₀v, F.rowsOf_smul hf ⟨g₀, hg₀⟩ hv] at hr
    obtain ⟨r', ⟨w, hw, hvw', rfl⟩, hr'⟩ := hr
    exact hr₀ w hw hvw' ((L.π ⟨g₀, hg₀⟩).val.injective hr')
  obtain ⟨r, hr⟩ := hmiss
  set i := F.label v₁
  set j := F.label w₁
  have hj : j ∈ F.rowsOf f v₁ := ⟨w₁, hw₁, hvw, rfl⟩
  have hi : i ∈ F.rowsOf f v₁ := F.mem_rowsOf_self hv₁
  have hjr : j ≠ r := fun h => hr (h ▸ hj)
  have hir : i ≠ r := fun h => hr (h ▸ hi)
  -- A fourth row `x`.
  obtain ⟨x, hxi, hxj, hxr⟩ : ∃ x : Fin L.q, x ≠ i ∧ x ≠ j ∧ x ≠ r := by
    have h4 := F.four_le
    by_contra hno
    push Not at hno
    have hsub : (Finset.univ : Finset (Fin L.q)) ⊆ {i, j, r} := fun y _ => by
      by_cases h1 : y = i
      · simp [h1]
      by_cases h2 : y = j
      · simp [h2]
      simp [hno y h1 h2]
    have := Finset.card_le_card hsub
    simp only [Finset.card_univ, Fintype.card_fin] at this
    have h3 : ({i, j, r} : Finset (Fin L.q)).card ≤ 3 := Finset.card_le_three
    omega
  -- The 3-cycle `(j r x)` fixes `i` and moves `j` to `r`.
  let c : Perm (Fin L.q) := swap j r * swap r x
  have hc : c ∈ alternatingGroup (Fin L.q) := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hjr, sign_swap (Ne.symm hxr)]
    rfl
  have hci : c i = i := by
    simp only [c, Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne hir (Ne.symm hxi), swap_apply_of_ne_of_ne hne hir]
  have hcj : c j = r := by
    simp only [c, Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne hjr (Ne.symm hxj), swap_apply_left]
  obtain ⟨g, hg⟩ := L.π_surj ⟨c, hc⟩
  have hgv : g.val v₁ ∈ S.dom := (S.dom_inv _ g.2 v₁).2 hv₁
  have himg : F.rowsOf f (g.val v₁) = c '' F.rowsOf f v₁ := by
    rw [F.rowsOf_smul hf g hv₁, hg]
  have heq : F.rowsOf f (g.val v₁) = F.rowsOf f v₁ := by
    refine F.rowsOf_eq_of_meet hf hgv hv₁ (i := i) ?_ hi
    rw [himg]
    exact ⟨i, hi, hci⟩
  apply hr
  rw [← heq, himg]
  exact ⟨j, hj, hcj⟩

omit hf in
theorem low_bot : F.Low ⊥ := fun v _ w _ h => by
  have : v = w := h
  rw [this]

omit hf in
theorem high_mono {f' : Setoid Ω} (hH : F.High f) (hle : ∀ v ∈ S.dom, ∀ w ∈ S.dom, f.r v w → f'.r v w) :
    F.High f' := fun v hv i => by
  obtain ⟨w, hw, hvw, hi⟩ := hH v hv i
  exact ⟨w, hw, hle v hv w hw hvw, hi⟩

theorem inf_rowPart_inv :
    ∀ g ∈ S.G, ∀ v ∈ S.dom, ∀ w ∈ S.dom, (f ⊓ F.rowPart).r (g v) (g w) ↔ (f ⊓ F.rowPart).r v w :=
  fun g hg v hv w hw => and_congr (hf g hg v hv w hw) (F.rowPart_inv g hg v w)

omit hf in
/-- **A high class meets the rows in `q` classes.** -/
theorem count_high [Finite Ω] (htr : S.Transitive) (hH : F.High f) {a : Ω} (ha : a ∈ S.dom) :
    classCount (f ⊓ F.rowPart) (classIn S.G S.dom f a) = L.q := by
  have hwd : ∀ v ∈ classIn S.G S.dom f a, ∀ w ∈ classIn S.G S.dom f a,
      (f ⊓ F.rowPart).r v w → F.label v = F.label w := fun v hv w hw h =>
    (F.rowPart_iff hv.1 hw.1).1 h.2
  apply le_antisymm
  · have := classCount_le_ncard (f := f ⊓ F.rowPart) (X := classIn S.G S.dom f a) F.label
      Set.univ (fun _ _ => trivial) hwd fun v hv w hw h =>
        ⟨Setoid.trans' _ (Setoid.symm' _ hv.2.2) hw.2.2, (F.rowPart_iff hv.1 hw.1).2 h⟩
    simpa using this
  · have := ncard_le_classCount (f := f ⊓ F.rowPart) (X := classIn S.G S.dom f a) F.label
      Set.univ (fun i _ => by
        obtain ⟨w, hw, haw, hi⟩ := hH a ha i
        exact ⟨w, ⟨hw, htr a ha w hw, haw⟩, hi⟩) hwd
    simpa using this

/-- **One stored interval against the rows.** With `t` the number of `f`-classes in an
`f'`-class and `u` the same count for the meets with the rows: `u = t` when both levels are low
or both are high, and `u q = t` at the switch. -/
theorem level_step [Finite Ω] (htr : S.Transitive) {f' : Setoid Ω}
    (hf' : ∀ g ∈ S.G, ∀ v ∈ S.dom, ∀ w ∈ S.dom, f'.r (g v) (g w) ↔ f'.r v w)
    (hle : ∀ v ∈ S.dom, ∀ w ∈ S.dom, f.r v w → f'.r v w) {a : Ω} (ha : a ∈ S.dom) :
    (F.Low f → F.Low f' → classCount (f ⊓ F.rowPart) (classIn S.G S.dom (f' ⊓ F.rowPart) a) =
        classCount f (classIn S.G S.dom f' a)) ∧
      (F.Low f → F.High f' →
        classCount (f ⊓ F.rowPart) (classIn S.G S.dom (f' ⊓ F.rowPart) a) * L.q =
          classCount f (classIn S.G S.dom f' a)) ∧
      (F.High f → F.High f' →
        classCount (f ⊓ F.rowPart) (classIn S.G S.dom (f' ⊓ F.rowPart) a) =
          classCount f (classIn S.G S.dom f' a)) := by
  have hR := F.inf_rowPart_inv hf
  have hR' := F.inf_rowPart_inv hf'
  have h1 := classCount_mul S.dom_inv htr hR hR' (fun v hv w hw h => ⟨hle v hv w hw h.1, h.2⟩) ha
  have h2 := classCount_mul S.dom_inv htr hf hf' hle ha
  have hpos : 0 < classCount f' S.dom := one_le_classCount f' ⟨a, ha⟩
  have hq : 0 < L.q := by have := F.four_le; omega
  -- The number of classes of a meet with the rows.
  have nlow : ∀ {g : Setoid Ω}, F.Low g → classCount (g ⊓ F.rowPart) S.dom = classCount g S.dom :=
    fun hL => classCount_congr fun v hv w hw =>
      ⟨fun h => h.1, fun h => ⟨h, (F.rowPart_iff hv hw).2 (hL v hv w hw h)⟩⟩
  have nhigh : ∀ {g : Setoid Ω}, (∀ x ∈ S.G, ∀ v ∈ S.dom, ∀ w ∈ S.dom, g.r (x v) (x w) ↔ g.r v w) →
      F.High g → classCount (g ⊓ F.rowPart) S.dom = classCount g S.dom * L.q := by
    intro g hg hH
    rw [classCount_mul S.dom_inv htr (F.inf_rowPart_inv hg) hg (fun v _ w _ h => h.1) ha,
      F.count_high htr hH ha]
  set u := classCount (f ⊓ F.rowPart) (classIn S.G S.dom (f' ⊓ F.rowPart) a)
  set t := classCount f (classIn S.G S.dom f' a)
  refine ⟨fun hL hL' => ?_, fun hL hH' => ?_, fun hH hH' => ?_⟩
  · rw [nlow hL, nlow hL'] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)
  · rw [nlow hL, nhigh hf' hH'] at h1
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [← h2, h1]; ring
  · rw [nhigh hf hH, nhigh hf' hH', h2] at h1
    have : classCount f' S.dom * L.q * t = classCount f' S.dom * L.q * u := by
      rw [← h1]; ring
    exact (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hpos hq) this).symm

end RowForm

namespace RowForm

variable {S : State Ω C} {L : GiantLabels S} (F : RowForm S L)

/-- **The switch of a stored hierarchy** (Section 6.2: "the row partition is already an
interval of the retained hierarchy"). In a stored hierarchy with the invariant on a transitive
domain, there is one interval `J` at which the levels switch from refining the rows to meeting
every row. Intersecting with the rows keeps every count `t_k` except at `J`, where
`t_J = u_J q`. -/
theorem exists_switch [Finite Ω] (htr : S.Transitive) (hinv : S.HierInv) (hl : 0 < S.hier.length)
    {a : Ω} (ha : a ∈ S.dom) :
    ∃ J < S.hier.length, F.Low (levOf ⊥ S.hier J) ∧ F.High (levOf ⊥ S.hier (J + 1)) ∧
      ∀ k < S.hier.length,
      (k ≠ J → classCount (levOf ⊥ S.hier k ⊓ F.rowPart)
          (classIn S.G S.dom (levOf ⊥ S.hier (k + 1) ⊓ F.rowPart) a) =
        classCount (levOf ⊥ S.hier k) (classIn S.G S.dom (levOf ⊥ S.hier (k + 1)) a)) ∧
      (k = J → classCount (levOf ⊥ S.hier k ⊓ F.rowPart)
          (classIn S.G S.dom (levOf ⊥ S.hier (k + 1) ⊓ F.rowPart) a) * L.q =
        classCount (levOf ⊥ S.hier k) (classIn S.G S.dom (levOf ⊥ S.hier (k + 1)) a)) := by
  classical
  set l := S.hier
  have hinv' : HierInv S.G S.dom l := hinv
  have hinvk := levOf_inv hinv'
  -- The last level is high.
  have hex : ∃ k, F.High (levOf ⊥ l (k + 1)) := by
    refine ⟨l.length - 1, fun v hv i => ?_⟩
    obtain ⟨w, hw, hi⟩ := F.natural.onto i
    have := levOf_top hinv' hl v hv w hw (htr v hv w hw)
    rw [show l.length - 1 + 1 = l.length by omega]
    exact ⟨w, hw, this, hi⟩
  set J := Nat.find hex
  have hJ : F.High (levOf ⊥ l (J + 1)) := Nat.find_spec hex
  have hJlt : J < l.length := by
    have := Nat.find_min' hex (show F.High (levOf ⊥ l (l.length - 1 + 1)) by
      intro v hv i
      obtain ⟨w, hw, hi⟩ := F.natural.onto i
      have := levOf_top hinv' hl v hv w hw (htr v hv w hw)
      rw [show l.length - 1 + 1 = l.length by omega]
      exact ⟨w, hw, this, hi⟩)
    omega
  have hlow : ∀ k, k ≤ J → F.Low (levOf ⊥ l k) := by
    intro k hk
    cases k with
    | zero => exact F.low_bot
    | succ k =>
      have hnot : ¬ F.High (levOf ⊥ l (k + 1)) := Nat.find_min hex (by omega)
      exact (F.low_or_high (hinvk (k + 1)) htr).resolve_right hnot
  have hhigh : ∀ k, J + 1 ≤ k → k ≤ l.length → F.High (levOf ⊥ l k) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; exact hJ
    | succ k hk ih =>
      intro hkl
      exact F.high_mono (ih (by omega)) (levOf_mono hinv' k (by omega))
  refine ⟨J, hJlt, hlow J le_rfl, hJ, fun k hk => ⟨fun hkJ => ?_, fun hkJ => ?_⟩⟩
  · have step := F.level_step (hinvk k) htr (hinvk (k + 1)) (levOf_mono hinv' k hk) ha
    rcases Nat.lt_or_gt_of_ne hkJ with h | h
    · exact step.1 (hlow k (by omega)) (hlow (k + 1) (by omega))
    · exact step.2.2 (hhigh k (by omega) (by omega)) (hhigh (k + 1) (by omega) (by omega))
  · subst hkJ
    exact (F.level_step (hinvk J) htr (hinvk (J + 1)) (levOf_mono hinv' J hk) ha).2.1
      (hlow J le_rfl) hJ

end RowForm

end GI.Algorithm
