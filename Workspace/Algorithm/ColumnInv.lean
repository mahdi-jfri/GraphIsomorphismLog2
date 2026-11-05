module

public import Workspace.Algorithm.ColumnCoords
public import Workspace.Algorithm.Expose

@[expose] public section

/-!
# The hierarchy invariant after a column step

Algorithm 4: "Refactor the old hierarchy by splitting and reordering its interval factors.
Inherit every interval bound, clamped by its new interval ratio." The proof of Lemma A.14
splits each local ratio `[L_{j+1} : L_j]` into a lower factor `[L_{j+1} ∩ N : L_j ∩ N]` (inside
the cells `{i} × Δ`) and an upper factor `[N L_{j+1} : N L_j]` (on the column quotient), with
the row interval of ratio `q` between them ("the clean product interchanges the ratio sequence
`r_1, …, r_s, m` with `m, r_1, …, r_s`").

This file proves that the refactored hierarchy `ColumnStep.hier'` satisfies the hierarchy
invariant `HierInv` on a transitive state (`ColumnStep.hierInv`), from the data of the column
step alone. So the field `hinv` of `GiantCase.columns` follows from the other data.

## The proof

Every new coarse end is a block system: the rows, the local levels and the columns are
(`locRow_inv`, `cols_inv`, Lemma A.14), and meets and joins of block systems are. The coarse
ends are nested. The counting condition reduces, by transitivity, to the classes of the base
point `e(b₀, i0)`, and there each count is at most the size of an orbit whose stabilizer gives
the stored ratio:

* lower piece `j`: the level-`(j-1)` blocks inside `blk j b₀ ∩ N b₀` lie in one orbit of
  `L_{j+1} ∩ N` on the blocks, whose stabilizer is `L_j ∩ N` (`lower_count`);
* the row interval: the cells `{i} × Δ` of one column are indexed by the `q` rows
  (`mid_count`);
* upper piece `j`: the `N`-saturations of level-`(j-1)` blocks inside one saturation of a
  level-`j` block lie in one orbit of `N L_{j+1}`, whose stabilizer is `N L_j` (`upper_count`;
  here `H` is transitive on a row, `local_transitive`).

The last upper coarse end holds the whole domain, because the last local level holds the row.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Paper GI.NormalTranspose
open scoped Pointwise

variable {Ω C : Type}

namespace ColumnPre

variable {S : State Ω C} {L : GiantLabels S} (I : ColumnPre S L)

/-- The local group `H` is transitive on a row (`GI.NormalTranspose.local_transitive`). -/
theorem Hb_transitive (htr : S.Transitive) (b b' : I.B) : ∃ h : I.Hb, h • b = b' := by
  have hK : ∀ k ∈ blockKernel I.e, ∀ b i, (I.e.symm (k.val (I.e (b, i)))).2 = i := by
    rintro k ⟨y, hy⟩ b i
    change cleanRowPerm I.e y = (k : Perm S.dom) at hy
    rw [← hy, cleanRowPerm_apply, Equiv.symm_apply_apply]
  have htrans : ∀ v w : S.dom, ∃ g : S.domGroup, g.val v = w := by
    haveI := S.domGroup_pretransitive htr
    intro v w
    exact MulAction.exists_smul_eq S.domGroup v w
  exact local_transitive I.i0 I.pure hK I.complement htrans b b'

omit L I in
theorem onD {r : Setoid Ω} (h : ∀ g ∈ S.G, ∀ v w, r.r (g v) (g w) ↔ r.r v w) :
    ∀ g ∈ S.G, ∀ v ∈ S.dom, ∀ w ∈ S.dom, r.r (g v) (g w) ↔ r.r v w :=
  fun g hg v _ w _ => h g hg v w

/-- The fine ends of the lower pieces: the points, then the lower coarse ends. -/
noncomputable def lowFine : ℕ → Setoid Ω
  | 0 => ⊥
  | k + 1 => I.lowerPart k

/-- The fine ends of the upper pieces: the columns, then the upper coarse ends. -/
noncomputable def upFine : ℕ → Setoid Ω
  | 0 => I.cols
  | k + 1 => I.upperPart k

/-- The local tower. -/
abbrev Lt : ℕ → Subgroup I.Hb := RowForm.localTower I.e I.i0 I.loc I.b₀

theorem lowFine_inv (k : ℕ) : ∀ g ∈ S.G, ∀ v w, (I.lowFine k).r (g v) (g w) ↔ (I.lowFine k).r v w := by
  cases k with
  | zero => intro g _ v w; exact g.injective.eq_iff
  | succ k => exact I.lowerPart_inv k

theorem upFine_inv (k : ℕ) : ∀ g ∈ S.G, ∀ v w, (I.upFine k).r (g v) (g w) ↔ (I.upFine k).r v w := by
  cases k with
  | zero => exact I.cols_inv
  | succ k => exact I.upperPart_inv k

theorem coords {v : Ω} (hv : v ∈ S.dom) : ∃ c i, v = (I.e (c, i) : Ω) :=
  ⟨_, _, I.eq_e hv⟩

/-! ### The counts -/

theorem a₀_mem : (I.e (I.b₀, I.i0) : Ω) ∈ S.dom := (I.e _).2

variable [Finite Ω]

/-- **The count of a lower piece.** -/
theorem lower_count (htr : S.Transitive) (k : ℕ) (a : Ω) (ha : a ∈ S.dom) :
    classCount (I.lowFine k) (classIn S.G S.dom (I.lowerPart k) a) ≤
      (I.Lt k ⊓ I.Nl).relIndex (I.Lt (k + 1) ⊓ I.Nl) := by
  haveI : Finite I.B := Finite.of_injective (fun c => I.e (c, I.i0)) fun c d h => by
    simpa using h
  rw [classCount_classIn_eq S.dom_inv htr (onD (I.lowFine_inv k)) (onD (I.lowerPart_inv k))
    I.a₀_mem ha]
  rw [relIndex_eq_ncard_orbit _ _ (I.blk k I.b₀) fun x hx => by
    rw [Subgroup.mem_inf, Lt, I.localTower_eq, MulAction.mem_stabilizer_iff]
    exact and_iff_left (Subgroup.mem_inf.1 hx).2]
  refine classCount_le_ncard (fun v => I.blk k (I.cB v)) _ ?_ ?_ ?_
  · rintro v ⟨hv, -, hrel⟩
    obtain ⟨c, i, rfl⟩ := I.coords hv
    obtain ⟨⟨-, hl⟩, n, hn⟩ := (I.lowerPart_e k _ _ _ _).1 hrel
    simp only [blk, Set.mem_singleton_iff] at hn
    have hnL : (n : I.Hb) ∈ I.Lt (k + 1) := by
      rw [Lt, I.mem_localTower_iff]
      change RowForm.lvl I.e I.i0 I.loc k I.b₀ _
      rw [← hn]; exact hl
    refine ⟨⟨n, Subgroup.mem_inf.2 ⟨hnL, n.2⟩⟩, ?_⟩
    simp only [I.cB_e]
    rw [hn]
    exact I.blk_smul (n : I.Hb) k I.b₀
  · rintro v ⟨hv, -, -⟩ w ⟨hw, -, -⟩ hvw
    obtain ⟨c, i, rfl⟩ := I.coords hv
    obtain ⟨d, i', rfl⟩ := I.coords hw
    simp only [I.cB_e]
    cases k with
    | zero =>
      have : (I.e (c, i) : Ω) = I.e (d, i') := hvw
      rw [Subtype.coe_inj, I.e.apply_eq_iff_eq, Prod.mk.injEq] at this
      rw [this.1]
    | succ k =>
      obtain ⟨⟨-, hl⟩, -⟩ := (I.lowerPart_e k _ _ _ _).1 hvw
      exact (I.blk_eq_iff _ _ _).2 hl
  · rintro v ⟨hv, -, hv'⟩ w ⟨hw, -, hw'⟩ hvw
    obtain ⟨c, i, rfl⟩ := I.coords hv
    obtain ⟨d, i', rfl⟩ := I.coords hw
    simp only [I.cB_e] at hvw
    obtain ⟨⟨hi, -⟩, hc⟩ := (I.lowerPart_e k _ _ _ _).1 hv'
    obtain ⟨⟨hi', -⟩, hd⟩ := (I.lowerPart_e k _ _ _ _).1 hw'
    have hcd : d ∈ I.sat 0 c := by
      rw [I.sat_eq_of_mem 0 hc]; exact hd
    cases k with
    | zero =>
      have : d = c := by
        have := I.mem_blk_self 0 d
        rw [← hvw] at this
        exact this
      change (I.e (c, i) : Ω) = I.e (d, i')
      rw [this, ← hi, ← hi']
    | succ k =>
      refine (I.lowerPart_e k _ _ _ _).2 ⟨⟨hi.symm.trans hi', ?_⟩, hcd⟩
      have := I.mem_blk_self (k + 1) d
      rw [← hvw] at this
      exact this

omit [Finite Ω] in
/-- **The count of the row interval.** -/
theorem mid_count (a : Ω) :
    classCount (I.lowerPart (I.loc.length - 1)) (classIn S.G S.dom I.cols a) ≤ L.q := by
  have hT := classCount_le_ncard (f := I.lowerPart (I.loc.length - 1))
    (X := classIn S.G S.dom I.cols a) (fun v => I.cI v) Set.univ (fun _ _ => trivial) ?_ ?_
  · simpa using hT
  · rintro v ⟨hv, -, -⟩ w ⟨hw, -, -⟩ hvw
    obtain ⟨c, i, rfl⟩ := I.coords hv
    obtain ⟨d, i', rfl⟩ := I.coords hw
    obtain ⟨⟨hi, -⟩, -⟩ := (I.lowerPart_e _ _ _ _ _).1 hvw
    simp [hi]
  · rintro v ⟨hv, -, hv'⟩ w ⟨hw, -, hw'⟩ hvw
    obtain ⟨c, i, rfl⟩ := I.coords hv
    obtain ⟨d, i', rfl⟩ := I.coords hw
    simp only [I.cI_e] at hvw
    have hcols : I.cols.r (I.e (c, i)) (I.e (d, i')) := Setoid.trans' _ (Setoid.symm' _ hv') hw'
    refine (I.lowerPart_e _ _ _ _ _).2 ⟨⟨hvw, I.lvl_top c d⟩, (I.cols_e _ _ _ _).1 hcols⟩

/-- **The count of an upper piece.** -/
theorem upper_count (htr : S.Transitive) (k : ℕ) (a : Ω) (ha : a ∈ S.dom) :
    classCount (I.upFine k) (classIn S.G S.dom (I.upperPart k) a) ≤
      (I.Nl ⊔ I.Lt k).relIndex (I.Nl ⊔ I.Lt (k + 1)) := by
  haveI : Finite I.B := Finite.of_injective (fun c => I.e (c, I.i0)) fun c d h => by
    simpa using h
  rw [classCount_classIn_eq S.dom_inv htr (onD (I.upFine_inv k)) (onD (I.upperPart_inv k))
    I.a₀_mem ha]
  -- The stabilizer of the saturation of the base block is `N L_k`.
  have hstab : ∀ x : I.Hb, x ∈ I.Nl ⊔ I.Lt k ↔ x • I.sat k I.b₀ = I.sat k I.b₀ := by
    intro x
    constructor
    · intro hx
      have h1 : I.Nl ≤ MulAction.stabilizer I.Hb (I.sat k I.b₀) := by
        intro n hn
        rw [MulAction.mem_stabilizer_iff, I.sat_smul, eq_comm, I.sat_eq_iff]
        exact ⟨⟨n, hn⟩, I.mem_blk_self _ _⟩
      have h2 : I.Lt k ≤ MulAction.stabilizer I.Hb (I.sat k I.b₀) := by
        intro l hl
        rw [Lt, I.mem_localTower_iff] at hl
        rw [MulAction.mem_stabilizer_iff, I.sat_smul, eq_comm, I.sat_eq_iff]
        exact ⟨1, by simpa using hl⟩
      exact (sup_le h1 h2) hx
    · intro hx
      rw [I.sat_smul, eq_comm, I.sat_eq_iff] at hx
      obtain ⟨n, hn⟩ := hx
      rw [← I.blk_smul, Set.mem_smul_set_iff_inv_smul_mem, smul_smul] at hn
      have hl : (n : I.Hb)⁻¹ * x ∈ I.Lt k := by
        rw [Lt, I.mem_localTower_iff]; exact hn
      have : x = (n : I.Hb) * ((n : I.Hb)⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right hl)
  rw [relIndex_eq_ncard_orbit _ _ (I.sat k I.b₀) fun x _ => hstab x]
  refine classCount_le_ncard (fun v => I.sat k (I.cB v)) _ ?_ ?_ ?_
  · rintro v ⟨hv, -, hrel⟩
    obtain ⟨c, i, rfl⟩ := I.coords hv
    obtain ⟨n, hn⟩ := (I.upperPart_e k _ _ _ _).1 hrel
    rw [← I.blk_smul, Set.mem_smul_set_iff_inv_smul_mem] at hn
    obtain ⟨h, hh⟩ := I.Hb_transitive htr I.b₀ ((n : I.Hb)⁻¹ • c)
    have hhL : h ∈ I.Lt (k + 1) := by
      rw [Lt, I.mem_localTower_iff, hh]; exact hn
    refine ⟨⟨(n : I.Hb) * h, Subgroup.mul_mem _ (Subgroup.mem_sup_left n.2)
      (Subgroup.mem_sup_right hhL)⟩, ?_⟩
    change ((n : I.Hb) * h) • I.sat k I.b₀ = I.sat k (I.cB (I.e (c, i)))
    rw [I.sat_smul, mul_smul, hh, smul_inv_smul, I.cB_e]
  · rintro v ⟨hv, -, -⟩ w ⟨hw, -, -⟩ hvw
    obtain ⟨c, i, rfl⟩ := I.coords hv
    obtain ⟨d, i', rfl⟩ := I.coords hw
    simp only [I.cB_e]
    rw [I.sat_eq_iff]
    cases k with
    | zero => exact (I.cols_e _ _ _ _).1 hvw
    | succ k => exact (I.upperPart_e k _ _ _ _).1 hvw
  · rintro v ⟨hv, -, -⟩ w ⟨hw, -, -⟩ hvw
    obtain ⟨c, i, rfl⟩ := I.coords hv
    obtain ⟨d, i', rfl⟩ := I.coords hw
    simp only [I.cB_e] at hvw
    rw [I.sat_eq_iff] at hvw
    cases k with
    | zero => exact (I.cols_e _ _ _ _).2 hvw
    | succ k => exact (I.upperPart_e k _ _ _ _).2 hvw

/-! ### The bounds -/

omit [Finite Ω] in
theorem label_of_locRow {j : ℕ} {v w : Ω} (hv : v ∈ S.dom) (hw : w ∈ S.dom)
    (h : (I.locRow j).r v w) : I.label v = I.label w := by
  rw [locRow, State.domKer_r_of_mem _ hv hw] at h
  exact congrArg Prod.fst h

omit [Finite Ω] in
/-- An element that keeps the row of `a` keeps every point of that row in its row. -/
theorem label_keep {u : Perm Ω} (hu : u ∈ S.G) {a w : Ω} (ha : a ∈ S.dom) (hw : w ∈ S.dom)
    (hua : I.label (u a) = I.label a) (hwa : I.label w = I.label a) :
    I.label (u w) = I.label w := by
  have h1 := I.natural.equivariant ⟨u, hu⟩ w hw
  have h2 := I.natural.equivariant ⟨u, hu⟩ a ha
  simp only at h1 h2
  rw [h1, hwa, ← h2, hua]

omit [Finite Ω] in
theorem loc_of_lvl {j : ℕ} (hj : j < I.loc.length) (c d : I.B) (i : Fin L.q) :
    I.loc[j].part.r (I.e (c, i)) (I.e (d, i)) ↔ RowForm.lvl I.e I.i0 I.loc j c d := by
  rw [I.lvl_iff j c d i, I.lvlPart_of_lt hj]

omit [Finite Ω] in
theorem lowerPart_loc {j : ℕ} (hj : j < I.loc.length) {v w : Ω} (hv : v ∈ S.dom)
    (hw : w ∈ S.dom) (h : (I.lowerPart j).r v w) : I.loc[j].part.r v w := by
  obtain ⟨c, i, rfl⟩ := I.coords hv
  obtain ⟨d, i', rfl⟩ := I.coords hw
  obtain ⟨⟨rfl, hl⟩, -⟩ := (I.lowerPart_e j _ _ _ _).1 h
  exact (I.loc_of_lvl hj c d i).2 hl

omit [Finite Ω] in
theorem loc_upperPart {j : ℕ} (hj : j < I.loc.length) {v w : Ω} (hv : v ∈ S.dom)
    (hw : w ∈ S.dom) (h : I.loc[j].part.r v w) : (I.upperPart j).r v w := by
  obtain ⟨c, i, rfl⟩ := I.coords hv
  obtain ⟨d, i', rfl⟩ := I.coords hw
  have hii : i = i' := by
    have := I.loc_low j hj _ (I.e _).2 _ (I.e _).2 h
    rwa [I.e_label, I.e_label] at this
  subst hii
  exact (I.upperPart_e j _ _ _ _).2 ⟨1, by simpa [blk] using (I.loc_of_lvl hj c d i).1 h⟩

omit [Finite Ω] in
/-- The fine ends of the upper pieces ignore the rows and the action of `N`. -/
theorem upFine_smul (j : ℕ) (n : I.Nl) (d : I.B) (i i' : Fin L.q) :
    (I.upFine j).r (I.e (d, i)) (I.e ((n : I.Hb) • d, i')) := by
  cases j with
  | zero => exact (I.cols_e _ _ _ _).2 ⟨n, I.mem_blk_self _ _⟩
  | succ k => exact (I.upperPart_e k _ _ _ _).2 ⟨n, I.mem_blk_self _ _⟩

omit [Finite Ω] in
theorem upFine_row (j : ℕ) (d : I.B) (i i' : Fin L.q) :
    (I.upFine j).r (I.e (d, i)) (I.e (d, i')) := by
  simpa using I.upFine_smul j 1 d i i'

omit [Finite Ω] in
theorem oldFine_upFine (j : ℕ) (hj : j < I.loc.length) {v w : Ω} (hv : v ∈ S.dom)
    (hw : w ∈ S.dom) (h : (fineEnd ⊥ (I.loc.take j)).r v w) : (I.upFine j).r v w := by
  cases j with
  | zero =>
    rw [fineEnd_take_zero] at h
    have : v = w := h
    subst this; exact Setoid.refl' _ _
  | succ k =>
    rw [fineEnd_take_succ _ _ _ (by omega)] at h
    exact I.loc_upperPart (by omega) hv hw h

omit [Finite Ω] in
/-- **The bound of a lower piece** is the old bound of its interval: the lower piece at `a` is a
sub-interval of the old interval at `a`. -/
theorem lower_capAt (j : ℕ) (hj : j < I.loc.length) (a : Ω) (ha : a ∈ S.dom) :
    CapAt S.G S.dom (I.lowFine j) (I.lowerPart j) I.loc[j].cap a := by
  have hsub : ∀ w ∈ classIn S.G S.dom (I.lowerPart j) a, w ∈ classIn S.G S.dom I.loc[j].part a :=
    fun w hw => ⟨hw.1, hw.2.1, I.lowerPart_loc hj ha hw.1 hw.2.2⟩
  refine (I.loc_caps j hj a ha).sub le_rfl (fun u _ hua => hsub _ hua)
    fun u hu hua hfix w hw => ?_
  have h1 := hfix w (hsub w hw)
  cases j with
  | zero => rw [fineEnd_take_zero] at h1; exact h1
  | succ k =>
    rw [fineEnd_take_succ _ _ _ (by omega)] at h1
    have huw : u w ∈ S.dom := (S.dom_inv u hu w).2 hw.1
    have hlab : I.label (u w) = I.label w := by
      refine I.label_keep hu ha hw.1 ?_ ?_
      · exact (I.label_of_locRow ha hua.1 hua.2.2.1).symm
      · exact (I.label_of_locRow ha hw.1 hw.2.2.1).symm
    refine ⟨?_, ?_⟩
    · rw [locRow, State.domKer_r_of_mem _ huw hw.1]
      refine Prod.ext hlab (Quotient.sound ?_)
      change (I.lvlPart k).r (u w) w
      rw [I.lvlPart_of_lt (by omega)]
      exact h1
    · have h2 : I.cols.r (u a) (u w) := (I.cols_inv u hu a w).2 hw.2.2.2
      exact Setoid.trans' _ (Setoid.symm' _ h2)
        (Setoid.trans' _ (Setoid.symm' _ hua.2.2.2) hw.2.2.2)

omit [Finite Ω] in
/-- **The bound of an upper piece** is the old bound of its interval (Lemma A.14): the old
interval at `a` lies in the upper piece at `a`, and every element that keeps the upper class acts
on its fine classes as an element that keeps the old class. The correction uses a pure element,
which moves the rows, and an element of `N`, which moves the old block inside its saturation. -/
theorem upper_capAt (htr : S.Transitive) (j : ℕ) (hj : j < I.loc.length) (a : Ω)
    (ha : a ∈ S.dom) : CapAt S.G S.dom (I.upFine j) (I.upperPart j) I.loc[j].cap a := by
  obtain ⟨c, ia, rfl⟩ := I.coords ha
  refine (I.loc_caps j hj _ ha).transfer S.dom_inv ha (I.loc_inv j hj)
    (onD (I.upperPart_inv j)) (onD (I.upFine_inv j))
    (fun w hw => ⟨hw.1, hw.2.1, I.loc_upperPart hj ha hw.1 hw.2.2⟩) ?_ ?_
  · -- An element that fixes the old fine classes fixes the new ones.
    intro v hv hva hfix w hw
    obtain ⟨d, i, rfl⟩ := I.coords hw.1
    obtain ⟨n, hn⟩ := (I.upperPart_e j _ _ _ _).1 hw.2.2
    have hl : RowForm.lvl I.e I.i0 I.loc j c (((n⁻¹ : I.Nl) : I.Hb) • d) := by
      have := (I.lvl_inv j ((n⁻¹ : I.Nl) : I.Hb).2 ((n : I.Hb) • c) d).2 hn
      simpa [smul_eq, ← Perm.mul_apply] using this
    have hw' : (I.e (((n⁻¹ : I.Nl) : I.Hb) • d, ia) : Ω) ∈ classIn S.G S.dom I.loc[j].part (I.e (c, ia)) :=
      ⟨(I.e _).2, htr _ ha _ (I.e _).2, (I.loc_of_lvl hj _ _ ia).2 hl⟩
    have h1 := I.oldFine_upFine j hj ((S.dom_inv v hv _).2 (I.e _).2) (I.e _).2 (hfix _ hw')
    have h2 : (I.upFine j).r (I.e (d, i)) (I.e (((n⁻¹ : I.Nl) : I.Hb) • d, ia)) :=
      I.upFine_smul j n⁻¹ d i ia
    have h3 := (I.upFine_inv j v hv _ _).2 h2
    exact Setoid.trans' _ h3 (Setoid.trans' _ h1 (Setoid.symm' _ h2))
  · -- The correction.
    intro u hu hua
    have hua' := hua
    obtain ⟨c', i', hc'⟩ := I.coords hua.1
    rw [hc'] at hua'
    obtain ⟨n, hn⟩ := (I.upperPart_e j _ _ _ _).1 hua'.2.2
    obtain ⟨g₁, hg₁, hg₁e⟩ := I.pure_move ia
    obtain ⟨g₂, hg₂, hg₂e⟩ := I.pure_move i'
    obtain ⟨x, hx, hxe⟩ := I.local_move ((n⁻¹ : I.Nl) : I.Hb).2
    have hinv₁ : ∀ d, g₁⁻¹ (I.e (d, ia) : Ω) = I.e (d, I.i0) := fun d => by
      rw [Perm.inv_eq_iff_eq, hg₁e]
    have hinv₂ : ∀ d, g₂⁻¹ (I.e (d, i') : Ω) = I.e (d, I.i0) := fun d => by
      rw [Perm.inv_eq_iff_eq, hg₂e]
    set p := g₁ * g₂⁻¹
    set m := g₁ * x * g₁⁻¹
    have hp : p ∈ S.G := S.G.mul_mem hg₁ (S.G.inv_mem hg₂)
    have hm : m ∈ S.G := S.G.mul_mem (S.G.mul_mem hg₁ hx) (S.G.inv_mem hg₁)
    have hpe : ∀ d, p (I.e (d, i') : Ω) = I.e (d, ia) := fun d => by
      simp only [p, Perm.mul_apply, hinv₂, hg₁e]
    have hme : ∀ d, m (I.e (d, ia) : Ω) =
        I.e ((((n⁻¹ : I.Nl) : I.Hb) : Perm I.B) d, ia) := fun d => by
      simp only [m, Perm.mul_apply, hinv₁, hxe, hg₁e]
    -- `p` and `m` fix every new fine class.
    have hpf : ∀ y ∈ S.dom, (I.upFine j).r (p y) y := by
      intro y hy
      obtain ⟨d, i, rfl⟩ := I.coords hy
      have h1 := (I.upFine_inv j p hp _ _).2 (I.upFine_row j d i i')
      rw [hpe] at h1
      exact Setoid.trans' _ h1 (I.upFine_row j d ia i)
    have hmf : ∀ y ∈ S.dom, (I.upFine j).r (m y) y := by
      intro y hy
      obtain ⟨d, i, rfl⟩ := I.coords hy
      have h1 := (I.upFine_inv j m hm _ _).2 (I.upFine_row j d i ia)
      rw [hme] at h1
      have h2 : (I.upFine j).r (I.e (d, ia)) (I.e (((n⁻¹ : I.Nl) : I.Hb) • d, ia)) :=
        I.upFine_smul j n⁻¹ d ia ia
      rw [smul_eq] at h2
      exact Setoid.trans' _ (Setoid.trans' _ h1 (Setoid.symm' _ h2)) (I.upFine_row j d ia i)
    refine ⟨m * p * u, S.G.mul_mem (S.G.mul_mem hm hp) hu, ?_, fun w hw => ?_⟩
    · have hval : (m * p * u) (I.e (c, ia) : Ω) =
          I.e ((((n⁻¹ : I.Nl) : I.Hb) : Perm I.B) c', ia) := by
        simp only [Perm.mul_apply, hc', hpe, hme]
      rw [hval]
      refine ⟨(I.e _).2, htr _ ha _ (I.e _).2, (I.loc_of_lvl hj _ _ ia).2 ?_⟩
      have := (I.lvl_inv j ((n⁻¹ : I.Nl) : I.Hb).2 ((n : I.Hb) • c) c').2 hn
      simpa [smul_eq, ← Perm.mul_apply] using this
    · have huw : u w ∈ S.dom := (S.dom_inv u hu w).2 hw.1
      have hpw : p (u w) ∈ S.dom := (S.dom_inv p hp _).2 huw
      simp only [Perm.mul_apply]
      exact Setoid.trans' _ (hmf _ hpw) (hpf _ huw)

/-! ### The invariant -/

/-- **The hierarchy invariant after a column step** (Lemma A.14 with the data of
`ColumnStep`): the refactored hierarchy is a tower of block systems from the points to the
domain, with the stored ratios as bounds. -/
theorem hierInv (htr : S.Transitive) : HierInv S.G S.dom I.hier' := by
  have hlen := I.loc_pos
  -- The lower pieces.
  obtain ⟨hlow, hlowEnd⟩ := chain_towerSplit_fst (G := S.G) (D := S.dom) I.Lt I.Nl I.lowerPart
    I.upperPart I.lowFine (fun _ => rfl) 0 I.loc fun k _ _ => by
      refine ⟨onD (I.lowerPart_inv k), fun v hv w hw h => ?_, fun a ha => I.lower_count htr k a ha⟩
      obtain ⟨c, i, rfl⟩ := I.coords hv
      obtain ⟨d, i', rfl⟩ := I.coords hw
      cases k with
      | zero =>
        have : (I.e (c, i) : Ω) = I.e (d, i') := h
        exact this ▸ Setoid.refl' _ _
      | succ k =>
        obtain ⟨⟨hi, hl⟩, hc⟩ := (I.lowerPart_e k _ _ _ _).1 h
        exact (I.lowerPart_e _ _ _ _ _).2 ⟨⟨hi, I.lvl_mono k c d hl⟩, hc⟩
  -- The upper pieces.
  obtain ⟨hup, hupEnd⟩ := chain_towerSplit_snd (G := S.G) (D := S.dom) I.Lt I.Nl I.lowerPart
    I.upperPart I.upFine (fun _ => rfl) 0 I.loc fun k _ _ => by
      refine ⟨onD (I.upperPart_inv k), fun v hv w hw h => ?_, fun a ha => I.upper_count htr k a ha⟩
      obtain ⟨c, i, rfl⟩ := I.coords hv
      obtain ⟨d, i', rfl⟩ := I.coords hw
      cases k with
      | zero => exact (le_sup_right : I.cols ≤ I.upperPart 0) h
      | succ k =>
        obtain ⟨n, hn⟩ := (I.upperPart_e k _ _ _ _).1 h
        exact (I.upperPart_e _ _ _ _ _).2 ⟨n, I.lvl_mono k _ _ hn⟩
  have hlowEnd' : fineEnd ⊥ (I.split.map Prod.fst) = I.lowerPart (I.loc.length - 1) := by
    have : I.lowFine (0 + I.loc.length) = I.lowerPart (I.loc.length - 1) := by
      rw [zero_add]
      obtain ⟨m, hm⟩ : ∃ m, I.loc.length = m + 1 := ⟨I.loc.length - 1, by omega⟩
      rw [hm]; rfl
    rw [← this, ← hlowEnd]; rfl
  have hmidEnd : fineEnd ⊥ (I.split.map Prod.fst ++ [{ I.rowI with part := I.cols }]) = I.cols := by
    rw [fineEnd_append]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hier', chain_append, chain_append, hmidEnd]
    refine ⟨⟨hlow, ?_⟩, hup⟩
    rw [hlowEnd']
    refine ⟨onD I.cols_inv, fun v _ w _ h => (inf_le_right : I.lowerPart _ ≤ I.cols) h,
      fun a _ => ?_, I.rowI_cap, trivial⟩
    change _ ≤ I.rowI.ratio
    rw [I.rowI_ratio]
    exact I.mid_count a
  · rw [hier', fineEnd_append, hmidEnd]
    have : fineEnd I.cols (I.split.map Prod.snd) = I.upperPart (I.loc.length - 1) := by
      have h := hupEnd
      rw [zero_add] at h
      obtain ⟨m, hm⟩ : ∃ m, I.loc.length = m + 1 := ⟨I.loc.length - 1, by omega⟩
      rw [hm] at h ⊢
      exact h
    rw [this]
    intro a ha w hw _
    obtain ⟨c, i, rfl⟩ := I.coords ha
    obtain ⟨d, i', rfl⟩ := I.coords hw
    exact (I.upperPart_e _ _ _ _ _).2 ⟨1, by simpa [blk] using I.lvl_top c d⟩
  · rw [hier', caps_append, caps_append, hmidEnd]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact caps_towerSplit_fst (G := S.G) (D := S.dom) I.Lt I.Nl I.lowerPart I.upperPart
        I.lowFine (fun _ => rfl) 0 I.loc fun i hi a ha => by
          simp only [zero_add]
          exact capAt_min_count (I.lower_capAt i hi a ha) S.dom_inv (onD (I.lowFine_inv i))
            (onD (I.lowerPart_inv i)) (I.lower_count htr i a ha)
    · rw [hlowEnd']
      refine ⟨fun a _ => ?_, trivial⟩
      have hc := capAt_of_count (a := a) S.dom_inv (onD (I.lowerPart_inv _)) (onD I.cols_inv)
        (I.mid_count a)
      by_cases h5 : 5 ≤ L.q
      · change CapAt _ _ _ _ I.rowI.cap a
        rw [I.rowI_cap_eq h5]; exact hc
      · exact hc.of_lt_five (by omega) _
    · exact caps_towerSplit_snd (G := S.G) (D := S.dom) I.Lt I.Nl I.lowerPart I.upperPart
        I.upFine (fun _ => rfl) 0 I.loc fun i hi a ha => by
          simp only [zero_add]
          exact capAt_min_count (I.upper_capAt htr i hi a ha) S.dom_inv (onD (I.upFine_inv i))
            (onD (I.upperPart_inv i)) (I.upper_count htr i a ha)

end ColumnPre

end GI.Algorithm
