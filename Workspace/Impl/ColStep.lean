import Workspace.Algorithm.RowExpose

/-!
# The column step at a chosen switch and base point

`RowForm.columnStep` (`Workspace/Algorithm/RowExpose.lean`) builds a `ColumnStep` from a row form
with an intransitive `N`. It picks the switch `J` by `Classical.choose` and the base point
`b₀` by `Set.Nonempty.some`, so a program cannot follow it. This file builds the same column step
for any switch and any base point (`colStep`):

* a *switch* is an index `J` of the stored hierarchy whose level `J` refines the rows (`Low`)
  and whose level `J + 1` meets every row (`High`). A program finds it as the first index whose
  next level does not refine the rows. Below the switch every level is low, above it every level
  is high, so the counts of `exists_switch` hold at every point (`colSwitch_counts`);
* the base point is any coordinate of a row.

The data that the child of the column step stores are then fixed by the state, the row form and
these two choices. Section "Ratios as counts" turns the stored ratios (indices of block
stabilizers) into counts of blocks that a program computes from partition labels:

* `[L_{k+1} : L_k]` is the number of level-`k` blocks in the level-`(k+1)` block of `b₀`
  (`colRatio_eq`, using that `H` is transitive on a row);
* `[L_{k+1} ∩ N : L_k ∩ N]` is the number of level-`k` blocks met by the points of the
  `N`-orbit of `b₀` in the level-`(k+1)` block of `b₀` (`colLower_eq`).

The upper ratio is the quotient of the two (eq. `modular-index-split`).
-/

namespace GI.Impl

open GI.Algorithm GI.Paper Equiv Equiv.Perm
open scoped Pointwise

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

namespace Col

variable (F : RowForm S L)

/-- The levels are nested, over several steps. -/
theorem colLev_le {G : Subgroup (Perm Ω)} {D : Set Ω} {l : List (Interval Ω)} (h : HierInv G D l)
    {k J : ℕ} (hkJ : k ≤ J) (hJ : J ≤ l.length) :
    ∀ v ∈ D, ∀ w ∈ D, (levOf ⊥ l k).r v w → (levOf ⊥ l J).r v w := by
  induction J, hkJ using Nat.le_induction with
  | base => exact fun _ _ _ _ h => h
  | succ J hk ih =>
    intro v hv w hw hvw
    exact levOf_mono h J (by omega) v hv w hw (ih (by omega) v hv w hw hvw)

/-- **The counts at a switch.** If level `J` refines the rows and level `J + 1` meets every row,
then intersecting with the rows keeps the counts `t_k` for `k ≠ J`, and `u_J q = t_J`. -/
theorem colSwitch_counts [Finite Ω] (htr : S.Transitive) (hinv : S.HierInv) {J : ℕ}
    (hJlt : J < S.hier.length) (hlowJ : F.Low (levOf ⊥ S.hier J))
    (hJ : F.High (levOf ⊥ S.hier (J + 1))) {a : Ω} (ha : a ∈ S.dom) :
    ∀ k < S.hier.length,
      (k ≠ J → classCount (levOf ⊥ S.hier k ⊓ F.rowPart)
          (classIn S.G S.dom (levOf ⊥ S.hier (k + 1) ⊓ F.rowPart) a) =
        classCount (levOf ⊥ S.hier k) (classIn S.G S.dom (levOf ⊥ S.hier (k + 1)) a)) ∧
      (k = J → classCount (levOf ⊥ S.hier k ⊓ F.rowPart)
          (classIn S.G S.dom (levOf ⊥ S.hier (k + 1) ⊓ F.rowPart) a) * L.q =
        classCount (levOf ⊥ S.hier k) (classIn S.G S.dom (levOf ⊥ S.hier (k + 1)) a)) := by
  set l := S.hier
  have hinv' : HierInv S.G S.dom l := hinv
  have hinvk := levOf_inv hinv'
  have hlow : ∀ k, k ≤ J → F.Low (levOf ⊥ l k) := by
    intro k hk v hv w hw hvw
    exact hlowJ v hv w hw (colLev_le hinv' hk hJlt.le v hv w hw hvw)
  have hhigh : ∀ k, J + 1 ≤ k → k ≤ l.length → F.High (levOf ⊥ l k) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; exact hJ
    | succ k hk ih =>
      intro hkl
      exact F.high_mono (ih (by omega)) (levOf_mono hinv' k (by omega))
  refine fun k hk => ⟨fun hkJ => ?_, fun hkJ => ?_⟩
  · have step := F.level_step (hinvk k) htr (hinvk (k + 1)) (levOf_mono hinv' k hk) ha
    rcases Nat.lt_or_gt_of_ne hkJ with h | h
    · exact step.1 (hlow k (by omega)) (hlow (k + 1) (by omega))
    · exact step.2.2 (hhigh k (by omega) (by omega)) (hhigh (k + 1) (by omega) (by omega))
  · subst hkJ
    exact (F.level_step (hinvk k) htr (hinvk (k + 1)) (levOf_mono hinv' k hk) ha).2.1
      (hlow k le_rfl) hJ

/-- **The stored counts bound the exposed counts**, at any base point and any switch
(`RowForm.exposed_counts` for the chosen ones). -/
theorem colExposed_counts [Finite Ω] (hint : 2 ≤ Nat.card (Quotient (MulAction.orbitRel F.Nl F.B)))
    (htr : S.Transitive) (hinv : S.HierInv) (hne : S.dom.Nonempty) (b₀ : F.B) {J : ℕ}
    (hJl : J < S.hier.length) (hlowJ : F.Low (levOf ⊥ S.hier J))
    (hhighJ : F.High (levOf ⊥ S.hier (J + 1))) :
    (5 ≤ L.q → L.q ≤ S.hier[J].cap) ∧
      ∀ (k : ℕ) (hk : k < S.hier.length),
      (k ≠ J → F.expRatio b₀ k ≤ S.hier[k].ratio) ∧
      (k = J → ∃ u, 1 ≤ u ∧ F.expRatio b₀ k ≤ u ∧ u * L.q ≤ S.hier[k].ratio) := by
  set a : Ω := (F.e (b₀, F.i0) : Ω)
  have ha : a ∈ S.dom := (F.e _).2
  have hinv' : HierInv S.G S.dom S.hier := hinv
  have hsw := colSwitch_counts F htr hinv hJl hlowJ hhighJ ha
  have hJcap : 5 ≤ L.q → L.q ≤ S.hier[J].cap := fun hq =>
    F.le_cap_of_switch htr hinv hJl hlowJ hhighJ hq ha
  refine ⟨hJcap, fun k hk => ⟨fun hkJ => ?_, fun hkJ => ?_⟩⟩
  · have h1 := F.relIndex_le_count hint htr hinv hne J hJl hJcap b₀ k hk
    have h2 := (chain_getElem _ _ hinv'.chain k hk).2.2.1 a ha
    rw [← levOf_succ_of_lt hk] at h2
    rw [(hsw k hk).1 hkJ] at h1
    exact h1.trans h2
  · refine ⟨_, ?_, F.relIndex_le_count hint htr hinv hne J hJl hJcap b₀ k hk, ?_⟩
    · exact one_le_classCount _ ⟨a, ha, htr a ha a ha, Setoid.refl' _ _⟩
    · have h2 := (chain_getElem _ _ hinv'.chain k hk).2.2.1 a ha
      rw [← levOf_succ_of_lt hk] at h2
      rw [(hsw k hk).2 hkJ]
      exact h2

/-- **The column step at the switch `J` and the base point `b₀`.** The same construction as
`RowForm.columnStep`, with the two choices as parameters. -/
noncomputable def colStep [Finite Ω] (hint : 2 ≤ Nat.card (Quotient (MulAction.orbitRel F.Nl F.B)))
    (htr : S.Transitive) (hinv : S.HierInv) (hne : S.dom.Nonempty) (b₀ : F.B) (J : ℕ)
    (hJl : J < S.hier.length) (hlowJ : F.Low (levOf ⊥ S.hier J))
    (hhighJ : F.High (levOf ⊥ S.hier (J + 1))) : ColumnStep S L :=
  have hc := colExposed_counts F hint htr hinv hne b₀ hJl hlowJ hhighJ
  have hsw := hc.2
  let P := F.columnPre hint htr hinv hne J hJl hc.1 b₀
  { toColumnPre := P
    exp_rho := by
      show State.hierRho (F.expLoc b₀ ++ [⟨⊤, L.q, min S.hier[J].cap L.q,
        S.hier[J].origin⟩]) ≤ State.hierRho S.hier
      rw [hierRho_append]
      simp only [State.hierRho, RowForm.expLoc, List.map_ofFn, List.sum_ofFn, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero, Function.comp_def]
      rw [← Fin.sum_univ_fun_getElem]
      apply sum_switch_le _ _ _ ⟨J, hJl⟩
      · intro k hk
        have := (hsw k k.2).1 (fun h => hk (Fin.ext h))
        exact_mod_cast GI.tower_rank_mono this
      · obtain ⟨u, hu1, heu, huq⟩ := (hsw J hJl).2 rfl
        have h1 := GI.tower_rank_mono heu
        have h2 := towerRank_split_le hu1 (show 2 ≤ L.q by have := F.four_le; omega) huq
        push_cast
        exact_mod_cast (by linarith : GI.towerRank (F.expRatio b₀ J) +
          GI.towerRank L.q ≤ GI.towerRank S.hier[J].ratio)
    exp_Q := by
      show State.hierQ (F.expLoc b₀ ++ [⟨⊤, L.q, min S.hier[J].cap L.q,
        S.hier[J].origin⟩]) ≤ State.hierQ S.hier
      rw [hierQ_append]
      simp only [State.hierQ, RowForm.expLoc, List.map_ofFn, List.sum_ofFn, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero, Function.comp_def]
      rw [← Fin.sum_univ_fun_getElem]
      apply sum_switch_le _ _ _ ⟨J, hJl⟩
      · intro k hk
        exact RowForm.logTerm_le' ((hsw k k.2).1 (fun h => hk (Fin.ext h)))
      · obtain ⟨u, hu1, heu, huq⟩ := (hsw J hJl).2 rfl
        have h2 := RowForm.log_switch_le (cap := S.hier[J].cap) heu hu1
          (show 1 ≤ L.q by have := F.four_le; omega) huq
        simp only [Fin.getElem_fin]
        linarith
    tower_mono := P.localTower_mono
    tower_ratio := fun j hj => by
      show (F.expLoc b₀)[j].ratio = _
      rw [F.expLoc_ratio]
      unfold RowForm.expRatio
      rw [localTower_congr _ _ _ (F.lvl_expLoc b₀).symm]
      rfl }

end Col

end GI.Impl

/-! ### Ratios as counts -/

namespace GI.Impl

open GI.Algorithm GI.Paper Equiv Equiv.Perm
open scoped Pointwise

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

namespace Col

variable (I : ColumnPre S L)

theorem colOrbit_eq (A : Subgroup I.Hb) (k : ℕ) :
    MulAction.orbit A (I.blk k I.b₀) =
      I.blk k '' {c | ∃ a : A, ((a : I.Hb) • I.b₀) = c} := by
  ext X
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, (I.blk_smul (a : I.Hb) k I.b₀).symm⟩
  · rintro ⟨c, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, I.blk_smul (a : I.Hb) k I.b₀⟩

/-- **A local ratio is a count of blocks**: `[L_{k+1} : L_k]` is the number of level-`k` blocks
in the level-`(k+1)` block of `b₀`. `L_{k+1}` is transitive on that block because `H` is
transitive on the row (`ColumnPre.Hb_transitive`) and permutes the blocks. -/
theorem colRatio_eq (htr : S.Transitive) (k : ℕ) :
    (RowForm.localTower I.e I.i0 I.loc I.b₀ k).relIndex
        (RowForm.localTower I.e I.i0 I.loc I.b₀ (k + 1)) =
      (I.blk k '' I.blk (k + 1) I.b₀).ncard := by
  rw [relIndex_eq_ncard_orbit _ _ (I.blk k I.b₀) fun x _ => by
    rw [I.localTower_eq, MulAction.mem_stabilizer_iff], colOrbit_eq]
  congr 2
  ext c
  constructor
  · rintro ⟨a, rfl⟩
    exact (I.mem_localTower_iff (k + 1) a).1 a.2
  · intro hc
    obtain ⟨h, rfl⟩ := I.Hb_transitive htr I.b₀ c
    exact ⟨⟨h, (I.mem_localTower_iff (k + 1) h).2 hc⟩, rfl⟩

/-- **A lower ratio is a count of blocks**: `[L_{k+1} ∩ N : L_k ∩ N]` is the number of level-`k`
blocks met by the points of the `N`-orbit of `b₀` that lie in the level-`(k+1)` block of
`b₀`. -/
theorem colLower_eq (k : ℕ) :
    (RowForm.localTower I.e I.i0 I.loc I.b₀ k ⊓ I.Nl).relIndex
        (RowForm.localTower I.e I.i0 I.loc I.b₀ (k + 1) ⊓ I.Nl) =
      (I.blk k '' {c | (∃ n : I.Nl, (n : I.Hb) • I.b₀ = c) ∧ c ∈ I.blk (k + 1) I.b₀}).ncard := by
  rw [relIndex_eq_ncard_orbit _ _ (I.blk k I.b₀) fun x hx => by
    rw [Subgroup.mem_inf, I.localTower_eq, MulAction.mem_stabilizer_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, (Subgroup.mem_inf.1 hx).2⟩⟩, colOrbit_eq]
  congr 2
  ext c
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨⟨⟨a, (Subgroup.mem_inf.1 a.2).2⟩, rfl⟩,
      (I.mem_localTower_iff (k + 1) a).1 (Subgroup.mem_inf.1 a.2).1⟩
  · rintro ⟨⟨n, rfl⟩, hc⟩
    exact ⟨⟨n, Subgroup.mem_inf.2 ⟨(I.mem_localTower_iff (k + 1) n).2 hc, n.2⟩⟩, rfl⟩

/-- **An upper ratio is a quotient** (eq. `modular-index-split`). -/
theorem colUpper_eq (k : ℕ) :
    (I.Nl ⊔ RowForm.localTower I.e I.i0 I.loc I.b₀ k).relIndex
        (I.Nl ⊔ RowForm.localTower I.e I.i0 I.loc I.b₀ (k + 1)) =
      (RowForm.localTower I.e I.i0 I.loc I.b₀ k).relIndex
          (RowForm.localTower I.e I.i0 I.loc I.b₀ (k + 1)) /
        (RowForm.localTower I.e I.i0 I.loc I.b₀ k ⊓ I.Nl).relIndex
          (RowForm.localTower I.e I.i0 I.loc I.b₀ (k + 1) ⊓ I.Nl) := by
  rw [GI.Paper.eq_modular_index_split I.Nl (I.localTower_mono k)]
  rw [Nat.mul_div_cancel_left _ (relIndex_pos_of_finite _ _)]

/-! ### The child partitions as fibers -/

theorem colDomKer_iff {X : Type*} (c : S.dom → X) (v w : Ω) :
    (S.domKer c).r v w ↔ (∃ (hv : v ∈ S.dom) (hw : w ∈ S.dom), c ⟨v, hv⟩ = c ⟨w, hw⟩) ∨
      (v ∉ S.dom ∧ w ∉ S.dom) := by
  classical
  change (if h : v ∈ S.dom then some (c ⟨v, h⟩) else none) =
      (if h : w ∈ S.dom then some (c ⟨w, h⟩) else none) ↔ _
  by_cases hv : v ∈ S.dom <;> by_cases hw : w ∈ S.dom <;>
    simp [hv, hw]

/-- The meet of two fiber partitions is the fiber partition of the pair. -/
theorem colDomKer_inf {X Y : Type*} (c : S.dom → X) (c' : S.dom → Y) :
    S.domKer c ⊓ S.domKer c' = S.domKer fun v => (c v, c' v) := by
  ext v w
  change (S.domKer c).r v w ∧ (S.domKer c').r v w ↔ (S.domKer fun v => (c v, c' v)).r v w
  simp only [colDomKer_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hv, hw, h⟩ | h, h' | h'⟩
    · obtain ⟨_, _, h'⟩ := h'; exact Or.inl ⟨hv, hw, h, h'⟩
    · exact absurd hv h'.1
    · obtain ⟨hv, -⟩ := h'; exact absurd hv h.1
    · exact Or.inr h
  · rintro (⟨hv, hw, h, h'⟩ | h)
    · exact ⟨Or.inl ⟨hv, hw, h⟩, Or.inl ⟨hv, hw, h'⟩⟩
    · exact ⟨Or.inr h, Or.inr h⟩

/-- **The upper coarse end is a fiber partition**: the `N`-saturation of the level-`(k+1)` block
of the row coordinate. -/
theorem colUpper_domKer (k : ℕ) :
    I.upperPart k = S.domKer fun v => I.sat (k + 1) (I.cB v) := by
  refine le_antisymm (I.upperPart_le k) fun v w h => ?_
  rcases (colDomKer_iff _ v w).1 h with ⟨hv, hw, hvw⟩ | ⟨hv, hw⟩
  · rw [I.eq_e hv, I.eq_e hw, I.upperPart_e]
    have : I.cB w ∈ I.sat (k + 1) (I.cB w) := I.mem_sat_self _ _
    simp only at hvw
    rwa [← hvw] at this
  · refine (le_sup_left : I.locRow k ≤ I.upperPart k) ?_
    exact (colDomKer_iff _ v w).2 (Or.inr ⟨hv, hw⟩)

/-! ### Blocks read from labels -/

/-- **Counting blocks by labels.** If `d ∈ blkF c` exactly when `g c = g d`, the blocks of the
points of `T` are as many as the labels of the points of `T`. -/
theorem colNcard_image {B : Type*} (blkF : B → Set B) (g : B → ℕ)
    (hg : ∀ c d, d ∈ blkF c ↔ g c = g d) (T : Set B) : (blkF '' T).ncard = (g '' T).ncard := by
  have hF : blkF = (fun n => {d | n = g d}) ∘ g := by
    funext c; ext d; exact hg c d
  rw [hF, Set.image_comp]
  refine Set.InjOn.ncard_image ?_
  rintro _ ⟨c, -, rfl⟩ _ ⟨c', -, rfl⟩ h
  have : c' ∈ {d | g c' = g d} := rfl
  simp only at h
  rw [← h] at this
  exact this

/-- At level `0` the block is the point. -/
theorem colBlk_zero (c d : I.B) : d ∈ I.blk 0 c ↔ c = d := by
  simp only [ColumnPre.blk, Set.mem_singleton_iff]
  exact eq_comm

/-- Above level `0` the block is a class of the local level, read in row `i0`. -/
theorem colBlk_succ (k : ℕ) (hk : k < I.loc.length) (c d : I.B) :
    d ∈ I.blk (k + 1) c ↔ I.loc[k].part.r (I.e (c, I.i0)) (I.e (d, I.i0)) := by
  show RowForm.lvl I.e I.i0 I.loc k c d ↔ _
  rw [I.lvl_of_lt hk]
  rfl

/-! ### The child partitions from keys

A program describes a partition by a key of each point (an orbit label, a level label, a row
label). These lemmas say which keys give the partitions of the column step. -/

theorem colDomKer_congr {X Y : Type*} (c₁ : S.dom → X) (c₂ : S.dom → Y)
    (h : ∀ v w : S.dom, c₁ v = c₁ w ↔ c₂ v = c₂ w) : S.domKer c₁ = S.domKer c₂ := by
  ext v w
  change (S.domKer c₁).r v w ↔ (S.domKer c₂).r v w
  rw [colDomKer_iff, colDomKer_iff]
  constructor
  · rintro (⟨hv, hw, e⟩ | h')
    · exact Or.inl ⟨hv, hw, (h _ _).1 e⟩
    · exact Or.inr h'
  · rintro (⟨hv, hw, e⟩ | h')
    · exact Or.inl ⟨hv, hw, (h _ _).2 e⟩
    · exact Or.inr h'

theorem colCB_dom (v : S.dom) : I.cB (v : Ω) = (I.e.symm v).1 := by
  simp [ColumnPre.cB, v.2]

/-- **The columns from orbit labels**: a key of the row coordinate that is constant exactly on
the `N`-orbits. -/
theorem colCols_key (g : I.B → ℕ) (hg : ∀ c d, g c = g d ↔ ∃ n : I.Nl, (n : I.Hb) • c = d) :
    I.cols = S.domKer fun v => g (I.cB v) := by
  unfold ColumnPre.cols
  refine colDomKer_congr _ _ fun v w => ?_
  rw [colCB_dom, colCB_dom, hg]
  simp only [GI.NormalTranspose.colOf]
  rw [Quotient.eq]
  change (I.e.symm v).1 ∈ MulAction.orbit I.Nl (I.e.symm w).1 ↔ _
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n⁻¹, ?_⟩
    rw [← hn]
    exact inv_smul_smul n _
  · rintro ⟨n, hn⟩
    refine ⟨n⁻¹, ?_⟩
    change (n⁻¹ : I.Nl) • (I.e.symm w).1 = _
    rw [← hn]
    exact inv_smul_smul n _

/-- **The upper parts from saturation keys.** -/
theorem colUpper_key (k : ℕ) (g : I.B → ℕ) (hg : ∀ c d, g c = g d ↔ d ∈ I.sat (k + 1) c) :
    I.upperPart k = S.domKer fun v => g (I.cB v) := by
  rw [colUpper_domKer]
  exact colDomKer_congr _ _ fun v w => by rw [hg, I.sat_eq_iff]

end Col

namespace Col

variable (F : RowForm S L)

/-- **The lower parts from keys**, for the column step at `J` and `b₀`: the row label, a label
of the stored level `k + 1`, and a key of the column. -/
theorem colLower_key [Finite Ω] (hint : 2 ≤ Nat.card (Quotient (MulAction.orbitRel F.Nl F.B)))
    (htr : S.Transitive) (hinv : S.HierInv) (hne : S.dom.Nonempty) (b₀ : F.B) (J : ℕ)
    (hJl : J < S.hier.length) (hlowJ : F.Low (levOf ⊥ S.hier J))
    (hhighJ : F.High (levOf ⊥ S.hier (J + 1))) {k : ℕ} (hk : k < S.hier.length)
    (hl : Ω → ℕ) (hhl : ∀ v w, S.hier[k].part.r v w ↔ hl v = hl w)
    (g : F.B → ℕ) (hg : ∀ c d, g c = g d ↔ ∃ n : F.Nl, (n : F.Hb) • c = d) :
    (colStep F hint htr hinv hne b₀ J hJl hlowJ hhighJ).lowerPart k =
      S.domKer fun v => ((F.label v : ℕ), hl v,
        g ((colStep F hint htr hinv hne b₀ J hJl hlowJ hhighJ).cB v)) := by
  set I := (colStep F hint htr hinv hne b₀ J hJl hlowJ hhighJ).toColumnPre
  have hloc : I.loc = F.expLoc b₀ := rfl
  have hkl : k < I.loc.length := by rw [hloc, RowForm.expLoc_length]; exact hk
  unfold ColumnPre.lowerPart ColumnPre.locRow
  rw [colCols_key I g hg, colDomKer_inf]
  refine colDomKer_congr _ _ fun v w => ?_
  simp only [Prod.mk.injEq]
  have hlab : (I.label v = I.label w) ↔ ((F.label v : ℕ) = F.label w) := by
    change F.label v = F.label w ↔ _
    exact Fin.val_inj.symm
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨hlab.1 h1, ?_, h3⟩
    have h2' := Quotient.exact h2
    change I.lvlPart k v w at h2'
    rw [I.lvlPart_of_lt hkl] at h2'
    change ((F.expLoc b₀)[k]'(by simpa using hk)).part.r v w at h2'
    rw [F.expLoc_part] at h2'
    unfold RowForm.expPart at h2'
    rw [levOf_succ_of_lt hk] at h2'
    exact (hhl v w).1 h2'.1
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨hlab.2 h1, Quotient.sound ?_⟩, h3⟩
    change I.lvlPart k v w
    rw [I.lvlPart_of_lt hkl]
    change ((F.expLoc b₀)[k]'(by simpa using hk)).part.r v w
    rw [F.expLoc_part]
    unfold RowForm.expPart
    rw [levOf_succ_of_lt hk]
    exact ⟨(hhl v w).2 h2, (F.rowPart_iff v.2 w.2).2 (Fin.val_inj.1 h1)⟩

/-- **The switch found by a scan**: if the levels `1, …, J` refine the rows and level `J + 1`
does not, then `J` is a switch (a block system of a transitive domain that does not refine the
rows meets every row, `RowForm.low_or_high`). -/
theorem colSwitch_of_first (htr : S.Transitive) (hinv : S.HierInv) {J : ℕ}
    (hbelow : ∀ k < J, F.Low (levOf ⊥ S.hier (k + 1)))
    (hJ : ¬ F.Low (levOf ⊥ S.hier (J + 1))) :
    F.Low (levOf ⊥ S.hier J) ∧ F.High (levOf ⊥ S.hier (J + 1)) := by
  have hinv' : HierInv S.G S.dom S.hier := hinv
  refine ⟨?_, (F.low_or_high (levOf_inv hinv' (J + 1)) htr).resolve_left hJ⟩
  cases J with
  | zero => exact F.low_bot
  | succ k => exact hbelow k (by omega)

/-- The scan stops inside the hierarchy: its last level holds the domain, which meets two
rows, so it does not refine the rows. -/
theorem colLast_not_low (htr : S.Transitive) (hinv : S.HierInv) (hl : 0 < S.hier.length)
    (hne : S.dom.Nonempty) : ¬ F.Low (levOf ⊥ S.hier S.hier.length) := by
  intro hlow
  have hinv' : HierInv S.G S.dom S.hier := hinv
  obtain ⟨a, ha⟩ := hne
  have h0 : (0 : ℕ) < L.q := by have := F.four_le; omega
  have h1 : (1 : ℕ) < L.q := by have := F.four_le; omega
  set b := (F.e.symm ⟨a, ha⟩).1
  have hv := (F.e (b, ⟨0, h0⟩)).2
  have hw := (F.e (b, ⟨1, h1⟩)).2
  have := hlow _ hv _ hw (levOf_top hinv' hl _ hv _ hw (htr _ hv _ hw))
  rw [F.e_label, F.e_label, Fin.mk.injEq] at this
  omega

end Col

end GI.Impl
