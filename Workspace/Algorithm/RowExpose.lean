import Workspace.Algorithm.RowLevels

/-!
# Exposing the row interval: the column step from a row form

Algorithm 4, after the row normal form: "Let `D_1, …, D_t` be the within-row orbits of `L`.
Make column `j` the union of the copies of `D_j` in all rows. Refactor the old hierarchy by
splitting and reordering its interval factors. Inherit every interval bound, clamped by its new
interval ratio." Section 6.2: "In the natural case, the row partition is already an interval of
the retained hierarchy."

The stored hierarchy of a `GiantStep` state is the one kept by the normalization, and its
ratios are upper bounds. So the column step first exposes
the row level in it. With `R` the row partition and `⊥ = f_0 ≤ f_1 ≤ ⋯ ≤ f_t` the stored
levels:

* the local tower inside a row has the levels `f_{k+1} ⊓ R` (`RowForm.expPart`), and its
  ratios are the indices `[L_{k+1} : L_k]` of the block stabilizers in `H`
  (`RowForm.expLoc`), as `ColumnStep` asks;
* the row interval has ratio `q`, and inherits the bound and origin of the stored interval `J`
  at which the levels switch from refining the rows to meeting every row
  (`RowForm.exists_switch`).

`[L_{k+1} : L_k]` is the number of level-`k` blocks of `H` met by the orbit of `L_{k+1}`, at most
the count `u_k` of `f_k ⊓ R`-classes in one `f_{k+1} ⊓ R`-class (`relIndex_le_count`). The
stored ratio `d_k` bounds `t_k`, and `u_k = t_k` for `k ≠ J`, `q u_J = t_J`. So `ρ` and `Q` do
not increase (`exp_rho`, `exp_Q`; Section 7.1: "Splitting a ratio into at least two nontrivial
factors decreases `ρ`. … Splitting or restricting intervals also cannot increase `Q`").

The result is `RowForm.columnStep`: a `ColumnStep` built from a row form with an intransitive
`N`, on a transitive state with the hierarchy invariant. No cited result is used.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Paper GI.NormalTranspose
open scoped Pointwise

variable {Ω C : Type}

/-! ### Facts on lists and sums -/

theorem lvl_congr {S : State Ω C} {L : GiantLabels S} {B : Type} (e : B × Fin L.q ≃ S.dom)
    (i0 : Fin L.q) {l l' : List (Interval Ω)} (hlen : l.length = l'.length)
    (hp : ∀ (j : ℕ) (h : j < l.length) (h' : j < l'.length), l[j].part = l'[j].part) :
    RowForm.lvl e i0 l = RowForm.lvl e i0 l' := by
  funext j
  unfold RowForm.lvl
  by_cases h : j < l.length
  · rw [dif_pos h, dif_pos (hlen ▸ h), hp j h (hlen ▸ h)]
  · rw [dif_neg h, dif_neg (hlen ▸ h)]

theorem localTower_congr {S : State Ω C} {L : GiantLabels S} {B : Type}
    (e : B × Fin L.q ≃ S.dom) (i0 : Fin L.q) {l l' : List (Interval Ω)} (b₀ : B)
    (h : RowForm.lvl e i0 l = RowForm.lvl e i0 l') :
    RowForm.localTower e i0 l b₀ = RowForm.localTower e i0 l' b₀ := by
  funext j
  cases j with
  | zero => rfl
  | succ j =>
    show MulAction.stabilizer _ {c | RowForm.lvl e i0 l j b₀ c} =
      MulAction.stabilizer _ {c | RowForm.lvl e i0 l' j b₀ c}
    rw [h]

/-- A sum with one term split off: `Σ a_k + b ≤ Σ c_k` from `a_k ≤ c_k` for `k ≠ J` and
`a_J + b ≤ c_J`. -/
theorem sum_switch_le {t : ℕ} (a c : Fin t → ℝ) (b : ℝ) (J : Fin t) (h1 : ∀ k, k ≠ J → a k ≤ c k)
    (h2 : a J + b ≤ c J) : (∑ k, a k) + b ≤ ∑ k, c k := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ J), ← Finset.add_sum_erase _ c (Finset.mem_univ J)]
  have : ∑ k ∈ Finset.univ.erase J, a k ≤ ∑ k ∈ Finset.univ.erase J, c k :=
    Finset.sum_le_sum fun k hk => h1 k (Finset.ne_of_mem_erase hk)
  linarith

/-! ### The local levels of the exposed tower -/

namespace ColumnPre

variable {S : State Ω C} {L : GiantLabels S} (I : ColumnPre S L)

theorem blk_sub : ∀ (j : ℕ), I.blk j I.b₀ ⊆ I.blk (j + 1) I.b₀
  | 0 => by
    intro d hd
    simp only [blk, Set.mem_singleton_iff] at hd
    subst hd
    exact I.mem_blk_self 1 _
  | j + 1 => fun _ hd => I.lvl_mono j _ _ hd

/-- **The local tower is a chain.** -/
theorem localTower_mono (j : ℕ) : RowForm.localTower I.e I.i0 I.loc I.b₀ j ≤
    RowForm.localTower I.e I.i0 I.loc I.b₀ (j + 1) := by
  intro x hx
  rw [I.mem_localTower_iff] at hx ⊢
  exact I.blk_sub j hx

end ColumnPre

namespace RowForm

variable {S : State Ω C} {L : GiantLabels S} (F : RowForm S L)

/-- The `k`-th local level of the exposed tower: the stored level `f_{k+1}` inside the rows. -/
noncomputable def expPart (k : ℕ) : Setoid Ω := levOf ⊥ S.hier (k + 1) ⊓ F.rowPart

/-- The local levels, without ratios. -/
noncomputable def expParts : List (Interval Ω) :=
  List.ofFn fun k : Fin S.hier.length => ⟨F.expPart k, 0, 0, 0⟩

/-- The ratio of the `k`-th local interval: the index of the block stabilizers. -/
noncomputable def expRatio (b₀ : F.B) (k : ℕ) : ℕ :=
  (localTower F.e F.i0 F.expParts b₀ k).relIndex (localTower F.e F.i0 F.expParts b₀ (k + 1))

/-- **The local tower of the exposed hierarchy**: the levels `f_{k+1} ⊓ R`, the stabilizer
indices as ratios, and the stored bounds and origins. The column step clamps the bounds of the
pieces it makes from these intervals (`towerSplit`). -/
noncomputable def expLoc (b₀ : F.B) : List (Interval Ω) :=
  List.ofFn fun k : Fin S.hier.length =>
    ⟨F.expPart k, F.expRatio b₀ k, S.hier[k].cap, S.hier[k].origin⟩

@[simp] theorem expLoc_length (b₀ : F.B) : (F.expLoc b₀).length = S.hier.length := by
  simp [expLoc]

theorem expLoc_part (b₀ : F.B) (k : ℕ) (hk : k < (F.expLoc b₀).length) :
    (F.expLoc b₀)[k].part = F.expPart k := by
  simp [expLoc]

theorem expLoc_ratio (b₀ : F.B) (k : ℕ) (hk : k < (F.expLoc b₀).length) :
    (F.expLoc b₀)[k].ratio = F.expRatio b₀ k := by
  simp [expLoc]

theorem expLoc_cap (b₀ : F.B) (k : ℕ) (hk : k < (F.expLoc b₀).length) :
    (F.expLoc b₀)[k].cap = (S.hier[k]'(by simpa using hk)).cap := by
  simp [expLoc]

theorem lvl_expLoc (b₀ : F.B) : lvl F.e F.i0 (F.expLoc b₀) = lvl F.e F.i0 F.expParts :=
  lvl_congr _ _ (by simp [expParts]) fun j h h' => by simp [expLoc, expParts]

include F in
/-- The stored hierarchy is not empty: its last level holds the domain, which has two points
in different rows. -/
theorem hier_pos (htr : S.Transitive) (hinv : S.HierInv) (hne : S.dom.Nonempty) :
    0 < S.hier.length := by
  by_contra h0
  have hnil : S.hier = [] := List.eq_nil_of_length_eq_zero (by omega)
  have htop := hinv.top
  rw [hnil] at htop
  obtain ⟨a, ha⟩ := hne
  have h0 : (0 : ℕ) < L.q := by have := F.four_le; omega
  have h1 : (1 : ℕ) < L.q := by have := F.four_le; omega
  set b := (F.e.symm ⟨a, ha⟩).1
  have hv := (F.e (b, ⟨0, h0⟩)).2
  have hw := (F.e (b, ⟨1, h1⟩)).2
  have := htop _ hv _ hw (htr _ hv _ hw)
  change ((F.e (b, ⟨0, h0⟩) : Ω)) = F.e (b, ⟨1, h1⟩) at this
  rw [Subtype.coe_inj, F.e.apply_eq_iff_eq, Prod.mk.injEq, Fin.mk.injEq] at this
  omega

variable [Finite Ω]

/-- **The data of the exposed tower** (`ColumnPre`), for a base point `b₀` and the switch `J`. -/
noncomputable def columnPre (hint : 2 ≤ Nat.card (Quotient (MulAction.orbitRel F.Nl F.B)))
    (htr : S.Transitive) (hinv : S.HierInv) (hne : S.dom.Nonempty) (J : ℕ) (hJ : J < S.hier.length)
    (hJcap : 5 ≤ L.q → L.q ≤ S.hier[J].cap) (b₀ : F.B) :
    ColumnPre S L where
  toRowForm := F
  intransitive := hint
  loc := F.expLoc b₀
  rowI := ⟨⊤, L.q, min S.hier[J].cap L.q, S.hier[J].origin⟩
  rowI_ratio := rfl
  rowI_cap := min_le_right _ _
  loc_inv j hj := by
    rw [F.expLoc_part]
    exact F.inf_rowPart_inv (levOf_inv hinv (j + 1))
  loc_mono j hj v hv w hw h := by
    rw [F.expLoc_part] at h ⊢
    have hj' : j + 1 < S.hier.length := by simpa using hj
    exact ⟨levOf_mono hinv (j + 1) hj' v hv w hw h.1, h.2⟩
  loc_pos := by rw [expLoc_length]; exact F.hier_pos htr hinv hne
  loc_top v hv w hw h := by
    have hl := F.hier_pos htr hinv hne
    have hlen : (F.expLoc b₀).length - 1 + 1 = S.hier.length := by simp; omega
    rw [F.expLoc_part]
    unfold expPart
    rw [hlen]
    exact ⟨levOf_top hinv hl v hv w hw (htr v hv w hw), (F.rowPart_iff hv hw).2 h⟩
  loc_low j hj v hv w hw h := by
    rw [F.expLoc_part] at h
    exact (F.rowPart_iff hv hw).1 h.2
  loc_caps j hj a ha := by
    have hinv' : HierInv S.G S.dom S.hier := hinv
    have hj' : j < S.hier.length := by simpa using hj
    have hold := caps_getElem ⊥ S.hier hinv'.caps j hj' a ha
    rw [F.expLoc_part, F.expLoc_cap]
    unfold expPart
    rw [levOf_succ_of_lt hj']
    refine hold.sub le_rfl (fun u _ hua => ⟨hua.1, hua.2.1, hua.2.2.1⟩)
      fun u hu hua hfix w hw => ?_
    have h1 := hfix w ⟨hw.1, hw.2.1, hw.2.2.1⟩
    cases j with
    | zero => rw [fineEnd_take_zero] at h1 ⊢; exact h1
    | succ k =>
      rw [fineEnd_take_succ _ _ _ (by omega)] at h1
      rw [fineEnd_take_succ _ _ k (by simp at hj ⊢; omega), F.expLoc_part]
      unfold expPart
      rw [levOf_succ_of_lt (by omega)]
      have huw : u w ∈ S.dom := (S.dom_inv u hu w).2 hw.1
      refine ⟨h1, (F.rowPart_iff huw hw.1).2 ?_⟩
      have e1 := F.natural.equivariant ⟨u, hu⟩ w hw.1
      have e2 := F.natural.equivariant ⟨u, hu⟩ a ha
      have hwa := (F.rowPart_iff ha hw.1).1 hw.2.2.2
      have hua' := (F.rowPart_iff ha hua.1).1 hua.2.2.2
      simp only at e1 e2
      rw [e1, ← hwa, ← e2, ← hua']
  rowI_cap_eq hq := min_eq_right (hJcap hq)
  b₀ := b₀

/-- **A local ratio is at most the count of the meets** (orbit–stabilizer): the blocks met by
the orbit of `L_{k+1}` are level-`k` blocks inside one `f_{k+1} ⊓ R`-class. -/
theorem relIndex_le_count (hint : 2 ≤ Nat.card (Quotient (MulAction.orbitRel F.Nl F.B)))
    (htr : S.Transitive) (hinv : S.HierInv) (hne : S.dom.Nonempty) (J : ℕ) (hJ : J < S.hier.length)
    (hJcap : 5 ≤ L.q → L.q ≤ S.hier[J].cap) (b₀ : F.B) (k : ℕ) (hk : k < S.hier.length) :
    F.expRatio b₀ k ≤ classCount (levOf ⊥ S.hier k ⊓ F.rowPart)
      (classIn S.G S.dom (levOf ⊥ S.hier (k + 1) ⊓ F.rowPart) (F.e (b₀, F.i0))) := by
  set I := F.columnPre hint htr hinv hne J hJ hJcap b₀
  haveI : Finite I.B := Finite.of_injective (fun c => I.e (c, I.i0)) fun c d h => by
    simpa using h
  have hT : localTower F.e F.i0 F.expParts b₀ = localTower I.e I.i0 I.loc I.b₀ :=
    (localTower_congr _ _ _ (F.lvl_expLoc b₀)).symm
  have hlvl : ∀ (c d : I.B), lvl I.e I.i0 I.loc k c d ↔
      (levOf ⊥ S.hier (k + 1) ⊓ F.rowPart).r (F.e (c, F.i0)) (F.e (d, F.i0)) := by
    intro c d
    rw [I.lvl_eq, I.lvlPart_of_lt (by simpa [I, columnPre] using hk)]
    change ((F.expLoc b₀)[k]'(by simpa using hk)).part.r _ _ ↔ _
    rw [F.expLoc_part]
    rfl
  have hR : F.expRatio b₀ k = (localTower I.e I.i0 I.loc I.b₀ k).relIndex
      (localTower I.e I.i0 I.loc I.b₀ (k + 1)) := by
    unfold expRatio; rw [hT]; rfl
  change _ ≤ classCount (levOf ⊥ S.hier k ⊓ F.rowPart)
      (classIn S.G S.dom (levOf ⊥ S.hier (k + 1) ⊓ F.rowPart) (I.e (I.b₀, I.i0)))
  rw [hR, relIndex_eq_ncard_orbit _ _ (I.blk k I.b₀) fun x _ => by
    rw [I.localTower_eq, MulAction.mem_stabilizer_iff]]
  refine ncard_le_classCount (fun v => I.blk k (I.cB v)) _ ?_ ?_
  · rintro Z ⟨x, rfl⟩
    have hx := (I.mem_localTower_iff (k + 1) x).1 x.2
    have hv := (I.e ((x : I.Hb) • I.b₀, I.i0)).2
    refine ⟨I.e ((x : I.Hb) • I.b₀, I.i0), ⟨hv, htr _ (I.e _).2 _ hv, ?_⟩, ?_⟩
    · exact ((hlvl _ _).1 hx)
    · simp only [I.cB_e]
      exact (I.blk_smul (x : I.Hb) k I.b₀).symm
  · rintro v ⟨hv, -, hv'⟩ w ⟨hw, -, hw'⟩ hvw
    obtain ⟨c, i, rfl⟩ := I.coords hv
    obtain ⟨d, i', rfl⟩ := I.coords hw
    simp only [I.cB_e]
    have hi : i = I.i0 := by
      have h1 := (F.rowPart_iff (I.e _).2 (I.e _).2).1 hv'.2
      have h2 : F.label (I.e (c, i)) = i := F.e_label c i
      have h3 : F.label (I.e (I.b₀, I.i0)) = I.i0 := F.e_label _ _
      exact h2.symm.trans (h1.symm.trans h3)
    have hi' : i' = I.i0 := by
      have h1 := (F.rowPart_iff (I.e _).2 (I.e _).2).1 hw'.2
      have h2 : F.label (I.e (d, i')) = i' := F.e_label d i'
      have h3 : F.label (I.e (I.b₀, I.i0)) = I.i0 := F.e_label _ _
      exact h2.symm.trans (h1.symm.trans h3)
    subst hi hi'
    cases k with
    | zero =>
      have : (I.e (c, I.i0) : Ω) = I.e (d, I.i0) := hvw.1
      rw [Subtype.coe_inj, I.e.apply_eq_iff_eq, Prod.mk.injEq] at this
      rw [this.1]
    | succ k =>
      have hlvl' : lvl I.e I.i0 I.loc k c d := by
        rw [I.lvl_eq, I.lvlPart_of_lt (by simp [I, columnPre]; omega)]
        change ((F.expLoc b₀)[k]'(by simp; omega)).part.r _ _
        rw [F.expLoc_part]
        exact hvw
      exact (I.blk_eq_iff _ _ _).2 hlvl'

omit [Finite Ω] in
/-- **The switch interval has bound at least `q`** (Section 7.2: "The old cap is at least `q`
because the selected alternating section belongs to that whole constituent"). Below the switch
the levels refine the rows, and above it each class meets every row. So an element that keeps
a class of the switch interval and fixes each of its fine classes fixes every row, and the
stabilizer of the class maps onto `Alt(q)`. -/
theorem le_cap_of_switch (htr : S.Transitive) (hinv : S.HierInv) {J : ℕ} (hJ : J < S.hier.length)
    (hlow : F.Low (levOf ⊥ S.hier J)) (hhigh : F.High (levOf ⊥ S.hier (J + 1)))
    (hq : 5 ≤ L.q) {a : Ω} (ha : a ∈ S.dom) : L.q ≤ S.hier[J].cap := by
  have hinv' : HierInv S.G S.dom S.hier := hinv
  have hcap := caps_getElem ⊥ S.hier hinv'.caps J hJ a ha
  rw [← levOf_eq_fineEnd _ _ _ hJ.le] at hcap
  rw [levOf_succ_of_lt hJ] at hhigh
  refine le_of_capAt hcap S.dom_inv (chain_getElem _ _ hinv'.chain J hJ).1 ha L.π L.π_surj hq
    (fun g => ?_) (fun g hga hfix => ?_)
  · have hga : (g : Perm Ω) a ∈ S.dom := (S.dom_inv g g.2 a).2 ha
    obtain ⟨w, hw, haw, hlab⟩ := hhigh a ha (F.label ((g : Perm Ω) a))
    obtain ⟨k, hk, hkw⟩ := (F.natural.fibers _ hga w hw).1 hlab.symm
    refine ⟨k, hk, ?_⟩
    show (k : Perm Ω) ((g : Perm Ω) a) ∈ _
    rw [hkw]
    exact ⟨hw, htr a ha w hw, haw⟩
  · apply Subtype.ext
    apply Equiv.ext
    intro i
    obtain ⟨w, hw, haw, hlab⟩ := hhigh a ha i
    have h1 := hfix w ⟨hw, htr a ha w hw, haw⟩
    have hgw : (g : Perm Ω) w ∈ S.dom := (S.dom_inv g g.2 w).2 hw
    have h2 := hlow _ hgw w hw h1
    rw [F.natural.equivariant g w hw, hlab] at h2
    exact h2

/-- The base point of the local tower: any column of the (nonempty) domain. -/
noncomputable def baseB (hne : S.dom.Nonempty) : F.B := (F.e.symm ⟨hne.some, hne.some_mem⟩).1

/-- **The stored counts bound the exposed counts.** With `J` the switch of `exists_switch` at
the base point, each local ratio is at most the stored ratio, and at `J` the local ratio and
the row ratio `q` together fit in the stored ratio. -/
theorem exposed_counts (hint : 2 ≤ Nat.card (Quotient (MulAction.orbitRel F.Nl F.B)))
    (htr : S.Transitive) (hinv : S.HierInv) (hne : S.dom.Nonempty) :
    ∃ J < S.hier.length, (5 ≤ L.q → ∀ h : J < S.hier.length, L.q ≤ (S.hier[J]'h).cap) ∧
      ∀ (k : ℕ) (hk : k < S.hier.length),
      (k ≠ J → F.expRatio (F.baseB hne) k ≤ S.hier[k].ratio) ∧
      (k = J → ∃ u, 1 ≤ u ∧ F.expRatio (F.baseB hne) k ≤ u ∧ u * L.q ≤ S.hier[k].ratio) := by
  set b₀ := F.baseB hne
  set a : Ω := (F.e (b₀, F.i0) : Ω)
  have ha : a ∈ S.dom := (F.e _).2
  have hl := F.hier_pos htr hinv hne
  have hinv' : HierInv S.G S.dom S.hier := hinv
  obtain ⟨J, hJ, hlowJ, hhighJ, hsw⟩ := F.exists_switch htr hinv hl ha
  have hJcap : 5 ≤ L.q → L.q ≤ S.hier[J].cap := fun hq =>
    F.le_cap_of_switch htr hinv hJ hlowJ hhighJ hq ha
  refine ⟨J, hJ, fun hq _ => hJcap hq, fun k hk => ⟨fun hkJ => ?_, fun hkJ => ?_⟩⟩
  · have h1 := F.relIndex_le_count hint htr hinv hne J hJ hJcap b₀ k hk
    have h2 := (chain_getElem _ _ hinv'.chain k hk).2.2.1 a ha
    rw [← levOf_succ_of_lt hk] at h2
    rw [(hsw k hk).1 hkJ] at h1
    exact h1.trans h2
  · refine ⟨_, ?_, F.relIndex_le_count hint htr hinv hne J hJ hJcap b₀ k hk, ?_⟩
    · exact one_le_classCount _ ⟨a, ha, htr a ha a ha, Setoid.refl' _ _⟩
    · have h2 := (chain_getElem _ _ hinv'.chain k hk).2.2.1 a ha
      rw [← levOf_succ_of_lt hk] at h2
      rw [(hsw k hk).2 hkJ]
      exact h2

theorem logTerm_mono {cap e u : ℕ} (h : e ≤ u) :
    Real.log e * Real.log (max (min cap e) 2 : ℕ) ≤ Real.log u * Real.log (max (min cap u) 2 : ℕ) := by
  have hlog : Real.log e ≤ Real.log u := by
    rcases Nat.eq_zero_or_pos e with he | he
    · rw [he, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg u
    · exact Real.log_le_log (by exact_mod_cast he) (by exact_mod_cast h)
  have hcap : Real.log (max (min cap e) 2 : ℕ) ≤ Real.log (max (min cap u) 2 : ℕ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast max_le_max (min_le_min le_rfl h) le_rfl
  exact mul_le_mul hlog hcap (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

theorem logTerm_le {cap e d : ℕ} (h : e ≤ d) :
    Real.log e * Real.log (max (min cap e) 2 : ℕ) ≤ Real.log d * Real.log (max cap 2 : ℕ) := by
  have hlog : Real.log e ≤ Real.log d := by
    rcases Nat.eq_zero_or_pos e with he | he
    · rw [he, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg d
    · exact Real.log_le_log (by exact_mod_cast he) (by exact_mod_cast h)
  have hcap : Real.log (max (min cap e) 2 : ℕ) ≤ Real.log (max cap 2 : ℕ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast max_le_max (min_le_left _ _) le_rfl
  exact mul_le_mul hlog hcap (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

theorem logTerm_le' {cap e d : ℕ} (h : e ≤ d) :
    Real.log e * Real.log (max cap 2 : ℕ) ≤ Real.log d * Real.log (max cap 2 : ℕ) := by
  have hlog : Real.log e ≤ Real.log d := by
    rcases Nat.eq_zero_or_pos e with he | he
    · rw [he, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg d
    · exact Real.log_le_log (by exact_mod_cast he) (by exact_mod_cast h)
  exact mul_le_mul_of_nonneg_right hlog (Real.log_natCast_nonneg _)

theorem log_switch_le {cap e u q d : ℕ} (heu : e ≤ u) (hu : 1 ≤ u) (hq : 1 ≤ q)
    (huq : u * q ≤ d) :
    Real.log e * Real.log (max cap 2 : ℕ) + Real.log q * Real.log (max (min cap q) 2 : ℕ) ≤
      Real.log d * Real.log (max cap 2 : ℕ) := by
  have hL : Real.log (max (min cap q) 2 : ℕ) ≤ Real.log (max cap 2 : ℕ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast max_le_max (min_le_left _ _) le_rfl
  have hL0 : 0 ≤ Real.log (max (min cap q) 2 : ℕ) := Real.log_natCast_nonneg _
  have hq0 := Real.log_natCast_nonneg q
  have he : Real.log e ≤ Real.log u := by
    rcases Nat.eq_zero_or_pos e with he | he
    · rw [he, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg u
    · exact Real.log_le_log (by exact_mod_cast he) (by exact_mod_cast heu)
  have hsum : Real.log u + Real.log q ≤ Real.log d := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    exact_mod_cast huq
  have hLc : 0 ≤ Real.log (max cap 2 : ℕ) := Real.log_natCast_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hL hq0
  nlinarith

/-- **The column step from a row form** (Algorithm 4, the intransitive case). The retained tower
is the stored hierarchy inside the rows, followed by the row interval of ratio `q`. -/
noncomputable def columnStep (hint : 2 ≤ Nat.card (Quotient (MulAction.orbitRel F.Nl F.B)))
    (htr : S.Transitive) (hinv : S.HierInv) (hne : S.dom.Nonempty) : ColumnStep S L :=
  let hJ := F.exposed_counts hint htr hinv hne
  let J := Classical.choose hJ
  have hJl : J < S.hier.length := (Classical.choose_spec hJ).1
  have hsw := (Classical.choose_spec hJ).2.2
  let P := F.columnPre hint htr hinv hne J hJl (fun hq => (Classical.choose_spec hJ).2.1 hq hJl)
    (F.baseB hne)
  { toColumnPre := P
    exp_rho := by
      show State.hierRho (F.expLoc (F.baseB hne) ++ [⟨⊤, L.q, min S.hier[J].cap L.q,
        S.hier[J].origin⟩]) ≤ State.hierRho S.hier
      rw [hierRho_append]
      simp only [State.hierRho, expLoc, List.map_ofFn, List.sum_ofFn, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, Function.comp_def]
      rw [← Fin.sum_univ_fun_getElem]
      apply sum_switch_le _ _ _ ⟨J, hJl⟩
      · intro k hk
        have := (hsw k k.2).1 (fun h => hk (Fin.ext h))
        exact_mod_cast GI.tower_rank_mono this
      · obtain ⟨u, hu1, heu, huq⟩ := (hsw J hJl).2 rfl
        have h1 := GI.tower_rank_mono heu
        have h2 := towerRank_split_le hu1 (show 2 ≤ L.q by have := F.four_le; omega) huq
        push_cast
        exact_mod_cast (by linarith : GI.towerRank (F.expRatio (F.baseB hne) J) +
          GI.towerRank L.q ≤ GI.towerRank S.hier[J].ratio)
    exp_Q := by
      show State.hierQ (F.expLoc (F.baseB hne) ++ [⟨⊤, L.q, min S.hier[J].cap L.q,
        S.hier[J].origin⟩]) ≤ State.hierQ S.hier
      rw [hierQ_append]
      simp only [State.hierQ, expLoc, List.map_ofFn, List.sum_ofFn, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, Function.comp_def]
      rw [← Fin.sum_univ_fun_getElem]
      apply sum_switch_le _ _ _ ⟨J, hJl⟩
      · intro k hk
        exact logTerm_le' ((hsw k k.2).1 (fun h => hk (Fin.ext h)))
      · obtain ⟨u, hu1, heu, huq⟩ := (hsw J hJl).2 rfl
        have h2 := log_switch_le (cap := S.hier[J].cap) heu hu1
          (show 1 ≤ L.q by have := F.four_le; omega) huq
        simp only [Fin.getElem_fin]
        linarith
    tower_mono := P.localTower_mono
    tower_ratio := fun j hj => by
      show (F.expLoc (F.baseB hne))[j].ratio = _
      rw [F.expLoc_ratio]
      unfold expRatio
      rw [localTower_congr _ _ _ (F.lvl_expLoc (F.baseB hne)).symm]
      rfl }

end RowForm

end GI.Algorithm
