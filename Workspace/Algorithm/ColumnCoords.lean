module

public import Workspace.Algorithm.RowSteps
public import Workspace.Algorithm.HierInv
public import Workspace.NormalTransposeOrbits

@[expose] public section

/-!
# The column step in row coordinates

Tools for the hierarchy invariant of the column step (`Workspace/Algorithm/ColumnInv.lean`).
A column step `I : ColumnStep S L` carries clean coordinates `e : B × [q] ≃ dom` and a local
tower inside a row. This file reads its partitions in these coordinates.

* A pure element moves row `i0` to any row `i` without changing the within-row coordinate
  (`pure_move`), so the level-`j` partition of row `i` is the level-`j` partition of row `i0`
  (`lvl_iff`). An element of the local group `H` is the coordinate at `i0` of a blockwise
  element of `G|_dom` (`local_move`), so `H` preserves every level (`lvl_inv`).
* The blocks `blk j c` of a point `c` of a row: `{c}` at `j = 0`, the level-`(j-1)` class
  above. `H` permutes them (`blk_smul`), and `L_j` is the stabilizer of `blk j b₀`
  (`localTower_eq`).
* The `N`-saturations `sat j c = ⋃_{n ∈ N} n • blk j c`. Since `N ◁ H`, `H` permutes them too
  (`sat_smul`).
* The partitions of the refactored hierarchy in coordinates: `rowPart` (the row), `cols` (the
  `N`-orbit), `locRow j` (the row and the level-`j` class), `lowerPart j` (both and the column),
  and `upperPart j` (one `N`-saturation of a level-`j` block, over all rows; `upperPart_iff`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Paper GI.NormalTranspose
open scoped Pointwise

variable {Ω C : Type}

/-! ### Partitions that a group preserves -/

section Inv

variable {G : Subgroup (Perm Ω)}

/-- The meet of two invariant partitions is invariant. -/
theorem setoid_inf_inv {r s : Setoid Ω} (hr : ∀ g ∈ G, ∀ v w, r.r (g v) (g w) ↔ r.r v w)
    (hs : ∀ g ∈ G, ∀ v w, s.r (g v) (g w) ↔ s.r v w) :
    ∀ g ∈ G, ∀ v w, (r ⊓ s).r (g v) (g w) ↔ (r ⊓ s).r v w := by
  intro g hg v w
  exact and_congr (hr g hg v w) (hs g hg v w)

/-- The join of two invariant partitions is invariant. -/
theorem setoid_sup_inv {r s : Setoid Ω} (hr : ∀ g ∈ G, ∀ v w, r.r (g v) (g w) ↔ r.r v w)
    (hs : ∀ g ∈ G, ∀ v w, s.r (g v) (g w) ↔ s.r v w) :
    ∀ g ∈ G, ∀ v w, (r ⊔ s).r (g v) (g w) ↔ (r ⊔ s).r v w := by
  -- One direction for every element of `G`; the other is the same for `g⁻¹`.
  have key : ∀ g ∈ G, r ⊔ s ≤ Setoid.comap g (r ⊔ s) := by
    intro g hg
    refine sup_le (fun v w h => ?_) (fun v w h => ?_)
    · exact (le_sup_left : r ≤ r ⊔ s) ((hr g hg v w).2 h)
    · exact (le_sup_right : s ≤ r ⊔ s) ((hs g hg v w).2 h)
  intro g hg v w
  refine ⟨fun h => ?_, fun h => key g hg h⟩
  have := key g⁻¹ (G.inv_mem hg) h
  change (r ⊔ s).r (g⁻¹ (g v)) (g⁻¹ (g w)) at this
  simpa using this

end Inv

/-! ### Chains read along a tower split -/

section Split

variable {G : Subgroup (Perm Ω)} {D : Set Ω} {H : Type*} [Group H] (Lt : ℕ → Subgroup H)
  (N : Subgroup H) (p₁ p₂ : ℕ → Setoid Ω)

theorem towerSplit_length : ∀ (j : ℕ) (l : List (Interval Ω)),
    (towerSplit Lt N p₁ p₂ j l).length = l.length
  | _, [] => rfl
  | j, _ :: l => by simp [towerSplit, towerSplit_length (j + 1) l]

/-- **The chain of the lower pieces.** If the fine end at `k + 1` is the `k`-th lower coarse
end, and each lower piece satisfies the chain conditions, the lower pieces form a chain. -/
theorem chain_towerSplit_fst (fe : ℕ → Setoid Ω) (hfe : ∀ k, fe (k + 1) = p₁ k) :
    ∀ (j : ℕ) (l : List (Interval Ω)),
      (∀ k, j ≤ k → k < j + l.length →
        (∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, (p₁ k).r (g v) (g w) ↔ (p₁ k).r v w) ∧
        (∀ v ∈ D, ∀ w ∈ D, (fe k).r v w → (p₁ k).r v w) ∧
        (∀ a ∈ D, classCount (fe k) (classIn G D (p₁ k) a) ≤ (Lt k ⊓ N).relIndex (Lt (k + 1) ⊓ N))) →
      Chain G D (fe j) ((towerSplit Lt N p₁ p₂ j l).map Prod.fst) ∧
        fineEnd (fe j) ((towerSplit Lt N p₁ p₂ j l).map Prod.fst) = fe (j + l.length)
  | j, [], _ => ⟨trivial, by simp [towerSplit]⟩
  | j, I :: l, h => by
    obtain ⟨h1, h2, h3⟩ := h j le_rfl (by simp)
    obtain ⟨ih1, ih2⟩ := chain_towerSplit_fst fe hfe (j + 1) l fun k hk1 hk2 =>
      h k (by omega) (by simp; omega)
    refine ⟨⟨h1, h2, h3, min_le_right _ _, ?_⟩, ?_⟩
    · rw [← hfe j]; exact ih1
    · simp only [towerSplit, List.map_cons, fineEnd_cons, List.length_cons]
      rw [← hfe j, ih2]; congr 1; omega

/-- **The chain of the upper pieces**, as for `chain_towerSplit_fst`. -/
theorem chain_towerSplit_snd (fe : ℕ → Setoid Ω) (hfe : ∀ k, fe (k + 1) = p₂ k) :
    ∀ (j : ℕ) (l : List (Interval Ω)),
      (∀ k, j ≤ k → k < j + l.length →
        (∀ g ∈ G, ∀ v ∈ D, ∀ w ∈ D, (p₂ k).r (g v) (g w) ↔ (p₂ k).r v w) ∧
        (∀ v ∈ D, ∀ w ∈ D, (fe k).r v w → (p₂ k).r v w) ∧
        (∀ a ∈ D, classCount (fe k) (classIn G D (p₂ k) a) ≤ (N ⊔ Lt k).relIndex (N ⊔ Lt (k + 1)))) →
      Chain G D (fe j) ((towerSplit Lt N p₁ p₂ j l).map Prod.snd) ∧
        fineEnd (fe j) ((towerSplit Lt N p₁ p₂ j l).map Prod.snd) = fe (j + l.length)
  | j, [], _ => ⟨trivial, by simp [towerSplit]⟩
  | j, I :: l, h => by
    obtain ⟨h1, h2, h3⟩ := h j le_rfl (by simp)
    obtain ⟨ih1, ih2⟩ := chain_towerSplit_snd fe hfe (j + 1) l fun k hk1 hk2 =>
      h k (by omega) (by simp; omega)
    refine ⟨⟨h1, h2, h3, min_le_right _ _, ?_⟩, ?_⟩
    · rw [← hfe j]; exact ih1
    · simp only [towerSplit, List.map_cons, fineEnd_cons, List.length_cons]
      rw [← hfe j, ih2]; congr 1; omega

/-- **The bounds of the lower pieces**, as for `chain_towerSplit_fst`. -/
theorem caps_towerSplit_fst (fe : ℕ → Setoid Ω) (hfe : ∀ k, fe (k + 1) = p₁ k) :
    ∀ (j : ℕ) (l : List (Interval Ω)),
      (∀ (i : ℕ) (hi : i < l.length), CapOK G D (fe (j + i)) (p₁ (j + i))
        (min l[i].cap ((Lt (j + i) ⊓ N).relIndex (Lt (j + i + 1) ⊓ N)))) →
      Caps G D (fe j) ((towerSplit Lt N p₁ p₂ j l).map Prod.fst)
  | _, [], _ => trivial
  | j, I :: l, h => by
    simp only [towerSplit, List.map_cons, Caps]
    have h0 := h 0 (by simp)
    refine ⟨by simpa using h0, ?_⟩
    rw [← hfe j]
    exact caps_towerSplit_fst fe hfe (j + 1) l fun i hi => by
      have := h (i + 1) (by simpa using hi)
      simp only [List.getElem_cons_succ] at this
      rwa [show j + (i + 1) = j + 1 + i by omega] at this

/-- **The bounds of the upper pieces**, as for `chain_towerSplit_snd`. -/
theorem caps_towerSplit_snd (fe : ℕ → Setoid Ω) (hfe : ∀ k, fe (k + 1) = p₂ k) :
    ∀ (j : ℕ) (l : List (Interval Ω)),
      (∀ (i : ℕ) (hi : i < l.length), CapOK G D (fe (j + i)) (p₂ (j + i))
        (min l[i].cap ((N ⊔ Lt (j + i)).relIndex (N ⊔ Lt (j + i + 1))))) →
      Caps G D (fe j) ((towerSplit Lt N p₁ p₂ j l).map Prod.snd)
  | _, [], _ => trivial
  | j, I :: l, h => by
    simp only [towerSplit, List.map_cons, Caps]
    have h0 := h 0 (by simp)
    refine ⟨by simpa using h0, ?_⟩
    rw [← hfe j]
    exact caps_towerSplit_snd fe hfe (j + 1) l fun i hi => by
      have := h (i + 1) (by simpa using hi)
      simp only [List.getElem_cons_succ] at this
      rwa [show j + (i + 1) = j + 1 + i by omega] at this

end Split

/-! ### Counting through a map -/

/-- Classes counted by a map: if `F` is constant on the classes of `f` in `X`, separates
them, and lands in `T`, then `X` meets at most `|T|` classes. -/
theorem classCount_le_ncard {f : Setoid Ω} {X : Set Ω} {β : Type*} [Finite β] (F : Ω → β)
    (T : Set β) (hT : ∀ v ∈ X, F v ∈ T) (hwd : ∀ v ∈ X, ∀ w ∈ X, f.r v w → F v = F w)
    (hinj : ∀ v ∈ X, ∀ w ∈ X, F v = F w → f.r v w) : classCount f X ≤ T.ncard := by
  unfold classCount
  rw [← Nat.card_coe_set_eq]
  let φ : Quotient (Setoid.comap (Subtype.val : X → Ω) f) → T :=
    Quotient.lift (fun v => ⟨F v.1, hT v.1 v.2⟩) fun v w h =>
      Subtype.ext (hwd v.1 v.2 w.1 w.2 h)
  refine Nat.card_le_card_of_injective φ fun a b hab => ?_
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  exact Quotient.sound (hinj _ (Subtype.prop _) _ (Subtype.prop _) (congrArg Subtype.val hab))

/-- A set covered by the classes of `f` in `X`: if every element of `T` is the value of a
map `F` that is constant on the classes, then `|T|` is at most the number of classes. -/
theorem ncard_le_classCount [Finite Ω] {f : Setoid Ω} {X : Set Ω} {β : Type*} (F : Ω → β)
    (T : Set β) (hT : ∀ t ∈ T, ∃ v ∈ X, F v = t)
    (hwd : ∀ v ∈ X, ∀ w ∈ X, f.r v w → F v = F w) : T.ncard ≤ classCount f X := by
  unfold classCount
  let φ : Quotient (Setoid.comap (Subtype.val : X → Ω) f) → β :=
    Quotient.lift (fun v => F v.1) fun v w h => hwd v.1 v.2 w.1 w.2 h
  have hsub : T ⊆ Set.range φ := by
    intro t ht
    obtain ⟨v, hv, rfl⟩ := hT t ht
    exact ⟨Quotient.mk _ ⟨v, hv⟩, rfl⟩
  refine (Set.ncard_le_ncard hsub (Set.finite_range φ)).trans ?_
  rw [← Nat.card_coe_set_eq]
  exact Finite.card_range_le φ

/-- The index of a stabilizer as a relative index: if `A` meets `B` in the stabilizer of `x`,
then `[B : A ∩ B]` is the size of the `B`-orbit of `x`. -/
theorem relIndex_eq_ncard_orbit {H X : Type*} [Group H] [MulAction H X] (A B : Subgroup H)
    (x : X) (hA : ∀ b ∈ B, b ∈ A ↔ b • x = x) :
    A.relIndex B = (MulAction.orbit B x).ncard := by
  have : A.subgroupOf B = MulAction.stabilizer B x := by
    ext b
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, hA b b.2]
    rfl
  rw [Subgroup.relIndex, this, MulAction.index_stabilizer]

/-! ### The column step in coordinates -/

namespace ColumnPre

variable {S : State Ω C} {L : GiantLabels S} (I : ColumnPre S L)

/-- The within-row coordinate of a point of `Ω` (`b₀` off the domain). -/
noncomputable def cB (v : Ω) : I.B := by
  classical
  exact if h : v ∈ S.dom then (I.e.symm ⟨v, h⟩).1 else I.b₀

/-- The row of a point of `Ω` (`i0` off the domain). -/
noncomputable def cI (v : Ω) : Fin L.q := by
  classical
  exact if h : v ∈ S.dom then (I.e.symm ⟨v, h⟩).2 else I.i0

@[simp] theorem cB_e (c : I.B) (i : Fin L.q) : I.cB (I.e (c, i) : Ω) = c := by
  simp [cB, (I.e (c, i)).2]

@[simp] theorem cI_e (c : I.B) (i : Fin L.q) : I.cI (I.e (c, i) : Ω) = i := by
  simp [cI, (I.e (c, i)).2]

theorem eq_e {v : Ω} (hv : v ∈ S.dom) : v = I.e (I.cB v, I.cI v) := by
  simp [cB, cI, hv]

/-- The `H`-action on `B`, as permutations. -/
theorem smul_eq (h : I.Hb) (c : I.B) : h • c = (h : Perm I.B) c := rfl

/-- **A pure element moves row `i0` to row `i`** without changing the within-row
coordinate (Theorem A.17: `s(p)` acts only on the block index). -/
theorem pure_move (i : Fin L.q) : ∃ g ∈ S.G, ∀ c, g (I.e (c, I.i0) : Ω) = I.e (c, i) := by
  haveI : MulAction.IsPretransitive (alternatingGroup (Fin L.q)) (Fin L.q) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin L.q) (by simpa using I.three_le)
  obtain ⟨p, hp⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin L.q)) I.i0 i
  obtain ⟨⟨g, hg⟩, hgp⟩ := (I.s p).2
  refine ⟨g, hg, fun c => ?_⟩
  have h1 := I.pure p c I.i0
  rw [← hgp] at h1
  have h2 := congrArg Subtype.val h1
  rw [State.domHom_apply] at h2
  rw [h2]
  exact congrArg (fun j => (I.e (c, j) : Ω)) hp

/-- **An element of the local group `H` is the row-`i0` coordinate of an element of `G`**
that keeps every row. -/
theorem local_move {h : Perm I.B} (hh : h ∈ I.Hb) :
    ∃ g ∈ S.G, ∀ c, g (I.e (c, I.i0) : Ω) = I.e (h c, I.i0) := by
  obtain ⟨y, hy, rfl⟩ := hh
  obtain ⟨⟨g, hg⟩, hgy⟩ := hy
  refine ⟨g, hg, fun c => ?_⟩
  have h1 := cleanRowPerm_apply I.e y c I.i0
  rw [← hgy] at h1
  have h2 := congrArg Subtype.val h1
  rw [State.domHom_apply] at h2
  exact h2

theorem lvlPart_of_lt {j : ℕ} (h : j < I.loc.length) : I.lvlPart j = I.loc[j].part := dif_pos h

theorem lvlPart_of_ge {j : ℕ} (h : ¬ j < I.loc.length) : I.lvlPart j = ⊤ := dif_neg h

theorem lvl_of_lt {j : ℕ} (h : j < I.loc.length) : RowForm.lvl I.e I.i0 I.loc j =
    Setoid.comap (fun c => (I.e (c, I.i0) : Ω)) I.loc[j].part := dif_pos h

theorem lvl_of_ge {j : ℕ} (h : ¬ j < I.loc.length) : RowForm.lvl I.e I.i0 I.loc j = ⊤ :=
  dif_neg h

/-- The partition of the `j`-th local level is a block system of the domain. -/
theorem lvlPart_inv (j : ℕ) : ∀ g ∈ S.G, ∀ v ∈ S.dom, ∀ w ∈ S.dom,
    (I.lvlPart j).r (g v) (g w) ↔ (I.lvlPart j).r v w := by
  intro g hg v hv w hw
  by_cases h : j < I.loc.length
  · rw [I.lvlPart_of_lt h]; exact I.loc_inv j h g hg v hv w hw
  · rw [I.lvlPart_of_ge h]; exact Iff.rfl

theorem lvl_eq (j : ℕ) (c d : I.B) :
    RowForm.lvl I.e I.i0 I.loc j c d ↔ (I.lvlPart j).r (I.e (c, I.i0)) (I.e (d, I.i0)) := by
  by_cases h : j < I.loc.length
  · rw [I.lvl_of_lt h, I.lvlPart_of_lt h]; exact Iff.rfl
  · rw [I.lvl_of_ge h, I.lvlPart_of_ge h]; exact Iff.rfl

/-- **The levels of all rows agree** (pure elements): the level-`j` partition of row `i` is
that of row `i0`. -/
theorem lvl_iff (j : ℕ) (c d : I.B) (i : Fin L.q) :
    RowForm.lvl I.e I.i0 I.loc j c d ↔ (I.lvlPart j).r (I.e (c, i)) (I.e (d, i)) := by
  obtain ⟨g, hg, hgc⟩ := I.pure_move i
  rw [I.lvl_eq, ← hgc, ← hgc]
  exact (I.lvlPart_inv j g hg _ (I.e _).2 _ (I.e _).2).symm

/-- **`H` preserves every level.** -/
theorem lvl_inv (j : ℕ) {h : Perm I.B} (hh : h ∈ I.Hb) (c d : I.B) :
    RowForm.lvl I.e I.i0 I.loc j (h c) (h d) ↔ RowForm.lvl I.e I.i0 I.loc j c d := by
  obtain ⟨g, hg, hgc⟩ := I.local_move hh
  rw [I.lvl_eq, I.lvl_eq, ← hgc, ← hgc]
  exact I.lvlPart_inv j g hg _ (I.e _).2 _ (I.e _).2

theorem lvl_mono (j : ℕ) (c d : I.B) (h : RowForm.lvl I.e I.i0 I.loc j c d) :
    RowForm.lvl I.e I.i0 I.loc (j + 1) c d := by
  by_cases h1 : j + 1 < I.loc.length
  · rw [I.lvl_of_lt (by omega)] at h
    rw [I.lvl_of_lt h1]
    exact I.loc_mono j h1 _ (I.e _).2 _ (I.e _).2 h
  · rw [I.lvl_of_ge h1]; trivial

/-- The last level holds each row. -/
theorem lvl_top (c d : I.B) : RowForm.lvl I.e I.i0 I.loc (I.loc.length - 1) c d := by
  rw [I.lvl_of_lt (by have := I.loc_pos; omega)]
  exact I.loc_top _ (I.e _).2 _ (I.e _).2 (by rw [I.e_label, I.e_label])

/-! ### Blocks and saturations -/

/-- The block of `c` at level `j`: `{c}` at `j = 0`, the level-`(j-1)` class of `c` above. -/
def blk : ℕ → I.B → Set I.B
  | 0, c => {c}
  | j + 1, c => {d | RowForm.lvl I.e I.i0 I.loc j c d}

theorem mem_blk_self : ∀ (j : ℕ) (c : I.B), c ∈ I.blk j c
  | 0, _ => rfl
  | _ + 1, _ => Setoid.refl' _ _

theorem blk_eq_of_mem : ∀ (j : ℕ) {c d : I.B}, d ∈ I.blk j c → I.blk j d = I.blk j c
  | 0, _, _, h => by simp only [blk, Set.mem_singleton_iff] at h ⊢; rw [h]
  | j + 1, c, d, h => by
    ext x
    simp only [blk, Set.mem_setOf_eq] at h ⊢
    exact ⟨fun hx => Setoid.trans' _ h hx, fun hx => Setoid.trans' _ (Setoid.symm' _ h) hx⟩

theorem blk_eq_iff (j : ℕ) (c d : I.B) : I.blk j c = I.blk j d ↔ d ∈ I.blk j c := by
  constructor
  · intro h; rw [h]; exact I.mem_blk_self j d
  · intro h; exact (I.blk_eq_of_mem j h).symm

/-- **`H` permutes the blocks.** -/
theorem blk_smul (h : I.Hb) : ∀ (j : ℕ) (c : I.B), h • I.blk j c = I.blk j (h • c)
  | 0, c => by simp [blk]
  | j + 1, c => by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [blk, Set.mem_setOf_eq]
    rw [← I.lvl_inv j h.2 c ((h⁻¹ : I.Hb) • x)]
    simp [smul_eq]

/-- `L_j` is the stabilizer of the block of `b₀` at level `j`. -/
theorem localTower_eq : ∀ j, RowForm.localTower I.e I.i0 I.loc I.b₀ j =
    MulAction.stabilizer I.Hb (I.blk j I.b₀)
  | 0 => rfl
  | _ + 1 => rfl

theorem mem_localTower_iff (j : ℕ) (h : I.Hb) :
    h ∈ RowForm.localTower I.e I.i0 I.loc I.b₀ j ↔ h • I.b₀ ∈ I.blk j I.b₀ := by
  rw [localTower_eq, MulAction.mem_stabilizer_iff, I.blk_smul, eq_comm, I.blk_eq_iff]

/-- The `N`-saturation of the block of `c` at level `j`: the union of the blocks of the
`N`-translates of `c`. -/
def sat (j : ℕ) (c : I.B) : Set I.B := {d | ∃ n : I.Nl, d ∈ I.blk j ((n : I.Hb) • c)}

/-- `N` is normal in `H`. -/
theorem conj_mem (h : I.Hb) (n : I.Nl) : h * (n : I.Hb) * h⁻¹ ∈ I.Nl :=
  I.Nl_normal.conj_mem _ n.2 h

/-- **`H` permutes the saturations** (`N ◁ H`). -/
theorem sat_smul (h : I.Hb) (j : ℕ) (c : I.B) : h • I.sat j c = I.sat j (h • c) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨⟨_, I.conj_mem h n⟩, ?_⟩
    have e1 : ((⟨_, I.conj_mem h n⟩ : I.Nl) : I.Hb) • (h • c) = h • ((n : I.Hb) • c) := by
      simp [smul_smul, mul_assoc]
    rw [e1, ← I.blk_smul, Set.mem_smul_set_iff_inv_smul_mem]
    exact hn
  · rintro ⟨n, hn⟩
    have hc : h⁻¹ * (n : I.Hb) * h ∈ I.Nl := by simpa using I.conj_mem h⁻¹ n
    refine ⟨⟨_, hc⟩, ?_⟩
    have e1 : ((⟨_, hc⟩ : I.Nl) : I.Hb) • c = h⁻¹ • ((n : I.Hb) • (h • c)) := by
      simp [smul_smul, mul_assoc]
    rw [e1, ← I.blk_smul]
    exact Set.smul_mem_smul_set hn

theorem mem_sat_self (j : ℕ) (c : I.B) : c ∈ I.sat j c :=
  ⟨1, by simpa using I.mem_blk_self j c⟩

theorem sat_eq_of_mem (j : ℕ) {c d : I.B} (h : d ∈ I.sat j c) : I.sat j d = I.sat j c := by
  obtain ⟨n, hn⟩ := h
  have key : ∀ m : I.Nl, I.blk j ((m : I.Hb) • d) = I.blk j (((m * n : I.Nl) : I.Hb) • c) := by
    intro m
    rw [← I.blk_smul, I.blk_eq_of_mem j hn, I.blk_smul, smul_smul]
    rfl
  ext x
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m * n, by rw [← key]; exact hm⟩
  · rintro ⟨m, hm⟩
    refine ⟨m * n⁻¹, ?_⟩
    rw [key]
    simpa using hm

theorem sat_eq_iff (j : ℕ) (c d : I.B) : I.sat j c = I.sat j d ↔ d ∈ I.sat j c := by
  constructor
  · intro h; rw [h]; exact I.mem_sat_self j d
  · intro h; exact (I.sat_eq_of_mem j h).symm

/-! ### The partitions in coordinates -/

theorem domKer_le {X Y : Type*} {c : S.dom → X} {c' : S.dom → Y}
    (h : ∀ v w : S.dom, c v = c w → c' v = c' w) : S.domKer c ≤ S.domKer c' := by
  classical
  intro x y hxy
  change (if h : x ∈ S.dom then some (c ⟨x, h⟩) else none) =
    (if h : y ∈ S.dom then some (c ⟨y, h⟩) else none) at hxy
  change (if h : x ∈ S.dom then some (c' ⟨x, h⟩) else none) =
    (if h : y ∈ S.dom then some (c' ⟨y, h⟩) else none)
  by_cases hx : x ∈ S.dom <;> by_cases hy : y ∈ S.dom <;>
    simp only [hx, hy, dif_pos, dif_neg, not_false_eq_true, Option.some_inj,
      reduceCtorEq] at hxy ⊢
  exact h _ _ hxy

theorem rowPart_e (c d : I.B) (i i' : Fin L.q) :
    I.rowPart.r (I.e (c, i)) (I.e (d, i')) ↔ i = i' := by
  rw [rowPart, State.domKer_r_of_mem _ (I.e _).2 (I.e _).2]
  simp only [I.e_label]

theorem cols_e (c d : I.B) (i i' : Fin L.q) :
    I.cols.r (I.e (c, i)) (I.e (d, i')) ↔ d ∈ I.sat 0 c := by
  rw [cols, State.domKer_r_of_mem _ (I.e _).2 (I.e _).2]
  simp only [Subtype.coe_eta, colOf_apply]
  rw [Quotient.eq]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n⁻¹, ?_⟩
    change d = n⁻¹ • c
    rw [← hn]
    exact (inv_smul_smul n d).symm
  · rintro ⟨n, hn⟩
    change d = n • c at hn
    exact ⟨n⁻¹, by rw [hn]; exact inv_smul_smul n c⟩

theorem locRow_e (j : ℕ) (c d : I.B) (i i' : Fin L.q) :
    (I.locRow j).r (I.e (c, i)) (I.e (d, i')) ↔ i = i' ∧ RowForm.lvl I.e I.i0 I.loc j c d := by
  rw [locRow, State.domKer_r_of_mem _ (I.e _).2 (I.e _).2]
  simp only [I.e_label, Prod.mk.injEq, Quotient.eq]
  constructor
  · rintro ⟨rfl, h⟩; exact ⟨rfl, (I.lvl_iff j c d i).2 h⟩
  · rintro ⟨rfl, h⟩; exact ⟨rfl, (I.lvl_iff j c d i).1 h⟩

theorem lowerPart_e (j : ℕ) (c d : I.B) (i i' : Fin L.q) :
    (I.lowerPart j).r (I.e (c, i)) (I.e (d, i')) ↔
      (i = i' ∧ RowForm.lvl I.e I.i0 I.loc j c d) ∧ d ∈ I.sat 0 c := by
  rw [← I.locRow_e, ← I.cols_e]
  exact Iff.rfl

theorem upperPart_le (j : ℕ) : I.upperPart j ≤ S.domKer fun v => I.sat (j + 1) (I.cB v) := by
  refine sup_le (domKer_le fun v w h => ?_) (domKer_le fun v w h => ?_)
  · have h0 : (I.locRow j).r v w := by
      rw [locRow, State.domKer_r_of_mem _ v.2 w.2]
      exact h
    rw [I.eq_e v.2, I.eq_e w.2] at h0
    have h' := (I.locRow_e j _ _ _ _).1 h0
    rw [I.sat_eq_iff]
    exact ⟨1, by simpa [blk] using h'.2⟩
  · rw [I.sat_eq_iff]
    have h' := (I.cols_e (I.cB v) (I.cB w) (I.cI v) (I.cI w)).1 (by
      rw [← I.eq_e v.2, ← I.eq_e w.2]
      rw [cols, State.domKer_r_of_mem _ v.2 w.2]
      exact h)
    obtain ⟨n, hn⟩ := h'
    exact ⟨n, by rw [hn]; exact I.mem_blk_self _ _⟩

/-- **The upper coarse end in coordinates**: one `N`-saturation of a level-`j` block, over
all rows. -/
theorem upperPart_e (j : ℕ) (c d : I.B) (i i' : Fin L.q) :
    (I.upperPart j).r (I.e (c, i)) (I.e (d, i')) ↔ d ∈ I.sat (j + 1) c := by
  constructor
  · intro h
    have := I.upperPart_le j h
    rw [State.domKer_r_of_mem _ (I.e _).2 (I.e _).2] at this
    simp only [I.cB_e] at this
    rw [this]
    exact I.mem_sat_self _ _
  · rintro ⟨n, hn⟩
    have h1 : (I.cols).r (I.e (c, i)) (I.e ((n : I.Hb) • c, i')) :=
      (I.cols_e _ _ _ _).2 ⟨n, rfl⟩
    have h2 : (I.locRow j).r (I.e ((n : I.Hb) • c, i')) (I.e (d, i')) :=
      (I.locRow_e _ _ _ _ _).2 ⟨rfl, hn⟩
    exact Setoid.trans' _ ((le_sup_right : I.cols ≤ I.upperPart j) h1)
      ((le_sup_left : I.locRow j ≤ I.upperPart j) h2)

/-! ### Invariance -/

theorem locRow_inv (j : ℕ) : ∀ g ∈ S.G, ∀ v w, (I.locRow j).r (g v) (g w) ↔ (I.locRow j).r v w :=
  State.domKer_inv _ fun g v w h => by
    simp only [Prod.mk.injEq, Quotient.eq] at h ⊢
    refine ⟨?_, ?_⟩
    · rw [State.domHom_apply, State.domHom_apply, I.natural.equivariant g v v.2,
        I.natural.equivariant g w w.2, h.1]
    · rw [State.domHom_apply, State.domHom_apply]
      exact (I.lvlPart_inv j g g.2 v v.2 w w.2).2 h.2

theorem lowerPart_inv (j : ℕ) :
    ∀ g ∈ S.G, ∀ v w, (I.lowerPart j).r (g v) (g w) ↔ (I.lowerPart j).r v w :=
  setoid_inf_inv (I.locRow_inv j) I.cols_inv

theorem upperPart_inv (j : ℕ) :
    ∀ g ∈ S.G, ∀ v w, (I.upperPart j).r (g v) (g w) ↔ (I.upperPart j).r v w :=
  setoid_sup_inv (I.locRow_inv j) I.cols_inv

end ColumnPre

end GI.Algorithm
