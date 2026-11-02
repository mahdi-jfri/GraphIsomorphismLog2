import Workspace.Impl.ColElem

/-!
# The switch test, read from labels

The program finds the switch of the column step as the first stored level that does not refine
the rows (`Col.colSwitch_of_first`). It tests a level on one class only: the class of a point
`p00` of row `0`. This is enough because of the dichotomy `RowForm.low_or_high`: a block system
of a transitive domain either refines the rows or has every class meeting every row. So the
level refines the rows exactly when no domain point of the class of `p00` lies off row `0`
(`colLow_iff`). The program's test is `colLowQ` on all positions (`colLowQ_all`).
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm

variable {Ω C : Type} {n : ℕ} {S : State Ω C} {L : GiantLabels S}

/-- **The switch test.** Let `labs` label the classes of a `G`-invariant partition `f`, `dv` be
the indicator of the domain, `rl` give the row of each domain point, and `p00` be a domain point
of row `0`. Then `f` refines the rows exactly when every domain point in the class of `p00` has
row label `0`. -/
theorem colLow_iff (F : RowForm S L) (htr : S.Transitive) (e : Ω ≃ Fin n) {f : Setoid Ω}
    (hf : ∀ g ∈ S.G, ∀ v ∈ S.dom, ∀ w ∈ S.dom, f.r (g v) (g w) ↔ f.r v w)
    (labs dv rl : Fin n → ℕ) (hlabs : ∀ i j, labs i = labs j ↔ f.r (e.symm i) (e.symm j))
    (hdv : ∀ i, dv i ≠ 0 ↔ e.symm i ∈ S.dom)
    (hrl : ∀ i, e.symm i ∈ S.dom → rl i = (F.label (e.symm i) : ℕ))
    (p00 : Fin n) (hp0 : e.symm p00 ∈ S.dom) (hp0r : (F.label (e.symm p00) : ℕ) = 0) :
    F.Low f ↔ ∀ i : Fin n, ¬ (dv i ≠ 0 ∧ labs i = labs p00 ∧ rl i ≠ 0) := by
  constructor
  · rintro hlow i ⟨hi, hlab, hr⟩
    have hd := (hdv i).1 hi
    have hrel : f.r (e.symm i) (e.symm p00) := (hlabs i p00).1 hlab
    have := hlow _ hd _ hp0 hrel
    rw [hrl i hd, this, hp0r] at hr
    exact hr rfl
  · intro h
    rcases F.low_or_high hf htr with hl | hh
    · exact hl
    · exfalso
      have hq : 1 < L.q := by have := F.four_le; omega
      obtain ⟨w, hw, hvw, hwl⟩ := hh _ hp0 ⟨1, hq⟩
      refine h (e w) ⟨(hdv _).2 (by simpa using hw), ?_, ?_⟩
      · rw [hlabs]
        simpa using Setoid.symm' _ hvw
      · rw [hrl _ (by simpa using hw)]
        simp [hwl]

/-- The program's value of the test is `0` exactly when the level refines the rows. -/
theorem colNotLowv_eq_zero_iff (F : RowForm S L) (htr : S.Transitive) (e : Ω ≃ Fin n)
    {len : ℕ} (labs : Fin len → Fin n → ℕ) (k : Fin len) {f : Setoid Ω}
    (hf : ∀ g ∈ S.G, ∀ v ∈ S.dom, ∀ w ∈ S.dom, f.r (g v) (g w) ↔ f.r v w)
    (dv rl : Fin n → ℕ) (hlabs : ∀ i j, labs k i = labs k j ↔ f.r (e.symm i) (e.symm j))
    (hdv : ∀ i, dv i ≠ 0 ↔ e.symm i ∈ S.dom)
    (hrl : ∀ i, e.symm i ∈ S.dom → rl i = (F.label (e.symm i) : ℕ))
    (p00 : Fin n) (hp0 : e.symm p00 ∈ S.dom) (hp0r : (F.label (e.symm p00) : ℕ) = 0) :
    colNotLowv labs dv rl p00 k = 0 ↔ F.Low f := by
  rw [colLow_iff F htr e hf (labs k) dv rl hlabs hdv hrl p00 hp0 hp0r, ← colLowQ_all]
  unfold colNotLowv
  split_ifs with h <;> simp [h]

/-! ### The upper key: the least orbit label in a block

The `N`-saturation of the level-`(k+1)` block of `c` is a union of `N`-orbits, and an orbit lies
in it exactly when it meets the block of `c` (`N` permutes the blocks). So the least orbit label
over the block of `c` is a key of the saturation (`colSatKey`). The program computes this least
label with `colMinv`, with the roles of the two label functions swapped. -/

namespace Col

variable (I : ColumnPre S L)

/-- A point of the saturation of `c` has the orbit label of some point of the block of `c`. -/
theorem colSat_orbit (j : ℕ) (ol : I.B → ℕ)
    (hol : ∀ c d, ol c = ol d ↔ ∃ n : I.Nl, (n : I.Hb) • c = d) {c o : I.B}
    (ho : o ∈ I.sat j c) : ∃ o' ∈ I.blk j c, ol o' = ol o := by
  obtain ⟨n, hn⟩ := ho
  rw [← I.blk_smul, Set.mem_smul_set_iff_inv_smul_mem] at hn
  exact ⟨_, hn, (hol _ _).2 ⟨n, by simp⟩⟩

/-- **The least orbit label in the block is a key of the saturation.** -/
theorem colSatKey (j : ℕ) (ol g : I.B → ℕ)
    (hol : ∀ c d, ol c = ol d ↔ ∃ n : I.Nl, (n : I.Hb) • c = d)
    (hmin : ∀ d, (∃ o ∈ I.blk j d, ol o = g d) ∧ ∀ o ∈ I.blk j d, g d ≤ ol o) (c d : I.B) :
    g c = g d ↔ d ∈ I.sat j c := by
  have hblk_sat : ∀ c o, o ∈ I.blk j c → o ∈ I.sat j c := fun c o h => ⟨1, by simpa using h⟩
  -- `g c ≤ g d` whenever `d` lies in the saturation of `c`.
  have hle : ∀ c d, d ∈ I.sat j c → g c ≤ g d := by
    intro c d hd
    obtain ⟨⟨o, ho, hog⟩, -⟩ := hmin d
    have ho' : o ∈ I.sat j c := by
      rw [← I.sat_eq_of_mem j hd]; exact hblk_sat d o ho
    obtain ⟨o', ho'b, ho'l⟩ := colSat_orbit I j ol hol ho'
    calc g c ≤ ol o' := (hmin c).2 o' ho'b
      _ = g d := by rw [ho'l, hog]
  constructor
  · intro h
    obtain ⟨⟨o1, ho1, h1⟩, -⟩ := hmin c
    obtain ⟨⟨o2, ho2, h2⟩, -⟩ := hmin d
    obtain ⟨n, hn⟩ := (hol o1 o2).1 (by rw [h1, h2, h])
    -- `o2 = n • o1` lies in the saturation of `c` and in that of `d`.
    have hc : o2 ∈ I.sat j c := by
      obtain ⟨m, hm⟩ := hblk_sat c o1 ho1
      refine ⟨n * m, ?_⟩
      rw [← hn, Subgroup.coe_mul, mul_smul, ← I.blk_smul]
      exact Set.smul_mem_smul_set hm
    have hd : o2 ∈ I.sat j d := hblk_sat d o2 ho2
    rw [← I.sat_eq_iff, ← I.sat_eq_of_mem j hc, I.sat_eq_of_mem j hd]
  · intro h
    have h' : c ∈ I.sat j d := by
      rw [I.sat_eq_of_mem j h]; exact I.mem_sat_self j c
    exact le_antisymm (hle c d h) (hle d c h')

/-! ### Ratios as counts of labels -/

/-- **The local ratio as a count of labels**: `A` labels the level-`k` blocks and `bl` the
level-`(k+1)` blocks. -/
theorem colRatio_labels (htr : S.Transitive) (k : ℕ) (A bl : I.B → ℕ)
    (hA : ∀ c d, d ∈ I.blk k c ↔ A c = A d) (hbl : ∀ c d, d ∈ I.blk (k + 1) c ↔ bl c = bl d) :
    (RowForm.localTower I.e I.i0 I.loc I.b₀ k).relIndex
        (RowForm.localTower I.e I.i0 I.loc I.b₀ (k + 1)) =
      (A '' {c | bl c = bl I.b₀}).ncard := by
  rw [colRatio_eq I htr, colNcard_image _ A hA]
  congr 2
  ext c
  rw [hbl, eq_comm]
  rfl

/-- **The lower ratio as a count of labels**: as `colRatio_labels`, over the points of the
level-`(k+1)` block of `b₀` with the orbit label `ol` of `b₀`. -/
theorem colLower_labels (k : ℕ) (A bl ol : I.B → ℕ)
    (hA : ∀ c d, d ∈ I.blk k c ↔ A c = A d) (hbl : ∀ c d, d ∈ I.blk (k + 1) c ↔ bl c = bl d)
    (hol : ∀ c d, ol c = ol d ↔ ∃ n : I.Nl, (n : I.Hb) • c = d) :
    (RowForm.localTower I.e I.i0 I.loc I.b₀ k ⊓ I.Nl).relIndex
        (RowForm.localTower I.e I.i0 I.loc I.b₀ (k + 1) ⊓ I.Nl) =
      (A '' {c | bl c = bl I.b₀ ∧ ol c = ol I.b₀}).ncard := by
  rw [colLower_eq I, colNcard_image _ A hA]
  congr 2
  ext c
  simp only [Set.mem_setOf_eq]
  rw [hbl, ← hol, eq_comm (a := bl c), eq_comm (a := ol c), and_comm]

end Col

namespace Col

variable (F : RowForm S L)

/-- **The blocks above level `0` from hierarchy labels**: a label `lab` of the stored level `k`
reads the level-`(k+1)` blocks at the row-`i0` points. -/
theorem colBlk_lab [Finite Ω] (hint : 2 ≤ Nat.card (Quotient (MulAction.orbitRel F.Nl F.B)))
    (htr : S.Transitive) (hinv : S.HierInv) (hne : S.dom.Nonempty) (b₀ : F.B) (J : ℕ)
    (hJl : J < S.hier.length) (hlowJ : F.Low (levOf ⊥ S.hier J))
    (hhighJ : F.High (levOf ⊥ S.hier (J + 1))) (eΩ : Ω ≃ Fin n) (lab : Fin n → ℕ) {k : ℕ}
    (hk : k < S.hier.length)
    (hlab : ∀ i j, lab i = lab j ↔ S.hier[k].part.r (eΩ.symm i) (eΩ.symm j)) (c d : F.B) :
    d ∈ (colStep F hint htr hinv hne b₀ J hJl hlowJ hhighJ).blk (k + 1) c ↔
      lab (eΩ (F.e (c, F.i0))) = lab (eΩ (F.e (d, F.i0))) := by
  have hk' : k < (colStep F hint htr hinv hne b₀ J hJl hlowJ hhighJ).loc.length := by
    show k < (F.expLoc b₀).length
    simpa using hk
  refine (colBlk_succ (colStep F hint htr hinv hne b₀ J hJl hlowJ hhighJ).toColumnPre k hk' c
    d).trans ?_
  show ((F.expLoc b₀)[k]'(by simpa using hk)).part.r (F.e (c, F.i0)) (F.e (d, F.i0)) ↔ _
  rw [F.expLoc_part, RowForm.expPart, hlab, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    levOf_succ_of_lt hk]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rw [F.rowPart_iff (F.e (c, F.i0)).2 (F.e (d, F.i0)).2, F.e_label, F.e_label]

end Col

/-- **Orbit labels of the generators of `N`**: labels of the orbits of a generating list of
`N = Nl.map Hb.subtype` (as `orbits_spec` returns them) are labels of the `Nl`-orbits. -/
theorem colOrbit_labels (F : RowForm S L) {gs : List (Perm F.B)}
    (hgs : Subgroup.closure {σ | σ ∈ gs} = F.Nb) (ol : F.B → ℕ)
    (hol : ∀ x y, ol x = ol y ↔ y ∈ MulAction.orbit (Subgroup.closure {σ | σ ∈ gs}) x)
    (c d : F.B) : ol c = ol d ↔ ∃ n : F.Nl, (n : F.Hb) • c = d := by
  rw [hol, hgs]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
    exact ⟨⟨h, hh⟩, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨⟨_, Subgroup.mem_map_of_mem _ n.2⟩, rfl⟩

/-- The running minimum `colMinv ol bl d` is the least `ol` over a set that is the fiber of `bl`
through `d` (the form `hmin` of `Col.colSatKey`). -/
theorem colMinv_min {m : ℕ} (ol bl : Fin m → ℕ) (d : Fin m) (T : Set (Fin m))
    (hT : ∀ o, o ∈ T ↔ bl o = bl d) :
    (∃ o ∈ T, ol o = colMinv ol bl d) ∧ ∀ o ∈ T, colMinv ol bl d ≤ ol o := by
  obtain ⟨o, ho, he⟩ := colMinv_exists ol bl d
  exact ⟨⟨o, (hT o).2 ho, he⟩, fun o' h' => colMinv_le ol bl d o' ((hT o').1 h')⟩

end GI.Impl
