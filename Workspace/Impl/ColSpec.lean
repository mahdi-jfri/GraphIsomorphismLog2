import Workspace.Impl.ColLevel
import Workspace.Impl.RowPure

/-!
# What the column program must compute

For a row form built from pure coordinates `E : Fin m × Fin q ≃ dom` (`RowForm.ofPure`), the row
coordinates are numbers, so the class numbering can count them. This file fixes the values the
column program computes for each stored level `k`, from

* `labs k` (labels of the stored level `k`, read from the hierarchy value),
* `r0 c` (the position of the point `E (c, 0)` of row `0`),
* `ol` (orbit labels of `N` on `Fin m`), `cf i` (the column coordinate of position `i`),
  `rlf` (row labels) and the domain indicator,

and proves that the filtered list of their interval values is a canonical value of the child
hierarchy `dropTriv I.hier'` (`colChild_hierVal`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type} {n m : ℕ} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}

/-! ### The values, level by level -/

/-- The level-`(k+1)` labels of the row-`0` points. -/
def colBk (labs : ℕ → Fin n → ℕ) (r0 : Fin m → Fin n) (k : ℕ) (c : Fin m) : ℕ := labs k (r0 c)

/-- The level-`k` labels of the row-`0` points (the point itself at `k = 0`). -/
def colAk (labs : ℕ → Fin n → ℕ) (r0 : Fin m → Fin n) (k : ℕ) (c : Fin m) : ℕ :=
  if k = 0 then c else labs (k - 1) (r0 c)

/-- The ratio of level `k`: the number of level-`k` labels in the level-`(k+1)` block of `0`. -/
def colRat (labs : ℕ → Fin n → ℕ) (r0 : Fin m → Fin n) (h0 : 0 < m) (k : ℕ) : ℕ :=
  (Cls.repsOf (colEqv (colBk labs r0 k) (colBk labs r0 k) h0)
    (Cls.keyOf (fun c => colAk labs r0 k c + (m + 1))
      (colEqv (colBk labs r0 k) (colBk labs r0 k) h0))).length

/-- The lower ratio of level `k`: as `colRat`, inside the orbit of `0`. -/
def colLowRat (labs : ℕ → Fin n → ℕ) (r0 : Fin m → Fin n) (ol : Fin m → ℕ) (h0 : 0 < m)
    (k : ℕ) : ℕ :=
  (Cls.repsOf (colEqv (colBk labs r0 k) ol h0)
    (Cls.keyOf (fun c => colAk labs r0 k c + (m + 1)) (colEqv (colBk labs r0 k) ol h0))).length

/-- The labels of the lower part of level `k`. -/
def colLowLab (labs : ℕ → Fin n → ℕ) (ol : Fin m → ℕ) (cf : Fin n → Fin m) (rlf dvf : Fin n → ℕ)
    (k : ℕ) : Fin n → ℕ :=
  Cls.repOf (Cls.keyOf (colKeyv rlf (labs k) (fun i => ol (cf i)) (n + 1)) dvf)

/-- The labels of the upper part of level `k`. -/
def colUpLab (labs : ℕ → Fin n → ℕ) (r0 : Fin m → Fin n) (ol : Fin m → ℕ) (cf : Fin n → Fin m)
    (dvf : Fin n → ℕ) (k : ℕ) : Fin n → ℕ :=
  Cls.repOf (Cls.keyOf (fun i => colMinv ol (colBk labs r0 k) (cf i) + (n + 1)) dvf)

/-- The labels of the columns. -/
def colColsLab (ol : Fin m → ℕ) (cf : Fin n → Fin m) (dvf : Fin n → ℕ) : Fin n → ℕ :=
  Cls.repOf (Cls.keyOf (fun i => ol (cf i) + (n + 1)) dvf)

theorem colEqv_ne_zero {k : ℕ} (a₁ a₂ : Fin k → ℕ) (h : 0 < k) (i : Fin k) :
    colEqv a₁ a₂ h i ≠ 0 ↔ a₁ i = a₁ ⟨0, h⟩ ∧ a₂ i = a₂ ⟨0, h⟩ := by
  unfold colEqv; split_ifs with hc <;> simp [hc]

/-- The class count of `colCount`, with the offset written `+ (m + 1)`. -/
theorem colCount' (A dm : Fin m → ℕ) :
    (Cls.repsOf dm (Cls.keyOf (fun c => A c + (m + 1)) dm)).length =
      (A '' {c | dm c ≠ 0}).ncard := by
  have := colCount A dm
  simp only [← Nat.add_assoc] at this ⊢
  exact this

/-! ### The child hierarchy value -/

section Child

variable [Finite Ω] (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) (E : Fin m × Fin L.q ≃ S.dom)
  (hP : PureCoords S L label E) (bP : Fin m)
  (hint : 2 ≤ Nat.card (Quotient (MulAction.orbitRel (RowForm.ofPure hnat hq E hP bP).Nl
    (RowForm.ofPure hnat hq E hP bP).B)))
  (htr : S.Transitive) (hinv : S.HierInv) (hne : S.dom.Nonempty) (h0 : 0 < m) (J : ℕ)
  (hJl : J < S.hier.length)
  (hlowJ : (RowForm.ofPure hnat hq E hP bP).Low (levOf ⊥ S.hier J))
  (hhighJ : (RowForm.ofPure hnat hq E hP bP).High (levOf ⊥ S.hier (J + 1)))
  (eΩ : Ω ≃ Fin n) (labs : ℕ → Fin n → ℕ)
  (hlabs : ∀ k (hk : k < S.hier.length) i j, labs k i = labs k j ↔
    (S.hier[k]'hk).part.r (eΩ.symm i) (eΩ.symm j))
  (hlabn : ∀ k i, labs k i < n + 1)
  (r0 : Fin m → Fin n)
  (hr0 : ∀ c, r0 c = eΩ ((RowForm.ofPure hnat hq E hP bP).e (c, (RowForm.ofPure hnat hq E hP bP).i0)))
  (ol : Fin m → ℕ)
  (hol : ∀ c d : (RowForm.ofPure hnat hq E hP bP).B, ol c = ol d ↔ ∃ x : (RowForm.ofPure hnat hq E hP bP).Nl,
    (x : (RowForm.ofPure hnat hq E hP bP).Hb) • c = d)
  (holn : ∀ c, ol c < n + 1)
  (cf : Fin n → Fin m)
  (hcol : ∀ v : S.dom, cf (eΩ v) = ((RowForm.ofPure hnat hq E hP bP).e.symm v).1)
  (rlf : Fin n → ℕ) (hrl : ∀ v : S.dom, rlf (eΩ v) = ((RowForm.ofPure hnat hq E hP bP).label v : ℕ))

include hint htr hinv hne hlowJ hhighJ hlabs hlabn hr0 hol holn hcol hrl in
/-- **The child hierarchy value.** -/
theorem colChild_hierVal :
    HierValC eΩ (.list ((List.ofFn (fun k : Fin (Col.colStep (RowForm.ofPure hnat hq E hP bP) hint
          htr hinv hne ⟨0, h0⟩ J hJl hlowJ hhighJ).loc.length =>
        colIV (colLowLab labs ol cf rlf (indF eΩ S.dom) k) (colLowRat labs r0 ol h0 k)
          (min (Col.colStep (RowForm.ofPure hnat hq E hP bP) hint htr hinv hne ⟨0, h0⟩ J hJl hlowJ
            hhighJ).loc[k].cap (colLowRat labs r0 ol h0 k))
          (Col.colStep (RowForm.ofPure hnat hq E hP bP) hint htr hinv hne ⟨0, h0⟩ J hJl hlowJ
            hhighJ).loc[k].origin) ++
        [colIV (colColsLab ol cf (indF eΩ S.dom))
          (Col.colStep (RowForm.ofPure hnat hq E hP bP) hint htr hinv hne ⟨0, h0⟩ J hJl hlowJ
            hhighJ).rowI.ratio
          (Col.colStep (RowForm.ofPure hnat hq E hP bP) hint htr hinv hne ⟨0, h0⟩ J hJl hlowJ
            hhighJ).rowI.cap
          (Col.colStep (RowForm.ofPure hnat hq E hP bP) hint htr hinv hne ⟨0, h0⟩ J hJl hlowJ
            hhighJ).rowI.origin] ++
        List.ofFn (fun k : Fin (Col.colStep (RowForm.ofPure hnat hq E hP bP) hint
          htr hinv hne ⟨0, h0⟩ J hJl hlowJ hhighJ).loc.length =>
        colIV (colUpLab labs r0 ol cf (indF eΩ S.dom) k)
          (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k)
          (min (Col.colStep (RowForm.ofPure hnat hq E hP bP) hint htr hinv hne ⟨0, h0⟩ J hJl hlowJ
            hhighJ).loc[k].cap (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k))
          (Col.colStep (RowForm.ofPure hnat hq E hP bP) hint htr hinv hne ⟨0, h0⟩ J hJl hlowJ
            hhighJ).loc[k].origin)).filter colKeep))
      (dropTriv (Col.colStep (RowForm.ofPure hnat hq E hP bP) hint htr hinv hne ⟨0, h0⟩ J hJl hlowJ
        hhighJ).hier') := by
  set F := RowForm.ofPure hnat hq E hP bP with hF
  set b₀ : F.B := (⟨0, h0⟩ : Fin m)
  set I := Col.colStep F hint htr hinv hne b₀ J hJl hlowJ hhighJ with hI
  have hlen : I.loc.length = S.hier.length := by
    show (F.expLoc b₀).length = _
    simp
  -- the blocks of level `k`
  have hA : ∀ k < S.hier.length, ∀ c d : F.B,
      d ∈ I.blk k c ↔ colAk labs r0 k c = colAk labs r0 k d := by
    intro k hk c d
    rcases k with _ | k
    · refine (Col.colBlk_zero I.toColumnPre c d).trans ?_
      simp only [colAk, if_true]
      exact ⟨fun h => h ▸ rfl, fun h => Fin.ext h⟩
    · have hk' : k < S.hier.length := by omega
      refine (Col.colBlk_lab F hint htr hinv hne b₀ J hJl hlowJ hhighJ eΩ (labs k) hk'
        (hlabs k hk') c d).trans ?_
      simp only [colAk, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false, hr0]
      exact Iff.rfl
  have hbk : ∀ k c, colBk labs r0 k c = labs k (eΩ (F.e (c, F.i0))) := fun k c => by
    simp only [colBk, hr0]
    rfl
  have hkk : ∀ k : Fin I.loc.length, (k : ℕ) < S.hier.length := fun k => hlen ▸ k.2
  -- the two counts
  have hrat : ∀ k : Fin I.loc.length,
      (RowForm.localTower I.e I.i0 I.loc I.b₀ k).relIndex
          (RowForm.localTower I.e I.i0 I.loc I.b₀ (k + 1)) = colRat labs r0 h0 k ∧
      (RowForm.localTower I.e I.i0 I.loc I.b₀ k ⊓ I.Nl).relIndex
          (RowForm.localTower I.e I.i0 I.loc I.b₀ (k + 1) ⊓ I.Nl) =
        colLowRat labs r0 ol h0 k := by
    intro k
    obtain ⟨h1, h2⟩ := Col.colRatios_val F hint htr hinv hne b₀ J hJl hlowJ hhighJ eΩ ol hol
      (hkk k) (labs k) (hlabs k (hkk k)) (colAk labs r0 k) (hA k (hkk k))
    refine ⟨h1.trans ?_, h2.trans ?_⟩
    · unfold colRat
      rw [colCount']
      congr 2
      ext c
      simp only [Set.mem_setOf_eq, colEqv_ne_zero, and_self, hbk]
      rfl
    · unfold colLowRat
      rw [colCount']
      congr 2
      ext c
      simp only [Set.mem_setOf_eq, colEqv_ne_zero, hbk]
      rfl
  refine colHierVal eΩ I.toColumnPre _ _ _ _ _ (fun k => ?_) (fun k => ?_) ?_ (fun k => (hrat k).2.symm)
    (fun k => ?_)
  · exact Col.colLower_val F hint htr hinv hne b₀ J hJl hlowJ hhighJ eΩ cf hcol ol hol rlf hrl
      (hkk k) (labs k) (hlabs k (hkk k)) (hlabn k) holn
  · refine Col.colUpper_val F hint htr hinv hne b₀ J hJl hlowJ hhighJ eΩ cf hcol ol hol (hkk k)
      (labs k) (hlabs k (hkk k)) (fun d => colMinv ol (colBk labs r0 k) d) fun d => ?_
    obtain ⟨o, ho, he⟩ := colMinv_exists ol (colBk labs r0 k) d
    refine ⟨⟨o, by rw [← hbk, ← hbk]; exact ho, he⟩, fun o' h' => colMinv_le _ _ _ _ ?_⟩
    rw [hbk, hbk]; exact h'
  · exact Col.colCols_val F hint htr hinv hne b₀ J hJl hlowJ hhighJ eΩ cf hcol ol hol
  · rw [Col.colUpper_eq I.toColumnPre k, (hrat k).1, (hrat k).2]

end Child

end GI.Impl
