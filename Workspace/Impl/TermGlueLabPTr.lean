import Workspace.Impl.TermGlueLabPMat

/-!
# Transposing an integer matrix

Step 5 of the label program. The contract's matrix of a linear map is the transpose
of the matrix `U C V` (`tmGLP_mat`), so the program needs a transpose. `tmGLPTrFuns b`
(12 functions) on `[c, M]` with `M` an `r × c` matrix returns `Mᵀ`: it maps the column reader
`linColumn` over `[0, …, c - 1]` (`tmGLPTr_spec`, cost `tmGLPTrC W r c`).
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val encInt encIntMatrix)

/-- The entry, on `[c, M]`: map the column reader over `range c`. -/
def tmGLPTrF (b : ℕ) : Expr := .call (b + 2) (mk2 (arg 1) (.call (b + 5) (arg 0)))

/-- One column, on `[M, j]`. -/
def tmGLPTrColF (b : ℕ) : Expr := .call (b + 8) (mk2 (arg 1) (arg 0))

/-- **Transpose** (12 functions). -/
def tmGLPTrFuns (b : ℕ) : List Expr :=
  [tmGLPTrF b, tmGLPTrColF b] ++ mapFuns (b + 2) (b + 1) ++ rangeFuns (b + 5) ++
    linColumnFuns (b + 8)

theorem length_tmGLPTrFuns (b : ℕ) : (tmGLPTrFuns b).length = 12 := rfl

/-- The weight bound of a column with `r` entries of weight below `W`. -/
def tmGLPColW (W r : ℕ) : ℕ := 2 * (r * W) + r + 4

/-- The cost bound of one column. -/
def tmGLPTrColC (W r c : ℕ) : ℕ :=
  linColumnCost (2 * (W + c + 2) + 6) r + 200 * (W + c + 10) + tmGLPColW W r + 1

/-- The cost bound of the transpose. -/
def tmGLPTrC (W r c : ℕ) : ℕ :=
  loopModK * (c + 1) * (c + 2 + c + tmGLPColW (c + 2) c + 1) + tmGLPColW (c + 2) c +
    c * tmGLPTrColC W r c +
    mapK * (c + 1) * (4 * W + 4 * tmGLPColW (c + 2) c + 2 * tmGLPColW (tmGLPColW W r) c + 20) +
    200 * (W + tmGLPColW (c + 2) c + 10) + tmGLPColW (tmGLPColW W r) c + 1

/-- The weight of a list of values of weight at most `B`. -/
theorem tmGLP_wt_list_le {vs : List Val} {B : ℕ} (h : ∀ v ∈ vs, v.wt ≤ B) :
    (Val.list vs).wt ≤ tmGLPColW B vs.length := by
  have := linWtList h
  unfold tmGLPColW
  omega

theorem tmGLP_natList_wt (c : ℕ) : (natList (List.range c)).wt ≤ tmGLPColW (c + 2) c := by
  have h := tmGLP_wt_list_le (vs := (List.range c).map Val.nat) (B := c + 2) (by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
    have := wt_nat_le j
    have := List.mem_range.mp hj
    omega)
  simpa [natList] using h

/-- The columns of `M` are `Mᵀ`. -/
theorem tmGLP_cols_eq {r c : ℕ} (M : Matrix (Fin r) (Fin c) ℤ) :
    encIntMatrix M.transpose = .list ((List.finRange c).map fun j => linVecVal fun i => M i j) :=
  rfl

theorem tmGLP_range_eq (c : ℕ) :
    (List.range c).map Val.nat = (List.finRange c).map fun j => Val.nat j.val := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  rfl

/-- **Transpose.** -/
theorem tmGLPTr_spec {P : Program} {b : ℕ} (h : P.HasAt b (tmGLPTrFuns b)) {r c : ℕ}
    (M : Matrix (Fin r) (Fin c) ℤ) :
    FunDet P b (.list [.nat c, encIntMatrix M]) (encIntMatrix M.transpose)
      (tmGLPTrC (Val.list [.nat c, encIntMatrix M]).wt r c) := by
  set W := (Val.list [.nat c, encIntMatrix M]).wt with hW
  have hentry : P.funs[b]? = some (tmGLPTrF b) := by
    simpa using (h.block (gs := [tmGLPTrF b]) 0 rfl).single
  have hcol : P.funs[b + 1]? = some (tmGLPTrColF b) :=
    (h.block (gs := [tmGLPTrColF b]) 1 rfl).single
  have hmap : P.HasAt (b + 2) (mapFuns (b + 2) (b + 1)) := h.block 2 rfl
  have hrange : P.HasAt (b + 5) (rangeFuns (b + 5)) := h.block 5 rfl
  have hlc : P.HasAt (b + 8) (linColumnFuns (b + 8)) := h.block 8 rfl
  have wM : (encIntMatrix M).wt < W := wt_le_wt_list (by simp)
  have wc : (Val.nat c).wt < W := wt_le_wt_list (by simp)
  have wrow : ∀ i : Fin r, (linVecVal (M i)).wt < W := fun i =>
    (wt_le_wt_list (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)).trans wM
  -- one column
  have hcolW : ∀ j : Fin c, (linVecVal fun i => M i j).wt ≤ tmGLPColW W r := by
    intro j
    have := tmGLP_wt_list_le (vs := (List.finRange r).map fun i => encInt (M i j)) (B := W) (by
      intro v hv
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
      exact ((linVecEntryWt (M i) j).trans (wrow i)).le)
    simpa [linVecVal] using this
  have hs : ∀ v ∈ (List.range c).map Val.nat, FunAll P (b + 1) (.list [encIntMatrix M, v])
      (fun w cost => (∀ j : Fin c, v = .nat j.val → w = linVecVal fun i => M i j) ∧
        cost ≤ tmGLPTrColC W r c) := by
    intro v hv
    rw [tmGLP_range_eq] at hv
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hv
    apply FunAll.intro hcol
    have g0 := Det.arg' (P := P) (vs := [encIntMatrix M, .nat j.val]) (rest := []) (j := 0) rfl
    have g1 := Det.arg' (P := P) (vs := [encIntMatrix M, .nat j.val]) (rest := []) (j := 1) rfl
    have d := Det.call (Det.mk2 g1 g0) (linColumn_spec hlc M j)
    refine d.post fun cost hcost => ⟨fun j' hj' => ?_, ?_⟩
    · have : j' = j := Fin.ext (by injection hj' with e; exact e.symm)
      subst this; rfl
    · have w2 := wt_list2_le (.nat j.val) (encIntMatrix M)
      have w3 := wt_list2_le (encIntMatrix M) (.nat j.val)
      have wj := wt_nat_le j.val
      have hj := j.isLt
      have hl : linColumnCost (Val.list [.nat j.val, encIntMatrix M]).wt r ≤
          linColumnCost (2 * (W + c + 2) + 6) r := linColumnCost_mono (by omega) r
      have h3 := hcolW j
      unfold tmGLPTrColC
      omega
  -- the entry
  apply FunAll.intro hentry
  have g0 := Det.arg' (P := P) (vs := [.nat c, encIntMatrix M]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [.nat c, encIntMatrix M]) (rest := []) (j := 1) rfl
  set RC := loopModK * (c + 1) * ((Val.nat c).wt + c + (natList (List.range c)).wt + 1) with hRC
  have hr : FunDet P (b + 5) (.nat c) (natList (List.range c)) RC :=
    (range_spec hrange c).mono fun w cost ⟨hw, hc⟩ => ⟨hw, by rw [hw] at hc; exact hc⟩
  have dr := Det.call g0 hr
  have dargs := Det.mk2 g1 dr
  refine EvalAll.call_funAll dargs fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine (map_spec hmap (c := encIntMatrix M) (xs := (List.range c).map Val.nat) hs).mono ?_
  rintro w cost ⟨ws, rfl, hws, hcost⟩
  rw [tmGLP_range_eq] at hws
  have hws' : ws = (List.finRange c).map fun j => linVecVal fun i => M i j :=
    forall₂_map_eq (fun j _ w hw => hw j rfl) hws
  subst hws'
  refine ⟨(tmGLP_cols_eq M).symm, ?_⟩
  -- the cost
  have wN := tmGLP_natList_wt c
  have wO : (Val.list ((List.finRange c).map fun j => linVecVal fun i => M i j)).wt ≤
      tmGLPColW (tmGLPColW W r) c := by
    have := tmGLP_wt_list_le (vs := (List.finRange c).map fun j => linVecVal fun i => M i j)
      (B := tmGLPColW W r) (by
        intro v hv
        obtain ⟨j, -, rfl⟩ := List.mem_map.mp hv
        exact hcolW j)
    simpa using this
  have wc2 := wt_nat_le c
  have wl := wt_list2_le (encIntMatrix M) (natList (List.range c))
  have hsum : (((List.range c).map Val.nat).map fun _ => tmGLPTrColC W r c).sum =
      c * tmGLPTrColC W r c := by
    rw [List.map_map, Function.comp_def, List.map_const', List.sum_replicate, List.length_range,
      smul_eq_mul]
  rw [hsum] at hcost
  have hlen : ((List.range c).map Val.nat).length = c := by simp
  rw [hlen] at hcost
  have hm1 : mapK * (c + 1) * ((Val.list [encIntMatrix M, .list ((List.range c).map Val.nat)]).wt +
      (Val.list ((List.finRange c).map fun j => linVecVal fun i => M i j)).wt + 1) ≤
      mapK * (c + 1) * (4 * W + 4 * tmGLPColW (c + 2) c + 2 * tmGLPColW (tmGLPColW W r) c + 20) :=
    Nat.mul_le_mul_left _ (by change _ + _ + 1 ≤ _; unfold natList at wl wN; omega)
  have hRC' : RC ≤ loopModK * (c + 1) * (c + 2 + c + tmGLPColW (c + 2) c + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  unfold tmGLPTrC
  omega
