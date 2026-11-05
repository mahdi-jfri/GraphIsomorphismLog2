module

public import Workspace.Impl.SNFMainP
public import Workspace.Proved.HNFFinal

@[expose] public section

/-!
# Smith normal form of a nonsingular matrix, proved

The program `snfProgram` is the Hermite program `hnfFuns` (functions `0`–`151`) followed by the
functions of the Smith form (`152`–`227`, see `Impl/SNFAltP.lean`). Its main function `227`
computes `snfRes A` (`snfMain_spec`), which is correct by `snfRes_spec`. The cost is a polynomial
in the input weight (`snfMainCost_poly`), and every output entry has fewer than `snfB2 W` bits
(`snf_all_bits`), which is at most a power of the number of input cells.

The method is the one of Kannan and Bachem (1979), Section 3: alternate Hermite forms of the
matrix and of its transpose until the matrix is diagonal, then fix the divisibility of the
diagonal by pair steps.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved

/-! ### The program -/

/-- All functions of the program. The main function is at index `227`. -/
def snfFuns : List Expr :=
  hnfFuns ++ hnfTabFuns 152 168 ++ [snfTrCellF] ++ hnfTabFuns 169 185 ++ [snfEmbCellF] ++
    linDenseMulFuns 186 ++ iterFuns 218 221 ++ [snfAltE] ++ iterFuns 222 225 ++
    [snfPairE, snfCoefE, snfMainE]

/-- **The Smith form program.** No primitives. -/
def snfProgram : Program := ⟨snfFuns, []⟩

theorem snf_hasAt {b : ℕ} {fs : List Expr} (h : (snfFuns.drop b).take fs.length = fs) :
    snfProgram.HasAt b fs := by
  intro j hj
  show snfFuns[b + j]? = some fs[j]
  have h1 : ((snfFuns.drop b).take fs.length)[j]? = fs[j]? := by rw [h]
  rw [List.getElem?_take_of_lt hj, List.getElem?_drop] at h1
  rw [h1, List.getElem?_eq_getElem hj]

theorem snf_funs_get {k : ℕ} {e : Expr} (h : (snfFuns.drop k).take 1 = [e]) :
    snfProgram.funs[k]? = some e := by
  have := snf_hasAt (b := k) (fs := [e]) h 0 (by simp)
  simpa using this

theorem snfProgram_hnf : hnfMainAt snfProgram where
  ints := snf_hasAt rfl
  bar := snf_hasAt rfl
  abs := snf_hasAt rfl
  pow := snf_hasAt rfl
  compl := snf_hasAt rfl
  tb := snf_hasAt rfl
  bcell := snf_funs_get rfl
  md := snf_hasAt rfl
  tu := snf_hasAt rfl
  ucell := snf_funs_get rfl
  th := snf_hasAt rfl
  hcell := snf_funs_get rfl
  nums := snf_funs_get rfl
  main := snf_funs_get rfl

theorem snfProgram_mul : linDenseMulAt snfProgram 186 := linDenseMulAt_of (snf_hasAt rfl)

theorem snfProgram_at : snfMainAt snfProgram where
  alt := ⟨snfProgram_hnf, hnfTabAt_of (snf_hasAt rfl), snf_funs_get rfl, snfProgram_mul, snf_funs_get rfl⟩
  pair := ⟨snfProgram_hnf, hnfTabAt_of (snf_hasAt rfl), snf_funs_get rfl, snfProgram_mul, snf_funs_get rfl,
    snf_funs_get rfl⟩
  it1 := snf_hasAt rfl
  it2 := snf_hasAt rfl
  main := snf_funs_get rfl

/-! ### The cost -/

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem snfMainCost_poly (K D : ℕ) : PBU (fun _ W _ => snfMainCost K D W) := by
  simp only [snfMainCost, snfAltCost, snfAltCostZ, snfPairCost, snfG, snfF, snfY, snfXw, snfB2,
    snfCn, snfBeta, hnfXW, hnfL, loopModK]
  hnf_norm_poly

set_option maxRecDepth 16000 in
theorem snfB2_poly : PBU (fun _ W _ => snfB2 W) := by
  simp only [snfB2, snfCn, snfBeta]
  hnf_norm_poly

/-! ### The input -/

theorem snf_input_size (I : NonsingularInst) :
    (nonsingularInput I).size = (encIntMatrix I.A).size + 5 := by
  rw [size_eq_length, size_eq_length]
  simp only [nonsingularInput, cells_list, cellsList_cons, cellsList_nil, cells_nat,
    List.length_append, List.length_cons, List.length_nil]
  omega

/-- **The cells of the input are at most its size plus one.** -/
theorem snf_input_cells (I : NonsingularInst) :
    ∀ a ∈ (nonsingularInput I).cells, a ≤ 1 * ((nonsingularInput I).size + 1) ^ 1 := by
  intro a ha
  rw [one_mul, pow_one, snf_input_size]
  have hM := hnfSmall_mat I.A
  have hr : I.n ∈ (encIntMatrix I.A).cells := by
    simp [encIntMatrix, cells_list]
  have hrM := hM _ hr
  have hlen : (Val.cellsList [.nat I.n, encIntMatrix I.A]).length =
      (encIntMatrix I.A).size + 2 := by
    rw [size_eq_length]
    simp only [cellsList_cons, cellsList_nil, cells_nat, List.length_append, List.length_cons,
      List.length_nil]
    omega
  simp only [nonsingularInput, cells_list, List.length_cons, List.length_nil, List.cons_append,
    List.nil_append, List.mem_cons] at ha
  rcases ha with h | h | h | ha
  · omega
  · omega
  · rw [h, hlen]; omega
  · simp only [cellsList_cons, cellsList_nil, cells_nat, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons] at ha
    rcases ha with h | h | ha
    · omega
    · omega
    · have := hM a ha; omega

/-- The input weight is at most a polynomial in the number of cells. -/
theorem snf_wt_cells (I : NonsingularInst) :
    (nonsingularInput I).wt + 2 ≤ (nonsingularInput I).cells.length ^ 4 ∧
      2 ≤ (nonsingularInput I).cells.length := by
  set s := (nonsingularInput I).cells.length with hs
  have hW : (nonsingularInput I).wt ≤ s * (s + 1 + 1) := by
    have := wt_le_of_cells_le (fun a ha => by simpa using snf_input_cells I a ha)
    rwa [size_eq_length] at this
  have h2 : 2 ≤ s := by have := (nonsingularInput I).two_le_size; rwa [size_eq_length] at this
  refine ⟨?_, h2⟩
  have h3 : s * (s + 1 + 1) + 2 ≤ s * s * 4 := by nlinarith
  have h4 : s * s * 4 ≤ s * s * (s * s) := Nat.mul_le_mul_left _ (by nlinarith)
  have h5 : s * s * (s * s) = s ^ 4 := by ring
  omega

/-! ### The output -/

theorem snf_output_correct (I : NonsingularInst) {C E : ℕ}
    (hCE : ∀ W, snfB2 W ≤ C * (W + 2) ^ E) :
    IsUnit (snfRes I.A).P.det ∧ IsUnit (snfRes I.A).Q.det ∧
      (snfRes I.A).P * I.A * (snfRes I.A).Q = (snfRes I.A).H ∧ IsSmithForm (snfRes I.A).H ∧
      EntriesBits ((nonsingularInput I).cells.length ^ (C + 4 * E)) (snfRes I.A).P ∧
      EntriesBits ((nonsingularInput I).cells.length ^ (C + 4 * E)) (snfRes I.A).H ∧
      EntriesBits ((nonsingularInput I).cells.length ^ (C + 4 * E)) (snfRes I.A).Q := by
  obtain ⟨n, hn, A, hA⟩ := I
  obtain ⟨hP, hQ, hrel, hS⟩ := snfRes_spec hn hA
  obtain ⟨hWs, hs2⟩ := snf_wt_cells ⟨n, hn, A, hA⟩
  set s := (nonsingularInput ⟨n, hn, A, hA⟩).cells.length with hs
  set W := (nonsingularInput ⟨n, hn, A, hA⟩).wt with hW
  have wA : (encIntMatrix A).wt < W := wt_le_wt_list (by simp [hW, nonsingularInput])
  obtain ⟨hnW, hEA, -, hc⟩ := snf_input_facts hn hA wA
  have hB : 1 + snfCount A * (snfBeta (snfBeta W) + snfBeta W) +
      n * n * (snfBeta (snfBeta W) + 2 * snfBeta W) ≤ snfB2 W := by
    have h1 := Nat.mul_le_mul_right (snfBeta (snfBeta W) + snfBeta W) hc
    have h2 := Nat.mul_le_mul_right (snfBeta (snfBeta W) + 2 * snfBeta W)
      (Nat.mul_le_mul hnW.le hnW.le)
    unfold snfB2
    omega
  obtain ⟨-, h2⟩ := snf_all_bits hn hA hEA hB
  obtain ⟨bH, bP, bQ⟩ := h2 (n * n) le_rfl
  -- `snfB2 W ≤ s ^ (C + 4 E)`
  have k1 : snfB2 W ≤ C * (W + 2) ^ E := hCE W
  have k2 : (W + 2) ^ E ≤ (s ^ 4) ^ E := Nat.pow_le_pow_left hWs E
  have k3 : C ≤ s ^ C := le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left hs2 C)
  have k4 : snfB2 W ≤ s ^ (C + 4 * E) := by
    calc snfB2 W ≤ C * (W + 2) ^ E := k1
      _ ≤ s ^ C * (s ^ 4) ^ E := Nat.mul_le_mul k3 k2
      _ = s ^ (C + 4 * E) := by rw [← pow_mul, ← pow_add]
  rw [← snfRes_eq] at bH bP bQ
  exact ⟨hP, hQ, hrel, hS, snfBits_mono k4 bP, snfBits_mono k4 bH, snfBits_mono k4 bQ⟩

end GI.Impl

namespace GI.Proved

open GI.Cited GI.Lang GI.Impl

/-- **Smith normal form with multipliers of a square nonsingular matrix** ([KannanBachem79,
Section 3, Theorems 3–5]), proved: the program `GI.Impl.snfProgram`. -/
theorem smithNonsingular : SmithNonsingular := by
  obtain ⟨K, D, hE⟩ := snfEnv_exists
  obtain ⟨C, E, hCE⟩ := snfMainCost_poly K D
  obtain ⟨C2, E2, hB2⟩ := snfB2_poly
  have hB2' : ∀ W, snfB2 W ≤ C2 * (W + 2) ^ E2 := fun W => by
    have := hB2 0 W 0; simpa [PB] using this
  refine ⟨C2 + 4 * E2, ?_⟩
  unfold SmithNonsingularTask
  refine polyTimeAt_ofVal_of_lang_cells snfProgram 227 (C * 2 ^ E) E 1 1 snf_input_cells
    fun I => ?_
  refine FunAll.mono (snfMain_spec snfProgram_at hE I) fun v cst hv => ⟨?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := snf_output_correct I hB2'
    exact ⟨_, _, _, hv.1, h1, h2, h3, h4, h5, h6, h7⟩
  · have h1 : snfMainCost K D (nonsingularInput I).wt ≤
        C * ((nonsingularInput I).wt + 0 + 0 + 2) ^ E := hCE 0 (nonsingularInput I).wt 0
    have h2 : ((nonsingularInput I).wt + 0 + 0 + 2) ^ E ≤ (2 * ((nonsingularInput I).wt + 1)) ^ E :=
      Nat.pow_le_pow_left (by omega) E
    calc cst ≤ snfMainCost K D (nonsingularInput I).wt := hv.2
      _ ≤ C * (2 * ((nonsingularInput I).wt + 1)) ^ E := h1.trans (Nat.mul_le_mul_left _ h2)
      _ = C * 2 ^ E * ((nonsingularInput I).wt + 1) ^ E := by rw [mul_pow]; ring

end GI.Proved
