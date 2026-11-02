import Workspace.Impl.HNFPoly
import Workspace.Impl.CamCells

/-!
# The Hermite normal form with transform is computable in polynomial time

`GI.Proved.hermiteFullRank` proves the cited statement `GI.Cited.HermiteFullRank` ([SL96,
Theorem 12]). The method is the modular Hermite form
of Domich–Kannan–Trotter as in [SL96, Section 2]: Bareiss elimination finds `c` independent rows
and their determinant `d`; the matrix is made square by unit columns; and one Hermite form of
`[[A', I], [0, K I]]` modulo `|d| K` gives both the Hermite form and the transform
(`GI.Proved.hnfRect_spec`). The program is `GI.Impl.hnfProgram`, its run is
`GI.Impl.hnfMain_spec`, and its cost is polynomial by `GI.Impl.hnfMainCost_poly`.

The output entries are below `2^L` with `L = 10 (W + 1)^2`, `W` the input weight; this is at most
`2^(s^12)` for `s` the number of input cells.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved

/-! ### The program -/

/-- All functions of the program. The main function is at index `151`. -/
def hnfFuns : List Expr :=
  linIntFuns 0 ++ hnfBarFuns 18 0 ++ hnfMatAbsFuns 42 0 ++ hnfPowFuns 50 ++ hnfComplFuns 54 ++
    hnfTabFuns 67 83 ++ [hnfBigCellF 0] ++ hnfModFuns 84 0 ++ hnfTabFuns 116 132 ++
    [hnfUCellF 0] ++ hnfTabFuns 133 149 ++ [hnfHCellF, hnfNumsF 42 50 0, hnfMainE]

/-- **The Hermite program.** No primitives. -/
def hnfProgram : Program := ⟨hnfFuns, []⟩

theorem hnf_hasAt {b : ℕ} {fs : List Expr} (h : (hnfFuns.drop b).take fs.length = fs) :
    hnfProgram.HasAt b fs := by
  intro j hj
  show hnfFuns[b + j]? = some fs[j]
  have h1 : ((hnfFuns.drop b).take fs.length)[j]? = fs[j]? := by rw [h]
  rw [List.getElem?_take_of_lt hj, List.getElem?_drop] at h1
  rw [h1, List.getElem?_eq_getElem hj]

theorem hnf_funs_get {k : ℕ} {e : Expr} (h : (hnfFuns.drop k).take 1 = [e]) :
    hnfProgram.funs[k]? = some e := by
  have := hnf_hasAt (b := k) (fs := [e]) h 0 (by simp)
  simpa using this

theorem hnfProgram_at : hnfMainAt hnfProgram where
  ints := hnf_hasAt rfl
  bar := hnf_hasAt rfl
  abs := hnf_hasAt rfl
  pow := hnf_hasAt rfl
  compl := hnf_hasAt rfl
  tb := hnf_hasAt rfl
  bcell := hnf_funs_get rfl
  md := hnf_hasAt rfl
  tu := hnf_hasAt rfl
  ucell := hnf_funs_get rfl
  th := hnf_hasAt rfl
  hcell := hnf_funs_get rfl
  nums := hnf_funs_get rfl
  main := hnf_funs_get rfl

/-! ### Cells of the input -/

/-- Values whose cells are at most their size plus one. -/
def HnfSmall (v : Val) : Prop := ∀ a ∈ v.cells, a ≤ v.size + 1

theorem hnfSmall_list {vs : List Val} (h : ∀ v ∈ vs, HnfSmall v) : HnfSmall (.list vs) := by
  intro a ha
  rw [size_eq_length]
  simp only [cells_list, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, List.mem_cons] at ha ⊢
  have hlen := length_le_cellsList vs
  rcases ha with rfl | rfl | rfl | ha
  · omega
  · omega
  · omega
  · obtain ⟨v, hv, ha⟩ := cam_mem_cellsList ha
    have h1 := h v hv a ha
    have h2 : v.size ≤ (Val.cellsList vs).length := by
      rw [length_cellsList]
      exact List.le_sum_of_mem (List.mem_map_of_mem hv)
    omega

theorem hnfSmall_nat {b : ℕ} (hb : b ≤ 1) : HnfSmall (.nat b) := by
  intro a ha
  simp only [cells_nat, List.mem_cons, List.not_mem_nil, or_false] at ha
  rw [size_nat]
  rcases ha with rfl | rfl <;> omega

theorem hnfSmall_encInt (z : ℤ) : HnfSmall (encInt z) := by
  unfold encInt
  refine hnfSmall_list fun v hv => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact hnfSmall_nat (by split_ifs <;> omega)
  · refine hnfSmall_list fun v hv => ?_
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hv
    exact hnfSmall_nat (by split_ifs <;> omega)

theorem hnfSmall_mat {r c : ℕ} (A : Matrix (Fin r) (Fin c) ℤ) : HnfSmall (encIntMatrix A) := by
  unfold encIntMatrix
  refine hnfSmall_list fun v hv => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
  refine hnfSmall_list fun v hv => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hv
  exact hnfSmall_encInt _

theorem hnf_input_size (I : FullRankInst) :
    (fullRankInput I).size = (encIntMatrix I.A).size + 7 := by
  rw [size_eq_length, size_eq_length]
  simp only [fullRankInput, cells_list, cellsList_cons, cellsList_nil, cells_nat,
    List.length_append, List.length_cons, List.length_nil]
  omega

/-- **The cells of the input are at most its size plus one.** -/
theorem hnf_input_cells (I : FullRankInst) :
    ∀ a ∈ (fullRankInput I).cells, a ≤ 1 * ((fullRankInput I).size + 1) ^ 1 := by
  intro a ha
  rw [one_mul, pow_one, hnf_input_size]
  have hM := hnfSmall_mat I.A
  -- `r` is the length of the list of rows, so it is a cell of the matrix
  have hr : I.r ∈ (encIntMatrix I.A).cells := by
    simp [encIntMatrix, cells_list]
  have hrM := hM _ hr
  have hcr := I.c_le
  have hlen : (Val.cellsList [.nat I.r, .nat I.c, encIntMatrix I.A]).length =
      (encIntMatrix I.A).size + 4 := by
    rw [size_eq_length]
    simp only [cellsList_cons, cellsList_nil, cells_nat, List.length_append, List.length_cons,
      List.length_nil]
    omega
  have ha' : a = 1 ∨ a = 3 ∨ a = (Val.cellsList [.nat I.r, .nat I.c, encIntMatrix I.A]).length ∨
      a = 0 ∨ a = I.r ∨ a = I.c ∨ a ∈ (encIntMatrix I.A).cells := by
    simp only [fullRankInput, cells_list, List.length_cons, List.length_nil, List.cons_append,
      List.nil_append, List.mem_cons] at ha
    rcases ha with h | h | h | ha
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · simp only [cellsList_cons, cellsList_nil, cells_nat, List.append_nil, List.cons_append,
        List.nil_append, List.mem_cons] at ha
      rcases ha with h | h | h | h | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ha)))))
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | ha
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · have := hM a ha; omega

/-! ### The final theorem -/

theorem hnf_L_le_cells (I : FullRankInst) :
    hnfL (fullRankInput I).wt ≤ (fullRankInput I).cells.length ^ 12 := by
  set s := (fullRankInput I).cells.length with hs
  have hW : (fullRankInput I).wt ≤ s * (s + 1 + 1) := by
    have := wt_le_of_cells_le (fun a ha => by simpa using hnf_input_cells I a ha)
    rwa [size_eq_length] at this
  have h2 : 2 ≤ s := by have := (fullRankInput I).two_le_size; rwa [size_eq_length] at this
  have h1 : (fullRankInput I).wt + 1 ≤ (s + 1) ^ 2 := by nlinarith
  have h3 : (s + 1) ^ 2 ≤ (2 * s) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h4 : hnfL (fullRankInput I).wt ≤ 10 * ((2 * s) ^ 2) ^ 2 := by
    unfold hnfL
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (h1.trans h3) 2)
  have h5 : 10 * ((2 * s) ^ 2) ^ 2 = 160 * s ^ 4 := by ring
  have h6 : 160 ≤ s ^ 8 := by
    calc 160 ≤ 2 ^ 8 := by norm_num
      _ ≤ s ^ 8 := Nat.pow_le_pow_left h2 8
  have h7 : 160 * s ^ 4 ≤ s ^ 8 * s ^ 4 := Nat.mul_le_mul_right _ h6
  have h8 : s ^ 8 * s ^ 4 = s ^ 12 := by ring
  omega

/-- The output is correct. -/
theorem hnf_output_correct (I : FullRankInst) :
    IsUnit (hnfRectU I.A (hnfTn I.A)).det ∧ hnfRectU I.A (hnfTn I.A) * I.A = hnfRectH I.A I.c_le (hnfTn I.A) ∧
      IsHermiteForm (hnfRectH I.A I.c_le (hnfTn I.A)) ∧
      EntriesBits ((fullRankInput I).cells.length ^ 12) (hnfRectU I.A (hnfTn I.A)) ∧
      EntriesBits ((fullRankInput I).cells.length ^ 12) (hnfRectH I.A I.c_le (hnfTn I.A)) := by
  obtain ⟨r, c, hc0, hcr, A, hA⟩ := I
  have hLs := hnf_L_le_cells ⟨r, c, hc0, hcr, A, hA⟩
  simp only at hLs ⊢
  set W := (fullRankInput ⟨r, c, hc0, hcr, A, hA⟩).wt with hW
  have wA : (encIntMatrix A).wt < W := wt_le_wt_list (by simp [hW, fullRankInput])
  have hrW : r ≤ W := (hnf_rows_lt_wt A).le.trans wA.le
  have hAW : ∀ i j, (A i j).natAbs < 2 ^ W := fun i j =>
    lt_of_lt_of_le (hnf_entry_lt_wt A i j) (Nat.pow_le_pow_right (by decide) wA.le)
  have hT1 : (1 : ℤ) ≤ (hnfTn A : ℤ) := by unfold hnfTn; omega
  obtain ⟨hunit, hmul, hherm, hU, hH, hd⟩ := hnfRect_spec A hA hc0 hcr hT1 (hnf_abs_le_Tn A)
  obtain ⟨hKL, hmL, -⟩ := hnf_sizes A hrW hcr hAW hd
  have hpow : 2 ^ hnfL W ≤ 2 ^ (fullRankInput ⟨r, c, hc0, hcr, A, hA⟩).cells.length ^ 12 :=
    Nat.pow_le_pow_right (by decide) hLs
  have eK : hnfK r (hnfTn A : ℤ) = (hnfKn A : ℤ) := (hnfKn_eq A).symm
  have em : |(hnfBarIter A c).d| * (hnfKn A : ℤ) = (hnfMn A (hnfBarIter A c).d : ℤ) := by
    unfold hnfMn; push_cast; rfl
  rw [eK] at hU hH
  rw [em] at hH
  refine ⟨hunit, hmul, hherm, fun i j => ?_, fun i j => ?_⟩
  · have h1 := hU i j
    rw [← Int.natCast_natAbs] at h1
    have h2 : (hnfRectU A (hnfTn A) i j).natAbs < hnfKn A := by exact_mod_cast h1
    omega
  · obtain ⟨h0, h1⟩ := hH i j
    have h2 : (hnfRectH A hcr (hnfTn A) i j).natAbs ≤ hnfMn A (hnfBarIter A c).d := by
      have h3 : ((hnfRectH A hcr (hnfTn A) i j).natAbs : ℤ) ≤ hnfMn A (hnfBarIter A c).d := by
        rw [Int.natCast_natAbs, abs_of_nonneg h0]; exact h1
      exact_mod_cast h3
    omega

end GI.Impl

namespace GI.Proved

open GI.Cited GI.Lang GI.Impl

/-- **Hermite normal form with a unimodular premultiplier** ([SL96, Theorem 12]), proved: the
program `GI.Impl.hnfProgram` with output exponent `12`. -/
theorem hermiteFullRank : HermiteFullRank := by
  obtain ⟨C, D, hCD⟩ := hnfMainCost_poly
  refine ⟨12, ?_⟩
  unfold HermiteFullRankTask
  refine polyTimeAt_ofVal_of_lang_cells hnfProgram 151 (C * 2 ^ D) D 1 1 hnf_input_cells
    fun I => ?_
  refine FunAll.mono (hnfMain_spec hnfProgram_at I) fun v cst hv => ⟨?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hnf_output_correct I
    exact ⟨_, _, hv.1, h1, h2, h3, h4, h5⟩
  · have h1 : hnfMainCost (fullRankInput I).wt ≤ C * ((fullRankInput I).wt + 0 + 0 + 2) ^ D :=
      hCD 0 (fullRankInput I).wt 0
    have h2 : ((fullRankInput I).wt + 0 + 0 + 2) ^ D ≤ (2 * ((fullRankInput I).wt + 1)) ^ D :=
      Nat.pow_le_pow_left (by omega) D
    calc cst ≤ hnfMainCost (fullRankInput I).wt := hv.2
      _ ≤ C * (2 * ((fullRankInput I).wt + 1)) ^ D := h1.trans (Nat.mul_le_mul_left _ h2)
      _ = C * 2 ^ D * ((fullRankInput I).wt + 1) ^ D := by rw [mul_pow]; ring

end GI.Proved
