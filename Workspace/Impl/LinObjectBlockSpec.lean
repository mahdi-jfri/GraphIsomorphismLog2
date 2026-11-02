import Workspace.Impl.LinObjectBlockProg
import Workspace.Impl.LinFiniteActionCost

namespace GI.Impl
open GI.Cited GI.Lang

def linObjectBlockRowCost (W c : ℕ) : ℕ :=
  10000 * (W + c + linTabulateCost (100 * (W + c + 1)) c
    (100000 * (100 * (W + c + 1) + 1)) + 1)

def linObjectBlockCost (W r c : ℕ) : ℕ :=
  10000 * (W + r + linTabulateCost (100 * (W + r + 1)) r
    (linObjectBlockRowCost (100 * (W + r + 1)) c) + 1)

theorem linObjectBlockRowCost_mono {W V c d : ℕ} (h : W ≤ V) (hc : c ≤ d) :
    linObjectBlockRowCost W c ≤ linObjectBlockRowCost V d := by
  unfold linObjectBlockRowCost
  gcongr
  exact linTabulateCost_mono (by omega) hc (by omega)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 5000 in
theorem linObjectBlockRow_spec {P : Program} {b p r d : ℕ}
    (h : linObjectBlockAt P b) (M : Fin p → Matrix (Fin r) (Fin d) ℤ)
    (i : Fin (r * p)) :
    FunDet P (b + 1) (.list [linObjectBlockInput M, .nat i])
      (linVecVal (linObjectBlockMatrix M i))
      (linObjectBlockRowCost (Val.list [linObjectBlockInput M, .nat i]).wt (d * p)) := by
  let input := linObjectBlockInput M
  let a := Val.list [input, .nat i]
  let W := a.wt
  let C := d * p
  have wi : input.wt < W := wt_le_wt_list (by simp [a, W])
  have harg : (Val.list [a, .nat C]).wt ≤ 100 * (W + C + 1) := by
    have hh := wt_list2_le a (.nat C)
    have hc := wt_nat_le C
    dsimp only [W]
    omega
  have hcell (k : Fin C) : (Val.list [a, .nat k]).wt ≤ 100 * (W + C + 1) := by
    have hh := wt_list2_le a (.nat k)
    have hk := wt_nat_le k.val
    have := k.isLt
    dsimp only [W]
    omega
  have hs (k : Fin C) : FunDet P (b + 2) (.list [a, .nat k])
      (encInt (linObjectBlockMatrix M i k))
      (100000 * (100 * (W + C + 1) + 1)) := by
    obtain ⟨⟨ai, ii⟩, hi⟩ := finProdFinEquiv.surjective i
    obtain ⟨⟨aj, ij⟩, hj⟩ := finProdFinEquiv.surjective k
    subst i
    subst k
    simpa only [linObjectBlockMatrix_apply] using
      (linObjectBlockCell_spec h.cell M ii ij ai aj).mono
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (hcell (finProdFinEquiv (aj, ij))) 1))
  have ht := (linTabulate_spec h.cols a
    (fun k : Fin C => encInt (linObjectBlockMatrix M i k))
    (100000 * (100 * (W + C + 1) + 1)) hs).mono
      (linTabulateCost_mono harg le_rfl le_rfl)
  have dc := Det.arg' (P := P) (vs := [input, .nat i]) (rest := []) (j := 0) rfl
  have dcols := Det.length (Det.get' dc (Det.nat 1) rfl)
  have dpieces := Det.length (Det.get' dc (Det.nat 2) rfl)
  simp only [linObjectBlockInput, input, encFun, List.length_map, List.length_finRange] at dcols dpieces
  have dn := Det.arith' (op := .mul) dcols dpieces rfl
  have da := Det.var' (P := P) (env := [a]) (i := 0) rfl
  have dout := Det.call (Det.mk2 da dn) ht
  apply FunDet.intro h.row
  refine dout.mono ?_
  have wo := ht.wt_lt.le
  have wr : (encFun (fun i : Fin d => i.val)).wt < input.wt := wt_le_wt_list (by
    simp [input, linObjectBlockInput])
  have wp : (Val.list ((List.finRange p).map fun i => encIntMatrix (M i))).wt < input.wt :=
    wt_le_wt_list (by simp [input, linObjectBlockInput])
  have hc := wt_nat_le C
  have hh := wt_list2_le a (.nat C)
  have hd := length_lt_wt_list ((List.finRange d).map fun i => Val.nat i.val)
  have hp := length_lt_wt_list ((List.finRange p).map fun i => encIntMatrix (M i))
  simp only [List.length_map, List.length_finRange] at hd hp
  change _ ≤ linObjectBlockRowCost W C
  unfold linObjectBlockRowCost
  dsimp only [a, W, C, input, linObjectBlockInput, encFun, GI.Machine.BinOp.eval] at *
  omega

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 5000 in
theorem linObjectBlock_spec {P : Program} {b p r d : ℕ}
    (h : linObjectBlockAt P b) (M : Fin p → Matrix (Fin r) (Fin d) ℤ) :
    FunDet P b (linObjectBlockInput M) (encIntMatrix (linObjectBlockMatrix M))
      (linObjectBlockCost (linObjectBlockInput M).wt (r * p) (d * p)) := by
  let a := linObjectBlockInput M
  let W := a.wt
  let R := r * p
  let C := d * p
  have harg : (Val.list [a, .nat R]).wt ≤ 100 * (W + R + 1) := by
    have hh := wt_list2_le a (.nat R)
    have hc := wt_nat_le R
    dsimp only [W]
    omega
  have hrow (i : Fin R) : (Val.list [a, .nat i]).wt ≤ 100 * (W + R + 1) := by
    have hh := wt_list2_le a (.nat i)
    have hi := wt_nat_le i.val
    have := i.isLt
    dsimp only [W]
    omega
  have ht := (linTabulate_spec h.rows a
    (fun i : Fin R => linVecVal (linObjectBlockMatrix M i))
    (linObjectBlockRowCost (100 * (W + R + 1)) C) (fun i =>
      (linObjectBlockRow_spec h M i).mono (linObjectBlockRowCost_mono (hrow i) le_rfl))).mono
        (linTabulateCost_mono harg le_rfl le_rfl)
  have dr := Det.length (Det.arg' (P := P) (vs :=
    [encFun (fun i : Fin r => i.val), encFun (fun i : Fin d => i.val),
      .list ((List.finRange p).map fun i => encIntMatrix (M i))]) (rest := []) (j := 0) rfl)
  have dp := Det.length (Det.arg' (P := P) (vs :=
    [encFun (fun i : Fin r => i.val), encFun (fun i : Fin d => i.val),
      .list ((List.finRange p).map fun i => encIntMatrix (M i))]) (rest := []) (j := 2) rfl)
  simp only [encFun, List.length_map, List.length_finRange] at dr dp
  have dn := Det.arith' (op := .mul) dr dp rfl
  have da := Det.var' (P := P) (env := [a]) (i := 0) rfl
  have dout := Det.call (Det.mk2 da dn) ht
  apply FunDet.intro h.entry
  refine dout.mono ?_
  have wo := ht.wt_lt.le
  have wr : (encFun (fun i : Fin r => i.val)).wt < a.wt := wt_le_wt_list (by
    simp [a, linObjectBlockInput])
  have wp : (Val.list ((List.finRange p).map fun i => encIntMatrix (M i))).wt < a.wt :=
    wt_le_wt_list (by simp [a, linObjectBlockInput])
  have hr := length_lt_wt_list ((List.finRange r).map fun i => Val.nat i.val)
  have hp := length_lt_wt_list ((List.finRange p).map fun i => encIntMatrix (M i))
  simp only [List.length_map, List.length_finRange] at hr hp
  have hc := wt_nat_le R
  have hh := wt_list2_le a (.nat R)
  change _ ≤ linObjectBlockCost W R C
  unfold linObjectBlockCost
  dsimp only [a, W, R, C, linObjectBlockInput, encFun, GI.Machine.BinOp.eval] at *
  omega

theorem linObjectBlockCost_mono {W V r s c d : ℕ}
    (hW : W ≤ V) (hr : r ≤ s) (hc : c ≤ d) :
    linObjectBlockCost W r c ≤ linObjectBlockCost V s d := by
  unfold linObjectBlockCost
  gcongr
  exact linTabulateCost_mono (by omega) hr (linObjectBlockRowCost_mono (by omega) hc)

theorem linObjectBlockCost_poly : PBU (fun r W c => linObjectBlockCost W r c) := by
  simp only [linObjectBlockCost, linObjectBlockRowCost, linTabulateCost,
    linTabulateRangeCost, linMapBudget]
  norm_poly

theorem linObjectBlockInput_dimensions {p r d : ℕ}
    (M : Fin p → Matrix (Fin r) (Fin d) ℤ) :
    r ≤ (linObjectBlockInput M).wt ∧ d ≤ (linObjectBlockInput M).wt ∧
      p ≤ (linObjectBlockInput M).wt := by
  have hr := length_lt_wt_list ((List.finRange r).map fun i => Val.nat i.val)
  have hd := length_lt_wt_list ((List.finRange d).map fun i => Val.nat i.val)
  have hp := length_lt_wt_list ((List.finRange p).map fun i => encIntMatrix (M i))
  have wr : (encFun (fun i : Fin r => i.val)).wt < (linObjectBlockInput M).wt :=
    wt_le_wt_list (by simp [linObjectBlockInput])
  have wd : (encFun (fun i : Fin d => i.val)).wt < (linObjectBlockInput M).wt :=
    wt_le_wt_list (by simp [linObjectBlockInput])
  have wp : (Val.list ((List.finRange p).map fun i => encIntMatrix (M i))).wt <
      (linObjectBlockInput M).wt := wt_le_wt_list (by simp [linObjectBlockInput])
  simp only [List.length_map, List.length_finRange] at hr hd hp
  change r < (encFun (fun i : Fin r => i.val)).wt at hr
  change d < (encFun (fun i : Fin d => i.val)).wt at hd
  omega

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem linObjectBlock_spec_poly :
    ∃ K D : ℕ, ∀ {P : Program} {b p r d : ℕ}, linObjectBlockAt P b →
      ∀ M : Fin p → Matrix (Fin r) (Fin d) ℤ,
        FunDet P b (linObjectBlockInput M) (encIntMatrix (linObjectBlockMatrix M))
          (K * ((linObjectBlockInput M).wt + 1) ^ D) := by
  have hpoly : PBU (fun _ W _ => linObjectBlockCost W (W * W) (W * W)) := by
    exact linPoly_subst (f := fun r W c => linObjectBlockCost W r c)
      linObjectBlockCost_poly (PBU.mul PBU.W PBU.W) PBU.W
      (PBU.mul PBU.W PBU.W)
  obtain ⟨K, D, hKD⟩ := linPoly_source_bound hpoly
  refine ⟨K, D, ?_⟩
  intro P b p r d h M
  obtain ⟨hr, hd, hp⟩ := linObjectBlockInput_dimensions M
  exact (linObjectBlock_spec h M).mono
    ((linObjectBlockCost_mono le_rfl (Nat.mul_le_mul hr hp) (Nat.mul_le_mul hd hp)).trans
      (hKD 0 _ _ (Nat.zero_le _) le_rfl))

end GI.Impl
