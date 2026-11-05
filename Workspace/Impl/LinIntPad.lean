module

public import Workspace.Impl.LinHermite
public import Workspace.Lang.Lib.LinIntTake

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

/-- Zero extension has the expected dense row encoding. -/
theorem linPad_value {r c : ℕ} (hcr : c ≤ r) (y : Fin c → ℤ) :
    linVecVal (linPad (r := r) y) = .list
      (((List.finRange c).map fun i => encInt (y i)) ++ List.replicate (r - c) (encInt 0)) := by
  apply congrArg Val.list
  apply List.ext_getElem (by simp; omega)
  intro i hi1 hi2
  simp only [List.getElem_map, List.getElem_finRange]
  by_cases hic : i < c
  · rw [List.getElem_append_left (by simpa using hic)]
    simp only [List.getElem_map, List.getElem_finRange, linPad, Fin.val_cast, ↓reduceDIte]
    split_ifs <;> simp_all
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_replicate, linPad, Fin.val_cast]
    split_ifs <;> simp_all

/-- Replicate with its known output substituted into the cost bound. -/
theorem linReplicate_det {P : Program} {b : ℕ} (h : P.HasAt b (replicateFuns b)) (n : ℕ) (v : Val) :
    FunDet P b (.list [.nat n, v]) (.list (List.replicate n v))
      (loopModK * (n + 1) * ((Val.list [.nat n, v]).wt + n + (Val.list (List.replicate n v)).wt + 1)) :=
  FunAll.mono (replicate_spec h n v) fun w cost hw => ⟨hw.1, by rw [hw.1] at hw; exact hw.2⟩

/-- Input [r,y], with y of length c ≤ r. Append r-c integer zeros. -/
def linPadF (rep append : ℕ) : Expr :=
  .letE (.call rep (mk2 (.arith .sub (arg 0) (.length (arg 1))) linIntZeroE))
    (.call append (mk2 (arg 1) (.var 1)))

def linPadCost (W r : ℕ) : ℕ := 10 ^ 6 * (W + r + 1) ^ 4

set_option maxHeartbeats 1000000 in
theorem linPad_spec {P : Program} {f rep append r c : ℕ}
    (hf : P.funs[f]? = some (linPadF rep append)) (hr : P.HasAt rep (replicateFuns rep))
    (ha : P.HasAt append (appendFuns append)) (hcr : c ≤ r) (y : Fin c → ℤ) :
    FunDet P f (.list [.nat r, linVecVal y]) (linVecVal (linPad (r := r) y))
      (linPadCost (Val.list [.nat r, linVecVal y]).wt r) := by
  let W := (Val.list [.nat r, linVecVal y]).wt
  let zeros := List.replicate (r - c) (encInt 0)
  let out := ((List.finRange c).map fun i => encInt (y i)) ++ zeros
  have dr := Det.arg' (P := P) (vs := [.nat r, linVecVal y]) (rest := []) (j := 0) rfl
  have dy := Det.arg' (P := P) (vs := [.nat r, linVecVal y]) (rest := []) (j := 1) rfl
  have dl := Det.length dy
  simp only [List.length_map, List.length_finRange] at dl
  have dn := Det.arith (op := .sub) dr dl
  have dz := Det.mk2 (Det.nat (P := P) (env := [.list [.nat r, linVecVal y]]) 0) Det.nil
  have dc := Det.call (Det.mk2 dn dz) (linReplicate_det hr (r - c) (encInt 0))
  have da := Det.call (Det.mk2
    (Det.arg' (P := P) (vs := [.nat r, linVecVal y]) (rest := [.list zeros]) (j := 1) rfl)
    (Det.var' (P := P) (env := [.list [.nat r, linVecVal y], .list zeros]) (i := 1) rfl))
    (linAppend_det ha ((List.finRange c).map fun i => encInt (y i)) zeros)
  rw [linPad_value hcr]
  apply FunDet.intro hf
  refine (Det.letE dc da).mono ?_
  have wy : (linVecVal y).wt < W := wt_le_wt_list (by simp)
  have wz0 : (encInt 0).wt ≤ 100 := by decide
  have wz := linWtList (vs := zeros) (B := 100) (by
    intro v hv
    have he : v = encInt 0 := List.eq_of_mem_replicate hv
    rw [he]; exact wz0)
  have hout := linWtList (vs := out) (B := W + 100) (by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
      exact ((linVecEntryWt y i).trans wy).le.trans (by omega)
    · have he : v = encInt 0 := List.eq_of_mem_replicate hv
      rw [he]; omega)
  have hzlen : zeros.length = r - c := List.length_replicate ..
  have holen : out.length = r := by
    simp only [out, List.length_append, List.length_map, List.length_finRange, hzlen]
    omega
  rw [hzlen] at wz
  rw [holen] at hout
  have wrepArg := wt_list2_le (.nat (r - c)) (encInt 0)
  have wn := wt_nat_le (r - c)
  have wappArg := wt_list2_le (linVecVal y) (.list zeros)
  have hRep : loopModK * (r - c + 1) * ((Val.list [.nat (r - c), encInt 0]).wt + (r - c) +
      (Val.list zeros).wt + 1) ≤ 1000 * (r + 1) * (204 * r + 215) := by
    simp only [loopModK]
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_left 1000 (by omega)
    · omega
  have hApp : loopModK * (zeros.length + 1) *
      ((Val.list [linVecVal y, .list zeros]).wt + zeros.length + (Val.list out).wt + 1) ≤
      1000 * (r + 1) * (2 * W + 500 * r + 2 * (r * (W + 100)) + 100) := by
    rw [hzlen]
    simp only [loopModK]
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_left 1000 (by omega)
    · omega
  have w0 : (Val.nat 0).wt = 2 := rfl
  have wnil : (Val.list []).wt = 4 := rfl
  have hzero : Val.list [.nat 0, .list []] = encInt 0 := rfl
  rw [hzero]
  simp only [GI.Machine.BinOp.eval_sub, List.length_map, List.length_finRange]
  unfold linPadCost
  change _ ≤ 10 ^ 6 * (W + r + 1) ^ 4
  change (Val.list out).wt ≤ 2 * (r * (W + 100)) + r + 4 at hout
  change (Val.list zeros).wt ≤ 2 * ((r - c) * 100) + (r - c) + 4 at wz
  have hyval : Val.list ((List.finRange c).map fun i => encInt (y i)) = linVecVal y := rfl
  have houtval : Val.list (((List.finRange c).map fun i => encInt (y i)) ++ zeros) = Val.list out := rfl
  rw [hyval, houtval]
  have hwr : (Val.nat (r - c)).wt ≤ r + 2 := by omega
  simp only [W, zeros, out, linVecVal] at *
  ring_nf at *
  omega

end GI.Impl
