import Workspace.Impl.LinIntPad
import Workspace.Impl.LinMapEncoded

namespace GI.Impl
open GI.Cited GI.Lang

def linZeroModMatrixF (rep : ℕ) : Expr :=
  .letE (.call rep (mk2 (.var 0) (.nat 0))) (.call rep (mk2 (.var 0) (.var 1)))

def linZeroModMatrixFuns (b : ℕ) : List Expr :=
  [linZeroModMatrixF (b + 1)] ++ replicateFuns (b + 1)

theorem linZeroModMatrixFuns_length (b : ℕ) : (linZeroModMatrixFuns b).length = 4 := rfl

def linZeroModMatrixCost (d : ℕ) : ℕ :=
  100000 * (d + 1) * (100 * (d + 1) ^ 2 + 100 * (d + 1) + 1)

set_option maxHeartbeats 1000000 in
theorem linZeroModMatrix_spec {P : Program} {b : ℕ}
    (h : P.HasAt b (linZeroModMatrixFuns b)) (p d : ℕ) :
    FunDet P b (.nat d) (encModMatrix (0 : Matrix (Fin d) (Fin d) (ZMod p)))
      (linZeroModMatrixCost d) := by
  let row := List.replicate d (Val.nat 0)
  let rows := List.replicate d (Val.list row)
  have wrow : (Val.list row).wt ≤ 10 * (d + 1) := by
    have hh := linWtList (vs := row) (B := 2) (by
      intro v hv; rw [List.eq_of_mem_replicate hv]; rfl)
    have hlen : row.length = d := by simp [row]
    rw [hlen] at hh
    change (Val.list row).wt ≤ _ at hh
    omega
  have wrows : (Val.list rows).wt ≤ 100 * (d + 1) ^ 2 := by
    have hh := linWtList (vs := rows) (B := 10 * (d + 1)) (by
      intro v hv; rw [List.eq_of_mem_replicate hv]; exact wrow)
    have hlen : rows.length = d := by simp [rows]
    rw [hlen] at hh
    change (Val.list rows).wt ≤ _ at hh
    nlinarith
  have warg₁ := wt_list2_le (.nat d) (.nat 0)
  have warg₂ := wt_list2_le (.nat d) (.list row)
  have wd := wt_nat_le d
  have w0 : (Val.nat 0).wt = 2 := rfl
  have hr := linReplicate_det (h.block 1 rfl) d (.nat 0)
  have hm := linReplicate_det (h.block 1 rfl) d (.list row)
  have dr := Det.call (Det.mk2 (Det.var' (P := P) (env := [.nat d]) (i := 0) rfl) (Det.nat 0)) hr
  have dm := Det.call (Det.mk2
    (Det.var' (P := P) (env := [.nat d, .list row]) (i := 0) rfl)
    (Det.var' (P := P) (env := [.nat d, .list row]) (i := 1) rfl)) hm
  have he : encModMatrix (0 : Matrix (Fin d) (Fin d) (ZMod p)) = .list rows := by
    simp [encModMatrix, encVec, rows, row]
  rw [he]
  apply FunDet.intro (h.block (gs := [linZeroModMatrixF (b + 1)]) 0 rfl).single
  refine (Det.letE dr dm).mono ?_
  change _ ≤ linZeroModMatrixCost d
  unfold linZeroModMatrixCost
  dsimp only [row, rows] at *
  simp only [loopModK]
  nlinarith [Nat.mul_le_mul_left (1000 * (d + 1)) warg₁,
    Nat.mul_le_mul_left (1000 * (d + 1)) warg₂]

theorem linZeroModMatrixCost_poly : PBU (fun d _ _ => linZeroModMatrixCost d) := by
  unfold linZeroModMatrixCost
  norm_poly

end GI.Impl
