module

public import Workspace.Impl.LinAffineRows
public import Workspace.Impl.LinIntPad
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-! The explicit homogeneous matrix, with the scalar coordinate last. -/
namespace GI.Impl
open GI.Cited GI.Lang

/-- Extend a dense vector by one final coordinate. -/
def linExtend {α : Type*} {d : ℕ} (x : Fin d → α) (s : α) (i : Fin (d + 1)) : α :=
  if h : i.val < d then x ⟨i.val, h⟩ else s

@[simp] theorem linExtend_castSucc {α : Type*} {d : ℕ} (x : Fin d → α) (s : α) (i : Fin d) :
    linExtend x s i.castSucc = x i := by simp [linExtend, i.isLt]

@[simp] theorem linExtend_last {α : Type*} {d : ℕ} (x : Fin d → α) (s : α) :
    linExtend x s (Fin.last d) = s := by simp [linExtend]

/-- Extension is implemented by snoc, for any scalar encoding. -/
theorem linExtend_value {α : Type*} {d : ℕ} (enc : α → Val) (x : Fin d → α) (s : α) :
    (List.finRange (d + 1)).map (fun i => enc (linExtend x s i)) =
      (List.finRange d).map (fun i => enc (x i)) ++ [enc s] := by
  apply List.ext_getElem (by simp)
  intro k hk hk'
  simp only [List.getElem_map, List.getElem_finRange]
  by_cases hkd : k < d
  · rw [List.getElem_append_left (by simpa using hkd)]
    simp [linExtend, hkd]
  · have he : k = d := by simp only [List.length_map, List.length_finRange] at hk; omega
    subst k
    rw [List.getElem_append_right (by simp)]
    simp [linExtend]

def linAffineMatrix {R : Type*} [Zero R] [One R] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) R) (u : Fin d → R) : Matrix (Fin (d + 1)) (Fin (d + 1)) R :=
  linExtend (fun i => linExtend (A i) (u i)) (linExtend (fun _ => 0) 1)

/-- The dense matrix realizes the affine action after adjoining a scalar. -/
theorem linAffineMatrix_mulVec {R : Type*} [CommRing R] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) R) (u x : Fin d → R) (s : R) :
    (linAffineMatrix A u).mulVec (linExtend x s) = linExtend (A.mulVec x + s • u) s := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
  by_cases hi : i.val < d
  · simp [linAffineMatrix, linExtend, hi, Matrix.mulVec, dotProduct, mul_comm]
  · simp [linAffineMatrix, linExtend, hi]

theorem linAffineMatrix_value {p d : ℕ} (hp : p.Prime)
    (A : Matrix (Fin d) (Fin d) (ZMod p)) (u : Fin d → ZMod p) :
    encModMatrix (linAffineMatrix A u) = .list
      (((List.finRange d).map fun i =>
        .list (((List.finRange d).map fun j => .nat (A i j).val) ++ [.nat (u i).val])) ++
      [.list (List.replicate d (.nat 0) ++ [.nat 1])]) := by
  have hrow (i : Fin d) : encVec (linExtend (A i) (u i)) =
      .list (((List.finRange d).map fun j => .nat (A i j).val) ++ [.nat (u i).val]) :=
    congrArg Val.list (linExtend_value (fun x : ZMod p => .nat x.val) (A i) (u i))
  have hlast : encVec (linExtend (fun _ : Fin d => (0 : ZMod p)) 1) =
      .list (List.replicate d (.nat 0) ++ [.nat 1]) := by
    have hz := congrArg Val.list (linExtend_value (fun x : ZMod p => Val.nat x.val)
      (fun _ : Fin d => (0 : ZMod p)) 1)
    simpa [encVec, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp.one_lt] using hz
  change Val.list ((List.finRange (d + 1)).map (fun i =>
    encVec (linExtend (fun i => linExtend (A i) (u i)) (linExtend (fun _ => 0) 1) i))) = _
  rw [linExtend_value]
  simp only [hrow, hlast]

def linAffineMatrixF (rows rep : ℕ) : Expr :=
  .letE (.call rows (.var 0))
    (.letE (.call rep (mk2 (.length (arg 1)) (.nat 0)))
      (.snoc (.var 1) (.snoc (.var 2) (.nat 1))))

def linAffineMatrixFuns (b : ℕ) : List Expr :=
  [linAffineMatrixF (b + 1) (b + 4)] ++ linAffineRowsFuns (b + 1) ++ replicateFuns (b + 4)

theorem linAffineMatrixFuns_length (b : ℕ) : (linAffineMatrixFuns b).length = 7 := rfl

structure linAffineMatrixAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linAffineMatrixF (b + 1) (b + 4))
  rows : P.HasAt (b + 1) (linAffineRowsFuns (b + 1))
  rep : P.HasAt (b + 4) (replicateFuns (b + 4))

theorem linAffineMatrixAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linAffineMatrixFuns b)) : linAffineMatrixAt P b where
  entry := (h.block (gs := [linAffineMatrixF (b + 1) (b + 4)]) 0 rfl).single
  rows := h.block 1 rfl
  rep := h.block 4 rfl

def linAffineMatrixCost (W d : ℕ) : ℕ :=
  1000 * (W + linAffineRowsCost W d + 100000 * (W + d + 1) ^ 3 + d + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linAffineMatrix_spec {P : Program} {b p d : ℕ} (h : linAffineMatrixAt P b)
    (hp : p.Prime) (A : Matrix (Fin d) (Fin d) (ZMod p)) (u : Fin d → ZMod p) :
    FunDet P b (.list [encModMatrix A, encVec u]) (encModMatrix (linAffineMatrix A u))
      (linAffineMatrixCost (Val.list [encModMatrix A, encVec u]).wt d) := by
  let a := Val.list [encModMatrix A, encVec u]
  let W := a.wt
  let rows := (List.finRange d).map fun i =>
    Val.list (((List.finRange d).map fun j => .nat (A i j).val) ++ [.nat (u i).val])
  let zs := List.replicate d (Val.nat 0)
  have hr := linAffineRows_spec h.rows A u
  have dr := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hr
  have rz := linReplicate_det h.rep d (.nat 0)
  have dl := Det.length (Det.arg' (P := P) (vs := [encModMatrix A, encVec u])
    (rest := [.list rows]) (j := 1) rfl)
  simp only [encVec, List.length_map, List.length_finRange] at dl
  have dz := Det.call (Det.mk2 dl (Det.nat 0)) rz
  have ds := Det.snoc (Det.var' (P := P) (env := [a, .list rows, .list zs]) (i := 1) rfl)
    (Det.snoc (Det.var' (P := P) (env := [a, .list rows, .list zs]) (i := 2) rfl) (Det.nat 1))
  rw [linAffineMatrix_value hp]
  apply FunDet.intro h.entry
  refine (Det.letE dr (Det.letE dz ds)).mono ?_
  have wr := hr.wt_lt.le
  have wz : (Val.list zs).wt ≤ 10 * (d + 1) := by
    have hh := linWtList (vs := zs) (B := 2) (by intro v hv; rw [List.eq_of_mem_replicate hv]; decide)
    simp only [zs, List.length_replicate] at hh
    dsimp only [zs]
    omega
  have wlast := wt_list_snoc_le zs (.nat 1)
  have wout := wt_list_snoc_le rows (.list (zs ++ [.nat 1]))
  have w0 : (Val.nat 0).wt = 2 := by decide
  have w1 : (Val.nat 1).wt = 3 := by decide
  have wrep := wt_list2_le (.nat d) (.nat 0)
  have wi := wt_nat_le d
  have wu : (encVec u).wt < W := wt_le_wt_list (by simp [W, a])
  have hrep : loopModK * (d + 1) * ((Val.list [.nat d, .nat 0]).wt + d + (Val.list zs).wt + 1) ≤
      100000 * (W + d + 1) ^ 3 := by
    simp only [loopModK]
    have hh : (Val.list [.nat d, .nat 0]).wt + d + (Val.list zs).wt + 1 ≤ 30 * (W + d + 1) := by omega
    have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 1000 (by omega : d + 1 ≤ W + d + 1)) hh
    nlinarith [Nat.zero_le ((W + d + 1) ^ 3)]
  change _ ≤ linAffineMatrixCost W d
  unfold linAffineMatrixCost
  dsimp only [W, a, rows, zs, encModMatrix, encVec] at *
  omega

theorem linAffineMatrixCost_mono {W V d e : ℕ} (hW : W ≤ V) (hd : d ≤ e) :
    linAffineMatrixCost W d ≤ linAffineMatrixCost V e := by
  simp only [linAffineMatrixCost, linAffineRowsCost, linAffineRowsAcc, linVectorAccWt]
  gcongr

/-- Fixed polynomial bit cost, including construction of the extra row. -/
theorem linAffineMatrixCost_poly : PBU (fun d W _ => linAffineMatrixCost W d) := by
  unfold linAffineMatrixCost linAffineRowsCost linAffineRowsAcc linVectorAccWt
  norm_poly

end GI.Impl
