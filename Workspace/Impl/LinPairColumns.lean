module

public import Workspace.Impl.LinMapSource
public import Workspace.Impl.LinPrimaryRecord

@[expose] public section

/-! Separate the two columns of a list of value pairs. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linPairColumnsGetF : Expr := .get (arg 1) (arg 0)
def linPairColumnsF (map : ℕ) : Expr :=
  .letE (.call map (mk2 (.nat 0) (.var 0)))
    (.letE (.call map (mk2 (.nat 1) (.var 0))) (mk2 (.var 1) (.var 2)))
def linPairColumnsFuns (b : ℕ) : List Expr :=
  [linPairColumnsF (b + 1)] ++ mapFuns (b + 1) (b + 4) ++ [linPairColumnsGetF]

theorem linPairColumnsFuns_length (b : ℕ) : (linPairColumnsFuns b).length = 5 := rfl

structure linPairColumnsAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linPairColumnsF (b + 1))
  map : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4))
  cell : P.funs[b + 4]? = some linPairColumnsGetF

theorem linPairColumnsAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linPairColumnsFuns b)) : linPairColumnsAt P b where
  entry := (h.block (gs := [linPairColumnsF (b + 1)]) 0 rfl).single
  map := h.block 1 rfl
  cell := (h.block (gs := [linPairColumnsGetF]) 4 rfl).single

def linPairColumnsVal (xs : List (Val × Val)) : Val :=
  .list (xs.map fun x => .list [x.1, x.2])
def linPairColumnsBudget (W : ℕ) : ℕ := linMapBudget (100 * (W + 1)) (100 * (W + 1))
def linPairColumnsCost (W : ℕ) : ℕ := 100000 * (W + linPairColumnsBudget W + 1)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 5000 in
theorem linPairColumns_spec {P : Program} {b : ℕ} (h : linPairColumnsAt P b)
    (xs : List (Val × Val)) :
    FunDet P b (linPairColumnsVal xs) (.list [.list (xs.map Prod.fst), .list (xs.map Prod.snd)])
      (linPairColumnsCost (linPairColumnsVal xs).wt) := by
  let a := linPairColumnsVal xs
  let W := a.wt
  let L := Val.list (xs.map Prod.fst)
  let R := Val.list (xs.map Prod.snd)
  have hpairs (x : Val × Val) (hx : x ∈ xs) : (Val.list [x.1, x.2]).wt < W :=
    wt_le_wt_list (List.mem_map.mpr ⟨x, hx, rfl⟩)
  have hcell (k : ℕ) (hk : k = 0 ∨ k = 1) (x : Val × Val) (hx : x ∈ xs) :
      FunDet P (b + 4) (.list [.nat k, .list [x.1, x.2]])
        (if k = 0 then x.1 else x.2) (100 * (W + 1)) := by
    have wpair := hpairs x hx
    have wx : x.1.wt < (Val.list [x.1, x.2]).wt := wt_le_wt_list (by simp)
    have wy : x.2.wt < (Val.list [x.1, x.2]).wt := wt_le_wt_list (by simp)
    have wenv := wt_list2_le (.nat k) (.list [x.1, x.2])
    have wk := wt_nat_le k
    have darg := Det.arg' (P := P) (vs := [.nat k, .list [x.1, x.2]]) (rest := []) (j := 1) rfl
    have didx := Det.arg' (P := P) (vs := [.nat k, .list [x.1, x.2]]) (rest := []) (j := 0) rfl
    rcases hk with rfl | rfl
    · apply FunDet.intro h.cell
      exact (Det.get' darg didx rfl).mono (by omega)
    · apply FunDet.intro h.cell
      exact (Det.get' darg didx rfl).mono (by omega)
  have hL := linMapSource_spec h.map (fun x : Val × Val => .list [x.1, x.2])
    Prod.fst (.nat 0) xs (100 * (W + 1)) (fun x hx => by simpa using hcell 0 (Or.inl rfl) x hx)
  have hR := linMapSource_spec h.map (fun x : Val × Val => .list [x.1, x.2])
    Prod.snd (.nat 1) xs (100 * (W + 1)) (fun x hx => by simpa using hcell 1 (Or.inr rfl) x hx)
  have wa0 : (Val.list [.nat 0, a]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (.nat 0) a
    have hz : (Val.nat 0).wt = 2 := rfl
    dsimp only [W]
    omega
  have wa1 : (Val.list [.nat 1, a]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (.nat 1) a
    have hz : (Val.nat 1).wt = 3 := rfl
    dsimp only [W]
    omega
  have hm0 := hL.mono (show linMapBudget (Val.list [.nat 0, a]).wt (100 * (W + 1)) ≤
    linPairColumnsBudget W by simp only [linPairColumnsBudget, linMapBudget]; gcongr)
  have hm1 := hR.mono (show linMapBudget (Val.list [.nat 1, a]).wt (100 * (W + 1)) ≤
    linPairColumnsBudget W by simp only [linPairColumnsBudget, linMapBudget]; gcongr)
  have wL : L.wt ≤ linPairColumnsBudget W := hm0.wt_lt.le
  have wR : R.wt ≤ linPairColumnsBudget W := hm1.wt_lt.le
  have d0 := Det.call (Det.mk2 (Det.nat 0) (Det.var' (P := P) (env := [a]) (i := 0) rfl)) hm0
  have d1 := Det.call (Det.mk2 (Det.nat 1) (Det.var' (P := P) (env := [a, L]) (i := 0) rfl)) hm1
  have dout := Det.mk2
    (Det.var' (P := P) (env := [a, L, R]) (i := 1) rfl)
    (Det.var' (P := P) (env := [a, L, R]) (i := 2) rfl)
  apply FunDet.intro h.entry
  refine (Det.letE d0 (Det.letE d1 dout)).mono ?_
  have wo := wt_list2_le L R
  have w0 := wt_list2_le (.nat 0) a
  have w1 := wt_list2_le (.nat 1) a
  change _ ≤ linPairColumnsCost W
  unfold linPairColumnsCost
  dsimp only [W, a, L, R, linPairColumnsVal] at *
  omega

theorem linPairColumnsCost_mono {W V : ℕ} (h : W ≤ V) :
    linPairColumnsCost W ≤ linPairColumnsCost V := by
  unfold linPairColumnsCost linPairColumnsBudget linMapBudget
  gcongr

theorem linPairColumnsCost_poly : PBU (fun _ W _ => linPairColumnsCost W) := by
  unfold linPairColumnsCost linPairColumnsBudget linMapBudget
  norm_poly

end GI.Impl
