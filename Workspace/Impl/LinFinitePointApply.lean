module

public import Workspace.Impl.LinMatrixVec
public import Workspace.Impl.LinFinitePointReduce
public import Workspace.Impl.LinFiniteActionCost

@[expose] public section

/-! Apply a retained full affine transformation to a retained full point.
Reduction takes place after the integer dot products, including modulus zero
on the final homogeneous scalar. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linFinitePointApplyF (mul rem : ℕ) : Expr :=
  .letE (.call mul (mk2 (arg 1) (.get (arg 0) (.nat 1))))
    (.call rem (mk2 (.var 1) (.get (arg 0) (.nat 0))))

def linFinitePointApplyFuns (b : ℕ) : List Expr :=
  [linFinitePointApplyF (b + 1) (b + 26)] ++ linMatrixVecFuns (b + 1) ++ linFiniteReduceFuns (b + 26)

theorem linFinitePointApplyFuns_length (b : ℕ) : (linFinitePointApplyFuns b).length = 47 := rfl

structure linFinitePointApplyAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linFinitePointApplyF (b + 1) (b + 26))
  mul : linMatrixVecAt P (b + 1)
  rem : P.HasAt (b + 26) (linFiniteReduceFuns (b + 26))

theorem linFinitePointApplyAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linFinitePointApplyFuns b)) : linFinitePointApplyAt P b where
  entry := (h.block (gs := [linFinitePointApplyF (b + 1) (b + 26)]) 0 rfl).single
  mul := linMatrixVecAt_of (h.block 1 rfl)
  rem := h.block 26 rfl

def linFinitePointApplyMulBudget (W : ℕ) : ℕ := linMatrixVecCost (100 * (W + 1)) W
def linFinitePointApplyRemArg (W : ℕ) : ℕ := 100 * (W + linFinitePointApplyMulBudget W + 1)
def linFinitePointApplyRemBudget (W : ℕ) : ℕ := linFinitePointReduceCost (linFinitePointApplyRemArg W) W

def linFinitePointApplyCost (W : ℕ) : ℕ :=
  100000 * (W + linFinitePointApplyMulBudget W + linFinitePointApplyRemBudget W + 1)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 5000 in
theorem linFinitePointApply_spec {P : Program} {b d : ℕ} (h : linFinitePointApplyAt P b)
    (m : Fin d → ℕ) (hm : ∀ i, 0 < m i) (f : linFiniteVec m →+ linFiniteVec m)
    (u x : linFiniteVec m) (inv : Val) :
    let record := Val.list [linVecVal (linFiniteModuli m), encIntMatrix (linFiniteHomogeneous m f u), inv]
    let a := Val.list [record, linFinitePointVal m x]
    FunDet P b a (linFinitePointVal m (f x + u)) (linFinitePointApplyCost a.wt) := by
  let record := Val.list [linVecVal (linFiniteModuli m), encIntMatrix (linFiniteHomogeneous m f u), inv]
  let a := Val.list [record, linFinitePointVal m x]
  let W := a.wt
  let point := linExtend (fun i => ((x i).val : ℤ)) 1
  let y := (linFiniteHomogeneous m f u).mulVec point
  have wrec : record.wt < W := wt_le_wt_list (by simp [W, a])
  have wpoint : (linFinitePointVal m x).wt < W := wt_le_wt_list (by simp [W, a])
  have wmat : (encIntMatrix (linFiniteHomogeneous m f u)).wt < record.wt := wt_le_wt_list (by simp [record])
  have wmod : (linVecVal (linFiniteModuli m)).wt < record.wt := wt_le_wt_list (by simp [record])
  have hn : d + 1 ≤ W := by
    have hh := length_lt_wt_list ((List.finRange (d + 1)).map fun i => encInt (point i))
    simp only [List.length_map, List.length_finRange] at hh
    change d + 1 < (linFinitePointVal m x).wt at hh
    omega
  have warg : (Val.list [linVecVal point, encIntMatrix (linFiniteHomogeneous m f u)]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (linVecVal point) (encIntMatrix (linFiniteHomogeneous m f u))
    change (linVecVal point).wt < W at wpoint
    omega
  have hmul : FunDet P (b + 1) (.list [linVecVal point, encIntMatrix (linFiniteHomogeneous m f u)])
      (linVecVal y) (linFinitePointApplyMulBudget W) :=
    (linMatrixVec_spec h.mul (linFiniteHomogeneous m f u) point).mono (linMatrixVecCost_mono warg hn)
  have wy := hmul.wt_lt.le
  have wrem : (Val.list [linVecVal y, linVecVal (linFiniteModuli m)]).wt ≤ linFinitePointApplyRemArg W := by
    have hh := wt_list2_le (linVecVal y) (linVecVal (linFiniteModuli m))
    unfold linFinitePointApplyRemArg
    omega
  have hlast : y (Fin.last d) = 1 := linFiniteHomogeneous_last m f u x
  have hrem := (linFinitePointReduce_spec h.rem m hm y hlast).mono
    (linFinitePointReduceCost_mono wrem hn)
  have he : (fun i => y i % linFiniteModuli m i) = linExtend (fun i => (((f x + u) i).val : ℤ)) 1 :=
    linFiniteHomogeneous_apply m hm f u x
  rw [he] at hrem
  change FunDet P (b + 26) (.list [linVecVal y, linVecVal (linFiniteModuli m)])
    (linFinitePointVal m (f x + u)) (linFinitePointApplyRemBudget W) at hrem
  have wo := hrem.wt_lt.le
  have dr := Det.arg' (P := P) (vs := [record, linFinitePointVal m x]) (rest := []) (j := 0) rfl
  have dx := Det.arg' (P := P) (vs := [record, linFinitePointVal m x]) (rest := []) (j := 1) rfl
  have dm := Det.get' dr (Det.nat 1) rfl
  have dmul := Det.call (Det.mk2 dx dm) hmul
  have dr' := Det.arg' (P := P) (vs := [record, linFinitePointVal m x]) (rest := [linVecVal y]) (j := 0) rfl
  have dmod := Det.get' dr' (Det.nat 0) rfl
  have drem := Det.call (Det.mk2
    (Det.var' (P := P) (env := [a, linVecVal y]) (i := 1) rfl) dmod) hrem
  apply FunDet.intro h.entry
  refine (Det.letE dmul drem).mono ?_
  have wi := wt_list2_le (linVecVal point) (encIntMatrix (linFiniteHomogeneous m f u))
  have wi' := wt_list2_le (linVecVal y) (linVecVal (linFiniteModuli m))
  change _ ≤ linFinitePointApplyCost W
  dsimp only [linFinitePointApplyCost]
  dsimp only [record, a, W, point, linFinitePointVal] at *
  omega

set_option maxRecDepth 8000 in
theorem linFinitePointApplyCost_poly : PBU (fun _ W _ => linFinitePointApplyCost W) := by
  have hm : PBU (fun _ W _ => linFinitePointApplyMulBudget W) :=
    linPoly_subst linMatrixVecCost_poly PBU.W (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  have ha : PBU (fun _ W _ => linFinitePointApplyRemArg W) := PBU.smul 100 (PBU.addc (PBU.add PBU.W hm) 1)
  have hr : PBU (fun _ W _ => linFinitePointApplyRemBudget W) := by
    change PBU (fun _ W _ => linFinitePointReduceCost (linFinitePointApplyRemArg W) W)
    exact linPoly_subst (f := fun n W _ => linFinitePointReduceCost W n) linFinitePointReduceCost_poly PBU.W ha (PBU.const 0)
  exact PBU.smul 100000 (PBU.addc (PBU.add (PBU.add PBU.W hm) hr) 1)

theorem linFinitePointApply_spec_poly :
    ∃ K D : ℕ, ∀ {P : Program} {b d : ℕ}, linFinitePointApplyAt P b →
      ∀ (m : Fin d → ℕ) (hm : ∀ i, 0 < m i) (f : linFiniteVec m →+ linFiniteVec m)
        (u x : linFiniteVec m) (inv : Val),
      let record := Val.list [linVecVal (linFiniteModuli m), encIntMatrix (linFiniteHomogeneous m f u), inv]
      let a := Val.list [record, linFinitePointVal m x]
      FunDet P b a (linFinitePointVal m (f x + u)) (K * (a.wt + 1) ^ D) := by
  obtain ⟨K, D, hKD⟩ := linPoly_source_bound linFinitePointApplyCost_poly
  refine ⟨K, D, ?_⟩
  intro P b d hp m hm f u x inv
  exact (linFinitePointApply_spec hp m hm f u x inv).mono (hKD 0 _ _ (Nat.zero_le _) le_rfl)

end GI.Impl
