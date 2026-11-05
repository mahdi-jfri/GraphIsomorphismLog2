module

public import Workspace.Impl.LinWreathVector
public import Workspace.Impl.LinTabulate

@[expose] public section

/-! Restrict a swapping cover permutation to its first-to-second copy map. -/
namespace GI.Impl
open GI.Cited GI.Lang Equiv

def linWreathExtractPointF : Expr :=
  .arith .sub (.get (.get (arg 0) (.nat 1)) (arg 1)) (.get (arg 0) (.nat 0))

def linWreathExtractF (tab : ℕ) : Expr := .call tab (mk2 (.var 0) (arg 0))

def linWreathExtractFuns (b : ℕ) : List Expr :=
  [linWreathExtractF (b + 2), linWreathExtractPointF] ++ linTabulateFuns (b + 2) (b + 1)

theorem linWreathExtractFuns_length (b : ℕ) : (linWreathExtractFuns b).length = 9 := rfl

structure linWreathExtractAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linWreathExtractF (b + 2))
  point : P.funs[b + 1]? = some linWreathExtractPointF
  tab : linTabulateAt P (b + 2) (b + 1)

theorem linWreathExtractAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linWreathExtractFuns b)) : linWreathExtractAt P b where
  entry := (h.block (gs := [linWreathExtractF (b + 2)]) 0 rfl).single
  point := (h.block (gs := [linWreathExtractPointF]) 1 rfl).single
  tab := linTabulateAt_of (h.block 2 rfl)

theorem linWreathExtractPoint_spec {P : Program} {f n : ℕ}
    (hf : P.funs[f]? = some linWreathExtractPointF)
    (σ : Perm (Fin (n + n))) (i : Fin n) :
    FunDet P f (.list [.list [.nat n, encPerm σ], .nat i])
      (.nat ((σ (i.castAdd n) : ℕ) - n))
      (1000 * ((Val.list [.list [.nat n, encPerm σ], .nat i]).wt + n + 1)) := by
  let c := Val.list [.nat n, encPerm σ]
  let a := Val.list [c, .nat i]
  have dc := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 0) rfl
  have di := Det.arg' (P := P) (vs := [c, .nat i]) (rest := []) (j := 1) rfl
  have dp := Det.get' dc (Det.nat 1) rfl
  have dn := Det.get' dc (Det.nat 0) rfl
  have dg := Det.get dp di (by simp [encPerm]; have := i.isLt; omega)
  simp only [List.getElem_map, List.getElem_finRange] at dg
  have hmk (hi : i.val < n + n) :
      (⟨i.val, hi⟩ : Fin (n + n)) = i.castAdd n := by apply Fin.ext; rfl
  simp only [Fin.cast_mk, hmk] at dg
  change Det P [Val.list [c, .nat i]] _ (.nat (σ (i.castAdd n))) _ at dg
  have dd := Det.arith (op := .sub) dg dn
  apply FunDet.intro hf
  refine dd.mono ?_
  have wc : c.wt < a.wt := wt_le_wt_list (by simp [a])
  have wp : (encPerm σ).wt < c.wt := wt_le_wt_list (by simp [c])
  have wn := wt_nat_le n
  have wi := wt_nat_le i.val
  have wo := wt_nat_le (σ (i.castAdd n) : ℕ)
  have ws := wt_nat_le ((σ (i.castAdd n) : ℕ) - n)
  have hi := i.isLt
  have ho := (σ (i.castAdd n)).isLt
  change _ ≤ 1000 * (a.wt + n + 1)
  dsimp only [a, c, encPerm] at *
  simp only [GI.Machine.BinOp.eval_sub]
  omega

def linWreathExtractCost (W n : ℕ) : ℕ :=
  10000 * (W + n + linTabulateCost (100 * (W + n + 1)) n
    (1000 * (100 * (W + n + 1) + n + 1)) + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linWreathExtract_spec {P : Program} {b n : ℕ} (h : linWreathExtractAt P b)
    (gs : List (Perm (Fin n))) (a : gens gs ≀ᵣ linTwo) (hs : a.right = linTwoSwap) :
    FunDet P b (.list [.nat n, encPerm (linWreathFinCover (n := n) (gens gs) a)])
      (encPerm (a.left linTwoSwap).val)
      (linWreathExtractCost (Val.list [.nat n, encPerm (linWreathFinCover (n := n) (gens gs) a)]).wt n) := by
  let σ := linWreathFinCover (n := n) (gens gs) a
  let v := Val.list [.nat n, encPerm σ]
  let W := v.wt
  have hv : (Val.list [v, .nat n]).wt ≤ 100 * (W + n + 1) := by
    have hh := wt_list2_le v (.nat n)
    have hn := wt_nat_le n
    omega
  have hi (i : Fin n) : (Val.list [v, .nat i]).wt ≤ 100 * (W + n + 1) := by
    have hh := wt_list2_le v (.nat i)
    have hn := wt_nat_le i.val
    have := i.isLt
    omega
  have hpoint (i : Fin n) := linWreathExtractPoint_spec h.point σ i
  have he (i : Fin n) : ((σ (i.castAdd n) : ℕ) - n) = ((a.left linTwoSwap).val i : ℕ) := by
    dsimp only [σ]
    rw [linWreathFinCover_extract a hs]
    simp only [Fin.val_natAdd, Nat.add_sub_cancel_left]
    rfl
  have ht := linTabulate_spec h.tab v (fun i : Fin n => Val.nat ((a.left linTwoSwap).val i))
    (1000 * (100 * (W + n + 1) + n + 1)) (fun i => by
      have hh := hpoint i
      rw [he i] at hh
      exact hh.mono (Nat.mul_le_mul_left _ (by have hx := hi i; change (Val.list [v, .nat i]).wt + n + 1 ≤ _; omega)))
  have ht' := ht.mono (linTabulateCost_mono hv le_rfl le_rfl)
  have dn := Det.arg' (P := P) (vs := [.nat n, encPerm σ]) (rest := []) (j := 0) rfl
  have dd := Det.call (Det.mk2 (Det.var' (P := P) (env := [v]) (i := 0) rfl) dn) ht'
  apply FunDet.intro h.entry
  refine dd.mono ?_
  have wo := ht'.wt_lt.le
  have hw := wt_list2_le v (.nat n)
  have wn := wt_nat_le n
  change _ ≤ linWreathExtractCost W n
  dsimp only [linWreathExtractCost]
  dsimp only [W, v, σ, encPerm] at *
  omega

theorem linWreathExtractCost_poly : PBU (fun n W _ => linWreathExtractCost W n) := by
  unfold linWreathExtractCost linTabulateCost linTabulateRangeCost linMapBudget
  norm_poly

end GI.Impl
