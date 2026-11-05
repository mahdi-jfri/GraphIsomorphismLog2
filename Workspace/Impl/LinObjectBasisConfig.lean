module

public import Workspace.Impl.LinObjectBasisPiece
public import Workspace.Impl.LinObjectQuotientBuild

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

def linObjectBasisConfigItemF (piece : ℕ) : Expr :=
  .call piece (.snoc (mk4 (.get (arg 0) (.nat 0)) (.length (.get (arg 0) (.nat 1)))
    (arg 1) (.get (arg 0) (.nat 2))) (.get (.get (arg 0) (.nat 1)) (arg 1)))

def linObjectBasisConfigF (range map : ℕ) : Expr :=
  .letE (.call range (.length (arg 1))) (.call map (mk2 (.var 0) (.var 1)))

def linObjectBasisConfigFuns (b shift : ℕ) : List Expr :=
  [linObjectBasisConfigF (b + 38) (b + 1)] ++ mapFuns (b + 1) (b + 4) ++
    [linObjectBasisConfigItemF (b + 5)] ++ linObjectBasisPieceFuns (b + 5) shift ++ rangeFuns (b + 38)

theorem linObjectBasisConfigFuns_length (b shift : ℕ) : (linObjectBasisConfigFuns b shift).length = 41 := by
  simp only [linObjectBasisConfigFuns, List.length_append, List.length_cons, List.length_nil,
    linObjectBasisPieceFuns_length]
  rfl

structure linObjectBasisConfigAt (P : Program) (b shift : ℕ) : Prop where
  entry : P.funs[b]? = some (linObjectBasisConfigF (b + 38) (b + 1))
  map : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4))
  item : P.funs[b + 4]? = some (linObjectBasisConfigItemF (b + 5))
  piece : linObjectBasisPieceAt P (b + 5) shift
  range : P.HasAt (b + 38) (rangeFuns (b + 38))

theorem linObjectBasisConfigAt_of {P : Program} {b shift : ℕ}
    (h : P.HasAt b (linObjectBasisConfigFuns b shift)) : linObjectBasisConfigAt P b shift where
  entry := (h.block (gs := [linObjectBasisConfigF (b + 38) (b + 1)]) 0 rfl).single
  map := h.block 1 rfl
  item := (h.block (gs := [linObjectBasisConfigItemF (b + 5)]) 4 rfl).single
  piece := linObjectBasisPieceAt_of (h.block 5 rfl)
  range := h.block 38 rfl

def linObjectBasisConfigItemCost (W C : ℕ) : ℕ :=
  1000000 * (W + linObjectBasisPieceCost (100 * (W + 1)) C + 1)

def linObjectBasisConfigCost (W C : ℕ) : ℕ :=
  1000000 * ((W + 1) ^ 2 + W + linTabulateRangeCost W +
    linMapBudget (100 * (W + 1) ^ 2) (linObjectBasisConfigItemCost (100 * (W + 1)) C) + 1)

theorem linObjectBasisPieceCost_mono {W V C D : ℕ} (hW : W ≤ V) (hC : C ≤ D) :
    linObjectBasisPieceCost W C ≤ linObjectBasisPieceCost V D := by
  have hr : linObjectBasisPieceRowBudget W ≤ linObjectBasisPieceRowBudget V :=
    linObjectVectorRowCost_mono (by omega)
  have ha : linObjectBasisPieceWordArg W ≤ linObjectBasisPieceWordArg V := by
    unfold linObjectBasisPieceWordArg
    omega
  have hw := linPermWordCost_mono ha
  unfold linObjectBasisPieceCost linObjectBasisPieceWordBudget
  omega

theorem linObjectBasisConfigItemCost_mono {W V C D : ℕ} (hW : W ≤ V) (hC : C ≤ D) :
    linObjectBasisConfigItemCost W C ≤ linObjectBasisConfigItemCost V D := by
  have hh := linObjectBasisPieceCost_mono (show 100 * (W + 1) ≤ 100 * (V + 1) by omega) hC
  unfold linObjectBasisConfigItemCost
  omega

set_option maxHeartbeats 50000 in
set_option maxRecDepth 200 in
theorem linObjectBasisConfigCost_poly : PBU (fun _ W C => linObjectBasisConfigCost W C) := by
  have hi : PBU (fun _ W C => linObjectBasisConfigItemCost W C) :=
    PBU.smul 1000000 (PBU.addc (PBU.add PBU.W
      (linPoly_subst (f := fun _ W C => linObjectBasisPieceCost W C) linObjectBasisPieceCost_poly
        (PBU.const 0) (PBU.smul 100 (PBU.addc PBU.W 1)) PBU.B)) 1)
  have hitem : PBU (fun _ W C => linObjectBasisConfigItemCost (100 * (W + 1)) C) :=
    linPoly_subst (f := fun _ W C => linObjectBasisConfigItemCost W C) hi (PBU.const 0) (PBU.smul 100 (PBU.addc PBU.W 1)) PBU.B
  have hm : PBU (fun _ W C => linMapBudget (100 * (W + 1) ^ 2)
      (linObjectBasisConfigItemCost (100 * (W + 1)) C)) := by
    unfold linMapBudget
    simpa only [Nat.mul_assoc] using PBU.smul 10000 (PBU.mul
      (PBU.pow (PBU.addc (PBU.smul 100 (PBU.pow (PBU.addc PBU.W 1) 2)) 1) 2)
      (PBU.addc (PBU.add hitem (PBU.smul 100 (PBU.pow (PBU.addc PBU.W 1) 2))) 1))
  have hr : PBU (fun _ W _ => linTabulateRangeCost W) := by unfold linTabulateRangeCost; norm_poly
  exact PBU.smul 1000000 (PBU.addc (PBU.add (PBU.add (PBU.add
    (PBU.pow (PBU.addc PBU.W 1) 2) PBU.W) hr) hm) 1)

set_option maxHeartbeats 50000 in
set_option maxRecDepth 200 in
theorem linObjectBasisConfigItem_spec {P : Program} {b shift n p C : ℕ}
    (h : linObjectBasisConfigAt P b shift) (as : List (Equiv.Perm (Fin n)))
    (z : Fin (as.length * p) → ℤ) (Ps : Fin p → Val) (i : Fin p)
    (out : Fin p → Equiv.Perm (Fin n) → Val)
    (hshift : ∀ i a, FunDet P shift (.list [encPerm a, Ps i]) (out i a) C) :
    let ctx := Val.list [encGroup as, .list ((List.finRange p).map Ps), linVecVal z]
    let input := Val.list [ctx, .nat i]
    FunDet P (b + 4) input
      (out i (linGroupWord (fun j => as.get j) (linObjectUnflatten p as.length z i)))
      (linObjectBasisConfigItemCost input.wt C) := by
  let ctx := Val.list [encGroup as, .list ((List.finRange p).map Ps), linVecVal z]
  let input := Val.list [ctx, .nat i]
  let W := input.wt
  have wc : ctx.wt < W := wt_le_wt_list (by simp [input, W])
  have wi : (Val.nat i).wt < W := wt_le_wt_list (by simp [input, W])
  have wa : (encGroup as).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wz : (linVecVal z).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wp : (Val.list ((List.finRange p).map Ps)).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have ws : (Ps i).wt < (Val.list ((List.finRange p).map Ps)).wt :=
    wt_le_wt_list (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  have hp : p ≤ W := by
    have hh := length_lt_wt_list ((List.finRange p).map Ps)
    simp only [List.length_map, List.length_finRange] at hh
    omega
  have hpn := wt_nat_le p
  have harg := wt_list_le [encGroup as, .nat p, .nat i, linVecVal z, Ps i]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at harg
  have hw : (Val.list [encGroup as, .nat p, .nat i, linVecVal z, Ps i]).wt ≤ 100 * (W + 1) := by omega
  have hs := (linObjectBasisPiece_spec h.piece as z i (Ps i) (out i) (hshift i)).mono
    (linObjectBasisPieceCost_mono hw le_rfl)
  have dc := Det.arg' (P := P) (vs := [ctx, .nat i]) (rest := []) (j := 0) rfl
  have di := Det.arg' (P := P) (vs := [ctx, .nat i]) (rest := []) (j := 1) rfl
  have da := Det.get' dc (Det.nat 0) rfl
  have dps := Det.get' dc (Det.nat 1) rfl
  have dz := Det.get' dc (Det.nat 2) rfl
  have dp := Det.length dps
  simp only [List.length_map, List.length_finRange] at dp
  have dpi := Det.get' dps di (v := Ps i) (by simp)
  have dcall := Det.call (Det.snoc (Det.mk4 da dp di dz) dpi) hs
  apply FunAll.intro h.item
  refine dcall.post fun cost hc => ⟨rfl, ?_⟩
  have wo := hs.wt_lt.le
  have wh := wt_list4_le (encGroup as) (.nat p) (.nat i) (linVecVal z)
  change cost ≤ linObjectBasisConfigItemCost W C
  unfold linObjectBasisConfigItemCost
  dsimp only [ctx, input, W] at *
  simp only [List.cons_append, List.nil_append] at *
  omega

set_option maxHeartbeats 50000 in
set_option maxRecDepth 200 in
theorem linObjectBasisConfig_spec {P : Program} {b shift n p C : ℕ}
    (h : linObjectBasisConfigAt P b shift) (as : List (Equiv.Perm (Fin n)))
    (z : Fin (as.length * p) → ℤ) (Ps : Fin p → Val)
    (out : Fin p → Equiv.Perm (Fin n) → Val)
    (hshift : ∀ i a, FunDet P shift (.list [encPerm a, Ps i]) (out i a) C) :
    let input := Val.list [encGroup as, .list ((List.finRange p).map Ps), linVecVal z]
    FunDet P b input
      (.list ((List.finRange p).map fun i =>
        out i (linGroupWord (fun j => as.get j) (linObjectUnflatten p as.length z i))))
      (linObjectBasisConfigCost input.wt C) := by
  let input := Val.list [encGroup as, .list ((List.finRange p).map Ps), linVecVal z]
  let W := input.wt
  let f := fun i => out i (linGroupWord (fun j => as.get j) (linObjectUnflatten p as.length z i))
  let IB := linObjectBasisConfigItemCost (100 * (W + 1)) C
  have wp : (Val.list ((List.finRange p).map Ps)).wt < W := wt_le_wt_list (by simp [input, W])
  have hp : p ≤ W := by
    have hh := length_lt_wt_list ((List.finRange p).map Ps)
    simp only [List.length_map, List.length_finRange] at hh
    omega
  have hi : ∀ i : Fin p, FunDet P (b + 4) (.list [input, .nat i]) (f i) IB := by
    intro i
    have hh := wt_list2_le input (.nat i)
    have hin := wt_nat_le i.val
    have hilt := i.isLt
    exact (linObjectBasisConfigItem_spec h as z Ps i out hshift).mono
      (linObjectBasisConfigItemCost_mono (by
        change (Val.list [input, .nat i]).wt ≤ 100 * (W + 1)
        omega) le_rfl)
  have hm := linMapEncoded_spec h.map (fun i : Fin p => Val.nat i.val)
    (fun _ _ he => Fin.ext (Val.nat.inj he)) f input (List.finRange p) IB (fun i _ => hi i)
  have dp := Det.length (Det.arg' (P := P)
    (vs := [encGroup as, .list ((List.finRange p).map Ps), linVecVal z]) (rest := []) (j := 1) rfl)
  simp only [List.length_map, List.length_finRange] at dp
  have dr := Det.call dp (linRange_spec h.range p)
  have hinc : p + 1 ≤ W + 1 := Nat.add_le_add_right hp 1
  have hsquare : (p + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left hinc 2
  have hr : linTabulateRangeCost p ≤ linTabulateRangeCost W := by
    unfold linTabulateRangeCost
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 10000 hinc) (by omega)
  have wids : (encFun (fun i : Fin p => i.val)).wt ≤ 4 * (W + 1) ^ 2 :=
    (wt_ids_le p).trans (Nat.mul_le_mul_left 4 hsquare)
  have ha : (Val.list [input, encFun (fun i : Fin p => i.val)]).wt ≤ 100 * (W + 1) ^ 2 := by
    have hh := wt_list2_le input (encFun (fun i : Fin p => i.val))
    have hsq : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by decide) _
    nlinarith
  have hm' := hm.mono (linMapBudget_mono ha le_rfl)
  apply FunAll.intro h.entry
  apply EvalAll.letE dr
  intro v cr hv
  obtain ⟨rfl, hcr⟩ := hv
  have dm := Det.call (Det.mk2 (Det.var' (P := P)
    (env := [input, encFun (fun i : Fin p => i.val)]) (i := 0) rfl)
    (Det.var' (P := P) (env := [input, encFun (fun i : Fin p => i.val)]) (i := 1) rfl)) hm'
  refine dm.post fun cost hc => ⟨rfl, ?_⟩
  have wo := hm'.wt_lt.le
  have hw := wt_list2_le input (encFun (fun i : Fin p => i.val))
  change _ ≤ linObjectBasisConfigCost W C
  unfold linObjectBasisConfigCost
  dsimp only [input, W, IB, encFun] at *
  omega

end GI.Impl
