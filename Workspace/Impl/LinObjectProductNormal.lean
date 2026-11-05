module

public import Workspace.Impl.LinObjectNormal
public import Workspace.Impl.LinObjectNormalMath
public import Workspace.Impl.TermGlueLabQ

@[expose] public section

/-! Assemble the product of local quotients and compute its finite abelian normal
form. The zero-column case is direct and makes no cited normal-form call. -/
namespace GI.Impl
open GI.Cited GI.Lang Matrix

def linObjectProductNormalPositiveF (build normal : ℕ) : Expr :=
  .letE (.call build (.var 0))
    (.call normal (mk3
      (.arith .mul (.length (arg 0)) (.length (arg 2)))
      (.arith .mul (.length (arg 1)) (.length (arg 2))) (.var 1)))

def linObjectProductNormalF (positive : ℕ) : Expr :=
  .ite (.arith .mul (.length (arg 1)) (.length (arg 2)))
    (.call positive (.var 0)) (mk2 .nil .nil)

def linObjectProductNormalFuns (b jh js : ℕ) : List Expr :=
  [linObjectProductNormalF (b + 1), linObjectProductNormalPositiveF (b + 2) (b + 19)] ++
    linObjectBlockFuns (b + 2) ++ tmGLQFuns (b + 19) jh js

theorem linObjectProductNormalFuns_length (b jh js : ℕ) : (linObjectProductNormalFuns b jh js).length = 28 := rfl

structure linObjectProductNormalAt (P : Program) (b jh js : ℕ) : Prop where
  entry : P.funs[b]? = some (linObjectProductNormalF (b + 1))
  positive : P.funs[b + 1]? = some (linObjectProductNormalPositiveF (b + 2) (b + 19))
  build : linObjectBlockAt P (b + 2)
  normal : P.HasAt (b + 19) (tmGLQFuns (b + 19) jh js)

theorem linObjectProductNormalAt_of {P : Program} {b jh js : ℕ}
    (h : P.HasAt b (linObjectProductNormalFuns b jh js)) : linObjectProductNormalAt P b jh js where
  entry := (h.block (gs := [linObjectProductNormalF (b + 1)]) 0 rfl).single
  positive := (h.block (gs := [linObjectProductNormalPositiveF (b + 2) (b + 19)]) 1 rfl).single
  build := linObjectBlockAt_of (h.block 2 rfl)
  normal := h.block 19 rfl

def linObjectProductFullRankInst {p r d : ℕ}
    (M : Fin p → Matrix (Fin r) (Fin d) ℤ) (hdr : d ≤ r)
    (hM : ∀ i, Function.Injective (M i).mulVec) (hpos : 0 < d * p) : FullRankInst where
  r := r * p
  c := d * p
  c_pos := hpos
  c_le := Nat.mul_le_mul_right p hdr
  A := linObjectBlockMatrix M
  rank := linObjectBlockMatrix_injective M hM

def linObjectProductBuildCost (W : ℕ) : ℕ := linObjectBlockCost W (W * W) (W * W)

theorem linObjectProductBuildCost_poly : PBU (fun _ W _ => linObjectProductBuildCost W) :=
  linPoly_subst (f := fun r W c => linObjectBlockCost W r c)
    linObjectBlockCost_poly (PBU.mul PBU.W PBU.W) PBU.W (PBU.mul PBU.W PBU.W)

def linObjectProductNormalArg (W : ℕ) : ℕ := 100 * (W + linObjectProductBuildCost W + 1)
noncomputable def linObjectProductNormalBudget (hH : HermiteFullRank) (hS : SmithNonsingular) (W : ℕ) : ℕ :=
  tmGLQBudget hH hS (linObjectProductNormalArg W)
noncomputable def linObjectProductNormalCost (hH : HermiteFullRank) (hS : SmithNonsingular) (W : ℕ) : ℕ :=
  1000000 * ((W + 1) ^ 2 + W + linObjectProductBuildCost W + linObjectProductNormalBudget hH hS W + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 5000 in
theorem linObjectProductNormalPositive_spec (hH : HermiteFullRank) (hS : SmithNonsingular)
    {P : Program} {b jh js p r d : ℕ} (h : linObjectProductNormalAt P b jh js)
    (hjh : P.prims[jh]? = some (linHermitePrim hH))
    (hjs : P.prims[js]? = some (linSmithPrim hS))
    (M : Fin p → Matrix (Fin r) (Fin d) ℤ) (hdr : d ≤ r)
    (hM : ∀ i, Function.Injective (M i).mulVec) (hpos : 0 < d * p) :
    let a := linObjectBlockInput M
    FunAll P (b + 1) a (fun out cost => TmGLQOut (linObjectBlockMatrix M) out ∧
      cost ≤ linObjectProductNormalCost hH hS a.wt) := by
  let a := linObjectBlockInput M
  let W := a.wt
  let I := linObjectProductFullRankInst M hdr hM hpos
  let mv := encIntMatrix I.A
  let BC := linObjectProductBuildCost W
  let NC := linObjectProductNormalBudget hH hS W
  obtain ⟨hr, hd, hp⟩ := linObjectBlockInput_dimensions M
  change r ≤ W at hr
  change d ≤ W at hd
  change p ≤ W at hp
  have hb := (linObjectBlock_spec h.build M).mono
    (linObjectBlockCost_mono le_rfl (Nat.mul_le_mul hr hp) (Nat.mul_le_mul hd hp))
  have wm : mv.wt ≤ BC := hb.wt_lt.le
  have hrm : I.r ≤ BC := by
    have hh := length_lt_wt_list ((List.finRange I.r).map fun i => linVecVal (I.A i))
    simp only [List.length_map, List.length_finRange] at hh
    change I.r < mv.wt at hh
    omega
  have hcm : I.c ≤ BC := I.c_le.trans hrm
  have harg : (fullRankInput I).wt ≤ linObjectProductNormalArg W := by
    have hh := wt_list3_le (.nat I.r) (.nat I.c) mv
    have hn := wt_nat_le I.r
    have hc := wt_nat_le I.c
    unfold linObjectProductNormalArg
    change (Val.list [.nat I.r, .nat I.c, mv]).wt ≤ _
    dsimp only [BC] at *
    omega
  have hs := tmGLQ_spec hH hS h.normal hjh hjs I
  have db := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hb
  apply FunAll.intro h.positive
  apply EvalAll.letE db
  intro v cb hv
  obtain ⟨rfl, hcb⟩ := hv
  have dr := Det.length (Det.arg' (P := P) (vs :=
    [encFun (fun i : Fin r => i.val), encFun (fun i : Fin d => i.val),
      .list ((List.finRange p).map fun i => encIntMatrix (M i))]) (rest := [mv]) (j := 0) rfl)
  have dd := Det.length (Det.arg' (P := P) (vs :=
    [encFun (fun i : Fin r => i.val), encFun (fun i : Fin d => i.val),
      .list ((List.finRange p).map fun i => encIntMatrix (M i))]) (rest := [mv]) (j := 1) rfl)
  have dp := Det.length (Det.arg' (P := P) (vs :=
    [encFun (fun i : Fin r => i.val), encFun (fun i : Fin d => i.val),
      .list ((List.finRange p).map fun i => encIntMatrix (M i))]) (rest := [mv]) (j := 2) rfl)
  simp only [encFun, List.length_map, List.length_finRange] at dr dd dp
  have drow := Det.arith' (op := .mul) dr dp rfl
  have dcol := Det.arith' (op := .mul) dd dp rfl
  have dm := Det.var' (P := P) (env := [a, mv]) (i := 1) rfl
  apply EvalAll.call_funAll (Det.mk3 drow dcol dm)
  intro v ca hv
  obtain ⟨rfl, hca⟩ := hv
  refine hs.wt_lt.mono fun out cost ho => ⟨ho.1.1, ?_⟩
  have hcost : cost ≤ NC := ho.1.2.trans (linObjectNormalBudget_mono hH hS harg)
  have wo : out.wt ≤ NC := ho.2.le.trans hcost
  have warg := wt_list3_le (.nat I.r) (.nat I.c) mv
  have hrow : r * p = I.r := rfl
  have hcol : d * p = I.c := rfl
  have hrp : r * p ≤ BC := by omega
  have hnrow := wt_nat_le I.r
  have hncol := wt_nat_le I.c
  have wrs : (encFun (fun i : Fin r => i.val)).wt < W := wt_le_wt_list (by
    simp [a, W, linObjectBlockInput])
  have wcs : (encFun (fun i : Fin d => i.val)).wt < W := wt_le_wt_list (by
    simp [a, W, linObjectBlockInput])
  have wpcs : (Val.list ((List.finRange p).map fun i => encIntMatrix (M i))).wt < W :=
    wt_le_wt_list (by simp [a, W, linObjectBlockInput])
  change _ ≤ linObjectProductNormalCost hH hS W
  unfold linObjectProductNormalCost
  dsimp only [a, W, mv, BC, NC, fullRankInput, I, linObjectProductFullRankInst,
    linObjectBlockInput, encFun, GI.Machine.BinOp.eval, linObjectProductBuildCost] at *
  omega

theorem linObjectProductNormal_zeroDim {r c : ℕ} (M : Matrix (Fin r) (Fin c) ℤ) (hc : c = 0) :
    TmGLQOut M (.list [.list [], .list []]) := by
  subst c
  exact linObjectNormal_zero M

noncomputable def linObjectProductNormalAllCost (hH : HermiteFullRank) (hS : SmithNonsingular) (W : ℕ) : ℕ :=
  1000 * (linObjectProductNormalCost hH hS W + (W + 1) ^ 2 + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 5000 in
theorem linObjectProductNormal_spec (hH : HermiteFullRank) (hS : SmithNonsingular)
    {P : Program} {b jh js p r d : ℕ} (h : linObjectProductNormalAt P b jh js)
    (hjh : P.prims[jh]? = some (linHermitePrim hH))
    (hjs : P.prims[js]? = some (linSmithPrim hS))
    (M : Fin p → Matrix (Fin r) (Fin d) ℤ) (hdr : d ≤ r)
    (hM : ∀ i, Function.Injective (M i).mulVec) :
    let a := linObjectBlockInput M
    FunAll P b a (fun out cost => TmGLQOut (linObjectBlockMatrix M) out ∧
      cost ≤ linObjectProductNormalAllCost hH hS a.wt) := by
  let a := linObjectBlockInput M
  let W := a.wt
  obtain ⟨hr, hd, hp⟩ := linObjectBlockInput_dimensions M
  change r ≤ W at hr
  change d ≤ W at hd
  change p ≤ W at hp
  have hmul : d * p ≤ W * W := Nat.mul_le_mul hd hp
  have wd : (encFun (fun i : Fin d => i.val)).wt < W := wt_le_wt_list (by
    simp [a, W, linObjectBlockInput])
  have wp : (Val.list ((List.finRange p).map fun i => encIntMatrix (M i))).wt < W :=
    wt_le_wt_list (by simp [a, W, linObjectBlockInput])
  have dd := Det.length (Det.arg' (P := P) (vs :=
    [encFun (fun i : Fin r => i.val), encFun (fun i : Fin d => i.val),
      .list ((List.finRange p).map fun i => encIntMatrix (M i))]) (rest := []) (j := 1) rfl)
  have dp := Det.length (Det.arg' (P := P) (vs :=
    [encFun (fun i : Fin r => i.val), encFun (fun i : Fin d => i.val),
      .list ((List.finRange p).map fun i => encIntMatrix (M i))]) (rest := []) (j := 2) rfl)
  simp only [encFun, List.length_map, List.length_finRange] at dd dp
  have dt := Det.arith' (op := .mul) dd dp rfl
  apply FunAll.intro h.entry
  apply EvalAll.ite dt (fun v cost ho => ⟨d * p, ho.1⟩)
  intro q cc hq
  obtain ⟨hq, hcc⟩ := hq
  have hq' : q = d * p := Val.nat.inj hq
  subst q
  by_cases hz : d * p = 0
  · rw [if_pos hz]
    have dz := Det.mk2 (P := P) (env := [a]) Det.nil Det.nil
    refine dz.post fun cost hc => ⟨linObjectProductNormal_zeroDim _ hz, ?_⟩
    have hw : (Val.list [.list [], .list []]).wt ≤ 100 := by decide
    change _ ≤ linObjectProductNormalAllCost hH hS W
    unfold linObjectProductNormalAllCost
    dsimp only [a, W, linObjectBlockInput, encFun, GI.Machine.BinOp.eval, linObjectProductBuildCost] at *
    nlinarith
  · rw [if_neg hz]
    apply EvalAll.call_funAll (Det.var' (P := P) (env := [a]) (i := 0) rfl)
    intro v ca hv
    obtain ⟨rfl, hca⟩ := hv
    refine (linObjectProductNormalPositive_spec hH hS h hjh hjs M hdr hM (Nat.pos_of_ne_zero hz)).wt_lt.mono
      fun out cost ho => ⟨ho.1.1, ?_⟩
    have hw := ho.2
    have hc := ho.1.2
    change _ ≤ linObjectProductNormalAllCost hH hS W
    unfold linObjectProductNormalAllCost
    dsimp only [a, W, linObjectBlockInput, encFun, GI.Machine.BinOp.eval, linObjectProductBuildCost] at *
    nlinarith

theorem linObjectProductNormalCost_poly (hH : HermiteFullRank) (hS : SmithNonsingular) :
    PBU (fun _ W _ => linObjectProductNormalCost hH hS W) := by
  have hb := linObjectProductBuildCost_poly
  have ha : PBU (fun _ W _ => linObjectProductNormalArg W) :=
    PBU.smul 100 (PBU.addc (PBU.add PBU.W hb) 1)
  have hn : PBU (fun _ W _ => linObjectProductNormalBudget hH hS W) :=
    linPoly_subst (f := fun _ W _ => tmGLQBudget hH hS W)
      (tmGLQBudget_poly hH hS) (PBU.const 0) ha (PBU.const 0)
  exact PBU.smul 1000000
    (PBU.addc (PBU.add (PBU.add (PBU.add (PBU.pow (PBU.addc PBU.W 1) 2) PBU.W) hb) hn) 1)

theorem linObjectProductNormalAllCost_poly (hH : HermiteFullRank) (hS : SmithNonsingular) :
    PBU (fun _ W _ => linObjectProductNormalAllCost hH hS W) :=
  PBU.smul 1000 (PBU.addc (PBU.add (linObjectProductNormalCost_poly hH hS)
    (PBU.pow (PBU.addc PBU.W 1) 2)) 1)

theorem linObjectProductNormal_spec_poly (hH : HermiteFullRank) (hS : SmithNonsingular) :
    ∃ K D : ℕ, ∀ {P : Program} {b jh js p r d : ℕ}, linObjectProductNormalAt P b jh js →
      P.prims[jh]? = some (linHermitePrim hH) → P.prims[js]? = some (linSmithPrim hS) →
      ∀ M : Fin p → Matrix (Fin r) (Fin d) ℤ, d ≤ r →
        (∀ i, Function.Injective (M i).mulVec) →
        FunAll P b (linObjectBlockInput M) (fun out cost =>
          TmGLQOut (linObjectBlockMatrix M) out ∧
          cost ≤ K * ((linObjectBlockInput M).wt + 1) ^ D) := by
  obtain ⟨K, D, hKD⟩ := linPoly_source_bound (linObjectProductNormalAllCost_poly hH hS)
  refine ⟨K, D, ?_⟩
  intro P b jh js p r d h hjh hjs M hdr hM
  exact (linObjectProductNormal_spec hH hS h hjh hjs M hdr hM).mono fun out cost ho =>
    ⟨ho.1, ho.2.trans (hKD 0 _ _ (Nat.zero_le _) le_rfl)⟩

end GI.Impl
