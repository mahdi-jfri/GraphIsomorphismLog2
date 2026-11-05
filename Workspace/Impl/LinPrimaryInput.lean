module

public import Workspace.Impl.LinPrimaryRecords
public import Workspace.Impl.LinPrimaryVectorPoint
public import Workspace.Impl.LinNatPower
public import Workspace.Impl.LinProject

@[expose] public section

/-! Assemble the field action of one primary layer from full affine records.
The input stores the cover, p, cyclic exponents, level, records and full point. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linPrimaryInputF (power records project vector : ℕ) : Expr :=
  .letE (.call power (mk2 (arg 1) (arg 3)))
    (.letE (.call records (mk2 (mk4 (arg 1) (arg 2) (arg 3) (.var 1)) (arg 4)))
      (.letE (.call project (mk2 (.nat 0) (.var 2)))
        (.letE (.call project (mk2 (.nat 1) (.var 2)))
          (.letE (.call vector (mk4 (arg 1) (.var 1) (arg 5) (arg 2)))
            (.snoc (mk4 (arg 0) (arg 1) (.var 3) (.var 4)) (.var 5))))))

def linPrimaryInputFuns (b : ℕ) : List Expr :=
  [linPrimaryInputF (b + 1) (b + 4) (b + 84) (b + 88)] ++
    linNatPowerFuns (b + 1) ++ linPrimaryRecordsFuns (b + 4) ++
    linProjectFuns (b + 84) ++ linPrimaryVectorFuns (b + 88)

theorem linPrimaryInputFuns_length (b : ℕ) : (linPrimaryInputFuns b).length = 116 := rfl

structure linPrimaryInputAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linPrimaryInputF (b + 1) (b + 4) (b + 84) (b + 88))
  power : P.HasAt (b + 1) (linNatPowerFuns (b + 1))
  records : linPrimaryRecordsAt P (b + 4)
  project : P.HasAt (b + 84) (linProjectFuns (b + 84))
  vector : linPrimaryVectorAt P (b + 88)

theorem linPrimaryInputAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linPrimaryInputFuns b)) : linPrimaryInputAt P b where
  entry := (h.block (gs := [linPrimaryInputF (b + 1) (b + 4) (b + 84) (b + 88)]) 0 rfl).single
  power := h.block 1 rfl
  records := linPrimaryRecordsAt_of (h.block 4 rfl)
  project := h.block 84 rfl
  vector := linPrimaryVectorAt_of (h.block 88 rfl)

def linPrimaryInputPowerBudget (W j : ℕ) : ℕ := linNatPowerCost (100 * (W + 1)) j

def linPrimaryInputRecordsArg (W j : ℕ) : ℕ := 100 * (W + linPrimaryInputPowerBudget W j + 1)
def linPrimaryInputRecordsBudget (W j : ℕ) : ℕ := linPrimaryRecordsCost (linPrimaryInputRecordsArg W j)
def linPrimaryInputArg (W j : ℕ) : ℕ :=
  100 * (W + linPrimaryInputPowerBudget W j + linPrimaryInputRecordsBudget W j + 1)
def linPrimaryInputProjectBudget (W j : ℕ) : ℕ := linProjectCost (linPrimaryInputArg W j)
def linPrimaryInputVectorBudget (W j : ℕ) : ℕ := linPrimaryVectorCost (linPrimaryInputArg W j) W

def linPrimaryInputCost (W j : ℕ) : ℕ := 1000000 * (W + linPrimaryInputPowerBudget W j +
  linPrimaryInputRecordsBudget W j + linPrimaryInputProjectBudget W j + linPrimaryInputVectorBudget W j + 1)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 7000 in
theorem linPrimaryInput_spec {P : Program} {b p d : ℕ} {G : Type} [Group G]
    (h : linPrimaryInputAt P b) (hp : p.Prime) (cover : Val) (ν : Fin d → ℕ) (level : ℕ)
    (ρ : G →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : G → linFiniteVec (linPrimaryOrders p ν)) (xs : List G)
    (x : linFiniteVec (linPrimaryOrders p ν)) :
    let m := linPrimaryOrders p ν
    let a := Val.list [cover, .nat p, encFun ν, .nat level,
      .list (xs.map (linFiniteAffineVal m ρ c)), linFinitePointVal m x]
    FunDet P b a (.list [cover, .nat p,
      .list (xs.map fun g => encModMatrix (linPrimaryFieldRep p hp.pos ν level ρ g).val),
      .list (xs.map fun g => encVec (linPrimaryCoord p ν level (c g))),
      encVec (linPrimaryCoord p ν level x)]) (linPrimaryInputCost a.wt level) := by
  let m := linPrimaryOrders p ν
  let records := Val.list (xs.map (linFiniteAffineVal m ρ c))
  let point := linFinitePointVal m x
  let a := Val.list [cover, .nat p, encFun ν, .nat level, records, point]
  let W := a.wt
  let q := Val.nat (p ^ level)
  let ctx := Val.list [.nat p, encFun ν, .nat level, q]
  let M := fun g => encModMatrix (linPrimaryFieldRep p hp.pos ν level ρ g).val
  let U := fun g => encVec (linPrimaryCoord p ν level (c g))
  let pairs := Val.list (xs.map fun g => .list [M g, U g])
  let mats := Val.list (xs.map M)
  let offsets := Val.list (xs.map U)
  let source := encVec (linPrimaryCoord p ν level x)
  have wc : cover.wt < W := wt_le_wt_list (by simp [W, a])
  have wp : (Val.nat p).wt < W := wt_le_wt_list (by simp [W, a])
  have wν : (encFun ν).wt < W := wt_le_wt_list (by simp [W, a])
  have wl : (Val.nat level).wt < W := wt_le_wt_list (by simp [W, a])
  have wr : records.wt < W := wt_le_wt_list (by simp [W, a])
  have wx : point.wt < W := wt_le_wt_list (by simp [W, a])
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => Val.nat (ν i))
    simp only [List.length_map, List.length_finRange] at hh
    change d < (encFun ν).wt at hh
    omega
  have wpower : (Val.list [.nat p, .nat level]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (.nat p) (.nat level)
    omega
  have hpower : FunDet P (b + 1) (.list [.nat p, .nat level]) q (linPrimaryInputPowerBudget W level) :=
    (linNatPower_spec h.power p level).mono (by
      unfold linPrimaryInputPowerBudget linNatPowerCost
      gcongr)
  have wq := hpower.wt_lt.le
  have wctx := wt_list4_le (.nat p) (encFun ν) (.nat level) q
  change ctx.wt ≤ _ at wctx
  have wrecords : (Val.list [ctx, records]).wt ≤ linPrimaryInputRecordsArg W level := by
    have hh := wt_list2_le ctx records
    unfold linPrimaryInputRecordsArg
    omega
  have hrecords := (linPrimaryRecords_spec h.records hp ν level ρ c xs).mono
    (linPrimaryRecordsCost_mono wrecords)
  change FunDet P (b + 4) (.list [ctx, records]) pairs (linPrimaryInputRecordsBudget W level) at hrecords
  have wpairs := hrecords.wt_lt.le
  have wproj (i : ℕ) (hi : i ≤ 1) : (Val.list [.nat i, pairs]).wt ≤ linPrimaryInputArg W level := by
    have hh := wt_list2_le (.nat i) pairs
    have hw := wt_nat_le i
    unfold linPrimaryInputArg
    omega
  have hm := (linProject_spec h.project 0 (fun g => [M g, U g]) M xs (by simp)).mono
    (linProjectCost_mono (wproj 0 (by omega)))
  have hu := (linProject_spec h.project 1 (fun g => [M g, U g]) U xs (by simp)).mono
    (linProjectCost_mono (wproj 1 (by omega)))
  change FunDet P (b + 84) (.list [.nat 0, pairs]) mats (linPrimaryInputProjectBudget W level) at hm
  change FunDet P (b + 84) (.list [.nat 1, pairs]) offsets (linPrimaryInputProjectBudget W level) at hu
  have wmats := hm.wt_lt.le
  have woffsets := hu.wt_lt.le
  have wvecarg : (Val.list [.nat p, q, point, encFun ν]).wt ≤ linPrimaryInputArg W level := by
    have hh := wt_list4_le (.nat p) q point (encFun ν)
    unfold linPrimaryInputArg
    omega
  have hv := (linPrimaryVector_point_spec h.vector hp.pos ν level x).mono (linPrimaryVectorCost_mono wvecarg hd)
  change FunDet P (b + 88) (.list [.nat p, q, point, encFun ν]) source (linPrimaryInputVectorBudget W level) at hv
  have wsource := hv.wt_lt.le
  have darg (rest : List Val) (k : ℕ) {v : Val}
      (hv : ([cover, .nat p, encFun ν, .nat level, records, point] : List Val)[k]? = some v) :=
    Det.arg' (P := P) (vs := [cover, .nat p, encFun ν, .nat level, records, point])
      (rest := rest) (j := k) hv
  have dpower := Det.call (Det.mk2 (darg [] 1 rfl) (darg [] 3 rfl)) hpower
  have drecords := Det.call (Det.mk2 (Det.mk4 (darg [q] 1 rfl) (darg [q] 2 rfl)
    (darg [q] 3 rfl) (Det.var' (P := P) (env := [a, q]) (i := 1) rfl)) (darg [q] 4 rfl)) hrecords
  have dm := Det.call (Det.mk2 (Det.nat 0)
    (Det.var' (P := P) (env := [a, q, pairs]) (i := 2) rfl)) hm
  have du := Det.call (Det.mk2 (Det.nat 1)
    (Det.var' (P := P) (env := [a, q, pairs, mats]) (i := 2) rfl)) hu
  have dv := Det.call (Det.mk4 (darg [q, pairs, mats, offsets] 1 rfl)
    (Det.var' (P := P) (env := [a, q, pairs, mats, offsets]) (i := 1) rfl)
    (darg [q, pairs, mats, offsets] 5 rfl) (darg [q, pairs, mats, offsets] 2 rfl)) hv
  have dout := Det.snoc (Det.mk4 (darg [q, pairs, mats, offsets, source] 0 rfl)
    (darg [q, pairs, mats, offsets, source] 1 rfl)
    (Det.var' (P := P) (env := [a, q, pairs, mats, offsets, source]) (i := 3) rfl)
    (Det.var' (P := P) (env := [a, q, pairs, mats, offsets, source]) (i := 4) rfl))
    (Det.var' (P := P) (env := [a, q, pairs, mats, offsets, source]) (i := 5) rfl)
  apply FunDet.intro h.entry
  refine (Det.letE dpower (Det.letE drecords (Det.letE dm (Det.letE du (Det.letE dv dout))))).mono ?_
  have w0 : (Val.nat 0).wt = 2 := rfl
  have w1 : (Val.nat 1).wt = 3 := rfl
  have wout4 := wt_list4_le cover (.nat p) mats offsets
  have wout := wt_list_snoc_le [cover, .nat p, mats, offsets] source
  have wrarg := wt_list2_le ctx records
  have wmarg := wt_list2_le (.nat 0) pairs
  have wuarg := wt_list2_le (.nat 1) pairs
  have wvarg := wt_list4_le (.nat p) q point (encFun ν)
  have wpowarg := wt_list2_le (.nat p) (.nat level)
  change _ ≤ linPrimaryInputCost W level
  unfold linPrimaryInputCost
  dsimp only [darg, a, W, ctx, q, records, point, M, U, pairs, mats, offsets, source] at *
  omega

theorem linPrimaryInputCost_poly : PBU (fun j W _ => linPrimaryInputCost W j) := by
  have hq : PBU (fun j W _ => linPrimaryInputPowerBudget W j) :=
    linPoly_subst linNatPowerCost_poly PBU.k (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  have hrarg : PBU (fun j W _ => linPrimaryInputRecordsArg W j) := PBU.smul 100 (PBU.addc (PBU.add PBU.W hq) 1)
  have hr : PBU (fun j W _ => linPrimaryInputRecordsBudget W j) :=
    linPoly_subst linPrimaryRecordsCost_poly (PBU.const 0) hrarg (PBU.const 0)
  have ha : PBU (fun j W _ => linPrimaryInputArg W j) := PBU.smul 100 (PBU.addc (PBU.add (PBU.add PBU.W hq) hr) 1)
  have hp : PBU (fun j W _ => linPrimaryInputProjectBudget W j) :=
    linPoly_subst linProjectCost_poly (PBU.const 0) ha (PBU.const 0)
  have hv : PBU (fun j W _ => linPrimaryInputVectorBudget W j) :=
    linPoly_subst linPrimaryVectorCost_poly PBU.W ha (PBU.const 0)
  exact PBU.smul 1000000 (PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add PBU.W hq) hr) hp) hv) 1)

end GI.Impl
