module

public import Workspace.Impl.LinObjectRelationImages
public import Workspace.Impl.LinElementList
public import Workspace.Impl.LinObjectPad
public import Workspace.Impl.LinAppend
public import Workspace.Impl.LinIntSolverCost

@[expose] public section

/-! One local presentation: compute generator coordinates, pad their
rows, and append them to the presentation of `A/N`. -/
namespace GI.Impl
open GI.Cited GI.Lang Matrix

def linObjectLocalRelationF (coords pad app : ℕ) : Expr :=
  .letE (.call coords (mk2 (.get (arg 0) (.nat 0)) (.get (arg 1) (.nat 1))))
    (.letE (.call pad (mk3 (.get (arg 0) (.nat 2)) (.get (arg 0) (.nat 3)) (.var 1)))
      (.call app (mk2 (.get (arg 0) (.nat 1)) (.var 2))))

def linObjectLocalRelationFuns (b jm : ℕ) : List Expr :=
  [linObjectLocalRelationF (b + 1) (b + 46) (b + 58)] ++
    linElementListFuns (b + 1) jm ++ linObjectPadFuns (b + 46) ++ appendFuns (b + 58)

theorem linObjectLocalRelationFuns_length (b jm : ℕ) :
    (linObjectLocalRelationFuns b jm).length = 61 := rfl

structure linObjectLocalRelationAt (P : Program) (b jm : ℕ) (hm : ConstructiveMembership) : Prop where
  entry : P.funs[b]? = some (linObjectLocalRelationF (b + 1) (b + 46) (b + 58))
  coords : linElementListAt P (b + 1) jm hm
  pad : linObjectPadAt P (b + 46)
  app : P.HasAt (b + 58) (appendFuns (b + 58))

theorem linObjectLocalRelationAt_of {P : Program} {b jm : ℕ} {hm : ConstructiveMembership}
    (h : P.HasAt b (linObjectLocalRelationFuns b jm))
    (hj : P.prims[jm]? = some (linMembershipPrim hm)) : linObjectLocalRelationAt P b jm hm where
  entry := (h.block (gs := [linObjectLocalRelationF (b + 1) (b + 46) (b + 58)]) 0 rfl).single
  coords := linElementListAt_of (h.block 1 rfl) hj
  pad := linObjectPadAt_of (h.block 46 rfl)
  app := h.block 58 rfl

theorem linElementListCost_mono (hm : ConstructiveMembership) {W V : ℕ} (hW : W ≤ V) :
    linElementListCost hm W ≤ linElementListCost hm V := by
  unfold linElementListCost linElementListBudget linMapBudget
  gcongr

theorem linObjectPadCost_mono {W V : ℕ} (hW : W ≤ V) :
    linObjectPadCost W ≤ linObjectPadCost V := by
  simp only [linObjectPadCost, linObjectPadZeroBudget, linObjectPadArg,
    linObjectPadTabBudget, linTabulateCost, linTabulateRangeCost, linMapBudget]
  gcongr

noncomputable def linObjectLocalRelationCoordsBudget (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  linElementListCost hm (100 * (W + 1))
noncomputable def linObjectLocalRelationPadArg (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  100 * (W + linObjectLocalRelationCoordsBudget hm W + 1)
noncomputable def linObjectLocalRelationPadBudget (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  linObjectPadCost (linObjectLocalRelationPadArg hm W)
noncomputable def linObjectLocalRelationAppendArg (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  100 * (W + linObjectLocalRelationPadBudget hm W + 1)
noncomputable def linObjectLocalRelationAppendBudget (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  linAppendCost (linObjectLocalRelationAppendArg hm W)
noncomputable def linObjectLocalRelationCost (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  10000000 * (W + linObjectLocalRelationCoordsBudget hm W +
    linObjectLocalRelationPadBudget hm W + linObjectLocalRelationAppendBudget hm W + 1)

set_option maxHeartbeats 300000 in
set_option maxRecDepth 2000 in
theorem linObjectLocalRelation_spec (hm : ConstructiveMembership)
    {P : Program} {b jm n N : ℕ} (h : linObjectLocalRelationAt P b jm hm)
    (as bs : List (Equiv.Perm (Fin n))) (hbs : ∀ x ∈ bs, x ∈ gens as)
    (hN : (1 :: bs).length ≤ N) (M : Matrix (Fin as.length) (Fin as.length) ℤ)
    {Q : Type*} [CommGroup Q] (π : gens as →* Q) :
    let ctx := Val.list [encGroup as, encIntMatrix M, encFun (fun i : Fin N => i.val),
      encFun (fun i : Fin as.length => i.val)]
    let a := Val.list [ctx, encGroup bs]
    FunAll P b a (fun out cost =>
      (∃ C : Matrix (Fin N) (Fin as.length) ℤ, out = encIntMatrix (linRowStack M C) ∧
        (linRelations C).map
          (linCoordMap (fun j : Fin as.length => π (linIntoSubgroup (gens as) (as.get j)))) =
          Submodule.span ℤ (Set.range fun i : Fin (1 :: bs).length =>
            Additive.ofMul (π (linIntoSubgroup (gens as) ((1 :: bs).get i))))) ∧
      cost ≤ linObjectLocalRelationCost hm a.wt) := by
  let ids := encFun (fun i : Fin N => i.val)
  let cols := encFun (fun i : Fin as.length => i.val)
  let ctx := Val.list [encGroup as, encIntMatrix M, ids, cols]
  let a := Val.list [ctx, encGroup bs]
  let W := a.wt
  let EB := linObjectLocalRelationCoordsBudget hm W
  let PA := linObjectLocalRelationPadArg hm W
  let PB := linObjectLocalRelationPadBudget hm W
  let AA := linObjectLocalRelationAppendArg hm W
  let AB := linObjectLocalRelationAppendBudget hm W
  let f : (Fin as.length → ℤ) →ₗ[ℤ] Additive Q :=
    linCoordMap (fun j : Fin as.length => π (linIntoSubgroup (gens as) (as.get j)))
  have wc : ctx.wt < W := wt_le_wt_list (by simp [a, W])
  have wb : (encGroup bs).wt < W := wt_le_wt_list (by simp [a, W])
  have wa : (encGroup as).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wM : (encIntMatrix M).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wids : ids.wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wcols : cols.wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wbs : (Val.list ((1 :: bs).map encPerm)).wt < (encGroup bs).wt := wt_le_wt_list (by
    simp [encGroup, encPerms])
  have harg : (Val.list [encGroup as, .list ((1 :: bs).map encPerm)]).wt ≤ 100 * (W + 1) := by
    have hw := wt_list2_le (encGroup as) (.list ((1 :: bs).map encPerm))
    omega
  have hmem : ∀ x ∈ 1 :: bs, x ∈ gens as := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (gens as).one_mem
    · exact hbs x hx
  have hs := linElementList_spec hm h.coords as (1 :: bs) hmem π
  have dc := Det.arg' (P := P) (vs := [ctx, encGroup bs]) (rest := []) (j := 0) rfl
  have db := Det.arg' (P := P) (vs := [ctx, encGroup bs]) (rest := []) (j := 1) rfl
  have das := Det.get' dc (Det.nat 0) rfl
  have dbs := Det.get' db (Det.nat 1) rfl
  have dd : EvalAll P [a] (.call (b + 1)
      (mk2 (.get (arg 0) (.nat 0)) (.get (arg 1) (.nat 1)))) (fun out cost =>
      (∃ Z : Matrix (Fin (1 :: bs).length) (Fin as.length) ℤ, out = encIntMatrix Z ∧
        ∀ i : Fin (1 :: bs).length,
          f (Z i) = Additive.ofMul (π (linIntoSubgroup (gens as) ((1 :: bs).get i)))) ∧
      out.wt ≤ EB ∧ cost ≤ 1000 * (W + EB + 1)) := by
    apply EvalAll.call_funAll (Det.mk2 das dbs)
    intro v ca hv
    obtain ⟨rfl, hca⟩ := hv
    refine hs.wt_lt.mono fun out cost ho => ?_
    obtain ⟨⟨⟨Z, rfl, hZ⟩, hcost⟩, hwout⟩ := ho
    have he : cost ≤ EB := hcost.trans (linElementListCost_mono hm harg)
    refine ⟨⟨Z, rfl, fun i => ?_⟩, hwout.le.trans he, ?_⟩
    · exact congrArg Additive.ofMul (hZ i)
    · have hw := wt_list2_le (encGroup as) (.list ((1 :: bs).map encPerm))
      dsimp only [a, W, ctx, encGroup, encPerms] at *
      omega
  apply FunAll.intro h.entry
  apply EvalAll.letE dd
  intro out co ho
  obtain ⟨⟨Z, rfl, hZ⟩, wz, hco⟩ := ho
  let C := linObjectPadMatrix Z N
  have hpadarg : (Val.list [ids, cols, encIntMatrix Z]).wt ≤ PA := by
    have hw := wt_list3_le ids cols (encIntMatrix Z)
    dsimp only [PA, linObjectLocalRelationPadArg, EB] at *
    omega
  have hp := (linObjectPad_spec h.pad Z).mono (linObjectPadCost_mono hpadarg)
  have wp : (encIntMatrix C).wt ≤ PB := hp.wt_lt.le
  have dc' := Det.arg' (P := P) (vs := [ctx, encGroup bs]) (rest := [encIntMatrix Z]) (j := 0) rfl
  have dids := Det.get' dc' (Det.nat 2) rfl
  have dcols := Det.get' dc' (Det.nat 3) rfl
  have dz := Det.var' (P := P) (env := [a, encIntMatrix Z]) (i := 1) rfl
  have dp := Det.call (Det.mk3 dids dcols dz) hp
  apply EvalAll.letE dp
  intro out cp ho
  obtain ⟨rfl, hcp⟩ := ho
  have happ : (Val.list [encIntMatrix M, encIntMatrix C]).wt ≤ AA := by
    have hw := wt_list2_le (encIntMatrix M) (encIntMatrix C)
    dsimp only [AA, linObjectLocalRelationAppendArg, PB] at *
    omega
  have ha := (linAppend_spec h.app
    ((List.finRange as.length).map fun i => linVecVal (M i))
    ((List.finRange N).map fun i => linVecVal (C i))).mono
      (show linAppendCost (Val.list [encIntMatrix M, encIntMatrix C]).wt ≤ AB from by
        change linAppendCost _ ≤ linAppendCost (linObjectLocalRelationAppendArg hm W)
        unfold linAppendCost
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right happ 1) 2))
  have dc'' := Det.arg' (P := P) (vs := [ctx, encGroup bs])
    (rest := [encIntMatrix Z, encIntMatrix C]) (j := 0) rfl
  have dM := Det.get' dc'' (Det.nat 1) rfl
  have dC := Det.var' (P := P) (env := [a, encIntMatrix Z, encIntMatrix C]) (i := 2) rfl
  have result := Det.call (Det.mk2 dM dC) ha
  refine result.post fun cost hc => ⟨⟨C, (linRowStack_value M C).symm, ?_⟩, ?_⟩
  · rw [linObjectPadMatrix_relations Z hN, linObjectRelationImage]
    exact congrArg (Submodule.span ℤ) (congrArg Set.range (funext hZ))
  · have hwout := ha.wt_lt.le
    have hwarg := wt_list2_le (encIntMatrix M) (encIntMatrix C)
    have hwp := wt_list3_le ids cols (encIntMatrix Z)
    change _ ≤ linObjectLocalRelationCost hm W
    unfold linObjectLocalRelationCost
    dsimp only [a, W, ctx, EB, PA, PB, AA, AB, C, linObjectLocalRelationPadBudget] at *
    omega

theorem linObjectLocalRelationCoordsBudget_poly (hm : ConstructiveMembership) :
    PBU (fun _ W _ => linObjectLocalRelationCoordsBudget hm W) := by
  unfold linObjectLocalRelationCoordsBudget linElementListCost linElementListBudget linMapBudget
  norm_poly

theorem linObjectLocalRelationCost_poly (hm : ConstructiveMembership) :
    PBU (fun _ W _ => linObjectLocalRelationCost hm W) := by
  have he := linObjectLocalRelationCoordsBudget_poly hm
  have ha : PBU (fun _ W _ => linObjectLocalRelationPadArg hm W) :=
    PBU.smul 100 (PBU.addc (PBU.add PBU.W he) 1)
  have hp : PBU (fun _ W _ => linObjectLocalRelationPadBudget hm W) :=
    linPoly_subst (f := fun _ W _ => linObjectPadCost W)
      linObjectPadCost_poly (PBU.const 0) ha (PBU.const 0)
  have haa : PBU (fun _ W _ => linObjectLocalRelationAppendArg hm W) :=
    PBU.smul 100 (PBU.addc (PBU.add PBU.W hp) 1)
  have hab : PBU (fun _ W _ => linObjectLocalRelationAppendBudget hm W) :=
    PBU.smul 100000 (PBU.pow (PBU.addc haa 1) 2)
  exact PBU.smul 10000000 (PBU.addc (PBU.add (PBU.add (PBU.add PBU.W he) hp) hab) 1)

end GI.Impl
