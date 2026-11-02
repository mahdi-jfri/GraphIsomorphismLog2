import Workspace.Impl.LinWitnessLayout
import Workspace.Impl.LinAssign
import Workspace.Lang.Prims.Ops

/-! Coordinates of a known group element: constructive membership, followed
by evaluation of its SLP in the integer unit-vector assignments. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linElementCoordinatesF (assign witness : ℕ) : Expr :=
  .letE (.arith .sub (.length (.get (arg 0) (.nat 1))) (.nat 1))
    (.letE (.call assign (mk3 (.var 1) (.nat 0) (.var 1)))
      (.letE (.call witness (mk3 (.var 0) (.var 2) .nil))
        (.get (.var 3) (.nat 1))))

def linElementCoordinatesFuns (b jm : ℕ) : List Expr :=
  [linElementCoordinatesF (b + 1) (b + 11), linAssignF (b + 2) (b + 5)] ++
    replicateFuns (b + 2) ++ linAssignUnitFuns (b + 5) (b + 8) ++ linBasisFuns (b + 8) ++
    linCoordinateWitnessFuns (b + 11) jm

theorem linElementCoordinatesFuns_length (b jm : ℕ) :
    (linElementCoordinatesFuns b jm).length = 42 := rfl

structure linElementCoordinatesAt (P : Program) (b jm : ℕ) (hm : ConstructiveMembership) : Prop where
  entry : P.funs[b]? = some (linElementCoordinatesF (b + 1) (b + 11))
  assign : P.funs[b + 1]? = some (linAssignF (b + 2) (b + 5))
  rep : P.HasAt (b + 2) (replicateFuns (b + 2))
  units : P.HasAt (b + 5) (linAssignUnitFuns (b + 5) (b + 8))
  basis : P.HasAt (b + 8) (linBasisFuns (b + 8))
  witness : linWitnessAt P (b + 11) jm hm

theorem linElementCoordinatesAt_of {P : Program} {b jm : ℕ} {hm : ConstructiveMembership}
    (h : P.HasAt b (linElementCoordinatesFuns b jm))
    (hj : P.prims[jm]? = some (linMembershipPrim hm)) : linElementCoordinatesAt P b jm hm where
  entry := (h.block (gs := [linElementCoordinatesF (b + 1) (b + 11)]) 0 rfl).single
  assign := (h.block (gs := [linAssignF (b + 2) (b + 5)]) 1 rfl).single
  rep := h.block 2 rfl
  units := h.block 5 rfl
  basis := h.block 8 rfl
  witness := linCoordinateWitnessAt_of (h.block 11 rfl) hj

noncomputable def linElementAssignCost (t : ℕ) : ℕ :=
  linAssignCost (Val.list [.nat t, .nat 0, .nat t]).wt t 0 t

noncomputable def linElementCoordinatesCost (h : ConstructiveMembership) (I : MemberInst) : ℕ :=
  let W := (memberInput I).wt
  let C := linElementAssignCost I.gs.length
  10000 * (W + C + linCoordinateWitnessCost h I (10 * (W + C + 1)) I.gs.length + 1)

theorem linCoordinateWitnessCost_mono (h : ConstructiveMembership) (I : MemberInst)
    {W V : ℕ} (hW : W ≤ V) (t : ℕ) :
    linCoordinateWitnessCost h I W t ≤ linCoordinateWitnessCost h I V t := by
  unfold linCoordinateWitnessCost
  gcongr
  exact linSlpValueCost_mono_all (by omega) le_rfl le_rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 6000 in
theorem linElementCoordinates_spec (hm : ConstructiveMembership) {P : Program} {b jm : ℕ}
    (hp : linElementCoordinatesAt P b jm hm) (I : MemberInst) (hx : I.x ∈ gens I.gs) :
    FunAll P b (memberInput I) (fun out cost =>
      (∃ (prog : List SlpInstr) (z : Fin I.gs.length → ℤ), out = linVecVal z ∧
        SlpReaches I.gs prog I.x ∧
        linExponentValue (linPrefixVectors I.gs.length 0 I.gs.length) prog = some z) ∧
      cost ≤ linElementCoordinatesCost hm I) := by
  let a := memberInput I
  let W := a.wt
  let t := I.gs.length
  let vectors := linPrefixVectors t 0 t
  let assignments := Val.list [.list (vectors.map linVecVal), linVecVal (0 : Fin t → ℤ)]
  let C := linElementAssignCost t
  let WC := linCoordinateWitnessCost hm I (10 * (W + C + 1)) t
  have ha := linAssign_spec hp.assign hp.rep hp.units hp.basis t 0 t le_rfl
  have wa : assignments.wt ≤ C := ha.wt_lt.le
  have hlen : I.gs.length = vectors.length := by simp [vectors, linPrefixVectors, t]
  have hs := linCoordinateWitness_spec hm hp.witness.entry hp.witness.member hp.witness.prim
    hp.witness.exponent hp.witness.table hp.witness.step hp.witness.ints
    hp.witness.add hp.witness.scale I hx vectors hlen (linPrefixVectors_bound t 0 t) (.list [])
  have wi := wt_list3_le a assignments (.list [])
  have wn : (Val.list []).wt = 4 := by decide
  have wpos : 2 ≤ W := a.two_le_size.trans a.size_le_wt
  have ww : (Val.list [a, assignments, .list []]).wt ≤ 10 * (W + C + 1) := by omega
  have hs' : FunAll P (b + 11) (.list [a, assignments, .list []]) (fun out cost =>
      (∃ (prog : List SlpInstr) (z : Fin t → ℤ), out = .list [.list [], linVecVal z] ∧
        SlpReaches I.gs prog I.x ∧ linExponentValue vectors prog = some z) ∧ cost ≤ WC) :=
    hs.mono fun out cost ho => ⟨ho.1, ho.2.trans (linCoordinateWitnessCost_mono hm I ww t)⟩
  have dgs := Det.arg' (P := P) (vs := [encGroup I.gs, encPerm I.x]) (rest := []) (j := 0) rfl
  have dt := Det.arith' (op := .sub) (Det.length (Det.get' dgs (Det.nat 1) rfl)) (Det.nat 1)
    (show ((1 :: I.gs).map encPerm).length - 1 = t by simp [t])
  have dc := Det.call (Det.mk3
    (Det.var' (P := P) (env := [a, .nat t]) (i := 1) rfl) (Det.nat 0)
    (Det.var' (P := P) (env := [a, .nat t]) (i := 1) rfl)) ha
  have dargs := Det.mk3
    (Det.var' (P := P) (env := [a, .nat t, assignments]) (i := 0) rfl)
    (Det.var' (P := P) (env := [a, .nat t, assignments]) (i := 2) rfl) Det.nil
  have wgs := S_le_wt_encGroup I.gs
  have wg : (encGroup I.gs).wt < W := wt_le_wt_list (by simp [W, a, memberInput])
  have wlist : (Val.list ((1 :: I.gs).map encPerm)).wt < W :=
    (wt_le_wt_list (by simp : Val.list ((1 :: I.gs).map encPerm) ∈
      [Val.nat I.n, .list ((1 :: I.gs).map encPerm)])).trans wg
  have wassign := wt_list3_le (.nat t) (.nat 0) (.nat t)
  have wtlen := wt_nat_le ((1 :: I.gs).map encPerm).length
  have ht : t ≤ W := by dsimp only [t]; nlinarith
  have wnat := wt_nat_le t
  have wn0 := wt_nat_le 0
  have wn1 := wt_nat_le 1
  have wn3 := wt_nat_le 3
  have hz0 : (Val.nat 0).wt = 2 := by decide
  have hz1 : (Val.nat 1).wt = 3 := by decide
  apply FunAll.intro hp.entry
  apply EvalAll.letE dt
  intro v cv hv
  obtain ⟨rfl, hcv⟩ := hv
  apply EvalAll.letE dc
  intro v cv' hv
  obtain ⟨rfl, hcv'⟩ := hv
  have hcall : EvalAll P [a, .nat t, assignments]
      (.call (b + 11) (mk3 (.var 0) (.var 2) .nil))
      (fun out cost =>
        (∃ (prog : List SlpInstr) (z : Fin t → ℤ), out = .list [.list [], linVecVal z] ∧
          SlpReaches I.gs prog I.x ∧ linExponentValue vectors prog = some z) ∧
        out.wt ≤ WC ∧ cost ≤ 100 * (W + C + WC + 1)) := by
    apply EvalAll.call_funAll dargs
    intro v ca hv
    obtain ⟨rfl, hca⟩ := hv
    refine hs'.wt_lt.mono fun out cost ho => ⟨ho.1.1, ho.2.le.trans ho.1.2, ?_⟩
    have hc := ho.1.2
    have hw := ho.2
    dsimp only [W, a, C, WC, assignments] at *
    omega
  apply EvalAll.letE hcall
  intro v cv'' hv
  obtain ⟨prog, z, rfl, hreach, hz⟩ := hv.1
  have wz : (linVecVal z).wt ≤ WC :=
    (wt_le_wt_list (by simp : linVecVal z ∈ [Val.list [], linVecVal z])).le.trans hv.2.1
  have dd := Det.get' (Det.var' (P := P)
    (env := [a, .nat t, assignments, .list [.list [], linVecVal z]]) (i := 3) rfl) (Det.nat 1) rfl
  refine dd.post fun cost hcost => ⟨⟨prog, z, rfl, hreach, hz⟩, ?_⟩
  change _ ≤ linElementCoordinatesCost hm I
  unfold linElementCoordinatesCost
  have hcost' := hv.2.2
  dsimp only [W, a, t, C, WC, assignments, linElementAssignCost, vectors, memberInput] at *
  simp only [List.length_map, List.length_cons] at *
  omega

theorem linAssignCost_mono_all {W V t s ns ms i j : ℕ}
    (hW : W ≤ V) (ht : t ≤ s) (hns : ns ≤ ms) (hi : i ≤ j) :
    linAssignCost W t ns i ≤ linAssignCost V s ms j := by
  simp only [linAssignCost, linAssignRepCost, linAssignZeroWt, linAssignInitWt,
    linAssignUnitsArg, linAssignUnitCost, linAssignUnitStepCost, linAssignUnitAccWt,
    linAssignUnitBasisCost, linAssignUnitBasisArg, linBasisCost, linVectorAccWt,
    linIntCodecCost]
  gcongr

def linElementAssignBudget (W : ℕ) : ℕ := linAssignCost (10 * (W + 1)) W 0 W

noncomputable def linElementMemberWtBudget (h : ConstructiveMembership) (W : ℕ) : ℕ :=
  400 * (W ^ linMembershipDegree h + 1) * (W + W ^ linMembershipDegree h + 2) + 100

noncomputable def linElementMemberCostBudget (h : ConstructiveMembership) (W : ℕ) : ℕ :=
  (linMembershipPrim h).boundSize W + W + linElementMemberWtBudget h W + 2

noncomputable def linElementWitnessBudget (h : ConstructiveMembership) (W : ℕ) : ℕ :=
  let V := 10 * (W + linElementAssignBudget W + 1)
  let MW := linElementMemberWtBudget h W
  1000 * (V + W + linElementMemberCostBudget h W + MW +
    linSlpValueCost (10 * (V + MW + 1)) (W ^ linMembershipDegree h) W + 1)

noncomputable def linElementBudget (h : ConstructiveMembership) (W : ℕ) : ℕ :=
  10000 * (W + linElementAssignBudget W + linElementWitnessBudget h W + 1)

set_option maxHeartbeats 1000000 in
theorem linElementCoordinatesCost_le (h : ConstructiveMembership) (I : MemberInst) :
    linElementCoordinatesCost h I ≤ linElementBudget h (memberInput I).wt := by
  let W := (memberInput I).wt
  have wg : (encGroup I.gs).wt < W := wt_le_wt_list (by simp [W, memberInput])
  have ws := S_le_wt_encGroup I.gs
  have hl : I.gs.length ≤ W := by nlinarith
  have wp : 2 ≤ W := (memberInput I).two_le_size.trans (memberInput I).size_le_wt
  have wa := wt_list3_le (.nat I.gs.length) (.nat 0) (.nat I.gs.length)
  have wt := wt_nat_le I.gs.length
  have w0 : (Val.nat 0).wt = 2 := by decide
  have wa' : (Val.list [.nat I.gs.length, .nat 0, .nat I.gs.length]).wt ≤ 10 * (W + 1) := by omega
  have ha : linElementAssignCost I.gs.length ≤ linElementAssignBudget W :=
    linAssignCost_mono_all wa' hl le_rfl hl
  have hs : (memberInput I).cells.length ≤ W := (memberInput I).size_le_wt
  have hm : linMembershipWt (linMembershipDegree h) I ≤ linElementMemberWtBudget h W := by
    unfold linMembershipWt linElementMemberWtBudget
    gcongr
  have hc : linMembershipCost h I ≤ linElementMemberCostBudget h W := by
    unfold linMembershipCost linElementMemberCostBudget
    have hp : (linMembershipPrim h).bound (memberInput I) ≤ (linMembershipPrim h).boundSize W := by
      unfold Prim.bound Prim.boundSize
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hs 2) _)
    omega
  have harg : 10 * (10 * (W + linElementAssignCost I.gs.length + 1) +
      linMembershipWt (linMembershipDegree h) I + 1) ≤
      10 * (10 * (W + linElementAssignBudget W + 1) + linElementMemberWtBudget h W + 1) := by omega
  have hslp := linSlpValueCost_mono_all harg (Nat.pow_le_pow_left hs (linMembershipDegree h)) hl
  have hw : linCoordinateWitnessCost h I (10 * (W + linElementAssignCost I.gs.length + 1)) I.gs.length ≤
      linElementWitnessBudget h W := by
    dsimp only [linCoordinateWitnessCost, linElementWitnessBudget]
    omega
  unfold linElementCoordinatesCost linElementBudget
  change 10000 * (W + linElementAssignCost I.gs.length + _ + 1) ≤ _
  dsimp only [W] at *
  omega

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 16000 in
theorem linElementBudget_poly (h : ConstructiveMembership) : PBU (fun _ W _ => linElementBudget h W) := by
  simp only [linElementBudget, linElementWitnessBudget, linElementMemberCostBudget,
    linElementMemberWtBudget, linElementAssignBudget, linAssignCost, linAssignRepCost,
    linAssignZeroWt, linAssignInitWt, linAssignUnitsArg, linAssignUnitCost,
    linAssignUnitStepCost, linAssignUnitAccWt, linAssignUnitBasisCost, linAssignUnitBasisArg,
    linBasisCost, linVectorAccWt, linIntCodecCost, Prim.boundSize,
    linSlpValueCost, linSlpCost, linSlpLoopStepCost, linSlpStepArg, linSlpTableBudget,
    linSlpStepCost, linVectorScaleCost, linVectorBinaryCost, linIntBinaryCost,
    linIntCoreBudget, linIntPartsCost]
  norm_poly

end GI.Impl
