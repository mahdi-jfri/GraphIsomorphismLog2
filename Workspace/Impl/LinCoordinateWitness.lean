import Workspace.Impl.LinIntSlpValid
import Workspace.Impl.LinMembership
import Workspace.Impl.LinIntPoly

/-! Constructive membership followed by checked exponent-vector evaluation.
This is the nondeterministic part of one cyclic relation row. -/
namespace GI.Impl
open GI.Cited GI.Lang

/-- Input [membership-input,[assignment-table,zero-vector],encoded-order]. -/
def linCoordinateWitnessF (member exponent : ℕ) : Expr :=
  .letE (.call member (arg 0))
    (.letE (.call exponent (mk3 (.get (arg 1) (.nat 0)) (.get (.var 1) (.nat 1))
      (.get (arg 1) (.nat 1))))
      (mk2 (arg 2) (.var 2)))

theorem linSlpValueCost_mono_all {W V L K t s : ℕ} (hW : W ≤ V) (hL : L ≤ K) (ht : t ≤ s) :
    linSlpValueCost W L t ≤ linSlpValueCost V K s := by
  simp only [linSlpValueCost, linSlpCost, linSlpLoopStepCost, linSlpStepArg,
    linSlpTableBudget, linSlpStepCost, linVectorScaleCost, linVectorBinaryCost, linVectorAccWt]
  gcongr

noncomputable def linCoordinateWitnessCost (h : ConstructiveMembership) (I : MemberInst) (W t : ℕ) : ℕ :=
  1000 * (W + t + linMembershipCost h I + linMembershipWt (linMembershipDegree h) I +
    linSlpValueCost (10 * (W + linMembershipWt (linMembershipDegree h) I + 1))
      ((memberInput I).cells.length ^ linMembershipDegree h) t + 1)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem linCoordinateWitness_spec (h : ConstructiveMembership) {P : Program}
    {f member exponent j table step add scale ib t : ℕ}
    (hf : P.funs[f]? = some (linCoordinateWitnessF member exponent))
    (hm : P.funs[member]? = some (linMembershipF j))
    (hj : P.prims[j]? = some (linMembershipPrim h))
    (he : P.funs[exponent]? = some (linSlpValueF table))
    (hp : P.HasAt table (linSlpFuns table step))
    (hstep : P.funs[step]? = some (linSlpStepF add scale)) (hi : linIntSpec P ib)
    (ha : P.HasAt add (linVectorBinaryFuns add (ib + 11)))
    (hs : P.HasAt scale (linVectorScaleFuns scale ib))
    (I : MemberInst) (hx : I.x ∈ gens I.gs)
    (vectors : List (Fin t → ℤ)) (hlen : I.gs.length = vectors.length)
    (hvec : ∀ v ∈ vectors, ∀ i, (v i).natAbs ≤ 1) (order : Val) :
    FunAll P f (.list [memberInput I, .list [.list (vectors.map linVecVal), linVecVal (0 : Fin t → ℤ)], order])
      (fun out cost => (∃ (prog : List SlpInstr) (z : Fin t → ℤ),
        out = .list [order, linVecVal z] ∧ SlpReaches I.gs prog I.x ∧
        linExponentValue vectors prog = some z) ∧
        cost ≤ linCoordinateWitnessCost h I
          (Val.list [memberInput I, .list [.list (vectors.map linVecVal), linVecVal (0 : Fin t → ℤ)], order]).wt t) := by
  let ctx := Val.list [.list (vectors.map linVecVal), linVecVal (0 : Fin t → ℤ)]
  let a := Val.list [memberInput I, ctx, order]
  let W := a.wt
  let MW := linMembershipWt (linMembershipDegree h) I
  let MC := linMembershipCost h I
  let EC := linSlpValueCost (10 * (W + MW + 1)) ((memberInput I).cells.length ^ linMembershipDegree h) t
  have wm : (memberInput I).wt < W := wt_le_wt_list (by simp)
  have wc : ctx.wt < W := wt_le_wt_list (by simp)
  have wo : order.wt < W := wt_le_wt_list (by simp)
  have wv : (Val.list (vectors.map linVecVal)).wt < W :=
    (wt_le_wt_list (by simp : Val.list (vectors.map linVecVal) ∈ [.list (vectors.map linVecVal), linVecVal (0 : Fin t → ℤ)])).trans wc
  have wz : (linVecVal (0 : Fin t → ℤ)).wt < W :=
    (wt_le_wt_list (by simp : linVecVal (0 : Fin t → ℤ) ∈ [.list (vectors.map linVecVal), linVecVal (0 : Fin t → ℤ)])).trans wc
  have dm := Det.arg' (P := P) (vs := [memberInput I, ctx, order]) (rest := []) (j := 0) rfl
  have hmc : EvalAll P [a] (.call member (arg 0)) (fun v cost =>
      (∃ prog : List SlpInstr, v = .list [.nat 1, .list (prog.map encSlpInstr)] ∧
        prog.length ≤ (memberInput I).cells.length ^ linMembershipDegree h ∧ SlpReaches I.gs prog I.x) ∧
      cost ≤ 10 * (W + MC + MW + 1)) := by
    apply EvalAll.call_funAll dm
    intro v ca hv
    obtain ⟨rfl, hca⟩ := hv
    refine (linMembership_member_spec h hm hj I hx).mono fun out cost ho => ⟨ho.1, ?_⟩
    have hwout := linMembershipOut_wt (d := linMembershipDegree h) (I := I) ho.1
    simp only [W, a, MC, MW] at *
    omega
  apply FunAll.intro hf
  apply EvalAll.letE hmc
  intro mv cm hmv
  obtain ⟨prog, rfl, hprog, hreach⟩ := hmv.1
  obtain ⟨z, hz⟩ := linExponent_of_reaches I.gs vectors hlen prog I.x hreach
  have wmem : (Val.list [.nat 1, .list (prog.map encSlpInstr)]).wt ≤ MW :=
    linMembershipOut_wt (d := linMembershipDegree h) (I := I) ⟨prog, rfl, hprog, hreach⟩
  have wp : (Val.list (prog.map encSlpInstr)).wt ≤ MW :=
    (wt_le_wt_list (by simp : Val.list (prog.map encSlpInstr) ∈ [.nat 1, .list (prog.map encSlpInstr)])).le.trans wmem
  have wexp := wt_list3_le (.list (vectors.map linVecVal)) (.list (prog.map encSlpInstr)) (linVecVal (0 : Fin t → ℤ))
  have wexp' : (Val.list [.list (vectors.map linVecVal), .list (prog.map encSlpInstr), linVecVal (0 : Fin t → ℤ)]).wt ≤ 10 * (W + MW + 1) := by omega
  have hes := (linExponent_spec he hp hstep hi ha hs vectors hvec prog z hz).mono
    (linSlpValueCost_mono_all wexp' hprog (le_refl t))
  have wres : (linVecVal z).wt ≤ EC := hes.wt_lt.le
  have dctx := Det.arg' (P := P) (vs := [memberInput I, ctx, order])
    (rest := [.list [.nat 1, .list (prog.map encSlpInstr)]]) (j := 1) rfl
  have da := Det.get' dctx (Det.nat 0) rfl
  have dzero := Det.get' dctx (Det.nat 1) rfl
  have dmv := Det.var' (P := P) (env := [a, .list [.nat 1, .list (prog.map encSlpInstr)]]) (i := 1) rfl
  have dp := Det.get' dmv (Det.nat 1) rfl
  have de := Det.call (Det.mk3 da dp dzero) hes
  have dout := Det.mk2 (Det.arg' (P := P) (vs := [memberInput I, ctx, order])
    (rest := [.list [.nat 1, .list (prog.map encSlpInstr)], linVecVal z]) (j := 2) rfl)
    (Det.var' (P := P) (env := [a, .list [.nat 1, .list (prog.map encSlpInstr)], linVecVal z]) (i := 2) rfl)
  refine (Det.letE de dout).post fun cost hc => ⟨⟨prog, z, rfl, hreach, hz⟩, ?_⟩
  have wout := wt_list2_le order (linVecVal z)
  have w1 : (Val.nat 1).wt = 3 := rfl
  change _ ≤ linCoordinateWitnessCost h I W t
  unfold linCoordinateWitnessCost
  simp only [W, a, ctx, MC, MW, EC] at *
  omega

end GI.Impl
