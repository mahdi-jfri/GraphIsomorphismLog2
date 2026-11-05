module

public import Workspace.Impl.LinActionSubgroup
public import Workspace.Lang.Prims.Ops

@[expose] public section

/-! One new cover generator: constructive membership and evaluation of its
SLP in the full retained affine action. -/
namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linActionContext {n d : ℕ} (gs : List (Equiv.Perm (Fin n))) (m : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m) : Val :=
  .list [encGroup gs, linGroupSlpTable (linFiniteAffineVal m ρ c) (linActionGens gs),
    linFiniteAffineVal m ρ c 1]

def linActionItemF (member slp : ℕ) : Expr :=
  .letE (.call member (mk2 (.get (arg 0) (.nat 0)) (arg 1)))
    (.call slp (mk3 (.get (arg 0) (.nat 1)) (.get (.var 1) (.nat 1)) (.get (arg 0) (.nat 2))))

def linActionItemFuns (b jm : ℕ) : List Expr :=
  [linActionItemF (b + 1) (b + 2), linMembershipF jm] ++ linFiniteActionSlpFuns (b + 2)

theorem linActionItemFuns_length (b jm : ℕ) : (linActionItemFuns b jm).length = 67 := rfl

structure linActionItemAt (P : Program) (b jm : ℕ) (hm : ConstructiveMembership) : Prop where
  entry : P.funs[b]? = some (linActionItemF (b + 1) (b + 2))
  member : P.funs[b + 1]? = some (linMembershipF jm)
  slp : linFiniteActionSlpAt P (b + 2)
  prim : P.prims[jm]? = some (linMembershipPrim hm)

theorem linActionItemAt_of {P : Program} {b jm : ℕ} {hm : ConstructiveMembership}
    (h : P.HasAt b (linActionItemFuns b jm)) (hj : P.prims[jm]? = some (linMembershipPrim hm)) :
    linActionItemAt P b jm hm where
  entry := (h.block (gs := [linActionItemF (b + 1) (b + 2)]) 0 rfl).single
  member := (h.block (gs := [linMembershipF jm]) 1 rfl).single
  slp := linFiniteActionSlpAt_of (h.block 2 rfl)
  prim := hj

noncomputable def linActionSlpCoefficient : ℕ := (linFiniteActionSlp_spec_poly.{0}).choose
noncomputable def linActionSlpDegree : ℕ := (linFiniteActionSlp_spec_poly.{0}).choose_spec.choose

def linActionMemberArg (W : ℕ) : ℕ := 100 * (W + 1)
noncomputable def linActionMemberOut (h : ConstructiveMembership) (W : ℕ) : ℕ :=
  400 * ((linActionMemberArg W) ^ linMembershipDegree h + 1) *
    (W + (linActionMemberArg W) ^ linMembershipDegree h + 2) + 100
noncomputable def linActionMemberCost (h : ConstructiveMembership) (W : ℕ) : ℕ :=
  (linMembershipPrim h).boundSize (linActionMemberArg W) + linActionMemberArg W + linActionMemberOut h W + 2
noncomputable def linActionItemCost (h : ConstructiveMembership) (W : ℕ) : ℕ :=
  100000 * (W + linActionMemberCost h W + linActionMemberOut h W +
    linActionSlpCoefficient * (100 * (W + linActionMemberOut h W + 1) + 1) ^ linActionSlpDegree + 1)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
theorem linActionItem_spec (h : ConstructiveMembership) {P : Program} {b jm n d : ℕ}
    (hp : linActionItemAt P b jm h) (gs : List (Equiv.Perm (Fin n))) (m : Fin d → ℕ)
    (hm : ∀ i, 0 < m i) (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m))
    (c : gens gs → linFiniteVec m) (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (x : gens gs) :
    FunDet P b (.list [linActionContext gs m ρ c, encPerm x.val]) (linFiniteAffineVal m ρ c x)
      (linActionItemCost h (Val.list [linActionContext gs m ρ c, encPerm x.val]).wt) := by
  let ctx := linActionContext gs m ρ c
  let a := Val.list [ctx, encPerm x.val]
  let W := a.wt
  let I : MemberInst := ⟨n, gs, x.val⟩
  let O := linActionMemberOut h W
  let MC := linActionMemberCost h W
  let SC := linActionSlpCoefficient * (100 * (W + O + 1) + 1) ^ linActionSlpDegree
  have wctx : ctx.wt < W := wt_le_wt_list (by simp [W, a])
  have wx : (encPerm x.val).wt < W := wt_le_wt_list (by simp [W, a])
  have wg : (encGroup gs).wt < W :=
    (wt_le_wt_list (by simp [ctx, linActionContext] : encGroup gs ∈
      [encGroup gs, linGroupSlpTable (linFiniteAffineVal m ρ c) (linActionGens gs), linFiniteAffineVal m ρ c 1])).trans wctx
  have wd : (linGroupSlpTable (linFiniteAffineVal m ρ c) (linActionGens gs)).wt < W :=
    (wt_le_wt_list (by simp : linGroupSlpTable (linFiniteAffineVal m ρ c) (linActionGens gs) ∈
      [encGroup gs, linGroupSlpTable (linFiniteAffineVal m ρ c) (linActionGens gs), linFiniteAffineVal m ρ c 1])).trans wctx
  have wone : (linFiniteAffineVal m ρ c 1).wt < W :=
    (wt_le_wt_list (by simp : linFiniteAffineVal m ρ c 1 ∈
      [encGroup gs, linGroupSlpTable (linFiniteAffineVal m ρ c) (linActionGens gs), linFiniteAffineVal m ρ c 1])).trans wctx
  have wi := wt_list2_le (encGroup gs) (encPerm x.val)
  have wI : (memberInput I).wt ≤ linActionMemberArg W := by
    change (Val.list [encGroup gs, encPerm x.val]).wt ≤ 100 * (W + 1)
    omega
  have wIs : (memberInput I).cells.length ≤ linActionMemberArg W := (memberInput I).size_le_wt.trans wI
  have hlen : gs.length ≤ W := by have hh := S_le_wt_encGroup gs; nlinarith
  have hO : linMembershipWt (linMembershipDegree h) I ≤ O := by
    have hpow := Nat.pow_le_pow_left wIs (linMembershipDegree h)
    have hli : I.gs.length ≤ W := hlen
    change 400 * ((memberInput I).cells.length ^ linMembershipDegree h + 1) *
      (I.gs.length + (memberInput I).cells.length ^ linMembershipDegree h + 2) + 100 ≤
      400 * ((linActionMemberArg W) ^ linMembershipDegree h + 1) *
      (W + (linActionMemberArg W) ^ linMembershipDegree h + 2) + 100
    exact Nat.add_le_add_right (Nat.mul_le_mul
      (Nat.mul_le_mul_left 400 (Nat.add_le_add_right hpow 1))
      (Nat.add_le_add_right (Nat.add_le_add hli hpow) 2)) 100
  have hMC : linMembershipCost h I ≤ MC := by
    have hb : (linMembershipPrim h).bound (memberInput I) ≤ (linMembershipPrim h).boundSize (linActionMemberArg W) := by
      unfold Prim.bound Prim.boundSize
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right wIs 2) _)
    unfold linMembershipCost
    dsimp only [MC, linActionMemberCost, O] at *
    omega
  have hs := linMembership_member_spec h hp.member hp.prim I x.property
  have dm := Det.mk2 (Det.get'
    (Det.arg' (P := P) (vs := [ctx, encPerm x.val]) (rest := []) (j := 0) rfl) (Det.nat 0) rfl)
    (Det.arg' (P := P) (vs := [ctx, encPerm x.val]) (rest := []) (j := 1) rfl)
  have hcall : EvalAll P [a] (.call (b + 1) (mk2 (.get (arg 0) (.nat 0)) (arg 1)))
      (fun out cost =>
        (∃ prog : List SlpInstr, out = .list [.nat 1, .list (prog.map encSlpInstr)] ∧
          prog.length ≤ (memberInput I).cells.length ^ linMembershipDegree h ∧ SlpReaches gs prog x.val) ∧
        cost ≤ 1000 * (W + MC + O + 1)) := by
    apply EvalAll.call_funAll dm
    intro v ca hv
    obtain ⟨rfl, hca⟩ := hv
    refine hs.mono fun out cost ho => ⟨ho.1, ?_⟩
    have hw := (linMembershipOut_wt (d := linMembershipDegree h) (I := I) ho.1).trans hO
    have hh := ho.2.trans hMC
    dsimp only [W, a, ctx, I, linActionContext] at *
    omega
  apply FunAll.intro hp.entry
  apply EvalAll.letE hcall
  intro mv cm hmv
  obtain ⟨prog, rfl, hprog, hreach⟩ := hmv.1
  obtain ⟨es, hes, hlast⟩ := linSlpSubgroup_spec gs x.val x.property prog hreach
  have hmem : (Val.list [.nat 1, .list (prog.map encSlpInstr)]).wt ≤ O :=
    (linMembershipOut_wt (d := linMembershipDegree h) (I := I) ⟨prog, rfl, hprog, hreach⟩).trans hO
  have wp : (Val.list (prog.map encSlpInstr)).wt ≤ O :=
    (wt_le_wt_list (by simp : Val.list (prog.map encSlpInstr) ∈ [Val.nat 1, Val.list (prog.map encSlpInstr)])).le.trans hmem
  have wslp := wt_list3_le (linGroupSlpTable (linFiniteAffineVal m ρ c) (linActionGens gs))
    (.list (prog.map encSlpInstr)) (linFiniteAffineVal m ρ c 1)
  have wslp' : (Val.list [linGroupSlpTable (linFiniteAffineVal m ρ c) (linActionGens gs),
      .list (prog.map encSlpInstr), linFiniteAffineVal m ρ c 1]).wt ≤ 100 * (W + O + 1) := by omega
  have hss := (linFiniteActionSlp_spec_poly.{0}).choose_spec.choose_spec m hm ρ c hc hp.slp
    (linActionGens gs) prog es hes
  have hsmono : linActionSlpCoefficient * ((Val.list [linGroupSlpTable (linFiniteAffineVal m ρ c) (linActionGens gs),
      .list (prog.map encSlpInstr), linFiniteAffineVal m ρ c 1]).wt + 1) ^ linActionSlpDegree ≤ SC := by
    dsimp only [SC]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right wslp' 1) _)
  have hss' := hss.mono hsmono
  rw [hlast] at hss'
  change FunDet P (b + 2) (.list [linGroupSlpTable (linFiniteAffineVal m ρ c) (linActionGens gs),
    .list (prog.map encSlpInstr), linFiniteAffineVal m ρ c 1]) (linFiniteAffineVal m ρ c x) SC at hss'
  have wo := hss'.wt_lt.le
  have da := Det.arg' (P := P) (vs := [ctx, encPerm x.val])
    (rest := [.list [.nat 1, .list (prog.map encSlpInstr)]]) (j := 0) rfl
  have dv := Det.var' (P := P) (env := [a, .list [.nat 1, .list (prog.map encSlpInstr)]]) (i := 1) rfl
  have dargs := Det.mk3 (Det.get' da (Det.nat 1) rfl) (Det.get' dv (Det.nat 1) rfl)
    (Det.get' da (Det.nat 2) rfl)
  refine (Det.call dargs hss').post fun cost hcost => ⟨rfl, ?_⟩
  change cm + cost + (linFiniteAffineVal m ρ c x).wt + 1 ≤ linActionItemCost h W
  unfold linActionItemCost
  have hcm := hmv.2
  dsimp only [W, a, ctx, MC, O, SC, linActionContext] at *
  omega

theorem linActionItemCost_poly (h : ConstructiveMembership) : PBU (fun _ W _ => linActionItemCost h W) := by
  simp only [linActionItemCost, linActionMemberCost, linActionMemberOut, linActionMemberArg, Prim.boundSize]
  norm_poly

end GI.Impl
