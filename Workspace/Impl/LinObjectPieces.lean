import Workspace.Impl.LinObjectLocal
import Workspace.Impl.LinFiniteActionCost

/-! Partition a normalized configuration into `A`-orbit pieces, then
collect all their local stabilizers. The output retains the pieces for
the later offset calculations and common-translation lifts. -/
namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset Equiv

def linObjectPiecesF (pcs collect : ℕ) : Expr :=
  .letE (.call pcs (mk2 (arg 0) (arg 2)))
    (.letE (.call collect (mk2 (mk2 (arg 0) (arg 1)) (.var 1)))
      (mk2 (.var 1) (.var 2)))

def linObjectPiecesFuns (b jsci jder jmem : ℕ) : List Expr :=
  [linObjectPiecesF (b + 12) (b + 1)] ++ linObjectLocalFuns (b + 1) jsci jder jmem

theorem linObjectPiecesFuns_length (b jsci jder jmem : ℕ) :
    (linObjectPiecesFuns b jsci jder jmem).length = 102 := rfl

structure linObjectPiecesAt (P : Program) (b jsci jder jmem : ℕ)
    (hsci : SolvableCosetIntersection) (hder : DerivedSubgroup) (hm : Membership) : Prop where
  entry : P.funs[b]? = some (linObjectPiecesF (b + 12) (b + 1))
  locals : linObjectLocalAt P (b + 1) jsci jder jmem hsci hder hm

theorem linObjectPiecesAt_of {P : Program} {b jsci jder jmem : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hm : Membership}
    (h : P.HasAt b (linObjectPiecesFuns b jsci jder jmem))
    (hs : P.prims[jsci]? = some (solvableCosetIntersectionPrim hsci))
    (hd : P.prims[jder]? = some (derivedSubgroupPrim hder))
    (hm' : P.prims[jmem]? = some (membershipPrim hm)) :
    linObjectPiecesAt P b jsci jder jmem hsci hder hm where
  entry := h.left.single
  locals := linObjectLocalAt_of h.right hs hd hm'

noncomputable def linObjectPiecesPartitionBudget (hsci : SolvableCosetIntersection)
    (n M W : ℕ) : ℕ :=
  tmRiPcsC (tmRiObjPC (solvableCosetIntersectionPrim hsci) n (2 * M)) (100 * (W + 1))

noncomputable def linObjectPiecesLocalArg (hsci : SolvableCosetIntersection) (n M W : ℕ) : ℕ :=
  100 * (W + linObjectPiecesPartitionBudget hsci n M W + 1)

noncomputable def linObjectPiecesCost (hsci : SolvableCosetIntersection) (hm : Membership)
    (n M W : ℕ) : ℕ :=
  100000 * (W + linObjectPiecesPartitionBudget hsci n M W +
    linObjectLocalCost hsci hm n M (linObjectPiecesLocalArg hsci n M W) + 1)

theorem linObjectPiecesLocalCost_mono (hsci : SolvableCosetIntersection) (hm : Membership)
    {n M W V : ℕ} (hW : W ≤ V) :
    linObjectLocalCost hsci hm n M W ≤ linObjectLocalCost hsci hm n M V := by
  unfold linObjectLocalCost linMapBudget linObjectLocalItemCost linObjectOrbitBudget
  gcongr

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
theorem linObjectPieces_spec {P : Program} {b jsci jder jmem n M : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hm : Membership}
    (h : linObjectPiecesAt P b jsci jder jmem hsci hder hm)
    (as ns : List (Perm (Fin n))) (X : List (TmRiO n))
    (hsol : IsSolvable (gens as)) (hNA : gens ns ≤ gens as)
    (hNn : GI.Multicoset.Normalizes (gens as) (gens ns))
    (hc : ∀ a ∈ gens as, ∀ b ∈ gens as, a * b * a⁻¹ * b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n ^ 2) (hX : X.length ≤ M)
    (hfix : Fixes (gens ns) (tmGlMs X)) (hok : TmRecObjOK M X) :
    let a := Val.list [encGroup as, encGroup ns, tmGlObjsVal X]
    FunAll P b a (fun out cost =>
      (∃ ws, out = .list [.list ((tmRiPcsO (gens as) X).map tmGlObjsVal), .list ws] ∧
        List.Forall₂ (fun S w => GroupValC n w (Aut (gens as) (tmGlMs S)))
          (tmRiPcsO (gens as) X) ws) ∧
      cost ≤ linObjectPiecesCost hsci hm n M a.wt) := by
  let a := Val.list [encGroup as, encGroup ns, tmGlObjsVal X]
  let W := a.wt
  let Ps := tmRiPcsO (gens as) X
  let pv := Val.list (Ps.map tmGlObjsVal)
  let ctx := Val.list [encGroup as, encGroup ns]
  let PC := linObjectPiecesPartitionBudget hsci n M W
  let LA := linObjectPiecesLocalArg hsci n M W
  let LC := linObjectLocalCost hsci hm n M LA
  have wa : (encGroup as).wt < W := wt_le_wt_list (by simp [a, W])
  have wn : (encGroup ns).wt < W := wt_le_wt_list (by simp [a, W])
  have wx : (tmGlObjsVal X).wt < W := wt_le_wt_list (by simp [a, W])
  have hOK : TmRiOK (2 * M) X := by
    intro o ho
    obtain ⟨hl, hcol, heq⟩ := hok o ho
    exact ⟨hl, hcol.le, heq⟩
  have harg : (Val.list [encGroup as, tmGlObjsVal X]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (encGroup as) (tmGlObjsVal X)
    omega
  have hp : FunDet P (b + 12) (.list [encGroup as, tmGlObjsVal X]) pv PC := by
    have hh := tmRi_pcs_spec h.locals.orbit.inner hsol hal hOK harg
    rw [← tmRiPcsO_val] at hh
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hh
  have dc := Det.arg' (P := P) (vs := [encGroup as, encGroup ns, tmGlObjsVal X])
    (rest := []) (j := 0) rfl
  have dx := Det.arg' (P := P) (vs := [encGroup as, encGroup ns, tmGlObjsVal X])
    (rest := []) (j := 2) rfl
  have dd := Det.call (Det.mk2 dc dx) hp
  apply FunAll.intro h.entry
  apply EvalAll.letE dd
  intro v cv hv
  obtain ⟨rfl, hcv⟩ := hv
  have wpv : pv.wt ≤ PC := hp.wt_lt.le
  have hlarg : (Val.list [ctx, pv]).wt ≤ LA := by
    have hwc := wt_list2_le (encGroup as) (encGroup ns)
    have hww := wt_list2_le ctx pv
    dsimp only [LA, linObjectPiecesLocalArg, PC, ctx] at *
    omega
  have hpc (S : List (TmRiO n)) (hS : S ∈ Ps) :
      TmRiPc as ns M S ∧ ∀ o ∈ S, o ∈ X := tmRiPcsO_pc hX hfix hS
  have hlocal := linObjectLocal_spec h.locals as ns Ps hsol hNA hNn hc hal
    (fun S hS => (hpc S hS).1.2.2.2) (fun S hS => (hpc S hS).1.2.2.1)
    (fun S hS => (hpc S hS).1.2.1) (fun S hS => ?_) (fun S hS => ?_)
  · have dn := Det.arg' (P := P) (vs := [encGroup as, encGroup ns, tmGlObjsVal X])
      (rest := [pv]) (j := 1) rfl
    have da := Det.arg' (P := P) (vs := [encGroup as, encGroup ns, tmGlObjsVal X])
      (rest := [pv]) (j := 0) rfl
    have dp := Det.var' (P := P) (env := [a, pv]) (i := 1) rfl
    have dh : EvalAll P [a, pv] (.call (b + 1) (mk2 (mk2 (arg 0) (arg 1)) (.var 1)))
        (fun out cost => (∃ ws, out = .list ws ∧ List.Forall₂
          (fun S w => GroupValC n w (Aut (gens as) (tmGlMs S))) Ps ws) ∧
          out.wt ≤ LC ∧ cost ≤ 1000 * (W + PC + LC + 1)) := by
      apply EvalAll.call_funAll (Det.mk2 (Det.mk2 da dn) dp)
      intro v ca hv
      obtain ⟨rfl, hca⟩ := hv
      refine hlocal.wt_lt.mono fun out cost ho => ⟨ho.1.1, ?_, ?_⟩
      · exact ho.2.le.trans (ho.1.2.trans (linObjectPiecesLocalCost_mono hsci hm hlarg))
      · have hcost := ho.1.2.trans (linObjectPiecesLocalCost_mono hsci hm hlarg)
        have wctx := wt_list2_le (encGroup as) (encGroup ns)
        have wlarg := wt_list2_le ctx pv
        dsimp only [a, W, ctx, LC, LA] at *
        omega
    apply EvalAll.letE dh
    intro out co ho
    obtain ⟨⟨ws, rfl, hws⟩, wout, hco⟩ := ho
    have dout := Det.mk2
      (Det.var' (P := P) (env := [a, pv, .list ws]) (i := 1) rfl)
      (Det.var' (P := P) (env := [a, pv, .list ws]) (i := 2) rfl)
    refine dout.post fun cost hh => ⟨⟨ws, rfl, hws⟩, ?_⟩
    have wo := wt_list2_le pv (.list ws)
    change _ ≤ linObjectPiecesCost hsci hm n M W
    unfold linObjectPiecesCost
    dsimp only [a, W, ctx, PC, LA, LC] at *
    omega
  · intro o ho
    have hoX : o ∈ X := (hpc S hS).2 o (by simpa using ho)
    obtain ⟨hl, hcol, heq⟩ := hok o hoX
    exact ⟨hl, hcol, fun o' ho' he => heq o' ((hpc S hS).2 o' (by simpa using ho')) he⟩
  · have hne := (hpc S hS).1.1
    cases S with
    | nil => exact False.elim (hne rfl)
    | cons o S => exact ⟨o, rfl⟩

theorem linObjectPiecesPartitionBudget_poly (hsci : SolvableCosetIntersection) :
    PBU (linObjectPiecesPartitionBudget hsci) := by
  unfold linObjectPiecesPartitionBudget
  simp only [tmRiPcsC, tmRiPcsStepC, tmRiObjPC,
    tmRiTestC, Prim.boundSize]
  norm_poly

theorem linObjectPiecesCost_poly (hsci : SolvableCosetIntersection) (hm : Membership) :
    PBU (linObjectPiecesCost hsci hm) := by
  have hp := linObjectPiecesPartitionBudget_poly hsci
  have ha : PBU (linObjectPiecesLocalArg hsci) :=
    PBU.smul 100 (PBU.addc (PBU.add PBU.B hp) 1)
  have hl := linPoly_subst (f := linObjectLocalCost hsci hm)
    (linObjectLocalCost_poly hsci hm) PBU.k PBU.W ha
  exact PBU.smul 100000 (PBU.addc (PBU.add (PBU.add PBU.B hp) hl) 1)

end GI.Impl
