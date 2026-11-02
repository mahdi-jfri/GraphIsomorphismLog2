import Workspace.Impl.LinObjectLocal

/-! The pair table used to find coordinates in one abelian layer.
Every recursive call has fuel zero. No object-glue hypothesis is used. -/
namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset Equiv

def linObjectPairTableF (table : ℕ) : Expr :=
  .call table (mk2 (mk4 (.nat 0) (arg 0) (arg 0) (arg 2)) (arg 2))

def linObjectPairTableFuns (b jsci jder jmem : ℕ) : List Expr :=
  [linObjectPairTableF (b + 68)] ++ linOrbitTransportFuns (b + 1) jsci jder jmem

theorem linObjectPairTableFuns_length (b jsci jder jmem : ℕ) :
    (linObjectPairTableFuns b jsci jder jmem).length = 98 := rfl

structure linObjectPairTableAt (P : Program) (b jsci jder jmem : ℕ)
    (hsci : SolvableCosetIntersection) (hder : DerivedSubgroup) (hm : Membership) : Prop where
  entry : P.funs[b]? = some (linObjectPairTableF (b + 68))
  orbit : linOrbitTransportAt P (b + 1) jsci jder jmem hsci hder hm

theorem linObjectPairTableAt_of {P : Program} {b jsci jder jmem : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hm : Membership}
    (h : P.HasAt b (linObjectPairTableFuns b jsci jder jmem))
    (hs : P.prims[jsci]? = some (solvableCosetIntersectionPrim hsci))
    (hd : P.prims[jder]? = some (derivedSubgroupPrim hder))
    (hm' : P.prims[jmem]? = some (membershipPrim hm)) :
    linObjectPairTableAt P b jsci jder jmem hsci hder hm :=
  ⟨h.left.single, linOrbitTransportAt_of h.right hs hd hm'⟩

def linObjectPairTableWt (n M : ℕ) : ℕ :=
  M * (2 * (M * (1400 * (n + 1) ^ 6 + 1) + 4) + 1) + 4

noncomputable def linObjectPairTableBudget (hsci : SolvableCosetIntersection) (hm : Membership)
    (n M W : ℕ) : ℕ :=
  M * M * (M * (linOrbitZeroBudget hsci n M + tmRiYC (solvableCosetIntersectionPrim hsci)
    n M (4 * (10 * (100 * (W + 1)) + 20) + 10))) + tmRiTabC hm n M M (100 * (W + 1))

noncomputable def linObjectPairTableCost (hsci : SolvableCosetIntersection) (hm : Membership)
    (n M W : ℕ) : ℕ :=
  100000 * (W + linObjectPairTableBudget hsci hm n M W + linObjectPairTableWt n M + 1)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4000 in
theorem linObjectPairTable_spec {P : Program} {b jsci jder jmem n M : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hm : Membership}
    (h : linObjectPairTableAt P b jsci jder jmem hsci hder hm)
    (as ns : List (Perm (Fin n))) (Ps : List (List (TmRiO n)))
    (hsol : IsSolvable (gens as)) (hNA : gens ns ≤ gens as)
    (hNn : GI.Multicoset.Normalizes (gens as) (gens ns))
    (hc : ∀ a ∈ gens as, ∀ b ∈ gens as, a * b * a⁻¹ * b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n ^ 2) (hPs : ∀ S ∈ Ps, TmRiPc as ns M S)
    (hlen : Ps.length ≤ M) (hok : TmRecObjOK M Ps.flatten) :
    let a := Val.list [encGroup as, encGroup ns, .list (Ps.map tmGlObjsVal)]
    FunAll P b a (fun out cost =>
      (∃ tab, out = .list tab ∧ TmRiTab (gens as) Ps tab) ∧
      cost ≤ linObjectPairTableCost hsci hm n M a.wt) := by
  let pv := Val.list (Ps.map tmGlObjsVal)
  let a := Val.list [encGroup as, encGroup ns, pv]
  let W := a.wt
  let ctx := Val.list [.nat 0, encGroup as, encGroup as, pv]
  have wa : (encGroup as).wt < W := wt_le_wt_list (by simp [a, W])
  have wp : pv.wt < W := wt_le_wt_list (by simp [a, W])
  have hctx := wt_list4_le (.nat 0) (encGroup as) (encGroup as) pv
  have harg := wt_list2_le ctx pv
  have wz : (Val.nat 0).wt = 2 := rfl
  have hw : (Val.list [ctx, pv]).wt ≤ 100 * (W + 1) := by
    dsimp only [ctx] at *
    omega
  have hA : gens as = relDerived (gens as) (gens ns) 0 := by
    rw [relDerived_zero]
  have hFuel : relDerived (gens as) (gens ns) (0 + 1) ≤ gens ns := by
    rw [relDerived_succ, relDerived_zero]
    apply sup_le _ le_rfl
    rw [Subgroup.commutator_le]
    intro a ha b hb
    simpa only [commutatorElement_def] using hc a ha b hb
  have ht := tmRi_table_spec h.orbit.inner (linOrbitZero_spec h.orbit.inner)
    hsol hal hal hNA hNn hA hFuel (by omega) hPs hok
    (fun S hS o ho => List.mem_flatten.mpr ⟨S, hS, ho⟩) hw
  have dA := Det.arg' (P := P) (vs := [encGroup as, encGroup ns, pv]) (rest := []) (j := 0) rfl
  have dP := Det.arg' (P := P) (vs := [encGroup as, encGroup ns, pv]) (rest := []) (j := 2) rfl
  apply FunAll.intro h.entry
  apply EvalAll.call_funAll (Det.mk2 (Det.mk4 (Det.nat 0) dA dA dP) dP)
  intro v ca hv
  obtain ⟨rfl, hca⟩ := hv
  refine ht.mono fun out cost ho => ?_
  obtain ⟨tab, rfl, htab, wtab, hcost⟩ := ho
  have wb : (Val.list tab).wt ≤ linObjectPairTableWt n M := wtab.trans (by
    unfold linObjectPairTableWt
    gcongr)
  have cb : cost ≤ linObjectPairTableBudget hsci hm n M W := hcost.trans (by
    unfold linObjectPairTableBudget
    exact Nat.add_le_add (by gcongr) (tmRiTabC_mono hm n M hlen _))
  refine ⟨⟨tab, rfl, htab⟩, ?_⟩
  change _ ≤ linObjectPairTableCost hsci hm n M W
  unfold linObjectPairTableCost
  dsimp only [ctx, a, W, pv] at *
  omega

theorem linObjectPairTableCost_poly (hsci : SolvableCosetIntersection) (hm : Membership) :
    PBU (fun n M W => linObjectPairTableCost hsci hm n M W) := by
  simp only [linObjectPairTableCost, linObjectPairTableBudget, linObjectPairTableWt,
    linOrbitZeroBudget, tmRiBaseC, tmRiObjPC, tmRiPcsStepC, tmRiTestC, tmRiVs,
    tmRiB, tmRiYC, tmRiV, tmRiMapShC, tmRiShC, tmRiPairC, tmRiTabC,
    tmRiB2, tmRiPairC, combCost, combM, cosetNFCost, memCost, reduceCost, Prim.boundSize]
  norm_poly

end GI.Impl
