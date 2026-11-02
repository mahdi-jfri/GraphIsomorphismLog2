import Workspace.Impl.TermRecInd
import Workspace.Impl.LinObjectNormalize

/-! The abelian-orbit transport subroutine of A.20. The existing point-image
loop is used only with recursive fuel zero, so this block has no glue premise. -/
namespace GI.Impl
open GI.Lang GI.Multicoset GI.Cited Equiv

/-- Input `[gens A, gens N, S, T]`. The two subconfigurations each lie in
one A-orbit. -/
def linOrbitTransportF (pair : ℕ) : Expr :=
  .call pair (mk2 (mk2 (mk4 (.nat 0) (arg 0) (arg 0) .nil) (arg 2)) (arg 3))

def linOrbitTransportFuns (b jsci jder jmem : ℕ) : List Expr :=
  [linOrbitTransportF (b + 11)] ++ tmRiFuns (b + 1) jsci jder jmem b

theorem linOrbitTransportFuns_length (b jsci jder jmem : ℕ) :
    (linOrbitTransportFuns b jsci jder jmem).length = 97 := rfl

structure linOrbitTransportAt (P : Program) (b jsci jder jmem : ℕ)
    (hsci : SolvableCosetIntersection) (hder : DerivedSubgroup) (hmem : Membership) : Prop where
  entry : P.funs[b]? = some (linOrbitTransportF (b + 11))
  inner : TmRiAt P (b + 1) jsci jder jmem b hsci hder hmem

theorem linOrbitTransportAt_of {P : Program} {b jsci jder jmem : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (h : P.HasAt b (linOrbitTransportFuns b jsci jder jmem))
    (hs : P.prims[jsci]? = some (solvableCosetIntersectionPrim hsci))
    (hd : P.prims[jder]? = some (derivedSubgroupPrim hder))
    (hm : P.prims[jmem]? = some (membershipPrim hmem)) :
    linOrbitTransportAt P b jsci jder jmem hsci hder hmem where
  entry := (h.block (gs := [linOrbitTransportF (b + 11)]) 0 rfl).single
  inner := ⟨h.block 1 rfl, hs, hd, hm⟩

noncomputable def linOrbitZeroBudget (hsci : SolvableCosetIntersection) (n M : ℕ) : ℕ :=
  tmRiBaseC (tmRiObjPC (solvableCosetIntersectionPrim hsci) n (2 * M)) n (tmRiVs n M) +
    10 * tmRiVs n M

/-- The recursive entry of the reused code is needed at fuel zero only. -/
theorem linOrbitZero_spec {P : Program} {b jsci jder jmem gObj n M : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hp : TmRiAt P b jsci jder jmem gObj hsci hder hmem) :
    TmRiIH P b n M 0 (linOrbitZeroBudget hsci n M) := by
  intro σH σN X Y hsol hNH hNn hfuel hℓ hNX hNY hHl hNl hX hY hok
  have hw := tmRi_in_wt hℓ hHl hNl hX hY hok
  exact tmRi_main_spec hp hw (fun _ => tmRi_base_spec hp hfuel hNX hHl hok hw)
    (fun h => absurd rfl h)

noncomputable def linOrbitTransportCost (hsci : SolvableCosetIntersection) (hm : Membership)
    (n M W : ℕ) : ℕ :=
  M * (linOrbitZeroBudget hsci n M +
    tmRiYC (solvableCosetIntersectionPrim hsci) n M (4 * (100 * (W + 1)) + 10)) +
    tmRiPairC hm n M (100 * (W + 1)) + 100000 * (W + 1) ^ 6

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 6000 in
theorem linOrbitTransport_spec {P : Program} {b jsci jder jmem n M : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hm : Membership}
    (hp : linOrbitTransportAt P b jsci jder jmem hsci hder hm)
    (as ns : List (Perm (Fin n))) (S T : List (TmRiO n))
    (hsol : IsSolvable (gens as)) (hNA : gens ns ≤ gens as)
    (hNn : GI.Multicoset.Normalizes (gens as) (gens ns))
    (hc : ∀ a ∈ gens as, ∀ b ∈ gens as, a * b * a⁻¹ * b⁻¹ ∈ gens ns)
    (hNT : Fixes (gens ns) (tmGlMs T)) (hal : as.length ≤ n ^ 2)
    (hSo : ∀ s ∈ tmGlMs S, ∀ s' ∈ tmGlMs S, SameOrb (gens as) s s')
    (hTo : ∀ t ∈ tmGlMs T, ∀ t' ∈ tmGlMs T, SameOrb (gens as) t t')
    (hSl : S.length ≤ M) (hTl : T.length ≤ M) (hok : TmRecObjOK M (S ++ T))
    (ox : TmRiO n) (hT0 : T[0]? = some ox) :
    FunAll P b (.list [encGroup as, encGroup ns, tmGlObjsVal S, tmGlObjsVal T])
      (fun u cost => CosetC n u (Iso (gens as) (tmGlMs S) (tmGlMs T)) ∧
        cost ≤ linOrbitTransportCost hsci hm n M
          (Val.list [encGroup as, encGroup ns, tmGlObjsVal S, tmGlObjsVal T]).wt) := by
  let vs := [encGroup as, encGroup ns, tmGlObjsVal S, tmGlObjsVal T]
  let W := (Val.list vs).wt
  let c := Val.list [.nat 0, encGroup as, encGroup as, .list []]
  let a := Val.list [.list [c, tmGlObjsVal S], tmGlObjsVal T]
  have wg : (encGroup as).wt < W := wt_le_wt_list (by simp [vs])
  have wS : (tmGlObjsVal S).wt < W := wt_le_wt_list (by simp [vs])
  have wT : (tmGlObjsVal T).wt < W := wt_le_wt_list (by simp [vs])
  have wc := wt_list4_le (.nat 0) (encGroup as) (encGroup as) (.list [])
  have wi := wt_list2_le c (tmGlObjsVal S)
  have wa := wt_list2_le (.list [c, tmGlObjsVal S]) (tmGlObjsVal T)
  have w0 : (Val.nat 0).wt = 2 := by decide
  have wnil : (Val.list []).wt = 4 := by decide
  have ww : a.wt ≤ 100 * (W + 1) := by dsimp only [a, c] at *; omega
  have hFuel : relDerived (gens as) (gens ns) (0 + 1) ≤ gens ns := by
    rw [relDerived_succ, relDerived_zero]
    apply sup_le _ le_rfl
    rw [Subgroup.commutator_le]
    intro a ha b hb
    simpa only [commutatorElement_def] using hc a ha b hb
  have hh := tmRi_pair_spec hp.inner (linOrbitZero_spec hp.inner) hsol hal hal hNA hNn
    rfl hFuel (by omega) hSo hTo hNT hSl hTl hok hT0 ww
  have de (i : ℕ) {v : Val} (hv : vs[i]? = some v) :=
    Det.arg' (P := P) (vs := vs) (rest := []) (j := i) hv
  have dc := Det.mk4 (Det.nat 0) (de 0 rfl) (de 0 rfl) Det.nil
  have da := Det.mk2 (Det.mk2 dc (de 2 rfl)) (de 3 rfl)
  have wn := S_le_wt_encGroup as
  have hn : n ≤ W := by nlinarith
  have wp : (n + 1) ^ 6 ≤ (W + 1) ^ 6 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 6
  have wone : W + 1 ≤ (W + 1) ^ 6 := Nat.le_self_pow (by decide) _
  apply FunAll.intro hp.entry
  refine EvalAll.call_funAll da fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine hh.mono fun u cost hu => ⟨hu.1, ?_⟩
  have wu := tmRi_wt_ansC hu.1
  have harg : ca ≤ 10000 * (W + 1) := by
    dsimp only [vs, W, c, a] at *
    omega
  change ca + cost + u.wt + 1 ≤ linOrbitTransportCost hsci hm n M W
  unfold linOrbitTransportCost
  have hh := hu.2
  dsimp only [a, c, W, vs] at *
  omega

theorem linOrbitTransportCost_poly (hsci : SolvableCosetIntersection) (hm : Membership) :
    PBU (fun n M W => linOrbitTransportCost hsci hm n M W) := by
  simp only [linOrbitTransportCost, linOrbitZeroBudget, tmRiBaseC, tmRiObjPC,
    tmRiPcsStepC, tmRiTestC, tmRiVs, tmRiB, tmRiYC, tmRiV, tmRiMapShC,
    tmRiShC, tmRiPairC, tmRiB2, combCost, combM, cosetNFCost, reduceCost, memCost, Prim.boundSize]
  norm_poly

end GI.Impl
