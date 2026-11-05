module

public import Workspace.Impl.LinOrbitTransport
public import Workspace.Impl.LinObjectEncoding
public import Workspace.Impl.LinMapAll

@[expose] public section

/-! Collect the local stabilizers of the pieces using the abelian orbit
transporter. Only the zero-fuel recursion is used, so this has no glue premise. -/
namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset Equiv

def linObjectLocalF (orbit : ℕ) : Expr :=
  .letE (.call orbit (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
    (arg 1) (arg 1))) (.get (.var 1) (.nat 1))

def linObjectLocalFuns (b jsci jder jmem : ℕ) : List Expr :=
  mapFuns b (b + 3) ++ [linObjectLocalF (b + 4)] ++
    linOrbitTransportFuns (b + 4) jsci jder jmem

theorem linObjectLocalFuns_length (b jsci jder jmem : ℕ) :
    (linObjectLocalFuns b jsci jder jmem).length = 101 := rfl

structure linObjectLocalAt (P : Program) (b jsci jder jmem : ℕ)
    (hsci : SolvableCosetIntersection) (hder : DerivedSubgroup) (hm : Membership) : Prop where
  map : P.HasAt b (mapFuns b (b + 3))
  item : P.funs[b + 3]? = some (linObjectLocalF (b + 4))
  orbit : linOrbitTransportAt P (b + 4) jsci jder jmem hsci hder hm

theorem linObjectLocalAt_of {P : Program} {b jsci jder jmem : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hm : Membership}
    (h : P.HasAt b (linObjectLocalFuns b jsci jder jmem))
    (hs : P.prims[jsci]? = some (solvableCosetIntersectionPrim hsci))
    (hd : P.prims[jder]? = some (derivedSubgroupPrim hder))
    (hm' : P.prims[jmem]? = some (membershipPrim hm)) :
    linObjectLocalAt P b jsci jder jmem hsci hder hm where
  map := h.block 0 rfl
  item := (h.block (gs := [linObjectLocalF (b + 4)]) 3 rfl).single
  orbit := linOrbitTransportAt_of (h.block 4 rfl) hs hd hm'

noncomputable def linObjectOrbitCoefficient (hsci : SolvableCosetIntersection) (hm : Membership) : ℕ :=
  (linOrbitTransportCost_poly hsci hm).choose
noncomputable def linObjectOrbitDegree (hsci : SolvableCosetIntersection) (hm : Membership) : ℕ :=
  (linOrbitTransportCost_poly hsci hm).choose_spec.choose
noncomputable def linObjectOrbitBudget (hsci : SolvableCosetIntersection) (hm : Membership)
    (n M W : ℕ) : ℕ :=
  linObjectOrbitCoefficient hsci hm * (M + 100 * (W + 1) + n + 2) ^ linObjectOrbitDegree hsci hm
noncomputable def linObjectLocalItemCost (hsci : SolvableCosetIntersection) (hm : Membership)
    (n M W : ℕ) : ℕ := 100000 * (W + linObjectOrbitBudget hsci hm n M W + 1)

theorem linObjectOrbitBudget_bound (hsci : SolvableCosetIntersection) (hm : Membership)
    (n M W U : ℕ) (hU : U ≤ 100 * (W + 1)) :
    linOrbitTransportCost hsci hm n M U ≤ linObjectOrbitBudget hsci hm n M W := by
  have hh := (linOrbitTransportCost_poly hsci hm).choose_spec.choose_spec n M U
  exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

theorem linObjectLocalItemCost_mono (hsci : SolvableCosetIntersection) (hm : Membership)
    {n M W V : ℕ} (hW : W ≤ V) :
    linObjectLocalItemCost hsci hm n M W ≤ linObjectLocalItemCost hsci hm n M V := by
  unfold linObjectLocalItemCost linObjectOrbitBudget
  gcongr

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 8000 in
theorem linObjectLocalItem_spec {P : Program} {b jsci jder jmem n M : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hm : Membership}
    (h : linObjectLocalAt P b jsci jder jmem hsci hder hm)
    (as ns : List (Perm (Fin n))) (S : List (TmRiO n))
    (hsol : TmRiListNorm (gens as) S) (hNA : gens ns ≤ gens as)
    (hNn : GI.Multicoset.Normalizes (gens as) (gens ns))
    (hc : ∀ a ∈ gens as, ∀ b ∈ gens as, a * b * a⁻¹ * b⁻¹ ∈ gens ns)
    (hfix : Fixes (gens ns) (tmGlMs S)) (hal : as.length ≤ n ^ 2)
    (horbit : ∀ s ∈ tmGlMs S, ∀ s' ∈ tmGlMs S, SameOrb (gens as) s s')
    (hS : S.length ≤ M) (hok : TmRecObjOK M (S ++ S))
    (ox : TmRiO n) (hS0 : S[0]? = some ox) :
    let a := Val.list [.list [encGroup as, encGroup ns], tmGlObjsVal S]
    FunAll P (b + 3) a (fun out cost => GroupValC n out (Aut (gens as) (tmGlMs S)) ∧
      cost ≤ linObjectLocalItemCost hsci hm n M a.wt) := by
  let ctx := Val.list [encGroup as, encGroup ns]
  let a := Val.list [ctx, tmGlObjsVal S]
  let W := a.wt
  let oa := Val.list [encGroup as, encGroup ns, tmGlObjsVal S, tmGlObjsVal S]
  let B := linObjectOrbitBudget hsci hm n M W
  have wc : ctx.wt < W := wt_le_wt_list (by simp [a, W])
  have ws : (tmGlObjsVal S).wt < W := wt_le_wt_list (by simp [a, W])
  have wa : (encGroup as).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have wn : (encGroup ns).wt < ctx.wt := wt_le_wt_list (by simp [ctx])
  have warg : oa.wt ≤ 100 * (W + 1) := by
    have hh := wt_list4_le (encGroup as) (encGroup ns) (tmGlObjsVal S) (tmGlObjsVal S)
    dsimp only [oa]; omega
  have ho := linOrbitTransport_spec h.orbit as ns S S (hsol.append hsol) hNA hNn hc hfix hal
    horbit horbit hS hS hok ox hS0
  have ho' : FunAll P (b + 4) oa (fun out cost =>
      CosetC n out (Iso (gens as) (tmGlMs S) (tmGlMs S)) ∧ cost ≤ B) :=
    ho.mono fun out cost hh => ⟨hh.1, hh.2.trans (linObjectOrbitBudget_bound hsci hm n M W _ warg)⟩
  have dc := Det.arg' (P := P) (vs := [ctx, tmGlObjsVal S]) (rest := []) (j := 0) rfl
  have ds := Det.arg' (P := P) (vs := [ctx, tmGlObjsVal S]) (rest := []) (j := 1) rfl
  have da := Det.get' dc (Det.nat 0) rfl
  have dn := Det.get' dc (Det.nat 1) rfl
  have darg := Det.mk4 da dn ds ds
  have dd : EvalAll P [a] (.call (b + 4)
      (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1) (arg 1)))
      (fun out cost => CosetC n out (Iso (gens as) (tmGlMs S) (tmGlMs S)) ∧
        cost ≤ 1000 * (W + B + 1)) := by
    apply EvalAll.call_funAll darg
    intro v ca hh
    obtain ⟨rfl, hca⟩ := hh
    refine ho'.wt_lt.mono fun out cost hout => ⟨hout.1.1, ?_⟩
    have wmk := wt_list4_le (encGroup as) (encGroup ns) (tmGlObjsVal S) (tmGlObjsVal S)
    dsimp only [W, a, ctx, oa] at *
    omega
  apply FunAll.intro h.item
  apply EvalAll.letE dd.wt_lt
  intro out cost hout0
  obtain ⟨hout, hws⟩ := hout0
  rcases hout.1 with hno | ⟨t, ks, rfl, hlen, hcoset⟩
  · have hi : (1 : Perm (Fin n)) ∈ Iso (gens as) (tmGlMs S) (tmGlMs S) :=
      ⟨(gens as).one_mem, act_one _⟩
    rw [hno.2] at hi
    exact False.elim hi
  · have hg : gens ks = Aut (gens as) (tmGlMs S) := tmRi_aut_gens hcoset
    have dv := Det.get' (Det.var' (P := P) (env := [a, .list [encPerm t, encGroup ks]])
      (i := 1) rfl) (Det.nat 1) rfl
    refine dv.post fun cost' hcost => ⟨⟨ks, rfl, hg, hlen⟩, ?_⟩
    have ww := wt_list2_le (encPerm t) (encGroup ks)
    have ht : (encGroup ks).wt < (Val.list [encPerm t, encGroup ks]).wt := wt_le_wt_list (by simp)
    change _ ≤ linObjectLocalItemCost hsci hm n M W
    unfold linObjectLocalItemCost
    dsimp only [ctx, a, W, oa, B] at *
    omega

noncomputable def linObjectLocalCost (hsci : SolvableCosetIntersection) (hm : Membership)
    (n M W : ℕ) : ℕ := linMapBudget W (linObjectLocalItemCost hsci hm n M (100 * (W + 1)))

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 8000 in
theorem linObjectLocal_spec {P : Program} {b jsci jder jmem n M : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hm : Membership}
    (h : linObjectLocalAt P b jsci jder jmem hsci hder hm)
    (as ns : List (Perm (Fin n))) (Ps : List (List (TmRiO n)))
    (hsol : ∀ S ∈ Ps, TmRiListNorm (gens as) S) (hNA : gens ns ≤ gens as)
    (hNn : GI.Multicoset.Normalizes (gens as) (gens ns))
    (hc : ∀ a ∈ gens as, ∀ b ∈ gens as, a * b * a⁻¹ * b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n ^ 2)
    (hfix : ∀ S ∈ Ps, Fixes (gens ns) (tmGlMs S))
    (horbit : ∀ S ∈ Ps, ∀ s ∈ tmGlMs S, ∀ s' ∈ tmGlMs S, SameOrb (gens as) s s')
    (hS : ∀ S ∈ Ps, S.length ≤ M) (hok : ∀ S ∈ Ps, TmRecObjOK M (S ++ S))
    (hne : ∀ S ∈ Ps, ∃ ox : TmRiO n, S[0]? = some ox) :
    let a := Val.list [.list [encGroup as, encGroup ns], .list (Ps.map tmGlObjsVal)]
    FunAll P b a (fun out cost =>
      (∃ ws, out = .list ws ∧ List.Forall₂
        (fun S w => GroupValC n w (Aut (gens as) (tmGlMs S))) Ps ws) ∧
      cost ≤ linObjectLocalCost hsci hm n M a.wt) := by
  let ctx := Val.list [encGroup as, encGroup ns]
  let a := Val.list [ctx, .list (Ps.map tmGlObjsVal)]
  let W := a.wt
  have wc : ctx.wt < W := wt_le_wt_list (by simp [a, W])
  have wp : (Val.list (Ps.map tmGlObjsVal)).wt < W := wt_le_wt_list (by simp [a, W])
  have hs (S : List (TmRiO n)) (hSP : S ∈ Ps) :
      (Val.list [ctx, tmGlObjsVal S]).wt ≤ 100 * (W + 1) := by
    have wS : (tmGlObjsVal S).wt < (Val.list (Ps.map tmGlObjsVal)).wt := wt_le_wt_list (by
      exact List.mem_map.mpr ⟨S, hSP, rfl⟩)
    have ww := wt_list2_le ctx (tmGlObjsVal S)
    omega
  exact linMapAll_spec h.map tmGlObjsVal linObjectListEncoding_injective
    (fun S w => GroupValC n w (Aut (gens as) (tmGlMs S))) ctx Ps
    (linObjectLocalItemCost hsci hm n M (100 * (W + 1))) (fun S hSP => by
      obtain ⟨ox, hox⟩ := hne S hSP
      exact (linObjectLocalItem_spec h as ns S (hsol S hSP) hNA hNn hc (hfix S hSP) hal
        (horbit S hSP) (hS S hSP) (hok S hSP) ox hox).mono fun out cost ho =>
          ⟨ho.1, ho.2.trans (linObjectLocalItemCost_mono hsci hm (hs S hSP))⟩)

theorem linObjectLocalCost_poly (hsci : SolvableCosetIntersection) (hm : Membership) :
    PBU (linObjectLocalCost hsci hm) := by
  unfold linObjectLocalCost linObjectLocalItemCost linObjectOrbitBudget linMapBudget
  norm_poly

end GI.Impl
