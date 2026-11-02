import Workspace.Impl.LinActionRebase
import Workspace.Impl.GenNormGlue

/-! Replace a cover by returned generators and retain their complete affine
records, including inverse records and the full identity action. -/
namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 16000

def linAffineRestrictF (restrict group : ℕ) : Expr :=
  .letE (.call restrict (.var 0))
    (.letE (.call group (mk2 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (arg 1)))
      (mk3 (.var 2) (.var 1) (.get (arg 0) (.nat 2))))

def linAffineRestrictFuns (b jm : ℕ) : List Expr :=
  [linAffineRestrictF (b + 1) (b + 71)] ++ linActionRestrictFuns (b + 1) jm ++ mkGroupFuns (b + 71)

theorem linAffineRestrictFuns_length (b jm : ℕ) : (linAffineRestrictFuns b jm).length = 78 := rfl

structure linAffineRestrictAt (P : Program) (b jm : ℕ) (h : ConstructiveMembership) : Prop where
  entry : P.funs[b]? = some (linAffineRestrictF (b + 1) (b + 71))
  restrict : linActionRestrictAt P (b + 1) jm h
  group : P.HasAt (b + 71) (mkGroupFuns (b + 71))

theorem linAffineRestrictAt_of (h : ConstructiveMembership) {P : Program} {b jm : ℕ}
    (hp : P.HasAt b (linAffineRestrictFuns b jm))
    (hj : P.prims[jm]? = some (linMembershipPrim h)) : linAffineRestrictAt P b jm h where
  entry := (hp.block (gs := [linAffineRestrictF (b + 1) (b + 71)]) 0 rfl).single
  restrict := linActionRestrictAt_of (hp.block 1 rfl) hj
  group := hp.block 71 rfl

def linAffineRestrictGroupBudget (W : ℕ) : ℕ := mkGroupK * ((W + 2) * (W + 1)) ^ 3
noncomputable def linAffineRestrictCost (h : ConstructiveMembership) (W : ℕ) : ℕ :=
  100000 * (W + linActionRestrictCost h W + linAffineRestrictGroupBudget W + 1)

set_option maxHeartbeats 1500000 in
theorem linAffineRestrict_spec (h : ConstructiveMembership) {P : Program} {b jm n d : ℕ}
    (hat : linAffineRestrictAt P b jm h) (gs hs : List (Equiv.Perm (Fin n)))
    (hle : gens hs ≤ gens gs) (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g) :
    FunDet P b (.list [linActionContext gs m ρ c, .list (hs.map encPerm)])
      (linActionContext hs m (ρ.comp (Subgroup.inclusion hle)) (c ∘ Subgroup.inclusion hle))
      (linAffineRestrictCost h (Val.list [linActionContext gs m ρ c, .list (hs.map encPerm)]).wt) := by
  let ctx := linActionContext gs m ρ c
  let raw := Val.list (hs.map encPerm)
  let a := Val.list [ctx, raw]
  let W := a.wt
  let dict := linGroupSlpTable (linFiniteAffineVal m (ρ.comp (Subgroup.inclusion hle))
    (c ∘ Subgroup.inclusion hle)) (linActionGens hs)
  let ident := linFiniteAffineVal m ρ c 1
  have wctx : ctx.wt < W := wt_le_wt_list (by simp [W, a])
  have wraw : raw.wt < W := wt_le_wt_list (by simp [W, a])
  have wg : (encGroup gs).wt < ctx.wt := wt_le_wt_list (by simp [ctx, linActionContext])
  have wn : n ≤ W := by have hh := S_le_wt_encGroup gs; nlinarith
  have hl : hs.length ≤ W := by
    have hh := length_lt_wt_list (hs.map encPerm)
    simp only [List.length_map] at hh
    change hs.length < raw.wt at hh
    omega
  have wid : ident.wt < ctx.wt := wt_le_wt_list (by simp [ctx, ident, linActionContext])
  have hr := linActionRestrict_new_spec h hat.restrict gs hs hle m hm ρ c hc
  change FunDet P (b + 1) a dict (linActionRestrictCost h W) at hr
  have wd := hr.wt_lt.le
  have hg := (mkGroup_spec hat.group hs).mono (c' := linAffineRestrictGroupBudget W) (by
    unfold linAffineRestrictGroupBudget
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul
      (Nat.add_le_add_right hl 2) (Nat.add_le_add_right wn 1)) 3))
  have wnew := hg.wt_lt.le
  have dr := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hr
  have dc := Det.arg' (P := P) (vs := [ctx, raw]) (rest := [dict]) (j := 0) rfl
  have dg := Det.get' dc (Det.nat 0) rfl
  have dn := Det.get' dg (Det.nat 0) rfl
  have ds := Det.arg' (P := P) (vs := [ctx, raw]) (rest := [dict]) (j := 1) rfl
  have dgroup := Det.call (Det.mk2 dn ds) hg
  have dc' := Det.arg' (P := P) (vs := [ctx, raw]) (rest := [dict, encGroup hs]) (j := 0) rfl
  have did := Det.get' dc' (Det.nat 2) rfl
  have dout := Det.mk3
    (Det.var' (P := P) (env := [a, dict, encGroup hs]) (i := 2) rfl)
    (Det.var' (P := P) (env := [a, dict, encGroup hs]) (i := 1) rfl) did
  have he : linActionContext hs m (ρ.comp (Subgroup.inclusion hle)) (c ∘ Subgroup.inclusion hle) =
      .list [encGroup hs, dict, ident] := by
    unfold linActionContext
    rw [linActionRestrictedIdentity]
  rw [he]
  apply FunDet.intro hat.entry
  refine (Det.letE dr (Det.letE dgroup dout)).mono ?_
  have wi := wt_list2_le (.nat n) raw
  have wnwt := wt_nat_le n
  have wo := wt_list3_le (encGroup hs) dict ident
  change _ ≤ linAffineRestrictCost h W
  unfold linAffineRestrictCost
  dsimp only [a, W, ctx, raw, dict, ident] at *
  omega

theorem linAffineRestrictCost_poly (h : ConstructiveMembership) :
    PBU (fun _ W _ => linAffineRestrictCost h W) := by
  have hg : PBU (fun _ W _ => linAffineRestrictGroupBudget W) := by
    unfold linAffineRestrictGroupBudget
    norm_poly
  exact PBU.smul 100000 (PBU.addc (PBU.add (PBU.add PBU.W (linActionRestrictCost_poly h)) hg) 1)

end GI.Impl
