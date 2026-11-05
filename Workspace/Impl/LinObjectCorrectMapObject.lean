module

public import Workspace.Impl.LinObjectCorrectMapSpec

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

def linObjectCorrectPair {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n)))
    (Y : Multiset (CObj ℕ (Equiv.Perm (Fin n)))) (g k : Equiv.Perm (Fin n)) : Prop :=
  ∃ a ∈ A, k = g*a ∧ (Y ↼ g) ↼ a = Y

noncomputable def linObjectCorrectMapCallBudget (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linPolyEnvelope (linObjectCorrectOneCost_poly hs hm hc hh) (100*(W+1)^2)
noncomputable def linObjectCorrectMapSource (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  100*(W+linObjectCorrectMapCallBudget hs hm hc hh W+1)^2
noncomputable def linObjectCorrectMapCost (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (hh : HermiteFullRank) (W : ℕ) : ℕ :=
  linMapBudget W (1000*(100*(linObjectCorrectMapSource hs hm hc hh W+1)^2+1)^2)

theorem linObjectCorrectMapCost_poly (hs : SolvableCosetIntersection)
    (hm : Membership) (hc : ConstructiveMembership) (hh : HermiteFullRank) :
    PBU (fun _ W _ => linObjectCorrectMapCost hs hm hc hh W) := by
  unfold linObjectCorrectMapCost linObjectCorrectMapSource linObjectCorrectMapCallBudget
    linMapBudget linPolyEnvelope
  norm_poly

set_option maxHeartbeats 500000 in
set_option maxRecDepth 2500 in
theorem linObjectCorrectMap_object_spec {P : Program} {b jsci jder jmem jm jh n r : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (hh : HermiteFullRank) (h : linObjectCorrectMapAt P b jsci jder jmem jm jh hs hd hm hc)
    (hjh : P.prims[jh]? = some (linHermitePrim hh))
    {Q : Type*} [CommGroup Q] (as ns : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (hπ : Function.Surjective π) (hf : Function.Surjective (linObjectLiftCoord as π))
    (Y : List (TmRiO n)) (hok : TmRecObjOK Y.length Y)
    (hsol : TmRiListNorm (gens as) Y) (hNA : gens ns ≤ gens as)
    (H : Subgroup (Equiv.Perm (Fin n))) (hAH : gens as ≤ H)
    (hA : GI.Multicoset.Normalizes H (gens as)) (hN : GI.Multicoset.Normalizes H (gens ns))
    (hcomm : ∀ a ∈ gens as, ∀ b ∈ gens as, a*b*a⁻¹*b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n^2) (hfix : Fixes (gens ns) (tmGlMs Y))
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    (L : Fin (tmRiPcsO (gens as) Y).length → Matrix (Fin r) (Fin as.length) ℤ)
    (hdr : as.length ≤ r) (hfull : ∀ i, Function.Injective (L i).mulVec)
    (hL : ∀ i, LinearMap.ker ((linObjectLocalImages as π Y i).mkQ.comp (linObjectLiftCoord as π)) = linRelations (L i))
    (gs : List (Equiv.Perm (Fin n))) (hgs : ∀ g ∈ gs, g ∈ H)
    (hy : ∀ g ∈ gs, Conf (gens as) (tmGlMs Y) (tmGlMs Y ↼ g))
    (hex : ∀ g ∈ gs, ∃ a ∈ gens as, (tmGlMs Y ↼ g) ↼ a = tmGlMs Y) :
    let ctx := [encGroup as,encGroup ns,Val.list ((tmRiPcsO (gens as) Y).map tmGlObjsVal),linObjectBlockInput L]
    let input := Val.list [.list ctx,.list (gs.map encPerm)]
    FunAll P b input (fun out cost =>
      (∃ ks, out = .list (ks.map encPerm) ∧ List.Forall₂ (linObjectCorrectPair (gens as) (tmGlMs Y)) gs ks) ∧
      cost ≤ linObjectCorrectMapCost hs hm hc hh input.wt) := by
  let ctx := [encGroup as,encGroup ns,Val.list ((tmRiPcsO (gens as) Y).map tmGlObjsVal),linObjectBlockInput L]
  let input := Val.list [.list ctx,.list (gs.map encPerm)]
  let W := input.wt
  let CB := linObjectCorrectMapCallBudget hs hm hc hh W
  let C := linObjectCorrectMapSource hs hm hc hh W
  have hp : W+CB+1 ≤ (W+CB+1)^2 := Nat.le_self_pow (by decide) _
  have wC : W ≤ C := by change W ≤ 100*(W+CB+1)^2; omega
  have cC : CB ≤ C := by change CB ≤ 100*(W+CB+1)^2; omega
  have wctx : (Val.list ctx).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wgs : (Val.list (gs.map encPerm)).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  apply linObjectCorrectMap_comp h ctx gs (linObjectCorrectPair (gens as) (tmGlMs Y)) wC
  intro g hg
  have wg : (encPerm g).wt ≤ W :=
    (wt_le_wt_list (List.mem_map.mpr ⟨g,hg,rfl⟩)).le.trans wgs
  have harg : (Val.list (ctx ++ [encPerm g])).wt ≤ 100*(W+1)^2 := by
    have hh' := wt_list_snoc_le ctx (encPerm g)
    have hp' : W+1 ≤ (W+1)^2 := Nat.le_self_pow (by decide) _
    omega
  have hr := linObjectCorrectOne_spec hh h.correct hjh as ns π hπ hf Y hok hsol hNA H hAH hA hN
    hcomm hal hfix hker L hdr hfull hL g (hgs g hg) (hy g hg)
  refine hr.mono fun out cost hout => ⟨?_,hout.2.trans ((linPolyEnvelope_bound
    (linObjectCorrectOneCost_poly hs hm hc hh) (Nat.zero_le _) harg (Nat.zero_le _)).trans cC)⟩
  obtain ⟨a,ha,he,hcorr⟩ := linObjectCorrectOneAnswer_success (gens as) (tmGlMs Y) (tmGlMs Y ↼ g) g out
    hout.1 (hex g hg)
  exact ⟨g*a,he,a,ha,rfl,hcorr⟩

end GI.Impl
