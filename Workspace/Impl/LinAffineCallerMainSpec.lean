module

public import Workspace.Impl.LinAffineCallerPrepareSpec
public import Workspace.Impl.LinAffineCallerResidual
public import Workspace.Impl.LinAffineCallerLeftArg

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 24000

private theorem linAffineCallerMainCollect {W X D R T B L F ca cl cb out : ℕ}
    (hca : ca ≤ W + 1 + 1000000 * (W + X + D + R + T + B + 1) + 1000 * (W + B + D + 1) + 1)
    (hcl : cl ≤ 1000 * (W + B + D + 1) + 2 * L + 2)
    (hcb : cb ≤ 100001 * (L + 1) + 3 * F + 100) (hw : out ≤ F + 4) :
    ca + (cl + cb + out + 1) + out + 1 ≤ 10000000 * (W + X + D + R + T + B + L + F + 1) := by omega

set_option maxHeartbeats 300000 in
theorem linAffineCallerMain_spec (hmem : Membership) (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jmem jm jv n d : ℕ} (hat : linAffineTransportAllAt P b jmem jm jv hmem hm hv)
    (gs : List (Equiv.Perm (Fin n))) (hgs : gs ≠ []) (hn2 : 2 ≤ n)
    (m : Fin d → ℕ) (hmpos : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (hs : IsSolvable ρ.range) (hprime : ∀ i p, p.Prime → p ∣ m i → p ≤ n)
    (v w : linFiniteVec m) :
    let a := tmGLAffIn gs m ρ c v w
    FunAll P (b + 1) a (fun out cost => CosetC n out (tmGLAffTrans gs ρ c v w) ∧
      cost ≤ linAffineCallerMainCost hmem hm hv a.wt) := by
  let kept := keepList gs
  let hle : gens kept ≤ gens gs := (gens_keepList gs).le
  let c' := linFiniteRecenter ρ c w
  let ρb := ρ.comp (Subgroup.inclusion hle)
  let cb := c' ∘ Subgroup.inclusion hle
  let point := v - w
  let a := tmGLAffIn gs m ρ c v w
  let W := a.wt
  let prep := linMixedLoopInputVal kept m ρb cb point 1
  let L := linAffineCallerLoopBudget hmem hm hv W
  let F := linAffineCallerLeftBudget hmem hm hv W
  have hprep0 := linAffineCallerPrepare_spec hmem hm hv hat gs hgs m hmpos ρ c hc v w
  have hprepare : FunDet P (b + 1010) a prep (linAffineCallerPrepCost hmem hm W) := hprep0.1
  have wprep : prep.wt ≤ linAffineCallerLoopArg hmem hm W := hprep0.2
  have dprep := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hprepare
  have hcb := linActionRestricted_cocycle m ρ c' (linFiniteRecenter_cocycle ρ c hc w) (Subgroup.inclusion hle)
  have hskeep := linPrimaryRange_solvable gs kept ρ hs hle
  have hloop : FunAll P (b + 244) prep (fun out cost =>
      linMixedLoopInv kept m hmpos ρb cb point 1 n out ∧ cost ≤ L) :=
    FunAll.mono (linMixedLoop_spec hm hv hat.mixed kept (length_keepList_le gs) m hmpos ρb hskeep cb hcb point 1)
      (fun out cost ho => ⟨ho.1, ho.2.trans (linAffineCallerLoop_bound hmem hm hv wprep)⟩)
  have call := normBound_call (Det.var' (P := P) (env := [a, prep]) (i := 1) rfl) hloop
  apply FunAll.intro hat.main
  apply EvalAll.letE dprep
  intro z ca hz
  obtain ⟨rfl, hca⟩ := hz
  have hca' : ca ≤ W + 1 + linAffineCallerPrepCost hmem hm W + linAffineCallerLoopArg hmem hm W + 1 := by
    change ca ≤ a.wt + 1 + linAffineCallerPrepCost hmem hm W + prep.wt + 1 at hca
    change ca ≤ a.wt + 1 + linAffineCallerPrepCost hmem hm W + linAffineCallerLoopArg hmem hm W + 1
    omega
  apply EvalAll.letE call
  intro ans cl ho
  have wans : ans.wt ≤ L := ho.2.1
  have hcl : cl ≤ linAffineCallerLoopArg hmem hm W + 2 * L + 2 := by
    have hh := ho.2.2
    change cl ≤ prep.wt + 1 + 2 * L + 1 at hh
    omega
  have ht := linMixedLoopInv_terminal kept m hmpos hprime ρb cb hcb point 1 ans ho.1
  rcases ht with ⟨rfl, hno⟩ | ⟨ks, hks, r, hans, hlen, hr, hof, hstab, hres⟩
  · have hT := linAffineCaller_no_transport gs kept (gens_keepList gs) hle m ρ c v w hno
    have dl := Det.length (Det.var' (P := P) (env := [a, prep, .list []]) (i := 2) rfl)
    have dd := Det.ite_zero (t := .call (b + 979) linAffineCallerLeftArgE) dl
      (Det.nil (P := P) (env := [a, prep, .list []]))
    refine dd.post fun cbCost hcost => ⟨Or.inl ⟨rfl, hT⟩, ?_⟩
    norm_num only [List.length_nil, wt_list_nil, Nat.add_assoc] at hcost
    have hbody : cbCost ≤ 100001 * (L + 1) + 3 * F + 100 := by omega
    have hw : (Val.list []).wt ≤ F + 4 := by norm_num only [wt_list_nil]; omega
    exact linAffineCallerMainCollect (W := W) (X := linAffineCallerContextBudget W)
      (D := linAffineCallerDiffBudget W) (R := linAffineCallerReduceBudget hmem W)
      (T := linAffineCallerTailBudget hmem W) (B := linAffineCallerRestrictBudget hmem hm W)
      (L := L) (F := F) hca' hcl hbody hw
  · simp only [mul_one] at hans
    subst ans
    let table := linGroupSlpTable (linFiniteAffineVal m (ρb.comp (Subgroup.inclusion hks))
      (cb ∘ Subgroup.inclusion hks)) (linActionGens ks)
    let ident := linFiniteAffineVal m (ρb.comp (Subgroup.inclusion hks)) (cb ∘ Subgroup.inclusion hks) 1
    let zero := linFinitePointVal m 0
    let ans := Val.list [.list [encGroup ks, table, ident], zero, encPerm r.val]
    let out := Val.list [encPerm r.val, encGroup (linConjugateGenerators ks r.val)]
    have wans' : ans.wt ≤ L := wans
    have wctx : (Val.list [encGroup ks, table, ident]).wt < ans.wt := wt_le_wt_list (by simp [ans])
    have wg : (encGroup ks).wt < (Val.list [encGroup ks, table, ident]).wt := wt_le_wt_list (by simp)
    have wr : (encPerm r.val).wt < ans.wt := wt_le_wt_list (by simp [ans])
    have warg : (Val.list [encGroup ks, encPerm r.val]).wt ≤ linAffineCallerLeftArg hmem hm hv W := by
      have hh := wt_list2_le (encGroup ks) (encPerm r.val)
      unfold linAffineCallerLeftArg
      omega
    have hleft := (linAffineLeft_spec hat.left ks r.val).mono (linAffineLeftCost_mono warg)
    have wout : out.wt ≤ F := hleft.wt_lt.le
    have da := linAffineCallerLeftArg_spec (P := P) a prep table ident zero ks r.val
    have dc := Det.call da hleft
    have dl := Det.length (Det.var' (P := P) (env := [a, prep, ans]) (i := 2) rfl)
    have dd := Det.ite_pos (e := .nil) dl (by change (3 : ℕ) ≠ 0; decide) dc
    have heq := linAffineCaller_transport_coset gs kept ks (gens_keepList gs) hle hks m ρ c v w r hres
    have hlen' : (linConjugateGenerators ks r.val).length ≤ n ^ 2 := by
      simpa only [linConjugateGenerators_length] using hlen
    refine dd.post fun cbCost hcost => ⟨Or.inr ⟨r.val, linConjugateGenerators ks r.val, rfl, hlen', heq⟩, ?_⟩
    norm_num only [List.length_cons, List.length_nil, Nat.add_assoc] at hcost
    have hbody : cbCost ≤ 100001 * (L + 1) + 3 * F + 100 := by
      dsimp only [ans, out, L, F, linAffineCallerLeftBudget] at wans' wout hcost ⊢
      omega
    have hw : out.wt ≤ F + 4 := by omega
    exact linAffineCallerMainCollect (W := W) (X := linAffineCallerContextBudget W)
      (D := linAffineCallerDiffBudget W) (R := linAffineCallerReduceBudget hmem W)
      (T := linAffineCallerTailBudget hmem W) (B := linAffineCallerRestrictBudget hmem hm W)
      (L := L) (F := F) hca' hcl hbody hw

end GI.Impl
