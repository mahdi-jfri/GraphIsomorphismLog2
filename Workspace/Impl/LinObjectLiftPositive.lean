import Workspace.Impl.LinObjectLiftAfter
import Workspace.Impl.LinObjectNormal
import Workspace.Impl.GenNormGlue

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linObjectLiftPositiveCost (hH : HermiteFullRank) (W : ℕ) : ℕ :=
  10000000 * ((W + 1) ^ 2 + W + linObjectLiftBuildBudget W + linObjectLiftNegBudget W +
    linObjectLiftSolveBudget hH W + linObjectLiftSliceBudget hH W + linObjectLiftWordBudget hH W + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linObjectLift_positive_spec (hH : HermiteFullRank) {P : Program} {b jh n p r : ℕ}
    (h : linObjectLiftAt P b jh) (hj : P.prims[jh]? = some (linHermitePrim hH))
    {Q : Type*} [CommGroup Q] (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (B : Fin p → Submodule ℤ (Additive Q)) (hf : Function.Surjective (linObjectLiftCoord as π))
    (L : Fin p → Matrix (Fin r) (Fin as.length) ℤ) (hdr : as.length ≤ r)
    (hfull : ∀ i, Function.Injective (L i).mulVec)
    (hL : ∀ i, LinearMap.ker ((B i).mkQ.comp (linObjectLiftCoord as π)) = linRelations (L i))
    (w : Fin (as.length * p) → ℤ) (hpos : 0 < as.length * p) :
    let a := Val.list [encGroup as, linObjectBlockInput L, linVecVal w]
    FunAll P (b + 1) a (fun out cost => linObjectLiftAnswer as π B w out ∧
      cost ≤ linObjectLiftPositiveCost hH a.wt) := by
  let a := Val.list [encGroup as, linObjectBlockInput L, linVecVal w]
  let W := a.wt
  let I := linObjectQuotientFullRankInst L hdr hfull hpos
  let mv := encIntMatrix I.A
  let nv := linVecVal (-w)
  let BB := linObjectLiftBuildBudget W
  let NB := linObjectLiftNegBudget W
  let RB := linObjectLiftSolveBudget hH W
  have wg : (encGroup as).wt < W := wt_le_wt_list (by simp [a, W])
  have wl : (linObjectBlockInput L).wt < W := wt_le_wt_list (by simp [a, W])
  have ww : (linVecVal w).wt < W := wt_le_wt_list (by simp [a, W])
  have hc : as.length * p ≤ W := by
    have hh := length_lt_wt_list ((List.finRange (as.length * p)).map fun i => encInt (w i))
    simp only [List.length_map, List.length_finRange] at hh
    change as.length * p < (linVecVal w).wt at hh
    omega
  have hb := (linObjectQuotientBuild_spec h.build L).mono
    (linObjectLiftBuild_bound (by omega : (linObjectBlockInput L).wt ≤ 100 * (W + 1)))
  have wm : mv.wt ≤ BB := hb.wt_lt.le
  have hr : I.r ≤ BB := by
    have hh := length_lt_wt_list ((List.finRange I.r).map fun i => linVecVal (I.A i))
    simp only [List.length_map, List.length_finRange] at hh
    change I.r < mv.wt at hh
    omega
  have hoff : r * p ≤ BB := by
    change r * p + as.length ≤ BB at hr
    omega
  have hnegarg : (Val.list [encInt (-1), linVecVal w]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (encInt (-1)) (linVecVal w)
    have hn : (encInt (-1)).wt ≤ 30 := by decide
    omega
  have hneg := (linVectorScale_spec h.solve.tri.ints h.neg (-1) w).mono
    (linVectorScaleCost_mono hnegarg hc)
  have he : (fun i => (-1 : ℤ) * w i) = -w := by ext i; simp
  rw [he] at hneg
  have wn : nv.wt ≤ NB := hneg.wt_lt.le
  have hsolvearg : (Val.list [fullRankInput I, nv]).wt ≤ linObjectLiftSolveArg W := by
    have hmat := wt_list3_le (.nat I.r) (.nat I.c) mv
    have htot := wt_list2_le (fullRankInput I) nv
    have hrn := wt_nat_le I.r
    have hcn := wt_nat_le I.c
    have hic : I.c ≤ BB := I.c_le.trans hr
    unfold linObjectLiftSolveArg
    dsimp only [fullRankInput, mv, BB, NB] at *
    omega
  have hs : FunAll P (b + 46) (.list [fullRankInput I, nv]) (fun out cost =>
      linRowAnswer I.A (-w) out ∧ cost ≤ RB) :=
    (linRowSystem_spec hH h.solve hj I (-w)).mono fun out cost ho =>
      ⟨ho.1, ho.2.trans (linObjectLiftSolve_bound hH I (-w) W hsolvearg)⟩
  have db := Det.call (Det.arg' (P := P)
    (vs := [encGroup as, linObjectBlockInput L, linVecVal w]) (rest := []) (j := 1) rfl) hb
  apply FunAll.intro h.positive
  apply EvalAll.letE db
  intro out cb hob
  obtain ⟨rfl, hcb⟩ := hob
  have du := Det.arg' (P := P)
    (vs := [encGroup as, linObjectBlockInput L, linVecVal w]) (rest := [mv]) (j := 2) rfl
  have dminus : Det P [a, mv] linIntMinusOneE (encInt (-1)) 100 :=
    (Det.mk2 (Det.nat 1) (Det.mk1 (Det.nat 1))).mono (by decide)
  have dn := Det.call (Det.mk2 dminus du) hneg
  apply EvalAll.letE dn
  intro out cn hon
  obtain ⟨rfl, hcn⟩ := hon
  have dm := Det.var' (P := P) (env := [a, mv, nv]) (i := 1) rfl
  have drows := Det.length dm
  have dcols := Det.length (Det.arg' (P := P)
    (vs := [encGroup as, linObjectBlockInput L, linVecVal w]) (rest := [mv, nv]) (j := 2) rfl)
  simp only [List.length_map, List.length_finRange] at drows dcols
  have dne := Det.var' (P := P) (env := [a, mv, nv]) (i := 2) rfl
  have dargs := Det.mk2 (Det.mk3 drows dcols dm) dne
  apply EvalAll.letE (normBound_call dargs hs)
  intro ans cr hans
  obtain ⟨hans, wans, hcr⟩ := hans
  refine (linObjectLift_after_spec hH h as π B hf L hL w mv nv ans hans wans hoff).wt_lt.mono
    fun out cost ho => ⟨ho.1.1, ?_⟩
  have hcost := ho.1.2
  have wout := ho.2
  have wnegarg := wt_list2_le (encInt (-1)) (linVecVal w)
  have wmat := wt_list3_le (.nat I.r) (.nat I.c) mv
  have wargs := wt_list2_le (fullRankInput I) nv
  have hrn := wt_nat_le I.r
  have hcn := wt_nat_le I.c
  have wminus : (encInt (-1)).wt ≤ 30 := by decide
  change _ ≤ linObjectLiftPositiveCost hH W
  unfold linObjectLiftPositiveCost linObjectLiftFinishCost at *
  dsimp only [a, W, mv, nv, BB, NB, RB, I, linObjectQuotientFullRankInst,
    fullRankInput, linVecVal, linObjectLiftNegBudget] at *
  omega

end GI.Impl
