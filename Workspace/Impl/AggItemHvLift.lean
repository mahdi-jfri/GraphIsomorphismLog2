module

public import Workspace.Impl.AggItemHvSig
public import Workspace.Impl.AggLiftChild
public import Workspace.Impl.RowProg

@[expose] public section

/-!
# Case 2a: the lifts `τ₀` and `t`

The alignment `τ₀` and the twist `t` of the halving item (`ItHvAl`, `ItHvTw` of
`AggItemHvMath.lean`) are lifts through `π` of the label permutations of `AggItemHvSig.lean`:
`τ₀` lifts the even aligner `σ` ("choose an even ideal permutation aligning their dominant orbits,
lift it through `π`"), and `t` lifts the paired transposition `(a b)(c d)` when `|C| ≥ 2`, and is
`1` otherwise. A lift is a first part `a` of a graph pair `(a, σ)` of `G`; the label lift of
`LabelLift.lean` finds one with one **NormalizedFactor** call (`liftLab_spec`).

* `it_hv_lift_mem`: a first part of a graph pair of `G` is (the image of) an element of `G` with
  that label image;
* `it_hv_al_of`, `it_hv_tw_of`: the facts `ItHvAl`, `ItHvTw` for the lifts;
* `it_hvLc_spec`: the context `liftLabCtx k q ps` of the label lift, built from `[[k, q], ⟨ps⟩]`;
* `it_hvLt_spec`: both lifts, `[e τ₀, e (τ₀ t)]`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens NormalizedFactor)

variable {Ω C : Type} {k : ℕ}

/-! ### Lifts from graph pairs -/

section Lift

variable {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- **A first part of a graph pair of `G` is a lift**: if `(a, σ)` lies in the group of graph pairs
of `G`, then `e⁻¹ a ∈ G` and its label image is `σ`. -/
theorem it_hv_lift_mem {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    {a : Perm (Fin k)} {σ : Perm (Fin L.q)} (h : (a, σ) ∈ Subgroup.closure {p | p ∈ ps}) :
    ∃ hg : (toFin e).symm a ∈ S.G,
      ((L.π ⟨(toFin e).symm a, hg⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) = σ := by
  rw [hps, mem_graphOf] at h
  obtain ⟨g, hg, -, h1, h2⟩ := h
  have h1' : toFin e g = a := h1
  have hga : (toFin e).symm a = g := by rw [← h1', MulEquiv.symm_apply_apply]
  subst hga
  exact ⟨hg, h2⟩

/-- **The alignment of a lift**: a lift of a label permutation that maps `Φ` onto `Φ'`. -/
theorem it_hv_al_of {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    {a : Perm (Fin k)} {σ : Perm (Fin L.q)} (h : (a, σ) ∈ Subgroup.closure {p | p ∈ ps})
    {Φ Φ' : Finset (Fin L.q)} (hσ : σ '' (Φ : Set (Fin L.q)) = Φ') :
    ItHvAl L Φ Φ' ((toFin e).symm a) := by
  obtain ⟨hg, hπ⟩ := it_hv_lift_mem hps h
  exact ⟨⟨_, hg⟩, rfl, by rw [hπ]; exact hσ⟩

/-- **The twist of a lift**: a lift of `(a b)(c d)` with `a ≠ b` in `Φ` and `c ≠ d` outside `Φ`
(`it_hv_tw_pair`). -/
theorem it_hv_tw_of {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    {x : Perm (Fin k)} {Φ : Finset (Fin L.q)} {a b c d : Fin L.q} (ha : a ∈ Φ) (hb : b ∈ Φ)
    (hab : a ≠ b) (hc : c ∉ Φ) (hd : d ∉ Φ) (hcd : c ≠ d)
    (h : (x, swap a b * swap c d) ∈ Subgroup.closure {p | p ∈ ps}) :
    ItHvTw L Φ ((toFin e).symm x) := by
  obtain ⟨hg, hπ⟩ := it_hv_lift_mem hps h
  exact it_hv_tw_pair ha hb hab hc hd hcd hg hπ

/-- An even label permutation has a lift in the graph group of `G` (`π` is onto). -/
theorem it_hv_lift_exists {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps)
    {σ : Perm (Fin L.q)} (hσ : sign σ = 1) : ∃ a, (a, σ) ∈ Subgroup.closure {p | p ∈ ps} := by
  obtain ⟨g, hg⟩ := L.π_surj ⟨σ, Perm.mem_alternatingGroup.2 hσ⟩
  refine ⟨toFin e g, ?_⟩
  rw [hps, mem_graphOf]
  exact ⟨g, g.2, g.2, rfl, by rw [hg]⟩

end Lift

/-! ### The context of the label lift -/

/-- On `[[k, q], ⟨ps⟩]`: the context `liftLabCtx k q ps = [k, Ĥ, N̂, [k, [1_k, 1_q]]]`. -/
def itHvLcF (rng gr fm : ℕ) : Expr :=
  .letE (.call rng (.get (arg 0) (.nat 0)))
  (.letE (.call rng (.get (arg 0) (.nat 1)))
  (.letE (.call fm (mk2 (.var 2) (arg 1)))
    (mk4 (.get (arg 0) (.nat 0)) (.call gr (.var 0)) (.call gr (mk2 (arg 0) (.var 3)))
      (mk2 (.get (arg 0) (.nat 0)) (mk2 (.var 1) (.var 2))))))

/-- The cost bound of `itHvLcF`, at `M = pM k q ps`. -/
def itHvLcC (M : ℕ) : ℕ := 10 ^ 14 * M ^ 6

theorem itHvLcC_mono {a b : ℕ} (h : a ≤ b) : itHvLcC a ≤ itHvLcC b :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 6)

/-- The cost of the map `(a, b) ↦ (a, 1)` on `ps`, at `M = pM k q ps`. -/
theorem itHv_fm_le {q : ℕ} (ps : List (Perm (Fin k) × Perm (Fin q))) :
    ps.length * (40 * (4 * (q + 1) ^ 2 + 22 * (k + q + 1) ^ 2) + 400) +
      mapK * (ps.length + 1) * ((Val.list [encPerm (1 : Perm (Fin q)), .list (ps.map pairV)]).wt +
        (Val.list ((onePairs ps).map pairV)).wt + 1) ≤ 10000000 * pM k q ps ^ 4 := by
  obtain ⟨M, hM⟩ : ∃ M, M = pM k q ps := ⟨_, rfl⟩
  have hMd : k + q + ps.length + 2 = M := by rw [hM]; rfl
  have hpl : pM k q (onePairs ps) = M := by simp [pM, onePairs, hM]
  have wps : (Val.list (ps.map pairV)).wt ≤ 50 * M ^ 3 := hM ▸ wt_pairList_le ps
  have wos : (Val.list ((onePairs ps).map pairV)).wt ≤ 50 * M ^ 3 := by
    have := wt_pairList_le (onePairs ps); rwa [hpl] at this
  have w1q := wt_encPerm_le (1 : Perm (Fin q))
  have wfm := wt_list2_le (encPerm (1 : Perm (Fin q))) (.list (ps.map pairV))
  have hM1 : 1 ≤ M := by omega
  have m12 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have m23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right hM1 (by omega)
  have m34 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by omega)
  have hq2 : (q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hkq2 : (k + q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  rw [← hM]
  have a1 : ps.length * (40 * (4 * (q + 1) ^ 2 + 22 * (k + q + 1) ^ 2) + 400) ≤
      M * (2000 * M ^ 2) := Nat.mul_le_mul (by omega) (by omega)
  have a2 : (ps.length + 1) * ((Val.list [encPerm (1 : Perm (Fin q)),
      .list (ps.map pairV)]).wt + (Val.list ((onePairs ps).map pairV)).wt + 1) ≤
      M * (300 * M ^ 3) := Nat.mul_le_mul (by omega) (by omega)
  have e1 : M * (2000 * M ^ 2) = 2000 * M ^ 3 := by ring
  have e2 : M * (300 * M ^ 3) = 300 * M ^ 4 := by ring
  have hmk : mapK = 1000 := rfl
  rw [hmk, Nat.mul_assoc]
  generalize (Val.list [encPerm (1 : Perm (Fin q)), .list (ps.map pairV)]).wt = X at *
  generalize (Val.list ((onePairs ps).map pairV)).wt = Y at *
  generalize M ^ 3 = M3 at *
  generalize M ^ 4 = M4 at *
  generalize ps.length * (40 * (4 * (q + 1) ^ 2 + 22 * (k + q + 1) ^ 2) + 400) = A at *
  generalize (ps.length + 1) * (X + Y + 1) = B at *
  generalize M * (2000 * M ^ 2) = A' at *
  generalize M * (300 * M3) = B' at *
  omega

set_option maxHeartbeats 2000000 in
/-- **The context of the label lift as a program.** -/
theorem it_hvLc_spec {P : Program} {f rng gr fm en mk : ℕ} (hf : P.funs[f]? = some (itHvLcF rng gr fm))
    (hrng : P.HasAt rng (rangeFuns rng)) (hgr : P.funs[gr]? = some (grpF en mk))
    (hen : P.HasAt en (pEncMapFuns en)) (hmk : P.HasAt mk (mkGroupFuns mk))
    (hfm : P.HasAt fm (fstMapFuns fm)) {q : ℕ} (ps : List (Perm (Fin k) × Perm (Fin q))) :
    FunDet P f (.list [.list [.nat k, .nat q], .list (ps.map pairV)]) (liftLabCtx k q ps)
      (itHvLcC (pM k q ps)) := by
  set M := pM k q ps with hM
  have hMd : k + q + ps.length + 2 = M := rfl
  have hM1 : 1 ≤ M := by omega
  have m12 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have m23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right hM1 (by omega)
  have m34 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by omega)
  have m46 : M ^ 4 ≤ M ^ 6 := Nat.pow_le_pow_right hM1 (by omega)
  have hk2 : (k + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hq2 : (q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hk3 : (k + 1) ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hq3 : (q + 1) ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hkq2 : (k + q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  obtain ⟨W, hW⟩ : ∃ W, W = 1000 * M ^ 4 := ⟨_, rfl⟩
  have hW4 : 4 ≤ W := by omega
  -- weights
  have hpl : pM k q (onePairs ps) = M := by simp [pM, onePairs, hM]
  have wps : (Val.list (ps.map pairV)).wt ≤ 50 * M ^ 3 := wt_pairList_le ps
  have wos : (Val.list ((onePairs ps).map pairV)).wt ≤ 50 * M ^ 3 := by
    have := wt_pairList_le (onePairs ps); rwa [hpl] at this
  have wG : (encGroup (ps.map encPair)).wt ≤ 40 * M ^ 4 := wt_encGroup_pairs_le ps
  have wN : (encGroup ((onePairs ps).map encPair)).wt ≤ 40 * M ^ 4 := by
    have := wt_encGroup_pairs_le (onePairs ps); rwa [hpl] at this
  have w1k := wt_encPerm_le (1 : Perm (Fin k))
  have w1q := wt_encPerm_le (1 : Perm (Fin q))
  have wk := wt_nat_le k
  have wq := wt_nat_le q
  have wkq := wt_list2_le (.nat k) (.nat q)
  have wctx := wt_liftLabCtx_le ps
  have hMd' : ps.length + k + q + 2 = M := by omega
  rw [hMd'] at wctx
  have wid := wt_list2_le (encPerm (1 : Perm (Fin k))) (encPerm (1 : Perm (Fin q)))
  have wsp := wt_list2_le (.nat k) (Val.list [encPerm (1 : Perm (Fin k)), encPerm (1 : Perm (Fin q))])
  have wfm := wt_list2_le (encPerm (1 : Perm (Fin q))) (.list (ps.map pairV))
  have wgr := wt_list2_le (.list [.nat k, .nat q]) (.list ((onePairs ps).map pairV))
  have hinW : (Val.list [.list [.nat k, .nat q], .list (ps.map pairV)]).wt ≤ W := by
    have := wt_list2_le (.list [.nat k, .nat q]) (.list (ps.map pairV)); omega
  set inp : Val := .list [.list [.nat k, .nat q], .list (ps.map pairV)] with hinp
  -- the calls
  have cK := GI.Lang.range_det hrng k
  have cQ := GI.Lang.range_det hrng q
  have cF := fstMap_spec hfm ps
  have cG : FunDet P gr (.list [.list [.nat k, .nat q], .list (ps.map pairV)])
      (encGroup (ps.map encPair)) (grpK * M ^ 6) := grp_spec hgr hen hmk ps
  have cN : FunDet P gr (.list [.list [.nat k, .nat q], .list ((onePairs ps).map pairV)])
      (encGroup ((onePairs ps).map encPair)) (grpK * M ^ 6) := by
    have := grp_spec hgr hen hmk (onePairs ps); rwa [hpl] at this
  -- the body
  have g0 : ∀ env : List Val, env[0]? = some inp →
      StDC P env (.get (arg 0) (.nat 0)) (.nat k) 5 0 W := fun env h0 =>
    StDC.get (StDC.get (StDC.var' h0 hinW) (StDC.nat 0 (by omega)) (v := .list [.nat k, .nat q])
      rfl (by omega)) (StDC.nat 0 (by omega)) (v := .nat k) rfl (by omega)
  have g1 : ∀ env : List Val, env[0]? = some inp →
      StDC P env (.get (arg 0) (.nat 1)) (.nat q) 5 0 W := fun env h0 =>
    StDC.get (StDC.get (StDC.var' h0 hinW) (StDC.nat 0 (by omega)) (v := .list [.nat k, .nat q])
      rfl (by omega)) (StDC.nat 1 (by omega)) (v := .nat q) rfl (by omega)
  have ga : ∀ env : List Val, env[0]? = some inp → ∀ (j : ℕ) (v : Val),
      [Val.list [.nat k, .nat q], .list (ps.map pairV)][j]? = some v → j + 2 ≤ W → v.wt ≤ W →
      StDC P env (arg j) v 3 0 W := fun env h0 j v hv hj hw =>
    (StDC.get (StDC.var' h0 hinW) (StDC.nat j hj) hv hw).mono (by omega) le_rfl
  have d1 := StDC.call (g0 [inp] rfl) cK (by omega)
  set E1 : List Val := [inp, encPerm (1 : Perm (Fin k))]
  have d2 := StDC.call (g1 E1 rfl) cQ (by omega)
  set E2 : List Val := E1 ++ [encPerm (1 : Perm (Fin q))]
  have d3 := StDC.call (StDC.mk2 (StDC.var' (W := W) (env := E2) (i := 2) rfl (by omega))
    (ga E2 rfl 1 _ rfl (by omega) (by omega)) (by omega) hW4) cF (by omega)
  set E3 : List Val := E2 ++ [Val.list ((onePairs ps).map pairV)]
  have dG := StDC.call (StDC.var' (W := W) (env := E3) (i := 0) rfl hinW) cG (by omega)
  have dN := StDC.call (StDC.mk2 (ga E3 rfl 0 _ rfl (by omega) (by omega))
    (StDC.var' (W := W) (env := E3) (i := 3) rfl (by omega)) (by omega) hW4) cN (by omega)
  have dS := StDC.mk2 (g0 E3 rfl) (StDC.mk2 (StDC.var' (W := W) (env := E3) (i := 1) rfl
    (by omega)) (StDC.var' (W := W) (env := E3) (i := 2) rfl (by omega)) (by omega) hW4)
    (by omega) hW4
  have d4 := StDC.mk4 (g0 E3 rfl) dG dN dS (by
    show (liftLabCtx k q ps).wt ≤ W; omega) hW4
  have hctx : (Val.list [.nat k, encGroup (ps.map encPair), encGroup ((onePairs ps).map encPair),
      .list [.nat k, .list [encPerm (1 : Perm (Fin k)), encPerm (1 : Perm (Fin q))]]]) =
      liftLabCtx k q ps := rfl
  rw [hctx] at d4
  have dall := StDC.letE d1 (StDC.letE d2 (StDC.letE d3 d4 (by omega)) (by omega)) (by omega)
  refine StDC.funDet hf dall ?_
  -- the cost
  have hF := itHv_fm_le ps
  rw [← hM] at hF
  unfold itHvLcC
  have hgk : grpK * M ^ 6 = 1000000000000 * M ^ 6 := rfl
  have h7 : (10 : ℕ) ^ 14 = 100000000000000 := by norm_num
  rw [h7]
  omega

/-! ### Both lifts -/

/-- On `[ctx, σ, σ', flag]`: `[a₀, a₀ a₁]` with `a₀` a lift of `σ` and `a₁` a lift of `σ'` if
`flag ≠ 0`, else `a₁ = 1`. -/
def itHvLtF (lift rng cmp : ℕ) : Expr :=
  .letE (.call lift (mk2 (arg 0) (arg 1)))
  (.letE (.call lift (mk2 (arg 0) (arg 2)))
  (.letE (.ite (arg 3) (.var 2) (.call rng (.get (arg 0) (.nat 0))))
    (mk2 (.var 1) (.call cmp (mk2 (.var 1) (.var 3))))))

/-- The cost bound of `itHvLtF` besides the two label lifts, at `M = |ps| + k + q + 2`. -/
def itHvLtC (M : ℕ) : ℕ := 10 ^ 8 * M ^ 4

/-- **One label lift as a call**: for an argument that evaluates to `[ctx, σ]`, the call returns
some lift `a` of `σ`, at cost the argument's cost plus `liftLabCost` plus the weight of the
result. -/
theorem itHv_liftCall (hfac : NormalizedFactor) {P : Program} {f sb sp jfac : ℕ}
    (hf : P.funs[f]? = some (liftLabF sb sp jfac)) (hs : ShiftAt P sb)
    (hsp : P.HasAt sp (pSplitFuns sp)) (hj : P.prims[jfac]? = some (normalizedFactorPrim hfac))
    {q : ℕ} (ps : List (Perm (Fin k) × Perm (Fin q))) {σ : Perm (Fin q)}
    (hσ : ∃ a, (a, σ) ∈ Subgroup.closure {p | p ∈ ps}) {env : List Val} {x : Expr} {ca : ℕ}
    (hx : Det P env x (.list [liftLabCtx k q ps, encPerm σ]) ca) :
    EvalAll P env (.call f x) (fun w c => ∃ a, w = encPerm a ∧
      (a, σ) ∈ Subgroup.closure {p | p ∈ ps} ∧
      c ≤ ca + liftLabCost (normalizedFactorPrim hfac) (ps.length + k + q + 2) + 4 * (k + 1) ^ 2 + 1) := by
  refine EvalAll.call_funAll hx fun v cv hv => ?_
  obtain ⟨rfl, hcv⟩ := hv
  refine (liftLab_spec hfac hf hs hsp hj ps hσ).mono fun w c hw => ?_
  obtain ⟨a, rfl, ha, hc⟩ := hw
  refine ⟨a, rfl, ha, ?_⟩
  have := wt_encPerm_le a
  omega

set_option maxHeartbeats 2000000 in
/-- **Both lifts as a program.** On `[liftLabCtx k q ps, σ, σ', flag]` with `flag ≤ 1`, the
program returns `[a₀, a₀ a₁']` where `a₀` lifts `σ`, and `a₁' = a₁` lifts `σ'` if `flag = 1` and
`a₁' = 1` if `flag = 0`. It makes two label lifts (**NormalizedFactor**). -/
theorem it_hvLt_spec (hfac : NormalizedFactor) {P : Program} {f lift sb sp jfac rng cmp : ℕ}
    (hf : P.funs[f]? = some (itHvLtF lift rng cmp))
    (hlift : P.funs[lift]? = some (liftLabF sb sp jfac)) (hs : ShiftAt P sb)
    (hsp : P.HasAt sp (pSplitFuns sp)) (hj : P.prims[jfac]? = some (normalizedFactorPrim hfac))
    (hrng : P.HasAt rng (rangeFuns rng)) (hcmp : P.HasAt cmp (composeFuns cmp))
    {q : ℕ} (ps : List (Perm (Fin k) × Perm (Fin q))) {σ σ' : Perm (Fin q)}
    (hσ : ∃ a, (a, σ) ∈ Subgroup.closure {p | p ∈ ps})
    (hσ' : ∃ a, (a, σ') ∈ Subgroup.closure {p | p ∈ ps}) {fl : ℕ} (hfl : fl ≤ 1) :
    FunAll P f (.list [liftLabCtx k q ps, encPerm σ, encPerm σ', .nat fl])
      (fun w c => ∃ a₀ a₁, w = .list [encPerm a₀, encPerm (a₀ * if fl = 0 then 1 else a₁)] ∧
        (a₀, σ) ∈ Subgroup.closure {p | p ∈ ps} ∧ (a₁, σ') ∈ Subgroup.closure {p | p ∈ ps} ∧
        c ≤ 2 * liftLabCost (normalizedFactorPrim hfac) (ps.length + k + q + 2) +
          itHvLtC (ps.length + k + q + 2)) := by
  obtain ⟨M, hM⟩ : ∃ M, M = ps.length + k + q + 2 := ⟨_, rfl⟩
  rw [← hM]
  have hM1 : 1 ≤ M := by omega
  have m12 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have m23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right hM1 (by omega)
  have m34 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by omega)
  have hk2 : (k + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hq2 : (q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hk3 : (k + 1) ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left (by omega) 3
  obtain ⟨W, hW⟩ : ∃ W, W = 2000 * M ^ 4 := ⟨_, rfl⟩
  have hW4 : 4 ≤ W := by omega
  set LC := liftLabCost (normalizedFactorPrim hfac) M with hLC
  have wctx : (liftLabCtx k q ps).wt ≤ 400 * M ^ 4 := hM ▸ wt_liftLabCtx_le ps
  have ws := wt_encPerm_le σ
  have ws' := wt_encPerm_le σ'
  have wfl := wt_nat_le fl
  have w4 := wt_list4_le (liftLabCtx k q ps) (encPerm σ) (encPerm σ') (.nat fl)
  have hinW : (Val.list [liftLabCtx k q ps, encPerm σ, encPerm σ', .nat fl]).wt ≤ W := by omega
  set inp : Val := .list [liftLabCtx k q ps, encPerm σ, encPerm σ', .nat fl] with hinp
  have w2 := wt_list2_le (liftLabCtx k q ps) (encPerm σ)
  have w2' := wt_list2_le (liftLabCtx k q ps) (encPerm σ')
  have ga : ∀ (env : List Val), env[0]? = some inp → ∀ (j : ℕ) (v : Val),
      [liftLabCtx k q ps, encPerm σ, encPerm σ', .nat fl][j]? = some v → j + 2 ≤ W → v.wt ≤ W →
      StDC P env (arg j) v 3 0 W := fun env h0 j v hv hj hw =>
    (StDC.get (StDC.var' h0 hinW) (StDC.nat j hj) hv hw).mono (by omega) le_rfl
  have hCA : 7 * (W + 1) + 0 ≤ 7 * (W + 1) := le_rfl
  -- the first lift
  have dA := (StDC.mk2 (ga [inp] rfl 0 _ rfl (by omega) (by omega))
    (ga [inp] rfl 1 _ rfl (by omega) (by omega)) (by omega) hW4).det
  refine FunAll.intro hf (EvalAll.letE (itHv_liftCall hfac hlift hs hsp hj ps hσ dA)
    fun w1 c1 h1 => ?_)
  obtain ⟨a₀, rfl, ha₀, hc1⟩ := h1
  rw [← hM] at hc1
  have wa₀ := wt_encPerm_le a₀
  -- the second lift
  set E1 : List Val := [inp, encPerm a₀]
  have dB := (StDC.mk2 (ga E1 rfl 0 _ rfl (by omega) (by omega))
    (ga E1 rfl 2 _ rfl (by omega) (by omega)) (by omega) hW4).det
  refine EvalAll.letE (itHv_liftCall hfac hlift hs hsp hj ps hσ' dB) fun w2 c2 h2 => ?_
  obtain ⟨a₁, rfl, ha₁, hc2⟩ := h2
  rw [← hM] at hc2
  have wa₁ := wt_encPerm_le a₁
  -- the rest is deterministic
  set E2 : List Val := E1 ++ [encPerm a₁]
  set t' : Perm (Fin k) := if fl = 0 then 1 else a₁ with ht'
  have wt' := wt_encPerm_le t'
  have w1k := wt_encPerm_le (1 : Perm (Fin k))
  have wk := wt_nat_le k
  have d3 := StDC.ite (v := encPerm t') (ga E2 rfl 3 (.nat fl) rfl (by omega) (by omega))
    (fun hx => by
      rw [ht', if_neg hx]
      exact StDC.var' (W := W) (env := E2) (i := 2) rfl (by omega))
    (fun hx => by
      rw [ht', if_pos hx]
      have g0 := ga E2 rfl 0 (liftLabCtx k q ps) rfl (by omega) (by omega)
      have dk := StDC.get g0 (StDC.nat 0 (by omega)) (vs := [.nat k, encGroup (ps.map encPair),
          encGroup ((onePairs ps).map encPair), pSplitCtx k q]) (v := .nat k) rfl (by omega)
      exact StDC.call dk (GI.Lang.range_det hrng k) (by omega)) (by omega)
  set E3 : List Val := E2 ++ [encPerm t']
  have wat := wt_encPerm_le (a₀ * t')
  have z1 : StDC P E3 (.var 1) (encPerm a₀) 1 0 W := StDC.var' rfl (by omega)
  have z3 : StDC P E3 (.var 3) (encPerm t') 1 0 W := StDC.var' rfl (by omega)
  have l1 := wt_list2_le (encPerm a₀) (encPerm t')
  have l2 := wt_list2_le (encPerm a₀) (encPerm (a₀ * t'))
  have d4 := StDC.mk2 z1 (StDC.call (StDC.mk2 z1 z3 (by omega) hW4) (compose_spec hcmp a₀ t')
    (by omega)) (by omega) hW4
  have hout : (Val.list [encPerm a₀, encPerm (a₀ * t')]).wt ≤ W := by omega
  have dall := (StDC.letE d3 d4 hout).det
  refine dall.post fun c hc => ⟨a₀, a₁, rfl, ha₀, ha₁, ?_⟩
  -- the cost
  have hK : 8000 * (k + 1) ^ 3 + permK * (k + 1) ^ 3 ≤ 40000 * M ^ 3 := by
    simp only [permK]; omega
  unfold itHvLtC
  omega

end GI.Impl
