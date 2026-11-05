module

public import Workspace.Impl.SocPreStep
public import Workspace.Impl.OutbSupp

@[expose] public section

/-!
# Computing the socle preimage from a nonabelian-chief chain

Given group encodings `encGroup σH`, `encGroup σR` (`R = gens σR ≤ H = gens σH`, `R` normalized by
`H`, and `H / R` radical-free) and a chain `socCsVal Ws` (`IsNonabelianChiefChain H R (Ws.map gens)`):

1. `socPreEntry` on `[encGroup σH, encGroup σR, socCsVal Ws]`:
   - cuts `σH` and `σR` to at most `n²` generators (`hs`, `rs`) via two calls to
     `normalizedIntersectionPrim` (`jni`),
   - wraps `hs` and `rs` into `encGroup hs'` and `encGroup rs'` via `mkGroupFuns` (`mg`),
   - runs `n² + 1` rounds of `socRoundBody` (`iterFuns` at `it_rd`) starting from
     `[encGroup hs', encGroup rs']` with loop context `[encGroup hs', encGroup rs', socCsVal Ws]`,
   - cuts the resulting `encGroup es` via `jni` to output `u` with
     `GensOf (soclePreimage (gens σH) (gens σR)) u`.
2. `socPreFuns` packages all 100 functions of the socle preimage module at base `b`, using only
   the three proved primitives `NormalizedIntersection` (`jni`), `Membership` (`jm`), and
   `Preimage` (`jpre`), and `socPreAt_of` establishes `SocPreAt`.
3. `socPre_spec` proves correctness and bounds the cost by `socPreCost` in terms of the input
   weight `T = (Val.list [encGroup σH, encGroup σR, socCsVal Ws]).wt`, chain length `Ws.length`,
   and any upper bound `q` on `((gens σR).subgroupOf (soclePreimage (gens σH) (gens σR))).index`.
   `socPre_spec_of_radicalPreimage` specializes this to `gens σR = radicalPreimage (gens σH) N`.
4. `socPreCost_le` proves that `socPreCost` is bounded by an explicit polynomial in `T`, `L`, and
   `q`, and `socPre_cost_le_expLogSq` derives the `expLogSq` bound when `(q : ℝ) ≤ expLogSq c N`
   and `T + 1 ≤ tmVB N`.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited GI.RadicalSocle GI.RadicalFreeOrder Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

set_option maxRecDepth 100000

/-! ### Entry point and module layout -/

/-- **The socle preimage program** on `[encGroup σH, encGroup σR, socCsVal Ws]`:
1. `.var 1 = outbSv hs` (`hs.length ≤ n²`, `gens hs = gens σH`) via `jni` on `[arg 0, arg 0]`
2. `.var 2 = outbSv rs` (`rs.length ≤ n²`, `gens rs = gens σR`) via `jni` on `[arg 1, arg 1]`
3. `.var 3 = encGroup hs'` via `mg` on `[n, .var 1]`
4. `.var 4 = encGroup rs'` via `mg` on `[n, .var 2]`
5. `.var 5 = [encGroup cs, encGroup es]` via `it_rd` (`n² + 1` rounds of `socRoundBody`) starting
   from `[.var 3, .var 4]` with loop context `[.var 3, .var 4, arg 2]`
6. returns `.prim jni (mk2 (.get (.var 5) (.nat 1)) (.get (.var 5) (.nat 1)))`. -/
def socPreEntry (it_rd mg jni : ℕ) : Expr :=
  .letE (.prim jni (mk2 (arg 0) (arg 0)))
  (.letE (.prim jni (mk2 (arg 1) (arg 1)))
  (.letE (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 1)))
  (.letE (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 2)))
  (.letE (.call it_rd (mk3
      (mk3 (.var 3) (.var 4) (arg 2))
      (.arith .add (.arith .mul (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0))) (.nat 1))
      (mk2 (.var 3) (.var 4))))
    (.prim jni (mk2 (.get (.var 5) (.nat 1)) (.get (.var 5) (.nat 1))))))))

/-- Where the socle preimage program and its dependencies sit in `P`. -/
structure SocPreAt (P : Program) (f it_rd rd sc it_sc sc_st jc mg le fk jni jm jpre : ℕ)
    (hni : NormalizedIntersection) (hmem : Membership) (hpre : Preimage) : Prop where
  entry : P.funs[f]? = some (socPreEntry it_rd mg jni)
  iter : P.HasAt it_rd (iterFuns it_rd rd)
  round : SocRoundAt P rd sc it_sc sc_st jc mg le fk jni jm jpre hni hmem hpre

/-- **The complete function block of the socle preimage module** at base `b`, using only the
primitive indices `jni` (NormalizedIntersection), `jm` (Membership), and `jpre` (Preimage).
Total length: 100 functions. -/
def socPreFuns (b jni jm jpre : ℕ) : List Expr :=
  [socPreEntry (b + 5) (b + 11) jni,
    socRoundBody (b + 2) (b + 4) (b + 11) (b + 18) jni (b + 23),
    socScanBody (b + 8),
    socScanStepBody (b + 11) (b + 18) jni,
    socJoinCutF (b + 11) jni] ++
  iterFuns (b + 5) (b + 1) ++
  iterFuns (b + 8) (b + 3) ++
  mkGroupFuns (b + 11) ++
  leFuns (b + 18) jm ++
  gmpFactorKernelFuns (b + 23) jm jpre

theorem length_socPreFuns (b jni jm jpre : ℕ) :
    (socPreFuns b jni jm jpre).length = 100 := rfl

set_option maxHeartbeats 800000 in
/-- **The layout `SocPreAt`** from `P.HasAt b (socPreFuns b jni jm jpre)`. -/
theorem socPreAt_of {P : Program} {b jni jm jpre : ℕ}
    {hni : NormalizedIntersection} {hmem : Membership} {hpre : Preimage}
    (h : P.HasAt b (socPreFuns b jni jm jpre))
    (pni : P.prims[jni]? = some (normalizedIntersectionPrim hni))
    (pm : P.prims[jm]? = some (membershipPrim hmem))
    (ppre : P.prims[jpre]? = some (preimagePrim hpre)) :
    SocPreAt P b (b + 5) (b + 1) (b + 2) (b + 8) (b + 3) (b + 4) (b + 11) (b + 18) (b + 23)
      jni jm jpre hni hmem hpre where
  entry := by
    rw [← Nat.add_zero b]
    exact (h.block (gs := [socPreEntry (b + 5) (b + 11) jni]) 0 rfl).single
  iter := h.block 5 rfl
  round :=
    { round := (h.block (gs := [socRoundBody (b + 2) (b + 4) (b + 11) (b + 18) jni (b + 23)]) 1
        rfl).single
      scan :=
        { scan := (h.block (gs := [socScanBody (b + 8)]) 2 rfl).single
          iter := h.block 8 rfl
          step := (h.block (gs := [socScanStepBody (b + 11) (b + 18) jni]) 3 rfl).single
          mg := h.block 11 rfl
          le := h.block 18 rfl
          ni := pni
          mem := pm }
      joinCut := (h.block (gs := [socJoinCutF (b + 11) jni]) 4 rfl).single
      fk := gmpFactorKernelAt_of (h.block 23 rfl) pm ppre }

/-! ### Cost and specification of `socPreEntry` -/

/-- Cost bound of `socPreEntry` for input weight `T`, chain length `L = Ws.length`, and index bound
`q` on `[soclePreimage H R : R]`. -/
def socPreCost (pni pm pfk : Prim) (T L q : ℕ) : ℕ :=
  3 * pni.boundSize (10 ^ 4 * (T + 1) ^ 6) +
    (T + 1) ^ 2 * socRoundCost pni pm pfk (8000 * (T + 1) ^ 6) L q +
    10 ^ 10 * (T + 1) ^ 9

theorem soc_length_le_wt (σH σR : List (Perm (Fin n))) (Ws : List (List (Perm (Fin n)))) :
    Ws.length ≤ (Val.list [encGroup σH, encGroup σR, socCsVal Ws]).wt := by
  have h1 := length_lt_wt_list (Ws.map fun hs => Val.list (hs.map encPerm))
  simp only [List.length_map] at h1
  have h2 : (socCsVal Ws).wt < (Val.list [encGroup σH, encGroup σR, socCsVal Ws]).wt :=
    wt_le_wt_list (by simp)
  exact (h1.trans h2).le

set_option maxHeartbeats 800000 in
open Classical in
/-- **Specification of `socPreEntry`**: given `R = gens σR ≤ H = gens σH` normalized by `H`,
with `H / R` radical-free, a nonabelian-chief chain `Ws` from `H` to `R`
(`IsNonabelianChiefChain H R (Ws.map gens)`), and an upper bound `q` on
`(R.subgroupOf (soclePreimage H R)).index`, computes `u` with `GensOf (soclePreimage H R) u` at
cost at most `socPreCost`. -/
theorem socPre_spec {hni : NormalizedIntersection} {hmem : Membership} {hpre : Preimage}
    {P : Program} {f it_rd rd sc it_sc sc_st jc mg le fk jni jm jpre : ℕ}
    (hP : SocPreAt P f it_rd rd sc it_sc sc_st jc mg le fk jni jm jpre hni hmem hpre)
    (σH σR : List (Perm (Fin n))) (Ws : List (List (Perm (Fin n))))
    (hRH : gens σR ≤ gens σH) (hnR : GI.Multicoset.Normalizes (gens σH) (gens σR))
    [((gens σR).subgroupOf (gens σH)).Normal]
    (hrf : ∀ N : Subgroup ((gens σH) ⧸ (gens σR).subgroupOf (gens σH)),
      N.Normal → Group.IsSolvable N → N = ⊥)
    (hchain : SocChain (gens σH) (gens σR) (Ws.map gens))
    {q : ℕ} (hq : ((gens σR).subgroupOf (soclePreimage (gens σH) (gens σR))).index ≤ q) :
    FunAll P f (.list [encGroup σH, encGroup σR, socCsVal Ws]) (fun u cost =>
      GensOf (soclePreimage (gens σH) (gens σR)) u ∧
      cost ≤ socPreCost (normalizedIntersectionPrim hni) (membershipPrim hmem)
        (gmpFactorKernelPrim hmem hpre)
        (Val.list [encGroup σH, encGroup σR, socCsVal Ws]).wt Ws.length q) := by
  set in_v := Val.list [encGroup σH, encGroup σR, socCsVal Ws] with hin_v
  set T := in_v.wt with hT
  have hHw : (encGroup σH).wt < T := wt_le_wt_list (vs := [encGroup σH, encGroup σR, socCsVal Ws]) (by simp)
  have hRw : (encGroup σR).wt < T := wt_le_wt_list (vs := [encGroup σH, encGroup σR, socCsVal Ws]) (by simp)
  have hWsw : (socCsVal Ws).wt < T := wt_le_wt_list (vs := [encGroup σH, encGroup σR, socCsVal Ws]) (by simp)
  have hnT : n + 1 ≤ T := by
    have := S_le_wt_encGroup σH
    have : n + 1 ≤ (σH.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hnT2 : (n + 1) ^ 2 ≤ (T + 1) ^ 2 := Nat.pow_le_pow_left (by omega) _
  have hnT6 : (n + 1) ^ 6 ≤ (T + 1) ^ 6 := Nat.pow_le_pow_left (by omega) _
  have hnT9 : (n + 1) ^ 9 ≤ (T + 1) ^ 9 := Nat.pow_le_pow_left (by omega) _
  have hT16 : T + 1 ≤ (T + 1) ^ 6 := Nat.le_self_pow (by decide) _
  have hT26 : (T + 1) ^ 2 ≤ (T + 1) ^ 6 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hT69 : (T + 1) ^ 6 ≤ (T + 1) ^ 9 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hT1_pos : 1 ≤ (T + 1) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  -- step 1: cut `σH` to `hs` (`hs.length ≤ n²`)
  have dH0 := Det.arg' (P := P) (vs := [encGroup σH, encGroup σR, socCsVal Ws])
    (rest := []) (j := 0) (v := encGroup σH) rfl
  rw [← hin_v] at dH0
  have hHH_w := wt_list2_le (encGroup σH) (encGroup σH)
  have hbH := (normalizedIntersectionPrim hni).bound_le
    (show (Val.list [encGroup σH, encGroup σH]).size ≤ 10 ^ 4 * (T + 1) ^ 6 from
      (Val.size_le_wt _).trans (by
        clear * - hHH_w hHw hT16 hT1_pos
        omega))
  refine FunAll.intro hP.entry (EvalAll.letE (normalizedIntersection_call hni hP.round.scan.ni
    (Det.mk2 dH0 dH0) ⟨σH, rfl, rfl⟩ ⟨σH, rfl, rfl⟩ fun x hx y hy =>
      (gens σH).mul_mem ((gens σH).mul_mem hx hy) ((gens σH).inv_mem hx)) fun v1 c1 h1 => ?_)
  clear dH0
  obtain ⟨⟨hs, rfl, hhl, hhs⟩, hc1⟩ := h1
  rw [inf_idem] at hhs
  -- step 2: cut `σR` to `rs` (`rs.length ≤ n²`)
  have dR1 := Det.arg' (P := P) (vs := [encGroup σH, encGroup σR, socCsVal Ws])
    (rest := [outbSv hs]) (j := 1) (v := encGroup σR) rfl
  rw [← hin_v] at dR1
  have hRR_w := wt_list2_le (encGroup σR) (encGroup σR)
  have hbR := (normalizedIntersectionPrim hni).bound_le
    (show (Val.list [encGroup σR, encGroup σR]).size ≤ 10 ^ 4 * (T + 1) ^ 6 from
      (Val.size_le_wt _).trans (by
        clear * - hRR_w hRw hT16 hT1_pos
        omega))
  refine EvalAll.letE (normalizedIntersection_call hni hP.round.scan.ni
    (Det.mk2 dR1 dR1) ⟨σR, rfl, rfl⟩ ⟨σR, rfl, rfl⟩ fun x hx y hy =>
      (gens σR).mul_mem ((gens σR).mul_mem hx hy) ((gens σR).inv_mem hx)) fun v2 c2 h2 => ?_
  clear dR1
  obtain ⟨⟨rs, rfl, hrl, hrs⟩, hc2⟩ := h2
  rw [inf_idem] at hrs
  -- step 3: `encGroup hs'` via `mg`
  set env2 := [in_v, outbSv hs, outbSv rs]
  have dn2 := Det.get' (Det.arg' (P := P) (vs := [encGroup σH, encGroup σR, socCsVal Ws])
    (rest := [outbSv hs, outbSv rs]) (j := 0) (v := encGroup σH) rfl)
    (Det.nat 0) (v := .nat n) rfl
  rw [← hin_v] at dn2
  have dhs2 := Det.var' (P := P) (env := env2) (i := 1) (v := outbSv hs) rfl
  obtain ⟨hs', hhl', hhs', dH_mk, hHw'⟩ := outb_mk_det hP.round.scan.mg dn2 dhs2
    (⟨hs, rfl, hhl, rfl⟩ : GensVal n (outbSv hs) (gens hs))
  rw [hhs] at hhs'
  clear dn2 dhs2
  refine EvalAll.letE dH_mk fun v3 c3 h3 => ?_
  obtain ⟨rfl, hc3⟩ := h3
  clear dH_mk
  -- step 4: `encGroup rs'` via `mg`
  set env3 := [in_v, outbSv hs, outbSv rs, encGroup hs']
  have dn3 := Det.get' (Det.arg' (P := P) (vs := [encGroup σH, encGroup σR, socCsVal Ws])
    (rest := [outbSv hs, outbSv rs, encGroup hs']) (j := 0) (v := encGroup σH) rfl)
    (Det.nat 0) (v := .nat n) rfl
  rw [← hin_v] at dn3
  have drs3 := Det.var' (P := P) (env := env3) (i := 2) (v := outbSv rs) rfl
  obtain ⟨rs', hrl', hrs', dR_mk, hRw'⟩ := outb_mk_det hP.round.scan.mg dn3 drs3
    (⟨rs, rfl, hrl, rfl⟩ : GensVal n (outbSv rs) (gens rs))
  rw [hrs] at hrs'
  clear dn3 drs3
  refine EvalAll.letE dR_mk fun v4 c4 h4 => ?_
  obtain ⟨rfl, hc4⟩ := h4
  clear dR_mk
  -- step 5: run `iter_spec` for `k = n² + 1` rounds of `socRound_spec`
  have hRH' : gens rs' ≤ gens hs' := by rw [hrs', hhs']; exact hRH
  have hnR' : GI.Multicoset.Normalizes (gens hs') (gens rs') := by rw [hrs', hhs']; exact hnR
  have : ((gens rs').subgroupOf (gens hs')).Normal := GI.Multicoset.normal_of_normalizes hnR'
  have hrf_tr : ∀ (H R : Subgroup (Perm (Fin n))) [(R.subgroupOf H).Normal],
      H = gens σH → R = gens σR →
      ∀ N : Subgroup (H ⧸ R.subgroupOf H), N.Normal → Group.IsSolvable N → N = ⊥ := by
    rintro _ _ _ rfl rfl
    exact hrf
  have hrf' := hrf_tr (gens hs') (gens rs') hhs' hrs'
  have hchain' : SocChain (gens hs') (gens rs') (Ws.map gens) := by
    rw [hhs', hrs']; exact hchain
  have hq' : ((gens rs').subgroupOf (soclePreimage (gens hs') (gens rs'))).index ≤ q := by
    rw [hhs', hrs']; exact hq
  have h0 : SocRoundValInv (gens hs') (gens rs') 0 (.list [encGroup hs', encGroup rs']) :=
    ⟨hs', rs', rfl, hhl', hrl', soc_round_init hRH' hnR'⟩
  set k := n ^ 2 + 1 with hk
  set M := 1500 * (n + 1) ^ 6 with hM
  set B := socRoundCost (normalizedIntersectionPrim hni) (membershipPrim hmem)
    (gmpFactorKernelPrim hmem hpre) (8000 * (T + 1) ^ 6) Ws.length q with hB
  set c_rd := Val.list [encGroup hs', encGroup rs', socCsVal Ws] with hc_rd
  have hcrd_w0 : c_rd.wt ≤ 2 * ((encGroup hs').wt + (encGroup rs').wt + (socCsVal Ws).wt) + 7 :=
    wt_list3_le (encGroup hs') (encGroup rs') (socCsVal Ws)
  have hcrd_w : c_rd.wt ≤ 1500 * (T + 1) ^ 6 := by
    clear * - hcrd_w0 hHw' hRw' hWsw hnT6 hT16 hT1_pos
    omega
  have hn2e : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  have hk_T2 : k ≤ (T + 1) ^ 2 := by
    have : k ≤ (n + 1) ^ 2 := by clear * - hk hn2e; omega
    exact this.trans hnT2
  have hk_T6 : k ≤ (T + 1) ^ 6 := hk_T2.trans hT26
  have hstep : ∀ i acc, i < k → SocRoundValInv (gens hs') (gens rs') i acc →
      FunAll P rd (.list [c_rd, .nat i, acc]) (fun w cw =>
        SocRoundValInv (gens hs') (gens rs') (i + 1) w ∧ cw ≤ B) := by
    intro i acc hi hinv
    have hacc_w := soc_round_val_wt hinv
    refine (socRound_spec hP.round hRH' hnR' hrf' hchain' hq' hinv).mono fun w cw h =>
      ⟨h.1, h.2.trans (socRoundCost_mono _ _ _ ?_ le_rfl le_rfl)⟩
    have hw3 := wt_list3_le c_rd (.nat i) acc
    have hwi := wt_nat_le i
    show (Val.list [c_rd, .nat i, acc]).wt ≤ 8000 * (T + 1) ^ 6
    clear * - hw3 hwi hi hk_T6 hcrd_w hacc_w hnT6 hT1_pos
    omega
  have hit := iter_spec hP.iter (c := c_rd) (k := k) (M := M) (B := fun _ => B) h0
    (fun i acc _ h => soc_round_val_wt h) hstep
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hit
  set env4 := [in_v, outbSv hs, outbSv rs, encGroup hs', encGroup rs']
  have dH4 := Det.var' (P := P) (env := env4) (i := 3) (v := encGroup hs') rfl
  have dR4 := Det.var' (P := P) (env := env4) (i := 4) (v := encGroup rs') rfl
  have dWs4 := Det.arg' (P := P) (vs := [encGroup σH, encGroup σR, socCsVal Ws])
    (rest := [outbSv hs, outbSv rs, encGroup hs', encGroup rs'])
    (j := 2) (v := socCsVal Ws) rfl
  rw [← hin_v] at dWs4
  have dcrd := Det.mk3 dH4 dR4 dWs4
  rw [← hc_rd] at dcrd
  have dn4 := Det.get' (Det.arg' (P := P) (vs := [encGroup σH, encGroup σR, socCsVal Ws])
    (rest := [outbSv hs, outbSv rs, encGroup hs', encGroup rs'])
    (j := 0) (v := encGroup σH) rfl) (Det.nat 0) (v := .nat n) rfl
  rw [← hin_v] at dn4
  have dk := Det.arith' (op := .add) (Det.arith' (op := .mul) dn4 dn4 rfl) (Det.nat 1) (z := k)
    (by simp [BinOp.eval, hk, sq])
  have dacc0 := Det.mk2 dH4 dR4
  have darg := Det.mk3 dcrd dk dacc0
  have hhw_H : (outbSv hs).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq hhl
  have hrw_R : (outbSv rs).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq hrl
  have hnw := wt_nat_le n
  have h0w := wt_nat_le 0
  have h1w := wt_nat_le 1
  refine EvalAll.letE (Ra := fun w cw => SocRoundValInv (gens hs') (gens rs') k w ∧
      cw ≤ k * B + 10 ^ 8 * (T + 1) ^ 9)
    (EvalAll.call_funAll darg fun v ca hv => ?_) fun v5 c5 h5 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine hit.mono fun w cw h => ⟨h.1, ?_⟩
    have hw_wt := soc_round_val_wt h.1
    have hcw := h.2
    have h0_wt := soc_round_val_wt h0
    have hkw := wt_nat_le k
    have hnn : n * n ≤ (T + 1) ^ 6 := by
      have : n * n ≤ (n + 1) ^ 2 := by
        rw [sq]; exact Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n)
      exact (this.trans hnT2).trans hT26
    have hw3 := wt_list3_le c_rd (.nat k) (.list [encGroup hs', encGroup rs'])
    have hw_acc0 := wt_list2_le (encGroup hs') (encGroup rs')
    have hwt_iter : (Val.list [c_rd, .nat k, .list [encGroup hs', encGroup rs']]).wt + k +
        M + 1 ≤ 8000 * (T + 1) ^ 6 := by
      clear * - hw3 hw_acc0 hcrd_w hkw hHw' hRw' hk_T6 hnT6 hT1_pos hM
      omega
    have hk1_T3 : k + 1 ≤ 2 * (T + 1) ^ 3 := by
      have h1 : 1 ≤ (T + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have h23 : (T + 1) ^ 2 ≤ (T + 1) ^ 3 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
      calc k + 1 ≤ 2 * (T + 1) ^ 2 := by clear * - hk_T2 h1; omega
        _ ≤ 2 * (T + 1) ^ 3 := Nat.mul_le_mul_left 2 h23
    have hL : loopModK * (k + 1) *
        ((Val.list [c_rd, .nat k, .list [encGroup hs', encGroup rs']]).wt + k + M + 1) ≤
        2 * 10 ^ 7 * (T + 1) ^ 9 := by
      calc _ ≤ loopModK * (2 * (T + 1) ^ 3) * (8000 * (T + 1) ^ 6) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hk1_T3) hwt_iter
        _ = 16 * 10 ^ 6 * ((T + 1) ^ 3 * (T + 1) ^ 6) := by simp only [loopModK]; ring
        _ = 16 * 10 ^ 6 * (T + 1) ^ 9 := by rw [← pow_add]
        _ ≤ 2 * 10 ^ 7 * (T + 1) ^ 9 := Nat.mul_le_mul_right _ (by norm_num)
    have hmul : BinOp.mul.eval n n = n * n := rfl
    clear * - hca hcw hL hw_wt hw3 hw_acc0 hcrd_w0 hcrd_w hHw' hRw' hWsw
      hnw h0w h1w hkw hnn hmul hk_T6 hnT hnT6 hT16 hT69 hT1_pos hM
    omega
  clear dH4 dR4 dWs4 dcrd dn4 dk dacc0 darg hit hstep
  -- step 6: extract `encGroup es` and cut via `jni` to `GensOf (soclePreimage (gens σH) (gens σR)) u`
  obtain ⟨⟨cs, es, rfl, hcl, hel, hrinv⟩, hc5⟩ := h5
  have hE_eq : gens es = soclePreimage (gens σH) (gens σR) := by
    rw [← hhs', ← hrs']
    exact soc_round_done hRH' hrinv
  set env5 := env4 ++ [Val.list [encGroup cs, encGroup es]]
  have dv5 := Det.var' (P := P) (env := env5) (i := 5) (v := .list [encGroup cs, encGroup es]) rfl
  have de5 := Det.get' dv5 (Det.nat 1) (v := encGroup es) rfl
  have hcw_end := wt_encGroup_sq hcl
  have hew_end := wt_encGroup_sq hel
  have hv5_w := wt_list2_le (encGroup cs) (encGroup es)
  have hEE_w := wt_list2_le (encGroup es) (encGroup es)
  have hbE := (normalizedIntersectionPrim hni).bound_le
    (show (Val.list [encGroup es, encGroup es]).size ≤ 10 ^ 4 * (T + 1) ^ 6 from
      (Val.size_le_wt _).trans (by
        clear * - hEE_w hew_end hnT6 hT1_pos
        omega))
  refine (normalizedIntersection_call hni hP.round.scan.ni (Det.mk2 de5 de5)
    ⟨es, rfl, rfl⟩ ⟨es, rfl, rfl⟩ fun x hx y hy =>
      (gens es).mul_mem ((gens es).mul_mem hx hy) ((gens es).inv_mem hx)).mono fun u cu h =>
    ⟨?_, ?_⟩
  · obtain ⟨hu, -⟩ := h
    rw [inf_idem, hE_eq] at hu
    exact hu
  · obtain ⟨hu0, hcu⟩ := h
    have huw := GensVal.wt_le hu0
    have hnhs_w := wt_list2_le (.nat n) (outbSv hs)
    have hnrs_w := wt_list2_le (.nat n) (outbSv rs)
    have hmk_T9 : 8 * mkGroupK * (n + 1) ^ 9 ≤ 10 ^ 6 * (T + 1) ^ 9 := by
      simp only [mkGroupK]; clear * - hnT9; omega
    have hkB : k * B ≤ (T + 1) ^ 2 * B := Nat.mul_le_mul_right _ hk_T2
    set NB := (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (T + 1) ^ 6) with hNB
    have hgoal_eq : socPreCost (normalizedIntersectionPrim hni) (membershipPrim hmem)
        (gmpFactorKernelPrim hmem hpre) T Ws.length q =
        3 * NB + (T + 1) ^ 2 * B + 10 ^ 10 * (T + 1) ^ 9 := by
      simp only [socPreCost, hNB, hB]
    rw [hgoal_eq]
    clear * - hc1 hc2 hc3 hc4 hc5 hcu hbH hbR hbE hkB hHH_w hRR_w hEE_w hHw hRw hWsw
      hhw_H hrw_R hHw' hRw' hcw_end hew_end hv5_w huw hnhs_w hnrs_w hnw h0w h1w hmk_T9
      hnT hnT6 hnT9 hT16 hT69 hT1_pos
    omega

open Classical in
/-- **Convenience corollary of `socPre_spec` for `R = radicalPreimage H N`**: when
`gens σR = radicalPreimage (gens σH) N` for `N ⊴ gens σH`, `(gens σH) / (gens σR)` is
automatically radical-free (`soc_radicalFree_of_radicalPreimage_eq`), so `socPreEntry` computes
`GensOf (soclePreimage (gens σH) (gens σR)) u`. -/
theorem socPre_spec_of_radicalPreimage {hni : NormalizedIntersection} {hmem : Membership}
    {hpre : Preimage} {P : Program} {f it_rd rd sc it_sc sc_st jc mg le fk jni jm jpre : ℕ}
    (hP : SocPreAt P f it_rd rd sc it_sc sc_st jc mg le fk jni jm jpre hni hmem hpre)
    {N : Subgroup (Perm (Fin n))}
    (σH σR : List (Perm (Fin n))) (Ws : List (List (Perm (Fin n))))
    (hNH : N ≤ gens σH) (hnN : GI.Multicoset.Normalizes (gens σH) N)
    (hR : gens σR = GI.Multicoset.radicalPreimage (gens σH) N)
    (hchain : SocChain (gens σH) (gens σR) (Ws.map gens))
    {q : ℕ} (hq : ((gens σR).subgroupOf (soclePreimage (gens σH) (gens σR))).index ≤ q) :
    FunAll P f (.list [encGroup σH, encGroup σR, socCsVal Ws]) (fun u cost =>
      GensOf (soclePreimage (gens σH) (gens σR)) u ∧
      cost ≤ socPreCost (normalizedIntersectionPrim hni) (membershipPrim hmem)
        (gmpFactorKernelPrim hmem hpre)
        (Val.list [encGroup σH, encGroup σR, socCsVal Ws]).wt Ws.length q) := by
  obtain ⟨hRH0, hNR0, -⟩ := GI.Multicoset.radicalPreimage_spec hNH hnN
  have hRH : gens σR ≤ gens σH := hR ▸ hRH0
  have : (N.subgroupOf (gens σH)).Normal := GI.Multicoset.normal_of_normalizes hnN
  have hnR : GI.Multicoset.Normalizes (gens σH) (gens σR) := by
    rw [hR]; exact GI.Multicoset.normalizes_of_normal hRH0
  have : ((gens σR).subgroupOf (gens σH)).Normal := GI.Multicoset.normal_of_normalizes hnR
  have hrf : ∀ (R : Subgroup (Perm (Fin n))) [(R.subgroupOf (gens σH)).Normal],
      R = GI.Multicoset.radicalPreimage (gens σH) N →
      ∀ M : Subgroup ((gens σH) ⧸ R.subgroupOf (gens σH)),
        M.Normal → Group.IsSolvable M → M = ⊥ := by
    rintro _ _ rfl
    exact radicalPreimage_quotient_radicalFree
  exact socPre_spec hP σH σR Ws hRH hnR (hrf (gens σR) hR) hchain hq

/-! ### Explicit polynomial and `expLogSq` cost bounds -/

/-- The constant `1000 * (2000 * 80011 ^ 6 + 1) ^ 6` bounding all `boundSize` arguments divided by
`(T + q + 1) ^ 216`. -/
def socY0 : ℕ := 1000 * (2000 * 80011 ^ 6 + 1) ^ 6

theorem socY0_eq : 1000 * (2000 * 80011 ^ 6 + 1) ^ 6 = socY0 := rfl

theorem le_socY0_1000 : 1000 ≤ socY0 :=
  Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (Nat.succ_pos _))

theorem le_socY0_10000 : 10 ^ 4 ≤ socY0 := by
  unfold socY0
  have h1 : 2 ≤ 2000 * 80011 ^ 6 + 1 := by
    have ha : 1 ≤ 80011 ^ 6 := Nat.one_le_pow _ _ (by decide)
    have hb : 2 ≤ 2000 * 80011 ^ 6 :=
      (by decide : 2 ≤ 2000).trans (Nat.le_mul_of_pos_right _ ha)
    exact hb.trans (Nat.le_succ _)
  have h2 : 2 ^ 6 ≤ (2000 * 80011 ^ 6 + 1) ^ 6 := Nat.pow_le_pow_left h1 6
  have h3 : (10 : ℕ) ^ 4 ≤ 1000 * 2 ^ 6 := by decide
  exact h3.trans (Nat.mul_le_mul_left _ h2)

theorem le_socY0_jc : 10 ^ 4 * 8001 ^ 6 ≤ socY0 := by
  unfold socY0
  have h1 : 10 * 8001 ≤ 2000 * 80011 ^ 6 + 1 := by
    have ha : 10 * 8001 ≤ 2000 * 80011 := by decide
    have hb : 80011 ≤ 80011 ^ 6 := Nat.le_self_pow (by decide) _
    exact (ha.trans (Nat.mul_le_mul_left 2000 hb)).trans (Nat.le_succ _)
  have h2 : (10 * 8001) ^ 6 ≤ (2000 * 80011 ^ 6 + 1) ^ 6 := Nat.pow_le_pow_left h1 6
  have h3 : (10 : ℕ) ^ 4 ≤ 1000 * 10 ^ 6 := by decide
  calc 10 ^ 4 * 8001 ^ 6 ≤ 1000 * 10 ^ 6 * 8001 ^ 6 := Nat.mul_le_mul_right _ h3
    _ = 1000 * (10 * 8001) ^ 6 := by rw [mul_pow, Nat.mul_assoc]
    _ ≤ 1000 * (2000 * 80011 ^ 6 + 1) ^ 6 := Nat.mul_le_mul_left _ h2

theorem le_socY0_rd : 1000 * 8001 ^ 6 ≤ socY0 :=
  (Nat.mul_le_mul_right _ (by decide : 1000 ≤ 10 ^ 4)).trans le_socY0_jc

attribute [irreducible] socY0

private theorem soc_mul_add_le {A B c : ℕ} (hB : 1 ≤ B) : A * B + c ≤ (A + c) * B := by
  rw [Nat.add_mul]
  exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hB) _

/-- The sum of the exponents of `pni`, `pm`, and `pfk`. -/
def socPreKs (pni pm pfk : Prim) : ℕ := pni.k + pm.k + pfk.k

/-- The sum of the constants of `pni`, `pm`, and `pfk` scaled by `socY0 + 2`. -/
def socPreKp (pni pm pfk : Prim) : ℕ :=
  pni.c * (socY0 + 2) ^ pni.k + pm.c * (socY0 + 2) ^ pm.k + pfk.c * (socY0 + 2) ^ pfk.k

/-- The exponent of `T + q + 1` in the polynomial bound of `socPreCost`. -/
def socPreD (pni pm pfk : Prim) : ℕ := 650 + 216 * socPreKs pni pm pfk

/-- The leading constant in the polynomial bound of `socPreCost`. -/
def socPreK (pni pm pfk : Prim) : ℕ :=
  20 * socY0 * socPreKp pni pm pfk + 3 * 10 ^ 9 * socY0 ^ 3

theorem soc_bS_le_at {p : Prim} {B X e : ℕ} (hX : 1 ≤ X)
    (hB : B ≤ socY0 * X ^ 216) (hk : p.k ≤ e) :
    p.boundSize B ≤ p.c * (socY0 + 2) ^ p.k * X ^ (216 * e) := by
  have hb := soc_boundSize_mono p hB
  unfold Prim.boundSize at hb
  have h1 : socY0 * X ^ 216 + 2 ≤ (socY0 + 2) * X ^ 216 :=
    soc_mul_add_le (Nat.one_le_pow _ _ hX)
  have h2 : p.c * (socY0 * X ^ 216 + 2) ^ p.k ≤ p.c * (socY0 + 2) ^ p.k * X ^ (216 * p.k) := by
    calc p.c * (socY0 * X ^ 216 + 2) ^ p.k ≤ p.c * ((socY0 + 2) * X ^ 216) ^ p.k :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
      _ = p.c * (socY0 + 2) ^ p.k * X ^ (216 * p.k) := by rw [mul_pow, ← pow_mul]; ring
  exact hb.trans (h2.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right hX (Nat.mul_le_mul_left 216 hk))))

/-- **`socPreCost` is polynomial in `T`, `L`, and `q`**:
`socPreCost pni pm pfk T L q ≤ socPreK pni pm pfk * ((L + 1) * (T + q + 1) ^ socPreD pni pm pfk)`. -/
theorem socPreCost_le (pni pm pfk : Prim) (T L q : ℕ) :
    socPreCost pni pm pfk T L q ≤
      socPreK pni pm pfk * ((L + 1) * (T + q + 1) ^ socPreD pni pm pfk) := by
  set X := T + q + 1 with hXdef
  have hX : 1 ≤ X := Nat.succ_pos _
  have hTX : T + 1 ≤ X := by omega
  have hqX : q + 1 ≤ X := by omega
  have hL1 : 1 ≤ L + 1 := Nat.succ_pos _
  have hXX : ∀ a b, a ≤ b → X ^ a ≤ X ^ b := fun a b h => Nat.pow_le_pow_right hX h
  have hX1 : ∀ a, 1 ≤ X ^ a := fun a => Nat.one_le_pow _ _ hX
  set Ks := socPreKs pni pm pfk with hKs
  set Kp := socPreKp pni pm pfk with hKp
  set Q := Kp * X ^ (216 * Ks) with hQ
  set Ym := socY0 * X ^ 216 with hYm
  have hD : socPreD pni pm pfk = 650 + 216 * Ks := rfl
  have hK : socPreK pni pm pfk = 20 * socY0 * Kp + 3 * 10 ^ 9 * socY0 ^ 3 := rfl
  clear_value X
  have hY0_pos : 1000 ≤ socY0 := le_socY0_1000
  have hYm3 : Ym ^ 3 = socY0 ^ 3 * X ^ 648 := by
    rw [hYm, mul_pow, ← pow_mul]
  -- Bound the arguments of `boundSize` by `Ym = socY0 * X ^ 216`
  set W_rd := 8000 * (T + 1) ^ 6 with hW_rd
  set W_sc := 10 * W_rd + 10 with hW_sc
  have hW_rd_X : W_rd ≤ 8000 * X ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hTX 6)
  have hW_sc1_X : W_sc + 1 ≤ 80011 * X ^ 6 := by
    have := hX1 6
    omega
  clear_value W_rd W_sc
  have hY_sc : 1000 * (2000 * (W_sc + 1) ^ 6 + 1) ^ 6 ≤ Ym := by
    have h1 : 2000 * (W_sc + 1) ^ 6 ≤ 2000 * 80011 ^ 6 * X ^ 36 := by
      calc 2000 * (W_sc + 1) ^ 6 ≤ 2000 * (80011 * X ^ 6) ^ 6 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hW_sc1_X 6)
        _ = 2000 * 80011 ^ 6 * X ^ 36 := by rw [mul_pow, ← pow_mul, ← Nat.mul_assoc]
    have hW_sc_inner : 2000 * (W_sc + 1) ^ 6 + 1 ≤ (2000 * 80011 ^ 6 + 1) * X ^ 36 :=
      (Nat.add_le_add_right h1 1).trans (soc_mul_add_le (hX1 36))
    calc 1000 * (2000 * (W_sc + 1) ^ 6 + 1) ^ 6
        ≤ 1000 * ((2000 * 80011 ^ 6 + 1) * X ^ 36) ^ 6 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hW_sc_inner 6)
      _ = 1000 * (2000 * 80011 ^ 6 + 1) ^ 6 * X ^ 216 := by
          rw [mul_pow, ← pow_mul, ← Nat.mul_assoc]
      _ = Ym := by rw [socY0_eq, hYm]
  have hY_rd : 1000 * (W_rd + q + 1) ^ 6 ≤ Ym := by
    have h1 : W_rd + q + 1 ≤ 8001 * X ^ 6 := by
      have : X ≤ X ^ 6 := Nat.le_self_pow (by decide) _
      omega
    calc 1000 * (W_rd + q + 1) ^ 6 ≤ 1000 * (8001 * X ^ 6) ^ 6 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 6)
      _ = 1000 * 8001 ^ 6 * X ^ 36 := by rw [mul_pow, ← pow_mul, ← Nat.mul_assoc]
      _ ≤ socY0 * X ^ 216 := Nat.mul_le_mul le_socY0_rd (hXX 36 216 (by decide))
  have hY_jc : 10 ^ 4 * (W_rd + 1) ^ 6 ≤ Ym := by
    have h1 : W_rd + 1 ≤ 8001 * X ^ 6 := by have := hX1 6; omega
    calc 10 ^ 4 * (W_rd + 1) ^ 6 ≤ 10 ^ 4 * (8001 * X ^ 6) ^ 6 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 6)
      _ = 10 ^ 4 * 8001 ^ 6 * X ^ 36 := by rw [mul_pow, ← pow_mul, ← Nat.mul_assoc]
      _ ≤ socY0 * X ^ 216 := Nat.mul_le_mul le_socY0_jc (hXX 36 216 (by decide))
  have hY_T : 10 ^ 4 * (T + 1) ^ 6 ≤ Ym := by
    calc 10 ^ 4 * (T + 1) ^ 6 ≤ 10 ^ 4 * X ^ 6 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hTX 6)
      _ ≤ socY0 * X ^ 216 := Nat.mul_le_mul le_socY0_10000 (hXX 6 216 (by decide))
  -- Primitive bounds at `Ym`
  have hQs : Q = pni.c * (socY0 + 2) ^ pni.k * X ^ (216 * Ks) +
      pm.c * (socY0 + 2) ^ pm.k * X ^ (216 * Ks) +
      pfk.c * (socY0 + 2) ^ pfk.k * X ^ (216 * Ks) := by
    simp only [hQ, hKp, socPreKp]; ring
  have qni_Ym : pni.boundSize Ym ≤ Q := by
    have := soc_bS_le_at (p := pni) hX (le_rfl : Ym ≤ socY0 * X ^ 216)
      (e := Ks) (by simp only [hKs, socPreKs]; omega)
    omega
  have qm_Ym : pm.boundSize Ym ≤ Q := by
    have := soc_bS_le_at (p := pm) hX (le_rfl : Ym ≤ socY0 * X ^ 216)
      (e := Ks) (by simp only [hKs, socPreKs]; omega)
    omega
  have qfk_Ym : pfk.boundSize Ym ≤ Q := by
    have := soc_bS_le_at (p := pfk) hX (le_rfl : Ym ≤ socY0 * X ^ 216)
      (e := Ks) (by simp only [hKs, socPreKs]; omega)
    omega
  have hYm_pos : 1 ≤ Ym :=
    Nat.mul_pos (Nat.lt_of_lt_of_le (by decide : 0 < 1000) hY0_pos) (hX1 216)
  clear_value Ks Kp Q Ym
  have qni_sc : pni.boundSize (1000 * (2000 * (W_sc + 1) ^ 6 + 1) ^ 6) ≤ Q :=
    (soc_boundSize_mono pni hY_sc).trans qni_Ym
  have qm_sc : pm.boundSize (1000 * (2000 * (W_sc + 1) ^ 6 + 1) ^ 6) ≤ Q :=
    (soc_boundSize_mono pm hY_sc).trans qm_Ym
  have qni_rd : pni.boundSize (1000 * (W_rd + q + 1) ^ 6) ≤ Q :=
    (soc_boundSize_mono pni hY_rd).trans qni_Ym
  have qm_rd : pm.boundSize (1000 * (W_rd + q + 1) ^ 6) ≤ Q :=
    (soc_boundSize_mono pm hY_rd).trans qm_Ym
  have qfk_rd : pfk.boundSize (1000 * (W_rd + q + 1) ^ 6) ≤ Q :=
    (soc_boundSize_mono pfk hY_rd).trans qfk_Ym
  have qni_jc : pni.boundSize (10 ^ 4 * (W_rd + 1) ^ 6) ≤ Q :=
    (soc_boundSize_mono pni hY_jc).trans qni_Ym
  have qni_T : pni.boundSize (10 ^ 4 * (T + 1) ^ 6) ≤ Q :=
    (soc_boundSize_mono pni hY_T).trans qni_Ym
  have hQ_YmQ : Q ≤ Ym * Q := Nat.le_mul_of_pos_left _ hYm_pos
  -- 1. `socScanStepCost pni pm (2000 * (W_sc + 1) ^ 6)`
  have hScanSt : socScanStepCost pni pm (2000 * (W_sc + 1) ^ 6) ≤
      2 * (Ym * Q) + 10 ^ 8 * Ym ^ 3 := by
    unfold socScanStepCost
    have h1 : 1000 * (2000 * (W_sc + 1) ^ 6 + 1) ^ 6 *
        pm.boundSize (1000 * (2000 * (W_sc + 1) ^ 6 + 1) ^ 6) ≤ Ym * Q :=
      Nat.mul_le_mul hY_sc qm_sc
    have h2 : (1000 * (2000 * (W_sc + 1) ^ 6 + 1) ^ 6) ^ 3 ≤ Ym ^ 3 :=
      Nat.pow_le_pow_left hY_sc 3
    omega
  -- 2. `socScanCost pni pm W_sc L`
  have hScan : socScanCost pni pm W_sc L ≤
      (L + 1) * (2 * (Ym * Q) + 2 * 10 ^ 8 * Ym ^ 3) := by
    unfold socScanCost
    have h1 : 10 ^ 7 * (L + 1) * (W_sc + 1) ^ 6 ≤ (L + 1) * (10 ^ 8 * Ym ^ 3) := by
      have hW6_Ym : (W_sc + 1) ^ 6 ≤ Ym := by
        calc (W_sc + 1) ^ 6
            ≤ 2000 * (W_sc + 1) ^ 6 + 1 := by omega
          _ ≤ (2000 * (W_sc + 1) ^ 6 + 1) ^ 6 := Nat.le_self_pow (by decide) _
          _ ≤ 1000 * (2000 * (W_sc + 1) ^ 6 + 1) ^ 6 := by omega
          _ ≤ Ym := hY_sc
      have hYm_Ym3 : Ym ≤ Ym ^ 3 := Nat.le_self_pow (by decide) _
      calc 10 ^ 7 * (L + 1) * (W_sc + 1) ^ 6
          ≤ 10 ^ 7 * (L + 1) * Ym ^ 3 :=
            Nat.mul_le_mul_left _ (hW6_Ym.trans hYm_Ym3)
        _ = (L + 1) * (10 ^ 7 * Ym ^ 3) := by ring
        _ ≤ (L + 1) * (10 ^ 8 * Ym ^ 3) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by decide))
    calc (L + 1) * socScanStepCost pni pm (2000 * (W_sc + 1) ^ 6) +
          10 ^ 7 * (L + 1) * (W_sc + 1) ^ 6
        ≤ (L + 1) * (2 * (Ym * Q) + 10 ^ 8 * Ym ^ 3) + (L + 1) * (10 ^ 8 * Ym ^ 3) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hScanSt) h1
      _ = (L + 1) * (2 * (Ym * Q) + 2 * 10 ^ 8 * Ym ^ 3) := by ring
  -- 3. `socJoinCutCost pni W_rd`
  have hJC : socJoinCutCost pni W_rd ≤ Ym * Q + 10 ^ 8 * Ym ^ 3 := by
    unfold socJoinCutCost
    have h1 : (W_rd + 1) ^ 9 ≤ Ym ^ 3 := by
      have : (W_rd + 1) ^ 9 ≤ ((W_rd + 1) ^ 6) ^ 3 := by
        rw [← pow_mul]
        exact Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
      exact this.trans (Nat.pow_le_pow_left (by omega : (W_rd + 1) ^ 6 ≤ Ym) 3)
    have := Nat.mul_le_mul_left (10 ^ 8) h1
    omega
  -- 4. `socRoundCost pni pm pfk W_rd L q`
  have hRound : socRoundCost pni pm pfk W_rd L q ≤
      (L + 1) * (10 * (Ym * Q) + 2 * 10 ^ 9 * Ym ^ 3) := by
    unfold socRoundCost
    rw [← hW_sc]
    have h1 : 1000 * (W_rd + q + 1) ^ 6 * pm.boundSize (1000 * (W_rd + q + 1) ^ 6) ≤ Ym * Q :=
      Nat.mul_le_mul hY_rd qm_rd
    have h2 : (1000 * (W_rd + q + 1) ^ 6) ^ 3 ≤ Ym ^ 3 := Nat.pow_le_pow_left hY_rd 3
    have hrest : socJoinCutCost pni W_rd + pfk.boundSize (1000 * (W_rd + q + 1) ^ 6) +
        pni.boundSize (1000 * (W_rd + q + 1) ^ 6) +
        1000 * (W_rd + q + 1) ^ 6 * pm.boundSize (1000 * (W_rd + q + 1) ^ 6) +
        10 ^ 9 * (1000 * (W_rd + q + 1) ^ 6) ^ 3 ≤
        (L + 1) * (4 * (Ym * Q) + 11 * 10 ^ 8 * Ym ^ 3) := by
      have h0 : socJoinCutCost pni W_rd + pfk.boundSize (1000 * (W_rd + q + 1) ^ 6) +
          pni.boundSize (1000 * (W_rd + q + 1) ^ 6) +
          1000 * (W_rd + q + 1) ^ 6 * pm.boundSize (1000 * (W_rd + q + 1) ^ 6) +
          10 ^ 9 * (1000 * (W_rd + q + 1) ^ 6) ^ 3 ≤
          4 * (Ym * Q) + 11 * 10 ^ 8 * Ym ^ 3 := by
        have := Nat.mul_le_mul_left (10 ^ 9) h2
        omega
      calc _ ≤ 1 * (4 * (Ym * Q) + 11 * 10 ^ 8 * Ym ^ 3) := by omega
        _ ≤ (L + 1) * (4 * (Ym * Q) + 11 * 10 ^ 8 * Ym ^ 3) := Nat.mul_le_mul_right _ hL1
    calc socScanCost pni pm W_sc L + socJoinCutCost pni W_rd +
          pfk.boundSize (1000 * (W_rd + q + 1) ^ 6) +
          pni.boundSize (1000 * (W_rd + q + 1) ^ 6) +
          1000 * (W_rd + q + 1) ^ 6 * pm.boundSize (1000 * (W_rd + q + 1) ^ 6) +
          10 ^ 9 * (1000 * (W_rd + q + 1) ^ 6) ^ 3
        = socScanCost pni pm W_sc L + (socJoinCutCost pni W_rd +
            pfk.boundSize (1000 * (W_rd + q + 1) ^ 6) +
            pni.boundSize (1000 * (W_rd + q + 1) ^ 6) +
            1000 * (W_rd + q + 1) ^ 6 * pm.boundSize (1000 * (W_rd + q + 1) ^ 6) +
            10 ^ 9 * (1000 * (W_rd + q + 1) ^ 6) ^ 3) := by omega
      _ ≤ (L + 1) * (2 * (Ym * Q) + 2 * 10 ^ 8 * Ym ^ 3) +
            (L + 1) * (4 * (Ym * Q) + 11 * 10 ^ 8 * Ym ^ 3) := Nat.add_le_add hScan hrest
      _ = (L + 1) * (6 * (Ym * Q) + 13 * 10 ^ 8 * Ym ^ 3) := by ring
      _ ≤ (L + 1) * (10 * (Ym * Q) + 2 * 10 ^ 9 * Ym ^ 3) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_right _ (by decide))
            (Nat.mul_le_mul_right _ (by decide)))
  -- 5. `socPreCost pni pm pfk T L q`
  unfold socPreCost
  rw [← hW_rd]
  have hT2_X2 : (T + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hTX 2
  have hT9_Ym3 : 10 ^ 10 * (T + 1) ^ 9 ≤ (L + 1) * (10 ^ 9 * (X ^ 2 * Ym ^ 3)) := by
    have h1 : (T + 1) ^ 9 ≤ X ^ 650 :=
      (Nat.pow_le_pow_left hTX 9).trans (hXX 9 650 (by decide))
    have h2 : 10 ^ 10 ≤ 10 ^ 9 * socY0 ^ 3 := by
      calc 10 ^ 10 = 10 ^ 9 * 10 := by decide
        _ ≤ 10 ^ 9 * 1000 ^ 3 := Nat.mul_le_mul_left _ (by decide)
        _ ≤ 10 ^ 9 * socY0 ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hY0_pos 3)
    have h3 : 10 ^ 10 * (T + 1) ^ 9 ≤ 10 ^ 9 * (X ^ 2 * Ym ^ 3) := by
      calc 10 ^ 10 * (T + 1) ^ 9 ≤ (10 ^ 9 * socY0 ^ 3) * X ^ 650 := Nat.mul_le_mul h2 h1
        _ = 10 ^ 9 * (X ^ 2 * (socY0 ^ 3 * X ^ 648)) := by ring
        _ = 10 ^ 9 * (X ^ 2 * Ym ^ 3) := by rw [← hYm3]
    calc 10 ^ 10 * (T + 1) ^ 9 ≤ 1 * (10 ^ 9 * (X ^ 2 * Ym ^ 3)) := by omega
      _ ≤ (L + 1) * (10 ^ 9 * (X ^ 2 * Ym ^ 3)) := Nat.mul_le_mul_right _ hL1
  have h3NB : 3 * pni.boundSize (10 ^ 4 * (T + 1) ^ 6) ≤ (L + 1) * (3 * (X ^ 2 * (Ym * Q))) := by
    have h1 : Q ≤ X ^ 2 * (Ym * Q) :=
      hQ_YmQ.trans (Nat.le_mul_of_pos_left _ (hX1 2))
    calc 3 * pni.boundSize (10 ^ 4 * (T + 1) ^ 6) ≤ 1 * (3 * (X ^ 2 * (Ym * Q))) := by omega
      _ ≤ (L + 1) * (3 * (X ^ 2 * (Ym * Q))) := Nat.mul_le_mul_right _ hL1
  have hRd_mul : (T + 1) ^ 2 * socRoundCost pni pm pfk W_rd L q ≤
      (L + 1) * (10 * (X ^ 2 * (Ym * Q)) + 2 * 10 ^ 9 * (X ^ 2 * Ym ^ 3)) := by
    calc (T + 1) ^ 2 * socRoundCost pni pm pfk W_rd L q
        ≤ X ^ 2 * ((L + 1) * (10 * (Ym * Q) + 2 * 10 ^ 9 * Ym ^ 3)) :=
          Nat.mul_le_mul hT2_X2 hRound
      _ = (L + 1) * (10 * (X ^ 2 * (Ym * Q)) + 2 * 10 ^ 9 * (X ^ 2 * Ym ^ 3)) := by ring
  have htot : 3 * pni.boundSize (10 ^ 4 * (T + 1) ^ 6) +
      (T + 1) ^ 2 * socRoundCost pni pm pfk W_rd L q + 10 ^ 10 * (T + 1) ^ 9 ≤
      (L + 1) * (20 * (X ^ 2 * (Ym * Q)) + 3 * 10 ^ 9 * (X ^ 2 * Ym ^ 3)) := by
    calc _ ≤ (L + 1) * (3 * (X ^ 2 * (Ym * Q))) +
            (L + 1) * (10 * (X ^ 2 * (Ym * Q)) + 2 * 10 ^ 9 * (X ^ 2 * Ym ^ 3)) +
            (L + 1) * (10 ^ 9 * (X ^ 2 * Ym ^ 3)) :=
          Nat.add_le_add (Nat.add_le_add h3NB hRd_mul) hT9_Ym3
      _ = (L + 1) * (13 * (X ^ 2 * (Ym * Q)) + 3 * 10 ^ 9 * (X ^ 2 * Ym ^ 3)) := by ring
      _ ≤ (L + 1) * (20 * (X ^ 2 * (Ym * Q)) + 3 * 10 ^ 9 * (X ^ 2 * Ym ^ 3)) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_right _ (by norm_num)) le_rfl)
  refine htot.trans ?_
  rw [hD, hK]
  have hXYmQ : X ^ 2 * (Ym * Q) ≤ socY0 * Kp * X ^ (650 + 216 * Ks) := by
    rw [hYm, hQ]
    calc X ^ 2 * (socY0 * X ^ 216 * (Kp * X ^ (216 * Ks)))
        = socY0 * Kp * (X ^ 2 * X ^ 216 * X ^ (216 * Ks)) := by ring
      _ = socY0 * Kp * X ^ (218 + 216 * Ks) := by rw [← pow_add, ← pow_add]
      _ ≤ socY0 * Kp * X ^ (650 + 216 * Ks) :=
          Nat.mul_le_mul_left _ (hXX _ _ (by omega))
  have hXYm3 : X ^ 2 * Ym ^ 3 ≤ socY0 ^ 3 * X ^ (650 + 216 * Ks) := by
    rw [hYm3]
    calc X ^ 2 * (socY0 ^ 3 * X ^ 648) = socY0 ^ 3 * (X ^ 2 * X ^ 648) := by ring
      _ = socY0 ^ 3 * X ^ 650 := by rw [← pow_add]
      _ ≤ socY0 ^ 3 * X ^ (650 + 216 * Ks) :=
          Nat.mul_le_mul_left _ (hXX _ _ (by omega))
  calc (L + 1) * (20 * (X ^ 2 * (Ym * Q)) + 3 * 10 ^ 9 * (X ^ 2 * Ym ^ 3))
      ≤ (L + 1) * (20 * (socY0 * Kp * X ^ (650 + 216 * Ks)) +
          3 * 10 ^ 9 * (socY0 ^ 3 * X ^ (650 + 216 * Ks))) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ hXYmQ)
          (Nat.mul_le_mul_left _ hXYm3))
    _ = (20 * socY0 * Kp + 3 * 10 ^ 9 * socY0 ^ 3) * ((L + 1) * X ^ (650 + 216 * Ks)) := by ring

/-- The constant in front of `(N + 2) ^ (8 * (socPreD + 1))` in the `expLogSq` bound of `socPreCost`. -/
def socPreCbig (pni pm pfk : Prim) : ℕ :=
  socPreK pni pm pfk * (8 * 10 ^ 6) ^ (socPreD pni pm pfk + 1)

/-- **The exponent constant of `socPreCost` in `expLogSq`** when `(q : ℝ) ≤ expLogSq c N`. -/
noncomputable def socPreA (pni pm pfk : Prim) (c : ℝ) : ℝ :=
  3 * (Real.log (socPreCbig pni pm pfk) + ((8 * (socPreD pni pm pfk + 1) : ℕ) : ℝ)) +
    (socPreD pni pm pfk : ℝ) * c

/-- **`socPreCost` lies in `expLogSq`**: when `(q : ℝ) ≤ expLogSq c N` (`0 ≤ c`), `L ≤ T`, and
`T + 1 ≤ tmVB N`, `(socPreCost pni pm pfk T L q : ℝ) ≤ expLogSq (socPreA pni pm pfk c) N`. -/
theorem socPre_cost_le_expLogSq (pni pm pfk : Prim) {c : ℝ} (hc : 0 ≤ c)
    {N T L q : ℕ} (hL : L ≤ T) (hq : (q : ℝ) ≤ expLogSq c N) (hTN : T + 1 ≤ tmVB N) :
    (socPreCost pni pm pfk T L q : ℝ) ≤ expLogSq (socPreA pni pm pfk c) N := by
  set D := socPreD pni pm pfk
  set K := socPreK pni pm pfk
  set V := tmVB N with hV
  have hVr : (((2 * V) ^ (D + 1) : ℕ) : ℝ) =
      (8 * 10 ^ 6 : ℝ) ^ (D + 1) * ((N : ℝ) + 2) ^ (8 * (D + 1)) := by
    rw [hV]; unfold tmVB; push_cast
    have e1 : (2 : ℝ) * (4000000 * ((N : ℝ) + 2) ^ 8) = (8 * 10 ^ 6 : ℝ) * ((N : ℝ) + 2) ^ 8 := by ring
    rw [e1, mul_pow, ← pow_mul]
  have hV_pos : 1 ≤ V := by
    rw [hV]; unfold tmVB
    have : 1 ≤ (N + 2) ^ 8 := Nat.one_le_pow _ _ (by omega)
    omega
  clear_value V
  have hP := socPreCost_le pni pm pfk T L q
  have hLV : L + 1 ≤ 2 * V := by omega
  have hE1 : (1 : ℝ) ≤ expLogSq c N := tm_one_le_expLogSq hc N
  have hV1 : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV_pos
  have hTq : ((T + q + 1 : ℕ) : ℝ) ≤ (2 * V : ℝ) * expLogSq c N := by
    have hT_r : ((T + 1 : ℕ) : ℝ) ≤ (V : ℝ) := by exact_mod_cast hTN
    have h1 : ((T + q + 1 : ℕ) : ℝ) = ((T + 1 : ℕ) : ℝ) + (q : ℝ) := by push_cast; ring
    have h2 : ((T + 1 : ℕ) : ℝ) ≤ (V : ℝ) * expLogSq c N := by
      calc ((T + 1 : ℕ) : ℝ) ≤ (V : ℝ) * 1 := by linarith
        _ ≤ (V : ℝ) * expLogSq c N := mul_le_mul_of_nonneg_left hE1 (by positivity)
    have h3 : (q : ℝ) ≤ (V : ℝ) * expLogSq c N := by
      calc (q : ℝ) ≤ 1 * expLogSq c N := by linarith
        _ ≤ (V : ℝ) * expLogSq c N := mul_le_mul_of_nonneg_right hV1 (expLogSq_nonneg _ _)
    linarith
  have hTqD : (((T + q + 1) ^ D : ℕ) : ℝ) ≤
      (2 * V : ℝ) ^ D * expLogSq ((D : ℝ) * c) N := by
    rw [Nat.cast_pow]
    calc ((T + q + 1 : ℕ) : ℝ) ^ D ≤ ((2 * V : ℝ) * expLogSq c N) ^ D :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hTq D
      _ = (2 * V : ℝ) ^ D * expLogSq ((D : ℝ) * c) N := by
          rw [mul_pow, outb_expLogSq_pow]
  have hLV_r : ((L + 1 : ℕ) : ℝ) ≤ (2 * V : ℝ) := by exact_mod_cast hLV
  have hprod : ((L + 1 : ℕ) : ℝ) * (((T + q + 1) ^ D : ℕ) : ℝ) ≤
      (((2 * V) ^ (D + 1) : ℕ) : ℝ) * expLogSq ((D : ℝ) * c) N := by
    calc ((L + 1 : ℕ) : ℝ) * (((T + q + 1) ^ D : ℕ) : ℝ)
        ≤ (2 * V : ℝ) * ((2 * V : ℝ) ^ D * expLogSq ((D : ℝ) * c) N) :=
          mul_le_mul hLV_r hTqD (Nat.cast_nonneg _) (by positivity)
      _ = ((2 * V : ℝ) * (2 * V : ℝ) ^ D) * expLogSq ((D : ℝ) * c) N := by ring
      _ = (((2 * V) ^ (D + 1) : ℕ) : ℝ) * expLogSq ((D : ℝ) * c) N := by
          rw [← pow_succ']; push_cast; rfl
  have hCb1 : (1 : ℝ) ≤ (socPreCbig pni pm pfk : ℝ) := by
    have hpos : 0 < socPreCbig pni pm pfk := by
      unfold socPreCbig socPreK
      have := le_socY0_1000
      have : 0 < 20 * socY0 * socPreKp pni pm pfk + 3 * 10 ^ 9 * socY0 ^ 3 := by
        have : 0 < socY0 ^ 3 := Nat.pow_pos (by omega)
        omega
      exact Nat.mul_pos this (pow_pos (by norm_num) _)
    exact_mod_cast hpos
  have hpe := pow_le_expLogSq hCb1 (8 * (D + 1)) N
  have hcast : (socPreCost pni pm pfk T L q : ℝ) ≤
      (K : ℝ) * (((L + 1 : ℕ) : ℝ) * (((T + q + 1) ^ D : ℕ) : ℝ)) := by
    have := (Nat.cast_le (α := ℝ)).2 hP
    push_cast at this ⊢
    exact this
  have hCb : (socPreCbig pni pm pfk : ℝ) = (K : ℝ) * (8 * 10 ^ 6 : ℝ) ^ (D + 1) := by
    unfold socPreCbig; push_cast; ring
  have heA : socPreA pni pm pfk c =
      3 * (Real.log (socPreCbig pni pm pfk) + ((8 * (D + 1) : ℕ) : ℝ)) + (D : ℝ) * c := rfl
  clear_value D K
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  refine hcast.trans ?_
  calc (K : ℝ) * (((L + 1 : ℕ) : ℝ) * (((T + q + 1) ^ D : ℕ) : ℝ))
      ≤ (K : ℝ) * ((((2 * V) ^ (D + 1) : ℕ) : ℝ) * expLogSq ((D : ℝ) * c) N) :=
        mul_le_mul_of_nonneg_left hprod hK0
    _ = ((socPreCbig pni pm pfk : ℝ) * ((N : ℝ) + 2) ^ (8 * (D + 1))) *
          expLogSq ((D : ℝ) * c) N := by
        rw [hVr, hCb]; ring
    _ ≤ expLogSq (3 * (Real.log (socPreCbig pni pm pfk) + ((8 * (D + 1) : ℕ) : ℝ))) N *
          expLogSq ((D : ℝ) * c) N :=
        mul_le_mul_of_nonneg_right hpe (expLogSq_nonneg _ _)
    _ = expLogSq (socPreA pni pm pfk c) N := by rw [tm_expLogSq_mul, heA]

end GI.Impl
