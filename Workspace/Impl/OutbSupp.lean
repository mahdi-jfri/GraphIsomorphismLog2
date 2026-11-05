module

public import Workspace.Impl.OutbSuppDesc
public import Workspace.Impl.TermSplitCost

@[expose] public section

/-!
# Brute-force solvable-quotient supplement modulo `R`

Given permutation groups `R ≤ E_H ≤ K ≤ Sym(n)` with `R ⊴ K`, `E_H ⊴ K`, and `K / E_H` solvable,
together with a list `reps` of coset representatives of `R` in `E_H`:

1. `outbSuppEntry` on `[encGroup σK, encGroup σE, encGroup σR, .list (reps.map encPerm)]`:
   - cuts the generator lists of `K`, `E_H`, and `R` to at most `n²` generators (`ks`, `es`, `rs`)
     via three calls to `normalizedIntersectionPrim` (`jni`),
   - forms `encGroup es` and `encGroup rs` via `mkGroupFuns` (`mg`),
   - runs `n² + 1` steps of `outbDescBody` (`iterFuns` at `it`) starting from `[.nat 0, outbSv ks]`,
   - returns the final generator list `outbSv ss`.
2. `outbSuppFuns` packages all 61 functions of the brute-force supplement module at base `b`,
   using only the four proved primitives `NormalizedIntersection` (`jni`), `NormalClosure` (`jnc`),
   `GroupOrder` (`jord`), and `Membership` (`jm`), and `outbSuppAt_of` establishes `OutbSuppAt`.
3. `outbSupp_spec` proves that `outbSuppEntry` outputs `u` with `GensOf R' u`, `R ≤ R' ≤ K`,
   `R' ⊔ E_H = K`, and `Group.IsSolvable (R' ⧸ R.subgroupOf R')` (`outb_solvable_quotient`), at cost
   at most `outbSuppCost`.
4. `outbSupp_radical_free_order` combines `outbSupp_spec` with
   `GI.RadicalFreeOrder.radical_free_order_of_quotient` (and `GI.schreier`) to conclude that when
   `radicalPreimage K E_H ≤ R`, the quotient order `|R' / R|` is at most `n ^ (13 log₂ n)`.
5. `outbSuppCost_le` proves the polynomial cost bound in `m = reps.length` and
   `T = (Val.list [encGroup σK, encGroup σE, encGroup σR]).wt`, and `outbSupp_cost_le_expLogSq`
   proves that when `(m : ℝ) ≤ expLogSq c N` and `T + 1 ≤ tmVB N`, the cost is bounded by
   `expLogSq (outbSuppA ... c) N`.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

set_option maxRecDepth 100000

/-! ### Entry point and module layout -/

/-- **The brute-force supplement program modulo `R`** on
`[encGroup σK, encGroup σE, encGroup σR, .list (reps.map encPerm)]`:
1. `.var 1 = outbSv ks` (`ks.length ≤ n²`, `gens ks = gens σK`) via `jni` on `[arg 0, arg 0]`
2. `.var 2 = outbSv es` (`es.length ≤ n²`, `gens es = gens σE`) via `jni` on `[arg 1, arg 1]`
3. `.var 3 = outbSv rs` (`rs.length ≤ n²`, `gens rs = gens σR`) via `jni` on `[arg 2, arg 2]`
4. `.var 4 = encGroup es` via `mg` on `[n, .var 2]`
5. `.var 5 = encGroup rs` via `mg` on `[n, .var 3]`
6. `.var 6 = [.nat 1, outbSv ss]` via `it` (`n² + 1` steps of `outbDescBody`) starting from
   `[.nat 0, .var 1]` with loop context `[.var 4, .var 5, arg 3]`
7. returns `.get (.var 6) (.nat 1)` (`outbSv ss`). -/
def outbSuppEntry (it mg jni : ℕ) : Expr :=
  .letE (.prim jni (mk2 (arg 0) (arg 0)))
  (.letE (.prim jni (mk2 (arg 1) (arg 1)))
  (.letE (.prim jni (mk2 (arg 2) (arg 2)))
  (.letE (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 2)))
  (.letE (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 3)))
  (.letE (.call it (mk3
      (mk3 (.var 4) (.var 5) (arg 3))
      (.arith .add (.arith .mul (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0))) (.nat 1))
      (mk2 (.nat 0) (.var 1))))
    (.get (.var 6) (.nat 1)))))))

/-- Where the brute-force supplement program and its modules sit. -/
structure OutbSuppAt (P : Program)
    (f it g jc mg jni fd_fn it_s gs_s sy_s pp_s it_sy ps_fn fd_sy st_sy le_s jnc jord jm
      mf fx fd_fx st_fx cp iv mc cj le_fx : ℕ)
    (hni : NormalizedIntersection) (hnc : NormalClosure) (hord : GroupOrder)
    (hmem : Membership) : Prop where
  entry : P.funs[f]? = some (outbSuppEntry it mg jni)
  iter : P.HasAt it (iterFuns it g)
  desc : OutbDescAt P g jc mg jni fd_fn it_s gs_s sy_s pp_s it_sy ps_fn fd_sy st_sy le_s jnc jord jm
    mf fx fd_fx st_fx cp iv mc cj le_fx hni hnc hord hmem

/-- **The complete function block of the brute-force supplement module** at base `b`, using only
the primitive indices `jni` (NormalizedIntersection), `jnc` (NormalClosure), `jord` (GroupOrder),
and `jm` (Membership). Total length: 61 functions. -/
def outbSuppFuns (b jni jnc jord jm : ℕ) : List Expr :=
  [outbSuppEntry (b + 12) (b + 18) jni,
    outbDescBody (b + 18) jni (b + 3) (b + 15) (b + 2),
    outbJoinCutF (b + 18) jni,
    outbFindBody (b + 25) jord,
    outbSearchBody (b + 5) (b + 18) (b + 28) jnc jord,
    outbSylBody (b + 6) (b + 33) jord,
    outbPPartF (b + 6),
    outbSylPassE (b + 36),
    outbSylStepE jm jord,
    outbFixBody (b + 39),
    outbFixStepE (b + 42) (b + 46) (b + 58) (b + 28) jm,
    outbConjF (b + 42)] ++
  iterFuns (b + 12) (b + 1) ++
  mapFuns (b + 15) (b + 9) ++
  mkGroupFuns (b + 18) ++
  iterFuns (b + 25) (b + 4) ++
  leFuns (b + 28) jm ++
  iterFuns (b + 33) (b + 7) ++
  foldlFuns (b + 36) (b + 8) ++
  foldlFuns (b + 39) (b + 10) ++
  composeFuns (b + 42) ++
  invFuns (b + 46) ++
  mapFuns (b + 58) (b + 11)

theorem length_outbSuppFuns (b jni jnc jord jm : ℕ) :
    (outbSuppFuns b jni jnc jord jm).length = 61 := rfl

set_option maxHeartbeats 800000 in
/-- **The layout `OutbSuppAt`** from `P.HasAt b (outbSuppFuns b jni jnc jord jm)`. -/
theorem outbSuppAt_of {P : Program} {b jni jnc jord jm : ℕ}
    {hni : NormalizedIntersection} {hnc : NormalClosure} {hord : GroupOrder}
    {hmem : Membership} (h : P.HasAt b (outbSuppFuns b jni jnc jord jm))
    (pni : P.prims[jni]? = some (normalizedIntersectionPrim hni))
    (pnc : P.prims[jnc]? = some (normalClosurePrim hnc))
    (pord : P.prims[jord]? = some (groupOrderPrim hord))
    (pm : P.prims[jm]? = some (membershipPrim hmem)) :
    OutbSuppAt P b (b + 12) (b + 1) (b + 2) (b + 18) jni (b + 3) (b + 25) (b + 4) (b + 5)
      (b + 6) (b + 33) (b + 7) (b + 36) (b + 8) (b + 28) jnc jord jm (b + 15) (b + 9)
      (b + 39) (b + 10) (b + 42) (b + 46) (b + 58) (b + 11) (b + 28)
      hni hnc hord hmem where
  entry := by
    rw [← Nat.add_zero b]
    exact (h.block (gs := [outbSuppEntry (b + 12) (b + 18) jni]) 0 rfl).single
  iter := h.block 12 rfl
  desc :=
    { step := (h.block (gs := [outbDescBody (b + 18) jni (b + 3) (b + 15) (b + 2)]) 1 rfl).single
      joinCut := (h.block (gs := [outbJoinCutF (b + 18) jni]) 2 rfl).single
      ni := pni
      find :=
        { entry := (h.block (gs := [outbFindBody (b + 25) jord]) 3 rfl).single
          iter := h.block 25 rfl
          step :=
            { step := (h.block (gs := [outbSearchBody (b + 5) (b + 18) (b + 28) jnc jord]) 4
                rfl).single
              syl :=
                { entry := (h.block (gs := [outbSylBody (b + 6) (b + 33) jord]) 5 rfl).single
                  ppart := (h.block (gs := [outbPPartF (b + 6)]) 6 rfl).single
                  iter := h.block 33 rfl
                  pass := (h.block (gs := [outbSylPassE (b + 36)]) 7 rfl).single
                  fold := h.block 36 rfl
                  step := (h.block (gs := [outbSylStepE jm jord]) 8 rfl).single
                  mem := pm
                  ord := pord }
              mg := h.block 18 rfl
              le := h.block 28 rfl
              nc := pnc
              ord := pord
              mem := pm } }
      map := h.block 15 rfl
      fix :=
        { fix := (h.block (gs := [outbFixBody (b + 39)]) 9 rfl).single
          fold := h.block 39 rfl
          step := (h.block (gs := [outbFixStepE (b + 42) (b + 46) (b + 58) (b + 28) jm]) 10
            rfl).single
          comp := h.block 42 rfl
          inv := h.block 46 rfl
          map := h.block 58 rfl
          conj := (h.block (gs := [outbConjF (b + 42)]) 11 rfl).single
          le := h.block 28 rfl
          mem := pm } }

/-! ### Cost and specification of `outbSuppEntry` -/

/-- Cost bound of `outbSuppEntry` for `reps` of length `m` and group-encoding weight `T`. -/
def outbSuppCost (pni pnc pord pm : Prim) (n m T : ℕ) : ℕ :=
  3 * pni.boundSize (10 ^ 4 * (T + 1) ^ 6) +
    (n ^ 2 + 1) * outbDescCost pni pnc pord pm n m +
    10 ^ 9 * (m + 1) ^ 2 * (T + 1) ^ 9

set_option maxHeartbeats 800000 in
/-- **Specification of `outbSuppEntry`**: given `R ≤ E_H ≤ K ≤ Sym(n)` with `R ⊴ K`, `E_H ⊴ K`,
`K / E_H` solvable, and coset representatives `reps` of `R` in `E_H`, computes generators of a
subgroup `R'` with `R ≤ R' ≤ K`, `R' ⊔ E_H = K`, and `R' / R` solvable. -/
theorem outbSupp_spec {hni : NormalizedIntersection} {hnc : NormalClosure}
    {hord : GroupOrder} {hmem : Membership} {P : Program}
    {f it g jc mg jni fd_fn it_s gs_s sy_s pp_s it_sy ps_fn fd_sy st_sy le_s jnc jord jm
      mf fx fd_fx st_fx cp iv mc cj le_fx : ℕ}
    (hP : OutbSuppAt P f it g jc mg jni fd_fn it_s gs_s sy_s pp_s it_sy ps_fn fd_sy st_sy le_s
      jnc jord jm mf fx fd_fx st_fx cp iv mc cj le_fx hni hnc hord hmem)
    (σK σE σR reps : List (Perm (Fin n)))
    (hRE : gens σR ≤ gens σE) (hEK : gens σE ≤ gens σK)
    [hEK_norm : ((gens σE).subgroupOf (gens σK)).Normal]
    [hRK_norm : ((gens σR).subgroupOf (gens σK)).Normal]
    (hsolv : Group.IsSolvable ((gens σK) ⧸ (gens σE).subgroupOf (gens σK)))
    (hcov : ∀ x ∈ gens σE, TmRpCov (gens σR) reps x) :
    FunAll P f (.list [encGroup σK, encGroup σE, encGroup σR, .list (reps.map encPerm)])
      (fun u cost => ∃ R' : Subgroup (Perm (Fin n)),
        GensOf R' u ∧ gens σR ≤ R' ∧ R' ≤ gens σK ∧ R' ⊔ gens σE = gens σK ∧
        (∃ (_ : ((gens σR).subgroupOf R').Normal),
          Group.IsSolvable (R' ⧸ (gens σR).subgroupOf R')) ∧
        cost ≤ outbSuppCost (normalizedIntersectionPrim hni) (normalClosurePrim hnc)
          (groupOrderPrim hord) (membershipPrim hmem) n reps.length
          (Val.list [encGroup σK, encGroup σE, encGroup σR]).wt) := by
  set xs := reps.map encPerm with hxs
  set c_grp := Val.list [encGroup σK, encGroup σE, encGroup σR] with hc_grp
  set T := c_grp.wt with hT
  set in_v := Val.list [encGroup σK, encGroup σE, encGroup σR, .list xs] with hin_v
  set ZT6 := (reps.length + 1) ^ 2 * (T + 1) ^ 6 with hZT6
  set ZT9 := (reps.length + 1) ^ 2 * (T + 1) ^ 9 with hZT9
  have hKw : (encGroup σK).wt < T := wt_le_wt_list (vs := [encGroup σK, encGroup σE, encGroup σR]) (by simp)
  have hEw_T : (encGroup σE).wt < T := wt_le_wt_list (vs := [encGroup σK, encGroup σE, encGroup σR]) (by simp)
  have hRw_T : (encGroup σR).wt < T := wt_le_wt_list (vs := [encGroup σK, encGroup σE, encGroup σR]) (by simp)
  have hnT : n + 1 ≤ T := by
    have := S_le_wt_encGroup σK
    have : n + 1 ≤ (σK.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hnT2 : (n + 1) ^ 2 ≤ (T + 1) ^ 2 := Nat.pow_le_pow_left (by omega) _
  have hnT6 : (n + 1) ^ 6 ≤ (T + 1) ^ 6 := Nat.pow_le_pow_left (by omega) _
  have hnT8 : (n + 1) ^ 8 ≤ (T + 1) ^ 8 := Nat.pow_le_pow_left (by omega) _
  have hnT9 : (n + 1) ^ 9 ≤ (T + 1) ^ 9 := Nat.pow_le_pow_left (by omega) _
  have hT16 : T + 1 ≤ (T + 1) ^ 6 := Nat.le_self_pow (by decide) _
  have hT26 : (T + 1) ^ 2 ≤ (T + 1) ^ 6 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hT68 : (T + 1) ^ 6 ≤ (T + 1) ^ 8 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hT69 : (T + 1) ^ 6 ≤ (T + 1) ^ 9 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hT89 : (T + 1) ^ 8 ≤ (T + 1) ^ 9 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hm12 : 1 ≤ (reps.length + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hT1_pos : 1 ≤ (T + 1) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hZT6_ZT9 : ZT6 ≤ ZT9 := Nat.mul_le_mul_left _ hT69
  have hT6_ZT6 : (T + 1) ^ 6 ≤ ZT6 := by
    calc (T + 1) ^ 6 = 1 * (T + 1) ^ 6 := (one_mul _).symm
      _ ≤ ZT6 := Nat.mul_le_mul_right _ hm12
  have hT9_ZT9 : (T + 1) ^ 9 ≤ ZT9 := by
    calc (T + 1) ^ 9 = 1 * (T + 1) ^ 9 := (one_mul _).symm
      _ ≤ ZT9 := Nat.mul_le_mul_right _ hm12
  have hn6_ZT6 : (n + 1) ^ 6 ≤ ZT6 := hnT6.trans hT6_ZT6
  have hn9_ZT9 : (n + 1) ^ 9 ≤ ZT9 := hnT9.trans hT9_ZT9
  have hn_ZT6 : n ≤ ZT6 :=
    (Nat.le_succ n).trans ((hnT.trans (Nat.le_succ T)).trans (hT16.trans hT6_ZT6))
  have hrepw : (Val.list xs).wt ≤ 13 * ZT6 := by
    calc (Val.list xs).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 := outb_wt_reps_le reps
      _ ≤ 13 * (reps.length + 1) ^ 2 * (T + 1) ^ 6 :=
          Nat.mul_le_mul_left _ (hnT2.trans hT26)
      _ = 13 * ZT6 := by rw [hZT6, Nat.mul_assoc]
  have hinw0 : in_v.wt ≤ 2 * ((encGroup σK).wt + (encGroup σE).wt + (encGroup σR).wt + (Val.list xs).wt) + 8 :=
    wt_list4_le (encGroup σK) (encGroup σE) (encGroup σR) (.list xs)
  have hinw : in_v.wt ≤ 50 * ZT6 := by
    clear * - hinw0 hKw hEw_T hRw_T hrepw hT16 hT6_ZT6 hT1_pos
    omega
  -- step 1: cut `σK` to `ks` (`ks.length ≤ n²`)
  have dK0 := Det.arg' (P := P) (vs := [encGroup σK, encGroup σE, encGroup σR, .list xs])
    (rest := []) (j := 0) (v := encGroup σK) rfl
  rw [← hin_v] at dK0
  have hKK_w := wt_list2_le (encGroup σK) (encGroup σK)
  have hbK := (normalizedIntersectionPrim hni).bound_le
    (show (Val.list [encGroup σK, encGroup σK]).size ≤ 10 ^ 4 * (T + 1) ^ 6 from
      (Val.size_le_wt _).trans (by
        clear * - hKK_w hKw hT16 hT1_pos
        omega))
  refine FunAll.intro hP.entry (EvalAll.letE (normalizedIntersection_call hni hP.desc.ni
    (Det.mk2 dK0 dK0) ⟨σK, rfl, rfl⟩ ⟨σK, rfl, rfl⟩ fun x hx y hy =>
      (gens σK).mul_mem ((gens σK).mul_mem hx hy) ((gens σK).inv_mem hx)) fun v1 c1 h1 => ?_)
  clear dK0
  obtain ⟨⟨ks, rfl, hkl, hks⟩, hc1⟩ := h1
  rw [inf_idem] at hks
  -- step 2: cut `σE` to `es` (`es.length ≤ n²`)
  have dE1 := Det.arg' (P := P) (vs := [encGroup σK, encGroup σE, encGroup σR, .list xs])
    (rest := [outbSv ks]) (j := 1) (v := encGroup σE) rfl
  rw [← hin_v] at dE1
  have hEE_w := wt_list2_le (encGroup σE) (encGroup σE)
  have hbE := (normalizedIntersectionPrim hni).bound_le
    (show (Val.list [encGroup σE, encGroup σE]).size ≤ 10 ^ 4 * (T + 1) ^ 6 from
      (Val.size_le_wt _).trans (by
        clear * - hEE_w hEw_T hT16 hT1_pos
        omega))
  refine EvalAll.letE (normalizedIntersection_call hni hP.desc.ni
    (Det.mk2 dE1 dE1) ⟨σE, rfl, rfl⟩ ⟨σE, rfl, rfl⟩ fun x hx y hy =>
      (gens σE).mul_mem ((gens σE).mul_mem hx hy) ((gens σE).inv_mem hx)) fun v2 c2 h2 => ?_
  clear dE1
  obtain ⟨⟨es, rfl, hel, hes⟩, hc2⟩ := h2
  rw [inf_idem] at hes
  -- step 3: cut `σR` to `rs` (`rs.length ≤ n²`)
  have dR2 := Det.arg' (P := P) (vs := [encGroup σK, encGroup σE, encGroup σR, .list xs])
    (rest := [outbSv ks, outbSv es]) (j := 2) (v := encGroup σR) rfl
  rw [← hin_v] at dR2
  have hRR_w := wt_list2_le (encGroup σR) (encGroup σR)
  have hbR := (normalizedIntersectionPrim hni).bound_le
    (show (Val.list [encGroup σR, encGroup σR]).size ≤ 10 ^ 4 * (T + 1) ^ 6 from
      (Val.size_le_wt _).trans (by
        clear * - hRR_w hRw_T hT16 hT1_pos
        omega))
  refine EvalAll.letE (normalizedIntersection_call hni hP.desc.ni
    (Det.mk2 dR2 dR2) ⟨σR, rfl, rfl⟩ ⟨σR, rfl, rfl⟩ fun x hx y hy =>
      (gens σR).mul_mem ((gens σR).mul_mem hx hy) ((gens σR).inv_mem hx)) fun v3 c3 h3 => ?_
  clear dR2
  obtain ⟨⟨rs, rfl, hrl, hrs⟩, hc3⟩ := h3
  rw [inf_idem] at hrs
  -- step 4: `encGroup es` via `mg`
  set env3 := [in_v, outbSv ks, outbSv es, outbSv rs]
  have dn3 := Det.get' (Det.arg' (P := P) (vs := [encGroup σK, encGroup σE, encGroup σR, .list xs])
    (rest := [outbSv ks, outbSv es, outbSv rs]) (j := 0) (v := encGroup σK) rfl)
    (Det.nat 0) (v := .nat n) rfl
  rw [← hin_v] at dn3
  have des3 := Det.var' (P := P) (env := env3) (i := 2) (v := outbSv es) rfl
  obtain ⟨es', hel', hes', dE_mk, hEw⟩ := outb_mk_det hP.desc.find.step.mg dn3 des3
    (⟨es, rfl, hel, rfl⟩ : GensVal n (outbSv es) (gens es))
  rw [hes] at hes'
  clear dn3 des3
  refine EvalAll.letE dE_mk fun v4 c4 h4 => ?_
  obtain ⟨rfl, hc4⟩ := h4
  clear dE_mk
  -- step 5: `encGroup rs` via `mg`
  set env4 := [in_v, outbSv ks, outbSv es, outbSv rs, encGroup es']
  have dn4 := Det.get' (Det.arg' (P := P) (vs := [encGroup σK, encGroup σE, encGroup σR, .list xs])
    (rest := [outbSv ks, outbSv es, outbSv rs, encGroup es']) (j := 0) (v := encGroup σK) rfl)
    (Det.nat 0) (v := .nat n) rfl
  rw [← hin_v] at dn4
  have drs4 := Det.var' (P := P) (env := env4) (i := 3) (v := outbSv rs) rfl
  obtain ⟨rs', hrl', hrs', dR_mk, hRw⟩ := outb_mk_det hP.desc.find.step.mg dn4 drs4
    (⟨rs, rfl, hrl, rfl⟩ : GensVal n (outbSv rs) (gens rs))
  rw [hrs] at hrs'
  clear dn4 drs4
  refine EvalAll.letE dR_mk fun v5 c5 h5 => ?_
  obtain ⟨rfl, hc5⟩ := h5
  clear dR_mk
  -- step 6: run `iter_spec` for `k = n² + 1` steps of `outbDesc_step`
  have hRE' : gens rs' ≤ gens es' := by rw [hrs', hes']; exact hRE
  have hEK' : gens es' ≤ gens σK := by rw [hes']; exact hEK
  have hRK' : gens rs' ≤ gens σK := hRE'.trans hEK'
  have : ((gens es').subgroupOf (gens σK)).Normal := by rwa [hes']
  have : ((gens rs').subgroupOf (gens σK)).Normal := by rwa [hrs']
  have hcov' : ∀ x ∈ gens es', TmRpCov (gens rs') reps x := by
    rw [hes', hrs']; exact hcov
  have h0 : OutbDescInv (gens σK) (gens es') (gens rs') 0 (.list [.nat 0, outbSv ks]) :=
    ⟨ks, hkl, by rw [hks]; exact hRK', hks.le, by rw [hks]; exact sup_eq_left.mpr hEK',
      Or.inr ⟨rfl, by rw [pow_zero, one_mul]; exact Subgroup.card_le_of_le inf_le_right⟩⟩
  set k := n ^ 2 + 1 with hk
  set B := outbDescCost (normalizedIntersectionPrim hni) (normalClosurePrim hnc)
    (groupOrderPrim hord) (membershipPrim hmem) n reps.length with hB
  set c_loop := Val.list [encGroup es', encGroup rs', .list xs] with hc_loop
  have hit := iter_spec hP.iter (c := c_loop) (k := k) (M := 40 * (n + 1) ^ 6) (B := fun _ => B) h0
    (fun i acc _ h => outb_desc_wt h)
    (fun i acc hi h => outbDesc_step hP.desc hRE' hEK' hel' hrl' hcov' (by omega) h)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hit
  set env5 := [in_v, outbSv ks, outbSv es, outbSv rs, encGroup es', encGroup rs']
  have dE5 := Det.var' (P := P) (env := env5) (i := 4) (v := encGroup es') rfl
  have dR5 := Det.var' (P := P) (env := env5) (i := 5) (v := encGroup rs') rfl
  have drep5 := Det.arg' (P := P) (vs := [encGroup σK, encGroup σE, encGroup σR, .list xs])
    (rest := [outbSv ks, outbSv es, outbSv rs, encGroup es', encGroup rs'])
    (j := 3) (v := .list xs) rfl
  rw [← hin_v] at drep5
  have dcloop := Det.mk3 dE5 dR5 drep5
  rw [← hc_loop] at dcloop
  have dn5 := Det.get' (Det.arg' (P := P) (vs := [encGroup σK, encGroup σE, encGroup σR, .list xs])
    (rest := [outbSv ks, outbSv es, outbSv rs, encGroup es', encGroup rs'])
    (j := 0) (v := encGroup σK) rfl) (Det.nat 0) (v := .nat n) rfl
  rw [← hin_v] at dn5
  have dk := Det.arith' (op := .add) (Det.arith' (op := .mul) dn5 dn5 rfl) (Det.nat 1) (z := k)
    (by simp [BinOp.eval, hk, sq])
  have dacc0 := Det.mk2 (Det.nat (P := P) (env := env5) 0)
    (Det.var' (P := P) (env := env5) (i := 1) (v := outbSv ks) rfl)
  have darg := Det.mk3 dcloop dk dacc0
  have hkw_K : (outbSv ks).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq hkl
  have hew_E : (outbSv es).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq hel
  have hrw_R : (outbSv rs).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq hrl
  have hnw := wt_nat_le n
  have h0w := wt_nat_le 0
  have h1w := wt_nat_le 1
  have hcloop_w0 : c_loop.wt ≤ 2 * ((encGroup es').wt + (encGroup rs').wt + (Val.list xs).wt) + 7 :=
    wt_list3_le (encGroup es') (encGroup rs') (.list xs)
  have hcloop_w : c_loop.wt ≤ 2000 * ZT6 := by
    clear * - hcloop_w0 hEw hRw hrepw hn6_ZT6 hT1_pos hT6_ZT6
    omega
  refine EvalAll.letE (Ra := fun w cw => OutbDescInv (gens σK) (gens es') (gens rs') k w ∧
      cw ≤ k * B + 10 ^ 8 * ZT9)
    (EvalAll.call_funAll darg fun v ca hv => ?_) fun v6 c6 h6 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine hit.mono fun w cw h => ⟨h.1, ?_⟩
    have hw_wt := outb_desc_wt h.1
    have hcw := h.2
    have h0_wt := outb_desc_wt h0
    have hn2e : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    have hkT2 : k + 1 ≤ 2 * (T + 1) ^ 2 := by
      have h1 : 1 ≤ (T + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
      clear * - hk hn2e hnT2 h1
      omega
    have hk_ZT6 : k ≤ ZT6 := by
      have : k ≤ (n + 1) ^ 2 := by
        clear * - hk hn2e
        omega
      exact (this.trans (hnT2.trans hT26)).trans hT6_ZT6
    have hkw := wt_nat_le k
    have hnn : n * n ≤ ZT6 := by
      have : n * n ≤ (n + 1) ^ 2 := by
        rw [sq]
        exact Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n)
      exact (this.trans (hnT2.trans hT26)).trans hT6_ZT6
    have hw3 := wt_list3_le c_loop (.nat k) (.list [.nat 0, outbSv ks])
    have hw_acc0 := wt_list2_le (.nat 0) (outbSv ks)
    have hwt_iter : (Val.list [c_loop, .nat k, .list [.nat 0, outbSv ks]]).wt + k +
        40 * (n + 1) ^ 6 + 1 ≤ 5000 * ZT6 := by
      clear * - hw3 hw_acc0 hcloop_w hkw h0w hkw_K hk_ZT6 hn6_ZT6 hT1_pos hT6_ZT6
      omega
    have hL : loopModK * (k + 1) *
        ((Val.list [c_loop, .nat k, .list [.nat 0, outbSv ks]]).wt + k +
          40 * (n + 1) ^ 6 + 1) ≤ 10 ^ 7 * ZT9 := by
      have hT23 : (T + 1) ^ 2 ≤ (T + 1) ^ 3 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
      have hkT3 : k + 1 ≤ 2 * (T + 1) ^ 3 := hkT2.trans (Nat.mul_le_mul_left 2 hT23)
      calc _ ≤ loopModK * (2 * (T + 1) ^ 3) * (5000 * ZT6) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hkT3) hwt_iter
        _ = 10 ^ 7 * ((reps.length + 1) ^ 2 * ((T + 1) ^ 3 * (T + 1) ^ 6)) := by
            simp only [loopModK, hZT6]; ring
        _ = 10 ^ 7 * ZT9 := by rw [← pow_add, hZT9]
    have hmul : BinOp.mul.eval n n = n * n := rfl
    clear * - hca hcw hL hw_wt hw3 hw_acc0 hcloop_w0 hcloop_w hinw hkw_K hew_E hrw_R hEw hRw
      hrepw hnw h0w h1w hkw hnn hmul hk_ZT6 hn_ZT6 hn6_ZT6 hZT6_ZT9 hT1_pos hT6_ZT6 hT9_ZT9
    omega
  clear dE5 dR5 drep5 dcloop dn5 dk dacc0 darg hit
  -- step 7: extract the final generator list `outbSv ss`
  obtain ⟨ss, hsl, hRS, hSK, hsup, rfl, hN_M, hnil⟩ := outbDesc_done h6.1
  have hc6 := h6.2
  refine (Det.get' (Det.var' (P := P) (env := env5 ++ [.list [.nat 1, outbSv ss]]) (i := 6) rfl)
    (Det.nat 1) (v := outbSv ss) rfl).post fun cu hcu => ?_
  have hsolv_E' : Group.IsSolvable ((gens σK) ⧸ (gens es').subgroupOf (gens σK)) := by
    let e := QuotientGroup.congr ((gens σE).subgroupOf (gens σK))
      ((gens es').subgroupOf (gens σK)) (MulEquiv.refl (gens σK)) (by ext x; simp [hes'])
    exact Group.isSolvable_of_surjective e.surjective
  have : ((gens rs').subgroupOf (gens ss)).Normal :=
    outb_normal_subgroupOf_of_le (hRE'.trans hEK') hSK
  have hsolv_R0 : Group.IsSolvable ((gens ss) ⧸ (gens rs').subgroupOf (gens ss)) :=
    outb_solvable_quotient hRE' hEK' hRS hSK hsolv_E' hnil
  rw [hrs'] at hRS
  rw [hes'] at hsup
  have hNR' : ((gens σR).subgroupOf (gens ss)).Normal :=
    outb_normal_subgroupOf_of_le (hRE.trans hEK) hSK
  have hsolv_R' : Group.IsSolvable ((gens ss) ⧸ (gens σR).subgroupOf (gens ss)) := by
    let e := QuotientGroup.congr ((gens rs').subgroupOf (gens ss))
      ((gens σR).subgroupOf (gens ss)) (MulEquiv.refl (gens ss)) (by ext x; simp [hrs'])
    exact Group.isSolvable_of_surjective e.surjective
  refine ⟨gens ss, ⟨ss, rfl, hsl, rfl⟩, hRS, hSK, hsup, ⟨hNR', hsolv_R'⟩, ?_⟩
  have hss_w : (outbSv ss).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq hsl
  have h1ss_w := wt_list2_le (.nat 1) (outbSv ss)
  have hnes_w := wt_list2_le (.nat n) (outbSv es)
  have hnrs_w := wt_list2_le (.nat n) (outbSv rs)
  have hmk_ZT9 : 8 * mkGroupK * (n + 1) ^ 9 ≤ 10 ^ 6 * ZT9 := by
    simp only [mkGroupK]
    clear * - hn9_ZT9
    omega
  set NB := (normalizedIntersectionPrim hni).boundSize (10 ^ 4 * (T + 1) ^ 6) with hNB
  have hgoal_eq : outbSuppCost (normalizedIntersectionPrim hni) (normalClosurePrim hnc)
      (groupOrderPrim hord) (membershipPrim hmem) n reps.length T =
      3 * NB + k * B + 10 ^ 9 * ZT9 := by
    simp only [outbSuppCost, hNB, hk, hB, hZT9, Nat.mul_assoc]
  rw [hgoal_eq]
  clear * - hc1 hc2 hc3 hc4 hc5 hc6 hcu hbK hbE hbR hKK_w hEE_w hRR_w hKw hEw_T hRw_T
    hinw hkw_K hew_E hrw_R hEw hRw hss_w h1ss_w hnes_w hnrs_w hnw h0w h1w hmk_ZT9
    hn_ZT6 hn6_ZT6 hn9_ZT9 hZT6_ZT9 hT16 hT69 hT1_pos hT6_ZT6 hT9_ZT9
  omega

/-- **Corollary of `outbSupp_spec` with `radical_free_order_of_quotient`**: when `gens σR = R`,
`gens σE = E_H`, and `gens σK = K*_H` for `N ◁ H` in `Sym(n)` (where `R = radicalPreimage H N`,
`E_H = soclePreimage H R`, `K*_H = radicalPreimage H E_H`), the subgroup `R'` produced by
`outbSuppEntry` satisfies `N ≤ R' ≤ H`, `N ◁ R'`, `R'/N` solvable, and `[H : R'] ≤ b(H/N)²`. -/
theorem outbSupp_radical_free_order
    {hni : NormalizedIntersection} {hnc : NormalClosure}
    {hord : GroupOrder} {hmem : Membership} {P : Program}
    {f it g jc mg jni fd_fn it_s gs_s sy_s pp_s it_sy ps_fn fd_sy st_sy le_s jnc jord jm
      mf fx fd_fx st_fx cp iv mc cj le_fx : ℕ}
    (hP : OutbSuppAt P f it g jc mg jni fd_fn it_s gs_s sy_s pp_s it_sy ps_fn fd_sy st_sy le_s
      jnc jord jm mf fx fd_fx st_fx cp iv mc cj le_fx hni hnc hord hmem)
    {H N : Subgroup (Perm (Fin n))} (hNH : N ≤ H) [(N.subgroupOf H).Normal]
    (σK σE σR reps : List (Perm (Fin n)))
    (hR : gens σR = GI.Multicoset.radicalPreimage H N)
    (hE : gens σE = GI.RadicalFreeOrder.soclePreimage H (GI.Multicoset.radicalPreimage H N))
    (hK : gens σK = GI.Multicoset.radicalPreimage H
      (GI.RadicalFreeOrder.soclePreimage H (GI.Multicoset.radicalPreimage H N)))
    (hcov : ∀ x ∈ gens σE, TmRpCov (gens σR) reps x) :
    FunAll P f (.list [encGroup σK, encGroup σE, encGroup σR, .list (reps.map encPerm)])
      (fun u cost => ∃ R' : Subgroup (Perm (Fin n)),
        GensOf R' u ∧ N ≤ R' ∧ R' ≤ H ∧ (N.subgroupOf R').Normal ∧
        (∃ ℓ, GI.Multicoset.relDerived R' N ℓ ≤ N) ∧
        (∀ [(N.subgroupOf R').Normal], Group.IsSolvable (R' ⧸ N.subgroupOf R')) ∧
        (R'.subgroupOf H).index ≤ GI.Composition.bFac (H ⧸ N.subgroupOf H) ^ 2 ∧
        cost ≤ outbSuppCost (normalizedIntersectionPrim hni) (normalClosurePrim hnc)
          (groupOrderPrim hord) (membershipPrim hmem) n reps.length
          (Val.list [encGroup σK, encGroup σE, encGroup σR]).wt) := by
  have hn : GI.Multicoset.Normalizes H N := GI.Multicoset.normalizes_of_normal hNH
  obtain ⟨hRH, hNR, -⟩ := GI.Multicoset.radicalPreimage_spec hNH hn
  have hRE : gens σR ≤ gens σE := by
    rw [hR, hE]; exact GI.RadicalFreeOrder.le_soclePreimage hRH
  have hEH : gens σE ≤ H := by
    rw [hE]; exact GI.RadicalFreeOrder.soclePreimage_le H _
  have hEK : gens σE ≤ gens σK := by
    rw [hE, hK]; exact GI.RadicalFreeOrder.le_radicalPreimage (by rw [← hE]; exact hEH)
  have hKH : gens σK ≤ H := by
    rw [hK]; exact GI.RadicalFreeOrder.radicalPreimage_le H _
  have hnE : GI.Multicoset.Normalizes H (gens σE) := by
    rw [hE]; exact GI.Multicoset.normalizes_of_normal (by rw [← hE]; exact hEH)
  have hnKE : GI.Multicoset.Normalizes (gens σK) (gens σE) := hnE.mono hKH
  have : ((gens σE).subgroupOf (gens σK)).Normal := GI.Multicoset.normal_of_normalizes hnKE
  have hnR : GI.Multicoset.Normalizes H (gens σR) := by
    rw [hR]; exact GI.Multicoset.normalizes_of_normal hRH
  have hnKR : GI.Multicoset.Normalizes (gens σK) (gens σR) := hnR.mono hKH
  have : ((gens σR).subgroupOf (gens σK)).Normal := GI.Multicoset.normal_of_normalizes hnKR
  have hsolv : Group.IsSolvable ((gens σK) ⧸ (gens σE).subgroupOf (gens σK)) := by
    obtain ⟨-, -, ℓ, hℓ⟩ := GI.Multicoset.radicalPreimage_spec hEH hnE
    have hK' : gens σK = GI.Multicoset.radicalPreimage H (gens σE) := by rw [hK, hE]
    rw [← hK'] at hℓ
    exact GI.Multicoset.isSolvable_quot_of_relDerived hℓ
  refine (outbSupp_spec hP σK σE σR reps hRE hEK hsolv hcov).mono fun u cost h => ?_
  obtain ⟨R', hR'u, hRR', hR'K, hsup, ⟨hNR', hsolv_R'⟩, hcost⟩ := h
  have hRR'' : GI.Multicoset.radicalPreimage H N ≤ R' := hR ▸ hRR'
  have hR'K' : R' ≤ GI.Multicoset.radicalPreimage H
      (GI.RadicalFreeOrder.soclePreimage H (GI.Multicoset.radicalPreimage H N)) := hK ▸ hR'K
  have hsup' : R' ⊔ GI.RadicalFreeOrder.soclePreimage H (GI.Multicoset.radicalPreimage H N) =
      GI.Multicoset.radicalPreimage H
        (GI.RadicalFreeOrder.soclePreimage H (GI.Multicoset.radicalPreimage H N)) := by
    rw [← hK, ← hE]; exact hsup
  have hsolv_R'' : ∀ [((GI.Multicoset.radicalPreimage H N).subgroupOf R').Normal],
      Group.IsSolvable (R' ⧸ (GI.Multicoset.radicalPreimage H N).subgroupOf R') := by
    intro _
    let e := QuotientGroup.congr ((gens σR).subgroupOf R')
      ((GI.Multicoset.radicalPreimage H N).subgroupOf R') (MulEquiv.refl R')
      (by ext x; simp [hR])
    exact Group.isSolvable_of_surjective e.surjective
  obtain ⟨hNR'_le, hR'H, hN_norm, hrel, hsolvN, hidx⟩ :=
    GI.RadicalFreeOrder.radical_free_order_of_quotient hNH hRR'' hR'K' hsolv_R'' hsup'
  exact ⟨R', hR'u, hNR'_le, hR'H, hN_norm, hrel, hsolvN, hidx, hcost⟩

/-! ### Polynomial and `expLogSq` cost bounds -/

/-- The sum of the exponents of the four primitives. -/
def outbSuppKs (pni pnc pord pm : Prim) : ℕ := pni.k + pnc.k + pord.k + pm.k

/-- The sum of the constants of the four primitives. -/
def outbSuppKp (pni pnc pord pm : Prim) : ℕ :=
  pni.c * 10002 ^ pni.k + pnc.c * 10002 ^ pnc.k + pord.c * 10002 ^ pord.k + pm.c * 10002 ^ pm.k

/-- The exponent of `T + 1` in the polynomial bound of `outbSuppCost`. -/
def outbSuppD (pni pnc pord pm : Prim) : ℕ := 22 + 6 * outbSuppKs pni pnc pord pm

/-- The constant of the polynomial bound of `outbSuppCost`. -/
def outbSuppK (pni pnc pord pm : Prim) : ℕ := 10 ^ 6 * outbSuppKp pni pnc pord pm + 10 ^ 21

/-- **`outbSuppCost` is polynomial in `m` and `T`**:
`outbSuppCost ≤ outbSuppK * ((m + 1)³ * (T + 1)^outbSuppD)` when `n ≤ T`. -/
theorem outbSuppCost_le (pni pnc pord pm : Prim) {n m T : ℕ} (hn : n ≤ T) :
    outbSuppCost pni pnc pord pm n m T ≤
      outbSuppK pni pnc pord pm * ((m + 1) ^ 3 * (T + 1) ^ outbSuppD pni pnc pord pm) := by
  set X := T + 1 with hXdef
  set L := m + 1 with hLdef
  have hX : 1 ≤ X := Nat.succ_pos _
  have hL : 1 ≤ L := Nat.succ_pos _
  have hnX : n + 1 ≤ X := Nat.succ_le_succ hn
  have hL13 : 1 ≤ L ^ 3 := Nat.one_le_pow _ _ hL
  have hL12 : L ≤ L ^ 2 := Nat.le_self_pow (by decide) _
  have hL23 : L ^ 2 ≤ L ^ 3 := Nat.pow_le_pow_right hL (by decide)
  have hL_L3 : L ≤ L ^ 3 := hL12.trans hL23
  set Ks := outbSuppKs pni pnc pord pm with hKs
  set Kp := outbSuppKp pni pnc pord pm with hKp
  set Q := Kp * X ^ (6 * Ks) with hQ
  set Y := 10 ^ 4 * (n + 1) ^ 6 with hYdef
  have hY : Y ≤ 10 ^ 4 * X ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnX 6)
  have qni := outb_bS_le pni hX hY (e := Ks) (by simp only [hKs, outbSuppKs]; omega)
  have qniT := outb_bS_le pni hX (le_rfl : 10 ^ 4 * X ^ 6 ≤ 10 ^ 4 * X ^ 6)
    (e := Ks) (by simp only [hKs, outbSuppKs]; omega)
  have qnc := outb_bS_le pnc hX hY (e := Ks) (by simp only [hKs, outbSuppKs]; omega)
  have qord := outb_bS_le pord hX hY (e := Ks) (by simp only [hKs, outbSuppKs]; omega)
  have qm := outb_bS_le pm hX hY (e := Ks) (by simp only [hKs, outbSuppKs]; omega)
  have hQs : Q = pni.c * 10002 ^ pni.k * X ^ (6 * Ks) + pnc.c * 10002 ^ pnc.k * X ^ (6 * Ks) +
      pord.c * 10002 ^ pord.k * X ^ (6 * Ks) + pm.c * 10002 ^ pm.k * X ^ (6 * Ks) := by
    simp only [hQ, hKp, outbSuppKp]; ring
  have hXX : ∀ a b, a ≤ b → X ^ a ≤ X ^ b := fun a b h => Nat.pow_le_pow_right hX h
  have hXQ : ∀ a b, a ≤ b → X ^ a * Q ≤ X ^ b * Q := fun a b h =>
    Nat.mul_le_mul_right _ (hXX a b h)
  have hn6X : (n + 1) ^ 6 ≤ X ^ 6 := Nat.pow_le_pow_left hnX 6
  have hn8X : (n + 1) ^ 8 ≤ X ^ 8 := Nat.pow_le_pow_left hnX 8
  have hn9X : (n + 1) ^ 9 ≤ X ^ 9 := Nat.pow_le_pow_left hnX 9
  have hY3 : Y ^ 3 ≤ 10 ^ 12 * X ^ 18 := by
    calc Y ^ 3 ≤ (10 ^ 4 * X ^ 6) ^ 3 := Nat.pow_le_pow_left hY 3
      _ = 10 ^ 12 * X ^ 18 := by ring
  have hD' : outbSuppD pni pnc pord pm = 22 + 6 * Ks := rfl
  have hK' : outbSuppK pni pnc pord pm = 10 ^ 6 * Kp + 10 ^ 21 := rfl
  clear_value X L Ks Kp Q Y
  -- 1. `outbSylStepCost`
  have hSylSt : outbSylStepCost pm pord n ≤ 3 * Q + 10 ^ 9 * X ^ 6 := by
    unfold outbSylStepCost
    rw [← hYdef]
    omega
  -- 2. `outbSylPassCost`
  have hSylPs : outbSylPassCost pm pord n m ≤ L ^ 3 * (3 * Q + 2 * 10 ^ 9 * X ^ 6) := by
    unfold outbSylPassCost
    rw [← hLdef]
    calc L * outbSylStepCost pm pord n + 10 ^ 7 * L ^ 3 * (n + 1) ^ 6
        ≤ L ^ 3 * (3 * Q + 10 ^ 9 * X ^ 6) + 10 ^ 7 * L ^ 3 * X ^ 6 :=
          Nat.add_le_add (Nat.mul_le_mul hL_L3 hSylSt)
            (Nat.mul_le_mul_left _ hn6X)
      _ ≤ L ^ 3 * (3 * Q + 2 * 10 ^ 9 * X ^ 6) := by
          have : L ^ 3 * (3 * Q + 10 ^ 9 * X ^ 6) + 10 ^ 7 * L ^ 3 * X ^ 6 =
              L ^ 3 * (3 * Q + 101 * 10 ^ 7 * X ^ 6) := by ring
          rw [this]
          exact Nat.mul_le_mul_left _ (by omega)
  -- 3. `outbSylCost`
  have hSyl : outbSylCost pm pord n m ≤ L ^ 3 * (8 * (X ^ 2 * Q) + 5 * 10 ^ 9 * X ^ 8) := by
    unfold outbSylCost
    rw [← hLdef, ← hYdef]
    have hn22 : n ^ 2 + 2 ≤ 2 * X ^ 2 := by
      have : (n + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hnX 2
      have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      omega
    have h1 : (n ^ 2 + 2) * outbSylPassCost pm pord n m ≤
        L ^ 3 * (6 * (X ^ 2 * Q) + 4 * 10 ^ 9 * X ^ 8) := by
      calc (n ^ 2 + 2) * outbSylPassCost pm pord n m
          ≤ (2 * X ^ 2) * (L ^ 3 * (3 * Q + 2 * 10 ^ 9 * X ^ 6)) := Nat.mul_le_mul hn22 hSylPs
        _ = L ^ 3 * (6 * (X ^ 2 * Q) + 4 * 10 ^ 9 * X ^ 8) := by ring
    have h2 : 2 * pord.boundSize Y ≤ L ^ 3 * (2 * (X ^ 2 * Q)) := by
      have : pord.boundSize Y ≤ X ^ 2 * Q := by
        have hQ1 : Q ≤ X ^ 2 * Q := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hX)
        omega
      calc 2 * pord.boundSize Y ≤ 1 * (2 * (X ^ 2 * Q)) := by omega
        _ ≤ L ^ 3 * (2 * (X ^ 2 * Q)) := Nat.mul_le_mul_right _ hL13
    have h3 : 10 ^ 8 * L ^ 3 * (n + 1) ^ 8 ≤ L ^ 3 * (10 ^ 9 * X ^ 8) := by
      calc 10 ^ 8 * L ^ 3 * (n + 1) ^ 8 ≤ 10 ^ 8 * L ^ 3 * X ^ 8 := Nat.mul_le_mul_left _ hn8X
        _ ≤ 10 ^ 9 * L ^ 3 * X ^ 8 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
        _ = L ^ 3 * (10 ^ 9 * X ^ 8) := by ring
    calc (n ^ 2 + 2) * outbSylPassCost pm pord n m + 2 * pord.boundSize Y + 10 ^ 8 * L ^ 3 * (n + 1) ^ 8
        ≤ L ^ 3 * (6 * (X ^ 2 * Q) + 4 * 10 ^ 9 * X ^ 8) + L ^ 3 * (2 * (X ^ 2 * Q)) +
            L ^ 3 * (10 ^ 9 * X ^ 8) := Nat.add_le_add (Nat.add_le_add h1 h2) h3
      _ = L ^ 3 * (8 * (X ^ 2 * Q) + 5 * 10 ^ 9 * X ^ 8) := by ring
  -- 4. `outbSearchCost`
  have hSearch : outbSearchCost pnc pord pm n m ≤
      L ^ 3 * (2 * 10 ^ 4 * (X ^ 6 * Q) + 2 * 10 ^ 19 * X ^ 18) := by
    unfold outbSearchCost
    rw [← hLdef, ← hYdef]
    have h1 : Y * pm.boundSize Y ≤ 10 ^ 4 * (X ^ 6 * Q) := by
      calc Y * pm.boundSize Y ≤ (10 ^ 4 * X ^ 6) * Q := Nat.mul_le_mul hY (by omega)
        _ = 10 ^ 4 * (X ^ 6 * Q) := by ring
    have h2 : pnc.boundSize Y + pord.boundSize Y + Y * pm.boundSize Y ≤
        L ^ 3 * (11000 * (X ^ 6 * Q)) := by
      have hQ6 : Q ≤ X ^ 6 * Q := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hX)
      have : pnc.boundSize Y + pord.boundSize Y + Y * pm.boundSize Y ≤ 11000 * (X ^ 6 * Q) := by
        omega
      calc _ ≤ 1 * (11000 * (X ^ 6 * Q)) := by omega
        _ ≤ L ^ 3 * (11000 * (X ^ 6 * Q)) := Nat.mul_le_mul_right _ hL13
    have h3 : 10 ^ 7 * L ^ 3 * Y ^ 3 ≤ L ^ 3 * (10 ^ 19 * X ^ 18) := by
      calc 10 ^ 7 * L ^ 3 * Y ^ 3 ≤ 10 ^ 7 * L ^ 3 * (10 ^ 12 * X ^ 18) :=
            Nat.mul_le_mul_left _ hY3
        _ = L ^ 3 * (10 ^ 19 * X ^ 18) := by ring
    have hSyl' : outbSylCost pm pord n m ≤ L ^ 3 * (8 * (X ^ 6 * Q) + 5 * 10 ^ 9 * X ^ 18) := by
      refine hSyl.trans (Nat.mul_le_mul_left _ (Nat.add_le_add
        (Nat.mul_le_mul_left _ (hXQ 2 6 (by decide)))
        (Nat.mul_le_mul_left _ (hXX 8 18 (by decide)))))
    calc outbSylCost pm pord n m + pnc.boundSize Y + pord.boundSize Y + Y * pm.boundSize Y +
          10 ^ 7 * L ^ 3 * Y ^ 3
        = outbSylCost pm pord n m + (pnc.boundSize Y + pord.boundSize Y + Y * pm.boundSize Y) +
            10 ^ 7 * L ^ 3 * Y ^ 3 := by omega
      _ ≤ L ^ 3 * (8 * (X ^ 6 * Q) + 5 * 10 ^ 9 * X ^ 18) + L ^ 3 * (11000 * (X ^ 6 * Q)) +
            L ^ 3 * (10 ^ 19 * X ^ 18) := Nat.add_le_add (Nat.add_le_add hSyl' h2) h3
      _ = L ^ 3 * (11008 * (X ^ 6 * Q) + (10 ^ 19 + 5 * 10 ^ 9) * X ^ 18) := by ring
      _ ≤ L ^ 3 * (2 * 10 ^ 4 * (X ^ 6 * Q) + 2 * 10 ^ 19 * X ^ 18) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_right _ (by norm_num))
            (Nat.mul_le_mul_right _ (by norm_num)))
  -- 5. `outbFindCost`
  have hFind : outbFindCost pnc pord pm n m ≤
      L ^ 3 * (4 * 10 ^ 4 * (X ^ 7 * Q) + 5 * 10 ^ 19 * X ^ 19) := by
    unfold outbFindCost
    rw [← hLdef, ← hYdef]
    have h1 : (n + 2) * outbSearchCost pnc pord pm n m ≤
        L ^ 3 * (4 * 10 ^ 4 * (X ^ 7 * Q) + 4 * 10 ^ 19 * X ^ 19) := by
      calc (n + 2) * outbSearchCost pnc pord pm n m
          ≤ (2 * X) * (L ^ 3 * (2 * 10 ^ 4 * (X ^ 6 * Q) + 2 * 10 ^ 19 * X ^ 18)) :=
            Nat.mul_le_mul (by omega) hSearch
        _ = L ^ 3 * (4 * 10 ^ 4 * (X ^ 7 * Q) + 4 * 10 ^ 19 * X ^ 19) := by ring
    have h2 : 10 ^ 6 * L ^ 3 * Y ^ 3 ≤ L ^ 3 * (10 ^ 19 * X ^ 19) := by
      have hX18_19 := hXX 18 19 (by decide)
      calc 10 ^ 6 * L ^ 3 * Y ^ 3 ≤ 10 ^ 6 * L ^ 3 * (10 ^ 12 * X ^ 18) :=
            Nat.mul_le_mul_left _ hY3
        _ = L ^ 3 * (10 ^ 18 * X ^ 18) := by ring
        _ ≤ L ^ 3 * (10 ^ 19 * X ^ 19) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul (by norm_num) hX18_19)
    calc (n + 2) * outbSearchCost pnc pord pm n m + 10 ^ 6 * L ^ 3 * Y ^ 3
        ≤ L ^ 3 * (4 * 10 ^ 4 * (X ^ 7 * Q) + 4 * 10 ^ 19 * X ^ 19) +
            L ^ 3 * (10 ^ 19 * X ^ 19) := Nat.add_le_add h1 h2
      _ = L ^ 3 * (4 * 10 ^ 4 * (X ^ 7 * Q) + 5 * 10 ^ 19 * X ^ 19) := by ring
  -- 6. `outbFixStepCost` and `outbFixCost`
  have hFixSt : outbFixStepCost pm n ≤ 2 * 10 ^ 4 * (X ^ 6 * Q) + 10 ^ 17 * X ^ 18 := by
    unfold outbFixStepCost
    rw [← hYdef]
    have h1 : (Y + 1) * pm.boundSize Y ≤ 2 * 10 ^ 4 * (X ^ 6 * Q) := by
      have hY1 : Y + 1 ≤ 2 * 10 ^ 4 * X ^ 6 := by
        have : 1 ≤ X ^ 6 := Nat.one_le_pow _ _ hX
        omega
      calc (Y + 1) * pm.boundSize Y ≤ (2 * 10 ^ 4 * X ^ 6) * Q := Nat.mul_le_mul hY1 (by omega)
        _ = 2 * 10 ^ 4 * (X ^ 6 * Q) := by ring
    have h2 : 10 ^ 5 * Y ^ 3 ≤ 10 ^ 17 * X ^ 18 := by
      calc 10 ^ 5 * Y ^ 3 ≤ 10 ^ 5 * (10 ^ 12 * X ^ 18) := Nat.mul_le_mul_left _ hY3
        _ = 10 ^ 17 * X ^ 18 := by ring
    exact Nat.add_le_add h1 h2
  have hFix : (n + 1) ^ 2 * outbFixCost pm n m ≤
      L ^ 3 * (2 * 10 ^ 4 * (X ^ 8 * Q) + 2 * 10 ^ 17 * X ^ 20) := by
    have h1 : outbFixCost pm n m ≤ L ^ 3 * (2 * 10 ^ 4 * (X ^ 6 * Q) + 2 * 10 ^ 17 * X ^ 18) := by
      unfold outbFixCost
      rw [← hLdef]
      have hX6_18 : (n + 1) ^ 6 ≤ X ^ 18 := hn6X.trans (hXX 6 18 (by decide))
      calc L * outbFixStepCost pm n + 10 ^ 7 * L ^ 3 * (n + 1) ^ 6
          ≤ L ^ 3 * (2 * 10 ^ 4 * (X ^ 6 * Q) + 10 ^ 17 * X ^ 18) + 10 ^ 7 * L ^ 3 * X ^ 18 :=
            Nat.add_le_add (Nat.mul_le_mul hL_L3 hFixSt) (Nat.mul_le_mul_left _ hX6_18)
        _ ≤ L ^ 3 * (2 * 10 ^ 4 * (X ^ 6 * Q) + 2 * 10 ^ 17 * X ^ 18) := by
            have : L ^ 3 * (2 * 10 ^ 4 * (X ^ 6 * Q) + 10 ^ 17 * X ^ 18) + 10 ^ 7 * L ^ 3 * X ^ 18 =
                L ^ 3 * (2 * 10 ^ 4 * (X ^ 6 * Q) + (10 ^ 17 + 10 ^ 7) * X ^ 18) := by ring
            rw [this]
            exact Nat.mul_le_mul_left _ (Nat.add_le_add_left
              (Nat.mul_le_mul_right _ (by norm_num)) _)
    calc (n + 1) ^ 2 * outbFixCost pm n m
        ≤ X ^ 2 * (L ^ 3 * (2 * 10 ^ 4 * (X ^ 6 * Q) + 2 * 10 ^ 17 * X ^ 18)) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hnX 2) h1
      _ = L ^ 3 * (2 * 10 ^ 4 * (X ^ 8 * Q) + 2 * 10 ^ 17 * X ^ 20) := by ring
  -- 7. `outbDescCost`
  have hDesc : outbDescCost pni pnc pord pm n m ≤
      L ^ 3 * (10 ^ 5 * (X ^ 8 * Q) + 10 ^ 20 * X ^ 20) := by
    unfold outbDescCost
    rw [← hLdef, ← hYdef]
    have h1 : 2 * pni.boundSize Y ≤ L ^ 3 * (2 * (X ^ 8 * Q)) := by
      have hQ8 : Q ≤ X ^ 8 * Q := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hX)
      calc 2 * pni.boundSize Y ≤ 1 * (2 * (X ^ 8 * Q)) := by omega
        _ ≤ L ^ 3 * (2 * (X ^ 8 * Q)) := Nat.mul_le_mul_right _ hL13
    have hFind' : outbFindCost pnc pord pm n m ≤
        L ^ 3 * (4 * 10 ^ 4 * (X ^ 8 * Q) + 5 * 10 ^ 19 * X ^ 20) :=
      hFind.trans (Nat.mul_le_mul_left _ (Nat.add_le_add
        (Nat.mul_le_mul_left _ (hXQ 7 8 (by decide)))
        (Nat.mul_le_mul_left _ (hXX 19 20 (by decide)))))
    have h3 : 10 ^ 9 * L ^ 2 * (n + 1) ^ 9 ≤ L ^ 3 * (10 ^ 9 * X ^ 20) := by
      have hX9_20 : (n + 1) ^ 9 ≤ X ^ 20 := hn9X.trans (hXX 9 20 (by decide))
      calc 10 ^ 9 * L ^ 2 * (n + 1) ^ 9 ≤ 10 ^ 9 * L ^ 3 * X ^ 20 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hL23) hX9_20
        _ = L ^ 3 * (10 ^ 9 * X ^ 20) := by ring
    calc 2 * pni.boundSize Y + outbFindCost pnc pord pm n m + (n + 1) ^ 2 * outbFixCost pm n m +
          10 ^ 9 * L ^ 2 * (n + 1) ^ 9
        ≤ L ^ 3 * (2 * (X ^ 8 * Q)) + L ^ 3 * (4 * 10 ^ 4 * (X ^ 8 * Q) + 5 * 10 ^ 19 * X ^ 20) +
            L ^ 3 * (2 * 10 ^ 4 * (X ^ 8 * Q) + 2 * 10 ^ 17 * X ^ 20) +
            L ^ 3 * (10 ^ 9 * X ^ 20) :=
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 hFind') hFix) h3
      _ = L ^ 3 * (60002 * (X ^ 8 * Q) + (5 * 10 ^ 19 + 2 * 10 ^ 17 + 10 ^ 9) * X ^ 20) := by ring
      _ ≤ L ^ 3 * (10 ^ 5 * (X ^ 8 * Q) + 10 ^ 20 * X ^ 20) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_right _ (by norm_num))
            (Nat.mul_le_mul_right _ (by norm_num)))
  -- 8. `outbSuppCost`
  unfold outbSuppCost
  rw [← hXdef, ← hLdef]
  have h1 : 3 * pni.boundSize (10 ^ 4 * X ^ 6) ≤ L ^ 3 * (3 * (X ^ 10 * Q)) := by
    have hQ10 : Q ≤ X ^ 10 * Q := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hX)
    calc 3 * pni.boundSize (10 ^ 4 * X ^ 6) ≤ 1 * (3 * (X ^ 10 * Q)) := by omega
      _ ≤ L ^ 3 * (3 * (X ^ 10 * Q)) := Nat.mul_le_mul_right _ hL13
  have hn21 : n ^ 2 + 1 ≤ X ^ 2 := by
    have : (n + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hnX 2
    have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  have h2 : (n ^ 2 + 1) * outbDescCost pni pnc pord pm n m ≤
      L ^ 3 * (10 ^ 5 * (X ^ 10 * Q) + 10 ^ 20 * X ^ 22) := by
    calc (n ^ 2 + 1) * outbDescCost pni pnc pord pm n m
        ≤ X ^ 2 * (L ^ 3 * (10 ^ 5 * (X ^ 8 * Q) + 10 ^ 20 * X ^ 20)) := Nat.mul_le_mul hn21 hDesc
      _ = L ^ 3 * (10 ^ 5 * (X ^ 10 * Q) + 10 ^ 20 * X ^ 22) := by ring
  have h3 : 10 ^ 9 * L ^ 2 * X ^ 9 ≤ L ^ 3 * (10 ^ 9 * X ^ 22) := by
    calc 10 ^ 9 * L ^ 2 * X ^ 9 ≤ 10 ^ 9 * L ^ 3 * X ^ 22 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hL23) (hXX 9 22 (by decide))
      _ = L ^ 3 * (10 ^ 9 * X ^ 22) := by ring
  have htot : 3 * pni.boundSize (10 ^ 4 * X ^ 6) + (n ^ 2 + 1) * outbDescCost pni pnc pord pm n m +
      10 ^ 9 * L ^ 2 * X ^ 9 ≤ L ^ 3 * (10 ^ 6 * (X ^ 10 * Q) + 10 ^ 21 * X ^ 22) := by
    calc _ ≤ L ^ 3 * (3 * (X ^ 10 * Q)) + L ^ 3 * (10 ^ 5 * (X ^ 10 * Q) + 10 ^ 20 * X ^ 22) +
          L ^ 3 * (10 ^ 9 * X ^ 22) := Nat.add_le_add (Nat.add_le_add h1 h2) h3
      _ = L ^ 3 * (100003 * (X ^ 10 * Q) + (10 ^ 20 + 10 ^ 9) * X ^ 22) := by ring
      _ ≤ L ^ 3 * (10 ^ 6 * (X ^ 10 * Q) + 10 ^ 21 * X ^ 22) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_right _ (by norm_num))
            (Nat.mul_le_mul_right _ (by norm_num)))
  refine htot.trans ?_
  rw [hD', hK']
  have hX10Q : X ^ 10 * Q ≤ Kp * X ^ (22 + 6 * Ks) := by
    rw [hQ]
    calc X ^ 10 * (Kp * X ^ (6 * Ks)) = Kp * X ^ (10 + 6 * Ks) := by rw [pow_add]; ring
      _ ≤ Kp * X ^ (22 + 6 * Ks) := Nat.mul_le_mul_left _ (hXX _ _ (by omega))
  have hX22 : X ^ 22 ≤ X ^ (22 + 6 * Ks) := hXX _ _ (by omega)
  calc L ^ 3 * (10 ^ 6 * (X ^ 10 * Q) + 10 ^ 21 * X ^ 22)
      ≤ L ^ 3 * (10 ^ 6 * (Kp * X ^ (22 + 6 * Ks)) + 10 ^ 21 * X ^ (22 + 6 * Ks)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ hX10Q)
          (Nat.mul_le_mul_left _ hX22))
    _ = (10 ^ 6 * Kp + 10 ^ 21) * (L ^ 3 * X ^ (22 + 6 * Ks)) := by ring

/-- Power of `expLogSq`. -/
theorem outb_expLogSq_pow (a : ℝ) (D N : ℕ) : expLogSq a N ^ D = expLogSq (D * a) N := by
  unfold expLogSq
  rw [← Real.exp_nat_mul]
  ring_nf

/-- The constant in front of `(N + 2) ^ (8 * outbSuppD)` in the `expLogSq` bound. -/
def outbSuppCbig (pni pnc pord pm : Prim) : ℕ :=
  outbSuppK pni pnc pord pm * 8 * (4 * 10 ^ 6) ^ outbSuppD pni pnc pord pm

/-- **The exponent constant of `outbSuppCost` in `expLogSq`** when `(m : ℝ) ≤ expLogSq c N`. -/
noncomputable def outbSuppA (pni pnc pord pm : Prim) (c : ℝ) : ℝ :=
  3 * (Real.log (outbSuppCbig pni pnc pord pm) + ((8 * outbSuppD pni pnc pord pm : ℕ) : ℝ)) + 3 * c

/-- **`outbSuppCost` lies in `expLogSq`**: when `(m : ℝ) ≤ expLogSq c N` (`0 ≤ c`) and
`T + 1 ≤ tmVB N` (`n ≤ T`), `(outbSuppCost pni pnc pord pm n m T : ℝ) ≤ expLogSq (outbSuppA ... c) N`. -/
theorem outbSupp_cost_le_expLogSq (pni pnc pord pm : Prim) {c : ℝ} (hc : 0 ≤ c)
    {N n m T : ℕ} (hn : n ≤ T) (hm : (m : ℝ) ≤ expLogSq c N) (hTN : T + 1 ≤ tmVB N) :
    (outbSuppCost pni pnc pord pm n m T : ℝ) ≤
      expLogSq (outbSuppA pni pnc pord pm c) N := by
  set e := outbSuppD pni pnc pord pm
  set K := outbSuppK pni pnc pord pm
  set V := tmVB N with hV
  have hVr : ((V ^ e : ℕ) : ℝ) = (4 * 10 ^ 6 : ℝ) ^ e * ((N : ℝ) + 2) ^ (8 * e) := by
    rw [hV]; unfold tmVB; push_cast; rw [mul_pow, ← pow_mul]; norm_num
  clear_value V
  have hP := outbSuppCost_le pni pnc pord pm hn (m := m)
  have hTe : (T + 1) ^ e ≤ V ^ e := Nat.pow_le_pow_left hTN e
  have hnat : outbSuppCost pni pnc pord pm n m T ≤ K * ((m + 1) ^ 3 * V ^ e) :=
    hP.trans (Nat.mul_le_mul_left K (Nat.mul_le_mul_left ((m + 1) ^ 3) hTe))
  have hE1 : (1 : ℝ) ≤ expLogSq c N := tm_one_le_expLogSq hc N
  have hL : ((m : ℝ) + 1) ≤ 2 * expLogSq c N := by linarith
  have hL3 : ((m : ℝ) + 1) ^ 3 ≤ 8 * expLogSq (3 * c) N := by
    have : ((m : ℝ) + 1) ^ 3 ≤ (2 * expLogSq c N) ^ 3 := pow_le_pow_left₀ (by positivity) hL 3
    have e3 : expLogSq c N ^ 3 = expLogSq ((3 : ℕ) * c) N := outb_expLogSq_pow c 3 N
    rw [mul_pow, e3] at this
    norm_num at this ⊢
    linarith
  have hCb1 : (1 : ℝ) ≤ (outbSuppCbig pni pnc pord pm : ℝ) := by
    have : 0 < outbSuppCbig pni pnc pord pm := by
      unfold outbSuppCbig outbSuppK
      exact Nat.mul_pos (Nat.mul_pos (by omega) (by norm_num)) (pow_pos (by norm_num) _)
    exact_mod_cast this
  have hpe := pow_le_expLogSq hCb1 (8 * e) N
  have hcast : (outbSuppCost pni pnc pord pm n m T : ℝ) ≤
      (K : ℝ) * (((m : ℝ) + 1) ^ 3 * ((V ^ e : ℕ) : ℝ)) := by
    have := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast at this ⊢
    linarith
  have hCb : (outbSuppCbig pni pnc pord pm : ℝ) = (K : ℝ) * 8 * (4 * 10 ^ 6 : ℝ) ^ e := by
    unfold outbSuppCbig; push_cast; ring
  have heA : outbSuppA pni pnc pord pm c =
      3 * (Real.log (outbSuppCbig pni pnc pord pm) + ((8 * e : ℕ) : ℝ)) + 3 * c := rfl
  clear_value e K
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hNe : (0 : ℝ) ≤ (4 * 10 ^ 6 : ℝ) ^ e * ((N : ℝ) + 2) ^ (8 * e) :=
    mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4 * 10 ^ 6) e)
      (pow_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith) (8 * e))
  refine hcast.trans ?_
  calc (K : ℝ) * (((m : ℝ) + 1) ^ 3 * ((V ^ e : ℕ) : ℝ))
      ≤ (K : ℝ) * ((8 * expLogSq (3 * c) N) *
          ((4 * 10 ^ 6 : ℝ) ^ e * ((N : ℝ) + 2) ^ (8 * e))) := by
        rw [hVr]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL3 hNe) hK0
    _ = ((outbSuppCbig pni pnc pord pm : ℝ) * ((N : ℝ) + 2) ^ (8 * e)) * expLogSq (3 * c) N := by
        rw [hCb]; ring
    _ ≤ expLogSq (3 * (Real.log (outbSuppCbig pni pnc pord pm) + ((8 * e : ℕ) : ℝ))) N *
          expLogSq (3 * c) N :=
        mul_le_mul_of_nonneg_right hpe (expLogSq_nonneg _ _)
    _ = expLogSq (outbSuppA pni pnc pord pm c) N := by rw [tm_expLogSq_mul, heA]

end GI.Impl
