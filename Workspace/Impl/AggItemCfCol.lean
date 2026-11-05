module

public import Workspace.Impl.AggItemCfCell
public import Workspace.Impl.AggItemCfSpec
public import Workspace.Impl.AggItemCfFr
public import Workspace.Impl.AggInc
public import Workspace.Lang.Lib.LinIntTake
public import Workspace.Lang.Lib.Tabulate
public import Workspace.Lang.Prims.Ops

@[expose] public section

/-!
# The orbital coloring of Case 2b, as a program (`col`)

`itCfColF` runs on `[q, ⟨H⟩, ⟨t⟩]` and returns the table `encKColoring (orbColOut H t)`
(`it_cfCol_spec`). It follows the definition (`OutOrbital.lean`):

1. `itCfFrF`: the sorted dominant orbit `Φ` of `H` and the degree `d = transDeg H Φ`, by the
   stabilizer chain (`AggItemCfFr.lean`).
2. If `d ≥ ℓ` there is no object, and the coloring is zero: `q²` zeros.
3. Otherwise: the anchors `A = t_0, …, t_{d-2}` (a prefix of `t`); their pointwise stabilizer
   `U` in `H`, by the cited **PointwiseStab** (`pstab_spec`; its precondition is that `⟨H⟩` is a
   group value, which holds for the input); the orbit of the pair `[t_{d-1}, t_d]` under `U`
   (`tupOrb_spec`, with at most `q²` points by `itCf_orbit_ncard`); and the table of the `q²`
   cells (`itCf_cell_spec`, `itCf_table_eq`).
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens pointwiseStab PointwiseStab encKColoring)

variable {q ℓ : ℕ}

/-- `q * q`, on the input `[q, ⟨H⟩, ⟨t⟩]`. -/
def itCfQQ : Expr := .arith .mul (arg 0) (arg 0)

/-- The degree `d`, read from the result `[⟨Φ⟩, d]` of the front (the second variable). -/
def itCfDE : Expr := .get (.var 1) (.nat 1)

/-- The branch `d < ℓ`. Variables: input, front result, anchors, stabilizer, orbit, points. -/
def itCfColMain (tk ps tor rng mp : ℕ) : Expr :=
  .letE (.call tk (mk2 (.arith .sub itCfDE (.nat 1)) (arg 2)))
   (.letE (.call ps (mk2 (arg 1) (.var 2)))
    (.letE (.call tor (mk5 (.nat 0) (.get (.var 3) (.nat 1))
         (mk2 (.get (arg 2) (.arith .sub itCfDE (.nat 1))) (.get (arg 2) itCfDE)) itCfQQ (arg 0)))
     (.letE (.call rng itCfQQ)
       (.call mp (mk2 (mk4 (arg 0) (.get (.var 1) (.nat 0)) (.var 2) (.var 4)) (.var 5))))))

/-- **The program `col`**, on `[q, ⟨H⟩, ⟨t⟩]`. -/
def itCfColF (fr rep tk ps tor rng mp : ℕ) : Expr :=
  .letE (.call fr (arg 1))
   (.ite (.arith .sub (.length (arg 2)) itCfDE) (itCfColMain tk ps tor rng mp)
     (.call rep (mk2 itCfQQ (.nat 0))))

theorem itCf_encPts_natList (xs : List (Fin q)) : encPts xs = natList (xs.map Fin.val) := by
  rw [itCf_encPts_eq, natList, List.map_map]
  rfl

theorem itCf_ids_eq : natList (List.range (q * q)) = encFun fun i : Fin (q ^ 2) => (i : ℕ) := by
  rw [← sq, encFun, natList, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

theorem itCf_wt_list5_le (a b c d e : Val) :
    (Val.list [a, b, c, d, e]).wt ≤ 2 * (a.wt + b.wt + c.wt + d.wt + e.wt) + 9 := by
  have := wt_list_le [a, b, c, d, e]; simp at this; omega

theorem itCf_wt_tab {m N : ℕ} (F : Fin m → Val) (hF : ∀ i, ∃ n ≤ N, F i = .nat n) :
    (Val.list ((List.finRange m).map F)).wt ≤ m * (2 * N + 5) + 4 := by
  have := wt_list_le_of ((List.finRange m).map F) (c := N + 2) (by
    intro v hv
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv
    obtain ⟨n, hn, e⟩ := hF i
    rw [e]; have := wt_nat_le n; omega)
  simpa [Nat.mul_add, Nat.add_assoc] using this

theorem linTakeCost_mono {a b : ℕ} (h : a ≤ b) : linTakeCost a ≤ linTakeCost b :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)

theorem itCf_boundSize_mono (p : Prim) {a b : ℕ} (h : a ≤ b) : p.boundSize a ≤ p.boundSize b :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-! ### The branch `d < ℓ` -/

/-- The bound of the orbit call. -/
def itCfTB (W : ℕ) : ℕ := tupK * (320 * W ^ 6 + W + W * W + 22) ^ 12

/-- The weight bound of the list of the points `0, …, q² - 1`. -/
def itCfColIB (W : ℕ) : ℕ := W * W * (2 * (W * W + 2) + 1) + 4

/-- The weight bound of the table (its entries are at most `7 + W`). -/
def itCfColKB (W : ℕ) : ℕ := W * W * (2 * W + 19) + 4

/-- The weight bound of the context of the cells. -/
def itCfCB (W RW : ℕ) : ℕ := 2 * (W + RW + W + itCfTB W) + 8

/-- The cost bound of the branch `d < ℓ`, for an input of weight `W` and a front result of weight
at most `RW`. -/
noncomputable def itCfColMC (hps : PointwiseStab) (W RW : ℕ) : ℕ :=
  linTakeCost (4 * W + 8) + (pointwiseStabPrim hps).boundSize (4 * W + 6) +
    pstabK * (4 * W + 6) ^ 9 + 2 * itCfTB W +
    loopModK * (W * W + 1) * (2 * (W * W) + itCfColIB W + 3) +
    W * W * itCfCellC (2 * itCfCB W RW + 2 * (W * W) + W + 20) +
    mapK * (W * W + 1) * (2 * (itCfCB W RW + itCfColIB W) + 6 + itCfColKB W + 1) +
    1000 * (W + RW + itCfTB W + itCfColIB W + itCfCB W RW + itCfColKB W + 320 * W ^ 6) + 1000

set_option maxHeartbeats 2000000 in
theorem itCf_colMain_spec (hps : PointwiseStab) {P : Program}
    {tk ps tor rng mp fc an1 an2 fnd pe pp jps : ℕ}
    (htk : P.HasAt tk (linTakeFuns tk)) (hpsF : P.HasAt ps (pstabFuns ps jps))
    (hj : P.prims[jps]? = some (pointwiseStabPrim hps)) (hto : P.HasAt tor (tupOrbFuns tor))
    (hrng : P.HasAt rng (rangeFuns rng)) (hmp : P.HasAt mp (mapFuns mp fc))
    (hfc : P.funs[fc]? = some (itCfCellF an1 an2 fnd)) (han1 : P.HasAt an1 (anyFuns an1 pe))
    (hpe : P.funs[pe]? = some itCfEqP) (han2 : P.HasAt an2 (anyFuns an2 pp))
    (hpp : P.funs[pp]? = some itCfPairP) (hfnd : P.HasAt fnd (findFuns fnd pe))
    (hs : List (Perm (Fin q))) (t : Fin ℓ → Fin q)
    (hd : transDeg (gens hs) (domSet (gens hs)) < ℓ) {RW : ℕ}
    (hR : (Val.list [encPts (domSet (gens hs)).sort,
      .nat (transDeg (gens hs) (domSet (gens hs)))]).wt ≤ RW) :
    EvalAll P [itCfColIn hs t, .list [encPts (domSet (gens hs)).sort,
        .nat (transDeg (gens hs) (domSet (gens hs)))]] (itCfColMain tk ps tor rng mp)
      (fun w c => w = encKColoring (orbColOut (gens hs) t) ∧
        c ≤ itCfColMC hps (itCfColIn hs t).wt RW) := by
  set d := transDeg (gens hs) (domSet (gens hs)) with hdd
  set xs := (domSet (gens hs)).sort with hxs
  set tv : List Val := ((List.finRange ℓ).map fun i => (t i : ℕ)).map Val.nat with htv
  set vs : List Val := [.nat q, encGroup hs, .list tv] with hvs
  have ev : itCfColIn hs t = .list vs := rfl
  set R : Val := .list [encPts xs, .nat d] with hRd
  rw [ev]
  set W := (Val.list vs).wt with hW
  have eR : (Val.list [encPts xs, .nat d]).wt = R.wt := rfl
  -- weights of the input
  have wq : (Val.nat q).wt < W := wt_le_wt_list (by simp [hvs])
  have wg : (encGroup hs).wt < W := wt_le_wt_list (by simp [hvs])
  have wt' : (Val.list tv).wt < W := wt_le_wt_list (by simp [hvs])
  have hq1 : q + 1 ≤ (encGroup hs).wt := by have := S_le_wt_encGroup hs; nlinarith
  have hltv : tv.length = ℓ := by simp [htv]
  have hlW : ℓ < W := by have := length_lt_wt_list tv; omega
  have hdq : d ≤ q := by
    have h1 := (transDeg_spec (gens hs) (domSet (gens hs))).2
    have h2 := Finset.card_le_univ (domSet (gens hs))
    rw [Fintype.card_fin] at h2
    omega
  -- step 1: the anchors
  have dE : Det P [Val.list vs, R] itCfDE (.nat d) _ :=
    Det.get' (Det.var' (P := P) (env := [Val.list vs, R]) (i := 1) rfl) (Det.nat 1) rfl
  have dA := Det.mk2 (Det.arith' (op := .sub) dE (Det.nat 1) rfl)
    (Det.arg' (P := P) (vs := vs) (rest := [R]) (j := 2) rfl)
  have hTk := linTake_spec htk tv (d - 1) (by omega)
  rw [show Val.list (tv.take (d - 1)) = encPts (itCfAnc t d) from (itCf_anc_val t d).symm] at hTk
  have d1 := Det.call dA hTk
  refine EvalAll.letE d1 fun w1 c1 h1 => ?_
  obtain ⟨rfl, hc1⟩ := h1
  -- step 2: the pointwise stabilizer of the anchors
  have aW : (encPts (itCfAnc t d)).wt ≤ (Val.list tv).wt := by
    rw [itCf_anc_val]; exact wt_list_sublist (List.take_sublist _ _)
  have hP := pstab_spec hps hpsF hj (G := gens hs) ⟨hs, rfl, rfl⟩ (itCfAnc t d)
  have dm2 := Det.mk2 (Det.arg' (P := P) (vs := vs) (rest := [R, encPts (itCfAnc t d)]) (j := 1) rfl)
    (Det.var' (P := P) (env := [Val.list vs, R, encPts (itCfAnc t d)]) (i := 2) rfl)
  have hcall2 : EvalAll P [Val.list vs, R, encPts (itCfAnc t d)] (.call ps (mk2 (arg 1) (.var 2)))
      (fun w c => ∃ gs : List (Perm (Fin q)), w = encGroup gs ∧
        gens gs = pointwiseStab (gens hs) (itCfAnc t d) ∧ w.wt ≤ 320 * (q + 1) ^ 6 ∧
        c ≤ 2 * W + 1 + 5 + ((encPts (itCfAnc t d)).wt + 1) +
          2 * (Val.list [encGroup hs, encPts (itCfAnc t d)]).wt + 7 +
          ((pointwiseStabPrim hps).bound (.list [encGroup hs, encPts (itCfAnc t d)]) +
            pstabK * (Val.list [encGroup hs, encPts (itCfAnc t d)]).wt ^ 9) + w.wt + 1) :=
    EvalAll.call_funAll dm2 fun v ca hv => by
      obtain ⟨rfl, hca⟩ := hv
      exact hP.mono fun w c ⟨⟨gs, hw, hgs⟩, hww, hc⟩ => ⟨gs, hw, hgs, hww, by omega⟩
  refine EvalAll.letE hcall2 fun w2 c2 h2 => ?_
  obtain ⟨gs, rfl, hgs, hUw, hc2⟩ := h2
  -- step 3: the orbit of the pair `[t_{d-1}, t_d]` under the stabilizer
  have hdl : d - 1 < ℓ := by omega
  have dE2 : Det P [Val.list vs, R, encPts (itCfAnc t d), encGroup gs] itCfDE (.nat d) _ :=
    Det.get' (Det.var' (P := P) (env := [Val.list vs, R, encPts (itCfAnc t d), encGroup gs])
      (i := 1) rfl) (Det.nat 1) rfl
  have dT := Det.arg' (P := P) (vs := vs) (rest := [R, encPts (itCfAnc t d), encGroup gs])
    (j := 2) (v := .list tv) rfl
  have du := Det.get' dT (Det.arith' (op := .sub) dE2 (Det.nat 1) rfl) (itCf_stTv_get t (d - 1) hdl)
  have dv := Det.get' dT dE2 (itCf_stTv_get t d hd)
  have dG : Det P [Val.list vs, R, encPts (itCfAnc t d), encGroup gs] (.get (.var 3) (.nat 1))
      (.list ((1 :: gs).map encPerm)) _ :=
    Det.get' (Det.var' (P := P) (env := [Val.list vs, R, encPts (itCfAnc t d), encGroup gs])
      (i := 3) rfl) (Det.nat 1) rfl
  have dq0 := Det.arg' (P := P) (vs := vs) (rest := [R, encPts (itCfAnc t d), encGroup gs])
    (j := 0) (v := .nat q) rfl
  have dQQ := Det.arith' (op := .mul) dq0 dq0 rfl
  have wU : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
    wt_le_wt_list (show _ ∈ [Val.nat q, _] by simp)
  have wpair := wt_list2_le (.nat (t ⟨d - 1, hdl⟩)) (.nat (t ⟨d, hd⟩))
  have wp0 := wt_nat_le (t ⟨d - 1, hdl⟩); have wp1 := wt_nat_le (t ⟨d, hd⟩)
  have hp0 := (t ⟨d - 1, hdl⟩).isLt; have hp1 := (t ⟨d, hd⟩).isLt
  have w5 := itCf_wt_list5_le (.nat 0) (.list ((1 :: gs).map encPerm))
    (.list [.nat (t ⟨d - 1, hdl⟩), .nat (t ⟨d, hd⟩)]) (.nat (q * q)) (.nat q)
  have eU : (encGroup gs).wt = (Val.list [.nat q, .list ((1 :: gs).map encPerm)]).wt := rfl
  have wn0 := wt_nat_le 0; have wnqq := wt_nat_le (q * q); have wnq := wt_nat_le q
  have wnd := wt_nat_le d
  have dm5 := (Det.mk5 (Det.nat (P := P)
    (env := [Val.list vs, R, encPts (itCfAnc t d), encGroup gs]) 0) dG (Det.mk2 du dv) dQQ dq0).mono
    (c' := 300 * (W + R.wt + (encGroup gs).wt + q * q) + 500) (by
      simp only [GI.Machine.BinOp.eval]
      omega)
  have hT := (tupOrb_spec hto (1 :: gs) [t ⟨d - 1, hdl⟩, t ⟨d, hd⟩]
    (itCf_orbit_ncard _ _ _)).wt_lt
  set TT := tupK * ((1 :: gs).length + q + q * q + [t ⟨d - 1, hdl⟩, t ⟨d, hd⟩].length + 20) ^ 12
    with hTT
  have hcall3 : EvalAll P [Val.list vs, R, encPts (itCfAnc t d), encGroup gs]
      (.call tor (mk5 (.nat 0) (.get (.var 3) (.nat 1))
         (mk2 (.get (arg 2) (.arith .sub itCfDE (.nat 1))) (.get (arg 2) itCfDE)) itCfQQ (arg 0)))
      (fun w c => ∃ L : List (List (Fin q) × Perm (Fin q)), w = encPairs ptsKey L ∧
        (∀ y, y ∈ L.map Prod.fst ↔
          y ∈ actOrbit (fun g (xs : List (Fin q)) => xs.map g) (1 :: gs) [t ⟨d - 1, hdl⟩, t ⟨d, hd⟩]) ∧
        (∀ p ∈ L, p.1.length = 2) ∧ w.wt < TT ∧
        c ≤ 300 * (W + R.wt + (encGroup gs).wt + q * q) + 500 + TT + w.wt + 1) :=
    EvalAll.call_funAll dm5 fun v ca hv => by
      obtain ⟨rfl, hca⟩ := hv
      refine hT.mono fun w c hw => ?_
      obtain ⟨⟨L, hw, _, hLm, hLp, _, hc⟩, hwc⟩ := hw
      refine ⟨L, hw, hLm, fun p hp => ?_, ?_, ?_⟩
      · rw [← (hLp p hp).2, List.length_map]; rfl
      · rw [hTT]; omega
      · rw [hTT]; omega
  refine EvalAll.letE hcall3 fun w3 c3 h3 => ?_
  obtain ⟨L, rfl, hLm, hL2, hLw, hc3⟩ := h3
  -- step 4: the points `0, …, q² - 1`
  have dq3 := Det.arg' (P := P) (vs := vs)
    (rest := [R, encPts (itCfAnc t d), encGroup gs, encPairs ptsKey L]) (j := 0) (v := .nat q) rfl
  have dQQ3 := (Det.arith' (op := .mul) dq3 dq3 rfl).mono (c' := 5 * W + 20 + q * q)
    (by simp only [GI.Machine.BinOp.eval]; omega)
  have hRg := range_spec hrng (q * q)
  have hIB : (natList (List.range (q * q))).wt ≤ q * q * (2 * (q * q + 2) + 1) + 4 := by
    have := wt_list_le_of ((List.range (q * q)).map Val.nat) (c := q * q + 2) (by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hv
      have := wt_nat_le j
      rw [List.mem_range] at hj
      omega)
    simpa [natList] using this
  have hcall4 : EvalAll P [Val.list vs, R, encPts (itCfAnc t d), encGroup gs, encPairs ptsKey L]
      (.call rng itCfQQ) (fun w c => w = natList (List.range (q * q)) ∧
        c ≤ 5 * W + 20 + q * q + loopModK * (q * q + 1) *
          (q * q + 2 + q * q + (q * q * (2 * (q * q + 2) + 1) + 4) + 1) + w.wt + 1) :=
    EvalAll.call_funAll dQQ3 fun v ca hv => by
      obtain ⟨rfl, hca⟩ := hv
      refine hRg.mono fun w c hw => ⟨hw.1, ?_⟩
      obtain ⟨rfl, hc⟩ := hw
      have := wt_nat_le (q * q)
      have := Nat.mul_le_mul_left (loopModK * (q * q + 1))
        (show (Val.nat (q * q)).wt + q * q + (natList (List.range (q * q))).wt + 1 ≤
          q * q + 2 + q * q + (q * q * (2 * (q * q + 2) + 1) + 4) + 1 by omega)
      omega
  refine EvalAll.letE hcall4 fun w4 c4 h4 => ?_
  obtain ⟨rfl, hc4⟩ := h4
  -- step 5: the table
  have dq4 := Det.arg' (P := P) (vs := vs) (rest := [R, encPts (itCfAnc t d), encGroup gs,
    encPairs ptsKey L, natList (List.range (q * q))]) (j := 0) (v := .nat q) rfl
  have dxs := Det.get' (Det.var' (P := P) (env := [Val.list vs, R, encPts (itCfAnc t d),
    encGroup gs, encPairs ptsKey L, natList (List.range (q * q))]) (i := 1) rfl) (Det.nat 0)
    (v := encPts xs) rfl
  have dAn := Det.var' (P := P) (env := [Val.list vs, R, encPts (itCfAnc t d),
    encGroup gs, encPairs ptsKey L, natList (List.range (q * q))]) (i := 2)
    (v := encPts (itCfAnc t d)) rfl
  have dLv := Det.var' (P := P) (env := [Val.list vs, R, encPts (itCfAnc t d),
    encGroup gs, encPairs ptsKey L, natList (List.range (q * q))]) (i := 4)
    (v := encPairs ptsKey L) rfl
  have dids := Det.var' (P := P) (env := [Val.list vs, R, encPts (itCfAnc t d),
    encGroup gs, encPairs ptsKey L, natList (List.range (q * q))]) (i := 5)
    (v := natList (List.range (q * q))) rfl
  have dm := Det.mk2 (Det.mk4 dq4 dxs dAn dLv) dids
  have ectx : Val.list [.nat q, encPts xs, encPts (itCfAnc t d), encPairs ptsKey L] =
      itCfCtx q xs (itCfAnc t d) L := by
    rw [itCfCtx, itCf_encPts_natList, itCf_encPts_natList]
  rw [show Val.list [Val.list [.nat q, encPts xs, encPts (itCfAnc t d), encPairs ptsKey L],
      natList (List.range (q * q))] =
      Val.list [itCfCtx q xs (itCfAnc t d) L, encFun fun i : Fin (q ^ 2) => (i : ℕ)] by
    rw [ectx, itCf_ids_eq]] at dm
  have hTab := tabulate_spec hmp (c := itCfCtx q xs (itCfAnc t d) L)
    (fun i : Fin (q ^ 2) => itCf_cell_spec hfc han1 hpe han2 hpp hfnd xs (itCfAnc t d) L hL2 i.val
      (itCf_lt_sq i.isLt))
  have hval := itCf_table_eq hs t hd xs (fun b => Finset.mem_sort _) gs hgs L hLm
  refine (Det.call dm hTab).post fun c hc => ⟨hval, ?_⟩
  -- the cost
  have hq0 : 0 < q := by omega
  have hAl : (itCfAnc t d).length ≤ W := by
    have : (itCfAnc t d).length ≤ ℓ := by
      unfold itCfAnc ancList
      exact (List.length_take_le' _ _).trans (by simp)
    omega
  have hKw := itCf_wt_tab (m := q ^ 2) (N := 7 + W)
    (fun i => Val.nat (itCfCellN xs (itCfAnc t d) L ⟨i.val % q, Nat.mod_lt _ hq0⟩
      ⟨i.val / q, Nat.div_lt_of_lt_mul (itCf_lt_sq i.isLt)⟩))
    fun i => ⟨_, (itCfCellN_le _ _ _ _ _).trans (by omega), rfl⟩
  generalize (Val.list ((List.finRange (q ^ 2)).map
    (fun i => Val.nat (itCfCellN xs (itCfAnc t d) L ⟨i.val % q, Nat.mod_lt _ hq0⟩
      ⟨i.val / q, Nat.div_lt_of_lt_mul (itCf_lt_sq i.isLt)⟩)))).wt = KK at hc hKw
  have hqW : q * q ≤ W * W := Nat.mul_le_mul (by omega) (by omega)
  have hq2 : q ^ 2 = q * q := sq q
  have hqW2 : q ^ 2 ≤ W * W := by rw [hq2]; exact hqW
  have hKB : q ^ 2 * (2 * (7 + W) + 5) + 4 ≤ itCfColKB W := by
    unfold itCfColKB
    have := Nat.mul_le_mul_right (2 * (7 + W) + 5) hqW2
    have e : 2 * (7 + W) + 5 = 2 * W + 19 := by omega
    rw [e] at this ⊢
    omega
  have hKB2 : W * W * 19 + 4 ≤ itCfColKB W := by
    unfold itCfColKB
    have := Nat.mul_le_mul_left (W * W) (show 19 ≤ 2 * W + 19 by omega)
    omega
  -- step 1
  have wd := wt_nat_le d; have wd1 := wt_nat_le (d - 1)
  have hWa : (Val.list [Val.nat (d - 1), Val.list tv]).wt ≤ 4 * W + 8 := by
    have := wt_list2_le (Val.nat (d - 1)) (Val.list tv); omega
  have k1 := linTakeCost_mono hWa
  -- step 2
  have hX : (Val.list [encGroup hs, encPts (itCfAnc t d)]).wt ≤ 4 * W + 6 := by
    have := wt_list2_le (encGroup hs) (encPts (itCfAnc t d)); omega
  have k2 := (Prim.bound_le (pointwiseStabPrim hps) (le_trans (Val.size_le_wt _) hX))
  have k3 := Nat.mul_le_mul_left pstabK (Nat.pow_le_pow_left hX 9)
  have hW6 : 320 * (q + 1) ^ 6 ≤ 320 * W ^ 6 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6)
  -- step 3
  have hlen : (1 :: gs).length ≤ 320 * W ^ 6 := by
    have := length_lt_wt_list ((1 :: gs).map encPerm)
    rw [List.length_map] at this
    omega
  have hTB : TT ≤ itCfTB W := by
    rw [hTT]; unfold itCfTB
    have h2 : [t ⟨d - 1, hdl⟩, t ⟨d, hd⟩].length = 2 := rfl
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 12)
  -- step 4
  have hIB : q * q * (2 * (q * q + 2) + 1) + 4 ≤ itCfColIB W := by
    unfold itCfColIB
    have := Nat.mul_le_mul hqW (show 2 * (q * q + 2) + 1 ≤ 2 * (W * W + 2) + 1 by omega)
    omega
  have k4 := Nat.mul_le_mul (Nat.mul_le_mul_left loopModK (show q * q + 1 ≤ W * W + 1 by omega))
    (show q * q + 2 + q * q + (q * q * (2 * (q * q + 2) + 1) + 4) + 1 ≤
      2 * (W * W) + itCfColIB W + 3 by omega)
  -- step 5
  have ectx' : (Val.list [Val.nat q, encPts xs, encPts (itCfAnc t d), encPairs ptsKey L]).wt =
      (itCfCtx q xs (itCfAnc t d) L).wt := by rw [ectx]
  have wxs : (encPts xs).wt < R.wt := wt_le_wt_list (by simp)
  have hCB : (itCfCtx q xs (itCfAnc t d) L).wt ≤ itCfCB W RW := by
    rw [← ectx']
    have := wt_list4_le (Val.nat q) (encPts xs) (encPts (itCfAnc t d)) (encPairs ptsKey L)
    unfold itCfCB
    omega
  have hids : (encFun fun i : Fin (q ^ 2) => (i : ℕ)).wt ≤ itCfColIB W := by
    rw [← itCf_ids_eq]; omega
  have w2 := wt_list2_le (itCfCtx q xs (itCfAnc t d) L) (encFun fun i : Fin (q ^ 2) => (i : ℕ))
  have k5 := Nat.mul_le_mul hqW2 (itCfCellC_mono (show
    2 * (itCfCtx q xs (itCfAnc t d) L).wt + 2 * (q * q) + q + 20 ≤
      2 * itCfCB W RW + 2 * (W * W) + W + 20 by omega))
  have k6 := Nat.mul_le_mul (Nat.mul_le_mul_left mapK (show q ^ 2 + 1 ≤ W * W + 1 by omega))
    (show (Val.list [itCfCtx q xs (itCfAnc t d) L, encFun fun i : Fin (q ^ 2) => (i : ℕ)]).wt +
        KK + 1 ≤
      2 * (itCfCB W RW + itCfColIB W) + 6 + itCfColKB W + 1 by omega)
  have hTW : 320 * W ^ 6 ≤ itCfTB W := by
    unfold itCfTB
    have : 320 * W ^ 6 ≤ (320 * W ^ 6 + W + W * W + 22) ^ 12 :=
      le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
    exact this.trans (Nat.le_mul_of_pos_left _ (by unfold tupK; norm_num))
  unfold itCfColMC
  simp only [GI.Machine.BinOp.eval] at hc1
  generalize (pointwiseStabPrim hps).bound (Val.list [encGroup hs, encPts (itCfAnc t d)]) = B1 at *
  generalize pstabK * (Val.list [encGroup hs, encPts (itCfAnc t d)]).wt ^ 9 = B2 at *
  omega

/-! ### The program `col` -/

theorem itCfFrC_mono (hps : PointwiseStab) {a b : ℕ} (h : a ≤ b) : itCfFrC hps a ≤ itCfFrC hps b := by
  unfold itCfFrC
  have h1 := itDomC_mono h
  have h2 := itCfDegB_mono hps (show 2 * (a + itDomC a) + 6 ≤ 2 * (b + itDomC b) + 6 by omega)
  omega

/-- The cost bound of `col` on an input of weight `W`. -/
noncomputable def itCfColC (hps : PointwiseStab) (W : ℕ) : ℕ :=
  4 * itCfFrC hps W + 3 * itCfColMC hps W (itCfFrC hps W) +
    3 * (loopModK * (W * W + 1) * (8 * (W * W) + 19)) + 100 * (W * W) + 100 * W + 1000

/-- **The orbital coloring of Case 2b, as a program.** On `[q, ⟨H⟩, ⟨t⟩]` the program `col`
returns the table of `orbColOut H t`. -/
theorem it_cfCol_spec (hps : PointwiseStab) {P : Program}
    {f fr dom orb rng0 fd pd cnt deg jps rep tk ps tor rng mp fc an1 an2 fnd pe pp : ℕ}
    (hf : P.funs[f]? = some (itCfColF fr rep tk ps tor rng mp))
    (hfr : P.funs[fr]? = some (itCfFrF dom deg))
    (hdom : P.funs[dom]? = some (itDomF orb rng0 fd)) (horb : P.HasAt orb (orbitFuns orb))
    (hrng0 : P.HasAt rng0 (rangeFuns rng0)) (hfd : P.HasAt fd (filterFuns fd pd))
    (hpd : P.funs[pd]? = some (acpDomF cnt)) (hcnt : P.HasAt cnt (countFuns cnt))
    (hdeg : P.HasAt deg (itCfDegFuns deg jps)) (hj : P.prims[jps]? = some (pointwiseStabPrim hps))
    (hrep : P.HasAt rep (replicateFuns rep))
    (htk : P.HasAt tk (linTakeFuns tk)) (hpsF : P.HasAt ps (pstabFuns ps jps))
    (hto : P.HasAt tor (tupOrbFuns tor))
    (hrng : P.HasAt rng (rangeFuns rng)) (hmp : P.HasAt mp (mapFuns mp fc))
    (hfc : P.funs[fc]? = some (itCfCellF an1 an2 fnd)) (han1 : P.HasAt an1 (anyFuns an1 pe))
    (hpe : P.funs[pe]? = some itCfEqP) (han2 : P.HasAt an2 (anyFuns an2 pp))
    (hpp : P.funs[pp]? = some itCfPairP) (hfnd : P.HasAt fnd (findFuns fnd pe)) (hs : List (Perm (Fin q))) (t : Fin ℓ → Fin q) :
    FunAll P f (itCfColIn hs t) fun w cost =>
      w = encKColoring (orbColOut (gens hs) t) ∧ cost ≤ itCfColC hps (itCfColIn hs t).wt := by
  set d := transDeg (gens hs) (domSet (gens hs)) with hdd
  set xs := (domSet (gens hs)).sort with hxs
  set tv : List Val := ((List.finRange ℓ).map fun i => (t i : ℕ)).map Val.nat with htv
  set vs : List Val := [.nat q, encGroup hs, .list tv] with hvs
  have ev : itCfColIn hs t = .list vs := rfl
  rw [ev]
  set W := (Val.list vs).wt with hW
  have wg : (encGroup hs).wt < W := wt_le_wt_list (by simp [hvs])
  have wq : (Val.nat q).wt < W := wt_le_wt_list (by simp [hvs])
  have wt' : (Val.list tv).wt < W := wt_le_wt_list (by simp [hvs])
  have hq1 : q + 1 ≤ (encGroup hs).wt := by have := S_le_wt_encGroup hs; nlinarith
  have hltv : tv.length = ℓ := by simp [htv]
  have hlW : ℓ < W := by have := length_lt_wt_list tv; omega
  have hdq : d ≤ q := by
    have h1 := (transDeg_spec (gens hs) (domSet (gens hs))).2
    have h2 := Finset.card_le_univ (domSet (gens hs))
    rw [Fintype.card_fin] at h2
    omega
  have hF := it_cfFr_spec hps hfr hdom horb hrng0 hfd hpd hcnt hdeg hj hs
  have hFm := itCfFrC_mono hps wg.le
  have hRw : (Val.list [encPts xs, .nat d]).wt ≤ itCfFrC hps W := (hF.wt_lt.trans_le hFm).le
  have dF := Det.call (Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl) hF
  refine FunAll.intro hf (EvalAll.letE dF fun w1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  set R : Val := .list [encPts xs, .nat d] with hRd
  have dE : Det P [Val.list vs, R] itCfDE (.nat d) _ :=
    Det.get' (Det.var' (P := P) (env := [Val.list vs, R]) (i := 1) rfl) (Det.nat 1) rfl
  have dc := Det.arith' (op := .sub) (Det.length (Det.arg' (P := P) (vs := vs) (rest := [R])
    (j := 2) (v := .list tv) rfl)) dE rfl
  refine EvalAll.ite dc (fun _ _ h => ⟨_, h.1⟩) fun x cc h => ?_
  obtain ⟨hx, hcc⟩ := h
  cases hx
  have wd := wt_nat_le d
  have hRwt : R.wt ≤ itCfFrC hps W := hRw
  by_cases hd : d < ℓ
  · rw [if_neg (by simp only [GI.Machine.BinOp.eval]; omega)]
    refine (itCf_colMain_spec hps htk hpsF hj hto hrng hmp hfc han1 hpe han2 hpp hfnd hs t hd
      hRwt).wt_lt.mono fun w c hw => ?_
    obtain ⟨⟨rfl, hcw⟩, hwc⟩ := hw
    refine ⟨rfl, ?_⟩
    rw [ev] at hcw
    have eW : itCfColMC hps (Val.list vs).wt (itCfFrC hps W) = itCfColMC hps W (itCfFrC hps W) := rfl
    have eR : (Val.list [encPts xs, .nat d]).wt = R.wt := rfl
    unfold itCfColC
    simp only [GI.Machine.BinOp.eval] at hcc
    have := hltv
    omega
  · rw [if_pos (by simp only [GI.Machine.BinOp.eval]; omega)]
    have dq0 := Det.arg' (P := P) (vs := vs) (rest := [R]) (j := 0) (v := .nat q) rfl
    have dm := Det.mk2 (Det.arith' (op := .mul) dq0 dq0 rfl) (Det.nat (P := P)
      (env := [Val.list vs, R]) 0)
    have hRp := replicate_spec hrep (q * q) (.nat 0)
    have hz : orbColOut (gens hs) t = fun _ => 0 := by
      unfold orbColOut orbColAt
      rw [dif_neg hd]
    refine EvalAll.call_funAll dm fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine hRp.mono fun w c hw => ?_
    obtain ⟨rfl, hcw⟩ := hw
    refine ⟨by rw [hz, itCf_encK_zero], ?_⟩
    have hrw : (Val.list (List.replicate (q * q) (Val.nat 0))).wt ≤ q * q * 5 + 4 := by
      have := wt_list_le_of (List.replicate (q * q) (Val.nat 0)) (c := 2) (by
        intro v hv; rw [List.eq_of_mem_replicate hv]; exact wt_nat_le 0)
      simpa using this
    have hqW : q * q ≤ W * W := Nat.mul_le_mul (by omega) (by omega)
    have w2 := wt_list2_le (Val.nat (q * q)) (Val.nat 0)
    have := wt_nat_le (q * q); have := wt_nat_le 0
    have k := Nat.mul_le_mul (Nat.mul_le_mul_left loopModK (show q * q + 1 ≤ W * W + 1 by omega))
      (show (Val.list [Val.nat (q * q), Val.nat 0]).wt + q * q +
        (Val.list (List.replicate (q * q) (Val.nat 0))).wt + 1 ≤ 8 * (W * W) + 19 by omega)
    have eR : (Val.list [encPts xs, .nat d]).wt = R.wt := rfl
    unfold itCfColC
    simp only [GI.Machine.BinOp.eval] at hcc hca ⊢
    omega

end GI.Impl
