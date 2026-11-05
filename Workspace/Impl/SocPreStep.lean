module

public import Workspace.Impl.SocPreScan

@[expose] public section

/-!
# One outer round of the socle preimage program

Given loop context `c_rd = [encGroup hs, encGroup rs, socCsVal Ws]` (`H = gens hs`, `R = gens rs`)
and round accumulator `acc = [encGroup cs, encGroup es]` (`C = gens cs`, `E = gens es`) with
`cs.length ≤ n²`, `es.length ≤ n²`, and `SocRoundInv H R i C E`:

1. `socJoinCutF` on `[encGroup es, encGroup is]` appends the generator lists of `es` and `is`, cuts
   the join to at most `n²` generators via `normalizedIntersectionPrim` (`jni`), and wraps it into
   `encGroup es'` (`es'.length ≤ n²`, `gens es' = gens es ⊔ gens is`) via `mkGroupFuns` (`mg`).
2. `socRoundBody` on `[c_rd, .nat i, [encGroup cs, encGroup es]]`:
   - tests `decide (gens cs ≤ gens rs)` via `leFuns` (`le`);
   - if `gens cs ≤ gens rs`, returns `arg 2` unchanged;
   - otherwise:
     * calls `socScanBody` (`sc`) on `[encGroup rs, socCsVal Ws, encGroup cs]` to obtain
       `encGroup is` (`I = socTerm R (Ws.map gens) k ⊓ C`),
     * calls `socJoinCutF` (`jc`) on `[encGroup es, encGroup is]` to obtain `encGroup es'`
       (`gens es' = E ⊔ I`, `es'.length ≤ n²`),
     * calls `gmpFactorKernelFuns` (`fk`) on `[encGroup hs, encGroup is, encGroup rs]` to obtain
       generators of `Z = {h ∈ H | ∀ u ∈ I, [h, u] ∈ R}`,
     * intersects `C ⊓ Z` via `jni` and `mg` to obtain `encGroup cs'`
       (`gens cs' = C ⊓ Z`, `cs'.length ≤ n²`),
     * returns `[encGroup cs', encGroup es']`.
3. `socRound_spec` proves that `socRoundBody` preserves `SocRoundValInv` from `i` to `i + 1`.

Only **NormalizedIntersection** (`jni`), **Membership** (`jm`), and **Preimage** (`jpre`) are used.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.RadicalSocle GI.RadicalFreeOrder Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### Joining two `encGroup` values and cutting to `≤ n²` generators (`socJoinCutF`) -/

/-- `socJoinCutF` on `[encGroup es, encGroup is]`:
1. `.var 1 = encGroup (es ++ (1 :: is))` via `mg + 4` (`appendFuns`)
2. `.var 2 = v2` (`GensVal n v2 (gens es ⊔ gens is)`) via `jni` on `[.var 1, .var 1]`
3. returns `encGroup es'` (`es'.length ≤ n²`, `gens es' = gens es ⊔ gens is`) via `mg`. -/
def socJoinCutF (mg jni : ℕ) : Expr :=
  .letE (mk2 (.get (arg 0) (.nat 0))
    (.call (mg + 4) (mk2 (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 1)))))
  (.letE (.prim jni (mk2 (.var 1) (.var 1)))
    (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 2))))

/-- Cost bound of `socJoinCutF`. -/
def socJoinCutCost (pni : Prim) (n : ℕ) : ℕ :=
  pni.boundSize (10 ^ 4 * (n + 1) ^ 6) + 10 ^ 8 * (n + 1) ^ 9

theorem soc_gens_append_one_cons (es is : List (Perm (Fin n))) :
    gens (es ++ (1 :: is)) = gens es ⊔ gens is := by
  rw [outb_gens_append]
  congr 1
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr fun x hx => ?_
    simp only [Set.mem_ofPred_eq, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact (gens is).one_mem
    · exact Subgroup.subset_closure hx
  · exact Subgroup.closure_mono fun x hx => List.mem_cons_of_mem _ hx

/-- **Specification of `socJoinCutF`**: on `[encGroup es, encGroup is]` with `es.length ≤ n²` and
`is.length ≤ n²`, returns `encGroup es'` with `es'.length ≤ n²` and `gens es' = gens es ⊔ gens is`. -/
theorem socJoinCut_spec {hni : NormalizedIntersection} {P : Program} {jc mg jni : ℕ}
    (hjc : P.funs[jc]? = some (socJoinCutF mg jni))
    (hmg : P.HasAt mg (mkGroupFuns mg))
    (hjni : P.prims[jni]? = some (normalizedIntersectionPrim hni))
    {es is : List (Perm (Fin n))} (hel : es.length ≤ n ^ 2) (hil : is.length ≤ n ^ 2) :
    FunAll P jc (.list [encGroup es, encGroup is]) (fun w cost =>
      ∃ es' : List (Perm (Fin n)), w = encGroup es' ∧ es'.length ≤ n ^ 2 ∧
        gens es' = gens es ⊔ gens is ∧
        cost ≤ socJoinCutCost (normalizedIntersectionPrim hni) n) := by
  have happ : P.HasAt (mg + 4) (appendFuns (mg + 4)) := by
    simp only [mkGroupFuns] at hmg
    simpa [rangeFuns, loopFuns, Nat.add_assoc] using hmg.right
  set in_v := Val.list [encGroup es, encGroup is] with hin_v
  set u := es ++ (1 :: is) with hudef
  have hEw := wt_encGroup_sq hel
  have hIw := wt_encGroup_sq hil
  have hE1w : (Val.list ((1 :: es).map encPerm)).wt ≤ 160 * (n + 1) ^ 6 :=
    (wt_le_wt_list (vs := [.nat n, _]) (by simp)).le.trans hEw
  have hI1w : (Val.list ((1 :: is).map encPerm)).wt ≤ 160 * (n + 1) ^ 6 :=
    (wt_le_wt_list (vs := [.nat n, _]) (by simp)).le.trans hIw
  have hu1w_0 := soc_wt_append ((1 :: es).map encPerm) ((1 :: is).map encPerm)
  have hmap_eq : ((1 :: es).map encPerm) ++ (1 :: is).map encPerm = (1 :: u).map encPerm := by
    simp [hudef]
  rw [hmap_eq] at hu1w_0
  have hnw := wt_nat_le n
  have hn16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hn26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hn68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hn89 : (n + 1) ^ 8 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hn69 : (n + 1) ^ 6 ≤ (n + 1) ^ 9 := hn68.trans hn89
  have hn_le : n ≤ (n + 1) ^ 6 := (Nat.le_succ n).trans (Nat.le_self_pow (by decide) _)
  have huw_0 := wt_list2_le (.nat n) (.list ((1 :: u).map encPerm))
  have e_u : (Val.list [.nat n, .list ((1 :: u).map encPerm)]).wt = (encGroup u).wt := rfl
  have huw : (encGroup u).wt ≤ 2000 * (n + 1) ^ 6 := by omega
  have hinw : in_v.wt ≤ 2 * ((encGroup es).wt + (encGroup is).wt) + 6 :=
    wt_list2_le (encGroup es) (encGroup is)
  -- step 1: form `encGroup u`
  have dG : Det P [in_v]
      (mk2 (.get (arg 0) (.nat 0))
        (.call (mg + 4) (mk2 (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 1)))))
      (encGroup u) (2 * 10 ^ 7 * (n + 1) ^ 8) := by
    have d0 := Det.arg' (P := P) (vs := [encGroup es, encGroup is]) (rest := [])
      (j := 0) (v := encGroup es) rfl
    have d1 := Det.arg' (P := P) (vs := [encGroup es, encGroup is]) (rest := [])
      (j := 1) (v := encGroup is) rfl
    rw [← hin_v] at d0 d1
    have dn := Det.get' d0 (Det.nat 0) (v := .nat n) rfl
    have de1 := Det.get' d0 (Det.nat 1) (v := .list ((1 :: es).map encPerm)) rfl
    have di1 := Det.get' d1 (Det.nat 1) (v := .list ((1 :: is).map encPerm)) rfl
    have hap0 := append_spec happ ((1 :: es).map encPerm) ((1 :: is).map encPerm)
    rw [hmap_eq] at hap0
    have hapd : FunDet P (mg + 4)
        (.list [.list ((1 :: es).map encPerm), .list ((1 :: is).map encPerm)])
        (.list ((1 :: u).map encPerm))
        (loopModK * ((1 :: is).length + 1) *
          ((Val.list [.list ((1 :: es).map encPerm), .list ((1 :: is).map encPerm)]).wt +
            (1 :: is).length + (Val.list ((1 :: u).map encPerm)).wt + 1)) :=
      FunAll.mono hap0 fun w c hw => by
        obtain ⟨rfl, hc⟩ := hw
        exact ⟨rfl, by simpa using hc⟩
    have dcall := Det.call (Det.mk2 de1 di1) hapd
    have dmk := Det.mk2 dn dcall
    refine dmk.mono ?_
    have hil2 : (1 :: is).length + 1 ≤ 2 * (n + 1) ^ 2 := by
      simp only [List.length_cons]
      have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      omega
    have hil6 : (1 :: is).length ≤ 2 * (n + 1) ^ 6 :=
      (Nat.le_succ _).trans (hil2.trans (Nat.mul_le_mul_left _ hn26))
    have hw_pair := wt_list2_le (.list ((1 :: es).map encPerm)) (.list ((1 :: is).map encPerm))
    have hL : loopModK * ((1 :: is).length + 1) *
        ((Val.list [.list ((1 :: es).map encPerm), .list ((1 :: is).map encPerm)]).wt +
          (1 :: is).length + (Val.list ((1 :: u).map encPerm)).wt + 1) ≤
        10 ^ 7 * (n + 1) ^ 8 := by
      calc loopModK * ((1 :: is).length + 1) *
          ((Val.list [.list ((1 :: es).map encPerm), .list ((1 :: is).map encPerm)]).wt +
            (1 :: is).length + (Val.list ((1 :: u).map encPerm)).wt + 1) ≤
          loopModK * (2 * (n + 1) ^ 2) * (4000 * (n + 1) ^ 6) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hil2) (by
              clear d0 d1 dn de1 di1 hap0 hapd dcall dmk
              clear_value in_v u
              omega)
        _ = 8 * 10 ^ 6 * (n + 1) ^ 8 := by simp only [loopModK]; ring
        _ ≤ 10 ^ 7 * (n + 1) ^ 8 := Nat.mul_le_mul_right _ (by norm_num)
    clear d0 d1 dn de1 di1 hap0 hapd dcall dmk
    clear_value in_v u
    omega
  -- step 2: call `jni` on `[encGroup u, encGroup u]`
  refine FunAll.intro hjc (EvalAll.letE dG fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  have dv1 := Det.var' (P := P) (env := [in_v, encGroup u]) (i := 1) (v := encGroup u) rfl
  have hnorm : GI.Lang.Normalizes (gens u) (gens u) := fun x hx y hy =>
    (gens u).mul_mem ((gens u).mul_mem hx hy) ((gens u).inv_mem hx)
  have hni_wt := wt_list2_le (encGroup u) (encGroup u)
  have hni_sz : (Val.list [encGroup u, encGroup u]).size ≤ 10 ^ 4 * (n + 1) ^ 6 :=
    (Val.size_le_wt _).trans (by omega)
  refine EvalAll.letE
    (normalizedIntersection_call hni hjni (Det.mk2 dv1 dv1) ⟨u, rfl, rfl⟩ ⟨u, rfl, rfl⟩ hnorm)
    fun v2 c2 h2 => ?_
  obtain ⟨hv2, hc2⟩ := h2
  have hb2 := (normalizedIntersectionPrim hni).bound_le hni_sz
  -- step 3: wrap `v2` via `mg`
  have d0' := Det.arg' (P := P) (vs := [encGroup es, encGroup is]) (rest := [encGroup u, v2])
    (j := 0) (v := encGroup es) rfl
  have dn' := Det.get' d0' (Det.nat 0) (v := .nat n) rfl
  rw [← hin_v] at dn'
  obtain ⟨es', hel', heg', d3, hew'⟩ :=
    outb_mk_det hmg dn' (Det.var' (P := P) (env := [in_v, encGroup u, v2]) (i := 2) (v := v2) rfl) hv2
  refine d3.post fun c3 hc3 => ⟨es', rfl, hel', ?_, ?_⟩
  · rw [heg', inf_idem, soc_gens_append_one_cons]
  · have w2 := GensVal.wt_le hv2
    have hl_mk := wt_list2_le (.nat n) v2
    have hmk_9 : 8 * mkGroupK * (n + 1) ^ 9 ≤ 10 ^ 6 * (n + 1) ^ 9 := by
      simp only [mkGroupK]; omega
    unfold socJoinCutCost
    clear d3 dn' d0' dv1 dG
    clear_value in_v u
    omega

/-! ### Expressions for the outer round `socRoundBody` -/

/-- `encGroup hs` in the outer round context `[[hv, rv, ws], i, acc]`. -/
def socRdHvE : Expr := .get (arg 0) (.nat 0)
/-- `encGroup rs` in the outer round context `[[hv, rv, ws], i, acc]`. -/
def socRdRvE : Expr := .get (arg 0) (.nat 1)
/-- `socCsVal Ws` in the outer round context `[[hv, rv, ws], i, acc]`. -/
def socRdWsE : Expr := .get (arg 0) (.nat 2)
/-- The degree `n`, read off `encGroup hs`. -/
def socRdNE : Expr := .get socRdHvE (.nat 0)
/-- `encGroup cs` in the outer round accumulator `acc = [cv, ev]`. -/
def socRdCvE : Expr := .get (arg 2) (.nat 0)
/-- `encGroup es` in the outer round accumulator `acc = [cv, ev]`. -/
def socRdEvE : Expr := .get (arg 2) (.nat 1)

/-- **One outer round of the socle preimage program** on
`[[encGroup hs, encGroup rs, socCsVal Ws], .nat i, [encGroup cs, encGroup es]]`:
1. `.var 1 = .nat (if decide (gens cs ≤ gens rs) then 1 else 0)` via `le`
2. If `.var 1 ≠ 0`, returns `arg 2` (`[encGroup cs, encGroup es]`).
3. Otherwise:
   - `.var 2 = encGroup is` via `sc` (`socScanBody`) on `[encGroup rs, socCsVal Ws, encGroup cs]`
   - `.var 3 = encGroup es'` via `jc` (`socJoinCutF`) on `[encGroup es, .var 2]`
   - `.var 4 = v4` (`GensVal n v4 Z`) via `fk` (`gmpFactorKernelFuns`) on `[encGroup hs, .var 2, encGroup rs]`
   - `.var 5 = v5` (`GensVal n v5 (gens cs ⊓ Z)`) via `jni` on `[encGroup cs, mg [n, .var 4]]`
   - `.var 6 = encGroup cs'` via `mg` on `[n, .var 5]`
   - returns `[.var 6, .var 3]`. -/
def socRoundBody (sc jc mg le jni fk : ℕ) : Expr :=
  .letE (.call le (mk2 socRdRvE socRdCvE))
  (.ite (.var 1) (arg 2)
    (.letE (.call sc (mk3 socRdRvE socRdWsE socRdCvE))
    (.letE (.call jc (mk2 socRdEvE (.var 2)))
    (.letE (.call fk (mk3 socRdHvE (.var 2) socRdRvE))
    (.letE (.prim jni (mk2 socRdCvE (.call mg (mk2 socRdNE (.var 4)))))
    (.letE (.call mg (mk2 socRdNE (.var 5)))
      (mk2 (.var 6) (.var 3))))))))

/-! ### Reading the outer round context -/

section ReadRound

variable {P : Program} {hv rv ws acc : Val} {i : ℕ} {rest : List Val}

theorem socRd_d_hv : Det P (.list [.list [hv, rv, ws], .nat i, acc] :: rest) socRdHvE hv
    (4 * socW hv rv ws acc i + 10) := socScan_d_rv

theorem socRd_d_rv : Det P (.list [.list [hv, rv, ws], .nat i, acc] :: rest) socRdRvE rv
    (4 * socW hv rv ws acc i + 10) := socScan_d_ws

theorem socRd_d_ws : Det P (.list [.list [hv, rv, ws], .nat i, acc] :: rest) socRdWsE ws
    (4 * socW hv rv ws acc i + 11) := socScan_d_cv

theorem socRd_d_acc : Det P (.list [.list [hv, rv, ws], .nat i, acc] :: rest) (arg 2) acc
    (3 * socW hv rv ws acc i + 10) := socScan_d_acc

theorem socRd_d_n {hs : List (Perm (Fin n))} (hh : hv = encGroup hs) :
    Det P (.list [.list [hv, rv, ws], .nat i, acc] :: rest) socRdNE (.nat n)
      (6 * socW hv rv ws acc i + 20) := socScan_d_n hh

theorem socRd_d_cv {cv ev : Val} (ha : acc = .list [cv, ev]) :
    Det P (.list [.list [hv, rv, ws], .nat i, acc] :: rest) socRdCvE cv
      (5 * socW hv rv ws acc i + 20) := by
  have hw := soc_wt_facts hv rv ws acc i
  have hlt : cv.wt < acc.wt := by
    rw [ha]; exact wt_le_wt_list (vs := [cv, ev]) (by simp)
  have da : Det P (.list [.list [hv, rv, ws], .nat i, acc] :: rest) (arg 2) acc
      (3 * socW hv rv ws acc i + 10) := socRd_d_acc
  rw [ha] at da hlt hw ⊢
  exact (Det.get' da (Det.nat 0) (v := cv) rfl).mono (by omega)

theorem socRd_d_ev {cv ev : Val} (ha : acc = .list [cv, ev]) :
    Det P (.list [.list [hv, rv, ws], .nat i, acc] :: rest) socRdEvE ev
      (5 * socW hv rv ws acc i + 20) := by
  have hw := soc_wt_facts hv rv ws acc i
  have hlt : ev.wt < acc.wt := by
    rw [ha]; exact wt_le_wt_list (vs := [cv, ev]) (by simp)
  have da : Det P (.list [.list [hv, rv, ws], .nat i, acc] :: rest) (arg 2) acc
      (3 * socW hv rv ws acc i + 10) := socRd_d_acc
  rw [ha] at da hlt hw ⊢
  exact (Det.get' da (Det.nat 1) (v := ev) rfl).mono (by omega)

end ReadRound

/-! ### Invariant and cost of the outer round -/

/-- Value-level invariant of the outer round loop after `i` rounds:
`acc = .list [encGroup cs, encGroup es]` with `cs.length ≤ n²`, `es.length ≤ n²`, and
`SocRoundInv H R i (gens cs) (gens es)`. -/
def SocRoundValInv (H R : Subgroup (Perm (Fin n))) [(R.subgroupOf H).Normal]
    (i : ℕ) (acc : Val) : Prop :=
  ∃ cs es : List (Perm (Fin n)), acc = .list [encGroup cs, encGroup es] ∧
    cs.length ≤ n ^ 2 ∧ es.length ≤ n ^ 2 ∧
    SocRoundInv H R i (gens cs) (gens es)

theorem soc_round_val_wt {H R : Subgroup (Perm (Fin n))} [(R.subgroupOf H).Normal]
    {i : ℕ} {acc : Val} (h : SocRoundValInv H R i acc) :
    acc.wt ≤ 1500 * (n + 1) ^ 6 := by
  obtain ⟨cs, es, rfl, hcl, hel, -⟩ := h
  have hcw := wt_encGroup_sq hcl
  have hew := wt_encGroup_sq hel
  have h2 := wt_list2_le (encGroup cs) (encGroup es)
  have hn16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  omega

/-- Where the outer round function and its dependencies sit in `P`. -/
structure SocRoundAt (P : Program) (rd sc it_sc sc_st jc mg le fk jni jm jpre : ℕ)
    (hni : NormalizedIntersection) (hmem : Membership) (hpre : Preimage) : Prop where
  round : P.funs[rd]? = some (socRoundBody sc jc mg le jni fk)
  scan : SocScanAt P sc it_sc sc_st mg le jni jm hni hmem
  joinCut : P.funs[jc]? = some (socJoinCutF mg jni)
  fk : GmpFactorKernelAt P hmem hpre fk jm jpre

/-- Cost bound of one outer round on an argument of weight `W`, chain length `L = Ws.length`,
and index bound `q` (`[soclePreimage H R : R] ≤ q`). -/
def socRoundCost (pni pm pfk : Prim) (W L q : ℕ) : ℕ :=
  socScanCost pni pm (10 * W + 10) L +
    socJoinCutCost pni W +
    pfk.boundSize (1000 * (W + q + 1) ^ 6) +
    pni.boundSize (1000 * (W + q + 1) ^ 6) +
    1000 * (W + q + 1) ^ 6 * pm.boundSize (1000 * (W + q + 1) ^ 6) +
    10 ^ 9 * (1000 * (W + q + 1) ^ 6) ^ 3

theorem socJoinCutCost_mono (pni : Prim) {n n' : ℕ} (h : n ≤ n') :
    socJoinCutCost pni n ≤ socJoinCutCost pni n' := by
  unfold socJoinCutCost
  have h1 : 10 ^ 4 * (n + 1) ^ 6 ≤ 10 ^ 4 * (n' + 1) ^ 6 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 6)
  have h2 := soc_boundSize_mono pni h1
  have h3 : 10 ^ 8 * (n + 1) ^ 9 ≤ 10 ^ 8 * (n' + 1) ^ 9 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 9)
  omega

theorem socRoundCost_mono (pni pm pfk : Prim) {W W' L L' q q' : ℕ}
    (hW : W ≤ W') (hL : L ≤ L') (hq : q ≤ q') :
    socRoundCost pni pm pfk W L q ≤ socRoundCost pni pm pfk W' L' q' := by
  unfold socRoundCost
  have hWq : W + q + 1 ≤ W' + q' + 1 := by omega
  have hY : 1000 * (W + q + 1) ^ 6 ≤ 1000 * (W' + q' + 1) ^ 6 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hWq 6)
  have h1 := socScanCost_mono pni pm (show 10 * W + 10 ≤ 10 * W' + 10 by omega) hL
  have h2 := socJoinCutCost_mono pni hW
  have h3 := soc_boundSize_mono pfk hY
  have h4 := soc_boundSize_mono pni hY
  have h5 := Nat.mul_le_mul hY (soc_boundSize_mono pm hY)
  have h6 := Nat.pow_le_pow_left hY 3
  omega

set_option maxHeartbeats 800000 in
open Classical in
/-- **One outer round** `socRoundBody` preserves `SocRoundValInv` from `i` to `i + 1`. -/
theorem socRound_spec {hni : NormalizedIntersection} {hmem : Membership} {hpre : Preimage}
    {P : Program} {rd sc it_sc sc_st jc mg le fk jni jm jpre : ℕ}
    (hP : SocRoundAt P rd sc it_sc sc_st jc mg le fk jni jm jpre hni hmem hpre)
    {hs rs : List (Perm (Fin n))} {Ws : List (List (Perm (Fin n)))}
    (hRH : gens rs ≤ gens hs) (hnR : GI.Multicoset.Normalizes (gens hs) (gens rs))
    [((gens rs).subgroupOf (gens hs)).Normal]
    (hrf : ∀ N : Subgroup ((gens hs) ⧸ (gens rs).subgroupOf (gens hs)),
      N.Normal → Group.IsSolvable N → N = ⊥)
    (hchain : SocChain (gens hs) (gens rs) (Ws.map gens))
    {q : ℕ} (hq : ((gens rs).subgroupOf (soclePreimage (gens hs) (gens rs))).index ≤ q)
    {i : ℕ} {acc : Val}
    (hinv : SocRoundValInv (gens hs) (gens rs) i acc) :
    FunAll P rd (.list [.list [encGroup hs, encGroup rs, socCsVal Ws], .nat i, acc])
      (fun w c => SocRoundValInv (gens hs) (gens rs) (i + 1) w ∧
        c ≤ socRoundCost (normalizedIntersectionPrim hni) (membershipPrim hmem)
          (gmpFactorKernelPrim hmem hpre)
          (socW (encGroup hs) (encGroup rs) (socCsVal Ws) acc i) Ws.length q) := by
  obtain ⟨cs, es, rfl, hcl, hel, hrinv⟩ := hinv
  set acc_v := Val.list [encGroup cs, encGroup es] with hacc_v
  have hw := soc_wt_facts (encGroup hs) (encGroup rs) (socCsVal Ws) acc_v i
  set W := socW (encGroup hs) (encGroup rs) (socCsVal Ws) acc_v i with hWdef
  set Y := 1000 * (W + q + 1) ^ 6 with hY
  have hcw_lt : (encGroup cs).wt < acc_v.wt := wt_le_wt_list (vs := [encGroup cs, encGroup es]) (by simp)
  have hew_lt : (encGroup es).wt < acc_v.wt := wt_le_wt_list (vs := [encGroup cs, encGroup es]) (by simp)
  have hnW : n + 1 ≤ W := by
    have := S_le_wt_encGroup hs
    have : n + 1 ≤ (hs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hn_le_W : n ≤ W := by omega
  have hW6 : W + q + 1 ≤ (W + q + 1) ^ 6 := Nat.le_self_pow (by decide) _
  have hW2 : (W + 1) ^ 2 ≤ (W + q + 1) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have hn6 : (n + 1) ^ 6 ≤ (W + q + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hn9 : 8 * mkGroupK * (n + 1) ^ 9 ≤ Y ^ 2 := by
    have : (n + 1) ^ 9 ≤ (W + q + 1) ^ 12 :=
      (Nat.pow_le_pow_left (show n + 1 ≤ W + q + 1 by omega) 9).trans
        (Nat.pow_le_pow_right (by omega) (by decide))
    have e : Y ^ 2 = 1000000 * (W + q + 1) ^ 12 := by rw [hY]; ring
    simp only [mkGroupK]; omega
  have hY1 : Y ≤ Y ^ 2 := Nat.le_self_pow (by decide) _
  have hY2 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  -- step 1: `.var 1 = decide (gens cs ≤ gens rs)` via `le_spec`
  have drv := socRd_d_rv (P := P) (hv := encGroup hs) (rv := encGroup rs) (ws := socCsVal Ws)
    (acc := acc_v) (i := i) (rest := [])
  have dcv := socRd_d_cv (P := P) (hv := encGroup hs) (rv := encGroup rs) (ws := socCsVal Ws)
    (acc := acc_v) (i := i) (rest := []) rfl
  have hles := le_spec hmem hP.scan.le hP.scan.mem
    (⟨rs, rfl, rfl⟩ : GroupVal n (encGroup rs) (gens rs)) cs
  have d1 := Det.call (Det.mk2 drv dcv) hles
  set b := decide (gens cs ≤ gens rs) with hbdef
  refine FunAll.intro hP.round (EvalAll.letE d1 fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  -- Bounds for `le` call
  have hlarg := wt_list2_le (encGroup rs) (encGroup cs)
  have hmarg := wt_list2_le (encGroup rs) (encPerm (1 : Perm (Fin n)))
  have hn2 : (n + 1) ^ 2 ≤ (W + q + 1) ^ 6 :=
    (Nat.pow_le_pow_left (show n + 1 ≤ W + 1 by omega) 2).trans hW2
  have hp1 : (encPerm (1 : Perm (Fin n))).wt ≤ 4 * (W + q + 1) ^ 6 :=
    (wt_encPerm_le (1 : Perm (Fin n))).trans (Nat.mul_le_mul_left _ hn2)
  have hms : (Val.list [encGroup rs, encPerm (1 : Perm (Fin n))]).size ≤ Y :=
    (Val.size_le_wt _).trans (by omega)
  have hbm := (membershipPrim hmem).bound_le hms
  have hX : (Val.list [encGroup rs, encGroup cs]).wt ≤ Y := by omega
  have hX3 : (Val.list [encGroup rs, encGroup cs]).wt ^ 3 ≤ Y ^ 3 :=
    Nat.pow_le_pow_left hX 3
  have hXm : (Val.list [encGroup rs, encGroup cs]).wt *
      (membershipPrim hmem).bound (.list [encGroup rs, encPerm (1 : Perm (Fin n))]) ≤
      Y * (membershipPrim hmem).boundSize Y := Nat.mul_le_mul hX hbm
  have hw_b : (boolVal b).wt ≤ 3 := wt_boolVal_le b
  simp only [← hWdef] at hc1
  -- Branch on `b = decide (gens cs ≤ gens rs)`
  by_cases hCR : gens cs ≤ gens rs
  · -- Then branch: `gens cs ≤ gens rs`
    have hb : b = true := decide_eq_true hCR
    rw [hb]
    have dv1 := Det.var' (P := P)
      (env := [.list [.list [encGroup hs, encGroup rs, socCsVal Ws], .nat i, acc_v],
        boolVal true])
      (i := 1) (v := .nat 1) rfl
    have dacc := socRd_d_acc (P := P) (hv := encGroup hs) (rv := encGroup rs) (ws := socCsVal Ws)
      (acc := acc_v) (i := i) (rest := [boolVal true])
    refine (Det.ite_pos dv1 Nat.one_ne_zero dacc).post fun c2 hc2 => ?_
    simp only [← hWdef] at hc2
    obtain ⟨hRC, hCH, hnC, hRE, hES, hnE, hCE, _⟩ := hrinv
    refine ⟨⟨cs, es, rfl, hcl, hel, hRC, hCH, hnC, hRE, hES, hnE, hCE, Or.inl hCR⟩, ?_⟩
    unfold socRoundCost
    simp only [← hY]
    have hw1 := wt_nat_le 1
    clear dacc dv1 d1 hles dcv drv
    clear_value W Y acc_v b
    omega
  · -- Else branch: `¬ (gens cs ≤ gens rs)`
    have hb : b = false := decide_eq_false hCR
    rw [hb]
    have dv1 := Det.var' (P := P)
      (env := [.list [.list [encGroup hs, encGroup rs, socCsVal Ws], .nat i, acc_v],
        boolVal false])
      (i := 1) (v := .nat 0) rfl
    obtain ⟨hRC, hCH, hnC, hRE, hES, hnE, hCE, hdone_or_card⟩ := hrinv
    have hcard_i : 2 ^ i * Nat.card (gens cs) ≤ Nat.card (gens hs) :=
      hdone_or_card.resolve_left hCR
    refine (soc_ite_zero dv1 (R := fun w ce =>
      SocRoundValInv (gens hs) (gens rs) (i + 1) w ∧
      ce ≤ socScanCost (normalizedIntersectionPrim hni) (membershipPrim hmem) (10 * W + 10) Ws.length +
        socJoinCutCost (normalizedIntersectionPrim hni) W +
        (gmpFactorKernelPrim hmem hpre).boundSize Y +
        (normalizedIntersectionPrim hni).boundSize Y +
        5 * 10 ^ 8 * Y ^ 3) ?_).mono fun w cost h => ?_
    · -- Evaluate the else body
      -- 1. `.var 2 = encGroup is` via `socScan_spec`
      have drv2 := socRd_d_rv (P := P) (hv := encGroup hs) (rv := encGroup rs) (ws := socCsVal Ws)
        (acc := acc_v) (i := i) (rest := [.nat 0])
      have dws2 := socRd_d_ws (P := P) (hv := encGroup hs) (rv := encGroup rs) (ws := socCsVal Ws)
        (acc := acc_v) (i := i) (rest := [.nat 0])
      have dcv2 := socRd_d_cv (P := P) (hv := encGroup hs) (rv := encGroup rs) (ws := socCsVal Ws)
        (acc := acc_v) (i := i) (rest := [.nat 0]) rfl
      have dsc_arg := Det.mk3 drv2 dws2 dcv2
      have hsc_wt0 := wt_list3_le (encGroup rs) (socCsVal Ws) (encGroup cs)
      have hsc_wt : (Val.list [encGroup rs, socCsVal Ws, encGroup cs]).wt ≤ 10 * W + 10 := by omega
      refine EvalAll.letE
        (Det.call_funAll dsc_arg (socScan_spec hP.scan hnR hchain hCH hCR hcl))
        fun v2 c2 h2 => ?_
      obtain ⟨cb2, ⟨⟨is, rfl, hil, k, hk, hI_eq, hI_not, hnext_le⟩, hcb2⟩, hc2⟩ := h2
      have hb2 : cb2 ≤ socScanCost (normalizedIntersectionPrim hni) (membershipPrim hmem)
          (10 * W + 10) Ws.length :=
        hcb2.trans (socScanCost_mono _ _ hsc_wt le_rfl)
      have hIw := wt_encGroup_sq hil
      -- 2. `.var 3 = encGroup es'` via `socJoinCut_spec`
      have dev3 := socRd_d_ev (P := P) (hv := encGroup hs) (rv := encGroup rs) (ws := socCsVal Ws)
        (acc := acc_v) (i := i) (rest := [.nat 0, encGroup is]) rfl
      have dv2 := Det.var' (P := P)
        (env := [.list [.list [encGroup hs, encGroup rs, socCsVal Ws], .nat i, acc_v],
          .nat 0, encGroup is])
        (i := 2) (v := encGroup is) rfl
      have djc_arg := Det.mk2 dev3 dv2
      have hjc_wt := wt_list2_le (encGroup es) (encGroup is)
      refine EvalAll.letE
        (Det.call_funAll djc_arg (socJoinCut_spec hP.joinCut hP.scan.mg hP.scan.ni hel hil))
        fun v3 c3 h3 => ?_
      obtain ⟨cb3, ⟨es', rfl, hel', heg', hcb3⟩, hc3⟩ := h3
      have hb3 : cb3 ≤ socJoinCutCost (normalizedIntersectionPrim hni) W :=
        hcb3.trans (socJoinCutCost_mono _ hn_le_W)
      have hE'w := wt_encGroup_sq hel'
      -- Mathematical properties of `I = gens is` for `gmpFactorKernel_spec`
      have hk_map : k < (Ws.map gens).length - 1 := by simp [hk]
      have hnI : GI.Multicoset.Normalizes (gens hs) (gens is) := by
        rw [hI_eq]
        exact fun g hg x ⟨hx1, hx2⟩ =>
          ⟨soc_term_normalized hnR hchain k g hg x hx1, hnC g hg x hx2⟩
      -- 3. `.var 4 = v4` via `gmpFactorKernel_spec`
      have dhv4 := socRd_d_hv (P := P) (hv := encGroup hs) (rv := encGroup rs) (ws := socCsVal Ws)
        (acc := acc_v) (i := i) (rest := [.nat 0, encGroup is, encGroup es'])
      have dv2_4 := Det.var' (P := P)
        (env := [.list [.list [encGroup hs, encGroup rs, socCsVal Ws], .nat i, acc_v],
          .nat 0, encGroup is, encGroup es'])
        (i := 2) (v := encGroup is) rfl
      have drv4 := socRd_d_rv (P := P) (hv := encGroup hs) (rv := encGroup rs) (ws := socCsVal Ws)
        (acc := acc_v) (i := i) (rest := [.nat 0, encGroup is, encGroup es'])
      have dfk_arg := Det.mk3 dhv4 dv2_4 drv4
      have hfk_wt0 := wt_list3_le (encGroup hs) (encGroup is) (encGroup rs)
      refine EvalAll.letE
        (EvalAll.call_spec dfk_arg
          (gmpFactorKernel_spec hP.fk ⟨hs, rfl, rfl⟩ ⟨is, rfl, rfl⟩ ⟨rs, rfl, rfl⟩
            hnI hnR le_rfl))
        fun v4 c4 h4 => ?_
      obtain ⟨cb4, ⟨⟨Z, hZ_val, hZ_mem⟩, hcb4⟩, hc4⟩ := h4
      have hZ_mem' : ∀ h, h ∈ Z ↔
          h ∈ gens hs ∧ ∀ u ∈ socTerm (gens rs) (Ws.map gens) k ⊓ gens cs,
            h * u * h⁻¹ * u⁻¹ ∈ gens rs := by
        simpa only [hI_eq] using hZ_mem
      obtain ⟨hI_soc, hidx_le, hEI_soc, hCZ_quot, hcard_step⟩ :=
        soc_round_step_math hRH hnR hrf hchain hRC hCH hnC hES hCE hk_map hI_not hnext_le hZ_mem'
      have hidx_q : ((gens rs).subgroupOf (gens is)).index ≤ q := by
        rw [hI_eq]
        exact hidx_le.trans hq
      have hfk_wt_le : (Val.list [encGroup hs, encGroup is, encGroup rs]).wt ≤
          400 * (W + q + 1) ^ 6 := by omega
      have hb4 : cb4 ≤ (gmpFactorKernelPrim hmem hpre).boundSize Y :=
        (hcb4.trans (gmpFactorKernelCost_mono hmem hpre hfk_wt_le hidx_q)).trans
          ((gmpFactorKernelCost_le_boundSize hmem hpre (400 * (W + q + 1) ^ 6) q).trans
            (soc_boundSize_mono (gmpFactorKernelPrim hmem hpre) (by
              have : (W + q + 1) ≤ (W + q + 1) ^ 6 := hW6
              omega)))
      -- 4. `.var 5 = v5` via `jni` on `[encGroup cs, mg [n, .var 4]]`
      have dn5 := socRd_d_n (P := P) (hv := encGroup hs) (rv := encGroup rs) (ws := socCsVal Ws)
        (acc := acc_v) (i := i) (rest := [.nat 0, encGroup is, encGroup es', v4]) rfl
      obtain ⟨zs, hzl, hzg, dZ, hZw⟩ :=
        outb_mk_det hP.scan.mg dn5 (Det.var' (P := P)
          (env := [.list [.list [encGroup hs, encGroup rs, socCsVal Ws], .nat i, acc_v],
            .nat 0, encGroup is, encGroup es', v4])
          (i := 4) (v := v4) rfl) hZ_val
      have dcv5 := socRd_d_cv (P := P) (hv := encGroup hs) (rv := encGroup rs) (ws := socCsVal Ws)
        (acc := acc_v) (i := i) (rest := [.nat 0, encGroup is, encGroup es', v4]) rfl
      have hIH : gens is ≤ gens hs := by rw [hI_eq]; exact inf_le_right.trans hCH
      obtain ⟨hRZ, hZH, hnZ, _⟩ := soc_factorKernel_props hRH hnR hIH hnI hZ_mem
      have hnCZ : GI.Lang.Normalizes (gens cs) (gens zs) := by
        rw [hzg]
        exact fun g hg x hx => hnZ g (hCH hg) x hx
      have dni5 := Det.mk2 dcv5 dZ
      have hni5_wt := wt_list2_le (encGroup cs) (encGroup zs)
      have hni5_sz : (Val.list [encGroup cs, encGroup zs]).size ≤ Y :=
        (Val.size_le_wt _).trans (by omega)
      refine EvalAll.letE
        (normalizedIntersection_call hni hP.scan.ni dni5 ⟨cs, rfl, rfl⟩ ⟨zs, rfl, rfl⟩ hnCZ)
        fun v5 c5 h5 => ?_
      obtain ⟨hv5, hc5⟩ := h5
      have hb5 := (normalizedIntersectionPrim hni).bound_le hni5_sz
      -- 5. `.var 6 = encGroup cs'` via `mg` on `[n, .var 5]`
      have dn6 := socRd_d_n (P := P) (hv := encGroup hs) (rv := encGroup rs) (ws := socCsVal Ws)
        (acc := acc_v) (i := i) (rest := [.nat 0, encGroup is, encGroup es', v4, v5]) rfl
      obtain ⟨cs', hcl', hcg', dC', hC'w⟩ :=
        outb_mk_det hP.scan.mg dn6 (Det.var' (P := P)
          (env := [.list [.list [encGroup hs, encGroup rs, socCsVal Ws], .nat i, acc_v],
            .nat 0, encGroup is, encGroup es', v4, v5])
          (i := 5) (v := v5) rfl) hv5
      refine EvalAll.letE dC' fun v6 c6 h6 => ?_
      obtain ⟨rfl, hc6⟩ := h6
      -- 6. Return `mk2 (.var 6) (.var 3)`
      have dv6 := Det.var' (P := P)
        (env := [.list [.list [encGroup hs, encGroup rs, socCsVal Ws], .nat i, acc_v],
          .nat 0, encGroup is, encGroup es', v4, v5, encGroup cs'])
        (i := 6) (v := encGroup cs') rfl
      have dv3 := Det.var' (P := P)
        (env := [.list [.list [encGroup hs, encGroup rs, socCsVal Ws], .nat i, acc_v],
          .nat 0, encGroup is, encGroup es', v4, v5, encGroup cs'])
        (i := 3) (v := encGroup es') rfl
      refine (Det.mk2 dv6 dv3).post fun c7 hc7 => ⟨⟨cs', es', rfl, hcl', hel', ?_⟩, ?_⟩
      · -- `SocRoundInv (gens hs) (gens rs) (i + 1) (gens cs') (gens es')`
        rw [hcg', hzg, heg', hI_eq]
        have hnC' : GI.Multicoset.Normalizes (gens hs) (gens cs ⊓ Z) :=
          fun g hg x ⟨hx1, hx2⟩ => ⟨hnC g hg x hx1, hnZ g hg x hx2⟩
        have hnE' : GI.Multicoset.Normalizes (gens hs)
            (gens es ⊔ (socTerm (gens rs) (Ws.map gens) k ⊓ gens cs)) :=
          rad_sup_normalized hnE (by rwa [← hI_eq])
        have hcard_i1 : 2 ^ (i + 1) * Nat.card (gens cs ⊓ Z : Subgroup _) ≤
            Nat.card (gens hs) := by
          calc 2 ^ (i + 1) * Nat.card (gens cs ⊓ Z : Subgroup _) =
                2 ^ i * (2 * Nat.card (gens cs ⊓ Z : Subgroup _)) := by ring
            _ ≤ 2 ^ i * Nat.card (gens cs) := Nat.mul_le_mul_left _ hcard_step
            _ ≤ Nat.card (gens hs) := hcard_i
        exact ⟨le_inf hRC hRZ, inf_le_left.trans hCH, hnC',
          le_sup_of_le_left hRE, hEI_soc, hnE', hCZ_quot, Or.inr hcard_i1⟩
      · -- Cost bound of the else body
        have w4 := GensVal.wt_le hZ_val
        have w5 := GensVal.wt_le hv5
        have hl_mk4 := wt_list2_le (.nat n) v4
        have hl_mk5 := wt_list2_le (.nat n) v5
        have hl_out := wt_list2_le (encGroup cs') (encGroup es')
        have hnw : (Val.nat n).wt < (encGroup hs).wt :=
          wt_le_wt_list (vs := [.nat n, _]) (by simp)
        simp only [← hWdef] at hc2 hc3 hc4 hc5 hc6 hc7
        clear dv3 dv6 dC' dn6 dni5 dcv5 dZ dn5 dfk_arg drv4 dv2_4 dhv4 djc_arg dv2 dev3 dsc_arg
          dcv2 dws2 drv2 dv1 d1 hles dcv drv
        clear_value W Y acc_v b
        omega
    · -- Combine outer `le` cost, `ite` overhead, and else body cost
      obtain ⟨ce, ⟨hinv_w, hce⟩, hcost⟩ := h
      have hw_wt := soc_round_val_wt hinv_w
      refine ⟨hinv_w, ?_⟩
      unfold socRoundCost
      simp only [← hY]
      have hw0 := wt_nat_le 0
      clear dv1 d1 hles dcv drv
      clear_value W Y acc_v b
      omega

end GI.Impl
