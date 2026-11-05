module

public import Workspace.SocPreMath
public import Workspace.Impl.OutbSuppDesc
public import Workspace.Impl.GMPFactorKernel

@[expose] public section

/-!
# Inner scan loop of the socle preimage program

Given `[encGroup rs, socCsVal Ws, encGroup cs]` where `Ws` is a nonabelian-chief chain from `H` to
`R = gens rs`, `C = gens cs ≤ H` is normalized by `H`, and `¬ (C ≤ R)`:

1. `socScanStepBody` on `[[encGroup rs, socCsVal Ws, encGroup cs], .nat j, encGroup is]`:
   - forms `encGroup Ws[j]` via `mkGroupFuns` (`mg`),
   - intersects `C ⊓ W_j` via `normalizedIntersectionPrim` (`jni`) and wraps into `encGroup ks`
     (`ks.length ≤ n²`, `gens ks = W_j ⊓ C`) via `mg`,
   - tests `decide (gens ks ≤ gens rs)` via `leFuns` (`le`),
   - returns `encGroup is` if `gens ks ≤ gens rs` and `encGroup ks` otherwise.
2. `socScanBody` iterates `socScanStepBody` for `j = 0, …, Ws.length - 2` starting from
   `encGroup cs`, returning `encGroup is` (`is.length ≤ n²`) with
   `gens is = socTerm R (Ws.map gens) k ⊓ C` for the largest `k < Ws.length - 1` such that
   `¬ (socTerm R (Ws.map gens) k ⊓ C ≤ R)` (`socScan_spec`).

Only **NormalizedIntersection** (`jni`) and **Membership** (`jm`) are used.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### Value representation of a subgroup chain and general step helpers -/

/-- A chain of generator lists as a `Val` (`abbrev` so it unifies definitionally with
`.list (Ws.map fun hs => .list (hs.map encPerm))`). -/
abbrev socCsVal (Ws : List (List (Perm (Fin n)))) : Val :=
  .list (Ws.map fun hs => .list (hs.map encPerm))

/-- Weight of a 3-element context step argument `[[a, b, c], .nat j, acc]`. -/
abbrev socW (a b c acc : Val) (j : ℕ) : ℕ :=
  (Val.list [.list [a, b, c], .nat j, acc]).wt

theorem soc_wt_facts (a b c acc : Val) (j : ℕ) :
    a.wt < socW a b c acc j ∧ b.wt < socW a b c acc j ∧ c.wt < socW a b c acc j ∧
      acc.wt < socW a b c acc j ∧ (Val.nat j).wt < socW a b c acc j := by
  have hc : (Val.list [a, b, c]).wt < socW a b c acc j := wt_le_wt_list (by simp)
  have h1 : a.wt < (Val.list [a, b, c]).wt := wt_le_wt_list (by simp)
  have h2 : b.wt < (Val.list [a, b, c]).wt := wt_le_wt_list (by simp)
  have h3 : c.wt < (Val.list [a, b, c]).wt := wt_le_wt_list (by simp)
  have h4 : acc.wt < socW a b c acc j := wt_le_wt_list (by simp)
  have h5 : (Val.nat j).wt < socW a b c acc j := wt_le_wt_list (by simp)
  omega

theorem soc_boundSize_mono (p : Prim) {B B' : ℕ} (h : B ≤ B') :
    p.boundSize B ≤ p.boundSize B' :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem soc_wt_append (xs ys : List Val) :
    (Val.list (xs ++ ys)).wt ≤ 3 * ((Val.list xs).wt + (Val.list ys).wt) + 4 := by
  have h := wt_list_le (xs ++ ys)
  have h1 := sum_wt_lt_wt_list xs
  have h2 := sum_wt_lt_wt_list ys
  have h3 := length_lt_wt_list xs
  have h4 := length_lt_wt_list ys
  simp only [List.map_append, List.sum_append, List.length_append] at h
  omega

theorem soc_ite_zero {P : Program} {env : List Val} {c t e : Expr} {cc : ℕ}
    (hc : Det P env c (.nat 0) cc) {R : Val → ℕ → Prop} (he : EvalAll P env e R) :
    EvalAll P env (.ite c t e) (fun w c' => ∃ ce, R w ce ∧ c' ≤ cc + ce + w.wt + 1) :=
  EvalAll.ite hc (fun _ _ h => ⟨0, h.1⟩) fun y cc' h => by
    obtain ⟨h1, h2⟩ := h
    cases h1
    simp only [↓reduceIte]
    exact he.mono fun w ce hw => ⟨ce, hw, by omega⟩

theorem soc_ite_bool {P : Program} {env : List Val} {e e1 e2 : Expr}
    {b : Bool} {v1 v2 : Val} {ce c1 c2 : ℕ}
    (he : Det P env e (boolVal b) ce)
    (h1 : Det P env e1 v1 c1) (h2 : Det P env e2 v2 c2) :
    Det P env (.ite e e1 e2) (if b then v1 else v2)
      (ce + max c1 c2 + max v1.wt v2.wt + 1) := by
  cases b
  · exact (Det.ite_zero he h2).mono (by omega)
  · exact (Det.ite_pos he (by decide) h1).mono (by omega)

/-! ### Expressions for the scan step and scan loop -/

/-- `encGroup rs` in the scan step context `[[rv, ws, cv], j, acc]`. -/
def socScanRvE : Expr := .get (arg 0) (.nat 0)
/-- `socCsVal Ws` in the scan step context `[[rv, ws, cv], j, acc]`. -/
def socScanWsE : Expr := .get (arg 0) (.nat 1)
/-- `encGroup cs` in the scan step context `[[rv, ws, cv], j, acc]`. -/
def socScanCvE : Expr := .get (arg 0) (.nat 2)
/-- The degree `n`, read off `encGroup rs`. -/
def socScanNE : Expr := .get socScanRvE (.nat 0)

/-- **One step of the inner scan** on `[[encGroup rs, socCsVal Ws, encGroup cs], .nat j, encGroup is]`:
1. `.var 1 = encGroup Ws[j]` via `mg`
2. `.var 2 = v2` (`GensVal n v2 (gens cs ⊓ gens Ws[j])`) via `jni`
3. `.var 3 = encGroup ks` (`ks.length ≤ n²`, `gens ks = gens Ws[j] ⊓ gens cs`) via `mg`
4. `.var 4 = .nat (if decide (gens ks ≤ gens rs) then 1 else 0)` via `le`
5. returns `arg 2` if `.var 4 ≠ 0`, else `.var 3`. -/
def socScanStepBody (mg le jni : ℕ) : Expr :=
  .letE (.call mg (mk2 socScanNE (.get socScanWsE (arg 1))))
  (.letE (.prim jni (mk2 socScanCvE (.var 1)))
  (.letE (.call mg (mk2 socScanNE (.var 2)))
  (.letE (.call le (mk2 socScanRvE (.var 3)))
    (.ite (.var 4) (arg 2) (.var 3)))))

/-- **The inner scan function** on `[encGroup rs, socCsVal Ws, encGroup cs]`:
runs `Ws.length - 1` steps of `socScanStepBody` via `it_sc` starting from `encGroup cs`. -/
def socScanBody (it_sc : ℕ) : Expr :=
  .call it_sc (mk3 (.var 0)
    (.arith .sub (.length (arg 1)) (.nat 1))
    (arg 2))

/-! ### Reading the scan step context -/

section ReadScan

variable {P : Program} {rv ws cv acc : Val} {j : ℕ} {rest : List Val}

theorem soc_d_ctx :
    Det P (.list [.list [rv, ws, cv], .nat j, acc] :: rest) (arg 0) (.list [rv, ws, cv])
      (2 * socW rv ws cv acc j + 5) := Det.arg' (j := 0) rfl

theorem socScan_d_rv : Det P (.list [.list [rv, ws, cv], .nat j, acc] :: rest) socScanRvE rv
    (4 * socW rv ws cv acc j + 10) := by
  have := soc_wt_facts rv ws cv acc j
  exact (Det.get' soc_d_ctx (Det.nat 0) rfl).mono (by omega)

theorem socScan_d_ws : Det P (.list [.list [rv, ws, cv], .nat j, acc] :: rest) socScanWsE ws
    (4 * socW rv ws cv acc j + 10) := by
  have := soc_wt_facts rv ws cv acc j
  exact (Det.get' soc_d_ctx (Det.nat 1) rfl).mono (by omega)

theorem socScan_d_cv : Det P (.list [.list [rv, ws, cv], .nat j, acc] :: rest) socScanCvE cv
    (4 * socW rv ws cv acc j + 11) := by
  have := soc_wt_facts rv ws cv acc j
  exact (Det.get' soc_d_ctx (Det.nat 2) rfl).mono (by omega)

theorem socScan_d_j : Det P (.list [.list [rv, ws, cv], .nat j, acc] :: rest) (arg 1) (.nat j)
    (3 * socW rv ws cv acc j + 10) := by
  have := soc_wt_facts rv ws cv acc j
  have e : (Val.list [.list [rv, ws, cv], .nat j, acc]).wt = socW rv ws cv acc j := rfl
  exact (Det.arg' (j := 1) rfl).mono (by omega)

theorem socScan_d_acc : Det P (.list [.list [rv, ws, cv], .nat j, acc] :: rest) (arg 2) acc
    (3 * socW rv ws cv acc j + 10) := by
  have := soc_wt_facts rv ws cv acc j
  have e : (Val.list [.list [rv, ws, cv], .nat j, acc]).wt = socW rv ws cv acc j := rfl
  exact (Det.arg' (j := 2) rfl).mono (by omega)

theorem socScan_d_n {rs : List (Perm (Fin n))} (hr : rv = encGroup rs) :
    Det P (.list [.list [rv, ws, cv], .nat j, acc] :: rest) socScanNE (.nat n)
      (6 * socW rv ws cv acc j + 20) := by
  have := soc_wt_facts rv ws cv acc j
  have hn : (Val.nat n).wt < rv.wt := by
    rw [hr]; exact wt_le_wt_list (vs := [.nat n, _]) (by simp)
  have hh : Det P (.list [.list [rv, ws, cv], .nat j, acc] :: rest) socScanRvE rv
    (4 * socW rv ws cv acc j + 10) := socScan_d_rv
  rw [hr] at hh hn ⊢
  exact (Det.get' hh (Det.nat 0) (v := .nat n) rfl).mono (by rw [hr] at this; omega)

theorem socScan_d_wsj {Ws : List (List (Perm (Fin n)))}
    (hws : ws = socCsVal Ws) {j : ℕ} (hj : j < Ws.length) :
    Det P (.list [.list [rv, ws, cv], .nat j, acc] :: rest) (.get socScanWsE (arg 1))
      (.list (Ws[j].map encPerm)) (10 * socW rv ws cv acc j + 30) := by
  have hw := soc_wt_facts rv ws cv acc j
  have hlt : (Val.list (Ws[j].map encPerm)).wt < ws.wt := by
    rw [hws]
    exact wt_le_wt_list (List.mem_map.mpr ⟨Ws[j], List.getElem_mem hj, rfl⟩)
  have hh : Det P (.list [.list [rv, ws, cv], .nat j, acc] :: rest) socScanWsE ws
      (4 * socW rv ws cv acc j + 10) := socScan_d_ws
  have dj : Det P (.list [.list [rv, ws, cv], .nat j, acc] :: rest) (arg 1) (.nat j)
      (3 * socW rv ws cv acc j + 10) := socScan_d_j
  have hget : (Ws.map fun hs => Val.list (hs.map encPerm))[j]? = some (.list (Ws[j].map encPerm)) := by
    simp [hj]
  rw [hws] at hh hlt dj hw ⊢
  exact (Det.get' hh dj hget).mono (by omega)

end ReadScan

/-! ### Weight of `encGroup hs` from the weight of `hs.map encPerm` -/

theorem soc_wt_encGroup_of_list_wt {hs : List (Perm (Fin n))} {W : ℕ}
    (hnW : n + 1 ≤ W) (hlW : (Val.list (hs.map encPerm)).wt ≤ W) :
    (encGroup hs).wt ≤ 100 * (W + 1) ^ 2 := by
  have hp1 := wt_encPerm_le (1 : Perm (Fin n))
  have hl1 := wt_list1_le (encPerm (1 : Perm (Fin n)))
  have hap := soc_wt_append [encPerm (1 : Perm (Fin n))] (hs.map encPerm)
  have hmap : [encPerm (1 : Perm (Fin n))] ++ hs.map encPerm = (1 :: hs).map encPerm := rfl
  rw [hmap] at hap
  have hnw := wt_nat_le n
  have h2 := wt_list2_le (.nat n) (.list ((1 :: hs).map encPerm))
  have e : (Val.list [.nat n, .list ((1 :: hs).map encPerm)]).wt = (encGroup hs).wt := rfl
  have hn2 : (n + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hp1' : (encPerm (1 : Perm (Fin n))).wt ≤ 4 * (W + 1) ^ 2 :=
    hp1.trans (Nat.mul_le_mul_left _ hn2)
  have hW2 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by decide) _
  omega

/-! ### Invariant and cost of the scan step -/

/-- Value-level invariant of the scan loop after `j` steps: `acc = encGroup is` with
`is.length ≤ n²` and `SocScanInv R (Ws.map gens) C j (gens is)`. -/
def SocScanValInv (R : Subgroup (Perm (Fin n))) (Ws : List (List (Perm (Fin n))))
    (C : Subgroup (Perm (Fin n))) (j : ℕ) (acc : Val) : Prop :=
  ∃ is : List (Perm (Fin n)), acc = encGroup is ∧ is.length ≤ n ^ 2 ∧
    SocScanInv R (Ws.map gens) C j (gens is)

/-- Cost bound of one scan step on an argument of weight `W`. -/
def socScanStepCost (pni pm : Prim) (W : ℕ) : ℕ :=
  pni.boundSize (1000 * (W + 1) ^ 6) +
    1000 * (W + 1) ^ 6 * pm.boundSize (1000 * (W + 1) ^ 6) +
    10 ^ 8 * (1000 * (W + 1) ^ 6) ^ 3

theorem socScanStepCost_mono (pni pm : Prim) {W W' : ℕ} (h : W ≤ W') :
    socScanStepCost pni pm W ≤ socScanStepCost pni pm W' := by
  have hY : 1000 * (W + 1) ^ 6 ≤ 1000 * (W' + 1) ^ 6 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  unfold socScanStepCost
  have := soc_boundSize_mono pni hY
  have := Nat.mul_le_mul hY (soc_boundSize_mono pm hY)
  have := Nat.pow_le_pow_left hY 3
  omega

/-- Where the scan function and its step sit in `P`. -/
structure SocScanAt (P : Program) (sc it_sc sc_st mg le jni jm : ℕ)
    (hni : NormalizedIntersection) (hmem : Membership) : Prop where
  scan : P.funs[sc]? = some (socScanBody it_sc)
  iter : P.HasAt it_sc (iterFuns it_sc sc_st)
  step : P.funs[sc_st]? = some (socScanStepBody mg le jni)
  mg : P.HasAt mg (mkGroupFuns mg)
  le : P.HasAt le (leFuns le jm)
  ni : P.prims[jni]? = some (normalizedIntersectionPrim hni)
  mem : P.prims[jm]? = some (membershipPrim hmem)

theorem soc_term_map_eq {R : Subgroup (Perm (Fin n))} {Ws : List (List (Perm (Fin n)))}
    {j : ℕ} (hj : j < Ws.length) :
    socTerm R (Ws.map gens) j = gens Ws[j] := by
  simp [socTerm, hj]

set_option maxHeartbeats 400000 in
open Classical in
/-- **One step of the inner scan** preserves `SocScanValInv` from `j` to `j + 1`. -/
theorem socScanStep_spec {hni : NormalizedIntersection} {hmem : Membership}
    {P : Program} {sc_st mg le jni jm : ℕ}
    (hstep : P.funs[sc_st]? = some (socScanStepBody mg le jni))
    (hmg : P.HasAt mg (mkGroupFuns mg))
    (hle : P.HasAt le (leFuns le jm))
    (hji : P.prims[jni]? = some (normalizedIntersectionPrim hni))
    (hjm : P.prims[jm]? = some (membershipPrim hmem))
    {H : Subgroup (Perm (Fin n))} {rs cs : List (Perm (Fin n))}
    {Ws : List (List (Perm (Fin n)))}
    (hnR : GI.Multicoset.Normalizes H (gens rs))
    (hs : SocChain H (gens rs) (Ws.map gens))
    (hCH : gens cs ≤ H) (hCR : ¬ (gens cs ≤ gens rs))
    {j : ℕ} (hj : j < Ws.length - 1) {acc : Val}
    (hinv : SocScanValInv (gens rs) Ws (gens cs) j acc) :
    FunAll P sc_st (.list [.list [encGroup rs, socCsVal Ws, encGroup cs], .nat j, acc])
      (fun w c => SocScanValInv (gens rs) Ws (gens cs) (j + 1) w ∧
        c ≤ socScanStepCost (normalizedIntersectionPrim hni) (membershipPrim hmem)
          (socW (encGroup rs) (socCsVal Ws) (encGroup cs) acc j)) := by
  obtain ⟨is, rfl, hil, hsinv⟩ := hinv
  have hw := soc_wt_facts (encGroup rs) (socCsVal Ws) (encGroup cs) (encGroup is) j
  set W := socW (encGroup rs) (socCsVal Ws) (encGroup cs) (encGroup is) j with hWdef
  set Y := 1000 * (W + 1) ^ 6 with hY
  have hj0 : j < Ws.length := by omega
  have hWj_eq : socTerm (gens rs) (Ws.map gens) j = gens (Ws[j]'hj0) := soc_term_map_eq hj0
  have hnWj : GI.Multicoset.Normalizes H (gens (Ws[j]'hj0)) := by
    have := soc_term_normalized hnR hs j
    rwa [hWj_eq] at this
  have hnCWj : GI.Lang.Normalizes (gens cs) (gens (Ws[j]'hj0)) :=
    fun g hg x hx => hnWj g (hCH hg) x hx
  have hnW : n + 1 ≤ W := by
    have := S_le_wt_encGroup rs
    have : n + 1 ≤ (rs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hwj_wt : (Val.list ((Ws[j]'hj0).map encPerm)).wt ≤ W := by
    have : (Val.list ((Ws[j]'hj0).map encPerm)).wt < (socCsVal Ws).wt :=
      wt_le_wt_list (List.mem_map.mpr ⟨Ws[j]'hj0, List.getElem_mem hj0, rfl⟩)
    omega
  have hwj_len : (Ws[j]'hj0).length < W := by
    have h1 := length_lt_wt_list ((Ws[j]'hj0).map encPerm)
    simp only [List.length_map] at h1
    omega
  have hW6 : W + 1 ≤ (W + 1) ^ 6 := Nat.le_self_pow (by decide) _
  have hW2 : (W + 1) ^ 2 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hn6 : (n + 1) ^ 6 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hn9 : 8 * mkGroupK * (n + 1) ^ 9 ≤ Y ^ 2 := by
    have : (n + 1) ^ 9 ≤ (W + 1) ^ 12 :=
      (Nat.pow_le_pow_left (show n + 1 ≤ W + 1 by omega) 9).trans
        (Nat.pow_le_pow_right (by omega) (by decide))
    have e : Y ^ 2 = 1000000 * (W + 1) ^ 12 := by rw [hY]; ring
    simp only [mkGroupK]; omega
  have hY1 : Y ≤ Y ^ 2 := Nat.le_self_pow (by decide) _
  have hY2 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  -- step 1: `.var 1 = encGroup (Ws[j]'hj0)` via `mkGroup_spec`
  have dn0 := socScan_d_n (P := P) (rv := encGroup rs) (ws := socCsVal Ws) (cv := encGroup cs)
    (acc := encGroup is) (j := j) (rest := []) rfl
  have dwsj := socScan_d_wsj (P := P) (rv := encGroup rs) (ws := socCsVal Ws) (cv := encGroup cs)
    (acc := encGroup is) (j := j) (rest := []) rfl hj0
  have d1 := Det.call (Det.mk2 dn0 dwsj) (mkGroup_spec hmg (Ws[j]'hj0))
  have hw1 : (encGroup (Ws[j]'hj0)).wt ≤ 100 * (W + 1) ^ 2 :=
    soc_wt_encGroup_of_list_wt hnW hwj_wt
  have hS_le : ((Ws[j]'hj0).length + 2) * (n + 1) ≤ 2 * (W + 1) ^ 2 := by
    calc ((Ws[j]'hj0).length + 2) * (n + 1) ≤ (2 * (W + 1)) * (W + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * (W + 1) ^ 2 := by ring
  have hmk1_cost : mkGroupK * (((Ws[j]'hj0).length + 2) * (n + 1)) ^ 3 ≤ Y ^ 2 := by
    have hpow : (((Ws[j]'hj0).length + 2) * (n + 1)) ^ 3 ≤ (2 * (W + 1) ^ 2) ^ 3 :=
      Nat.pow_le_pow_left hS_le 3
    have e1 : (2 * (W + 1) ^ 2) ^ 3 = 8 * (W + 1) ^ 6 := by ring
    have e2 : Y ^ 2 = 1000000 * (W + 1) ^ 12 := by rw [hY]; ring
    have h612 : (W + 1) ^ 6 ≤ (W + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by decide)
    simp only [mkGroupK] at *
    omega
  refine FunAll.intro hstep (EvalAll.letE d1 fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  -- step 2: `.var 2 = v2` (`GensVal n v2 (gens cs ⊓ gens (Ws[j]'hj0))`) via `jni`
  have dcv := socScan_d_cv (P := P) (rv := encGroup rs) (ws := socCsVal Ws) (cv := encGroup cs)
    (acc := encGroup is) (j := j) (rest := [encGroup (Ws[j]'hj0)])
  have dv1 := Det.var' (P := P)
    (env := [.list [.list [encGroup rs, socCsVal Ws, encGroup cs], .nat j, encGroup is],
      encGroup (Ws[j]'hj0)])
    (i := 1) (v := encGroup (Ws[j]'hj0)) rfl
  have dni_arg := Det.mk2 dcv dv1
  have hni_wt := wt_list2_le (encGroup cs) (encGroup (Ws[j]'hj0))
  have hni_sz : (Val.list [encGroup cs, encGroup (Ws[j]'hj0)]).size ≤ Y :=
    (Val.size_le_wt _).trans (by omega)
  refine EvalAll.letE
    (normalizedIntersection_call hni hji dni_arg ⟨cs, rfl, rfl⟩ ⟨Ws[j]'hj0, rfl, rfl⟩ hnCWj)
    fun v2 c2 h2 => ?_
  obtain ⟨hv2, hc2⟩ := h2
  have hb2 := (normalizedIntersectionPrim hni).bound_le hni_sz
  -- step 3: `.var 3 = encGroup ks` via `outb_mk_det`
  have dn2 := socScan_d_n (P := P) (rv := encGroup rs) (ws := socCsVal Ws) (cv := encGroup cs)
    (acc := encGroup is) (j := j) (rest := [encGroup (Ws[j]'hj0), v2]) rfl
  obtain ⟨ks, hkl, hkg, d3, hkw⟩ :=
    outb_mk_det hmg dn2 (Det.var' (P := P)
      (env := [.list [.list [encGroup rs, socCsVal Ws, encGroup cs], .nat j, encGroup is],
        encGroup (Ws[j]'hj0), v2])
      (i := 2) (v := v2) rfl) hv2
  have hkg' : gens ks = socTerm (gens rs) (Ws.map gens) j ⊓ gens cs := by
    rw [hkg, inf_comm, hWj_eq]
  refine EvalAll.letE d3 fun v3 c3 h3 => ?_
  obtain ⟨rfl, hc3⟩ := h3
  -- step 4: `.var 4 = decide (gens ks ≤ gens rs)` via `le_spec`
  have drv := socScan_d_rv (P := P) (rv := encGroup rs) (ws := socCsVal Ws) (cv := encGroup cs)
    (acc := encGroup is) (j := j) (rest := [encGroup (Ws[j]'hj0), v2, encGroup ks])
  have dv3 := Det.var' (P := P)
    (env := [.list [.list [encGroup rs, socCsVal Ws, encGroup cs], .nat j, encGroup is],
      encGroup (Ws[j]'hj0), v2, encGroup ks])
    (i := 3) (v := encGroup ks) rfl
  have hles := le_spec hmem hle hjm (⟨rs, rfl, rfl⟩ : GroupVal n (encGroup rs) (gens rs)) ks
  have d4 := Det.call (Det.mk2 drv dv3) hles
  set b := decide (gens ks ≤ gens rs) with hbdef
  refine EvalAll.letE d4 fun v4 c4 h4 => ?_
  obtain ⟨rfl, hc4⟩ := h4
  -- step 5: `.ite (.var 4) (arg 2) (.var 3)`
  have dv4 := Det.var' (P := P)
    (env := [.list [.list [encGroup rs, socCsVal Ws, encGroup cs], .nat j, encGroup is],
      encGroup (Ws[j]'hj0), v2, encGroup ks, boolVal b])
    (i := 4) (v := boolVal b) rfl
  have dacc := socScan_d_acc (P := P) (rv := encGroup rs) (ws := socCsVal Ws) (cv := encGroup cs)
    (acc := encGroup is) (j := j)
    (rest := [encGroup (Ws[j]'hj0), v2, encGroup ks, boolVal b])
  have dv3' := Det.var' (P := P)
    (env := [.list [.list [encGroup rs, socCsVal Ws, encGroup cs], .nat j, encGroup is],
      encGroup (Ws[j]'hj0), v2, encGroup ks, boolVal b])
    (i := 3) (v := encGroup ks) rfl
  have dite := soc_ite_bool dv4 dacc dv3'
  refine dite.post fun c5 hc5 => ?_
  -- Bounds for the cost
  have w2 := GensVal.wt_le hv2
  have hl_mk1 := wt_list2_le (.nat n) (.list ((Ws[j]'hj0).map encPerm))
  have hl_mk2 := wt_list2_le (.nat n) v2
  have hnw : (Val.nat n).wt < (encGroup rs).wt := wt_le_wt_list (vs := [.nat n, _]) (by simp)
  have hlarg := wt_list2_le (encGroup rs) (encGroup ks)
  have hmarg := wt_list2_le (encGroup rs) (encPerm (1 : Perm (Fin n)))
  have hn2 : (n + 1) ^ 2 ≤ (W + 1) ^ 6 :=
    (Nat.pow_le_pow_left (show n + 1 ≤ W + 1 by omega) 2).trans hW2
  have hp1 : (encPerm (1 : Perm (Fin n))).wt ≤ 4 * (W + 1) ^ 6 :=
    (wt_encPerm_le (1 : Perm (Fin n))).trans (Nat.mul_le_mul_left _ hn2)
  have hms : (Val.list [encGroup rs, encPerm (1 : Perm (Fin n))]).size ≤ Y :=
    (Val.size_le_wt _).trans (by omega)
  have hbm := (membershipPrim hmem).bound_le hms
  have hX : (Val.list [encGroup rs, encGroup ks]).wt ≤ Y := by omega
  have hX3 : (Val.list [encGroup rs, encGroup ks]).wt ^ 3 ≤ Y ^ 3 :=
    Nat.pow_le_pow_left hX 3
  have hXm : (Val.list [encGroup rs, encGroup ks]).wt *
      (membershipPrim hmem).bound (.list [encGroup rs, encPerm (1 : Perm (Fin n))]) ≤
      Y * (membershipPrim hmem).boundSize Y := Nat.mul_le_mul hX hbm
  have hw_b : (boolVal b).wt ≤ 3 := wt_boolVal_le b
  have hmax_wt : max (encGroup is).wt (encGroup ks).wt ≤ Y := max_le (by omega) (by omega)
  have hres_wt : (if b = true then encGroup is else encGroup ks).wt ≤ Y := by
    split <;> omega
  simp only [← hWdef] at hc1 hc2 hc3 hc4 hc5
  constructor
  · by_cases hb : b = true
    · have hle_ks : socTerm (gens rs) (Ws.map gens) j ⊓ gens cs ≤ gens rs := by
        rw [← hkg']
        exact of_decide_eq_true (hbdef ▸ hb)
      simp only [hb, ↓reduceIte]
      exact ⟨is, rfl, hil, soc_scan_step_true hs hCH hCR hsinv hle_ks⟩
    · have hnot_ks : ¬ (socTerm (gens rs) (Ws.map gens) j ⊓ gens cs ≤ gens rs) := by
        rw [← hkg']
        exact of_decide_eq_false (hbdef ▸ Bool.eq_false_of_ne_true hb)
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact ⟨ks, rfl, hkl, hkg' ▸ soc_scan_step_false hnot_ks⟩
  · unfold socScanStepCost
    simp only [← hY]
    generalize (if b = true then encGroup is else encGroup ks) = res at hres_wt hc5 ⊢
    generalize max (encGroup is).wt (encGroup ks).wt = mwt at hmax_wt hc5
    clear dite dv3' dacc dv4 d4 hles dv3 drv d3 dni_arg dv1 dcv d1 dwsj dn0 dn2
    clear_value W Y b
    omega

/-! ### Specification of the full inner scan `socScanBody` -/

/-- Cost bound of `socScanBody` on an input `[encGroup rs, socCsVal Ws, encGroup cs]` of weight `W`
and chain length `L = Ws.length`. -/
def socScanCost (pni pm : Prim) (W L : ℕ) : ℕ :=
  (L + 1) * socScanStepCost pni pm (2000 * (W + 1) ^ 6) +
    10 ^ 7 * (L + 1) * (W + 1) ^ 6

theorem socScanCost_mono (pni pm : Prim) {W W' L L' : ℕ} (hW : W ≤ W') (hL : L ≤ L') :
    socScanCost pni pm W L ≤ socScanCost pni pm W' L' := by
  unfold socScanCost
  have hY : 2000 * (W + 1) ^ 6 ≤ 2000 * (W' + 1) ^ 6 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hW 1) 6)
  have h1 := Nat.mul_le_mul (Nat.add_le_add_right hL 1) (socScanStepCost_mono pni pm hY)
  have h2 : 10 ^ 7 * (L + 1) * (W + 1) ^ 6 ≤ 10 ^ 7 * (L' + 1) * (W' + 1) ^ 6 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right hL 1))
      (Nat.pow_le_pow_left (Nat.add_le_add_right hW 1) 6)
  omega

set_option maxHeartbeats 400000 in
open Classical in
/-- **The inner scan function** `socScanBody` on `[encGroup rs, socCsVal Ws, encGroup cs]` returns
`encGroup is` (`is.length ≤ n²`) with `gens is = socTerm (gens rs) (Ws.map gens) k ⊓ gens cs`,
`¬ (socTerm (gens rs) (Ws.map gens) k ⊓ gens cs ≤ gens rs)`, and
`socTerm (gens rs) (Ws.map gens) (k + 1) ⊓ gens cs ≤ gens rs` for some `k < Ws.length - 1`. -/
theorem socScan_spec {hni : NormalizedIntersection} {hmem : Membership}
    {P : Program} {sc it_sc sc_st mg le jni jm : ℕ}
    (hP : SocScanAt P sc it_sc sc_st mg le jni jm hni hmem)
    {H : Subgroup (Perm (Fin n))} {rs cs : List (Perm (Fin n))}
    {Ws : List (List (Perm (Fin n)))}
    (hnR : GI.Multicoset.Normalizes H (gens rs))
    (hs : SocChain H (gens rs) (Ws.map gens))
    (hCH : gens cs ≤ H) (hCR : ¬ (gens cs ≤ gens rs))
    (hcl : cs.length ≤ n ^ 2) :
    FunAll P sc (.list [encGroup rs, socCsVal Ws, encGroup cs]) (fun w cost =>
      (∃ is : List (Perm (Fin n)), w = encGroup is ∧ is.length ≤ n ^ 2 ∧
        ∃ k < Ws.length - 1,
          gens is = socTerm (gens rs) (Ws.map gens) k ⊓ gens cs ∧
          ¬ (socTerm (gens rs) (Ws.map gens) k ⊓ gens cs ≤ gens rs) ∧
          socTerm (gens rs) (Ws.map gens) (k + 1) ⊓ gens cs ≤ gens rs) ∧
      cost ≤ socScanCost (normalizedIntersectionPrim hni) (membershipPrim hmem)
        (Val.list [encGroup rs, socCsVal Ws, encGroup cs]).wt Ws.length) := by
  set c := Val.list [encGroup rs, socCsVal Ws, encGroup cs] with hcdef
  set W := c.wt with hWdef
  set k := Ws.length - 1 with hkdef
  set M := 320 * (n + 1) ^ 6 with hMdef
  have hrW : (encGroup rs).wt < W := wt_le_wt_list (by simp)
  have hwsW : (socCsVal Ws).wt < W := wt_le_wt_list (by simp)
  have hcW : (encGroup cs).wt < W := wt_le_wt_list (by simp)
  have hnW : n + 1 ≤ W := by
    have := S_le_wt_encGroup rs
    have : n + 1 ≤ (rs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hL_wt : Ws.length < W := by
    have h1 := length_lt_wt_list (Ws.map fun hs => Val.list (hs.map encPerm))
    simp only [List.length_map] at h1
    exact h1.trans hwsW
  have hW6 : W + 1 ≤ (W + 1) ^ 6 := Nat.le_self_pow (by decide) _
  have hn6 : (n + 1) ^ 6 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hcw_M : (encGroup cs).wt ≤ M := (wt_encGroup_sq hcl).trans (by omega)
  have h0 : SocScanValInv (gens rs) Ws (gens cs) 0 (encGroup cs) :=
    ⟨cs, rfl, hcl, soc_scan_init⟩
  have hwt_inv : ∀ j acc, j ≤ k → SocScanValInv (gens rs) Ws (gens cs) j acc → acc.wt ≤ M := by
    intro j acc _ hinv
    obtain ⟨is, rfl, hil, _⟩ := hinv
    exact (wt_encGroup_sq hil).trans (by omega)
  have hstep : ∀ j acc, j < k → SocScanValInv (gens rs) Ws (gens cs) j acc →
      FunAll P sc_st (.list [c, .nat j, acc]) (fun w cost =>
        SocScanValInv (gens rs) Ws (gens cs) (j + 1) w ∧
        cost ≤ socScanStepCost (normalizedIntersectionPrim hni) (membershipPrim hmem)
          (2000 * (W + 1) ^ 6)) := by
    intro j acc hj hinv
    have hacc_wt := hwt_inv j acc (by omega) hinv
    refine (socScanStep_spec hP.step hP.mg hP.le hP.ni hP.mem hnR hs hCH hCR hj hinv).mono
      fun w cost h => ⟨h.1, h.2.trans (socScanStepCost_mono _ _ ?_)⟩
    have h3 := wt_list3_le c (.nat j) acc
    have h4 := wt_nat_le j
    show (Val.list [c, .nat j, acc]).wt ≤ 2000 * (W + 1) ^ 6
    omega
  have hit := iter_spec hP.iter (c := c) (k := k) (M := M) h0 hwt_inv hstep
  -- Argument of `it_sc` inside `socScanBody`
  have dc := Det.var' (P := P) (env := [c]) (i := 0) (v := c) rfl
  have dws := Det.arg' (P := P) (vs := [encGroup rs, socCsVal Ws, encGroup cs]) (rest := [])
    (j := 1) (v := socCsVal Ws) rfl
  have dcv := Det.arg' (P := P) (vs := [encGroup rs, socCsVal Ws, encGroup cs]) (rest := [])
    (j := 2) (v := encGroup cs) rfl
  rw [← hcdef] at dws dcv
  have dk := Det.arith' (z := k) (P := P) (op := .sub) (Det.length dws) (Det.nat 1)
    (by simp [BinOp.eval, hkdef])
  have darg := Det.mk3 dc dk dcv
  have hw_arg := wt_list3_le c (.nat k) (encGroup cs)
  have hwk := wt_nat_le k
  have hwl := wt_nat_le Ws.length
  have darg' : Det P [c]
      (mk3 (.var 0) (.arith .sub (.length (arg 1)) (.nat 1)) (arg 2))
      (.list [c, .nat k, encGroup cs]) (100 * (W + 1) ^ 6) := by
    refine darg.mono ?_
    have e1 : (List.map (fun hs => Val.list (List.map encPerm hs)) Ws).length = Ws.length := by simp
    clear darg dk dcv dws dc hit hstep
    omega
  set B := socScanStepCost (normalizedIntersectionPrim hni) (membershipPrim hmem)
    (2000 * (W + 1) ^ 6) with hB
  set I := k * B + loopModK * (k + 1) * ((Val.list [c, .nat k, encGroup cs]).wt + k + M + 1)
    with hI
  have hit' : FunAll P it_sc (.list [c, .nat k, encGroup cs]) (fun w cost =>
      SocScanValInv (gens rs) Ws (gens cs) k w ∧ cost ≤ I) :=
    hit.mono fun w cost h => ⟨h.1, by
      have := h.2
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
      exact this⟩
  refine FunAll.intro hP.scan ((Det.call_funAll darg' hit').mono fun w cost h => ?_)
  obtain ⟨cb, ⟨⟨is, rfl, hil, hsinv⟩, hcb⟩, hcost⟩ := h
  have hsinv' : SocScanInv (gens rs) (Ws.map gens) (gens cs) ((Ws.map gens).length - 1) (gens is) := by
    simpa [hkdef] using hsinv
  obtain ⟨idx, hidx, hI_eq, hnot, hnext⟩ := soc_scan_done hs hCH hCR hsinv'
  simp only [List.length_map] at hidx
  refine ⟨⟨is, rfl, hil, idx, hidx, hI_eq, hnot, hnext⟩, ?_⟩
  have hwi : (encGroup is).wt ≤ M := (wt_encGroup_sq hil).trans (by omega)
  have hkL : k ≤ Ws.length := Nat.sub_le _ _
  have hloop_bound : loopModK * (k + 1) * ((Val.list [c, .nat k, encGroup cs]).wt + k + M + 1) ≤
      5 * 10 ^ 6 * (Ws.length + 1) * (W + 1) ^ 6 := by
    calc loopModK * (k + 1) * ((Val.list [c, .nat k, encGroup cs]).wt + k + M + 1) ≤
        loopModK * (Ws.length + 1) * (5000 * (W + 1) ^ 6) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by
            clear darg' darg dk dcv dws dc hit' hit hstep
            omega)
      _ = 5 * 10 ^ 6 * (Ws.length + 1) * (W + 1) ^ 6 := by simp only [loopModK]; ring
  have hkB : k * B ≤ (Ws.length + 1) * B := Nat.mul_le_mul_right _ (by omega)
  have h100 : 100 * (W + 1) ^ 6 + M + 1 ≤ 5 * 10 ^ 6 * (Ws.length + 1) * (W + 1) ^ 6 := by
    have : 1 ≤ Ws.length + 1 := Nat.succ_pos _
    calc 100 * (W + 1) ^ 6 + M + 1 ≤ 1000 * (W + 1) ^ 6 := by omega
      _ ≤ 5 * 10 ^ 6 * 1 * (W + 1) ^ 6 := by omega
      _ ≤ 5 * 10 ^ 6 * (Ws.length + 1) * (W + 1) ^ 6 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
  unfold socScanCost
  simp only [← hB]
  have h2y : 2 * (5 * 10 ^ 6 * (Ws.length + 1) * (W + 1) ^ 6) =
      10 ^ 7 * (Ws.length + 1) * (W + 1) ^ 6 := by ring
  omega

end GI.Impl
