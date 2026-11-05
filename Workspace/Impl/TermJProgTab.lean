module

public import Workspace.Impl.TermJProgYg5

@[expose] public section

/-!
# The local generators read off the `N`-test table (program)

The diagonal entry `(x_a, x_a)` of the `N`-test table is `r ⟨gs⟩ = Aut_N(x_a)`. `tmJLgList O`
lists the pairs `(a, g)` for `g ∈ 1 :: gs`, row after row; these are the local generators `g_k`
of the sum map. `tmJ_lg_spec`: on `[us, q, m]` the program `tmJLgF` returns
`tmJLgVal (tmJLgList O)`, each pair as `[a, g]`.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)

variable {m q : ℕ}

/-- The pairs of one row. -/
def tmJLgOf (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) (a : Fin q) :
    List (Fin q × Perm (Fin m)) :=
  match O a a with
  | some (_, gs) => (1 :: gs).map fun g => (a, g)
  | none => []

/-- All pairs. -/
def tmJLgList (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) :
    List (Fin q × Perm (Fin m)) :=
  ((List.finRange q).map (tmJLgOf O)).flatten

/-- The value of a list of pairs. -/
def tmJLgVal (l : List (Fin q × Perm (Fin m))) : Val :=
  .list (l.map fun p => .list [.nat p.1, encPerm p.2])

/-- One pair: on `[a, g]`, `[a, g]`. -/
def tmJLgEF : Expr := mk2 (arg 0) (arg 1)

/-- The pairs of one row: on `[[us, q], a]`, map `tmJLgEF` with context `a` over the stored list
`us[a (2q) + a][1][1]`. -/
def tmJLgRowF (mp : ℕ) : Expr :=
  .call mp (mk2 (arg 1)
    (.get (.get (.get (.get (arg 0) (.nat 0)) (.arith .add (.arith .mul (arg 1)
      (.arith .mul (.nat 2) (.get (arg 0) (.nat 1)))) (arg 1))) (.nat 1)) (.nat 1)))

/-- On `[us, q, m]`: all pairs. -/
def tmJLgF (rg tbR fl : ℕ) : Expr :=
  .call fl (.call tbR (mk2 (mk2 (arg 0) (arg 1)) (.call rg (arg 1))))

theorem tmJ_lgE_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some tmJLgEF) (a : ℕ) (v : Val) :
    FunDet P f (.list [.nat a, v]) (.list [.nat a, v]) (10 * ((Val.list [.nat a, v]).wt + 5)) := by
  refine FunDet.intro hf ?_
  have d0 := Det.arg' (P := P) (vs := [.nat a, v]) (rest := []) (j := 0) (v := .nat a) rfl
  have d1 := Det.arg' (P := P) (vs := [.nat a, v]) (rest := []) (j := 1) (v := v) rfl
  refine (Det.mk2 d0 d1).mono ?_
  have := wt_list2_le (Val.nat a) v
  have h1 : (Val.nat a).wt < (Val.list [.nat a, v]).wt := wt_le_wt_list (by simp)
  have h2 : v.wt < (Val.list [.nat a, v]).wt := wt_le_wt_list (by simp)
  omega

/-- The cost of one row, in `V = wt us + (m + 1) (q + 1)`. -/
def tmJLgRowK (V : ℕ) : ℕ := 10 ^ 6 * V ^ 4

theorem tmJ_lgRow_spec {P : Program} {f mp e : ℕ} (hf : P.funs[f]? = some (tmJLgRowF mp))
    (hmp : P.HasAt mp (mapFuns mp e)) (he : P.funs[e]? = some tmJLgEF)
    (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) (a : Fin q)
    {r : Perm (Fin m)} {gs : List (Perm (Fin m))} (hO : O a a = some (r, gs)) (us : List Val)
    (hu : us[(a : ℕ) * (2 * q) + a]? = some (.list [encPerm r, encGroup gs])) :
    FunDet P f (.list [.list [.list us, .nat q], .nat a]) (tmJLgVal (tmJLgOf O a))
      (tmJLgRowK ((Val.list us).wt + (m + 1) * (q + 1))) := by
  refine FunDet.intro hf ?_
  unfold tmJLgRowF
  set V := (Val.list us).wt + (m + 1) * (q + 1) with hV
  have d0 := Det.arg' (P := P) (vs := [.list [.list us, .nat q], .nat a]) (rest := [])
    (j := 0) (v := .list [.list us, .nat q]) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [.list us, .nat q], .nat a]) (rest := [])
    (j := 1) (v := .nat a) rfl
  have dus := Det.get' d0 (Det.nat 0) (vs := [.list us, .nat q]) (v := .list us) rfl
  have dq := Det.get' d0 (Det.nat 1) (vs := [.list us, .nat q]) (v := .nat q) rfl
  have d2q := Det.arith' (op := .mul) (Det.nat 2) dq (z := 2 * q) rfl
  have dmul := Det.arith' (op := .mul) d1 d2q (z := (a : ℕ) * (2 * q)) rfl
  have didx := Det.arith' (op := .add) dmul d1 (z := (a : ℕ) * (2 * q) + a) rfl
  have de := Det.get' dus didx hu
  have dg := Det.get' de (Det.nat 1) (vs := [encPerm r, encGroup gs]) (v := encGroup gs) rfl
  have dL := Det.get' dg (Det.nat 1) (vs := [.nat m, .list ((1 :: gs).map encPerm)])
    (v := .list ((1 :: gs).map encPerm)) rfl
  have hB : ∀ g : Perm (Fin m), 10 * ((Val.list [.nat a, encPerm g]).wt + 5) ≤
      10 * (2 * ((a : ℕ) + 2 + 4 * (m + 1) ^ 2) + 11) := by
    intro g
    have := wt_list2_le (Val.nat a) (encPerm g)
    have := wt_nat_le a
    have := wt_encPerm_le g
    omega
  have hM := mapList_spec hmp (1 :: gs) encPerm (fun g => .list [.nat a, encPerm g])
    (c := .nat a) (fun g _ g' _ hg => by rw [encPerm_injective hg])
    (fun g _ => (tmJ_lgE_spec he a (encPerm g)).mono (hB g))
  have dall := Det.call (Det.mk2 d1 dL) hM
  have hval : Val.list ((1 :: gs).map fun g => Val.list [.nat a, encPerm g]) =
      tmJLgVal (tmJLgOf O a) := by
    simp only [tmJLgVal, tmJLgOf, hO, List.map_map]
    rfl
  rw [hval] at dall
  refine dall.mono ?_
  clear_value V
  clear dall hM dL dg de didx dmul d2q dq dus d1 d0
  -- the cost
  have hL := tmJYg_row_wt hu
  have hlen := length_lt_wt_list ((1 :: gs).map encPerm)
  simp only [List.length_map] at hlen
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hm1 : m + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hV1 : 1 ≤ V := by omega
  have hmV : (m + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have ha := a.2
  have haq : (a : ℕ) * (2 * q) ≤ 2 * V ^ 2 := by
    have : (a : ℕ) * (2 * q) ≤ V * (2 * V) := Nat.mul_le_mul (by omega) (by omega)
    have e : V * (2 * V) = 2 * V ^ 2 := by ring
    omega
  have hV2 : V ≤ V ^ 2 := Nat.le_self_pow (by norm_num) _
  have hV23 : V ^ 2 ≤ V ^ 3 := Nat.pow_le_pow_right hV1 (by norm_num)
  have hV34 : V ^ 3 ≤ V ^ 4 := Nat.pow_le_pow_right hV1 (by norm_num)
  have he' : (Val.list [encPerm r, encGroup gs]).wt < (Val.list us).wt :=
    wt_le_wt_list (List.mem_of_getElem? hu)
  have hg : (encGroup gs).wt < (Val.list [encPerm r, encGroup gs]).wt := wt_le_wt_list (by simp)
  have wa := wt_nat_le a
  have wq := wt_nat_le q
  have w2 := wt_nat_le 2
  have wul := wt_list2_le (.list us) (.nat q)
  have wl2 := wt_list2_le (.nat a) (.list ((1 :: gs).map encPerm))
  have win := wt_list2_le (.list [.list us, .nat q]) (.nat a)
  -- the output weight
  have wout : (tmJLgVal (tmJLgOf O a)).wt ≤ V * (2 * (2 * (V + 2 + 4 * V ^ 2) + 6) + 1) + 4 := by
    rw [← hval]
    have := tmJ_wt_list_le (vs := (1 :: gs).map fun g => Val.list [.nat a, encPerm g])
      (E := 2 * (V + 2 + 4 * V ^ 2) + 6) (by
        intro v hv
        obtain ⟨g, -, rfl⟩ := List.mem_map.1 hv
        have := wt_list2_le (Val.nat a) (encPerm g)
        have := wt_encPerm_le g
        omega)
    simp only [List.length_map] at this
    have : (1 :: gs).length * (2 * (2 * (V + 2 + 4 * V ^ 2) + 6) + 1) ≤
        V * (2 * (2 * (V + 2 + 4 * V ^ 2) + 6) + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have e1 : V * (2 * (2 * (V + 2 + 4 * V ^ 2) + 6) + 1) = 4 * V ^ 2 + 16 * V ^ 3 + 21 * V := by
    ring
  have P1 : (1 :: gs).length * (10 * (2 * ((a : ℕ) + 2 + 4 * (m + 1) ^ 2) + 11)) ≤
      V * (10 * (2 * (V + 2 + 4 * V ^ 2) + 11)) := Nat.mul_le_mul (by omega) (by omega)
  have e2 : V * (10 * (2 * (V + 2 + 4 * V ^ 2) + 11)) = 20 * V ^ 2 + 80 * V ^ 3 + 150 * V := by
    ring
  have P2 : mapK * ((1 :: gs).length + 1) * ((Val.list [.nat a,
      .list ((1 :: gs).map encPerm)]).wt + (tmJLgVal (tmJLgOf O a)).wt + 1) ≤
      1000 * V * (200 * V ^ 3) := by
    unfold mapK
    refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) ?_
    omega
  have e3 : 1000 * V * (200 * V ^ 3) = 200000 * V ^ 4 := by ring
  have wout' : (Val.list ((1 :: gs).map fun g => Val.list [.nat a, encPerm g])).wt ≤
      V * (2 * (2 * (V + 2 + 4 * V ^ 2) + 6) + 1) + 4 := by rw [hval]; exact wout
  show _ ≤ 10 ^ 6 * V ^ 4
  omega

/-- The weight of the pairs of one row. -/
theorem tmJ_lgOf_wt (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m))))
    (hloc : ∀ a, ∃ r gs, O a a = some (r, gs)) (us : List Val)
    (hus : ∀ a a' : Fin q, us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (O a a'))) (a : Fin q) :
    (tmJLgVal (tmJLgOf O a)).wt ≤ 50 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 3 := by
  obtain ⟨r, gs, hO⟩ := hloc a
  have hu : us[(a : ℕ) * (2 * q) + a]? = some (.list [encPerm r, encGroup gs]) := by
    rw [hus a a, hO]; rfl
  set V := (Val.list us).wt + (m + 1) * (q + 1) with hV
  clear_value V
  have hL := tmJYg_row_wt hu
  have hlen := length_lt_wt_list ((1 :: gs).map encPerm)
  simp only [List.length_map] at hlen
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hm1 : m + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hmV : (m + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have ha := a.2
  have hval : tmJLgVal (tmJLgOf O a) =
      Val.list ((1 :: gs).map fun g => Val.list [.nat a, encPerm g]) := by
    simp only [tmJLgVal, tmJLgOf, hO, List.map_map]; rfl
  rw [hval]
  have := tmJ_wt_list_le (vs := (1 :: gs).map fun g => Val.list [.nat a, encPerm g])
    (E := 2 * (V + 2 + 4 * V ^ 2) + 6) (by
      intro v hv
      obtain ⟨g, -, rfl⟩ := List.mem_map.1 hv
      have := wt_list2_le (Val.nat a) (encPerm g)
      have := wt_encPerm_le g
      have := wt_nat_le a
      omega)
  simp only [List.length_map] at this
  have h1 : (1 :: gs).length * (2 * (2 * (V + 2 + 4 * V ^ 2) + 6) + 1) ≤
      V * (2 * (2 * (V + 2 + 4 * V ^ 2) + 6) + 1) := Nat.mul_le_mul_right _ (by omega)
  have e1 : V * (2 * (2 * (V + 2 + 4 * V ^ 2) + 6) + 1) = 4 * V ^ 2 + 16 * V ^ 3 + 21 * V := by
    ring
  have hV1 : 1 ≤ V := by omega
  have hV2 : V ≤ V ^ 2 := Nat.le_self_pow (by norm_num) _
  have hV23 : V ^ 2 ≤ V ^ 3 := Nat.pow_le_pow_right hV1 (by norm_num)
  omega

/-- The value of the flattened list. -/
theorem tmJLgVal_flatten (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) :
    Val.list (((List.finRange q).map fun a =>
      (tmJLgOf O a).map fun p => Val.list [.nat p.1, encPerm p.2]).flatten) =
      tmJLgVal (tmJLgList O) := by
  simp only [tmJLgVal, tmJLgList, List.map_flatten, List.map_map]
  rfl

/-- The cost of all pairs. -/
def tmJLgK (V : ℕ) : ℕ := 10 ^ 13 * V ^ 12

structure TmJLgAt (P : Program) (f rg tbR row mp e fl app : ℕ) : Prop where
  hf : P.funs[f]? = some (tmJLgF rg tbR fl)
  hrg : P.HasAt rg (rangeFuns rg)
  htbR : P.HasAt tbR (mapFuns tbR row)
  hrow : P.funs[row]? = some (tmJLgRowF mp)
  hmp : P.HasAt mp (mapFuns mp e)
  he : P.funs[e]? = some tmJLgEF
  hfl : P.funs[fl]? = some (tmJFlatF (fl + 1))
  hflF : P.HasAt (fl + 1) (foldlFuns (fl + 1) (fl + 4))
  hst : P.funs[fl + 4]? = some (tmJFlatStepF app)
  happ : P.HasAt app (appendFuns app)

/-- **All local generators of the sum map.** -/
theorem tmJ_lg_spec {P : Program} {f rg tbR row mp e fl app : ℕ}
    (hA : TmJLgAt P f rg tbR row mp e fl app)
    (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m))))
    (hloc : ∀ a, ∃ r gs, O a a = some (r, gs)) (us : List Val)
    (hus : ∀ a a' : Fin q, us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (O a a'))) :
    FunDet P f (.list [.list us, .nat q]) (tmJLgVal (tmJLgList O))
      (tmJLgK ((Val.list us).wt + (m + 1) * (q + 1))) := by
  refine FunDet.intro hA.hf ?_
  unfold tmJLgF
  set V := (Val.list us).wt + (m + 1) * (q + 1) with hV
  have d0 := Det.arg' (P := P) (vs := [.list us, .nat q]) (rest := []) (j := 0) (v := .list us) rfl
  have d1 := Det.arg' (P := P) (vs := [.list us, .nat q]) (rest := []) (j := 1) (v := .nat q) rfl
  have dr := Det.call d1 (tmJ_range_det hA.hrg q)
  have hT := tabulate_spec hA.htbR (c := .list [.list us, .nat q])
    (F := fun a : Fin q => tmJLgVal (tmJLgOf O a)) (B := tmJLgRowK V) (fun a => by
      obtain ⟨r, gs, hO⟩ := hloc a
      have hu : us[(a : ℕ) * (2 * q) + a]? = some (.list [encPerm r, encGroup gs]) := by
        rw [hus a a, hO]; rfl
      exact tmJ_lgRow_spec hA.hrow hA.hmp hA.he O a hO us hu)
  have dt := Det.call (Det.mk2 (Det.mk2 d0 d1) dr) hT
  have hrows : Val.list ((List.finRange q).map fun a => tmJLgVal (tmJLgOf O a)) =
      Val.list (((List.finRange q).map fun a =>
        (tmJLgOf O a).map fun p => Val.list [.nat p.1, encPerm p.2]).map Val.list) := by
    simp only [List.map_map]; rfl
  rw [hrows] at dt
  have hF := tmJ_flat_spec hA.hfl hA.hflF hA.hst hA.happ ((List.finRange q).map fun a =>
    (tmJLgOf O a).map fun p => Val.list [.nat p.1, encPerm p.2])
  have dall := Det.call dt hF
  rw [tmJLgVal_flatten] at dall
  refine dall.mono ?_
  clear_value V
  clear dall hF dt hT dr d1 d0
  -- the cost
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hV1 : 1 ≤ V := by omega
  have hpow : ∀ i j, i ≤ j → V ^ i ≤ V ^ j := fun i j h => Nat.pow_le_pow_right hV1 h
  have hV2 : V ≤ V ^ 2 := Nat.le_self_pow (by norm_num) _
  have wrow := tmJ_lgOf_wt O hloc us hus
  simp only [← hV] at wrow
  have wR : (Val.list ((List.finRange q).map fun a => tmJLgVal (tmJLgOf O a))).wt ≤
      101 * V ^ 4 + 4 := by
    have := tmJ_wt_list_le (vs := (List.finRange q).map fun a => tmJLgVal (tmJLgOf O a))
      (E := 50 * V ^ 3) (by
        intro v hv
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hv
        exact wrow a)
    simp only [List.length_map, List.length_finRange] at this
    have h1 : q * (2 * (50 * V ^ 3) + 1) ≤ V * (101 * V ^ 3) := by
      have : 2 * (50 * V ^ 3) + 1 ≤ 101 * V ^ 3 := by have := hpow 0 3 (by norm_num); simp at this; omega
      exact Nat.mul_le_mul (by omega) this
    have e : V * (101 * V ^ 3) = 101 * V ^ 4 := by ring
    omega
  rw [hrows] at wR
  have wid := wt_ids_le q
  have wus := wt_list2_le (.list us) (.nat q)
  have wq := wt_nat_le q
  have wc := wt_list2_le (.list [.list us, .nat q]) (encFun fun i : Fin q => (i : ℕ))
  have hqV : (q + 1) ^ 3 ≤ V ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have P1 : q * tmJLgRowK V ≤ 10 ^ 6 * V ^ 5 := by
    unfold tmJLgRowK
    calc q * (10 ^ 6 * V ^ 4) ≤ V * (10 ^ 6 * V ^ 4) := Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 6 * V ^ 5 := by ring
  have P2 : mapK * (q + 1) * ((Val.list [.list [.list us, .nat q],
      encFun fun i : Fin q => (i : ℕ)]).wt + (Val.list (((List.finRange q).map fun a =>
        (tmJLgOf O a).map fun p => Val.list [.nat p.1, encPerm p.2]).map Val.list)).wt + 1) ≤
      1000 * V * (200 * V ^ 4) := by
    unfold mapK
    refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) ?_
    have := hpow 2 4 (by norm_num)
    have := hpow 1 4 (by norm_num)
    have : (q + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have e2 : 1000 * V * (200 * V ^ 4) = 200000 * V ^ 5 := by ring
  have P3 : tmJFlatK (Val.list (((List.finRange q).map fun a =>
      (tmJLgOf O a).map fun p => Val.list [.nat p.1, encPerm p.2]).map Val.list)).wt ≤
      10 ^ 6 * (102 * V ^ 4 + 5) ^ 3 := by
    unfold tmJFlatK
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have P4 : 10 ^ 6 * (102 * V ^ 4 + 5) ^ 3 ≤ 10 ^ 6 * (107 * V ^ 4) ^ 3 := by
    have := hpow 0 4 (by norm_num); simp at this
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have e4 : 10 ^ 6 * (107 * V ^ 4) ^ 3 = 1225043000000 * V ^ 12 := by ring
  have h5 := hpow 5 12 (by norm_num)
  have h3 := hpow 3 12 (by norm_num)
  have wrg : 10000 * (q + 1) ^ 3 ≤ 10000 * V ^ 12 := Nat.mul_le_mul_left _ (hqV.trans h3)
  have wtot : (Val.list [.list us, .nat q]).wt ≤ 20 * V ^ 12 := by
    have := hpow 1 12 (by norm_num); simp at this; omega
  have wfl := tmJ_wt_flatten_le ((List.finRange q).map fun a =>
    (tmJLgOf O a).map fun p => Val.list [.nat p.1, encPerm p.2])
  rw [tmJLgVal_flatten] at wfl
  have h4 := hpow 4 12 (by norm_num)
  have hq2 : (q + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 := hpow 2 12 (by norm_num)
  show _ ≤ 10 ^ 13 * V ^ 12
  omega

end GI.Impl
