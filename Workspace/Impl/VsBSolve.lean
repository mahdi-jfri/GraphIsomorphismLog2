module

public import Workspace.Proved.VsBSolveMath
public import Workspace.Impl.VsWProgKer
public import Workspace.Impl.VsWProgImg
public import Workspace.Lang.Lib.Search

@[expose] public section

/-!
# The solving program

On `[p, vs, u]`, with `u` in the span of `vs`, the coefficients `vsBSolveL p vs u`
(`vsBSolve_spec`): the relations among `vs ++ [u]`, the first with a nonzero last entry `r`,
the inverse of that entry, and `-r_m⁻¹ r`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved

/-- The main function, on `[p, vs, u]`. -/
def vsBSolveE (ker fnd inv lin : ℕ) : Expr :=
  .letE (.call ker (mk2 (arg 0) (.snoc (arg 1) (arg 2))))
  (.letE (.call fnd (mk2 (.length (arg 1)) (.var 1)))
  (.letE (.get (.var 1) (.var 2))
  (.letE (.call inv (mk2 (arg 0) (.get (.var 3) (.length (arg 1)))))
    (.call lin (.snoc (mk4 (arg 0) (.arith .sub (arg 0) (.var 4)) (.nat 0) (.var 3)) (.var 3))))))

/-- The test, on `[m, r]`: is `r_m` nonzero? -/
def vsBSolveTestE : Expr := .arith .lt (.nat 0) (.get (arg 1) (arg 0))

/-- The solving program at base `b` (57 functions). -/
def vsBSolveFuns (b : ℕ) : List Expr :=
  [vsBSolveE (b + 2) (b + 38) (b + 41) (b + 49), vsBSolveTestE] ++ vsWKerFuns (b + 2) ++
    findFuns (b + 38) (b + 1) ++ [vsInvF (b + 43) (b + 46), vsInvTestF] ++ rangeFuns (b + 43) ++
    findFuns (b + 46) (b + 42) ++ vsLinFuns (b + 49)

theorem vsBSolveFuns_length (b : ℕ) : (vsBSolveFuns b).length = 57 := by
  simp [vsBSolveFuns, vsWKerFuns, vsUnitPairsFuns, vsInsertAllFuns, findFuns, rangeFuns, vsLinFuns,
    loopFuns, foldlFuns, vsInsertFuns, vsUnitFuns, mapFuns, vsSiftFuns]

open Classical in
/-- The test as a function on values. -/
noncomputable def vsBSolveQ (m : ℕ) (v : Val) : Bool :=
  decide (∃ r : List ℕ, v = natList r ∧ 0 < r.getD m 0)

open Classical in
theorem vsBSolveQ_natList (m : ℕ) (r : List ℕ) :
    vsBSolveQ m (natList r) = decide (0 < r.getD m 0) := by
  unfold vsBSolveQ
  refine Bool.decide_congr ⟨fun ⟨r', h1, h2⟩ => ?_, fun h => ⟨r, rfl, h⟩⟩
  rw [vsQ_natList_injective h1]; exact h2

set_option maxHeartbeats 4000000 in
/-- **Solving.** On `[p, vs, u]` with `u` in the span of `vs`, the coefficients
`vsBSolveL p vs u`. -/
theorem vsBSolve_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsBSolveFuns b)) {p N d : ℕ}
    (hp : p.Prime) (hpN : p ≤ N) (hdN : d ≤ N) {vs : List (List ℕ)} (hvs : VsWFit p d vs)
    (hl : vs.length + 1 ≤ N) {u : List ℕ} (hu : VsWFit p d [u])
    (hsp : vsWV p d u ∈ vsWSp p d vs) :
    FunDet P b (.list [.nat p, vsWVs vs, natList u]) (natList (vsBSolveL p vs u))
      (10 ^ 9 * (N + 1) ^ 6) := by
  have h0 : P.funs[b]? = some (vsBSolveE (b + 2) (b + 38) (b + 41) (b + 49)) :=
    h.get (j := 0) (by rw [vsBSolveFuns_length]; omega)
  have h1 : P.funs[b + 1]? = some vsBSolveTestE := h.get (j := 1) (by rw [vsBSolveFuns_length]; omega)
  have hker : P.HasAt (b + 2) (vsWKerFuns (b + 2)) := h.block 2 rfl
  have hfd : P.HasAt (b + 38) (findFuns (b + 38) (b + 1)) := h.block 38 rfl
  have hinv : P.funs[b + 41]? = some (vsInvF (b + 43) (b + 46)) :=
    h.get (j := 41) (by rw [vsBSolveFuns_length]; omega)
  have htst : P.funs[b + 42]? = some vsInvTestF := h.get (j := 42) (by rw [vsBSolveFuns_length]; omega)
  have hrng : P.HasAt (b + 43) (rangeFuns (b + 43)) := h.block 43 rfl
  have hfd2 : P.HasAt (b + 46) (findFuns (b + 46) (b + 42)) := h.block 46 rfl
  have hlin : P.HasAt (b + 49) (vsLinFuns (b + 49)) := h.block 49 rfl
  have hfound := vsBSolve_found hp hvs hu hsp
  have hfit : VsWFit p d (vs ++ [u]) := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact hvs x hx
    · exact hu x hx
  set m := vs.length
  set K := vsWKer p (vs ++ [u])
  set r := vsBSolveR p vs u
  have hKfit := vsWKer_fit hp.one_lt hfit
  have hKl : K.length ≤ m + 1 := by
    have := vsWKer_length_le hp.one_lt hpN hdN hfit (by simp [m]; omega)
    simpa [m] using this
  have hfound' : (K.map natList).findIdx (vsBSolveQ m) = vsBSolveIdx p vs u := by
    rw [List.findIdx_map]
    simp only [Function.comp_def, vsBSolveQ_natList]
    rfl
  set idx := vsBSolveIdx p vs u
  have hidx : idx < K.length := hfound
  have hrK : (K.map natList)[idx]? = some (natList r) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hidx]
    simp only [r, vsBSolveR, Option.map_some, Option.some.injEq]
    rw [List.getD_eq_getElem _ _ hidx]
  have hrmem : r ∈ K := by
    simp only [r, vsBSolveR]; rw [List.getD_eq_getElem _ _ hidx]; exact List.getElem_mem _
  have hrfit := hKfit r hrmem
  have hrl : r.length = m + 1 := by rw [hrfit.2]; simp [m]
  set a := Val.list [.nat p, vsWVs vs, natList u]
  have g0 := Det.arg' (P := P) (rest := []) (vs := [.nat p, vsWVs vs, natList u]) (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := [.nat p, vsWVs vs, natList u]) (j := 1) rfl
  have g2 := Det.arg' (P := P) (rest := []) (vs := [.nat p, vsWVs vs, natList u]) (j := 2) rfl
  have esn : Val.list (vs.map natList ++ [natList u]) = vsWVs (vs ++ [u]) := by simp [vsWVs]
  have dsn := Det.snoc g1 g2
  rw [esn] at dsn
  have dK := Det.call (Det.mk2 g0 dsn) (vsWKer_spec hker hp.one_lt hpN hdN hfit (by simp [m]; omega))
  -- the test on each relation
  have htest : ∀ x ∈ K.map natList, FunDet P (b + 1) (.list [.nat m, x]) (boolVal (vsBSolveQ m x))
      (10 * (Val.list [.nat m, x]).wt + 100) := by
    intro x hx
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hx
    have hr'f := hKfit r' hr'
    have hr'l : m < r'.length := by rw [hr'f.2]; simp [m]
    have t0 := Det.arg' (P := P) (rest := []) (vs := [.nat m, natList r']) (j := 0) rfl
    have t1 := Det.arg' (P := P) (rest := []) (vs := [.nat m, natList r']) (j := 1) rfl
    have tg := Det.get' t1 t0 (v := .nat (r'.getD m 0)) (by
      show (r'.map Val.nat)[m]? = _
      simp [List.getD_eq_getElem _ _ hr'l, hr'l])
    have dlt := Det.arith' (op := .lt) (Det.nat (P := P) (env := [.list [.nat m, natList r']]) 0) tg
      (z := (decide (0 < r'.getD m 0)).toNat) (by
        simp only [GI.Machine.BinOp.eval]
        split_ifs <;> simp_all)
    rw [vsBSolveQ_natList]
    refine FunDet.intro h1 (dlt.mono ?_)
    have w1 : (Val.nat (r'.getD m 0)).wt < (natList r').wt := by
      apply wt_le_wt_list
      simp only [natList, List.mem_map]
      exact ⟨_, by rw [List.getD_eq_getElem _ _ hr'l]; exact List.getElem_mem _, rfl⟩
    have w2 : (natList r').wt < (Val.list [.nat m, natList r']).wt := wt_le_wt_list (by simp)
    have w3 : (Val.nat m).wt < (Val.list [.nat m, natList r']).wt := wt_le_wt_list (by simp)
    have := wt_nat_le 0; have := wt_nat_le 1
    have := wt_nat_le (r'.getD m 0)
    have hb : (decide (0 < r'.getD m 0)).toNat ≤ 1 := by cases decide (0 < r'.getD m 0) <;> simp
    have := wt_nat_le (decide (0 < r'.getD m 0)).toNat
    omega
  -- weights
  have hKb : VsWBnd N K := fun t ht => ⟨fun y hy => ((hKfit t ht).1 y hy).le.trans hpN,
    by rw [(hKfit t ht).2]; simp [m]; omega⟩
  have wK := wt_vsWVs_le hKb (by omega)
  have hvb : VsWBnd N vs := VsWFit.bnd hvs hpN hdN
  have wvs := wt_vsWVs_le hvb (by omega)
  have hu' := hu u (List.mem_singleton_self _)
  have wu := wt_natList_le_sq (B := N) (xs := u) (fun y hy => (hu'.1 y hy).le.trans hpN)
    (by rw [hu'.2]; exact hdN)
  have wr := wt_natList_le_sq (B := N) (xs := r) (fun y hy => (hrfit.1 y hy).le.trans hpN)
    (by rw [hrl]; omega)
  have hrm : r.getD m 0 < p := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hrfit.1 _ (List.getElem_mem _)
  set ci := vsInv p (r.getD m 0)
  have hci : ci ≤ p := vsInv_le p _
  -- the find
  have hfind : FunDet P (b + 38) (.list [.nat m, .list (K.map natList)]) (.nat idx)
      (10 ^ 6 * (N + 1) ^ 4) := by
    refine (find_spec hfd htest).mono fun w c hw => ⟨by rw [hw.1, hfound'], hw.2.trans ?_⟩
    have hB : ∀ x ∈ K.map natList, 10 * (Val.list [.nat m, x]).wt + 100 ≤ 10 * (2 * (m + 2 +
        (vsWVs K).wt) + 6) + 100 := by
      intro x hx
      have := wt_list2_le (.nat m) x
      have := wt_nat_le m
      have : x.wt < (vsWVs K).wt := wt_le_wt_list hx
      omega
    have hs := List.sum_le_card_nsmul ((K.map natList).map fun x => 10 * (Val.list [.nat m, x]).wt + 100)
      (10 * (2 * (m + 2 + (vsWVs K).wt) + 6) + 100) (by
        intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hB x hx)
    simp only [List.length_map, smul_eq_mul] at hs
    have w2 := wt_list2_le (.nat m) (.list (K.map natList))
    have := wt_nat_le m
    have eK : (vsWVs K).wt = (Val.list (K.map natList)).wt := rfl
    have q1 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h1 : K.length * (10 * (2 * (m + 2 + (vsWVs K).wt) + 6) + 100) ≤
        (N + 1) * (10 * (2 * (N + 2 + 15 * (N + 1) ^ 3) + 6) + 100) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : loopModK * ((K.map natList).length + 1) * ((Val.list [.nat m, .list (K.map natList)]).wt +
        2 * (K.map natList).length + 3) ≤ loopModK * (N + 2) * (2 * (N + 2 + 15 * (N + 1) ^ 3) + 6 + 2 * N + 6) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by simp; omega)) (by simp only [List.length_map]; omega)
    have q3 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have e1 : (N + 1) * (10 * (2 * (N + 2 + 15 * (N + 1) ^ 3) + 6) + 100) ≤ 1000 * (N + 1) ^ 4 := by
      have : 10 * (2 * (N + 2 + 15 * (N + 1) ^ 3) + 6) + 100 ≤ 1000 * (N + 1) ^ 3 := by omega
      calc _ ≤ (N + 1) * (1000 * (N + 1) ^ 3) := Nat.mul_le_mul_left _ this
        _ = 1000 * (N + 1) ^ 4 := by ring
    have e2 : loopModK * (N + 2) * (2 * (N + 2 + 15 * (N + 1) ^ 3) + 6 + 2 * N + 6) ≤
        10 ^ 5 * (N + 1) ^ 4 := by
      have : 2 * (N + 2 + 15 * (N + 1) ^ 3) + 6 + 2 * N + 6 ≤ 50 * (N + 1) ^ 3 := by omega
      calc _ ≤ 1000 * (2 * (N + 1)) * (50 * (N + 1) ^ 3) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) this
        _ = 10 ^ 5 * (N + 1) ^ 4 := by ring
    omega
  -- the main chain
  set Kv := vsWVs K
  have e1v : ∀ rest, Det P (a :: rest) (arg 1) (vsWVs vs) _ := fun rest =>
    Det.arg' (P := P) (rest := rest) (vs := [.nat p, vsWVs vs, natList u]) (j := 1) rfl
  have e0v : ∀ rest, Det P (a :: rest) (arg 0) (.nat p) _ := fun rest =>
    Det.arg' (P := P) (rest := rest) (vs := [.nat p, vsWVs vs, natList u]) (j := 0) rfl
  have elen : ∀ rest, Det P (a :: rest) (.length (arg 1)) (.nat m) _ := fun rest => by
    have := Det.length (e1v rest)
    rwa [show (vs.map natList).length = m by simp [m]] at this
  have dfind := Det.call (Det.mk2 (elen [Kv]) (Det.var' (P := P) (env := [a, Kv]) (i := 1) rfl)) hfind
  have dr := Det.get' (Det.var' (P := P) (env := [a, Kv, .nat idx]) (i := 1) rfl)
    (Det.var' (P := P) (env := [a, Kv, .nat idx]) (i := 2) rfl) hrK
  have hrm' : (r.map Val.nat)[m]? = some (.nat (r.getD m 0)) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]; rfl
  have dm := Det.get' (Det.var' (P := P) (env := [a, Kv, .nat idx, natList r]) (i := 3) rfl)
    (elen [Kv, .nat idx, natList r]) hrm'
  have dci := Det.call (Det.mk2 (e0v [Kv, .nat idx, natList r]) dm)
    (vsInv_spec hinv hrng hfd2 htst hpN (show r.getD m 0 ≤ N by omega))
  set env4 := [a, Kv, Val.nat idx, natList r, Val.nat ci]
  have dsub := Det.arith' (op := .sub) (e0v [Kv, .nat idx, natList r, .nat ci])
    (Det.var' (P := P) (env := env4) (i := 4) rfl) (z := p - ci) rfl
  have dv3 := Det.var' (P := P) (env := env4) (i := 3) rfl
  have dl := Det.call (Det.snoc (Det.mk4 (e0v [Kv, .nat idx, natList r, .nat ci]) dsub (Det.nat 0) dv3) dv3)
    (vsLin_spec hlin (N := N) (a := p - ci) (b := 0) (v := r) (u := r) hp.pos
      (fun y hy => (hrfit.1 y hy).le.trans hpN) (fun y hy => (hrfit.1 y hy).le.trans hpN)
      (by omega) (by omega) le_rfl hpN (by omega) (by omega))
  have dall := Det.letE dK (Det.letE dfind (Det.letE dr (Det.letE dci dl)))
  refine FunDet.intro h0 (dall.mono ?_)
  have hout := vsBSolve_comb hp hvs hu hsp
  have wo := wt_natList_le_sq (B := N) (xs := vsBSolveL p vs u) (fun y hy => (hout.1 y hy).le.trans hpN)
    (by rw [hout.2.1]; omega)
  have wa := wt_list3_le (.nat p) (vsWVs vs) (natList u)
  have ea : (Val.list [.nat p, vsWVs vs, natList u]).wt = a.wt := rfl
  have wsn := wt_list_snoc_le (vs.map natList) (natList u)
  have esn' : (Val.list (vs.map natList)).wt = (vsWVs vs).wt := rfl
  have esn2 : (Val.list (vs.map natList ++ [natList u])).wt = (vsWVs (vs ++ [u])).wt := by rw [esn]
  have w2 := wt_list2_le (.nat p) (vsWVs (vs ++ [u]))
  have w2b := wt_list2_le (.nat m) Kv
  have w2c := wt_list2_le (.nat p) (.nat (r.getD m 0))
  have w4 := wt_list4_le (.nat p) (.nat (p - ci)) (.nat 0) (natList r)
  have w5 := wt_list_snoc_le [Val.nat p, .nat (p - ci), .nat 0, natList r] (natList r)
  have eKv : Kv.wt = (vsWVs K).wt := rfl
  have wr2 : (Val.nat (r.getD m 0)).wt < (natList r).wt := by
    apply wt_le_wt_list
    simp only [natList, List.mem_map]
    exact ⟨_, by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _, rfl⟩
  have := wt_nat_le p; have := wt_nat_le m; have := wt_nat_le idx; have := wt_nat_le ci
  have := wt_nat_le (p - ci); have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2
  have := wt_nat_le (r.getD m 0)
  have hidxN : idx ≤ N := by omega
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have q45 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have q56 : (N + 1) ^ 5 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have wKa : (vsWVs (vs ++ [u])).wt ≤ 15 * (N + 1) ^ 3 := by
    have := wt_vsWVs_le (VsWFit.bnd hfit hpN hdN) (by simp [m]; omega)
    omega
  have f1 : (natList (vsLin p (p - ci) 0 r r)).wt = (natList (vsBSolveL p vs u)).wt := rfl
  have f2 : (Val.list (K.map natList)).wt = (vsWVs K).wt := rfl
  have f3 : (Val.list (r.map Val.nat)).wt = (natList r).wt := rfl
  have f4 : (Val.nat (vsInv p (r.getD m 0))).wt = (Val.nat ci).wt := rfl
  have f5 : vsInv p (r.getD m 0) = ci := rfl
  omega

end GI.Impl
