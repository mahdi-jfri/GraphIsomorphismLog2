module

public import Workspace.Impl.TermJProgTab

@[expose] public section

/-!
# The lifted transpositions of two different rows (program)

`tmJTlList O`: the triples `(a, a', b)` with `a ≠ a'` and `O a a' = b ⟨…⟩` (the off-diagonal
entries of the `N`-test table), for `t < q²` in order (`a = t / q`, `a' = t % q`).
`tmJ_tl_spec`: on `[us, q]` the program returns `tmJTlVal (tmJTlList O)`, each triple as
`[a, a', b]`.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)

variable {m q : ℕ}

/-- The triple of an index, if any. -/
def tmJTlOf (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) (t : Fin (q * q)) :
    List (Fin q × Fin q × Perm (Fin m)) :=
  if tmJFst t = tmJSnd t then [] else
    match O (tmJFst t) (tmJSnd t) with
    | some (b, _) => [(tmJFst t, tmJSnd t, b)]
    | none => []

/-- All triples. -/
def tmJTlList (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) :
    List (Fin q × Fin q × Perm (Fin m)) :=
  ((List.finRange (q * q)).map (tmJTlOf O)).flatten

/-- The value of one triple. -/
def tmJTrVal (x : Fin q × Fin q × Perm (Fin m)) : Val := .list [.nat x.1, .nat x.2.1, encPerm x.2.2]

/-- The value of a list of triples. -/
def tmJTlVal (l : List (Fin q × Fin q × Perm (Fin m))) : Val := .list (l.map tmJTrVal)

/-- `q`, read from `[[us, q], t]`. -/
def tmJTlQE : Expr := .get (arg 0) (.nat 1)

/-- On `[[us, q], t]`: `[]` if `a = a'` or the entry `e = us[a (2q) + a']` is empty, else
`[[a, a', e[0]]]`. -/
def tmJTlEF : Expr :=
  .letE (.get (.get (arg 0) (.nat 0)) (.arith .add (.arith .mul (.arith .div (arg 1) tmJTlQE)
    (.arith .mul (.nat 2) tmJTlQE)) (.arith .mod (arg 1) tmJTlQE)))
  (.ite (.arith .add (.arith .sub (.arith .div (arg 1) tmJTlQE) (.arith .mod (arg 1) tmJTlQE))
      (.arith .sub (.arith .mod (arg 1) tmJTlQE) (.arith .div (arg 1) tmJTlQE)))
    (.ite (.length (.var 1))
      (.snoc .nil (mk3 (.arith .div (arg 1) tmJTlQE) (.arith .mod (arg 1) tmJTlQE)
        (.get (.var 1) (.nat 0))))
      .nil)
    .nil)

theorem tmJ_tlE_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some tmJTlEF)
    (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) (us : List Val)
    (hus : ∀ a a' : Fin q, us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (O a a')))
    (t : Fin (q * q)) :
    FunDet P f (.list [.list [.list us, .nat q], .nat t]) (tmJTlVal (tmJTlOf O t))
      (1000 * ((Val.list us).wt + q * q + 20)) := by
  refine FunDet.intro hf ?_
  unfold tmJTlEF tmJTlQE
  have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact t.elim0)
  have d0 := Det.arg' (P := P) (vs := [.list [.list us, .nat q], .nat t]) (rest := [])
    (j := 0) (v := .list [.list us, .nat q]) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [.list us, .nat q], .nat t]) (rest := [])
    (j := 1) (v := .nat t) rfl
  have dus := Det.get' d0 (Det.nat 0) (vs := [.list us, .nat q]) (v := .list us) rfl
  have dq := Det.get' d0 (Det.nat 1) (vs := [.list us, .nat q]) (v := .nat q) rfl
  have ddiv := Det.arith' (op := .div) d1 dq (z := (tmJFst t : ℕ)) rfl
  have dmod := Det.arith' (op := .mod) d1 dq (z := (tmJSnd t : ℕ)) rfl
  have d2q := Det.arith' (op := .mul) (Det.nat 2) dq (z := 2 * q) rfl
  have dmul := Det.arith' (op := .mul) ddiv d2q (z := (tmJFst t : ℕ) * (2 * q)) rfl
  have didx := Det.arith' (op := .add) dmul dmod
    (z := (tmJFst t : ℕ) * (2 * q) + (tmJSnd t : ℕ)) rfl
  have de := Det.get' dus didx (hus (tmJFst t) (tmJSnd t))
  -- the body, in the environment extended by the entry
  have e0 := Det.arg' (P := P) (vs := [.list [.list us, .nat q], .nat t])
    (rest := [tmJEntVal (O (tmJFst t) (tmJSnd t))]) (j := 0) (v := .list [.list us, .nat q]) rfl
  have e1 := Det.arg' (P := P) (vs := [.list [.list us, .nat q], .nat t])
    (rest := [tmJEntVal (O (tmJFst t) (tmJSnd t))]) (j := 1) (v := .nat t) rfl
  have eq' := Det.get' e0 (Det.nat 1) (vs := [.list us, .nat q]) (v := .nat q) rfl
  have ediv := Det.arith' (op := .div) e1 eq' (z := (tmJFst t : ℕ)) rfl
  have emod := Det.arith' (op := .mod) e1 eq' (z := (tmJSnd t : ℕ)) rfl
  have dcnd := Det.arith' (op := .add)
    (Det.arith' (op := .sub) ediv emod (z := (tmJFst t : ℕ) - tmJSnd t) rfl)
    (Det.arith' (op := .sub) emod ediv (z := (tmJSnd t : ℕ) - tmJFst t) rfl)
    (z := ((tmJFst t : ℕ) - tmJSnd t) + ((tmJSnd t : ℕ) - tmJFst t)) rfl
  have dv1 := Det.var' (P := P) (env := [Val.list [.list [.list us, .nat q], .nat t],
    tmJEntVal (O (tmJFst t) (tmJSnd t))]) (i := 1)
    (v := tmJEntVal (O (tmJFst t) (tmJSnd t))) rfl
  -- the weights
  have ht := t.2
  have hfs := tmJYg_fst_le t
  have hsn := tmJYg_snd_le t
  have hqq : q ≤ q * q := Nat.le_mul_of_pos_left _ hq0
  have hfq : (tmJFst t : ℕ) * (2 * q) ≤ 2 * (q * q) := by
    have : (tmJFst t : ℕ) * (2 * q) ≤ q * (2 * q) := Nat.mul_le_mul_right _ hfs.le
    have e : q * (2 * q) = 2 * (q * q) := by ring
    omega
  have wt' := wt_nat_le t
  have wq := wt_nat_le q
  have w2 := wt_nat_le 2
  have w0 := wt_nat_le 0
  have w1 := wt_nat_le 1
  have wul := wt_list2_le (.list us) (.nat q)
  have win := wt_list2_le (.list [.list us, .nat q]) (.nat t)
  have wf := wt_nat_le (tmJFst t)
  have ws := wt_nat_le (tmJSnd t)
  have w2q := wt_nat_le (2 * q)
  have wfq := wt_nat_le ((tmJFst t : ℕ) * (2 * q))
  have widx := wt_nat_le ((tmJFst t : ℕ) * (2 * q) + (tmJSnd t : ℕ))
  have wsub1 := wt_nat_le ((tmJFst t : ℕ) - tmJSnd t)
  have wsub2 := wt_nat_le ((tmJSnd t : ℕ) - tmJFst t)
  have wcnd := wt_nat_le (((tmJFst t : ℕ) - tmJSnd t) + ((tmJSnd t : ℕ) - tmJFst t))
  have hE : (tmJEntVal (O (tmJFst t) (tmJSnd t))).wt < (Val.list us).wt :=
    wt_le_wt_list (List.mem_of_getElem? (hus (tmJFst t) (tmJSnd t)))
  by_cases heq : tmJFst t = tmJSnd t
  · have hz : ((tmJFst t : ℕ) - tmJSnd t) + ((tmJSnd t : ℕ) - tmJFst t) = 0 := by
      rw [heq]; simp
    rw [hz] at dcnd
    have hv : tmJTlVal (tmJTlOf O t) = .list [] := by simp [tmJTlOf, heq, tmJTlVal]
    rw [hv]
    refine (Det.letE de (Det.ite_zero dcnd Det.nil)).mono ?_
    simp only [wt_list_nil]
    omega
  · have hz : ((tmJFst t : ℕ) - tmJSnd t) + ((tmJSnd t : ℕ) - tmJFst t) ≠ 0 := by
      intro h; apply heq; ext; omega
    cases hO : O (tmJFst t) (tmJSnd t) with
    | none =>
      have hv : tmJTlVal (tmJTlOf O t) = .list [] := by simp [tmJTlOf, heq, hO, tmJTlVal]
      rw [hv]
      rw [hO] at dv1 de hE dcnd
      simp only [tmJEntVal] at dv1 de hE dcnd
      have dlen := Det.length dv1 (vs := [])
      refine (Det.letE de (Det.ite_pos dcnd hz (Det.ite_zero dlen Det.nil))).mono ?_
      simp only [tmJEntVal, wt_list_nil, List.length_nil] at hE ⊢
      omega
    | some p =>
      obtain ⟨b, gs⟩ := p
      have hv : tmJTlVal (tmJTlOf O t) =
          .list ([] ++ [.list [.nat (tmJFst t), .nat (tmJSnd t), encPerm b]]) := by
        simp [tmJTlOf, heq, hO, tmJTlVal, tmJTrVal]
      rw [hv]
      rw [hO] at dv1 de hE dcnd ediv emod
      simp only [tmJEntVal] at dv1 de hE dcnd ediv emod
      have dlen := Det.length dv1 (vs := [encPerm b, encGroup gs])
      have dg := Det.get' dv1 (Det.nat 0) (vs := [encPerm b, encGroup gs]) (v := encPerm b) rfl
      have dt := Det.mk3 ediv emod dg
      have dsn := Det.snoc Det.nil dt
      refine (Det.letE de (Det.ite_pos dcnd hz (Det.ite_pos dlen (by simp) dsn))).mono ?_
      have wb : (encPerm b).wt < (Val.list [encPerm b, encGroup gs]).wt :=
        wt_le_wt_list (by simp)
      have w3 := wt_list3_le (.nat (tmJFst t)) (.nat (tmJSnd t)) (encPerm b)
      have w4 := wt_list_le [Val.list [.nat (tmJFst t), .nat (tmJSnd t), encPerm b]]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil, List.nil_append] at w4 ⊢
      omega

/-- The weight of the triples of one index. -/
theorem tmJ_tlOf_wt (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m))))
    (us : List Val)
    (hus : ∀ a a' : Fin q, us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (O a a')))
    (t : Fin (q * q)) :
    (tmJTlVal (tmJTlOf O t)).wt ≤ 20 * ((Val.list us).wt + (m + 1) * (q + 1)) := by
  have hE : (tmJEntVal (O (tmJFst t) (tmJSnd t))).wt < (Val.list us).wt :=
    wt_le_wt_list (List.mem_of_getElem? (hus (tmJFst t) (tmJSnd t)))
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hfs := tmJYg_fst_le t
  have hsn := tmJYg_snd_le t
  have wf := wt_nat_le (tmJFst t)
  have ws := wt_nat_le (tmJSnd t)
  unfold tmJTlOf
  split_ifs with heq
  · simp only [tmJTlVal, List.map_nil, wt_list_nil]; omega
  · cases hO : O (tmJFst t) (tmJSnd t) with
    | none => simp only [tmJTlVal, List.map_nil, wt_list_nil]; omega
    | some p =>
      obtain ⟨b, gs⟩ := p
      rw [hO] at hE
      simp only [tmJEntVal] at hE
      have wb : (encPerm b).wt < (Val.list [encPerm b, encGroup gs]).wt :=
        wt_le_wt_list (by simp)
      have w3 := wt_list3_le (.nat (tmJFst t)) (.nat (tmJSnd t)) (encPerm b)
      have w4 := wt_list_le [Val.list [.nat (tmJFst t), .nat (tmJSnd t), encPerm b]]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.length_cons, List.length_nil] at w4
      simp only [tmJTlVal, tmJTrVal, List.map_cons, List.map_nil]
      omega

/-- The value of the flattened list. -/
theorem tmJTlVal_flatten (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) :
    Val.list (((List.finRange (q * q)).map fun t => (tmJTlOf O t).map tmJTrVal).flatten) =
      tmJTlVal (tmJTlList O) := by
  simp only [tmJTlVal, tmJTlList, List.map_flatten, List.map_map]
  rfl

/-- On `[us, q]`: tabulate the triples of every `t < q²` and flatten. -/
def tmJTlF (rg tbE fl : ℕ) : Expr :=
  .call fl (.call tbE (mk2 (mk2 (arg 0) (arg 1)) (.call rg (.arith .mul (arg 1) (arg 1)))))

/-- The cost of all triples. -/
def tmJTlK (V : ℕ) : ℕ := 10 ^ 13 * V ^ 12

structure TmJTlAt (P : Program) (f rg tbE e fl app : ℕ) : Prop where
  hf : P.funs[f]? = some (tmJTlF rg tbE fl)
  hrg : P.HasAt rg (rangeFuns rg)
  htbE : P.HasAt tbE (mapFuns tbE e)
  he : P.funs[e]? = some tmJTlEF
  hfl : P.funs[fl]? = some (tmJFlatF (fl + 1))
  hflF : P.HasAt (fl + 1) (foldlFuns (fl + 1) (fl + 4))
  hst : P.funs[fl + 4]? = some (tmJFlatStepF app)
  happ : P.HasAt app (appendFuns app)

set_option maxHeartbeats 1000000 in
/-- **The lifted transpositions of two different rows.** -/
theorem tmJ_tl_spec {P : Program} {f rg tbE e fl app : ℕ} (hA : TmJTlAt P f rg tbE e fl app)
    (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) (us : List Val)
    (hus : ∀ a a' : Fin q, us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (O a a'))) :
    FunDet P f (.list [.list us, .nat q]) (tmJTlVal (tmJTlList O))
      (tmJTlK ((Val.list us).wt + (m + 1) * (q + 1))) := by
  refine FunDet.intro hA.hf ?_
  unfold tmJTlF
  set V := (Val.list us).wt + (m + 1) * (q + 1) with hV
  have d0 := Det.arg' (P := P) (vs := [.list us, .nat q]) (rest := []) (j := 0) (v := .list us) rfl
  have d1 := Det.arg' (P := P) (vs := [.list us, .nat q]) (rest := []) (j := 1) (v := .nat q) rfl
  have dqq := Det.arith' (op := .mul) d1 d1 (z := q * q) rfl
  have dr := Det.call dqq (tmJ_range_det hA.hrg (q * q))
  have hT := tabulate_spec hA.htbE (c := .list [.list us, .nat q])
    (F := fun t : Fin (q * q) => tmJTlVal (tmJTlOf O t))
    (B := 1000 * ((Val.list us).wt + q * q + 20)) (fun t => tmJ_tlE_spec hA.he O us hus t)
  have dt := Det.call (Det.mk2 (Det.mk2 d0 d1) dr) hT
  have hrows : Val.list ((List.finRange (q * q)).map fun t => tmJTlVal (tmJTlOf O t)) =
      Val.list (((List.finRange (q * q)).map fun t => (tmJTlOf O t).map tmJTrVal).map
        Val.list) := by
    simp only [List.map_map]; rfl
  rw [hrows] at dt
  have hF := tmJ_flat_spec hA.hfl hA.hflF hA.hst hA.happ
    ((List.finRange (q * q)).map fun t => (tmJTlOf O t).map tmJTrVal)
  have dall := Det.call dt hF
  rw [tmJTlVal_flatten] at dall
  refine dall.mono ?_
  -- the cost
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hV1 : 1 ≤ V := by omega
  have hpow : ∀ i j, i ≤ j → V ^ i ≤ V ^ j := fun i j h => Nat.pow_le_pow_right hV1 h
  have hqV : q + 1 ≤ V := by omega
  have hqq : q * q + 1 ≤ V ^ 2 := by
    have : (q + 1) * (q + 1) ≤ V * V := Nat.mul_le_mul hqV hqV
    have e : V ^ 2 = V * V := by ring
    nlinarith
  have wrow := tmJ_tlOf_wt O us hus
  have wR : (Val.list ((List.finRange (q * q)).map fun t => tmJTlVal (tmJTlOf O t))).wt ≤
      41 * V ^ 3 + 4 := by
    have := tmJ_wt_list_le (vs := (List.finRange (q * q)).map fun t => tmJTlVal (tmJTlOf O t))
      (E := 20 * V) (by
        intro v hv
        obtain ⟨t, -, rfl⟩ := List.mem_map.1 hv
        exact wrow t)
    simp only [List.length_map, List.length_finRange] at this
    have h1 : q * q * (2 * (20 * V) + 1) ≤ V ^ 2 * (41 * V) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : V ^ 2 * (41 * V) = 41 * V ^ 3 := by ring
    omega
  rw [hrows] at wR
  have wid := wt_ids_le (q * q)
  have wus := wt_list2_le (.list us) (.nat q)
  have wq := wt_nat_le q
  have wqq := wt_nat_le (q * q)
  have wc := wt_list2_le (.list [.list us, .nat q]) (encFun fun i : Fin (q * q) => (i : ℕ))
  have hq4 : (q * q + 1) ^ 2 ≤ V ^ 4 := by
    have := Nat.pow_le_pow_left hqq 2
    have e : (V ^ 2) ^ 2 = V ^ 4 := by ring
    omega
  have hq6 : (q * q + 1) ^ 3 ≤ V ^ 6 := by
    have := Nat.pow_le_pow_left hqq 3
    have e : (V ^ 2) ^ 3 = V ^ 6 := by ring
    omega
  have P1 : q * q * (1000 * ((Val.list us).wt + q * q + 20)) ≤ V ^ 2 * (1000 * (21 * V ^ 2)) := by
    refine Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ ?_)
    have := hpow 0 2 (by norm_num); simp at this
    have := hpow 1 2 (by norm_num); simp at this
    omega
  have e1 : V ^ 2 * (1000 * (21 * V ^ 2)) = 21000 * V ^ 4 := by ring
  have P2 : mapK * (q * q + 1) * ((Val.list [.list [.list us, .nat q],
      encFun fun i : Fin (q * q) => (i : ℕ)]).wt + (Val.list (((List.finRange (q * q)).map
        fun t => (tmJTlOf O t).map tmJTrVal).map Val.list)).wt + 1) ≤
      1000 * V ^ 2 * (100 * V ^ 4) := by
    unfold mapK
    refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) ?_
    have := hpow 3 4 (by norm_num)
    have := hpow 1 4 (by norm_num); simp only [pow_one] at this
    have := hpow 0 4 (by norm_num); simp at this
    omega
  have e2 : 1000 * V ^ 2 * (100 * V ^ 4) = 100000 * V ^ 6 := by ring
  have P3 : tmJFlatK (Val.list (((List.finRange (q * q)).map fun t =>
      (tmJTlOf O t).map tmJTrVal).map Val.list)).wt ≤ 10 ^ 6 * (41 * V ^ 3 + 5) ^ 3 := by
    unfold tmJFlatK
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have P4 : 10 ^ 6 * (41 * V ^ 3 + 5) ^ 3 ≤ 10 ^ 6 * (46 * V ^ 3) ^ 3 := by
    have := hpow 0 3 (by norm_num); simp at this
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have e4 : 10 ^ 6 * (46 * V ^ 3) ^ 3 = 97336000000 * V ^ 9 := by ring
  have wrg : 10000 * (q * q + 1) ^ 3 ≤ 10000 * V ^ 6 := Nat.mul_le_mul_left _ hq6
  have wtot : (Val.list [.list us, .nat q]).wt ≤ 20 * V := by omega
  have wfl := tmJ_wt_flatten_le ((List.finRange (q * q)).map fun t =>
    (tmJTlOf O t).map tmJTrVal)
  rw [tmJTlVal_flatten] at wfl
  have h1 := hpow 1 12 (by norm_num)
  simp only [pow_one] at h1
  have h2 := hpow 2 12 (by norm_num)
  have h3 := hpow 3 12 (by norm_num)
  have h4 := hpow 4 12 (by norm_num)
  have h6 := hpow 6 12 (by norm_num)
  have h9 := hpow 9 12 (by norm_num)
  show _ ≤ 10 ^ 13 * V ^ 12
  omega

end GI.Impl
