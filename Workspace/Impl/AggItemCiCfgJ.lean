import Workspace.Impl.AggItemCiCfgZ

/-!
# The configuration query: the points outside the fiber and their transpositions

* `itcqNfT fb` on `[rcCertIn X x₀, a]`: whether `a` is outside the fiber (the fiber test `fb`,
  negated). `itcqFlF fr ff` with the filter of this test gives the points outside the fiber in
  increasing order, `itcqDR X` (`itcq_dlF_spec`).
* `itcqSwB` on `[[a, b], t]`: `swap a b t`; mapped over `[0, …, q - 1]` it gives `swap a b`
  (`itcq_swm_spec`).
* `itcqCsB sm` on `[[D, d, R, cX], j]`: the transposition `itcqCsE X D j` of `D[j / d]` and
  `D[j % d]` when the two points have the same color, else the identity (the transposition of
  `D[j / d]` with itself); `itcqCsF rng cm` on `[D, R, cX]` maps it over `[0, …, d² - 1]` and
  gives `itcqCs X` (`itcq_csF_spec`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup encPerms)

variable {q : ℕ}

/-- On `[rcCertIn X x₀, a]`: whether `a` is outside the fiber. -/
def itcqNfT (fb : ℕ) : Expr := .ite (.call fb (.var 0)) (.nat 0) (.nat 1)

/-- On `[[a, b], t]`: the number `swap a b t`. -/
def itcqSwB : Expr := itcqSE (arg 1) (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))

/-- Entry `D[j / d]` of the input `[[D, d, R, cX], j]`. -/
def itcqDaE : Expr := .get (.get (arg 0) (.nat 0)) (.arith .div (arg 1) (.get (arg 0) (.nat 1)))

/-- Entry `D[j % d]` of the input `[[D, d, R, cX], j]`. -/
def itcqDbE : Expr := .get (.get (arg 0) (.nat 0)) (.arith .mod (arg 1) (.get (arg 0) (.nat 1)))

/-- The diagonal color of the point `x` in the certificate input `cZ`. -/
def itcqCoE (cZ x : Expr) : Expr := .get (.get (.get cZ (.nat 0)) x) x

/-- On `[[D, d, R, cX], j]`: the transposition of `a = D[j / d]` and `b = D[j % d]` if they
have the same color in `cX = rcCertIn X x₀`, else of `a` with itself, by the map `sm` of
`itcqSwB` over `R`. -/
def itcqCsB (sm : ℕ) : Expr :=
  .call sm (mk2 (mk2 itcqDaE (.ite (.arith .eq (itcqCoE (.get (arg 0) (.nat 3)) itcqDaE)
      (itcqCoE (.get (arg 0) (.nat 3)) itcqDbE)) itcqDbE itcqDaE))
    (.get (arg 0) (.nat 2)))

/-- On `[D, R, cX]`: the transpositions of the points of `D` of the same color, by the map `cm`
of `itcqCsB`. -/
def itcqCsF (rng cm : ℕ) : Expr :=
  .letE (.length (.get (.var 0) (.nat 0)))
    (.call cm (mk2 (mk4 (.get (.var 0) (.nat 0)) (.var 1) (.get (.var 0) (.nat 1))
        (.get (.var 0) (.nat 2)))
      (.call rng (.arith .mul (.var 1) (.var 1)))))

/-- The cost bound of the transpositions of the outer classes. -/
def itcqCsC (V : ℕ) : ℕ := 10 ^ 16 * (V + 1) ^ 8

theorem itcq_dlC_arith {W q a A b B C : ℕ} (hq : q ≤ W) (ha : a ≤ W + 2)
    (hA : A ≤ 5 * (W + 1) ^ 2) (hb : b ≤ 2 * (W + 5 * (W + 1) ^ 2) + 6) (hB : B ≤ 5 * (W + 1) ^ 2)
    (hC : C ≤ 10 * (20 * (W + 1) ^ 2 + 1) + loopModK * (q + 1) * (a + q + A + 1) +
      (q * (40 * (20 * (W + 1) ^ 2 + 1)) + loopModK * (q + 1) * (b + q + B + 1))) :
    C ≤ itcqFlC W := by
  unfold itcqFlC
  unfold loopModK at hC
  have hs : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hst : (W + 1) ^ 2 + 1 ≤ (W + 2) ^ 2 := by
    have e1 : (W + 2) ^ 2 = (W + 1) ^ 2 + 2 * W + 3 := by ring
    omega
  have h1 : 1000 * (q + 1) * (a + q + A + 1) ≤ 1000 * ((W + 2) * (7 * (W + 2) ^ 2)) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have h2 : 1000 * (q + 1) * (b + q + B + 1) ≤ 1000 * ((W + 2) * (18 * (W + 2) ^ 2)) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have h3 : q * (40 * (20 * (W + 1) ^ 2 + 1)) ≤ (W + 2) * (40 * (21 * (W + 2) ^ 2)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 : (W + 2) ^ 2 ≤ (W + 2) * (W + 2) ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
  have e1 : (W + 2) * (7 * (W + 2) ^ 2) = 7 * ((W + 2) * (W + 2) ^ 2) := by ring
  have e2 : (W + 2) * (18 * (W + 2) ^ 2) = 18 * ((W + 2) * (W + 2) ^ 2) := by ring
  have e4 : (W + 2) * (40 * (21 * (W + 2) ^ 2)) = 840 * ((W + 2) * (W + 2) ^ 2) := by ring
  have e3 : (W + 2) ^ 3 = (W + 2) * (W + 2) ^ 2 := by ring
  omega

theorem itcq_nq_val (X : PairCfg q) (v : Val) :
    boolVal (itcqNq X v) = .nat (if (itcqFq X v).toNat = 0 then 1 else 0) := by
  unfold itcqNq; cases itcqFq X v <;> rfl

section Prog

variable {P : Program}

/-- **The test "outside the fiber"**, in cost `40 (W + 1)`. -/
theorem itcq_nfT_spec {f fb : ℕ} (hf : P.funs[f]? = some (itcqNfT fb))
    (hfb : P.funs[fb]? = some itcqFbT) (X : PairCfg q) (x₀ : ℕ) (a : Fin q) {W : ℕ}
    (hW : (Val.list [.list [rcColVal X, .nat X.j, .nat x₀], .nat a]).wt ≤ W) :
    FunDet P f (.list [.list [rcColVal X, .nat X.j, .nat x₀], .nat a])
      (boolVal (itcqNq X (.nat a))) (40 * (W + 1)) := by
  have h4 : 4 ≤ W := by
    have := wt_list_eq [Val.list [rcColVal X, .nat X.j, .nat x₀], .nat a]; omega
  have c := StDC.call (StDC.var' (P := P)
    (env := [.list [.list [rcColVal X, .nat X.j, .nat x₀], .nat a]]) (i := 0) rfl hW)
    (itcq_fbT_spec hfb X x₀ a hW) ((wt_boolVal_le _).trans (by omega))
  have hv : (boolVal (itcqNq X (.nat a))).wt ≤ W := (wt_boolVal_le _).trans (by omega)
  rw [itcq_nq_val] at hv ⊢
  have body := StDC.ite (nt := 1) (Et := 0) (ne := 1) (Ee := 0) c
    (fun h => by rw [if_neg h]; exact StDC.nat 0 (by omega))
    (fun h => by rw [if_pos h]; exact StDC.nat 1 (by omega)) hv
  exact StDC.funDet hf body (by omega)

/-- **The points outside the fiber** of `Z`, in cost `itcqFlC W`. -/
theorem itcq_dlF_spec {f fr ff fb fn : ℕ} (hf : P.funs[f]? = some (itcqFlF fr ff))
    (hr : P.HasAt fr (rangeFuns fr)) (hff : P.HasAt ff (filterFuns ff fn))
    (hfn : P.funs[fn]? = some (itcqNfT fb))
    (hfb : P.funs[fb]? = some itcqFbT) (Z : PairCfg q) (z₀ : ℕ) {W : ℕ}
    (hW : (Val.list [rcColVal Z, .nat Z.j, .nat z₀]).wt ≤ W) :
    FunDet P f (.list [rcColVal Z, .nat Z.j, .nat z₀]) (itcqDR Z) (itcqFlC W) := by
  set cZ : Val := .list [rcColVal Z, .nat Z.j, .nat z₀] with hcZ
  have hcol : (rcColVal Z).wt < cZ.wt := wt_le_wt_list (by simp)
  have hq := itcq_q_le Z
  have hqW : q ≤ W := by omega
  have hsq : (q + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hRw := itcq_range_wt q
  have hDw : (itcqDR Z).wt ≤ 5 * (q + 1) ^ 2 := by
    refine wt_natList_le_sq (fun x hx => ?_) ?_
    · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx; exact a.isLt.le
    · simp only [List.length_map, itciFl_length]
      exact Finset.card_le_univ _ |>.trans (by simp)
  have hW1 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hRw' : (natList (List.range q)).wt ≤ 5 * (W + 1) ^ 2 := by omega
  have hDw' : (itcqDR Z).wt ≤ 5 * (W + 1) ^ 2 := by omega
  have v0 := StDC.var' (P := P) (env := [cZ]) (i := 0) (W := 20 * (W + 1) ^ 2) rfl (by omega)
  have g0 := StDC.get v0 (StDC.nat 0 (by omega)) (v := rcColVal Z) rfl (by omega)
  have ln := StDC.length g0 (by rw [itcq_rc_length]; omega)
  rw [itcq_rc_length] at ln
  have hrd : FunDet P fr (.nat q) (natList (List.range q))
      (loopModK * (q + 1) * ((Val.nat q).wt + q + (natList (List.range q)).wt + 1)) :=
    (range_spec hr q).mono fun w c ⟨hw, hc⟩ => ⟨hw, by subst hw; exact hc⟩
  have cr := StDC.call ln hrd (by omega)
  have hin : (Val.list [cZ, natList (List.range q)]).wt ≤ 2 * (W + 5 * (W + 1) ^ 2) + 6 := by
    have := wt_list2_le cZ (natList (List.range q)); omega
  have m2 := StDC.mk2 v0 cr (by omega) (by omega)
  have hfd : FunDet P ff (.list [cZ, natList (List.range q)]) (itcqDR Z)
      (q * (40 * (20 * (W + 1) ^ 2 + 1)) + loopModK * (q + 1) *
        ((Val.list [cZ, natList (List.range q)]).wt + q + (itcqDR Z).wt + 1)) := by
    have key := filter_spec (P := P) hff (c := cZ) (xs := (List.range q).map Val.nat)
      (q := itcqNq Z) (B := fun _ => 40 * (20 * (W + 1) ^ 2 + 1)) (by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
        have ha' := List.mem_range.1 ha
        have h2 := wt_list2_le cZ (.nat a)
        have := wt_nat_le a
        exact itcq_nfT_spec hfn hfb Z z₀ ⟨a, ha'⟩
          (by show (Val.list [cZ, .nat a]).wt ≤ 20 * (W + 1) ^ 2; omega))
    refine key.mono fun w c ⟨hw, hc⟩ => ⟨?_, ?_⟩
    · rw [hw, itcq_nq_filter]; rfl
    · have hw' : w = itcqDR Z := by rw [hw, itcq_nq_filter]; rfl
      subst hw'
      simp only [List.map_const', List.sum_replicate, List.length_map, List.length_range,
        smul_eq_mul] at hc
      exact hc
  have cf := StDC.call m2 hfd (by omega)
  refine StDC.funDet hf cf ?_
  have hqw := wt_nat_le q
  refine itcq_dlC_arith (a := (Val.nat q).wt) hqW (by omega) hRw'
    (b := (Val.list [cZ, natList (List.range q)]).wt) hin hDw' ?_
  omega

/-- **One entry of a transposition**, in cost `44 (W + 1)`. -/
theorem itcq_swB_spec {f : ℕ} (hf : P.funs[f]? = some itcqSwB) (a b t : ℕ) {W : ℕ}
    (hW : (Val.list [.list [.nat a, .nat b], .nat t]).wt + a + b + t + 3 ≤ W) :
    FunDet P f (.list [.list [.nat a, .nat b], .nat t]) (.nat (itcqS a b t)) (44 * (W + 1)) := by
  have h0 : (Val.list [.nat a, .nat b]).wt < (Val.list [.list [.nat a, .nat b], .nat t]).wt :=
    wt_le_wt_list (by simp)
  have h1 : (Val.nat t).wt < (Val.list [.list [.nat a, .nat b], .nat t]).wt :=
    wt_le_wt_list (by simp)
  have ha : (Val.nat a).wt < (Val.list [.nat a, .nat b]).wt := wt_le_wt_list (by simp)
  have hb : (Val.nat b).wt < (Val.list [.nat a, .nat b]).wt := wt_le_wt_list (by simp)
  have A0 := StDC.arg (P := P) (rest := []) (vs := [.list [.nat a, .nat b], .nat t]) (j := 0) rfl
    (W := W) (by omega) (by omega) (by omega)
  have A1 := StDC.arg (P := P) (rest := []) (vs := [.list [.nat a, .nat b], .nat t]) (j := 1) rfl
    (W := W) (by omega) (by omega) (by omega)
  have gA := StDC.get A0 (StDC.nat 0 (by omega)) (v := .nat a) rfl (by omega)
  have gB := StDC.get A0 (StDC.nat 1 (by omega)) (v := .nat b) rfl (by omega)
  have e := itcq_se_spec A1 gA gB (by omega) (by omega) (by omega)
  exact StDC.funDet hf e (by omega)

/-- The cost bound of one transposition. -/
def itcqSmC (q : ℕ) : ℕ := 10 ^ 5 * (q + 1) ^ 3

/-- **A transposition** as the map of `itcqSwB` over `[0, …, q - 1]`. -/
theorem itcq_swm_spec {sm fs : ℕ} (hm : P.HasAt sm (mapFuns sm fs))
    (hf : P.funs[fs]? = some itcqSwB) (a b : Fin q) :
    FunDet P sm (.list [.list [.nat a, .nat b], natList (List.range q)]) (encPerm (swap a b))
      (itcqSmC q) := by
  have hal := a.isLt
  have hbl := b.isLt
  have hwa := wt_nat_le (a : ℕ)
  have hwb := wt_nat_le (b : ℕ)
  have hab := wt_list2_le (.nat (a : ℕ)) (.nat (b : ℕ))
  have key := itcq_mapPos_spec (P := P) hm (c := .list [.nat a, .nat b]) (m := q)
    (g := fun t => (swap a b t : ℕ)) (Bd := 44 * (14 * q + 40)) (fun t => by
      show FunDet P fs _ (.nat (swap a b t : ℕ)) _
      rw [← itcqS_val]
      refine itcq_swB_spec hf a b t ?_
      have := wt_list2_le (.list [.nat (a : ℕ), .nat (b : ℕ)]) (.nat (t : ℕ))
      have := wt_nat_le (t : ℕ)
      have := t.isLt
      omega)
  refine key.mono fun w c hwc => ⟨hwc.1, ?_⟩
  obtain ⟨hw, hc⟩ := hwc
  have hR := itcq_range_wt q
  have hin := wt_list2_le (.list [.nat (a : ℕ), .nat (b : ℕ)]) (natList (List.range q))
  have hout : w.wt ≤ 4 * (q + 1) ^ 2 := by rw [hw]; exact wt_encPerm_le (swap a b)
  have hc' : c ≤ q * (44 * (14 * q + 40)) + 1000 * (q + 1) * ((Val.list [.list [.nat (a : ℕ),
      .nat (b : ℕ)], natList (List.range q)]).wt + w.wt + 1) := hc
  have hq2 : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h1 : q * (44 * (14 * q + 40)) ≤ (q + 1) * (44 * (54 * (q + 1) ^ 2)) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))
  have h2 : 1000 * (q + 1) * ((Val.list [.list [.nat (a : ℕ), .nat (b : ℕ)],
      natList (List.range q)]).wt + w.wt + 1) ≤ 1000 * ((q + 1) * (50 * (q + 1) ^ 2)) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ?_)
    omega
  have e4 : (q + 1) * (44 * (54 * (q + 1) ^ 2)) = 2376 * (q + 1) ^ 3 := by ring
  have e5 : 1000 * ((q + 1) * (50 * (q + 1) ^ 2)) = 50000 * (q + 1) ^ 3 := by ring
  unfold itcqSmC
  generalize (q + 1) ^ 3 = T at e4 e5
  omega

/-- **The color lookup.** -/
theorem itcq_coE_st {env : List Val} {eZ ex : Expr} {Z : PairCfg q} {z₀ : ℕ} {a : Fin q}
    {n1 E1 n2 E2 W : ℕ} (hZ : StDC P env eZ (.list [rcColVal Z, .nat Z.j, .nat z₀]) n1 E1 W)
    (hx : StDC P env ex (.nat a) n2 E2 W) (hW : (Val.list [rcColVal Z, .nat Z.j, .nat z₀]).wt ≤ W) :
    StDC P env (itcqCoE eZ ex) (.nat (Z.col a a)) (n1 + n2 + n2 + 4) (E1 + E2 + E2) W := by
  have hc : (rcColVal Z).wt ≤ (Val.list [rcColVal Z, .nat Z.j, .nat z₀]).wt := st_wt_mem (by simp)
  have hrw : (encFun (Z.col a)).wt ≤ (rcColVal Z).wt :=
    st_wt_mem (List.mem_of_getElem? (itcq_col_get Z a))
  have hvw : (Val.nat (Z.col a a)).wt ≤ (encFun (Z.col a)).wt :=
    st_wt_mem (List.mem_of_getElem? (encFun_getElem? (Z.col a) a))
  have h2 := (Val.list [rcColVal Z, .nat Z.j, .nat z₀]).two_le_size
  have h3 := (Val.list [rcColVal Z, .nat Z.j, .nat z₀]).size_le_wt
  have g0 := StDC.get hZ (StDC.nat 0 (by omega)) (v := rcColVal Z) rfl (by omega)
  have r1 := StDC.get g0 hx (itcq_col_get Z a) (by omega)
  have r2 := StDC.get r1 hx (encFun_getElem? (Z.col a) a) (by omega)
  exact r2.mono (by omega) (by omega)

theorem itcq_nl_get {D : List (Fin q)} {i : ℕ} (h : i < D.length) :
    ((D.map Fin.val).map Val.nat)[i]? = some (.nat (D[i] : ℕ)) := by simp [h]

theorem itcqCsE_eq {X : PairCfg q} {D : List (Fin q)} {j : ℕ} (h1 : j / D.length < D.length)
    (h2 : j % D.length < D.length) : itcqCsE X D j = swap D[j / D.length]
      (if X.col D[j / D.length] D[j / D.length] = X.col D[j % D.length] D[j % D.length] then
        D[j % D.length] else D[j / D.length]) := by
  simp only [itcqCsE, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]
  split_ifs
  · rfl
  · exact (swap_self _).symm

/-- The cost bound of one transposition. -/
def itcqCbC (V : ℕ) : ℕ := 10 ^ 7 * (V + 2) ^ 3

theorem itcq_cs_arith {q V n C : ℕ} (hq : q + 1 ≤ V) (hn : n ≤ 200)
    (hC : C ≤ n * (4 * V + 20 * (q + 1) ^ 2 + 101) + itcqSmC q) : C ≤ itcqCbC V := by
  unfold itcqSmC at hC
  unfold itcqCbC
  have h1 : (q + 1) ^ 3 ≤ (V + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h1' : (q + 1) ^ 2 ≤ (V + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : V + 2 ≤ (V + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h2' : (V + 2) ^ 2 ≤ (V + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : n * (4 * V + 20 * (q + 1) ^ 2 + 101) ≤ 200 * (4 * V + 20 * (q + 1) ^ 2 + 101) :=
    Nat.mul_le_mul_right _ hn
  omega

set_option maxHeartbeats 1000000 in
/-- **Entry `j` of the transpositions of the outer classes**, for `j < d²`. -/
theorem itcq_csB_spec {f sm fs : ℕ} (hf : P.funs[f]? = some (itcqCsB sm))
    (hm : P.HasAt sm (mapFuns sm fs)) (hfs : P.funs[fs]? = some itcqSwB) (X : PairCfg q)
    (x₀ : ℕ) {j : ℕ} (hj : j < (itciFo X).length * (itciFo X).length) {V : ℕ} (hq : q + 1 ≤ V)
    (hV : (Val.list [.list [itcqDV X, .nat (itciFo X).length, natList (List.range q),
      .list [rcColVal X, .nat X.j, .nat x₀]], .nat j]).wt ≤ V) :
    FunDet P f (.list [.list [itcqDV X, .nat (itciFo X).length, natList (List.range q),
      .list [rcColVal X, .nat X.j, .nat x₀]], .nat j]) (encPerm (itcqCsE X (itciFo X) j))
      (itcqCbC V) := by
  set cX : Val := .list [rcColVal X, .nat X.j, .nat x₀]
  have hDV : itcqDV X = natList ((itciFo X).map Fin.val) := rfl
  have hd : (itciFo X).length ≤ q := by
    rw [itciFo_length]; exact Finset.card_le_univ _ |>.trans (by simp)
  rw [hDV] at hV ⊢
  generalize hD : itciFo X = D at hj hV hd ⊢
  set c := Val.list [natList (D.map Fin.val), .nat D.length, natList (List.range q), cX] with hc
  have hd0 : 0 < D.length := by
    rcases Nat.eq_zero_or_pos D.length with h | h
    · rw [h] at hj; omega
    · exact h
  have h1 : j / D.length < D.length := (Nat.div_lt_iff_lt_mul hd0).2 hj
  have h2 : j % D.length < D.length := Nat.mod_lt _ hd0
  have hjq : j ≤ (q + 1) ^ 2 := by
    have := Nat.mul_le_mul hd hd
    have e : (q + 1) ^ 2 = q * q + 2 * q + 1 := by ring
    omega
  have hcw : c.wt ≤ V := (st_wt_mem (by simp)).trans hV
  have hjw : (Val.nat j).wt ≤ V := (st_wt_mem (by simp)).trans hV
  have hDw : (natList (D.map Fin.val)).wt ≤ V := (st_wt_mem (by simp [hc])).trans hcw
  have hdw : (Val.nat D.length).wt ≤ V := (st_wt_mem (by simp [hc])).trans hcw
  have hRw : (natList (List.range q)).wt ≤ V := (st_wt_mem (by simp [hc])).trans hcw
  have hXw : cX.wt ≤ V := (st_wt_mem (by simp [hc])).trans hcw
  have hs2 := (Val.list [c, .nat j]).two_le_size
  have hs3 := (Val.list [c, .nat j]).size_le_wt
  obtain ⟨Wl, hWl⟩ : ∃ Wl, Wl = 4 * V + 20 * (q + 1) ^ 2 + 100 := ⟨_, rfl⟩
  have A0 := StDC.arg (P := P) (rest := []) (vs := [c, .nat j]) (j := 0) rfl (W := Wl)
    (by omega) (by omega) (by omega)
  have A1 := StDC.arg (P := P) (rest := []) (vs := [c, .nat j]) (j := 1) rfl (W := Wl)
    (by omega) (by omega) (by omega)
  have gD := StDC.get A0 (StDC.nat 0 (by omega)) (v := natList (D.map Fin.val)) rfl
    (by omega)
  have gd := StDC.get A0 (StDC.nat 1 (by omega)) (v := .nat D.length) rfl (by omega)
  have gR := StDC.get A0 (StDC.nat 2 (by omega)) (v := natList (List.range q)) rfl (by omega)
  have gX := StDC.get A0 (StDC.nat 3 (by omega)) (v := cX) rfl (by omega)
  have dv := StDC.arith A1 gd (op := .div) (z := j / D.length) rfl
    ((wt_nat_le _).trans (by have := Nat.div_le_self j D.length; have := wt_nat_le j; omega))
  have md := StDC.arith A1 gd (op := .mod) (z := j % D.length) rfl
    ((wt_nat_le _).trans (by have := Nat.mod_le j D.length; omega))
  set a := D[j / D.length]'h1
  set b := D[j % D.length]'h2
  have hwa : (Val.nat (a : ℕ)).wt ≤ V :=
    (st_wt_mem (List.mem_of_getElem? (itcq_nl_get h1))).trans hDw
  have hwb : (Val.nat (b : ℕ)).wt ≤ V :=
    (st_wt_mem (List.mem_of_getElem? (itcq_nl_get h2))).trans hDw
  have ea := StDC.get gD dv (v := .nat (a : ℕ)) (itcq_nl_get h1) (by omega)
  have eb := StDC.get gD md (v := .nat (b : ℕ)) (itcq_nl_get h2) (by omega)
  have coa := itcq_coE_st gX ea (hXw.trans (by omega))
  have cob := itcq_coE_st gX eb (hXw.trans (by omega))
  have h01 : ∀ p : Prop, [Decidable p] → (Val.nat (if p then 1 else 0)).wt ≤ Wl := fun p _ => by
    split_ifs <;> exact (wt_nat_le _).trans (by omega)
  have eqc := StDC.arith coa cob (op := .eq) rfl (h01 _)
  set b' := if X.col a a = X.col b b then b else a with hb'
  have hwb' : (Val.nat (b' : ℕ)).wt ≤ V := by rw [hb']; split_ifs <;> assumption
  have it := StDC.ite (v := .nat (b' : ℕ)) eqc
    (fun h => by
      rw [Machine.BinOp.eval_eq] at h
      have he : X.col a a = X.col b b := by by_contra h'; exact h (if_neg h')
      rw [hb', if_pos he]; exact eb)
    (fun h => by
      rw [Machine.BinOp.eval_eq] at h
      have he : X.col a a ≠ X.col b b := fun e => by rw [if_pos e] at h; exact one_ne_zero h
      rw [hb', if_neg he]; exact ea) (by omega)
  have hab := wt_list2_le (.nat (a : ℕ)) (.nat (b' : ℕ))
  have hla := wt_nat_le (a : ℕ)
  have hlb := wt_nat_le (b' : ℕ)
  have hal := a.isLt
  have hbl := b'.isLt
  have hq1 : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hab2 := wt_list2_le (.list [.nat (a : ℕ), .nat (b' : ℕ)]) (natList (List.range q))
  have mab := StDC.mk2 ea it (by omega) (by omega)
  have hRq := itcq_range_wt q
  have m2 := StDC.mk2 mab gR (by omega) (by omega)
  have hsw := wt_encPerm_le (swap a b')
  have hsw' : (encPerm (swap a b')).wt ≤ Wl := by omega
  have cl := StDC.call m2 (itcq_swm_spec hm hfs a b') hsw'
  have e : itcqCsE X D j = swap a b' := itcqCsE_eq h1 h2
  rw [e]
  refine StDC.funDet hf cl ?_
  refine itcq_cs_arith hq (n := 200) le_rfl ?_
  have : 200 * (4 * V + 20 * (q + 1) ^ 2 + 101) = 200 * (Wl + 1) := by omega
  rw [this]
  clear cl m2 mab it eqc coa cob ea eb dv md gD gd gR gX A0 A1
  omega

end Prog

end GI.Impl
