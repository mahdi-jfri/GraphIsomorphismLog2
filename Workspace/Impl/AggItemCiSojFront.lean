import Workspace.Impl.AggItemCiSojFiber

/-!
# The first-rectangle front: the literal cut test and fixed pair choice

From the pair table, construct the fiber and scan its ordered pairs. The result
contains the fiber list and the scan index. The no-hit index means the model's
primitive-cut predicate holds. A hit is the fixed pair of `itcsChoices`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

/-- On `rcCertIn X x₀`, return `[fiber, implication scan index]`. -/
def itcsFrontF (rng flt fd : ℕ) : Expr :=
  let q := Expr.length (.get (.var 0) (.nat 0))
  .letE (.call rng q)
    (.letE (.call flt (mk2 (.var 0) (.var 1)))
      (.letE (.call rng (.arith .mul (.length (.var 2)) (.length (.var 2))))
        (.letE (.call fd (mk2 (mk3 (.var 0) (.var 2) q) (.var 3)))
          (mk2 (.var 2) (.var 4)))))

/-- Cost of the ordered-pair scan. -/
def itcsFindC (q B : ℕ) : ℕ :=
  q * q * itcsTestC q B + loopModK * (q * q + 1) * (100 * itcsCompW q B + 2 * (q * q) + 3)

/-- Total cost of the pure first-rectangle front. -/
def itcsFrontC (q B : ℕ) : ℕ :=
  50 * (100 * itcsCompW q B + 1) + 7000 * (q + 1) ^ 3 + itcsFiberC q B +
    7000 * (q * q + 1) ^ 3 + itcsFindC q B

/-- The first-rectangle front, including the component-count callback's actual code. -/
theorem itcs_front_prog {q B : ℕ} {Pg : Program} {Ii : itcsCompIdx}
    {f rng flt fb fd ft fp fs : ℕ}
    (hi : itcsCompOk Pg Ii) (hf : Pg.funs[f]? = some (itcsFrontF rng flt fd))
    (hr : Pg.HasAt rng (rangeFuns rng)) (hflt : Pg.HasAt flt (filterFuns flt fb))
    (hfb : Pg.funs[fb]? = some itcqFbT) (hfd : Pg.HasAt fd (findFuns fd ft))
    (hft : Pg.funs[ft]? = some (itcsTestF fp fs)) (hfp : Pg.funs[fp]? = some itcqPcF)
    (hfs : Pg.funs[fs]? = some (itcsSizeF Ii.f Ii.c1.sz))
    (X : PairCfg q) (x₀ : Fin q) (hX : X.Good deltaB) (hx : x₀ ∈ X.fiber)
    (hcol : itCfColsLe (.pair X x₀) B) :
    FunDet Pg f (rcCertIn X x₀) (.list [itcqFV X, .nat (itcsImpScan X)]) (itcsFrontC q B) := by
  have hw := itcs_comp_weights X x₀ 0 hcol (Nat.zero_le _)
  let V := itcsCompW q B
  let Bw := 100 * V
  have budget : 10 * itCfObjB q B + 50 * (q * q + 1) ^ 2 + 10 * itcsGenW q +
      20 * B + 20 * q + 100 ≤ V := by dsimp only [V]; unfold itcsCompW; omega
  have hn : X.fiber.card ≤ q := (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have hs : X.fiber.card * X.fiber.card ≤ q * q := Nat.mul_le_mul hn hn
  have hv10 : 10 ≤ V := by have := hw.qle; omega
  have hcert : (rcCertIn X x₀).wt ≤ V :=
    (st_wt_mem (by simp : rcCertIn X x₀ ∈ [.nat 2, rcCertIn X x₀])).trans
      ((itCfOutV_wt_le hcol).trans (by omega))
  have htable : (rcColVal X).wt ≤ V := (st_wt_mem (List.mem_cons_self ..)).trans hcert
  have hqv : (Val.nat q).wt ≤ V := (wt_nat_le q).trans (by have := hw.qle; omega)
  have hfib : (itcqFV X).wt ≤ V := by
    have hqp : (q + 1) ^ 2 ≤ (q * q + 1) ^ 2 :=
      Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.le_mul_self q) 1) 2
    have h := (itcs_fv_weight X).trans (Nat.mul_le_mul_left 5 hqp)
    omega
  have hind : (natList (List.range (X.fiber.card * X.fiber.card))).wt ≤ V := by
    have hp : (X.fiber.card * X.fiber.card + 1) ^ 2 ≤ (q * q + 1) ^ 2 :=
      Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 2
    have h := (wt_range_le _).trans (Nat.mul_le_mul_left 4 hp)
    omega
  have hctx : (itcsTestCtx X x₀).wt ≤ 6 * V + 7 := st_wt_list3 hcert hfib hqv
  have hfindin : (Val.list [itcsTestCtx X x₀, natList (List.range (X.fiber.card * X.fiber.card))]).wt ≤ Bw := by
    have h := wt_list2_le (itcsTestCtx X x₀) (natList (List.range (X.fiber.card * X.fiber.card)))
    dsimp only [Bw]; omega
  have hidx : itcsImpScan X ≤ X.fiber.card * X.fiber.card := by
    have h := List.findIdx_le_length (p := itcsImpQ X)
      (xs := (List.range (X.fiber.card * X.fiber.card)).map Val.nat)
    simpa only [itcsImpScan, List.length_map, List.length_range] using h
  have hiw : (Val.nat (itcsImpScan X)).wt ≤ V :=
    (wt_nat_le _).trans (by have := hw.qsq; omega)
  have hres : (Val.list [itcqFV X, .nat (itcsImpScan X)]).wt ≤ Bw := by
    have h := wt_list2_le (itcqFV X) (.nat (itcsImpScan X))
    dsimp only [Bw]; omega
  have hscan := itcs_imp_scan_prog hfd X (itcsTestCtx X x₀)
    (Ct := itcsTestC q B) (fun t ht =>
      itcs_test_prog hi hft hfp hfs X x₀ hX hx hcol ⟨t, List.mem_range.1 ht⟩)
  have hscan' : FunDet Pg fd (.list [itcsTestCtx X x₀,
      natList (List.range (X.fiber.card * X.fiber.card))]) (.nat (itcsImpScan X)) (itcsFindC q B) := by
    apply hscan.mono
    apply Nat.add_le_add
    · exact Nat.mul_le_mul_right _ hs
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right hs 1))
        (by dsimp only [Bw, V] at hfindin ⊢; omega)
  have getTable (rest : List Val) : StDC Pg (rcCertIn X x₀ :: rest)
      (.get (.var 0) (.nat 0)) (rcColVal X) 3 0 Bw :=
    StDC.get (StDC.var' rfl (hcert.trans (by dsimp only [Bw]; omega)))
      (StDC.nat 0 (by dsimp only [Bw]; omega)) rfl (htable.trans (by dsimp only [Bw]; omega))
  have getQ (rest : List Val) : StDC Pg (rcCertIn X x₀ :: rest)
      (.length (.get (.var 0) (.nat 0))) (.nat q) 4 0 Bw := by
    have h := StDC.length (getTable rest) (by simp only [List.length_map, List.length_finRange]; dsimp only [Bw]; have := hw.qle; omega)
    simpa only [List.length_map, List.length_finRange] using h
  let Rq := natList (List.range q)
  let F := itcqFV X
  let Ts := natList (List.range (X.fiber.card * X.fiber.card))
  have rng1 := StDC.call (getQ []) (range_det hr q) (hw.range.trans (by dsimp only [Bw]; omega))
  have cert1 : StDC Pg [rcCertIn X x₀, Rq] (.var 0) (rcCertIn X x₀) 1 0 Bw :=
    StDC.var' rfl (hcert.trans (by dsimp only [Bw]; omega))
  have r1 : StDC Pg [rcCertIn X x₀, Rq] (.var 1) Rq 1 0 Bw :=
    StDC.var' rfl (hw.range.trans (by dsimp only [Bw]; omega))
  have hfltin : (Val.list [rcCertIn X x₀, Rq]).wt ≤ Bw := by
    have h := st_wt_list2 hcert hw.range
    dsimp only [Bw, Rq]; omega
  have fltCall := StDC.call (StDC.mk2 cert1 r1 hfltin (by dsimp only [Bw]; omega))
    (itcs_fiber_prog hflt hfb X x₀ hcol) (hfib.trans (by dsimp only [Bw]; omega))
  have f2 : StDC Pg [rcCertIn X x₀, Rq, F] (.var 2) F 1 0 Bw :=
    StDC.var' rfl (hfib.trans (by dsimp only [Bw]; omega))
  have lenF : StDC Pg [rcCertIn X x₀, Rq, F] (.length (.var 2)) (.nat X.fiber.card) 2 0 Bw := by
    have h := StDC.length f2 (by simp only [List.length_map, itciFl_length]; dsimp only [Bw]; have := hw.qle; omega)
    simpa only [List.length_map, itciFl_length] using h
  have nsq := StDC.arith' lenF lenF (op := .mul) (z := X.fiber.card * X.fiber.card) rfl
    (by dsimp only [Bw]; have := hw.qsq; omega)
  have rng2 := StDC.call nsq (range_det hr (X.fiber.card * X.fiber.card)) (hind.trans (by dsimp only [Bw]; omega))
  let env : List Val := [rcCertIn X x₀, Rq, F, Ts]
  have c0 : StDC Pg env (.var 0) (rcCertIn X x₀) 1 0 Bw :=
    StDC.var' rfl (hcert.trans (by dsimp only [Bw]; omega))
  have f0 : StDC Pg env (.var 2) F 1 0 Bw :=
    StDC.var' rfl (hfib.trans (by dsimp only [Bw]; omega))
  have ts0 : StDC Pg env (.var 3) Ts 1 0 Bw :=
    StDC.var' rfl (hind.trans (by dsimp only [Bw]; omega))
  have ctx := StDC.mk3 c0 f0 (getQ [Rq, F, Ts]) (hctx.trans (by dsimp only [Bw]; omega)) (by dsimp only [Bw]; omega)
  have fdCall := StDC.call (StDC.mk2 ctx ts0 hfindin (by dsimp only [Bw]; omega)) hscan'
    (hiw.trans (by dsimp only [Bw]; omega))
  have fo : StDC Pg (env ++ [.nat (itcsImpScan X)]) (.var 2) F 1 0 Bw :=
    StDC.var' rfl (hfib.trans (by dsimp only [Bw]; omega))
  have io : StDC Pg (env ++ [.nat (itcsImpScan X)]) (.var 4) (.nat (itcsImpScan X)) 1 0 Bw :=
    StDC.var' rfl (hiw.trans (by dsimp only [Bw]; omega))
  have res := StDC.mk2 fo io hres (by dsimp only [Bw]; omega)
  have body := StDC.letE rng1 (StDC.letE fltCall (StDC.letE rng2
    (StDC.letE fdCall res hres) hres) hres) hres
  have hpow : (X.fiber.card * X.fiber.card + 1) ^ 3 ≤ (q * q + 1) ^ 3 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 3
  have hcost := Nat.mul_le_mul_left 7000 hpow
  clear hw budget hcert htable hqv hfib hind hctx hfindin hidx hiw hres hscan hscan' getTable getQ
    rng1 cert1 r1 hfltin fltCall f2 lenF nsq rng2 c0 f0 ts0 ctx fdCall fo io res
  exact StDC.funDet hf body (by unfold itcsFrontC; dsimp only [Bw, V]; omega)

/-- Polynomial cost for the complete front after inserting the round's palette bound. -/
theorem itcs_front_pbu : PBU fun _ W _ => itcsFrontC (2 * W + 3) (2 * (2 * W + 3) ^ 64) := by
  simp only [itcsFrontC, itcsFindC, itcsFiberC, itcsTestC, itcsSizeC, itcsCompTotal,
    itcsCompC, itcsSqMapC, itcsCompW, itcsBalW, itCfObjB, itcsGenW, loopModK,
    countK, mapK, orbitK]
  norm_poly

end GI.Impl
