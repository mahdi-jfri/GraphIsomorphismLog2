module

public import Workspace.Impl.AggItemCiSojBT

@[expose] public section

/-!
# Checking that target components have at least two points

Count a component only for a point in the target fiber. Omitted points pass the
check without counting. This is the condition that lets the size-colored Case 1
partition program represent the model's two-colored component partition.
-/

set_option maxRecDepth 2048

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {q : ℕ}

/-- On `[[component labels, rcCertIn Y y₀], a]`, test the interior block size. -/
def itcsMinF (fb sz : ℕ) : Expr :=
  .ite (.call fb (mk2 (.get (arg 0) (.nat 1)) (arg 1)))
    (.arith .lt (.nat 1) (.call sz (mk2 (.get (arg 0) (.nat 0)) (arg 1)))) (.nat 1)

open Classical in
/-- The lower-size callback on the literal target components. -/
theorem itcs_min_spec {Pg : Program} {f fb sz cnt Bw : ℕ}
    (hf : Pg.funs[f]? = some (itcsMinF fb sz)) (hb : Pg.funs[fb]? = some itcqFbT)
    (hs : Pg.funs[sz]? = some (itSzB cnt)) (hc : Pg.HasAt cnt (countFuns cnt))
    (Y : PairCfg q) (y₀ a : Fin q) (v : ℕ)
    (hin : (Val.list [.list [encFun (itcsLab Y v), rcCertIn Y y₀], .nat a]).wt ≤ Bw)
    (hfb : (Val.list [rcCertIn Y y₀, .nat a]).wt ≤ Bw)
    (hsz : (Val.list [encFun (itcsLab Y v), .nat a]).wt ≤ Bw) (hq : q + 10 ≤ Bw) :
    FunDet Pg f (.list [.list [encFun (itcsLab Y v), rcCertIn Y y₀], .nat a])
      (boolVal (decide (a ∈ Y.fiber → 2 ≤ (Y.comp v a).card)))
      (200 * (Bw + 1) + (countK + 1000) * (q + 1) ^ 3) := by
  let env : List Val := [.list [.list [encFun (itcsLab Y v), rcCertIn Y y₀], .nat a]]
  have hctx : (Val.list [encFun (itcsLab Y v), rcCertIn Y y₀]).wt ≤ Bw :=
    (st_wt_mem (by simp)).trans hin
  have a0 : StDC Pg env (arg 0) (.list [encFun (itcsLab Y v), rcCertIn Y y₀]) 3 0 Bw :=
    StDC.arg rfl hin (by omega) hctx
  have a1 : StDC Pg env (arg 1) (.nat a) 3 0 Bw :=
    StDC.arg rfl hin (by omega) ((st_wt_mem (by simp)).trans hin)
  have tab := StDC.get a0 (StDC.nat 0 (by omega)) rfl
    ((st_wt_mem (List.mem_cons_self ..)).trans hctx)
  have cert := StDC.get a0 (StDC.nat 1 (by omega)) rfl
    ((st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans hctx)
  have fbcall := StDC.call (cb := 30 * (Bw + 1)) (StDC.mk2 cert a1 hfb (by omega))
    (itcq_fbT_spec hb Y y₀ a hfb) ((wt_boolVal_le _).trans (by omega))
  have he : itcqFq Y (.nat a) = decide (a ∈ Y.fiber) := by simp [itcqFq, a.isLt, PairCfg.mem_fiber]
  rw [he] at fbcall
  have hsize : itpSz (itcsLab Y v) a ≤ q :=
    (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have sizecall := StDC.call (cb := countK * (q + 1) ^ 3 + 1000 * (q + 1) ^ 3) (StDC.mk2 tab a1 hsz (by omega))
    (it_szB_spec hs hc (itcs_lab_lt Y v) a) ((wt_nat_le _).trans (by omega))
  have test := StDC.arith' (StDC.nat 1 (by omega)) sizecall (op := .lt)
    (z := if 1 < itpSz (itcsLab Y v) a then 1 else 0) rfl (by split_ifs <;> omega)
  have hszc : itpSz (itcsLab Y v) a = (Y.comp v a).card := by rw [itpSz, itcs_lab_blk]
  have body : StDC Pg env (itcsMinF fb sz)
      (boolVal (decide (a ∈ Y.fiber → 2 ≤ (Y.comp v a).card))) 100
      (30 * (Bw + 1) + (countK + 1000) * (q + 1) ^ 3) Bw := by
    by_cases ha : a ∈ Y.fiber
    · simp only [ha, true_implies, decide_true, boolVal, Bool.toNat_true] at fbcall ⊢
      have hout : (Val.nat (decide (2 ≤ (Y.comp v a).card)).toNat).wt ≤ Bw :=
        (wt_boolVal_le _).trans (by omega)
      have ht : (if 1 < itpSz (itcsLab Y v) a then 1 else 0) =
          (decide (2 ≤ (Y.comp v a).card)).toNat := by
        rw [hszc]
        by_cases hh : 2 ≤ (Y.comp v a).card
        · simp [hh, show 1 < (Y.comp v a).card by omega]
        · simp [hh, show ¬ 1 < (Y.comp v a).card by omega]
      rw [ht] at test
      exact (StDC.ite (nt := 30) (ne := 1) (Et := (countK + 1000) * (q + 1) ^ 3)
        (Ee := 0) fbcall (fun _ => test.mono (by omega) (by simp only [Nat.add_mul]; omega))
        (fun h => by omega) hout).mono (by omega) (by simp only [Nat.add_mul]; omega)
    · simp only [ha, decide_false, boolVal, Bool.toNat_false, false_implies, decide_true,
        Bool.toNat_true] at fbcall ⊢
      exact (StDC.ite (nt := 30) (ne := 1) (Et := (countK + 1000) * (q + 1) ^ 3)
        (Ee := 0) fbcall (fun h => by omega) (fun _ => StDC.nat 1 (by omega))
        ((wt_nat_le 1).trans (by omega))).mono (by omega) (by omega)
  exact StDC.funDet hf body (by omega)

end GI.Impl
