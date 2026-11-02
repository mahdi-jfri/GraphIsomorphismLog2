import Workspace.Impl.AggItemCiSojBS
import Workspace.Impl.AggItemCiSojTP

/-!
# The balance-test callback and finite conjunction

For every fiber point the callback counts its balanced vertex-color class and
checks `4m ≤ 3|C|`. The conjunction is precisely the model's balance predicate.
-/

set_option maxRecDepth 2048

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val)

variable {q : ℕ}

/-- Input `[[labels, fiber size], a]`: the integer balance test at `a`. -/
def itcsBalTestF (sz : ℕ) : Expr :=
  .arith .eq (.arith .lt (.arith .mul (.nat 3) (.get (arg 0) (.nat 1)))
    (.arith .mul (.nat 4) (.call sz (mk2 (.get (arg 0) (.nat 0)) (arg 1))))) (.nat 0)

/-- The literal per-point test. -/
theorem itcs_bal_testB {Pg : Program} {f sz cnt B W : ℕ}
    (hf : Pg.funs[f]? = some (itcsBalTestF sz))
    (hs : Pg.funs[sz]? = some (itSzB cnt)) (hc : Pg.HasAt cnt (countFuns cnt))
    (lab : Fin q → ℕ) (hl : ∀ a, lab a ≤ B) (a : Fin q) (n : ℕ)
    (hin : (Val.list [.list [encFun lab, .nat n], .nat a]).wt ≤ W)
    (hsz : (Val.list [encFun lab, .nat a]).wt ≤ W)
    (hqn : 4 * q + 3 * n + 10 ≤ W) :
    FunDet Pg f (.list [.list [encFun lab, .nat n], .nat a])
      (boolVal (decide (4 * itpSz lab a ≤ 3 * n)))
      (50 * (W + 1) + (countK + 1000) * (q + B + 1) ^ 3) := by
  let env : List Val := [.list [.list [encFun lab, .nat n], .nat a]]
  have hctx : (Val.list [encFun lab, .nat n]).wt ≤ W := (st_wt_mem (by simp)).trans hin
  have hlabels : (encFun lab).wt ≤ W := (st_wt_mem (by simp)).trans hctx
  have hn : (Val.nat n).wt ≤ W := (st_wt_mem (by simp)).trans hctx
  have g0 : StDC Pg env (arg 0) (.list [encFun lab, .nat n]) 3 0 W :=
    StDC.arg rfl hin (by omega) hctx
  have g1 : StDC Pg env (arg 1) (.nat a) 3 0 W :=
    StDC.arg rfl hin (by omega) ((st_wt_mem (by simp)).trans hin)
  have labels := StDC.get g0 (StDC.nat 0 (by omega)) rfl hlabels
  have nn := StDC.get g0 (StDC.nat 1 (by omega)) rfl hn
  have args := StDC.mk2 labels g1 hsz (by omega)
  have hsize : itpSz lab a ≤ q := (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have sc := StDC.call args (itcs_sz_palette hs hc lab hl a)
    ((wt_nat_le _).trans (by omega))
  have m4 := StDC.arith' (StDC.nat 4 (by omega)) sc (op := .mul) (z := 4 * itpSz lab a) rfl (by omega)
  have n3 := StDC.arith' (StDC.nat 3 (by omega)) nn (op := .mul) (z := 3 * n) rfl (by omega)
  have hv : Machine.BinOp.lt.eval (3 * n) (4 * itpSz lab a) =
      (decide (3 * n < 4 * itpSz lab a)).toNat := by
    by_cases hh : 3 * n < 4 * itpSz lab a <;> simp [Machine.BinOp.eval_lt, hh]
  have test := StDC.arith' n3 m4 (op := .lt) hv
    (by cases decide (3 * n < 4 * itpSz lab a) <;> simp <;> omega)
  have hv' : Machine.BinOp.eq.eval (decide (3 * n < 4 * itpSz lab a)).toNat 0 =
      (decide (4 * itpSz lab a ≤ 3 * n)).toNat := by
    by_cases hh : 4 * itpSz lab a ≤ 3 * n
    · have hlt : ¬ 3 * n < 4 * itpSz lab a := Nat.not_lt_of_ge hh
      simp [Machine.BinOp.eval_eq, hh, hlt]
    · have hlt : 3 * n < 4 * itpSz lab a := Nat.lt_of_not_ge hh
      simp [Machine.BinOp.eval_eq, hh, hlt]
  have test' := StDC.arith' test (StDC.nat 0 (by omega)) (op := .eq) hv'
    (by cases decide (4 * itpSz lab a ≤ 3 * n) <;> simp <;> omega)

  exact StDC.funDet hf test' (by omega)

open Classical in
/-- A test predicate on vertex values. Nonvertices are irrelevant to the fiber scan. -/
noncomputable def itcsBTQ (X : PairCfg q) (x₀ : Fin q) : Val → Bool
  | .nat a => if ha : a < q then decide (4 * itpSz (itcsBal X x₀) ⟨a, ha⟩ ≤ 3 * X.fiber.card) else false
  | _ => false

open Classical in
/-- A scan over the actual fiber has exactly the model's balanced truth value. -/
theorem itcs_bal_all (X : PairCfg q) (x₀ : Fin q) (hx : x₀ ∈ X.fiber) :
    ((itciFl X.fiber).map (fun a => Val.nat a.val)).all (itcsBTQ X x₀) =
      decide (∀ i, ((colorClass X.coloring false (X.idx hx) i).card : ℝ) ≤ etaB * X.fiber.card) := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, itcsBTQ, dif_pos (Fin.isLt _), decide_eq_true_eq]
  rw [itcs_bal_test X x₀ hx]
  simp only [itci_mem_fl]

/-- A finite conjunction with the installed callback, before substituting its count cost. -/
theorem itcs_bal_all_prog {Pg : Program} {all f Ct : ℕ}
    (ha : Pg.HasAt all (allFuns all f)) (X : PairCfg q) (x₀ : Fin q)
    (hf : ∀ a ∈ X.fiber, FunDet Pg f
      (.list [.list [encFun (itcsBal X x₀), .nat X.fiber.card], .nat a])
      (boolVal (decide (4 * itpSz (itcsBal X x₀) a ≤ 3 * X.fiber.card))) Ct) :
    FunDet Pg all (.list [.list [encFun (itcsBal X x₀), .nat X.fiber.card], itcqFV X])
      (boolVal (((itciFl X.fiber).map (fun a => Val.nat a.val)).all (itcsBTQ X x₀)))
      (X.fiber.card * Ct + loopModK * (X.fiber.card + 1) *
        ((Val.list [.list [encFun (itcsBal X x₀), .nat X.fiber.card], itcqFV X]).wt + X.fiber.card + 4)) := by
  have h := all_spec ha (c := .list [encFun (itcsBal X x₀), .nat X.fiber.card])
    (xs := (itciFl X.fiber).map fun a => Val.nat a.val) (q := itcsBTQ X x₀)
    (B := fun _ => Ct) (fun a ha => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
      simpa only [itcsBTQ, dif_pos i.isLt] using hf i (itci_mem_fl.1 hi))
  simpa only [List.map_map, Function.comp_def, List.map_const', List.sum_replicate, List.length_map, itciFl_length,
    itcqFV, natList, List.map_map, Function.comp_def] using h

end GI.Impl
