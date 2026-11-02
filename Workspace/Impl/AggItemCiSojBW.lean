import Workspace.Impl.AggItemCiSojBT

/-! # The balance scan with all weight preconditions discharged -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val)

variable {q : ℕ}

/-- A common bound for the balanced coloring and its count arguments. -/
def itcsBTW (q B : ℕ) : ℕ := 100 * (q * (4 * B + 7) + 5 * (q + 1) ^ 2 + q + 10)

/-- Total cost of checking every color class that occurs in the source row. -/
def itcsBTC (q B : ℕ) : ℕ :=
  q * (50 * (itcsBTW q B + 1) + (countK + 1000) * (q + (2 * B + 1) + 1) ^ 3) +
    loopModK * (q + 1) * (itcsBTW q B + q + 4)

open Classical in
/-- The balance scan requires only the source object palette bound. -/
theorem itcs_bal_test_prog {Pg : Program} {all f sz cnt B : ℕ}
    (ha : Pg.HasAt all (allFuns all f)) (hf : Pg.funs[f]? = some (itcsBalTestF sz))
    (hs : Pg.funs[sz]? = some (itSzB cnt)) (hc : Pg.HasAt cnt (countFuns cnt))
    (X : PairCfg q) (x₀ : Fin q) (hx : x₀ ∈ X.fiber)
    (hcol : itCfColsLe (.pair X x₀) B) :
    FunDet Pg all (.list [.list [encFun (itcsBal X x₀), .nat X.fiber.card], itcqFV X])
      (boolVal (decide (∀ i, ((colorClass X.coloring false (X.idx hx) i).card : ℝ) ≤
        etaB * X.fiber.card))) (itcsBTC q B) := by
  have hn : X.fiber.card ≤ q := (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have hl : (encFun (itcsBal X x₀)).wt ≤ q * (4 * B + 7) + 4 := by
    have h := wt_encFun_le (itcsBal X x₀) (itcs_bal_le hcol)
    convert h using 1 <;> ring
  have hnv := wt_nat_le X.fiber.card
  have hctx := wt_list2_le (encFun (itcsBal X x₀)) (.nat X.fiber.card)
  have hmain := wt_list2_le (.list [encFun (itcsBal X x₀), .nat X.fiber.card]) (itcqFV X)
  have hfv := itcs_fv_weight X
  have hw : (Val.list [.list [encFun (itcsBal X x₀), .nat X.fiber.card], itcqFV X]).wt ≤ itcsBTW q B := by
    unfold itcsBTW
    omega
  have hscan := itcs_bal_all_prog ha X x₀ (Ct :=
      50 * (itcsBTW q B + 1) + (countK + 1000) * (q + (2 * B + 1) + 1) ^ 3)
    (fun a _ => itcs_bal_testB hf hs hc (itcsBal X x₀) (itcs_bal_le hcol) a X.fiber.card
      (by have h := wt_list2_le (.list [encFun (itcsBal X x₀), .nat X.fiber.card]) (.nat a)
          have ha := wt_nat_le (a : ℕ)
          have hqa := a.isLt
          unfold itcsBTW
          omega)
      (by have h := wt_list2_le (encFun (itcsBal X x₀)) (.nat a)
          have ha := wt_nat_le (a : ℕ)
          have hqa := a.isLt
          unfold itcsBTW
          omega)
      (by unfold itcsBTW; omega))
  rw [itcs_bal_all X x₀ hx] at hscan
  refine hscan.mono ?_
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_right _ hn
  · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right hn 1)) (by omega)

/-- The complete count test has a polynomial bound at the round's parameters. -/
theorem itcs_bal_test_pbu : PBU fun _ W _ => itcsBTC (2 * W + 3) (2 * (2 * W + 3) ^ 64) := by
  simp only [itcsBTC, itcsBTW, countK, loopModK]
  norm_poly

end GI.Impl
