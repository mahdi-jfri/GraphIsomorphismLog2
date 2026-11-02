import Workspace.Impl.AggItemCiSojScan
import Workspace.Impl.AggItemCiSojSize

/-!
# The numeric callback of the primitive/implication scan

For one ordered pair of fiber indices, read its pair color, count its component
at the source vertex, reject a diagonal pair, and test `2 * size ≤ |C|`. The
coherence lemmas in `AggItemCiSojOne` prove that this is exactly `ImpPair`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val)

variable {q : ℕ}

/-- The source data retained during the pair scan. -/
def itcsTestCtx (X : PairCfg q) (x₀ : Fin q) : Val :=
  .list [rcCertIn X x₀, itcqFV X, .nat q]

/-- Pair-table expression inside a scan callback. -/
def itcsTestTable : Expr := .get (.get (arg 0) (.nat 0)) (.nat 0)

/-- Fiber-list expression inside a scan callback. -/
def itcsTestFiber : Expr := .get (arg 0) (.nat 1)

/-- On `[source context, t]`, the literal imprimitive-pair test. -/
def itcsTestF (pc sz : ℕ) : Expr :=
  let n := Expr.length itcsTestFiber
  .letE (.call pc (mk2 (mk3 itcsTestTable itcsTestFiber n) (arg 1)))
    (.letE (.call sz (itcsMk5 itcsTestTable (.get (.get (arg 0) (.nat 0)) (.nat 1))
      (.var 1) (.get (arg 0) (.nat 2)) (.get (.get (arg 0) (.nat 0)) (.nat 2))))
      (.ite (.arith .eq (.arith .div (arg 1) n) (.arith .mod (arg 1) n)) (.nat 0)
        (.ite (.arith .lt n (.arith .mul (.nat 2) (.var 2))) (.nat 0) (.nat 1))))

/-- The callback is correct, under explicit bounds on its constructed arguments. -/
theorem itcs_test_spec {Pg : Program} {f pc sz : ℕ}
    (hf : Pg.funs[f]? = some (itcsTestF pc sz)) (hpc : Pg.funs[pc]? = some itcqPcF)
    (X : PairCfg q) (x₀ : Fin q) (hX : X.Good deltaB) (hx : x₀ ∈ X.fiber)
    (t : Fin (X.fiber.card * X.fiber.card)) {W Cs : ℕ}
    (hin : (Val.list [itcsTestCtx X x₀, .nat t]).wt ≤ W)
    (hargpc : (Val.list [.list [rcColVal X, itcqFV X, .nat X.fiber.card], .nat t]).wt ≤ W)
    (hargsz : (Val.list [rcColVal X, .nat X.j,
      .nat (itcqPC X rfl ((itciPE X.fiber.card).symm t)), .nat q, .nat x₀]).wt ≤ W)
    (hsize : FunDet Pg sz (.list [rcColVal X, .nat X.j,
      .nat (itcqPC X rfl ((itciPE X.fiber.card).symm t)), .nat q, .nat x₀])
      (.nat (itpSz (itcsLab X (itcqPC X rfl ((itciPE X.fiber.card).symm t))) x₀)) Cs)
    (hW : 2 * q + 10 ≤ W) :
    FunDet Pg f (.list [itcsTestCtx X x₀, .nat t]) (boolVal (itcsImpQ X (.nat t)))
      (200 * (W + 1) + Cs) := by
  classical
  let a := ((itciPE X.fiber.card).symm t).1
  let b := ((itciPE X.fiber.card).symm t).2
  let v := itcqPC X rfl ((itciPE X.fiber.card).symm t)
  let m := itpSz (itcsLab X v) x₀
  have hmq : m ≤ q := (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have hnq : X.fiber.card ≤ q := (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  let inp : Val := .list [itcsTestCtx X x₀, .nat t]
  have ctxw : (itcsTestCtx X x₀).wt ≤ W := (st_wt_mem (List.mem_cons_self ..)).trans hin
  have certw : (rcCertIn X x₀).wt ≤ W :=
    (st_wt_mem (by simp : rcCertIn X x₀ ∈ [rcCertIn X x₀, itcqFV X, .nat q])).trans ctxw
  have fw : (itcqFV X).wt ≤ W :=
    (st_wt_mem (by simp : itcqFV X ∈ [rcCertIn X x₀, itcqFV X, .nat q])).trans ctxw
  have qw : (Val.nat q).wt ≤ W := (wt_nat_le q).trans (by omega)
  have tablew : (rcColVal X).wt ≤ W :=
    (st_wt_mem (List.mem_cons_self ..)).trans certw
  have jw : (Val.nat X.j).wt ≤ W :=
    (st_wt_mem (by simp : Val.nat X.j ∈ [rcColVal X, .nat X.j, .nat x₀])).trans certw
  have xw : (Val.nat x₀).wt ≤ W := (wt_nat_le _).trans (by have := x₀.isLt; omega)
  have vw : (Val.nat v).wt ≤ W :=
    (st_wt_mem (by simp : Val.nat v ∈ [rcColVal X, .nat X.j, .nat v, .nat q, .nat x₀])).trans hargsz
  have pcprew : (Val.list [rcColVal X, itcqFV X, .nat X.fiber.card]).wt ≤ W :=
    (st_wt_mem (List.mem_cons_self ..)).trans hargpc
  have getCtx (rest : List Val) : StDC Pg (inp :: rest) (arg 0) (itcsTestCtx X x₀) 3 0 W :=
    StDC.arg rfl hin (by omega) ctxw
  have getT (rest : List Val) : StDC Pg (inp :: rest) (arg 1) (.nat t) 3 0 W :=
    StDC.arg rfl hin (by omega) ((st_wt_mem (by simp)).trans hin)
  have getCert (rest : List Val) : StDC Pg (inp :: rest) (.get (arg 0) (.nat 0)) (rcCertIn X x₀) 5 0 W :=
    StDC.get (getCtx rest) (StDC.nat 0 (by omega)) rfl certw
  have getTable (rest : List Val) : StDC Pg (inp :: rest) itcsTestTable (rcColVal X) 7 0 W :=
    StDC.get (getCert rest) (StDC.nat 0 (by omega)) rfl tablew
  have getFiber (rest : List Val) : StDC Pg (inp :: rest) itcsTestFiber (itcqFV X) 5 0 W :=
    StDC.get (getCtx rest) (StDC.nat 1 (by omega)) rfl fw
  have getN (rest : List Val) : StDC Pg (inp :: rest) (.length itcsTestFiber) (.nat X.fiber.card) 6 0 W := by
    have hl : ((itciFl X.fiber).map Fin.val |>.map Val.nat).length = X.fiber.card := by simp [itciFl_length]
    have h := StDC.length (getFiber rest) (by rw [hl]; omega)
    simpa only [List.length_map, itciFl_length] using h
  have getQ (rest : List Val) : StDC Pg (inp :: rest) (.get (arg 0) (.nat 2)) (.nat q) 5 0 W :=
    StDC.get (getCtx rest) (StDC.nat 2 (by omega)) rfl qw
  have pcargs := StDC.mk2 (StDC.mk3 (getTable []) (getFiber []) (getN []) pcprew (by omega))
    (getT []) hargpc (by omega)
  have pccall := StDC.call (cb := 50 * (W + 1)) pcargs (itcq_pcF_spec hpc X t hargpc) vw
  have v1 : StDC Pg (inp :: [.nat v]) (.var 1) (.nat v) 1 0 W := StDC.var' rfl vw
  have sizeargs := itcs_mk5 (getTable [.nat v])
    (StDC.get (getCert [.nat v]) (StDC.nat 1 (by omega)) (v := .nat X.j) rfl jw) v1
    (getQ [.nat v])
    (StDC.get (getCert [.nat v]) (StDC.nat 2 (by omega)) (v := .nat x₀) rfl xw) hargsz (by omega)
  have mw : (Val.nat m).wt ≤ W := (wt_nat_le _).trans (by omega)
  have szcall := StDC.call sizeargs hsize mw
  let rest : List Val := [.nat v, .nat m]
  have div := StDC.arith' (getT rest) (getN rest) (op := .div) (z := (a : ℕ)) rfl
    (by have := a.isLt; omega)
  have md := StDC.arith' (getT rest) (getN rest) (op := .mod) (z := (b : ℕ)) rfl
    (by have := b.isLt; omega)
  have diag := StDC.arith' div md (op := .eq) (z := if a = b then 1 else 0)
    (by simp [Machine.BinOp.eval_eq, Fin.ext_iff]) (by split_ifs <;> omega)
  have vm : StDC Pg (inp :: rest) (.var 2) (.nat m) 1 0 W := StDC.var' rfl mw
  have dbl := StDC.arith' (StDC.nat 2 (by omega)) vm (op := .mul) (z := 2 * m) rfl (by omega)
  have half := StDC.arith' (getN rest) dbl (op := .lt)
    (z := if X.fiber.card < 2 * m then 1 else 0) (by simp [Machine.BinOp.eval_lt]) (by split_ifs <;> omega)
  have hp : itcsImpQ X (.nat t) = decide (a ≠ b ∧ 2 * m ≤ X.fiber.card) := by
    apply Bool.eq_iff_iff.2
    rw [itcs_impQ_iff, decide_eq_true_eq]
    exact itcs_imp_one X hX hx a b
  rw [hp]
  have final : StDC Pg (inp :: rest)
      (.ite (.arith .eq (.arith .div (arg 1) (.length itcsTestFiber))
        (.arith .mod (arg 1) (.length itcsTestFiber))) (.nat 0)
        (.ite (.arith .lt (.length itcsTestFiber) (.arith .mul (.nat 2) (.var 2))) (.nat 0) (.nat 1)))
      (boolVal (decide (a ≠ b ∧ 2 * m ≤ X.fiber.card))) 60 0 W := by
    by_cases hd : a = b
    · simp only [if_pos hd] at diag
      have out : boolVal (decide (a ≠ b ∧ 2 * m ≤ X.fiber.card)) = .nat 0 := by simp [boolVal, hd]
      rw [out]
      exact (StDC.ite (nt := 1) (ne := 1) (Et := 0) (Ee := 0) diag
        (fun _ => StDC.nat 0 (by omega)) (fun h => by omega) ((wt_nat_le 0).trans (by omega))).mono (by omega) (by omega)
    · simp only [if_neg hd] at diag
      have out : boolVal (decide (a ≠ b ∧ 2 * m ≤ X.fiber.card)) =
          .nat (if X.fiber.card < 2 * m then 0 else 1) := by
        by_cases hh : X.fiber.card < 2 * m
        · simp [boolVal, hd, hh, Nat.not_le_of_lt hh]
        · simp [boolVal, hd, hh, Nat.le_of_not_gt hh]
      rw [out]
      have inner : StDC Pg (inp :: rest)
          (.ite (.arith .lt (.length itcsTestFiber) (.arith .mul (.nat 2) (.var 2))) (.nat 0) (.nat 1))
          (.nat (if X.fiber.card < 2 * m then 0 else 1)) 20 0 W := by
        by_cases hh : X.fiber.card < 2 * m
        · simp only [if_pos hh] at half ⊢
          exact (StDC.ite (nt := 1) (ne := 1) (Et := 0) (Ee := 0) half
            (fun _ => StDC.nat 0 (by omega)) (fun h => by omega) ((wt_nat_le 0).trans (by omega))).mono (by omega) (by omega)
        · simp only [if_neg hh] at half ⊢
          exact (StDC.ite (nt := 1) (ne := 1) (Et := 0) (Ee := 0) half
            (fun h => by omega) (fun _ => StDC.nat 1 (by omega)) ((wt_nat_le 1).trans (by omega))).mono (by omega) (by omega)
      exact (StDC.ite (nt := 1) (ne := 20) (Et := 0) (Ee := 0) diag
        (fun h => by omega) (fun _ => inner)
        (by split_ifs <;> exact (wt_nat_le _).trans (by omega))).mono (by omega) (by omega)
  have body := StDC.letE pccall (StDC.letE szcall final ((wt_boolVal_le _).trans (by omega)))
    ((wt_boolVal_le _).trans (by omega))
  exact StDC.funDet hf body (by omega)

end GI.Impl
