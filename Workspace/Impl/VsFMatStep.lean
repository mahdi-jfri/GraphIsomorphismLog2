module

public import Workspace.Impl.VStabLinVec
public import Workspace.Lang.Lib.Fold

@[expose] public section

/-!
# One step of a row-times-matrix product over `𝔽_p`

The row `a B` of a matrix product is `∑_k a_k B_k`, the rows `B_k` weighted by the entries of
`a`. It is a fold over the rows of `B` with accumulator `(k, v)`: add `a_k B_k` to `v` (by the
L0 combination `vsLin p 1 a_k v B_k`) and go to `k + 1`.

* `vsFMulAcc`: the step on numbers; `vsFAccVal`, `vsFCtx`: the values.
* `vsFMulStepF lin`: the step program, calling `vsLinFuns` at `lin`.
* `vsFMulStep_spec`: it computes the step at cost at most `2 · 10^6 (N + 1)^3`.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp)

/-- The step: add `a_k r` to `v` (modulo `p`) and go to `k + 1`. -/
def vsFMulAcc (p : ℕ) (a : List ℕ) (acc : ℕ × List ℕ) (r : List ℕ) : ℕ × List ℕ :=
  (acc.1 + 1, vsLin p 1 (a.getD acc.1 0) acc.2 r)

/-- The value of an accumulator: `[k, natList v]`. -/
def vsFAccVal (acc : ℕ × List ℕ) : Val := .list [.nat acc.1, natList acc.2]

/-- The context of the fold: `[p, natList a]`. -/
def vsFCtx (p : ℕ) (a : List ℕ) : Val := .list [.nat p, natList a]

/-- The step, on `[[p, a], [k, v], r]`. -/
def vsFMulStepF (lin : ℕ) : Expr :=
  mk2 (.arith .add (.get (arg 1) (.nat 0)) (.nat 1))
    (.call lin (.snoc (mk4 (.get (arg 0) (.nat 0)) (.nat 1)
      (.get (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 0))) (.get (arg 1) (.nat 1))) (arg 2)))

theorem wt_vsFCtx_le {p N : ℕ} {a : List ℕ} (hpN : p ≤ N) (ha : ∀ y ∈ a, y ≤ N)
    (la : a.length ≤ N) : (vsFCtx p a).wt ≤ 20 * (N + 1) ^ 2 := by
  have h1 := wt_natList_le_sq ha la
  have := wt_list2_le (.nat p) (natList a)
  have := wt_nat_le p
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  simp only [vsFCtx]
  omega

theorem wt_vsFAccVal_le {N k : ℕ} {v : List ℕ} (hk : k ≤ N) (hv : ∀ y ∈ v, y ≤ N)
    (lv : v.length ≤ N) : (vsFAccVal (k, v)).wt ≤ 20 * (N + 1) ^ 2 := by
  have h1 := wt_natList_le_sq hv lv
  have := wt_list2_le (.nat k) (natList v)
  have := wt_nat_le k
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  simp only [vsFAccVal]
  omega

/-- **The step.** With `k` below the length of `a`, the entries of `a` and `v` below `p`, `v`
not longer than `r`, and all numbers and lengths at most `N`. -/
theorem vsFMulStep_spec {P : Program} {f lin : ℕ} (hf : P.funs[f]? = some (vsFMulStepF lin))
    (hl : P.HasAt lin (vsLinFuns lin)) {p N : ℕ} (hp : 0 < p) (hpN : p ≤ N)
    {a v r : List ℕ} {k : ℕ} (ha : ∀ y ∈ a, y < p) (la : a.length ≤ N) (hk : k < a.length)
    (hv : ∀ y ∈ v, y < p) (lv : v.length ≤ N) (hr : ∀ y ∈ r, y ≤ N) (lr : r.length ≤ N)
    (hvr : v.length ≤ r.length) :
    FunDet P f (.list [vsFCtx p a, vsFAccVal (k, v), natList r])
      (vsFAccVal (vsFMulAcc p a (k, v) r)) (2 * 10 ^ 6 * (N + 1) ^ 3) := by
  set A := Val.list [vsFCtx p a, vsFAccVal (k, v), natList r] with hA
  set c := a.getD k 0 with hc
  have hcp : c < p := ha c (by simp [hc, List.getD_eq_getElem?_getD, hk])
  have haN : ∀ y ∈ a, y ≤ N := fun y hy => (ha y hy).le.trans hpN
  have hvN : ∀ y ∈ v, y ≤ N := fun y hy => (hv y hy).le.trans hpN
  have d0 := Det.arg' (P := P) (rest := []) (vs := [vsFCtx p a, vsFAccVal (k, v), natList r])
    (j := 0) rfl
  have d1 := Det.arg' (P := P) (rest := []) (vs := [vsFCtx p a, vsFAccVal (k, v), natList r])
    (j := 1) rfl
  have d2 := Det.arg' (P := P) (rest := []) (vs := [vsFCtx p a, vsFAccVal (k, v), natList r])
    (j := 2) rfl
  have dk := Det.get' d1 (Det.nat 0) (show [Val.nat k, natList v][0]? = some _ from rfl)
  have dk1 := Det.arith' (op := .add) dk (Det.nat 1) rfl
  have dp := Det.get' d0 (Det.nat 0) (show [Val.nat p, natList a][0]? = some _ from rfl)
  have da := Det.get' d0 (Det.nat 1) (show [Val.nat p, natList a][1]? = some _ from rfl)
  have dc := Det.get' da dk (natList_getElem? hk)
  have dv := Det.get' d1 (Det.nat 1) (show [Val.nat k, natList v][1]? = some _ from rfl)
  have dargs := Det.snoc (Det.mk4 dp (Det.nat 1) dc dv) d2
  have hlin := vsLin_spec (a := 1) (b := c) hl hp hvN hr lv lr hvr hpN (by omega)
    (hcp.le.trans hpN)
  have dcall := Det.call dargs hlin
  have dm := Det.mk2 dk1 dcall
  refine FunDet.intro hf (dm.mono ?_)
  -- the cost
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN3 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have wC := wt_vsFCtx_le hpN haN la
  have hkN : k ≤ N := by omega
  have wV := wt_vsFAccVal_le hkN hvN lv
  have wr := wt_natList_le_sq hr lr
  have wv := wt_natList_le_sq hvN lv
  have wa := wt_natList_le_sq haN la
  have w3 := wt_list3_le (vsFCtx p a) (vsFAccVal (k, v)) (natList r)
  have hlt : ∀ y ∈ vsLin p 1 c v r, y < p := vsLin_lt hp _ _
  have wo := wt_natList_le_sq (fun y hy => (hlt y hy).le.trans hpN)
    (by rw [vsLin_length]; exact lv)
  have wO := wt_vsFAccVal_le (k := k + 1) (v := vsLin p 1 c v r) (N := N + 1) (by omega)
    (fun y hy => (hlt y hy).le.trans (by omega)) (by rw [vsLin_length]; omega)
  have wl := wt_vsLinArg_le (p := p) (a := 1) (b := c) hvN hr lv lr hpN (by omega)
    (hcp.le.trans hpN)
  have l4 := wt_list4_le (.nat p) (.nat 1) (.nat c) (natList v)
  have l5 := wt_list_snoc_le [Val.nat p, .nat 1, .nat c, natList v] (natList r)
  have wp := wt_nat_le p
  have wc := wt_nat_le c
  have wk := wt_nat_le k
  have wk1 := wt_nat_le (k + 1)
  have w1 := wt_nat_le 1
  have e1 : (Val.list [Val.nat p, .nat 1, .nat c, natList v, natList r]).wt =
    (vsLinArg p 1 c v r).wt := rfl
  have eO : vsFAccVal (vsFMulAcc p a (k, v) r) =
    Val.list [.nat (k + 1), natList (vsLin p 1 c v r)] := rfl
  have eO' : (Val.list [.nat (k + 1), natList (vsLin p 1 c v r)]).wt ≤ 20 * (N + 2) ^ 2 := wO
  have e22 : (N + 2) ^ 2 ≤ 4 * (N + 1) ^ 2 := by nlinarith
  have eadd : BinOp.add.eval k 1 = k + 1 := rfl
  simp only [List.cons_append, List.nil_append] at *
  rw [eadd]
  try rw [← hc]
  omega

end GI.Impl
