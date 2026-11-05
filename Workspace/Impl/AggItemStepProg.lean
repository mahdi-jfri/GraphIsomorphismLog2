module

public import Workspace.Impl.AggItemStepRep
public import Workspace.Impl.Combine

@[expose] public section

/-!
# The step function of the items as a program

The step function of the items is the loop of moves `cpLoopBody stp mv` of `AggCertLoop.lean`,
with the move `itSMvF m0 m1 m3`. The move reads the tag of the head `H` of the state
(`AggItemStepRep.lean`) and calls
* `m0 = itSM0F` between branches: if a branch tuple is left, start its branch with the case's
  branch state `[K.v, stTv b, w]` (tag `1`); otherwise return `[0, acc]`;
* `m1 = itSM1F disp fac` inside a branch: run the case's branch step through the dispatcher
  `disp` (on `[code, bst]`); if it finished, append its pieces and overcosets to `acc` (`fac`)
  and go on between branches (tag `0`); if it asks a call, return the call with the head of tag
  `3` as the kept value;
* `m3 = itSM3F` after a call: go on inside the branch with the case's state `[kst, u]`.

The dispatcher `itSDispF f₁ f₂ f₃` on `[code, x]` calls `f₁`, `f₂` or `f₃` on `x` by the case
code (`0` Case 1, `1` Case 2a, else Cases 2b and 3).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring)

/-! ### Programs -/

/-- The list `[a, b, c, d, e, f]`. -/
def itSMk6 (a b c d e f : Expr) : Expr := .snoc (.snoc (mk4 a b c d) e) f

/-- **The dispatcher** on `[code, x]`. -/
def itSDispF (f₁ f₂ f₃ : ℕ) : Expr :=
  .ite (arg 0) (.ite (.arith .eq (arg 0) (.nat 1)) (.call f₂ (arg 1)) (.call f₃ (arg 1)))
    (.call f₁ (arg 1))

/-- **The move**, on `[H, u]`. -/
def itSMvF (m0 m1 m3 : ℕ) : Expr :=
  .letE (.get (.var 0) (.nat 0))
  (.letE (.get (.var 1) (.nat 0))
    (.ite (.var 2)
      (.ite (.arith .eq (.var 2) (.nat 1)) (.call m1 (.var 1)) (.call m3 (.var 0)))
      (.call m0 (.var 1))))

/-- **Between branches**, on `H = [0, G, tv, j, acc, w]`. -/
def itSM0F : Expr :=
  .ite (.arith .lt (arg 3) (.length (arg 2)))
    (mk2 (.nat 2) (mk2 (itSMk6 (.nat 1) (arg 1) (arg 2) (.arith .add (arg 3) (.nat 1)) (arg 4)
      (mk3 (arg 1) (.get (arg 2) (arg 3)) (arg 5))) (.nat 0)))
    (mk2 (.nat 0) (arg 4))

/-- **Appending a branch output** on `[acc, [pv, ov, w']]`. -/
def itSFacF (app : ℕ) : Expr :=
  mk2 (.call app (mk2 (.get (arg 0) (.nat 0)) (.get (arg 1) (.nat 0))))
    (.call app (mk2 (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 1))))

/-- **Inside a branch**, on `H = [1, G, tv, j, acc, bst]`. -/
def itSM1F (disp fac : ℕ) : Expr :=
  .letE (.call disp (mk2 (.get (arg 1) (.nat 2)) (arg 5)))
    (.ite (.get (.var 1) (.nat 0))
      (mk4 (.nat 1) (.get (.var 1) (.nat 1)) (.get (.var 1) (.nat 2))
        (itSMk6 (.nat 3) (arg 1) (arg 2) (arg 3) (arg 4) (.get (.var 1) (.nat 3))))
      (mk2 (.nat 2) (mk2 (itSMk6 (.nat 0) (arg 1) (arg 2) (arg 3)
        (.call fac (mk2 (arg 4) (.get (.var 1) (.nat 1)))) (.get (.get (.var 1) (.nat 1)) (.nat 2)))
        (.nat 0))))

/-- **After a call**, on `[H, u]` with `H = [3, G, tv, j, acc, kst]`. -/
def itSM3F : Expr :=
  .letE (.get (.var 0) (.nat 0))
    (mk2 (.nat 2) (mk2 (itSMk6 (.nat 1) (.get (.var 1) (.nat 1)) (.get (.var 1) (.nat 2))
      (.get (.var 1) (.nat 3)) (.get (.var 1) (.nat 4))
      (mk2 (.get (.var 1) (.nat 5)) (.get (.var 0) (.nat 1)))) (.nat 0)))

/-! ### Small specifications -/

theorem Det.itSMk6 {P : Program} {env : List Val} {a b c d e f : Expr} {va vb vc vd ve vf : Val}
    {ca cb cc cd ce cf : ℕ} (ha : Det P env a va ca) (hb : Det P env b vb cb)
    (hc : Det P env c vc cc) (hd : Det P env d vd cd) (he : Det P env e ve ce)
    (hf : Det P env f vf cf) :
    Det P env (itSMk6 a b c d e f) (.list [va, vb, vc, vd, ve, vf])
      (ca + cb + cc + cd + ce + cf + 6 * (Val.list [va, vb, vc, vd, ve, vf]).wt + 20) := by
  have h1 := wt_list_mono (show [va, vb, vc, vd] <+: [va, vb, vc, vd, ve, vf] from ⟨[ve, vf], rfl⟩)
  have h2 := wt_list_mono (show [va, vb, vc, vd, ve] <+: [va, vb, vc, vd, ve, vf] from ⟨[vf], rfl⟩)
  exact (Det.snoc (Det.snoc (Det.mk4 ha hb hc hd) he) hf).mono
    (by simp only [List.cons_append, List.nil_append] at *; omega)

/-- The cost of the dispatcher besides the call. -/
def itSDispC (W : ℕ) : ℕ := 40 * W + 200

/-- The function of a case: `f₁` in Case 1, `f₂` in Case 2a, `f₃` in Cases 2b and 3. -/
def itSCaseF (f₁ f₂ f₃ : ℕ) : AggCase → ℕ
  | .one => f₁
  | .twoA => f₂
  | .twoB => f₃
  | .three => f₃

/-- **The dispatcher calls the function of the case.** -/
theorem itS_disp_spec {P : Program} {fd f₁ f₂ f₃ : ℕ} (hd : P.funs[fd]? = some (itSDispF f₁ f₂ f₃))
    (a : AggCase) (x : Val) {Q : Val → ℕ → Prop} (h : FunAll P (itSCaseF f₁ f₂ f₃ a) x Q) :
    FunAll P fd (.list [.nat (AggCase.code a), x]) (fun w c => ∃ c', Q w c' ∧
      c ≤ c' + itSDispC (Val.list [.nat (AggCase.code a), x]).wt + 3 * w.wt) := by
  have wc : (Val.nat (AggCase.code a)).wt ≤ 5 := (wt_nat_le _).trans (by have := it_code_le a; omega)
  refine FunAll.intro hd ?_
  have d1 : Det P [.list [.nat (AggCase.code a), x]] (arg 1) x _ :=
    Det.arg' (vs := [.nat (AggCase.code a), x]) (j := 1) rfl
  have d0 : Det P [.list [.nat (AggCase.code a), x]] (arg 0) (.nat (AggCase.code a)) _ :=
    Det.arg' (vs := [.nat (AggCase.code a), x]) (j := 0) rfl
  have hv1 : x.wt < (Val.list [.nat (AggCase.code a), x]).wt := wt_le_wt_list (by simp)
  have key : ∀ g, FunAll P g x Q → EvalAll P [.list [.nat (AggCase.code a), x]] (.call g (arg 1))
      (fun w c => ∃ c', Q w c' ∧
        c ≤ c' + 2 * (Val.list [.nat (AggCase.code a), x]).wt + 7 + w.wt + 1) := fun g hg =>
    EvalAll.call_funAll d1 fun v' ca h' => by
      obtain ⟨rfl, hca⟩ := h'
      exact FunAll.mono hg fun w c hw => ⟨c, hw, by omega⟩
  unfold itSDispF
  cases a with
  | one =>
    refine EvalAll.ite d0 (fun _ _ h => ⟨_, h.1⟩) fun y cc hy => ?_
    obtain ⟨hy, hcc⟩ := hy
    cases hy
    simp only [AggCase.code, if_true]
    refine EvalAll.mono (key f₁ h) fun w c ⟨c', hq, hc⟩ => ⟨c', hq, ?_⟩
    unfold itSDispC
    simp only [AggCase.code] at *
    omega
  | twoA =>
    refine EvalAll.ite d0 (fun _ _ h => ⟨_, h.1⟩) fun y cc hy => ?_
    obtain ⟨hy, hcc⟩ := hy
    cases hy
    simp only [AggCase.code, one_ne_zero, if_false]
    have dt := Det.arith' (op := .eq) d0 (Det.nat 1) (z := 1) (by simp [GI.Machine.BinOp.eval, AggCase.code])
    refine EvalAll.ite dt (fun _ _ h => ⟨_, h.1⟩) fun y' cc' hy' => ?_
    obtain ⟨hy', hcc'⟩ := hy'
    cases hy'
    simp only [one_ne_zero, if_false]
    refine EvalAll.mono (key f₂ h) fun w c ⟨c', hq, hc⟩ => ⟨c', hq, ?_⟩
    unfold itSDispC
    simp only [AggCase.code] at *
    omega
  | twoB =>
    refine EvalAll.ite d0 (fun _ _ h => ⟨_, h.1⟩) fun y cc hy => ?_
    obtain ⟨hy, hcc⟩ := hy
    cases hy
    simp only [AggCase.code, OfNat.ofNat_ne_zero, if_false]
    have dt := Det.arith' (op := .eq) d0 (Det.nat 1) (z := 0) (by simp [GI.Machine.BinOp.eval, AggCase.code])
    refine EvalAll.ite dt (fun _ _ h => ⟨_, h.1⟩) fun y' cc' hy' => ?_
    obtain ⟨hy', hcc'⟩ := hy'
    cases hy'
    simp only [if_true]
    refine EvalAll.mono (key f₃ h) fun w c ⟨c', hq, hc⟩ => ⟨c', hq, ?_⟩
    unfold itSDispC
    simp only [AggCase.code] at *
    omega
  | three =>
    refine EvalAll.ite d0 (fun _ _ h => ⟨_, h.1⟩) fun y cc hy => ?_
    obtain ⟨hy, hcc⟩ := hy
    cases hy
    simp only [AggCase.code, OfNat.ofNat_ne_zero, if_false]
    have dt := Det.arith' (op := .eq) d0 (Det.nat 1) (z := 0) (by simp [GI.Machine.BinOp.eval, AggCase.code])
    refine EvalAll.ite dt (fun _ _ h => ⟨_, h.1⟩) fun y' cc' hy' => ?_
    obtain ⟨hy', hcc'⟩ := hy'
    cases hy'
    simp only [if_true]
    refine EvalAll.mono (key f₃ h) fun w c ⟨c', hq, hc⟩ => ⟨c', hq, ?_⟩
    unfold itSDispC
    simp only [AggCase.code] at *
    omega

theorem wt_list6_le (a b c d e f : Val) :
    (Val.list [a, b, c, d, e, f]).wt ≤ 2 * (a.wt + b.wt + c.wt + d.wt + e.wt + f.wt) + 10 := by
  have := wt_list_le [a, b, c, d, e, f]; simp at this; omega

/-- The entries of a list of six values weigh less than the list. -/
theorem wt_list6_lt (a b c d e f : Val) :
    a.wt + b.wt + c.wt + d.wt + e.wt + f.wt < (Val.list [a, b, c, d, e, f]).wt := by
  have := sum_wt_lt_wt_list [a, b, c, d, e, f]; simp at this; omega

/-- The cost bound of the moves `m0` and `m3`, for states of weight at most `W`. -/
def itSM3C (W : ℕ) : ℕ := 1000 * W + 1000

/-- **After a call.** -/
theorem itS_m3_spec {P : Program} {m3 : ℕ} (hm : P.funs[m3]? = some itSM3F) {k q : ℕ} (G : Val)
    (j : ℕ) (pcs : List (Perm (Fin k) × Acc k)) (os : List (LcOver q)) (kst u : Val) :
    FunDet P m3 (.list [itSH 3 G j pcs os kst, u])
      (.list [.nat 2, .list [itSH 1 G j pcs os (.list [kst, u]), .nat 0]])
      (itSM3C (Val.list [itSH 3 G j pcs os kst, u]).wt) := by
  have eH : itSH 3 G j pcs os kst =
      .list [.nat 3, G, itSTv q, .nat j, itSOutV pcs os, kst] := rfl
  have eH' : itSH 1 G j pcs os (.list [kst, u]) =
      .list [.nat 1, G, itSTv q, .nat j, itSOutV pcs os, .list [kst, u]] := rfl
  rw [eH, eH']
  refine FunDet.intro hm ?_
  have dH : Det P [.list [.list [.nat 3, G, itSTv q, .nat j, itSOutV pcs os, kst], u]]
      (.get (.var 0) (.nat 0)) (.list [.nat 3, G, itSTv q, .nat j, itSOutV pcs os, kst]) _ :=
    Det.get' (Det.var' (i := 0) rfl) (Det.nat 0) rfl
  refine (Det.letE dH (Det.mk2 (Det.nat 2) (Det.mk2 (Det.itSMk6 (Det.nat 1)
    (Det.get' (Det.var' (i := 1) rfl) (Det.nat 1) rfl) (Det.get' (Det.var' (i := 1) rfl) (Det.nat 2) rfl)
    (Det.get' (Det.var' (i := 1) rfl) (Det.nat 3) rfl) (Det.get' (Det.var' (i := 1) rfl) (Det.nat 4) rfl)
    (Det.mk2 (Det.get' (Det.var' (i := 1) rfl) (Det.nat 5) rfl)
      (Det.get' (Det.var' (i := 0) rfl) (Det.nat 1) rfl))) (Det.nat 0)))).mono ?_
  have h6 := wt_list6_lt (.nat 3) G (itSTv q) (.nat j) (itSOutV pcs os) kst
  have h6' := wt_list6_le (.nat 1) G (itSTv q) (.nat j) (itSOutV pcs os) (.list [kst, u])
  have hs := sum_wt_lt_wt_list [.list [.nat 3, G, itSTv q, .nat j, itSOutV pcs os, kst], u]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hs
  have hku := wt_list2_le kst u
  have h1 := wt_list2_le (.list [.nat 1, G, itSTv q, .nat j, itSOutV pcs os, .list [kst, u]])
    (.nat 0)
  have h2 := wt_list2_le (.nat 2)
    (.list [.list [.nat 1, G, itSTv q, .nat j, itSOutV pcs os, .list [kst, u]], .nat 0])
  have := wt_nat_le 0
  have := wt_nat_le 1
  have := wt_nat_le 2
  unfold itSM3C
  omega

/-- **Between branches, a tuple left**: start its branch. -/
theorem itS_m0_next {P : Program} {m0 : ℕ} (hm : P.funs[m0]? = some itSM0F) {k q : ℕ} (G : Val)
    (j : ℕ) (pcs : List (Perm (Fin k) × Acc k)) (os : List (LcOver q)) (w : Val)
    {b : Fin (P₀.κ + 1) → Fin q} (hb : (itSTups q)[j]? = some b) :
    FunDet P m0 (itSH 0 G j pcs os w)
      (.list [.nat 2, .list [itSH 1 G (j + 1) pcs os (.list [G, stTv b, w]), .nat 0]])
      (itSM3C (itSH 0 G j pcs os w).wt) := by
  have eH : itSH 0 G j pcs os w = .list [.nat 0, G, itSTv q, .nat j, itSOutV pcs os, w] := rfl
  have eH' : itSH 1 G (j + 1) pcs os (.list [G, stTv b, w]) =
      .list [.nat 1, G, itSTv q, .nat (j + 1), itSOutV pcs os, .list [G, stTv b, w]] := rfl
  have hj : j < (itSTups q).length := by
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.1 hb; exact h
  have hbv : ((itSTups q).map stTv)[j]? = some (stTv b) := by
    rw [List.getElem?_map, hb]; rfl
  have wb : (stTv b).wt < (itSTv q).wt := wt_le_wt_list (List.mem_of_getElem? hbv)
  rw [eH, eH']
  refine FunDet.intro hm ?_
  set H := Val.list [.nat 0, G, itSTv q, .nat j, itSOutV pcs os, w] with hH
  have d3 : Det P [H] (arg 3) (.nat j) _ :=
    Det.arg' (vs := [.nat 0, G, itSTv q, .nat j, itSOutV pcs os, w]) (j := 3) rfl
  have d2 : Det P [H] (arg 2) (.list ((itSTups q).map stTv)) _ :=
    Det.arg' (vs := [.nat 0, G, itSTv q, .nat j, itSOutV pcs os, w]) (j := 2) rfl
  have dt := Det.arith (op := .lt) d3 (Det.length d2)
  have he : GI.Machine.BinOp.lt.eval j ((itSTups q).map stTv).length = 1 := by
    simp [GI.Machine.BinOp.eval, hj]
  rw [he] at dt
  have d1 : Det P [H] (arg 1) G _ :=
    Det.arg' (vs := [.nat 0, G, itSTv q, .nat j, itSOutV pcs os, w]) (j := 1) rfl
  have d4 : Det P [H] (arg 4) (itSOutV pcs os) _ :=
    Det.arg' (vs := [.nat 0, G, itSTv q, .nat j, itSOutV pcs os, w]) (j := 4) rfl
  have d5 : Det P [H] (arg 5) w _ :=
    Det.arg' (vs := [.nat 0, G, itSTv q, .nat j, itSOutV pcs os, w]) (j := 5) rfl
  have dj : Det P [H] (.arith .add (arg 3) (.nat 1)) (.nat (j + 1)) _ :=
    Det.arith (op := .add) d3 (Det.nat 1)
  have dg := Det.get' d2 d3 hbv
  refine (Det.ite_pos dt one_ne_zero (Det.mk2 (Det.nat 2) (Det.mk2 (Det.itSMk6 (Det.nat 1) d1 d2 dj d4
    (Det.mk3 d1 dg d5)) (Det.nat 0)))).mono ?_
  have h6 := wt_list6_lt (.nat 0) G (itSTv q) (.nat j) (itSOutV pcs os) w
  have eH2 : (Val.list [.nat 0, G, itSTv q, .nat j, itSOutV pcs os, w]).wt = H.wt := rfl
  have h6' := wt_list6_le (.nat 1) G (itSTv q) (.nat (j + 1)) (itSOutV pcs os)
    (.list [G, stTv b, w])
  have hj1 := wt_nat_le (j + 1)
  have hjw := wt_nat j
  have hjl := GI.Machine.len_le_self j
  have h3 := wt_list3_le G (stTv b) w
  have h1 := wt_list2_le (.list [.nat 1, G, itSTv q, .nat (j + 1), itSOutV pcs os,
    .list [G, stTv b, w]]) (.nat 0)
  have h2 := wt_list2_le (.nat 2) (.list [.list [.nat 1, G, itSTv q, .nat (j + 1), itSOutV pcs os,
    .list [G, stTv b, w]], .nat 0])
  have := wt_nat_le 0
  have := wt_nat_le 1
  have := wt_nat_le 2
  have hlen : (itSTups q).length < (itSTv q).wt := by
    have := length_lt_wt_list ((itSTups q).map stTv)
    rw [List.length_map] at this
    exact this
  have etv : (Val.list ((itSTups q).map stTv)).wt = (itSTv q).wt := rfl
  have hjl1 := len_add_le' j 1
  have hj1w := wt_nat (j + 1)
  have hb2 : (Val.nat (GI.Machine.BinOp.add.eval j 1)).wt = (Val.nat (j + 1)).wt := rfl
  have hl2 := length_lt_wt_list ((itSTups q).map stTv)
  rw [List.length_map] at hl2
  have hvl : ((itSTups q).map stTv).length = (itSTups q).length := List.length_map _
  have etv' : itSTv q = .list ((itSTups q).map stTv) := rfl
  rw [etv'] at h6 h6' h1 h2 wb hlen
  have eH3 : (Val.list [.nat 0, G, .list ((itSTups q).map stTv), .nat j, itSOutV pcs os, w]).wt =
    H.wt := rfl
  unfold itSM3C
  omega

/-- **Between branches, no tuple left**: return the pieces and overcosets. -/
theorem itS_m0_end {P : Program} {m0 : ℕ} (hm : P.funs[m0]? = some itSM0F) {k q : ℕ} (G : Val)
    (j : ℕ) (pcs : List (Perm (Fin k) × Acc k)) (os : List (LcOver q)) (w : Val)
    (hj : (itSTups q).length ≤ j) :
    FunDet P m0 (itSH 0 G j pcs os w) (.list [.nat 0, itSOutV pcs os])
      (itSM3C (itSH 0 G j pcs os w).wt) := by
  have eH : itSH 0 G j pcs os w =
      .list [.nat 0, G, .list ((itSTups q).map stTv), .nat j, itSOutV pcs os, w] := rfl
  rw [eH]
  refine FunDet.intro hm ?_
  have d3 : Det P [.list [.nat 0, G, .list ((itSTups q).map stTv), .nat j, itSOutV pcs os, w]]
      (arg 3) (.nat j) _ :=
    Det.arg' (vs := [.nat 0, G, .list ((itSTups q).map stTv), .nat j, itSOutV pcs os, w]) (j := 3) rfl
  have d2 : Det P [.list [.nat 0, G, .list ((itSTups q).map stTv), .nat j, itSOutV pcs os, w]]
      (arg 2) (.list ((itSTups q).map stTv)) _ :=
    Det.arg' (vs := [.nat 0, G, .list ((itSTups q).map stTv), .nat j, itSOutV pcs os, w]) (j := 2) rfl
  have d4 : Det P [.list [.nat 0, G, .list ((itSTups q).map stTv), .nat j, itSOutV pcs os, w]]
      (arg 4) (itSOutV pcs os) _ :=
    Det.arg' (vs := [.nat 0, G, .list ((itSTups q).map stTv), .nat j, itSOutV pcs os, w]) (j := 4) rfl
  have dt := Det.arith (op := .lt) d3 (Det.length d2)
  have he : GI.Machine.BinOp.lt.eval j ((itSTups q).map stTv).length = 0 := by
    simp only [GI.Machine.BinOp.eval, List.length_map]
    rw [if_neg (by omega)]
  rw [he] at dt
  refine (Det.ite_zero dt (Det.mk2 (Det.nat 0) d4)).mono ?_
  have h6 := wt_list6_lt (.nat 0) G (.list ((itSTups q).map stTv)) (.nat j) (itSOutV pcs os) w
  have h2 := wt_list2_le (.nat 0) (itSOutV pcs os)
  have hl2 := length_lt_wt_list ((itSTups q).map stTv)
  have := wt_nat_le 0
  unfold itSM3C
  omega

/-- **`append` as a deterministic function**, for inputs of weight at most `W`. -/
theorem itS_app_det {P : Program} {app : ℕ} (h : P.HasAt app (appendFuns app)) (xs ys : List Val)
    {W : ℕ} (hW : (Val.list [.list xs, .list ys]).wt ≤ W) :
    FunDet P app (.list [.list xs, .list ys]) (.list (xs ++ ys)) (5000 * (W + 1) ^ 2) := by
  refine FunAll.mono (append_spec h xs ys) fun w c ⟨hw, hc⟩ => ⟨hw, ?_⟩
  subst hw
  have h1 := wt_list_append_le xs ys
  have hx : (Val.list xs).wt < (Val.list [.list xs, .list ys]).wt := wt_le_wt_list (by simp)
  have hy : (Val.list ys).wt < (Val.list [.list xs, .list ys]).wt := wt_le_wt_list (by simp)
  have hl := length_lt_wt_list ys
  have : loopModK * (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length +
      (Val.list (xs ++ ys)).wt + 1) ≤ 1000 * (W + 1) * (5 * (W + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e : 1000 * (W + 1) * (5 * (W + 1)) = 5000 * (W + 1) ^ 2 := by ring
  unfold loopModK at this hc
  omega

/-- The cost bound of `itSFacF` for inputs of weight at most `W`. -/
def itSFacC (W : ℕ) : ℕ := 10 ^ 6 * (W + 1) ^ 2

/-- **Appending a branch output.** -/
theorem itS_fac_spec {P : Program} {fac app : ℕ} (hf : P.funs[fac]? = some (itSFacF app))
    (happ : P.HasAt app (appendFuns app)) {k q : ℕ} (pcs pcs' : List (Perm (Fin k) × Acc k))
    (os os' : List (LcOver q)) (w' : Val) :
    FunDet P fac (.list [itSOutV pcs os, .list [.list (pcs'.map encPiece),
        .list (os'.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2), w']])
      (itSOutV (pcs ++ pcs') (os ++ os'))
      (itSFacC (Val.list [itSOutV pcs os, .list [.list (pcs'.map encPiece),
        .list (os'.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2), w']]).wt) := by
  set A := pcs.map encPiece with hA
  set A' := pcs'.map encPiece with hA'
  set B := os.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2 with hB
  set B' := os'.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2 with hB'
  have eo : itSOutV (pcs ++ pcs') (os ++ os') = .list [.list (A ++ A'), .list (B ++ B')] := by
    simp only [itSOutV, List.map_append, hA, hA', hB, hB']
  have ei : itSOutV pcs os = .list [.list A, .list B] := rfl
  rw [eo, ei]
  refine FunDet.intro hf ?_
  have wv := wt_list2_le (.list [.list A, .list B]) (.list [.list A', .list B', w'])
  have wa : (Val.list [.list A, .list B]).wt < (Val.list [.list [.list A, .list B],
      .list [.list A', .list B', w']]).wt := wt_le_wt_list (by simp)
  have wb : (Val.list [.list A', .list B', w']).wt < (Val.list [.list [.list A, .list B],
      .list [.list A', .list B', w']]).wt := wt_le_wt_list (by simp)
  have wA : (Val.list A).wt < (Val.list [.list A, .list B]).wt := wt_le_wt_list (by simp)
  have wB : (Val.list B).wt < (Val.list [.list A, .list B]).wt := wt_le_wt_list (by simp)
  have wA' : (Val.list A').wt < (Val.list [.list A', .list B', w']).wt := wt_le_wt_list (by simp)
  have wB' : (Val.list B').wt < (Val.list [.list A', .list B', w']).wt := wt_le_wt_list (by simp)
  set W := (Val.list [.list [.list A, .list B], .list [.list A', .list B', w']]).wt with hW
  have h1 := wt_list2_le (.list A) (.list A')
  have h2 := wt_list2_le (.list B) (.list B')
  have d1 := itS_app_det happ A A' (W := 4 * W + 6) (by omega)
  have d2 := itS_app_det happ B B' (W := 4 * W + 6) (by omega)
  have r0 : Det P [.list [.list [.list A, .list B], .list [.list A', .list B', w']]] (arg 0)
      (.list [.list A, .list B]) _ := Det.arg' (vs := [.list [.list A, .list B],
        .list [.list A', .list B', w']]) (j := 0) rfl
  have r1 : Det P [.list [.list [.list A, .list B], .list [.list A', .list B', w']]] (arg 1)
      (.list [.list A', .list B', w']) _ := Det.arg' (vs := [.list [.list A, .list B],
        .list [.list A', .list B', w']]) (j := 1) rfl
  refine (Det.mk2 (Det.call (Det.mk2 (Det.get' r0 (Det.nat 0) rfl) (Det.get' r1 (Det.nat 0) rfl)) d1)
    (Det.call (Det.mk2 (Det.get' r0 (Det.nat 1) rfl) (Det.get' r1 (Det.nat 1) rfl)) d2)).mono ?_
  have hAA := wt_list_append_le A A'
  have hBB := wt_list_append_le B B'
  have h3 := wt_list2_le (.list (A ++ A')) (.list (B ++ B'))
  have p1 : (4 * W + 6 + 1) ^ 2 ≤ 49 * (W + 1) ^ 2 := by
    have : 4 * W + 6 + 1 ≤ 7 * (W + 1) := by omega
    calc (4 * W + 6 + 1) ^ 2 ≤ (7 * (W + 1)) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 49 * (W + 1) ^ 2 := by ring
  have pW : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h4 := wt_list2_le (.list A') (.list B')
  have := wt_nat_le 0
  have := wt_nat_le 1
  unfold itSFacC
  simp only [Nat.reducePow] at *
  omega

/-- The cost bound of the move inside a branch, besides the case's step: `W` bounds the head and
`Cd` the cost of the dispatched call. -/
def itSM1C (W Cd : ℕ) : ℕ := Cd + itSFacC (2 * (W + Cd) + 6) + 1000 * (W + Cd) + 1000

set_option maxHeartbeats 1000000 in
/-- **Inside a branch**: the case's step through the dispatcher, then either the call it asks, or
the output appended and the next branch. -/
theorem itS_m1_spec {P : Program} {m1 disp fac app : ℕ} (hm : P.funs[m1]? = some (itSM1F disp fac))
    (hfac : P.funs[fac]? = some (itSFacF app)) (happ : P.HasAt app (appendFuns app)) {k q : ℕ}
    (st ws sr : Val) (code : ℕ) (j : ℕ) (pcs : List (Perm (Fin k) × Acc k)) (os : List (LcOver q))
    (bst : Val) {Cd : ℕ}
    {R0 : List (Perm (Fin k) × Acc k) → List (LcOver q) → Val → Prop} {R1 : Val → Val → Val → Prop}
    (hd : FunAll P disp (.list [.nat code, bst]) (fun w c => c ≤ Cd ∧
      ((∃ pcs' os' w', w = .list [.nat 0, .list [.list (pcs'.map encPiece),
          .list (os'.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2), w']] ∧ R0 pcs' os' w') ∨
        (∃ cm arg kst, w = .list [.nat 1, cm, arg, kst] ∧ R1 cm arg kst)))) :
    FunAll P m1 (itSH 1 (.list [st, ws, .nat code, sr]) j pcs os bst) (fun w c =>
      c ≤ itSM1C (itSH 1 (.list [st, ws, .nat code, sr]) j pcs os bst).wt Cd ∧
      ((∃ pcs' os' w', R0 pcs' os' w' ∧
          w = .list [.nat 2, .list [itSH 0 (.list [st, ws, .nat code, sr]) j (pcs ++ pcs') (os ++ os') w',
            .nat 0]]) ∨
        (∃ cm arg kst, R1 cm arg kst ∧
          w = .list [.nat 1, cm, arg, itSH 3 (.list [st, ws, .nat code, sr]) j pcs os kst]))) := by
  set G := Val.list [st, ws, .nat code, sr] with hG
  have eH : itSH 1 G j pcs os bst = .list [.nat 1, G, itSTv q, .nat j, itSOutV pcs os, bst] := rfl
  rw [eH]
  set H := Val.list [.nat 1, G, itSTv q, .nat j, itSOutV pcs os, bst] with hH
  refine FunAll.intro hm ?_
  have hHs := wt_list6_lt (.nat 1) G (itSTv q) (.nat j) (itSOutV pcs os) bst
  have eHw : (Val.list [.nat 1, G, itSTv q, .nat j, itSOutV pcs os, bst]).wt = H.wt := rfl
  have rd : ∀ (i : ℕ) (v : Val), [Val.nat 1, G, itSTv q, .nat j, itSOutV pcs os, bst][i]? = some v →
      ∀ (rest : List Val), Det P (H :: rest) (arg i) v (2 * H.wt + i + 5) := fun i v hv rest =>
    Det.arg' (vs := [.nat 1, G, itSTv q, .nat j, itSOutV pcs os, bst]) hv
  have dcode : Det P [H] (.get (arg 1) (.nat 2)) (.nat code) _ :=
    Det.get' (rd 1 G rfl []) (Det.nat 2) (vs := [st, ws, .nat code, sr]) rfl
  have darg := Det.mk2 dcode (rd 5 bst rfl [])
  have wG : G.wt < H.wt := by omega
  have wcode : (Val.nat code).wt < G.wt := wt_le_wt_list (by simp)
  have wcb := wt_list2_le (.nat code) bst
  refine EvalAll.letE (Ra := fun w c => c ≤ 10 * H.wt + 50 + Cd + w.wt + 1 ∧ w.wt < Cd ∧
      ((∃ pcs' os' w', w = .list [.nat 0, .list [.list (pcs'.map encPiece),
          .list (os'.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2), w']] ∧ R0 pcs' os' w') ∨
        (∃ cm arg kst, w = .list [.nat 1, cm, arg, kst] ∧ R1 cm arg kst)))
    (EvalAll.call_funAll darg fun v ca hv => ?_) fun w cw hw => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine FunAll.mono hd.wt_lt fun w c ⟨⟨hc, hp⟩, hwc⟩ => ⟨?_, by omega, hp⟩
    have := wt_nat_le 2
    omega
  have ra : ∀ (i : ℕ) (v : Val), [Val.nat 1, G, itSTv q, .nat j, itSOutV pcs os, bst][i]? = some v →
      Det P ([H] ++ [w]) (arg i) v (2 * H.wt + i + 5) := fun i v hv => rd i v hv [w]
  have hwW : w.wt < Cd := hw.2.1
  obtain ⟨hcw, -, ⟨pcs', os', w', rfl, h0⟩ | ⟨cm, ag, kst, rfl, h1⟩⟩ := hw
  · -- the branch is finished
    set A' := pcs'.map encPiece with hA'
    set B' := os'.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2 with hB'
    have dw : Det P ([H] ++ [.list [.nat 0, .list [.list A', .list B', w']]]) (.var 1)
        (.list [.nat 0, .list [.list A', .list B', w']]) _ := Det.var' (i := 1) rfl
    have dt := Det.get' dw (Det.nat 0) (vs := [.nat 0, .list [.list A', .list B', w']]) rfl
    have dout := Det.get' dw (Det.nat 1) (vs := [.nat 0, .list [.list A', .list B', w']]) rfl
    have dw' := Det.get' dout (Det.nat 2) (vs := [.list A', .list B', w']) rfl
    have dfac := Det.call (Det.mk2 (ra 4 _ rfl) dout) (itS_fac_spec hfac happ pcs pcs' os os' w')
    refine EvalAll.mono (Det.ite_zero dt (Det.mk2 (Det.nat 2) (Det.mk2 (Det.itSMk6 (Det.nat 0)
      (ra 1 _ rfl) (ra 2 _ rfl) (ra 3 _ rfl) dfac dw') (Det.nat 0)))) fun v cv ⟨hv, hcv⟩ => ⟨?_, Or.inl ⟨pcs', os', w', h0, ?_⟩⟩
    · subst hv
      have s3 := sum_wt_lt_wt_list [.list A', .list B', w']
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at s3
      have s2 := sum_wt_lt_wt_list [.nat 0, .list [.list A', .list B', w']]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at s2
      have eo : itSOutV (pcs ++ pcs') (os ++ os') =
          .list [.list ((pcs.map encPiece) ++ A'),
            .list ((os.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2) ++ B')] := by
        simp only [itSOutV, List.map_append, hA', hB']
      have ei : itSOutV pcs os = .list [.list (pcs.map encPiece),
          .list (os.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2)] := rfl
      have sA := sum_wt_lt_wt_list [.list (pcs.map encPiece),
          .list (os.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2)]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at sA
      rw [← ei] at sA
      have ha1 := wt_list_append_le (pcs.map encPiece) A'
      have ha2 := wt_list_append_le (os.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2) B'
      have ho := wt_list2_le (.list ((pcs.map encPiece) ++ A'))
        (.list ((os.map fun o => lcOv (o.1 : Perm (Fin q)) o.2.2) ++ B'))
      rw [← eo] at ho
      have hin := wt_list2_le (itSOutV pcs os) (.list [.list A', .list B', w'])
      have hmono : itSFacC (Val.list [itSOutV pcs os, .list [.list A', .list B', w']]).wt ≤
          itSFacC (2 * (H.wt + Cd) + 6) := by
        unfold itSFacC
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      have e1 : (Val.list [itSOutV pcs os, Val.list [Val.list (List.map encPiece pcs'),
          Val.list (List.map (fun o => lcOv (o.1 : Perm (Fin q)) o.2.2) os'), w']]).wt =
          (Val.list [itSOutV pcs os, .list [.list A', .list B', w']]).wt := rfl
      have e2 : itSFacC (Val.list [itSOutV pcs os, Val.list [Val.list (List.map encPiece pcs'),
          Val.list (List.map (fun o => lcOv (o.1 : Perm (Fin q)) o.2.2) os'), w']]).wt =
          itSFacC (Val.list [itSOutV pcs os, .list [.list A', .list B', w']]).wt := rfl
      have h6 := wt_list6_le (.nat 0) G (itSTv q) (.nat j) (itSOutV (pcs ++ pcs') (os ++ os')) w'
      have h2a := wt_list2_le (.list [.nat 0, G, itSTv q, .nat j, itSOutV (pcs ++ pcs') (os ++ os'), w'])
        (.nat 0)
      have h2b := wt_list2_le (.nat 2) (.list [.list [.nat 0, G, itSTv q, .nat j,
        itSOutV (pcs ++ pcs') (os ++ os'), w'], .nat 0])
      have := wt_nat_le 0
      have := wt_nat_le 1
      have := wt_nat_le 2
      unfold itSM1C
      omega
    · rw [hv]; rfl
  · -- the case asks a call
    have dw : Det P ([H] ++ [.list [.nat 1, cm, ag, kst]]) (.var 1) (.list [.nat 1, cm, ag, kst]) _ :=
      Det.var' (i := 1) rfl
    have dt := Det.get' dw (Det.nat 0) (vs := [.nat 1, cm, ag, kst]) rfl
    refine EvalAll.mono (Det.ite_pos dt one_ne_zero (Det.mk4 (Det.nat 1)
      (Det.get' dw (Det.nat 1) (vs := [.nat 1, cm, ag, kst]) rfl)
      (Det.get' dw (Det.nat 2) (vs := [.nat 1, cm, ag, kst]) rfl)
      (Det.itSMk6 (Det.nat 3) (ra 1 _ rfl) (ra 2 _ rfl) (ra 3 _ rfl) (ra 4 _ rfl)
        (Det.get' dw (Det.nat 3) (vs := [.nat 1, cm, ag, kst]) rfl)))) fun v cv ⟨hv, hcv⟩ => ⟨?_, Or.inr ⟨cm, ag, kst, h1, ?_⟩⟩
    · subst hv
      have s4 := sum_wt_lt_wt_list [.nat 1, cm, ag, kst]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at s4
      have h6 := wt_list6_le (.nat 3) G (itSTv q) (.nat j) (itSOutV pcs os) kst
      have h4 := wt_list4_le (.nat 1) cm ag (.list [.nat 3, G, itSTv q, .nat j, itSOutV pcs os, kst])
      have := wt_nat_le 0
      have := wt_nat_le 1
      have := wt_nat_le 2
      have := wt_nat_le 3
      unfold itSM1C
      omega
    · rw [hv]; rfl

/-- The cost of the move besides the call of `m0`, `m1` or `m3`. -/
def itSMvC (W : ℕ) : ℕ := 40 * W + 200

/-- The function the move calls at a tag. -/
def itSMvG (m0 m1 m3 tag : ℕ) : ℕ := if tag = 0 then m0 else if tag = 1 then m1 else m3

/-- **The move calls the function of the tag.** On a state `[H, u]` with `H` of tag `tag`, the
move calls `m0` or `m1` on `H` (tags `0`, `1`), or `m3` on the state (other tags). -/
theorem itS_mv_spec {P : Program} {mv m0 m1 m3 : ℕ} (hm : P.funs[mv]? = some (itSMvF m0 m1 m3))
    (tag : ℕ) (rest : List Val) (u : Val) {Q : Val → ℕ → Prop}
    (h : FunAll P (itSMvG m0 m1 m3 tag)
      (if tag = 0 ∨ tag = 1 then .list (.nat tag :: rest) else .list [.list (.nat tag :: rest), u])
      Q) :
    FunAll P mv (.list [.list (.nat tag :: rest), u]) (fun w c => ∃ c', Q w c' ∧
      c ≤ c' + itSMvC (Val.list [.list (.nat tag :: rest), u]).wt + 6 * w.wt) := by
  refine FunAll.intro hm ?_
  have wH : (Val.list (.nat tag :: rest)).wt < (Val.list [.list (.nat tag :: rest), u]).wt :=
    wt_le_wt_list (by simp)
  have wt0 : (Val.nat tag).wt < (Val.list (.nat tag :: rest)).wt := wt_le_wt_list (by simp)
  have dH : Det P [.list [.list (.nat tag :: rest), u]] (.get (.var 0) (.nat 0))
      (.list (.nat tag :: rest)) _ :=
    Det.get' (Det.var' (i := 0) rfl) (Det.nat 0) (vs := [.list (.nat tag :: rest), u]) rfl
  unfold itSMvF
  refine EvalAll.letE dH fun v cv ⟨hv, hcv⟩ => ?_
  subst hv
  have dT : Det P ([.list [.list (.nat tag :: rest), u]] ++ [.list (.nat tag :: rest)])
      (.get (.var 1) (.nat 0)) (.nat tag) _ :=
    Det.get' (Det.var' (i := 1) rfl) (Det.nat 0) (vs := .nat tag :: rest) rfl
  refine EvalAll.letE dT fun v ct ⟨hv, hct⟩ => ?_
  subst hv
  have d2 : Det P ([.list [.list (.nat tag :: rest), u]] ++ [.list (.nat tag :: rest)] ++
      [.nat tag]) (.var 2) (.nat tag) _ := Det.var' (i := 2) rfl
  have hw2 := wt_nat_le 2
  have hw0 := wt_nat_le 0
  by_cases h0 : tag = 0
  · subst h0
    refine EvalAll.ite d2 (fun _ _ h => ⟨_, h.1⟩) fun y cc ⟨hy, hcc⟩ => ?_
    cases hy
    simp only [if_true]
    refine EvalAll.call_funAll (Det.var' (i := 1) rfl) fun v ca ⟨hv, hca⟩ => ?_
    subst hv
    refine FunAll.mono h fun w c hw => ⟨c, hw, ?_⟩
    unfold itSMvC
    omega
  · refine EvalAll.ite d2 (fun _ _ h => ⟨_, h.1⟩) fun y cc ⟨hy, hcc⟩ => ?_
    cases hy
    simp only [if_neg h0]
    by_cases h1 : tag = 1
    · subst h1
      have dt := Det.arith' (op := .eq) d2 (Det.nat 1) (z := 1) (by simp [GI.Machine.BinOp.eval])
      refine EvalAll.ite dt (fun _ _ h => ⟨_, h.1⟩) fun y' cc' ⟨hy', hcc'⟩ => ?_
      cases hy'
      simp only [one_ne_zero, if_false]
      refine EvalAll.call_funAll (Det.var' (i := 1) rfl) fun v ca ⟨hv, hca⟩ => ?_
      subst hv
      refine FunAll.mono h fun w c hw => ⟨c, hw, ?_⟩
      have := wt_nat_le 1
      unfold itSMvC
      omega
    · have dt := Det.arith' (op := .eq) d2 (Det.nat 1) (z := 0) (by
        simp [GI.Machine.BinOp.eval, h1])
      refine EvalAll.ite dt (fun _ _ h => ⟨_, h.1⟩) fun y' cc' ⟨hy', hcc'⟩ => ?_
      cases hy'
      simp only [if_true]
      refine EvalAll.call_funAll (Det.var' (i := 0) rfl) fun v ca ⟨hv, hca⟩ => ?_
      subst hv
      have e1 : itSMvG m0 m1 m3 tag = m3 := by simp [itSMvG, h0, h1]
      have e2 : (if tag = 0 ∨ tag = 1 then Val.list (.nat tag :: rest)
          else .list [.list (.nat tag :: rest), u]) = .list [.list (.nat tag :: rest), u] := by
        simp [h0, h1]
      rw [e1, e2] at h
      refine FunAll.mono h fun w c hw => ⟨c, hw, ?_⟩
      have := wt_nat_le 1
      unfold itSMvC
      omega

theorem itS_mv_spec0 {P : Program} {mv m0 m1 m3 : ℕ} (hm : P.funs[mv]? = some (itSMvF m0 m1 m3))
    (rest : List Val) (u : Val) {Q : Val → ℕ → Prop} (h : FunAll P m0 (.list (.nat 0 :: rest)) Q) :
    FunAll P mv (.list [.list (.nat 0 :: rest), u]) (fun w c => ∃ c', Q w c' ∧
      c ≤ c' + itSMvC (Val.list [.list (.nat 0 :: rest), u]).wt + 6 * w.wt) := by
  refine itS_mv_spec hm 0 rest u ?_
  have e : itSMvG m0 m1 m3 0 = m0 := if_pos rfl
  rw [e, if_pos (Or.inl rfl)]
  exact h

theorem itS_mv_spec1 {P : Program} {mv m0 m1 m3 : ℕ} (hm : P.funs[mv]? = some (itSMvF m0 m1 m3))
    (rest : List Val) (u : Val) {Q : Val → ℕ → Prop} (h : FunAll P m1 (.list (.nat 1 :: rest)) Q) :
    FunAll P mv (.list [.list (.nat 1 :: rest), u]) (fun w c => ∃ c', Q w c' ∧
      c ≤ c' + itSMvC (Val.list [.list (.nat 1 :: rest), u]).wt + 6 * w.wt) := by
  refine itS_mv_spec hm 1 rest u ?_
  have e : itSMvG m0 m1 m3 1 = m1 := by simp [itSMvG]
  rw [e, if_pos (Or.inr rfl)]
  exact h

theorem itS_mv_spec3 {P : Program} {mv m0 m1 m3 : ℕ} (hm : P.funs[mv]? = some (itSMvF m0 m1 m3))
    (rest : List Val) (u : Val) {Q : Val → ℕ → Prop}
    (h : FunAll P m3 (.list [.list (.nat 3 :: rest), u]) Q) :
    FunAll P mv (.list [.list (.nat 3 :: rest), u]) (fun w c => ∃ c', Q w c' ∧
      c ≤ c' + itSMvC (Val.list [.list (.nat 3 :: rest), u]).wt + 6 * w.wt) := by
  refine itS_mv_spec hm 3 rest u ?_
  have e : itSMvG m0 m1 m3 3 = m3 := by simp [itSMvG]
  rw [e, if_neg (by omega)]
  exact h

end GI.Impl
