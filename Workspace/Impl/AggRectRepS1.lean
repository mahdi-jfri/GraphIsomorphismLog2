import Workspace.Impl.AggRectRepLib

/-!
# The small steps of the representation program

Each step function computes a number function on its input, at cost linear in the weight of its
input. The number functions (`rcRSwN`, `rcRGrN`, `rcRCondN`) are the ones the program computes;
`AggRectRepEq*.lean` relates them to the mathematics.
-/

namespace GI.Impl

open GI.Lang
open GI.Machine (BinOp)
open GI.Cited (Val)

/-! ### Number functions -/

/-- The transposition `(x y)` at `z`. -/
def rcRSwN (x y z : ℕ) : ℕ := if z = x then y else if z = y then x else z

/-- The generator `swap w₀ w₁ * swap a b` at `j` (when `c ≠ 0`), else `j`. -/
def rcRGrN (a b w₀ w₁ c j : ℕ) : ℕ := if c = 0 then j else rcRSwN w₀ w₁ (rcRSwN a b j)

/-- The test of a generator: `a ≠ b` and `a, b` on the same sides of `W` and `R`. -/
def rcRCondN (wl rl : List ℕ) (a b : ℕ) : ℕ :=
  BinOp.eval .mul (BinOp.eval .eq (BinOp.eval .eq a b) 0)
    (BinOp.eval .mul (BinOp.eval .eq (wl.getD a 0) (wl.getD b 0))
      (BinOp.eval .eq (rl.getD a 0) (rl.getD b 0)))

/-- The generator for `t < q²`, as the list of its images. -/
def rcRGenL (wl rl : List ℕ) (w₀ w₁ q t : ℕ) : List ℕ :=
  (List.range q).map (rcRGrN (t / q) (t % q) w₀ w₁ (rcRCondN wl rl (t / q) (t % q)))

theorem rcR_swN_mem (x y z : ℕ) : rcRSwN x y z = x ∨ rcRSwN x y z = y ∨ rcRSwN x y z = z := by
  unfold rcRSwN; split_ifs <;> simp

theorem rcR_eval_eq_le (a b : ℕ) : BinOp.eval .eq a b ≤ 1 := by
  simp only [BinOp.eval]; split_ifs <;> omega

theorem rcR_eval_lt_le (a b : ℕ) : BinOp.eval .lt a b ≤ 1 := by
  simp only [BinOp.eval]; split_ifs <;> omega

theorem rcR_eval_mul_le {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : BinOp.eval .mul a b ≤ 1 := by
  simp only [BinOp.eval]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with rfl | rfl <;> omega

theorem rcR_condN_le (wl rl : List ℕ) (a b : ℕ) : rcRCondN wl rl a b ≤ 1 :=
  rcR_eval_mul_le (rcR_eval_eq_le _ _)
    (rcR_eval_mul_le (rcR_eval_eq_le _ _) (rcR_eval_eq_le _ _))

/-! ### Reading entries -/

section Read

variable {P : Program}

/-- Entry `j` of entry `0` of the argument. -/
theorem rcR_rd0 {vs cs rest : List Val} {j : ℕ} {v : Val} (h0 : vs[0]? = some (.list cs))
    (hj : cs[j]? = some v) :
    Det P (.list vs :: rest) (.get (arg 0) (.nat j)) v
      (2 * (Val.list vs).wt + 5 + (.list cs : Val).wt + 1 + j + 3 + v.wt + 1) := by
  have := Det.get' (Det.arg' (P := P) (rest := rest) h0) (Det.nat j) hj
  refine this.mono ?_
  omega

end Read

/-! ### The transposition -/

theorem Det.rcSw {P : Program} {env : List Val} {x y z : Expr} {X Y Z cx cy cz : ℕ}
    (hx : Det P env x (.nat X) cx) (hy : Det P env y (.nat Y) cy) (hz : Det P env z (.nat Z) cz) :
    Det P env (rcRSw x y z) (.nat (rcRSwN X Y Z))
      (2 * cx + 2 * cy + 3 * cz + 2 * ((Val.nat X).wt + (Val.nat Y).wt + (Val.nat Z).wt) + 20) := by
  unfold rcRSw rcREq rcRSwN
  by_cases h1 : Z = X
  · have dt := Det.arith' (op := .eq) hz hx (z := 1) (by simp [BinOp.eval, h1])
    rw [if_pos h1]
    exact (Det.ite_pos dt one_ne_zero hy).mono (by omega)
  · have dt := Det.arith' (op := .eq) hz hx (z := 0) (by simp [BinOp.eval, h1])
    rw [if_neg h1]
    by_cases h2 : Z = Y
    · have dt2 := Det.arith' (op := .eq) hz hy (z := 1) (by simp [BinOp.eval, h2])
      rw [if_pos h2]
      exact (Det.ite_zero dt (Det.ite_pos dt2 one_ne_zero hx)).mono (by omega)
    · have dt2 := Det.arith' (op := .eq) hz hy (z := 0) (by simp [BinOp.eval, h2])
      rw [if_neg h2]
      exact (Det.ite_zero dt (Det.ite_zero dt2 hz)).mono (by omega)

/-! ### Steps -/

section Steps

variable {P : Program} {I : RcRIdx}

/-- `get 0` on the second entry. -/
theorem rcR_g0_spec {f : ℕ} (hf : P.funs[f]? = some rcRGet0F) (c a : Val) (r : List Val) :
    FunDet P f (.list [c, .list (a :: r)]) a (10 * ((Val.list [c, .list (a :: r)]).wt + 10)) := by
  have g1 := Det.arg' (P := P) (vs := [c, .list (a :: r)]) (rest := []) (j := 1) rfl
  have ha : a.wt < (Val.list (a :: r)).wt := wt_le_wt_list (by simp)
  have hl : (Val.list (a :: r)).wt < (Val.list [c, .list (a :: r)]).wt := wt_le_wt_list (by simp)
  exact FunDet.intro hf ((Det.get' g1 (Det.nat 0) (v := a) rfl).mono (by omega))

/-- `get 1` on the second entry. -/
theorem rcR_g1_spec {f : ℕ} (hf : P.funs[f]? = some rcRGet1F) (c a b : Val) (r : List Val) :
    FunDet P f (.list [c, .list (a :: b :: r)]) b
      (10 * ((Val.list [c, .list (a :: b :: r)]).wt + 10)) := by
  have g1 := Det.arg' (P := P) (vs := [c, .list (a :: b :: r)]) (rest := []) (j := 1) rfl
  have hb : b.wt < (Val.list (a :: b :: r)).wt := wt_le_wt_list (by simp)
  have hl : (Val.list (a :: b :: r)).wt < (Val.list [c, .list (a :: b :: r)]).wt :=
    wt_le_wt_list (by simp)
  exact FunDet.intro hf ((Det.get' g1 (Det.nat 1) (v := b) rfl).mono (by omega))

/-- **One image of a generator.** -/
theorem rcR_grF_spec {f : ℕ} (hf : P.funs[f]? = some rcRGrF) (a b w₀ w₁ c j : ℕ) :
    FunDet P f (.list [.list [.nat a, .nat b, .nat w₀, .nat w₁, .nat c], .nat j])
      (.nat (rcRGrN a b w₀ w₁ c j))
      (100 * ((Val.list [.list [.nat a, .nat b, .nat w₀, .nat w₁, .nat c], .nat j]).wt + 10)) := by
  set C5 : Val := .list [.nat a, .nat b, .nat w₀, .nat w₁, .nat c] with hC5
  set v : Val := .list [C5, .nat j] with hv
  have wC : C5.wt < v.wt := wt_le_wt_list (by simp)
  have e1 : (Val.list [C5, .nat j]).wt = v.wt := rfl
  have e2 : (Val.list [.nat a, .nat b, .nat w₀, .nat w₁, .nat c]).wt = C5.wt := rfl
  have wj : (Val.nat j).wt < v.wt := wt_le_wt_list (by simp)
  have wa : (Val.nat a).wt < C5.wt := wt_le_wt_list (by simp [hC5])
  have wb : (Val.nat b).wt < C5.wt := wt_le_wt_list (by simp [hC5])
  have w0 : (Val.nat w₀).wt < C5.wt := wt_le_wt_list (by simp [hC5])
  have w1 : (Val.nat w₁).wt < C5.wt := wt_le_wt_list (by simp [hC5])
  have wc : (Val.nat c).wt < C5.wt := wt_le_wt_list (by simp [hC5])
  have r0 := rcR_rd0 (P := P) (vs := [C5, .nat j]) (rest := []) (j := 0) (v := .nat a) rfl rfl
  have r1 := rcR_rd0 (P := P) (vs := [C5, .nat j]) (rest := []) (j := 1) (v := .nat b) rfl rfl
  have aj := Det.arg' (P := P) (vs := [C5, .nat j]) (rest := []) (j := 1) (v := .nat j) rfl
  have s1 := Det.rcSw r0 r1 aj
  have wS : (Val.nat (rcRSwN a b j)).wt < v.wt := by
    rcases rcR_swN_mem a b j with h | h | h <;> rw [h] <;> omega
  have q2 := rcR_rd0 (P := P) (vs := [C5, .nat j]) (rest := [.nat (rcRSwN a b j)]) (j := 2) (v := .nat w₀) rfl rfl
  have q3 := rcR_rd0 (P := P) (vs := [C5, .nat j]) (rest := [.nat (rcRSwN a b j)]) (j := 3) (v := .nat w₁) rfl rfl
  have q4 := rcR_rd0 (P := P) (vs := [C5, .nat j]) (rest := [.nat (rcRSwN a b j)]) (j := 4) (v := .nat c) rfl rfl
  have vS := Det.var' (P := P) (env := [v, .nat (rcRSwN a b j)]) (i := 1) (v := .nat (rcRSwN a b j)) rfl
  have aj' := Det.arg' (P := P) (vs := [C5, .nat j]) (rest := [.nat (rcRSwN a b j)]) (j := 1) (v := .nat j) rfl
  have wG : (Val.nat (rcRGrN a b w₀ w₁ c j)).wt < v.wt := by
    unfold rcRGrN
    split_ifs
    · exact wj
    · rcases rcR_swN_mem w₀ w₁ (rcRSwN a b j) with h | h | h <;> rw [h] <;> omega
  refine FunDet.intro hf ?_
  unfold rcRGrF
  by_cases hc : c = 0
  · subst hc
    have e : rcRGrN a b w₀ w₁ 0 j = j := by simp [rcRGrN]
    rw [e] at wG ⊢
    exact (Det.letE s1 (Det.ite_zero q4 aj')).mono (by omega)
  · have e : rcRGrN a b w₀ w₁ c j = rcRSwN w₀ w₁ (rcRSwN a b j) := by simp [rcRGrN, hc]
    rw [e] at wG ⊢
    exact (Det.letE s1 (Det.ite_pos q4 hc (Det.rcSw q2 q3 vS))).mono (by omega)

end Steps

section Gen

variable {P : Program} {I : RcRIdx}

set_option maxHeartbeats 1000000 in
/-- **One generator.** -/
theorem rcR_genF_spec (hgD : P.funs[I.gD]? = some rcRGetDF) (hf : P.funs[I.genF]? = some I.genFF)
    (hm : P.HasAt I.mGR (mapFuns I.mGR I.grF)) (hgr : P.funs[I.grF]? = some rcRGrF)
    (wl rl : List ℕ) (w₀ w₁ q t : ℕ) {W : ℕ}
    (hW : 30 * ((Val.list [.list [natList wl, natList rl, .nat w₀, .nat w₁, .nat q,
      natList (List.range q)], .nat t]).wt + 10) ≤ W)
    (hout : (natList (rcRGenL wl rl w₀ w₁ q t)).wt ≤ W) :
    FunDet P I.genF (.list [.list [natList wl, natList rl, .nat w₀, .nat w₁, .nat q,
      natList (List.range q)], .nat t]) (natList (rcRGenL wl rl w₀ w₁ q t))
      (5000 * (W + 1) ^ 3) := by
  have wC : (Val.list [natList wl, natList rl, .nat w₀, .nat w₁, .nat q,
      natList (List.range q)]).wt < (Val.list [.list [natList wl, natList rl, .nat w₀, .nat w₁,
      .nat q, natList (List.range q)], .nat t]).wt := wt_le_wt_list (by simp)
  have wt' : (Val.nat t).wt < (Val.list [.list [natList wl, natList rl, .nat w₀, .nat w₁, .nat q,
      natList (List.range q)], .nat t]).wt := wt_le_wt_list (by simp)
  have ww : (natList wl).wt < (Val.list [natList wl, natList rl, .nat w₀, .nat w₁, .nat q,
      natList (List.range q)]).wt := wt_le_wt_list (by simp)
  have wr : (natList rl).wt < (Val.list [natList wl, natList rl, .nat w₀, .nat w₁, .nat q,
      natList (List.range q)]).wt := wt_le_wt_list (by simp)
  have w0 : (Val.nat w₀).wt < (Val.list [natList wl, natList rl, .nat w₀, .nat w₁, .nat q,
      natList (List.range q)]).wt := wt_le_wt_list (by simp)
  have w1 : (Val.nat w₁).wt < (Val.list [natList wl, natList rl, .nat w₀, .nat w₁, .nat q,
      natList (List.range q)]).wt := wt_le_wt_list (by simp)
  have wq : (Val.nat q).wt < (Val.list [natList wl, natList rl, .nat w₀, .nat w₁, .nat q,
      natList (List.range q)]).wt := wt_le_wt_list (by simp)
  have wR : (natList (List.range q)).wt < (Val.list [natList wl, natList rl, .nat w₀, .nat w₁,
      .nat q, natList (List.range q)]).wt := wt_le_wt_list (by simp)
  have wa : (Val.nat (t / q)).wt ≤ (Val.nat t).wt := rcR_wt_nat_mono (Nat.div_le_self _ _)
  have wb : (Val.nat (t % q)).wt ≤ (Val.nat t).wt := rcR_wt_nat_mono (Nat.mod_le _ _)
  -- the parts of the input, at each depth of the environment
  have gC : ∀ rest : List Val, ∀ j v, [natList wl, natList rl, Val.nat w₀, .nat w₁, .nat q,
      natList (List.range q)][j]? = some v → Det P (.list [.list [natList wl, natList rl, .nat w₀,
      .nat w₁, .nat q, natList (List.range q)], .nat t] :: rest) (.get (arg 0) (.nat j)) v _ :=
    fun rest j v h => rcR_rd0 (rest := rest) (cs := [natList wl, natList rl, .nat w₀, .nat w₁,
      .nat q, natList (List.range q)]) rfl h
  have at1 : ∀ rest : List Val, Det P (.list [.list [natList wl, natList rl, .nat w₀, .nat w₁,
      .nat q, natList (List.range q)], .nat t] :: rest) (arg 1) (.nat t) _ :=
    fun rest => Det.arg' (rest := rest) (j := 1) rfl
  have da := Det.arithW (op := .div) (at1 []) (gC [] 4 (.nat q) rfl) (z := t / q) rfl
  have db := Det.arithW (op := .mod) (at1 [.nat (t / q)]) (gC [.nat (t / q)] 4 (.nat q) rfl)
    (z := t % q) rfl
  -- the test
  have va : Det P [.list [.list [natList wl, natList rl, .nat w₀, .nat w₁, .nat q,
      natList (List.range q)], .nat t], .nat (t / q), .nat (t % q)] (.var 1) (.nat (t / q)) _ :=
    Det.var' rfl
  have vb : Det P [.list [.list [natList wl, natList rl, .nat w₀, .nat w₁, .nat q,
      natList (List.range q)], .nat t], .nat (t / q), .nat (t % q)] (.var 2) (.nat (t % q)) _ :=
    Det.var' rfl
  have gw := gC [.nat (t / q), .nat (t % q)] 0 (natList wl) rfl
  have gr := gC [.nat (t / q), .nat (t % q)] 1 (natList rl) rfl
  have dwa := Det.rcGdN I hgD gw va (Det.nat 0)
  have dwb := Det.rcGdN I hgD gw vb (Det.nat 0)
  have dra := Det.rcGdN I hgD gr va (Det.nat 0)
  have drb := Det.rcGdN I hgD gr vb (Det.nat 0)
  have dcond := Det.arith (op := .mul) (Det.arith (op := .eq) (Det.arith (op := .eq) va vb)
    (Det.nat 0)) (Det.arith (op := .mul) (Det.arith (op := .eq) dwa dwb)
      (Det.arith (op := .eq) dra drb))
  have ec : BinOp.eval .mul (BinOp.eval .eq (BinOp.eval .eq (t / q) (t % q)) 0)
      (BinOp.eval .mul (BinOp.eval .eq (wl.getD (t / q) 0) (wl.getD (t % q) 0))
        (BinOp.eval .eq (rl.getD (t / q) 0) (rl.getD (t % q) 0))) =
      rcRCondN wl rl (t / q) (t % q) := rfl
  rw [ec] at dcond
  have hc1 := rcR_condN_le wl rl (t / q) (t % q)
  -- the inner map
  have hin2 : (Val.list [.list [.nat (t / q), .nat (t % q), .nat w₀, .nat w₁,
      .nat (rcRCondN wl rl (t / q) (t % q))], natList (List.range q)]).wt ≤ W := by
    have h1 := wt_list2_le (.list [.nat (t / q), .nat (t % q), .nat w₀, .nat w₁,
      .nat (rcRCondN wl rl (t / q) (t % q))]) (natList (List.range q))
    have h2 := wt_list_le [Val.nat (t / q), .nat (t % q), .nat w₀, .nat w₁,
      .nat (rcRCondN wl rl (t / q) (t % q))]
    have h3 := wt_nat_le (rcRCondN wl rl (t / q) (t % q))
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at h2
    omega
  have hmap := rcR_mapN1 hm (c := .list [.nat (t / q), .nat (t % q), .nat w₀, .nat w₁,
      .nat (rcRCondN wl rl (t / q) (t % q))]) (xs := List.range q)
    (g := fun j => .nat (rcRGrN (t / q) (t % q) w₀ w₁ (rcRCondN wl rl (t / q) (t % q)) j))
    (K := 100) (W := W) (fun j _ => rcR_grF_spec hgr _ _ _ _ _ _) hin2 (by
      have e : (List.range q).map (fun j => Val.nat (rcRGrN (t / q) (t % q) w₀ w₁
          (rcRCondN wl rl (t / q) (t % q)) j)) = (rcRGenL wl rl w₀ w₁ q t).map Val.nat := by
        simp [rcRGenL, List.map_map]
      rw [e]; exact hout)
  have e2 : Val.list ((List.range q).map (fun j => Val.nat (rcRGrN (t / q) (t % q) w₀ w₁
      (rcRCondN wl rl (t / q) (t % q)) j))) = natList (rcRGenL wl rl w₀ w₁ q t) := by
    simp [rcRGenL, natList, List.map_map]
  rw [e2] at hmap
  have dctx := Det.mk2 (Det.mk5 (Det.var' (P := P) (env := [.list [.list [natList wl, natList rl,
      .nat w₀, .nat w₁, .nat q, natList (List.range q)], .nat t], .nat (t / q), .nat (t % q),
      .nat (rcRCondN wl rl (t / q) (t % q))]) (i := 1) rfl)
    (Det.var' (i := 2) rfl) (gC [.nat (t / q), .nat (t % q), .nat (rcRCondN wl rl (t / q) (t % q))]
      2 (.nat w₀) rfl)
    (gC [.nat (t / q), .nat (t % q), .nat (rcRCondN wl rl (t / q) (t % q))] 3 (.nat w₁) rfl)
    (Det.var' (i := 3) rfl))
    (gC [.nat (t / q), .nat (t % q), .nat (rcRCondN wl rl (t / q) (t % q))] 5
      (natList (List.range q)) rfl)
  have dcall := Det.call dctx hmap
  refine FunDet.intro hf ((Det.letE da (Det.letE db (Det.letE dcond dcall))).mono ?_)
  clear dcall dctx hmap da db dcond dwa dwb dra drb gw gr va vb gC at1
  have w3 := wt_nat_le (rcRCondN wl rl (t / q) (t % q))
  have hl := wt_list2_le (.list [.nat (t / q), .nat (t % q), .nat w₀, .nat w₁,
      .nat (rcRCondN wl rl (t / q) (t % q))]) (natList (List.range q))
  have hX := rcR_W_le (W := W) (d := 3) (by norm_num)
  have b1 := rcR_wt_bit (rcR_eval_eq_le (t / q) (t % q))
  have b2 := rcR_wt_bit (rcR_eval_eq_le (BinOp.eval .eq (t / q) (t % q)) 0)
  have b3 := rcR_wt_bit (rcR_eval_eq_le (wl.getD (t / q) 0) (wl.getD (t % q) 0))
  have b4 := rcR_wt_bit (rcR_eval_eq_le (rl.getD (t / q) 0) (rl.getD (t % q) 0))
  have b5 := rcR_wt_bit (rcR_eval_mul_le (rcR_eval_eq_le (wl.getD (t / q) 0) (wl.getD (t % q) 0))
    (rcR_eval_eq_le (rl.getD (t / q) 0) (rl.getD (t % q) 0)))
  have l1 := wt_list3_le (natList wl) (.nat (t / q)) (.nat 0)
  have l2 := wt_list3_le (natList wl) (.nat (t % q)) (.nat 0)
  have l3 := wt_list3_le (natList rl) (.nat (t / q)) (.nat 0)
  have l4 := wt_list3_le (natList rl) (.nat (t % q)) (.nat 0)
  have l0 := wt_nat_le 0
  have b6 := rcR_wt_bit hc1
  have r1 : (Val.list [.nat (t / q), .nat (t % q), .nat w₀, .nat w₁,
      .nat (rcRCondN wl rl (t / q) (t % q))]).wt < (Val.list [.list [.nat (t / q), .nat (t % q),
      .nat w₀, .nat w₁, .nat (rcRCondN wl rl (t / q) (t % q))], natList (List.range q)]).wt :=
    wt_le_wt_list (by simp)
  omega

end Gen

end GI.Impl
