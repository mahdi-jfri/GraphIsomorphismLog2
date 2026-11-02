import Workspace.Impl.TermJProgYg

/-!
# The generators of `Aut_{N ≀ Sym(q)}(X)` (program, part 2)

The small pieces: the entries of a lifted transposition (`tmJSwDEF`, `tmJSwPEF`) and one local
generator at a row `a` (`tmJLocAF`).
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)

/-- The weight of a list of five values. -/
theorem tmJYg_wt_list5_le (a b c d e : Val) :
    (Val.list [a, b, c, d, e]).wt ≤ 2 * (a.wt + b.wt + c.wt + d.wt + e.wt) + 9 := by
  have := wt_list_le [a, b, c, d, e]; simp at this; omega

/-! ### The top permutation of a lifted transposition -/

/-- On `[[a, a'], i]`: `swap a a' i`. -/
def tmJSwPEF : Expr :=
  .ite (.arith .eq (arg 1) (.get (arg 0) (.nat 0))) (.get (arg 0) (.nat 1))
    (.ite (.arith .eq (arg 1) (.get (arg 0) (.nat 1))) (.get (arg 0) (.nat 0)) (arg 1))

theorem tmJ_swPE_val {q : ℕ} (a a' i : Fin q) :
    (if (if (i : ℕ) = a then 1 else 0) = 0 then
      (if (if (i : ℕ) = a' then 1 else 0) = 0 then Val.nat i else Val.nat a) else Val.nat a') =
      Val.nat (swap a a' i) := by
  rw [swap_apply_def]
  by_cases h1 : i = a
  · subst h1; simp
  · have h1' : (i : ℕ) ≠ a := fun h => h1 (Fin.ext h)
    by_cases h2 : i = a'
    · subst h2; simp [h1, h1']
    · have h2' : (i : ℕ) ≠ a' := fun h => h2 (Fin.ext h)
      simp [h1, h1', h2, h2']

theorem tmJ_swPE_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some tmJSwPEF) {q : ℕ}
    (a a' i : Fin q) :
    FunDet P f (.list [.list [.nat a, .nat a'], .nat i]) (.nat (swap a a' i))
      (1000 * (q + 1)) := by
  refine FunDet.intro hf ?_
  have d0 := Det.arg' (P := P) (vs := [.list [.nat a, .nat a'], .nat i]) (rest := []) (j := 0)
    (v := .list [.nat a, .nat a']) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [.nat a, .nat a'], .nat i]) (rest := []) (j := 1)
    (v := .nat i) rfl
  have ga := Det.get' d0 (Det.nat 0) (vs := [.nat a, .nat a']) (v := .nat a) rfl
  have ga' := Det.get' d0 (Det.nat 1) (vs := [.nat a, .nat a']) (v := .nat a') rfl
  have e1 := Det.arith (op := .eq) d1 ga
  have e2 := Det.arith (op := .eq) d1 ga'
  have i2 := tmJ_det_ite e2 ga d1
  have i1 := tmJ_det_ite e1 ga' i2
  rw [show Machine.BinOp.eval .eq (i : ℕ) a = if (i : ℕ) = a then 1 else 0 from rfl,
    show Machine.BinOp.eval .eq (i : ℕ) a' = if (i : ℕ) = a' then 1 else 0 from rfl,
    tmJ_swPE_val] at i1
  refine i1.mono ?_
  have wa := wt_list2_le (Val.nat a) (Val.nat a')
  have wb := wt_list2_le (Val.list [.nat a, .nat a']) (Val.nat i)
  have := wt_nat_le a
  have := wt_nat_le a'
  have := wt_nat_le i
  have := a.2
  have := a'.2
  have := i.2
  have w1 : (Val.nat (if (i : ℕ) = a then 1 else 0)).wt ≤ 3 := by split_ifs <;> decide
  have w2 : (Val.nat (if (i : ℕ) = a' then 1 else 0)).wt ≤ 3 := by split_ifs <;> decide
  have w3 : (if (if (i : ℕ) = a' then 1 else 0) = 0 then Val.nat i else Val.nat a).wt ≤ q + 2 := by
    have := wt_nat_le i; have := wt_nat_le a; have := i.2; have := a.2
    split_ifs <;> omega
  have := wt_nat_le (swap a a' i)
  have := (swap a a' i).2
  omega

/-! ### The coordinates of a lifted transposition -/

/-- On `[[b, b⁻¹, one, a, a'], i]`: `b` if `i = a'`, else `b⁻¹` if `i = a`, else `one`. -/
def tmJSwDEF : Expr :=
  .ite (.arith .eq (arg 1) (.get (arg 0) (.nat 4))) (.get (arg 0) (.nat 0))
    (.ite (.arith .eq (arg 1) (.get (arg 0) (.nat 3))) (.get (arg 0) (.nat 1))
      (.get (arg 0) (.nat 2)))

theorem tmJ_swDE_val {m q : ℕ} (a a' : Fin q) (b : Perm (Fin m)) (i : Fin q) :
    (if (if (i : ℕ) = a' then 1 else 0) = 0 then
      (if (if (i : ℕ) = a then 1 else 0) = 0 then encPerm (1 : Perm (Fin m)) else encPerm b⁻¹)
      else encPerm b) = encPerm ((tmJSwD a a' b) i)⁻¹ := by
  unfold tmJSwD
  by_cases h2 : i = a'
  · subst h2; simp
  · have h2' : (i : ℕ) ≠ a' := fun h => h2 (Fin.ext h)
    rw [Function.update_of_ne h2]
    by_cases h1 : i = a
    · subst h1; simp [h2']
    · have h1' : (i : ℕ) ≠ a := fun h => h1 (Fin.ext h)
      simp [h1', h2', Pi.mulSingle_eq_of_ne h1]

/-- The context of the coordinates of a lifted transposition. -/
def tmJSwDCtx {m q : ℕ} (a a' : Fin q) (b : Perm (Fin m)) : Val :=
  .list [encPerm b, encPerm b⁻¹, encPerm (1 : Perm (Fin m)), .nat a, .nat a']

theorem wt_tmJSwDCtx_le {m q : ℕ} (a a' : Fin q) (b : Perm (Fin m)) :
    (tmJSwDCtx a a' b).wt ≤ 24 * (m + 1) ^ 2 + 2 * (2 * q + 4) + 9 := by
  have := tmJYg_wt_list5_le (encPerm b) (encPerm b⁻¹) (encPerm (1 : Perm (Fin m))) (.nat a)
    (.nat a')
  have := wt_encPerm_le b
  have := wt_encPerm_le b⁻¹
  have := wt_encPerm_le (1 : Perm (Fin m))
  have := wt_nat_le a
  have := wt_nat_le a'
  have := a.2
  have := a'.2
  unfold tmJSwDCtx
  omega

theorem tmJ_swDE_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some tmJSwDEF) {m q : ℕ}
    (a a' : Fin q) (b : Perm (Fin m)) (i : Fin q) :
    FunDet P f (.list [tmJSwDCtx a a' b, .nat i]) (encPerm ((tmJSwD a a' b) i)⁻¹)
      (1000 * ((m + 1) ^ 2 + q + 1)) := by
  refine FunDet.intro hf ?_
  have d0 := Det.arg' (P := P) (vs := [tmJSwDCtx a a' b, .nat i]) (rest := []) (j := 0)
    (v := tmJSwDCtx a a' b) rfl
  have d1 := Det.arg' (P := P) (vs := [tmJSwDCtx a a' b, .nat i]) (rest := []) (j := 1)
    (v := .nat i) rfl
  have g0 := Det.get' d0 (Det.nat 0) (vs := [encPerm b, encPerm b⁻¹, encPerm (1 : Perm (Fin m)),
    .nat a, .nat a']) (v := encPerm b) rfl
  have g1 := Det.get' d0 (Det.nat 1) (vs := [encPerm b, encPerm b⁻¹, encPerm (1 : Perm (Fin m)),
    .nat a, .nat a']) (v := encPerm b⁻¹) rfl
  have g2 := Det.get' d0 (Det.nat 2) (vs := [encPerm b, encPerm b⁻¹, encPerm (1 : Perm (Fin m)),
    .nat a, .nat a']) (v := encPerm (1 : Perm (Fin m))) rfl
  have g3 := Det.get' d0 (Det.nat 3) (vs := [encPerm b, encPerm b⁻¹, encPerm (1 : Perm (Fin m)),
    .nat a, .nat a']) (v := .nat a) rfl
  have g4 := Det.get' d0 (Det.nat 4) (vs := [encPerm b, encPerm b⁻¹, encPerm (1 : Perm (Fin m)),
    .nat a, .nat a']) (v := .nat a') rfl
  have e1 := Det.arith (op := .eq) d1 g4
  have e2 := Det.arith (op := .eq) d1 g3
  have i2 := tmJ_det_ite e2 g1 g2
  have i1 := tmJ_det_ite e1 g0 i2
  rw [show Machine.BinOp.eval .eq (i : ℕ) a = if (i : ℕ) = a then 1 else 0 from rfl,
    show Machine.BinOp.eval .eq (i : ℕ) a' = if (i : ℕ) = a' then 1 else 0 from rfl,
    tmJ_swDE_val] at i1
  refine i1.mono ?_
  have wc := wt_tmJSwDCtx_le a a' b
  have wb := wt_list2_le (tmJSwDCtx a a' b) (Val.nat i)
  have := wt_encPerm_le b
  have := wt_encPerm_le b⁻¹
  have := wt_encPerm_le (1 : Perm (Fin m))
  have := wt_nat_le a
  have := wt_nat_le a'
  have := wt_nat_le i
  have := a.2
  have := a'.2
  have := i.2
  have w1 : (Val.nat (if (i : ℕ) = a then 1 else 0)).wt ≤ 3 := by split_ifs <;> decide
  have w2 : (Val.nat (if (i : ℕ) = a' then 1 else 0)).wt ≤ 3 := by split_ifs <;> decide
  have w3 : (if (if (i : ℕ) = a then 1 else 0) = 0 then encPerm (1 : Perm (Fin m))
      else encPerm b⁻¹).wt ≤ 4 * (m + 1) ^ 2 := by split_ifs <;> assumption
  have := wt_encPerm_le ((tmJSwD a a' b) i)⁻¹
  omega

/-! ### One local generator at a row -/

/-- On `[[lc, a], s]`, with `lc = [one_m, one_q, q, m]`: the local generator `(s⁻¹ at a; 1)` on
`Fin (m q)`. -/
def tmJLocAF (dsA pr : ℕ) : Expr :=
  .call pr (mk4 (.call dsA (mk4 (arg 1) (.get (.get (arg 0) (.nat 0)) (.nat 0))
      (.get (.get (arg 0) (.nat 0)) (.nat 2)) (.get (arg 0) (.nat 1))))
    (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.get (.get (arg 0) (.nat 0)) (.nat 2))
    (.get (.get (arg 0) (.nat 0)) (.nat 3)))

theorem tmJ_locA_spec {P : Program} {f dsA rg tbA tbe pr prg prt prte : ℕ}
    (hf : P.funs[f]? = some (tmJLocAF dsA pr))
    (hds : P.funs[dsA]? = some (tmJDsAF rg tbA)) (hrg : P.HasAt rg (rangeFuns rg))
    (htb : P.HasAt tbA (mapFuns tbA tbe)) (htbe : P.funs[tbe]? = some tmJDsAEF)
    (hpr : TmJPairAt P pr prg prt prte) {m q : ℕ} (a : Fin q) (s : Perm (Fin m)) :
    FunDet P f (.list [.list [tmJLocCtx m q, .nat a], encPerm s])
      (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc a s⁻¹)))
      (tmJLocK ((m + 1) * (q + 1))) := by
  refine FunDet.intro hf ?_
  unfold tmJLocAF
  have d0 := Det.arg' (P := P) (vs := [.list [tmJLocCtx m q, .nat a], encPerm s]) (rest := [])
    (j := 0) (v := .list [tmJLocCtx m q, .nat a]) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [tmJLocCtx m q, .nat a], encPerm s]) (rest := [])
    (j := 1) (v := encPerm s) rfl
  have dc := Det.get' d0 (Det.nat 0) (vs := [tmJLocCtx m q, .nat a]) (v := tmJLocCtx m q) rfl
  have da := Det.get' d0 (Det.nat 1) (vs := [tmJLocCtx m q, .nat a]) (v := .nat a) rfl
  have g0 := Det.get' dc (Det.nat 0) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := encPerm (1 : Perm (Fin m))) rfl
  have g1 := Det.get' dc (Det.nat 1) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := encPerm (1 : Perm (Fin q))) rfl
  have g2 := Det.get' dc (Det.nat 2) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat q) rfl
  have g3 := Det.get' dc (Det.nat 3) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat m) rfl
  have cds := Det.call (Det.mk4 d1 g0 g2 da) (tmJ_dsA_spec hds hrg htb htbe a s)
  have cpr := Det.call (Det.mk4 cds g1 g2 g3) (tmJ_pair_spec hpr
    (Pi.mulSingle a s⁻¹ : Fin q → Perm (Fin m)) 1)
  refine cpr.mono ?_
  -- the cost
  have hm1 : m + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hW1 : 1 ≤ (m + 1) * (q + 1) := by omega
  have hW2 : (m + 1) * (q + 1) ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hm2 : (m + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.pow_le_pow_left hm1 2
  have hq2 : (q + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.pow_le_pow_left hq1 2
  have hmq : m * q + 1 ≤ (m + 1) * (q + 1) := by nlinarith
  have wds : (tmJDsVal (Pi.mulSingle a s⁻¹ : Fin q → Perm (Fin m))).wt ≤
      9 * ((m + 1) * (q + 1)) ^ 2 := by
    have h1 := wt_tmJDsVal_le (Pi.mulSingle a s⁻¹ : Fin q → Perm (Fin m))
    have : (q + 1) * (m + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := by
      have e : ((m + 1) * (q + 1)) ^ 2 = (q + 1) ^ 2 * (m + 1) ^ 2 := by ring
      rw [e]
      exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) _)
    have h9 : 9 * (q + 1) * (m + 1) ^ 2 = 9 * ((q + 1) * (m + 1) ^ 2) := by ring
    omega
  have wc := wt_tmJLocCtx_le m q
  have ws := wt_encPerm_le s
  have w1m := wt_encPerm_le (1 : Perm (Fin m))
  have w1q := wt_encPerm_le (1 : Perm (Fin q))
  have wq := wt_nat_le q
  have wm := wt_nat_le m
  have wa := wt_nat_le a
  have ha := a.2
  have wca := wt_list2_le (tmJLocCtx m q) (.nat a)
  have win := wt_list2_le (.list [tmJLocCtx m q, .nat a]) (encPerm s)
  have wa4 := wt_list4_le (encPerm s) (encPerm (1 : Perm (Fin m))) (.nat q) (.nat a)
  have wb4 := wt_list4_le (tmJDsVal (Pi.mulSingle a s⁻¹ : Fin q → Perm (Fin m)))
    (encPerm (1 : Perm (Fin q))) (.nat q) (.nat m)
  have wout := wt_encPerm_le (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    (tmJLoc a s⁻¹))
  have hout : (m * q + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.pow_le_pow_left hmq 2
  have hX : (Val.list [tmJDsVal (Pi.mulSingle a s⁻¹ : Fin q → Perm (Fin m)),
      encPerm (1 : Perm (Fin q)), .nat q, .nat m]).wt + m * q + 1 ≤
      50 * ((m + 1) * (q + 1)) ^ 2 := by omega
  have hP : tmJPairK ((Val.list [tmJDsVal (Pi.mulSingle a s⁻¹ : Fin q → Perm (Fin m)),
      encPerm (1 : Perm (Fin q)), .nat q, .nat m]).wt + m * q) ≤
      10 ^ 6 * (50 * ((m + 1) * (q + 1)) ^ 2) ^ 4 := by
    unfold tmJPairK
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX 4)
  have e1 : 10 ^ 6 * (50 * ((m + 1) * (q + 1)) ^ 2) ^ 4 =
      6250000000000 * ((m + 1) * (q + 1)) ^ 8 := by ring
  have hD : tmJDsK ((m + 1) * (q + 1)) ≤ 10 ^ 7 * ((m + 1) * (q + 1)) ^ 8 := by
    unfold tmJDsK
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW1 (by norm_num))
  have h28 : ((m + 1) * (q + 1)) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 8 :=
    Nat.pow_le_pow_right hW1 (by norm_num)
  have e2 : tmJLoc a s⁻¹ = tmJP ((Pi.mulSingle a s⁻¹ : Fin q → Perm (Fin m)), 1) := rfl
  rw [e2] at wout
  show _ ≤ 10 ^ 14 * ((m + 1) * (q + 1)) ^ 8
  omega

/-! ### One lifted transposition -/

/-- On `[b, lc, a, a']`: the lifted transposition `tmJSw a a' b` on `Fin (m q)`. -/
def tmJSwSF (iv tbD tbP pr : ℕ) : Expr :=
  .letE (.call iv (arg 0))
  (.call pr (mk4
    (.call tbD (mk2 (.snoc (mk4 (arg 0) (.var 1) (.get (arg 1) (.nat 0)) (arg 2)) (arg 3))
      (.get (arg 1) (.nat 1))))
    (.call tbP (mk2 (mk2 (arg 2) (arg 3)) (.get (arg 1) (.nat 1))))
    (.get (arg 1) (.nat 2)) (.get (arg 1) (.nat 3))))

theorem tmJ_swS_spec {P : Program} {f iv tbD swDE tbP swPE pr prg prt prte : ℕ}
    (hf : P.funs[f]? = some (tmJSwSF iv tbD tbP pr)) (hiv : P.HasAt iv (invFuns iv))
    (htbD : P.HasAt tbD (mapFuns tbD swDE)) (hswDE : P.funs[swDE]? = some tmJSwDEF)
    (htbP : P.HasAt tbP (mapFuns tbP swPE)) (hswPE : P.funs[swPE]? = some tmJSwPEF)
    (hpr : TmJPairAt P pr prg prt prte) {m q : ℕ} (a a' : Fin q) (b : Perm (Fin m)) :
    FunDet P f (.list [encPerm b, tmJLocCtx m q, .nat a, .nat a'])
      (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJSw a a' b)))
      (tmJLocK ((m + 1) * (q + 1))) := by
  refine FunDet.intro hf ?_
  unfold tmJSwSF
  have c1 := Det.call (Det.arg' (P := P) (vs := [encPerm b, tmJLocCtx m q, .nat a, .nat a'])
    (rest := []) (j := 0) (v := encPerm b) rfl) (inv_spec hiv b)
  have u0 := Det.arg' (P := P) (vs := [encPerm b, tmJLocCtx m q, .nat a, .nat a'])
    (rest := [encPerm b⁻¹]) (j := 0) (v := encPerm b) rfl
  have u1 := Det.arg' (P := P) (vs := [encPerm b, tmJLocCtx m q, .nat a, .nat a'])
    (rest := [encPerm b⁻¹]) (j := 1) (v := tmJLocCtx m q) rfl
  have u2 := Det.arg' (P := P) (vs := [encPerm b, tmJLocCtx m q, .nat a, .nat a'])
    (rest := [encPerm b⁻¹]) (j := 2) (v := .nat a) rfl
  have u3 := Det.arg' (P := P) (vs := [encPerm b, tmJLocCtx m q, .nat a, .nat a'])
    (rest := [encPerm b⁻¹]) (j := 3) (v := .nat a') rfl
  have v1 := Det.var' (P := P) (env := [Val.list [encPerm b, tmJLocCtx m q, .nat a, .nat a'],
    encPerm b⁻¹]) (i := 1) (v := encPerm b⁻¹) rfl
  have g0 := Det.get' u1 (Det.nat 0) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := encPerm (1 : Perm (Fin m))) rfl
  have g1 := Det.get' u1 (Det.nat 1) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := encFun fun i : Fin q => (i : ℕ)) rfl
  have g2 := Det.get' u1 (Det.nat 2) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat q) rfl
  have g3 := Det.get' u1 (Det.nat 3) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat m) rfl
  have dctx := Det.snoc (Det.mk4 u0 v1 g0 u2) u3
  have hD := tabulate_spec htbD (c := tmJSwDCtx a a' b)
    (F := fun i : Fin q => encPerm ((tmJSwD a a' b) i)⁻¹) (fun i => tmJ_swDE_spec hswDE a a' b i)
  have cD := Det.call (Det.mk2 dctx g1) hD
  have hP := tabulate_spec htbP (c := .list [.nat a, .nat a'])
    (F := fun i : Fin q => .nat (swap a a' i)) (fun i => tmJ_swPE_spec hswPE a a' i)
  have cP := Det.call (Det.mk2 (Det.mk2 u2 u3) g1) hP
  have e1 : Val.list ((List.finRange q).map fun i : Fin q => encPerm ((tmJSwD a a' b) i)⁻¹) =
      tmJDsVal (tmJSwD a a' b) := rfl
  have e2 : Val.list ((List.finRange q).map fun i : Fin q => Val.nat (swap a a' i)) =
      encPerm (swap a a') := rfl
  rw [e1] at cD
  rw [e2] at cP
  have cpr := Det.call (Det.mk4 cD cP g2 g3) (tmJ_pair_spec hpr (tmJSwD a a' b) (swap a a'))
  refine (Det.letE c1 cpr).mono ?_
  -- the cost
  have hm1 : m + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hW1 : 1 ≤ (m + 1) * (q + 1) := by omega
  have hW2 : (m + 1) * (q + 1) ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hW3 : ((m + 1) * (q + 1)) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 3 :=
    Nat.pow_le_pow_right hW1 (by norm_num)
  have hW4 : ((m + 1) * (q + 1)) ^ 3 ≤ ((m + 1) * (q + 1)) ^ 4 :=
    Nat.pow_le_pow_right hW1 (by norm_num)
  have hW8 : ((m + 1) * (q + 1)) ^ 4 ≤ ((m + 1) * (q + 1)) ^ 8 :=
    Nat.pow_le_pow_right hW1 (by norm_num)
  have hm2 : (m + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.pow_le_pow_left hm1 2
  have hq2 : (q + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.pow_le_pow_left hq1 2
  have hm4 : (m + 1) ^ 4 ≤ ((m + 1) * (q + 1)) ^ 4 := Nat.pow_le_pow_left hm1 4
  have hmq : m * q + 1 ≤ (m + 1) * (q + 1) := by nlinarith
  have wds : (tmJDsVal (tmJSwD a a' b)).wt ≤ 9 * ((m + 1) * (q + 1)) ^ 2 := by
    have h1 := wt_tmJDsVal_le (tmJSwD a a' b)
    have : (q + 1) * (m + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := by
      have e : ((m + 1) * (q + 1)) ^ 2 = (q + 1) ^ 2 * (m + 1) ^ 2 := by ring
      rw [e]
      exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) _)
    have h9 : 9 * (q + 1) * (m + 1) ^ 2 = 9 * ((q + 1) * (m + 1) ^ 2) := by ring
    omega
  have wc := wt_tmJLocCtx_le m q
  have wsd := wt_tmJSwDCtx_le a a' b
  have wb := wt_encPerm_le b
  have wbi := wt_encPerm_le b⁻¹
  have w1m := wt_encPerm_le (1 : Perm (Fin m))
  have wid := wt_ids_le q
  have wsw := wt_encPerm_le (swap a a')
  have wq := wt_nat_le q
  have wm := wt_nat_le m
  have wa := wt_nat_le a
  have wa' := wt_nat_le a'
  have ha := a.2
  have ha' := a'.2
  have win := wt_list4_le (encPerm b) (tmJLocCtx m q) (.nat a) (.nat a')
  have wa2 := wt_list2_le (.nat a) (.nat a')
  have wD2 := wt_list2_le (tmJSwDCtx a a' b) (encFun fun i : Fin q => (i : ℕ))
  have wP2 := wt_list2_le (.list [.nat a, .nat a']) (encFun fun i : Fin q => (i : ℕ))
  have wsn := wt_list_snoc_le [encPerm b, encPerm b⁻¹, encPerm (1 : Perm (Fin m)), .nat a]
    (.nat a')
  have w4 := wt_list4_le (encPerm b) (encPerm b⁻¹) (encPerm (1 : Perm (Fin m))) (.nat a)
  have rD : (Val.list ([encPerm b, encPerm b⁻¹, encPerm (1 : Perm (Fin m)), .nat a] ++
      [.nat a'])).wt = (tmJSwDCtx a a' b).wt := rfl
  have rD2 : (Val.list [Val.list ([encPerm b, encPerm b⁻¹, encPerm (1 : Perm (Fin m)), .nat a] ++
      [.nat a']), encFun fun i : Fin q => (i : ℕ)]).wt =
      (Val.list [tmJSwDCtx a a' b, encFun fun i : Fin q => (i : ℕ)]).wt := rfl
  have wb4 := wt_list4_le (tmJDsVal (tmJSwD a a' b)) (encPerm (swap a a')) (.nat q) (.nat m)
  have wout := wt_encPerm_le (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    (tmJSw a a' b))
  have hout : (m * q + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.pow_le_pow_left hmq 2
  have hX : (Val.list [tmJDsVal (tmJSwD a a' b), encPerm (swap a a'), .nat q, .nat m]).wt +
      m * q + 1 ≤ 50 * ((m + 1) * (q + 1)) ^ 2 := by omega
  have hPK : tmJPairK ((Val.list [tmJDsVal (tmJSwD a a' b), encPerm (swap a a'), .nat q,
      .nat m]).wt + m * q) ≤ 10 ^ 6 * (50 * ((m + 1) * (q + 1)) ^ 2) ^ 4 := by
    unfold tmJPairK
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX 4)
  have e3 : 10 ^ 6 * (50 * ((m + 1) * (q + 1)) ^ 2) ^ 4 =
      6250000000000 * ((m + 1) * (q + 1)) ^ 8 := by ring
  have PD1 : q * (1000 * ((m + 1) ^ 2 + q + 1)) ≤ 3000 * ((m + 1) * (q + 1)) ^ 3 := by
    calc q * (1000 * ((m + 1) ^ 2 + q + 1)) ≤
          ((m + 1) * (q + 1)) * (1000 * (3 * ((m + 1) * (q + 1)) ^ 2)) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 3000 * ((m + 1) * (q + 1)) ^ 3 := by ring
  have PD2 : mapK * (q + 1) * ((Val.list [tmJSwDCtx a a' b, encFun fun i : Fin q => (i : ℕ)]).wt +
      (tmJDsVal (tmJSwD a a' b)).wt + 1) ≤
      1000 * ((m + 1) * (q + 1)) * (200 * ((m + 1) * (q + 1)) ^ 2) := by
    unfold mapK
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hq1) (by omega)
  have PP1 : q * (1000 * (q + 1)) ≤ 1000 * ((m + 1) * (q + 1)) ^ 2 := by
    calc q * (1000 * (q + 1)) ≤ ((m + 1) * (q + 1)) * (1000 * ((m + 1) * (q + 1))) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 1000 * ((m + 1) * (q + 1)) ^ 2 := by ring
  have PP2 : mapK * (q + 1) * ((Val.list [.list [.nat a, .nat a'],
      encFun fun i : Fin q => (i : ℕ)]).wt + (encPerm (swap a a')).wt + 1) ≤
      1000 * ((m + 1) * (q + 1)) * (200 * ((m + 1) * (q + 1)) ^ 2) := by
    unfold mapK
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hq1) (by omega)
  have e4 : 1000 * ((m + 1) * (q + 1)) * (200 * ((m + 1) * (q + 1)) ^ 2) =
      200000 * ((m + 1) * (q + 1)) ^ 3 := by ring
  have hI : invK * (m + 1) ^ 4 ≤ 100000 * ((m + 1) * (q + 1)) ^ 4 := by
    unfold invK; omega
  have e5 : tmJSw a a' b = tmJP (tmJSwD a a' b, swap a a') := rfl
  rw [e5] at wout
  show _ ≤ 10 ^ 14 * ((m + 1) * (q + 1)) ^ 8
  omega

end GI.Impl
