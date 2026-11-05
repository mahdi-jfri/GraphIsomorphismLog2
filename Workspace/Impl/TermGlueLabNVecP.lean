module

public import Workspace.Impl.TermGlueLabNProg
public import Workspace.Impl.TermGlueLabSVPt
public import Workspace.Impl.LinIntTrim

@[expose] public section

/-!
# The vector wrapper of the label driver: the program

Proof of Theorem A.23, step 6: the affine transporter gets the two vectors
`E(p_{y'})` and `E(p_x)`. The vector programs (`tmGLSVecFuns`, `tmGLSPtFuns`)
read the plain context `[t, U, V, d]` and make one vector per call. Step 5 returns the plain
context when some type repeats, and the context `[t, U, V, 2 :: d]` (orientation coordinate in
front) when all types are distinct.

The wrapper `tmGLNVecF` on `[o5, gens N, xl, yl]` reads the context `ctx = o5[0]` and tells
the two cases apart by `length d - t` (`0` in the plain case, `1` in the orientation case):
* plain case (`tmGLNVPlF`): the label vector program on `[[gens N, ctx], yl]` and on
  `[[gens N, ctx], xl]`;
* orientation case (`tmGLNVOrF`): rebuild `[t, U, V, d]` with the list tail (`linTailFuns`),
  then the label point program on both lists.

The result is `[v_{y'}, v_x]`. This file has the programs and their evaluation lemmas with
abstract callee contracts; `TermGlueLabNVec.lean` plugs in the vector programs.
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Cited (Val encPerm encGroup encIntMatrix gens encInt)

/-! ### The program -/

/-- The context `o5[0]` of the input `[o5, gens N, xl, yl]`. -/
def tmGLNCtxE : Expr := .get (arg 0) (.nat 0)

/-- The two calls of `f`: on `[[gens N, X], yl]` and on `[[gens N, X], xl]`, then the pair of
results. `k` is the length of the environment. -/
def tmGLNPairE (f : ℕ) (X : Expr) (k : ℕ) : Expr :=
  .letE (.call f (mk2 (mk2 (arg 1) X) (arg 3)))
    (.letE (.call f (mk2 (mk2 (arg 1) X) (arg 2))) (mk2 (.var k) (.var (k + 1))))

/-- The plain case: the label vector program at `vf` on the context itself. -/
def tmGLNVPlF (vf : ℕ) : Expr := tmGLNPairE vf tmGLNCtxE 1

/-- The orientation case: the context `[t, U, V, tail d]`, then the label point program at
`pf`. -/
def tmGLNVOrF (pf tl : ℕ) : Expr :=
  .letE (mk4 (.get tmGLNCtxE (.nat 0)) (.get tmGLNCtxE (.nat 1)) (.get tmGLNCtxE (.nat 2))
      (.call tl (.get tmGLNCtxE (.nat 3))))
    (tmGLNPairE pf (.var 1) 2)

/-- **The vector wrapper**: the test `length d - t` picks the case. -/
def tmGLNVecF (pl orf : ℕ) : Expr :=
  .letE tmGLNCtxE (.ite (.arith .sub (.length (.get (.var 1) (.nat 3))) (.get (.var 1) (.nat 0)))
    (.call orf (.var 0)) (.call pl (.var 0)))

/-- **The vector module** (37 functions): the wrapper, the two cases, the label point program
(which holds the label vector program at its offset `1`), and the list tail. -/
def tmGLNVecFuns (b cs vec : ℕ) : List Expr :=
  [tmGLNVecF (b + 1) (b + 2), tmGLNVPlF (b + 4), tmGLNVOrF (b + 3) (b + 34)] ++
    tmGLSPtFuns (b + 3) cs vec ++ linTailFuns (b + 34)

theorem length_tmGLNVecFuns (b cs vec : ℕ) : (tmGLNVecFuns b cs vec).length = 37 := rfl

/-! ### The two calls -/

private theorem tmGLN_mem_of {vs : List Val} {j : ℕ} {v : Val} (h : vs[j]? = some v) :
    v ∈ vs := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.getElem_mem hj

private theorem tmGLN_in_ar {c1 c2 g wi W Wc CX j : ℕ} (hj : j ≤ 3)
    (h1 : c1 ≤ 2 * W + 1 + 5 + CX + 2 * g + 7) (hg : g ≤ 2 * (W + Wc) + 6)
    (h2 : c2 ≤ 2 * W + j + 5) (hwi : wi ≤ 2 * (2 * (W + Wc) + 6 + W) + 6) :
    c1 + c2 + 2 * wi + 7 ≤ 20 * (W + Wc + CX) + 100 := by
  omega

/-- The argument `[[gens N, X], z]` of one call. -/
theorem tmGLN_in_det {P : Program} {vs rest : List Val} {gN ctx z : Val} {X : Expr}
    {CX Wc j : ℕ} (hj : j ≤ 3) (h1 : vs[1]? = some gN) (hz : vs[j]? = some z)
    (hX : Det P (.list vs :: rest) X ctx CX) (hc : ctx.wt ≤ Wc) :
    Det P (.list vs :: rest) (mk2 (mk2 (arg 1) X) (arg j)) (.list [.list [gN, ctx], z])
        (20 * ((Val.list vs).wt + Wc + CX) + 100) ∧
      (Val.list [.list [gN, ctx], z]).wt ≤ 6 * (Val.list vs).wt + 4 * Wc + 18 := by
  have wg : gN.wt < (Val.list vs).wt := wt_le_wt_list (tmGLN_mem_of h1)
  have wz : z.wt < (Val.list vs).wt := wt_le_wt_list (tmGLN_mem_of hz)
  have g1 : Det P (.list vs :: rest) (arg 1) gN (2 * (Val.list vs).wt + 1 + 5) :=
    Det.arg' (P := P) (vs := vs) (rest := rest) (j := 1) h1
  have gj : Det P (.list vs :: rest) (arg j) z (2 * (Val.list vs).wt + j + 5) :=
    Det.arg' (P := P) (vs := vs) (rest := rest) (j := j) hz
  have m1 := Det.mk2 g1 hX
  have m2 := Det.mk2 m1 gj
  have hg := wt_list2_le gN ctx
  have hi := wt_list2_le (.list [gN, ctx]) z
  have hg' : (Val.list [gN, ctx]).wt ≤ 2 * ((Val.list vs).wt + Wc) + 6 := by omega
  have hi' : (Val.list [.list [gN, ctx], z]).wt ≤
      2 * (2 * ((Val.list vs).wt + Wc) + 6 + (Val.list vs).wt) + 6 := by omega
  exact ⟨m2.mono (tmGLN_in_ar hj le_rfl hg' le_rfl hi'), by omega⟩

private theorem tmGLN_pair_ar {c1 c2 c' l v1 v2 A C W Wc CX : ℕ} (h1 : c1 ≤ A + 2 * C + 1)
    (h2 : c2 ≤ A + 2 * C + 1) (hv1 : v1 < C) (hv2 : v2 < C)
    (hc' : c' ≤ v1 + 1 + (v2 + 1) + 2 * l + 7) (hl : l ≤ 2 * (v1 + v2) + 6)
    (hA : A = 20 * (W + Wc + CX) + 100) :
    c1 + (c2 + c' + l + 1) + l + 1 ≤ 300 * (W + Wc + CX + C + 1) := by
  subst hA; omega

/-- **The two calls**: with contracts `Ry`, `Rx` (cost `≤ C`) for the two arguments, the
result is a pair `[vv, ww]` with `Ry vv`, `Rx ww`. -/
theorem tmGLN_pair_spec {P : Program} {f : ℕ} {vs rest : List Val} {gN xl yl ctx : Val}
    {X : Expr} {CX Wc C : ℕ} {Ry Rx : Val → Prop}
    (h1 : vs[1]? = some gN) (h2 : vs[2]? = some xl) (h3 : vs[3]? = some yl)
    (hX : ∀ r' : List Val, Det P (.list vs :: (rest ++ r')) X ctx CX) (hc : ctx.wt ≤ Wc)
    (hy : FunAll P f (.list [.list [gN, ctx], yl]) (fun w c => Ry w ∧ c ≤ C))
    (hx : FunAll P f (.list [.list [gN, ctx], xl]) (fun w c => Rx w ∧ c ≤ C)) :
    EvalAll P (.list vs :: rest) (tmGLNPairE f X (rest.length + 1)) (fun u c => ∃ vv ww,
      u = .list [vv, ww] ∧ Ry vv ∧ Rx ww ∧ vv.wt < C ∧ ww.wt < C ∧
        c ≤ 300 * ((Val.list vs).wt + Wc + CX + C + 1)) := by
  have dy := (tmGLN_in_det (rest := rest ++ []) (by norm_num) h1 h3 (hX []) hc).1
  simp only [List.append_nil] at dy
  refine EvalAll.letE (tmGLP_callAll_le dy le_rfl hy) fun v1 c1 hv1 => ?_
  obtain ⟨hR1, hc1, hw1⟩ := hv1
  have dx := (tmGLN_in_det (rest := rest ++ [v1]) (by norm_num) h1 h2 (hX [v1]) hc).1
  refine EvalAll.letE (tmGLP_callAll_le dx le_rfl hx) fun v2 c2 hv2 => ?_
  obtain ⟨hR2, hc2, hw2⟩ := hv2
  have e1 : ((Val.list vs :: rest) ++ [v1] ++ [v2])[rest.length + 1]? = some v1 := by
    simp
  have e2 : ((Val.list vs :: rest) ++ [v1] ++ [v2])[rest.length + 1 + 1]? = some v2 := by
    simp
  have d1 := Det.var' (P := P) e1
  have d2 := Det.var' (P := P) e2
  refine (Det.mk2 d1 d2).post fun c' hc' => ⟨v1, v2, rfl, hR1, hR2, hw1, hw2, ?_⟩
  exact tmGLN_pair_ar hc1 hc2 hw1 hw2 hc' (wt_list2_le v1 v2) rfl

/-! ### The context and the two cases -/

/-- Reading the context `o5[0]`. -/
theorem tmGLN_ctx_det {P : Program} {ctx w5 gN xl yl : Val} {rest : List Val} :
    Det P (.list [.list [ctx, w5], gN, xl, yl] :: rest) tmGLNCtxE ctx
      (3 * (Val.list [.list [ctx, w5], gN, xl, yl]).wt + 9) := by
  have w1 : ctx.wt < (Val.list [ctx, w5]).wt := wt_le_wt_list (by simp)
  have w2 : (Val.list [ctx, w5]).wt < (Val.list [.list [ctx, w5], gN, xl, yl]).wt :=
    wt_le_wt_list (by simp)
  have g0 : Det P (.list [.list [ctx, w5], gN, xl, yl] :: rest) (arg 0) (.list [ctx, w5])
      (2 * (Val.list [.list [ctx, w5], gN, xl, yl]).wt + 0 + 5) := Det.arg' rfl
  exact (Det.get' g0 (Det.nat 0) (rfl : [ctx, w5][0]? = some ctx)).mono (by omega)

/-- **The plain case**: two calls of the label vector program at `vf`. -/
theorem tmGLN_vpl_spec {P : Program} {pl vf : ℕ} (hf : P.funs[pl]? = some (tmGLNVPlF vf))
    {ctx w5 gN xl yl : Val} {Ry Rx : Val → Prop} {C : ℕ}
    (hy : FunAll P vf (.list [.list [gN, ctx], yl]) (fun w c => Ry w ∧ c ≤ C))
    (hx : FunAll P vf (.list [.list [gN, ctx], xl]) (fun w c => Rx w ∧ c ≤ C)) :
    FunAll P pl (.list [.list [ctx, w5], gN, xl, yl]) (fun u c => (∃ vv ww,
      u = .list [vv, ww] ∧ Ry vv ∧ Rx ww) ∧
        c ≤ 300 * (5 * (Val.list [.list [ctx, w5], gN, xl, yl]).wt + C + 10)) := by
  have w1 : ctx.wt < (Val.list [ctx, w5]).wt := wt_le_wt_list (by simp)
  have w2 : (Val.list [ctx, w5]).wt < (Val.list [.list [ctx, w5], gN, xl, yl]).wt :=
    wt_le_wt_list (by simp)
  have h := tmGLN_pair_spec (P := P) (f := vf) (rest := [])
    (vs := [.list [ctx, w5], gN, xl, yl]) rfl rfl rfl (fun _ => tmGLN_ctx_det)
    (Wc := (Val.list [.list [ctx, w5], gN, xl, yl]).wt) (by omega) hy hx
  refine FunAll.intro hf (h.mono fun u c ⟨vv, ww, hu, h1, h2, _, _, hc⟩ =>
    ⟨⟨vv, ww, hu, h1, h2⟩, hc.trans (by omega)⟩)

private theorem tmGLN_vor_ar {cv cp u W LT Wc C a0 a1 a2 t0 t1 t2 : ℕ}
    (hcv : cv ≤ a0 + a1 + a2 + t2 + 4 * Wc + 9) (ha0 : a0 ≤ 4 * W + 16) (ha1 : a1 ≤ 4 * W + 16)
    (ha2 : a2 ≤ 4 * W + 16) (ht2 : t2 ≤ 4 * W + 16 + LT + t1 + 1) (ht1 : t1 < LT)
    (hWc : Wc ≤ 2 * (t0 + t1) + 8) (ht0 : t0 ≤ 3 * W)
    (hcp : cp ≤ 300 * (W + Wc + (Wc + 1) + C + 1)) (hu : u ≤ 4 * C + 6) :
    cv + cp + u + 1 ≤ 10 ^ 4 * (W + LT + C + 2) := by
  omega

/-- **The orientation case**: the context `[t, U, V, d]` from `[t, U, V, 2 :: d]` (list
tail), then two calls of the label point program at `pf`. -/
theorem tmGLN_vor_spec {P : Program} {orf pf tl : ℕ} (hf : P.funs[orf]? = some (tmGLNVOrF pf tl))
    (htl : P.HasAt tl (linTailFuns tl)) {t : ℕ} {U V : Matrix (Fin t) (Fin t) ℤ}
    {d : Fin t → ℤ} {w5 gN xl yl : Val} {Ry Rx : Val → Prop} {C : ℕ}
    (hy : FunAll P pf (.list [.list [gN, tmGLPMCtx U V d], yl]) (fun w c => Ry w ∧ c ≤ C))
    (hx : FunAll P pf (.list [.list [gN, tmGLPMCtx U V d], xl]) (fun w c => Rx w ∧ c ≤ C)) :
    FunAll P orf (.list [.list [tmGLNOCtx U V d, w5], gN, xl, yl]) (fun u c => (∃ vv ww,
      u = .list [vv, ww] ∧ Ry vv ∧ Rx ww) ∧
        c ≤ 10 ^ 4 * ((Val.list [.list [tmGLNOCtx U V d, w5], gN, xl, yl]).wt +
          linTailCost (Val.list [.list [tmGLNOCtx U V d, w5], gN, xl, yl]).wt + C + 2)) := by
  set a : Val := .list [.list [tmGLNOCtx U V d, w5], gN, xl, yl] with ha
  set W := a.wt with hW
  have hctx : Det P [a] tmGLNCtxE (tmGLNOCtx U V d) (3 * W + 9) := tmGLN_ctx_det
  have w1 : (tmGLNOCtx U V d).wt < (Val.list [tmGLNOCtx U V d, w5]).wt := wt_le_wt_list (by simp)
  have w2 : (Val.list [tmGLNOCtx U V d, w5]).wt < W := wt_le_wt_list (by simp)
  have e0 : (Val.nat t).wt < (tmGLNOCtx U V d).wt := wt_le_wt_list (by simp)
  have e1 : (encIntMatrix U).wt < (tmGLNOCtx U V d).wt := wt_le_wt_list (by simp)
  have e2 : (encIntMatrix V).wt < (tmGLNOCtx U V d).wt := wt_le_wt_list (by simp)
  have e3 : (linVecVal (Fin.cons 2 d : Fin (t + 1) → ℤ)).wt < (tmGLNOCtx U V d).wt :=
    wt_le_wt_list (by simp)
  have g0 := Det.get' hctx (Det.nat 0) (rfl : [Val.nat t, encIntMatrix U, encIntMatrix V,
    linVecVal (Fin.cons 2 d : Fin (t + 1) → ℤ)][0]? = some (.nat t))
  have g1 := Det.get' hctx (Det.nat 1) (rfl : [Val.nat t, encIntMatrix U, encIntMatrix V,
    linVecVal (Fin.cons 2 d : Fin (t + 1) → ℤ)][1]? = some (encIntMatrix U))
  have g2 := Det.get' hctx (Det.nat 2) (rfl : [Val.nat t, encIntMatrix U, encIntMatrix V,
    linVecVal (Fin.cons 2 d : Fin (t + 1) → ℤ)][2]? = some (encIntMatrix V))
  have g3 := Det.get' hctx (Det.nat 3) (rfl : [Val.nat t, encIntMatrix U, encIntMatrix V,
    linVecVal (Fin.cons 2 d : Fin (t + 1) → ℤ)][3]? = some
      (linVecVal (Fin.cons 2 d : Fin (t + 1) → ℤ)))
  have htail := linTail_vec_spec htl (Fin.cons 2 d : Fin (t + 1) → ℤ)
  have htw := tmGLP_fundet_wt htail
  have e : (fun i : Fin t => (Fin.cons 2 d : Fin (t + 1) → ℤ) i.succ) = d :=
    funext fun i => Fin.cons_succ _ _ _
  rw [e] at htail htw
  have hLT : linTailCost (linVecVal (Fin.cons 2 d : Fin (t + 1) → ℤ)).wt ≤ linTailCost W :=
    linTailCost_mono (by omega)
  have g3' := Det.call g3 htail
  have m4 : Det P [a] (mk4 (.get tmGLNCtxE (.nat 0)) (.get tmGLNCtxE (.nat 1))
      (.get tmGLNCtxE (.nat 2)) (.call tl (.get tmGLNCtxE (.nat 3)))) (tmGLPMCtx U V d) _ :=
    Det.mk4 g0 g1 g2 g3'
  have hc4 : (tmGLPMCtx U V d).wt ≤ 2 * ((Val.nat t).wt + (encIntMatrix U).wt +
      (encIntMatrix V).wt + (linVecVal d).wt) + 8 := wt_list4_le _ _ _ _
  refine FunAll.intro hf (EvalAll.letE m4 fun v cv hv => ?_)
  obtain ⟨rfl, hcv⟩ := hv
  have hp := tmGLN_pair_spec (P := P) (f := pf) (rest := [tmGLPMCtx U V d])
    (vs := [.list [tmGLNOCtx U V d, w5], gN, xl, yl]) (X := .var 1) rfl rfl rfl
    (fun _ => Det.var' rfl) le_rfl hy hx
  refine hp.mono fun u cp ⟨vv, ww, hu, h1, h2, hv1, hv2, hcp⟩ => ⟨⟨vv, ww, hu, h1, h2⟩, ?_⟩
  have hu' : u.wt ≤ 4 * C + 6 := by rw [hu]; have := wt_list2_le vv ww; omega
  have ht0 : (Val.nat t).wt + (encIntMatrix U).wt + (encIntMatrix V).wt ≤ 3 * W := by omega
  have r1 : (Val.list [Val.nat t, encIntMatrix U, encIntMatrix V, linVecVal d]).wt =
    (tmGLPMCtx U V d).wt := rfl
  have r2 : (Val.list [Val.list [tmGLNOCtx U V d, w5], gN, xl, yl]).wt = W := rfl
  exact tmGLN_vor_ar (W := W) (LT := linTailCost W) hcv (by omega) (by omega) (by omega)
    (by omega) (htw.trans_le hLT) (by omega) ht0 hcp hu'

/-! ### The test -/

/-- **The dispatch**: the test `length d - t` is `0` in the plain case, nonzero in the
orientation case, and the wrapper calls the function of that case. -/
theorem tmGLN_vec_disp {P : Program} {b pl orf : ℕ} (hf : P.funs[b]? = some (tmGLNVecF pl orf))
    {t : ℕ} {mU mV : Val} {ds : List Val} {w5 gN xl yl : Val} {R : Val → Prop} {G : ℕ}
    (g : ℕ) (hg : g = if ds.length - t = 0 then pl else orf)
    (h : FunAll P g (.list [.list [.list [.nat t, mU, mV, .list ds], w5], gN, xl, yl])
      (fun u c => R u ∧ c ≤ G)) :
    FunAll P b (.list [.list [.list [.nat t, mU, mV, .list ds], w5], gN, xl, yl])
      (fun u c => R u ∧ c ≤ 10 * (Val.list [.list [.list [.nat t, mU, mV, .list ds], w5],
        gN, xl, yl]).wt + 4 * G + 50) := by
  set ctx : Val := .list [.nat t, mU, mV, .list ds] with hctx
  set a : Val := .list [.list [ctx, w5], gN, xl, yl] with ha
  set W := a.wt with hW
  have w1 : ctx.wt < (Val.list [ctx, w5]).wt := wt_le_wt_list (by simp)
  have w2 : (Val.list [ctx, w5]).wt < W := wt_le_wt_list (by simp)
  have wd : (Val.list ds).wt < ctx.wt := wt_le_wt_list (by simp)
  have wt0 : (Val.nat t).wt < ctx.wt := wt_le_wt_list (by simp)
  have hl := length_lt_wt_list ds
  refine FunAll.intro hf (EvalAll.letE (tmGLN_ctx_det (rest := [])) fun v cv hv => ?_)
  obtain ⟨rfl, hcv⟩ := hv
  have dv : Det P [a, ctx] (.var 1) ctx (ctx.wt + 1) := Det.var' rfl
  have d3 := Det.length (Det.get' dv (Det.nat 3)
    (rfl : [Val.nat t, mU, mV, .list ds][3]? = some (.list ds)))
  have d0 := Det.get' dv (Det.nat 0) (rfl : [Val.nat t, mU, mV, .list ds][0]? = some (.nat t))
  have dt := Det.arith' (op := .sub) d3 d0 rfl
  have hz := wt_nat_le (GI.Machine.BinOp.eval .sub ds.length t)
  refine EvalAll.ite dt (fun _ _ h => ⟨_, h.1⟩) fun x cc hx => ?_
  obtain ⟨hx, hcc⟩ := hx
  cases hx
  have he : (if GI.Machine.BinOp.eval .sub ds.length t = 0 then Expr.call pl (.var 0)
      else .call orf (.var 0)) = .call g (.var 0) := by
    rw [hg]; by_cases h0 : ds.length - t = 0 <;> simp [GI.Machine.BinOp.eval_sub, h0]
  rw [he]
  refine EvalAll.call_funAll (Det.var' (P := P) (env := [a, ctx]) (i := 0) rfl)
    fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine (FunAll.wt_lt h).mono fun u c ⟨⟨hR, hc⟩, hu⟩ => ⟨hR, ?_⟩
  simp only [GI.Machine.BinOp.eval_sub] at hcc hz
  have hl' : (Val.list [Val.list [ctx, w5], gN, xl, yl]).wt = W := rfl
  omega

end GI.Impl
