import Workspace.Impl.TermGlueLabSLab

/-!
# Step 6 of the label program: one affine call and the answer

Proof of Theorem A.23: "The finite abelian affine transporter procedure in the
proof of Theorem A.20 now imposes both labels in polynomial time within this radical coset."
and "Adjoining `N` lifts the resulting label stabilizer and transporter back to `D`."

`tmGLS6F mg s5 ja out` runs on `[encGroup σN, encPerm τ, u_S, in5, v, w]`:

1. `u_S` is the T4 output (generators of the supplement `S`, `GensOf`); `mkGroup` makes it
   the group value `encGroup gs`;
2. step 5 (at `s5`, on `in5`) returns `[ctx, items]` with `ctx = [t, U, V, d]`;
3. the affine procedure (at `ja`) runs on `[encGroup gs, d, items, v, w]`, which is
   `tmGLAffIn gs m ρ c v w` when `d`, `items`, `v`, `w` are the encodings of the moduli, the
   items `[M(ρ g), c g, M(ρ g⁻¹), c g⁻¹]` and the two vectors (`tmGLS_affIn_eq`);
4. the output program (at `out`, `tmGLSOut_spec`) turns its answer into the label answer.

Step 5 enters as the hypothesis `h5` at `s5`. The affine procedure enters
as the hypothesis `hcall` at `ja`; `tmGLS_call` and `tmGLS_call'` give `hcall` from
`Iface.TmGLAffineSpec` through `tmGLP_aff_call(')`. The result `TmGLSOutRes` is the label answer
by `tmGLS_lab_ans`.
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Cited (Val encPerm encGroup gens PointwiseStab)

variable {n : ℕ}

/-- **Step 6.** `mkGroup` at `mg`, step 5 at `s5`, the affine procedure at `ja`, the output
program at `out`. -/
def tmGLS6F (mg s5 ja out : ℕ) : Expr :=
  .letE (.call mg (mk2 (.get (arg 0) (.nat 0)) (arg 2)))
    (.letE (.call s5 (arg 3))
      (.letE (.call ja (.snoc (mk4 (.var 1) (.get (.get (.var 2) (.nat 0)) (.nat 3))
          (.get (.var 2) (.nat 1)) (arg 4)) (arg 5)))
        (.call out (mk3 (arg 0) (arg 1) (.var 3)))))

/-- The weight bound of the affine input. -/
def tmGLS6A (C5 W : ℕ) : ℕ := 1000 * (W + 1) ^ 6 + 4 * C5

/-- The cost bound of the affine call. -/
def tmGLS6KA (Ka Da C5 W : ℕ) : ℕ := Ka * (tmGLS6A C5 W + 1) ^ Da

/-- **The cost bound of step 6**, for an input of weight `W`: `C5` bounds step 5, `Ka`, `Da` are
the constants of the affine procedure, `c`, `k` those of the PointwiseStab primitive. -/
def tmGLS6C (Ka Da c k C5 W : ℕ) : ℕ :=
  10 ^ 8 * (W + 1) ^ 9 + 3 * C5 + 20 * tmGLS6A C5 W + 10 * tmGLS6KA Ka Da C5 W +
    5 * (3 * tmGLSOutC c k (4 * W + 2 * tmGLS6KA Ka Da C5 W + 10))

theorem tmGLSOutC_mono (c k : ℕ) {W W' : ℕ} (h : W ≤ W') : tmGLSOutC c k W ≤ tmGLSOutC c k W' := by
  unfold tmGLSOutC
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (tmGLSRedC_mono c k (by omega)))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 8))

/-- The step-5 output: `[ctx, items]` with `ctx = [t, U, V, d]`. -/
def TmGLS5Out (modV : Val) (items : List Val) (w : Val) : Prop :=
  ∃ c0 c1 c2 : Val, w = .list [.list [c0, c1, c2, modV], .list items]

/-- **The encoding of the affine input.** With the moduli value `linVecVal (tmGLModZ m)`, the
items of `tmGLAffItem` and the vectors `linVecVal (tmGLVecZ v)`, `linVecVal (tmGLVecZ w)`, the
value the program passes is `tmGLAffIn gs m ρ c v w`. -/
theorem tmGLS_affIn_eq {d : ℕ} (gs : List (Perm (Fin n))) (m : Fin d → ℕ)
    (ρ : gens gs →* (tmGLVec m ≃+ tmGLVec m)) (c : gens gs → tmGLVec m) (v w : tmGLVec m) :
    Val.list [encGroup gs, linVecVal (tmGLModZ m),
      .list (gs.attach.map fun g => tmGLAffItem gs m ρ c ⟨g.1, Subgroup.subset_closure g.2⟩),
      linVecVal (tmGLVecZ v), linVecVal (tmGLVecZ w)] = tmGLAffIn gs m ρ c v w := rfl

/-- The moduli of step 5's context `d i = D i i` are those of the contract, `tmGLQMod D`. -/
theorem tmGLS_mod_val {t : ℕ} {D : Matrix (Fin t) (Fin t) ℤ} (hpos : ∀ i, 0 < D i i) :
    linVecVal (fun i => D i i) = linVecVal (tmGLModZ (tmGLQMod D)) := by
  unfold tmGLModZ tmGLQMod
  congr 1
  funext i
  rw [Int.toNat_of_nonneg (hpos i).le]

private theorem tmGLS6_ar {c1 c2 c3 c4 w Y C5 A KA O : ℕ} (h1 : c1 ≤ 10 ^ 7 * Y)
    (h2 : c2 ≤ 2 * A + 2 * C5) (h3 : c3 ≤ 10 * A + 2 * KA + 1) (h4 : c4 ≤ 2 * A + 8 * KA + 2 * O)
    (hw : w ≤ O) (hY : 1 ≤ Y) :
    c1 + (c2 + (c3 + c4 + w + 1) + w + 1) + w + 1 ≤
      10 ^ 8 * Y + 3 * C5 + 20 * A + 10 * KA + 5 * O := by
  omega

set_option maxHeartbeats 2000000 in
/-- **Step 6 as a program.** Given step 5 at `s5` (`h5`, cost at most `C5`) and the affine call
at `ja` on the value built from step 5's output (`hcall`, with transporter set `T`), the
program returns the output program's answer for the affine answer. -/
theorem tmGLS6_spec (hps : PointwiseStab) {P : Program}
    {f mg s5 ja out red app jp inv cp cj mc Ka Da : ℕ}
    (hf : P.funs[f]? = some (tmGLS6F mg s5 ja out))
    (hmg : P.HasAt mg (mkGroupFuns mg))
    (hout : P.funs[out]? = some (tmGLSOutF red inv cp mc))
    (hred : P.funs[red]? = some (tmGLSRedF app mg jp)) (happ : P.HasAt app (appendFuns app))
    (hj : P.prims[jp]? = some (pointwiseStabPrim hps))
    (hinv : P.HasAt inv (invFuns inv)) (hcp : P.HasAt cp (composeFuns cp))
    (hcj : P.funs[cj]? = some (supConjF cp)) (hmc : P.HasAt mc (mapFuns mc cj))
    (σN gs : List (Perm (Fin n))) (hgl : gs.length ≤ n ^ 2) (τ : Perm (Fin n))
    (in5 vv ww modV : Val) (items : List Val) (C5 : ℕ)
    (h5 : FunAll P s5 in5 (fun w c => TmGLS5Out modV items w ∧ c ≤ C5))
    {T : Set (Perm (Fin n))}
    (hcall : FunAll P ja (.list [encGroup gs, modV, .list items, vv, ww]) (fun u c =>
      TmGLAffOut n u T ∧ c ≤ Ka * ((Val.list [encGroup gs, modV, .list items, vv, ww]).wt + 1) ^ Da)) :
    FunAll P f (.list [encGroup σN, encPerm τ, .list (gs.map encPerm), in5, vv, ww]) (fun w c =>
      ∃ u, TmGLAffOut n u T ∧ TmGLSOutRes σN τ u w ∧
        c ≤ tmGLS6C Ka Da (pointwiseStabPrim hps).c (pointwiseStabPrim hps).k C5
          (Val.list [encGroup σN, encPerm τ, .list (gs.map encPerm), in5, vv, ww]).wt) := by
  set a : Val := .list [encGroup σN, encPerm τ, .list (gs.map encPerm), in5, vv, ww] with ha
  have hwa : (Val.list [encGroup σN, encPerm τ, .list (gs.map encPerm), in5, vv, ww]).wt =
    a.wt := rfl
  -- weights of the input
  have hsum : (encGroup σN).wt + (encPerm τ).wt + (Val.list (gs.map encPerm)).wt + in5.wt +
      vv.wt + ww.wt < a.wt := by
    have := sum_wt_lt_wt_list [encGroup σN, encPerm τ, .list (gs.map encPerm), in5, vv, ww]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
    omega
  have hnW : n < a.wt := by have := tmGLP_n_lt_wt τ; omega
  set Y := (a.wt + 1) ^ 9 with hY
  have hY1 : a.wt + 1 ≤ Y := Nat.le_self_pow (by norm_num) _
  have hYn : ∀ j, j ≤ 9 → (n + 1) ^ j ≤ Y := fun j hj =>
    (Nat.pow_le_pow_left (show n + 1 ≤ a.wt + 1 by omega) j).trans
      (Nat.pow_le_pow_right (by omega) hj)
  have hY6 : (a.wt + 1) ^ 6 ≤ Y := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h16 : a.wt + 1 ≤ (a.wt + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have hn6 : (n + 1) ^ 6 ≤ (a.wt + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  set A := tmGLS6A C5 a.wt with hA
  set KA := tmGLS6KA Ka Da C5 a.wt with hKA
  have hA6 : 1000 * (a.wt + 1) ^ 6 + 4 * C5 ≤ A := by rw [hA]; unfold tmGLS6A; exact le_rfl
  have hAW : 1000 * (a.wt + 1) ≤ A := by omega
  apply FunAll.intro hf
  -- 1. the group value of the supplement
  have e0 := Det.arg' (P := P) (vs := [encGroup σN, encPerm τ, .list (gs.map encPerm), in5, vv, ww])
    (rest := []) (j := 0) rfl
  have e2 := Det.arg' (P := P) (vs := [encGroup σN, encPerm τ, .list (gs.map encPerm), in5, vv, ww])
    (rest := []) (j := 2) rfl
  have en := Det.get' e0 (Det.nat 0) (vs := [.nat n, .list ((1 :: σN).map encPerm)]) rfl
  have wG := wt_encGroup_le_sq hgl
  have d1 := (Det.call (Det.mk2 en e2) (mkGroup_spec hmg gs)).mono (c' := 10 ^ 7 * Y) (by
    have hS3 := measure_le_of_sq hgl
    have hmk : mkGroupK * ((gs.length + 2) * (n + 1)) ^ 3 ≤ mkGroupK * (8 * (n + 1) ^ 9) := by
      refine Nat.mul_le_mul_left _ ?_
      calc ((gs.length + 2) * (n + 1)) ^ 3 ≤ (2 * (n + 1) ^ 3) ^ 3 := Nat.pow_le_pow_left hS3 3
        _ = 8 * (n + 1) ^ 9 := by ring
    have := hYn 9 (by norm_num); have := hYn 6 (by norm_num)
    have wn := wt_nat_le n
    have w2 := wt_list2_le (.nat n) (.list (gs.map encPerm))
    have wgs := wt_gens_le_encGroup gs
    unfold mkGroupK at hmk ⊢
    omega)
  refine EvalAll.letE d1 fun v1 c1 hv1 => ?_
  obtain ⟨rfl, hc1⟩ := hv1
  -- 2. step 5
  have f3 := Det.arg' (P := P) (vs := [encGroup σN, encPerm τ, .list (gs.map encPerm), in5, vv, ww])
    (rest := [encGroup gs]) (j := 3) rfl
  have d2 : EvalAll P [a, encGroup gs] (.call s5 (arg 3)) (fun w c =>
      (TmGLS5Out modV items w ∧ w.wt < C5) ∧ c ≤ 2 * A + 2 * C5) :=
    EvalAll.call_funAll f3 fun v ca hv => by
      obtain ⟨rfl, hca⟩ := hv
      refine (FunAll.wt_lt h5).mono fun w c hw => ⟨⟨hw.1.1, by omega⟩, ?_⟩
      have := hw.1.2; have := hw.2
      omega
  refine EvalAll.letE d2 fun v2 c2 hv2 => ?_
  obtain ⟨⟨⟨x0, x1, x2, rfl⟩, hw5⟩, hc2⟩ := hv2
  -- 3. the affine call
  set w5 : Val := .list [.list [x0, x1, x2, modV], .list items] with hw5d
  have wctx : (Val.list [x0, x1, x2, modV]).wt < w5.wt := wt_le_wt_list (by simp)
  have witems : (Val.list items).wt < w5.wt := wt_le_wt_list (by simp)
  have wmod : modV.wt < (Val.list [x0, x1, x2, modV]).wt := wt_le_wt_list (by simp)
  have hsum5 : (Val.list [x0, x1, x2, modV]).wt + (Val.list items).wt < w5.wt := by
    have := sum_wt_lt_wt_list [.list [x0, x1, x2, modV], .list items]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
    omega
  have g1 := Det.var' (P := P) (env := [a, encGroup gs, w5]) (i := 1) rfl
  have g2 := Det.var' (P := P) (env := [a, encGroup gs, w5]) (i := 2) rfl
  have gctx := Det.get' g2 (Det.nat 0) (vs := [.list [x0, x1, x2, modV], .list items]) rfl
  have gmod := Det.get' gctx (Det.nat 3) (vs := [x0, x1, x2, modV]) rfl
  have git := Det.get' g2 (Det.nat 1) (vs := [.list [x0, x1, x2, modV], .list items]) rfl
  have g4 := Det.arg' (P := P) (vs := [encGroup σN, encPerm τ, .list (gs.map encPerm), in5, vv, ww])
    (rest := [encGroup gs, w5]) (j := 4) rfl
  have g5 := Det.arg' (P := P) (vs := [encGroup σN, encPerm τ, .list (gs.map encPerm), in5, vv, ww])
    (rest := [encGroup gs, w5]) (j := 5) rfl
  have w4l := wt_list_le [encGroup gs, modV, .list items, vv]
  have wVl := wt_list_le [encGroup gs, modV, .list items, vv, ww]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w4l wVl
  have hVA : (Val.list [encGroup gs, modV, .list items, vv, ww]).wt ≤ A := by
    omega
  have dV : Det P [a, encGroup gs, w5] (.snoc (mk4 (.var 1) (.get (.get (.var 2) (.nat 0)) (.nat 3))
      (.get (.var 2) (.nat 1)) (arg 4)) (arg 5))
      (.list [encGroup gs, modV, .list items, vv, ww]) (10 * A) :=
    (Det.snoc (Det.mk4 g1 gmod git g4) g5).mono (by
      have e : (Val.list ([encGroup gs, modV, .list items, vv] ++ [ww])).wt =
        (Val.list [encGroup gs, modV, .list items, vv, ww]).wt := rfl
      omega)
  have hKA' : Ka * ((Val.list [encGroup gs, modV, .list items, vv, ww]).wt + 1) ^ Da ≤ KA :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have d3 : EvalAll P [a, encGroup gs, w5] (.call ja (.snoc (mk4 (.var 1)
      (.get (.get (.var 2) (.nat 0)) (.nat 3)) (.get (.var 2) (.nat 1)) (arg 4)) (arg 5)))
      (fun u c => (TmGLAffOut n u T ∧ u.wt < KA) ∧ c ≤ 10 * A + 2 * KA + 1) :=
    EvalAll.call_funAll dV fun v ca hv => by
      obtain ⟨rfl, hca⟩ := hv
      refine (FunAll.wt_lt hcall).mono fun u c hu => ⟨⟨hu.1.1, by omega⟩, ?_⟩
      have := hu.1.2; have := hu.2
      omega
  refine EvalAll.letE d3 fun u c3 hv3 => ?_
  obtain ⟨⟨hu, huw⟩, hc3⟩ := hv3
  -- 4. the output program
  have hU : u = .list [] ∨ ∃ (t : Perm (Fin n)) (L : List (Perm (Fin n))),
      u = .list [encPerm t, encGroup L] := by
    rcases hu with ⟨h1, -⟩ | ⟨t, L, h1, -⟩
    · exact Or.inl h1
    · exact Or.inr ⟨t, L, h1⟩
  have k0 := Det.arg' (P := P) (vs := [encGroup σN, encPerm τ, .list (gs.map encPerm), in5, vv, ww])
    (rest := [encGroup gs, w5, u]) (j := 0) rfl
  have k1 := Det.arg' (P := P) (vs := [encGroup σN, encPerm τ, .list (gs.map encPerm), in5, vv, ww])
    (rest := [encGroup gs, w5, u]) (j := 1) rfl
  have k3 := Det.var' (P := P) (env := [a, encGroup gs, w5, u]) (i := 3) rfl
  have wO := wt_list_le [encGroup σN, encPerm τ, u]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wO
  set O := 3 * tmGLSOutC (pointwiseStabPrim hps).c (pointwiseStabPrim hps).k
    (4 * a.wt + 2 * KA + 10) with hO
  have hOC : 3 * tmGLSOutC (pointwiseStabPrim hps).c (pointwiseStabPrim hps).k
      (Val.list [encGroup σN, encPerm τ, u]).wt ≤ O :=
    Nat.mul_le_mul_left _ (tmGLSOutC_mono _ _ (by omega))
  have hO1 : 4 * a.wt + 2 * KA + 10 ≤ O := by
    have : 4 * a.wt + 2 * KA + 10 + 1 ≤ (4 * a.wt + 2 * KA + 10 + 1) ^ 8 :=
      Nat.le_self_pow (by norm_num) _
    rw [hO]; unfold tmGLSOutC; omega
  have d4 := EvalAll.call_funAll (f := out) (Q := fun w c => (TmGLSOutRes σN τ u w ∧ w.wt < O) ∧
      c ≤ 2 * A + 8 * KA + 2 * O) (Det.mk3 k0 k1 k3) fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    exact (FunAll.wt_lt (tmGLSOut_spec hps hout hred happ hmg hj hinv hcp hcj hmc σN τ hU)).mono
      fun w c hw => (⟨⟨hw.1.1, by have := hw.1.2; have := hw.2; omega⟩,
        by have := hw.1.2; have := hw.2; omega⟩ :
        (TmGLSOutRes σN τ u w ∧ w.wt < O) ∧ ca + c + w.wt + 1 ≤ 2 * A + 8 * KA + 2 * O)
  refine d4.mono fun w c4 hw => ⟨u, hu, hw.1.1, ?_⟩
  obtain ⟨⟨-, hwO⟩, hc4⟩ := hw
  unfold tmGLS6C
  rw [← hA, ← hKA, ← hY]
  exact tmGLS6_ar hc1 hc2 hc3 hc4 hwO.le (by omega)

end GI.Impl
