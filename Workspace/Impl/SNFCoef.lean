module

public import Workspace.Impl.SNFAltP

@[expose] public section

/-!
# The coefficients of a pair step as a program (Smith form)

Function `226` takes `[a, b, p, q]`. It runs the Hermite program on the column `[a; b]`, which
gives `x, y` with `x a + y b = g`, and returns the contexts of the two block tables of the pair
step: `[x, y, -(b/g), a/g, p, q]` for `snfL` and `[1, -(y (b/g)), 1, x (a/g), p, q]` for
`snfR` (`snfCoef_spec`).

Weights of the values in a chain of calls grow by one envelope per call. `snfG K D j Z` is the
bound after `j` calls on an input of weight `Z`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved

/-- `j` nested envelopes. -/
def snfG (K D : ℕ) : ℕ → ℕ → ℕ
  | 0, Z => Z
  | j + 1, Z => snfF K D (1000000 * snfG K D j Z + 1000000)

theorem snfG_mono {K D : ℕ} (j : ℕ) {Z Z' : ℕ} (h : Z ≤ Z') : snfG K D j Z ≤ snfG K D j Z' := by
  induction j with
  | zero => exact h
  | succ j ih => exact snfF_mono (by omega)

theorem snfG_succB {K D : ℕ} (hE : SnfEnv K D) (j Z : ℕ) :
    1000000 * snfG K D j Z + 1000000 ≤ snfG K D (j + 1) Z :=
  snfF_ge hE.one_le hE.d_pos

theorem snfG_succ {K D : ℕ} (hE : SnfEnv K D) (j Z : ℕ) : 100 * snfG K D j Z + 100 ≤ snfG K D (j + 1) Z := by
  have := snfG_succB hE j Z; omega

theorem snfG_stepB {K D : ℕ} {j Z a : ℕ} (h : a ≤ 1000000 * snfG K D j Z + 1000000) :
    snfF K D a ≤ snfG K D (j + 1) Z := snfF_mono h

theorem snfG_step {K D : ℕ} {j Z a : ℕ} (h : a ≤ 100 * snfG K D j Z + 100) :
    snfF K D a ≤ snfG K D (j + 1) Z := snfF_mono (by omega)

theorem snfG_le {K D : ℕ} (hE : SnfEnv K D) {i j : ℕ} (h : i ≤ j) (Z : ℕ) : snfG K D i Z ≤ snfG K D j Z := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · have := ih (by omega); have := snfG_succ hE j Z; omega
    · rw [show i = j + 1 by omega]

/-- The column `[a; b]` as a full-rank instance. -/
def snfInst2 (a b : ℤ) (ha : a ≠ 0) : FullRankInst := ⟨2, 1, by norm_num, by norm_num, snfM2 a b, snfM2_inj ha⟩

theorem snfM2_enc (a b : ℤ) : encIntMatrix (snfM2 a b) = .list [.list [encInt a], .list [encInt b]] := rfl

/-- Six entries in a list. -/
def snfL6 (a b c d e f : Expr) : Expr := .snoc (.snoc (mk4 a b c d) e) f

/-- The coefficients of a pair step. -/
def snfCoefE : Expr :=
  .letE (.call 151 (mk3 (.nat 2) (.nat 1) (mk2 (mk1 (arg 0)) (mk1 (arg 1)))))
  (.letE (.get (.get (.get (.var 1) (.nat 0)) (.nat 0)) (.nat 0))
  (.letE (.get (.get (.get (.var 1) (.nat 0)) (.nat 0)) (.nat 1))
  (.letE (.get (.get (.get (.var 1) (.nat 1)) (.nat 0)) (.nat 0))
  (.letE (.call 14 (mk2 (arg 0) (.var 4)))
  (.letE (.call 14 (mk2 (arg 1) (.var 4)))
  (.letE (.call 12 (mk2 hnfZeroE (.var 6)))
  (.letE (.call 13 (mk2 (.var 3) (.var 6)))
  (.letE (.call 12 (mk2 hnfZeroE (.var 8)))
  (.letE (.call 13 (mk2 (.var 2) (.var 5)))
    (mk2 (snfL6 (.var 2) (.var 3) (.var 7) (.var 5) (arg 2) (arg 3))
      (snfL6 hnfOneE (.var 9) hnfOneE (.var 10) (arg 2) (arg 3))))))))))))

/-- The output of the coefficient function. -/
def snfCoefVal (a b : ℤ) (p q : ℕ) : Val :=
  .list [.list (snfEmbCtx p q (snfBx a b) (snfBy a b) (-(b / snfBg a b)) (a / snfBg a b)),
    .list (snfEmbCtx p q 1 (-(snfBy a b * (b / snfBg a b))) 1 (snfBx a b * (a / snfBg a b)))]

theorem snf_det_snoc2 {P : Program} {env : List Val} {a b c d e f : Expr}
    {va vb vc vd ve vf : Val} {ca cb cc cd ce cf : ℕ} (ha : Det P env a va ca)
    (hb : Det P env b vb cb) (hc : Det P env c vc cc) (hd : Det P env d vd cd)
    (he : Det P env e ve ce) (hf : Det P env f vf cf) :
    Det P env (snfL6 a b c d e f) (.list [va, vb, vc, vd, ve, vf])
      (ca + cb + cc + cd + ce + cf + 6 * (Val.list [va, vb, vc, vd, ve, vf]).wt + 11) := by
  have h4 := wt_list_mono (show [va, vb, vc, vd] <+: [va, vb, vc, vd, ve, vf] from ⟨[ve, vf], rfl⟩)
  have h5 := wt_list_mono (show [va, vb, vc, vd, ve] <+: [va, vb, vc, vd, ve, vf] from ⟨[vf], rfl⟩)
  exact (Det.snoc (Det.snoc (Det.mk4 ha hb hc hd) he) hf).mono (by
    simp only [List.cons_append, List.nil_append]; omega)

set_option maxHeartbeats 8000000 in
/-- **The coefficient function.** -/
theorem snfCoef_spec {P : Program} (hH : hnfMainAt P) (hf : P.funs[226]? = some snfCoefE)
    {K D : ℕ} (hE : SnfEnv K D) (a b : ℤ) (ha : a ≠ 0) (p q : ℕ) :
    FunDet P 226 (.list [encInt a, encInt b, .nat p, .nat q]) (snfCoefVal a b p q)
      (1000 * snfG K D 4 (Val.list [encInt a, encInt b, .nat p, .nat q]).wt) := by
  have hI := linInt_spec hH.ints
  set vs : List Val := [encInt a, encInt b, .nat p, .nat q] with hvs
  set Z := (Val.list vs).wt with hZ
  set G1 := snfG K D 1 Z with hG1
  set G2 := snfG K D 2 Z with hG2
  set G3 := snfG K D 3 Z with hG3
  set G4 := snfG K D 4 Z with hG4
  have s0 : 100 * Z + 100 ≤ G1 := snfG_succ hE 0 Z
  have s1 : 100 * G1 + 100 ≤ G2 := snfG_succ hE 1 Z
  have s2 : 100 * G2 + 100 ≤ G3 := snfG_succ hE 2 Z
  have s3 : 100 * G3 + 100 ≤ G4 := snfG_succ hE 3 Z
  have wa : (encInt a).wt < Z := wt_le_wt_list (by simp [hvs])
  have wb : (encInt b).wt < Z := wt_le_wt_list (by simp [hvs])
  have wp : (Val.nat p).wt < Z := wt_le_wt_list (by simp [hvs])
  have wq : (Val.nat q).wt < Z := wt_le_wt_list (by simp [hvs])
  have w0 : (encInt 0).wt ≤ 15 := by decide
  have w1 : (encInt 1).wt ≤ 21 := by decide
  have darg : ∀ (rest : List Val) (j : ℕ) (v : Val), vs[j]? = some v →
      Det P (Val.list vs :: rest) (arg j) v (2 * Z + 10) := fun rest j v hv =>
    (Det.arg' hv).mono (by have : j < 4 := (List.getElem?_eq_some_iff.mp hv).1; omega)
  -- the Hermite program on `[a; b]`
  set I := snfInst2 a b ha with hI2
  have eI : fullRankInput I = .list [.nat 2, .nat 1, .list [.list [encInt a], .list [encInt b]]] := rfl
  have wI : (fullRankInput I).wt ≤ 100 * Z + 100 := by
    rw [eI]
    have := wt_list3_le (.nat 2) (.nat 1) (.list [.list [encInt a], .list [encInt b]])
    have := wt_list2_le (.list [encInt a]) (.list [encInt b])
    have := wt_list_le [encInt a]; have := wt_list_le [encInt b]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at *
    have : (Val.nat 2).wt ≤ 4 := wt_nat_le 2
    have : (Val.nat 1).wt ≤ 3 := wt_nat_le 1
    omega
  set v1 := Val.list [encIntMatrix (snfBU a b), encIntMatrix (snfBH a b)] with hv1
  have sh : FunDet P 151 (.list [.nat 2, .nat 1, .list [.list [encInt a], .list [encInt b]]]) v1 G1 :=
    (hnfMain_spec hH I).mono ((hE.hnf _).trans (snfG_step wI))
  have wv1 : v1.wt < G1 := sh.wt_lt
  have d1 := Det.call (Det.mk3 (Det.nat 2) (Det.nat 1) (Det.mk2 (Det.mk1 (darg [] 0 _ rfl))
    (Det.mk1 (darg [] 1 _ rfl)))) sh
  -- reading `x`, `y`, `g`
  set x := snfBx a b with hx
  set y := snfBy a b with hy
  set g := snfBg a b with hg
  have wU : (encIntMatrix (snfBU a b)).wt < v1.wt := wt_le_wt_list (by simp [hv1])
  have wHm : (encIntMatrix (snfBH a b)).wt < v1.wt := wt_le_wt_list (by simp [hv1])
  have wU0 := hnf_row_wt_lt (snfBU a b) 0
  have wH0 := hnf_row_wt_lt (snfBH a b) 0
  have wx : (encInt x).wt < (linVecVal (snfBU a b 0)).wt := linVecEntryWt (snfBU a b 0) 0
  have wy : (encInt y).wt < (linVecVal (snfBU a b 0)).wt := linVecEntryWt (snfBU a b 0) 1
  have wg : (encInt g).wt < (linVecVal (snfBH a b 0)).wt := linVecEntryWt (snfBH a b 0) 0
  have dread : ∀ (env : List Val) (hv : env[1]? = some v1) (k i j : ℕ) (rows es : List Val)
      (v : Val), [encIntMatrix (snfBU a b), encIntMatrix (snfBH a b)][k]? = some (.list rows) →
      rows[i]? = some (.list es) → es[j]? = some v →
      Det P env (.get (.get (.get (.var 1) (.nat k)) (.nat i)) (.nat j)) v
        (v1.wt + (Val.list rows).wt + (Val.list es).wt + v.wt + i + j + k + 20) := by
    intro env hv k i j rows es v hM hrow hval
    have dM := Det.get' (Det.var' (P := P) hv) (Det.nat k) hM
    have dr := Det.get' dM (Det.nat i) hrow
    have e : (Val.list [encIntMatrix (snfBU a b), encIntMatrix (snfBH a b)]).wt = v1.wt := rfl
    exact (Det.get' dr (Det.nat j) hval).mono (by rw [e]; omega)
  have d2 := dread [Val.list vs, v1] rfl 0 0 0 _ _ (encInt x) rfl (hnf_mat_get (snfBU a b) 0)
    (hnf_vec_get (snfBU a b 0) 0)
  have d3 := dread [Val.list vs, v1, encInt x] rfl 0 0 1 _ _ (encInt y) rfl
    (hnf_mat_get (snfBU a b) 0) (hnf_vec_get (snfBU a b 0) 1)
  have d4 := dread [Val.list vs, v1, encInt x, encInt y] rfl 1 0 0 _ _ (encInt g) rfl
    (hnf_mat_get (snfBH a b) 0) (hnf_vec_get (snfBH a b 0) 0)
  -- integer operations
  have iop : ∀ (z : ℤ) (w : ℕ), w ≤ 100 * snfG K D 1 Z + 100 → linIntBinaryCost w ≤ G2 :=
    fun z w hw => (hE.ints w).trans (snfG_step hw)
  set e4 : List Val := [Val.list vs, v1, encInt x, encInt y, encInt g] with he4
  have wab : (Val.list [encInt a, encInt g]).wt ≤ 100 * G1 + 100 := by
    have := wt_list2_le (encInt a) (encInt g); omega
  have wbb : (Val.list [encInt b, encInt g]).wt ≤ 100 * G1 + 100 := by
    have := wt_list2_le (encInt b) (encInt g); omega
  have q1 := (hI.quo a g).mono ((hE.ints _).trans (snfG_step wab))
  have q2 := (hI.quo b g).mono ((hE.ints _).trans (snfG_step wbb))
  have wa' : (encInt (a / g)).wt < G2 := q1.wt_lt
  have wb' : (encInt (b / g)).wt < G2 := q2.wt_lt
  have d5 := Det.call (Det.mk2 (darg [v1, encInt x, encInt y, encInt g] 0 _ rfl)
    (Det.var' (P := P) (env := e4) (i := 4) rfl)) q1
  have d6 := Det.call (Det.mk2 (darg [v1, encInt x, encInt y, encInt g, encInt (a / g)] 1 _ rfl)
    (Det.var' (P := P) (env := e4 ++ [encInt (a / g)]) (i := 4) rfl)) q2
  set e6 := e4 ++ [encInt (a / g), encInt (b / g)] with he6
  have w7 : (Val.list [encInt 0, encInt (b / g)]).wt ≤ 100 * G2 + 100 := by
    have := wt_list2_le (encInt 0) (encInt (b / g)); omega
  have o7 := (hI.sub 0 (b / g)).mono ((hE.ints _).trans (snfG_step w7))
  have d7 := Det.call (Det.mk2 hnf_det_zero (Det.var' (P := P) (env := e6) (i := 6) rfl)) o7
  have wnb : (encInt (0 - b / g)).wt < G3 := o7.wt_lt
  set e7 := e6 ++ [encInt (0 - b / g)] with he7
  have w8 : (Val.list [encInt y, encInt (b / g)]).wt ≤ 100 * G2 + 100 := by
    have := wt_list2_le (encInt y) (encInt (b / g)); omega
  have o8 := (hI.mul y (b / g)).mono ((hE.ints _).trans (snfG_step w8))
  have d8 := Det.call (Det.mk2 (Det.var' (P := P) (env := e7) (i := 3) rfl)
    (Det.var' (P := P) (env := e7) (i := 6) rfl)) o8
  have wyb : (encInt (y * (b / g))).wt < G3 := o8.wt_lt
  set e8 := e7 ++ [encInt (y * (b / g))] with he8
  have w9 : (Val.list [encInt 0, encInt (y * (b / g))]).wt ≤ 100 * G3 + 100 := by
    have := wt_list2_le (encInt 0) (encInt (y * (b / g))); omega
  have o9 := (hI.sub 0 (y * (b / g))).mono ((hE.ints _).trans (snfG_step w9))
  have d9 := Det.call (Det.mk2 hnf_det_zero (Det.var' (P := P) (env := e8) (i := 8) rfl)) o9
  have wnyb : (encInt (0 - y * (b / g))).wt < G4 := o9.wt_lt
  set e9 := e8 ++ [encInt (0 - y * (b / g))] with he9
  have w10 : (Val.list [encInt x, encInt (a / g)]).wt ≤ 100 * G2 + 100 := by
    have := wt_list2_le (encInt x) (encInt (a / g)); omega
  have o10 := (hI.mul x (a / g)).mono ((hE.ints _).trans (snfG_step w10))
  have d10 := Det.call (Det.mk2 (Det.var' (P := P) (env := e9) (i := 2) rfl)
    (Det.var' (P := P) (env := e9) (i := 5) rfl)) o10
  have wxa : (encInt (x * (a / g))).wt < G3 := o10.wt_lt
  set e10 := e9 ++ [encInt (x * (a / g))] with he10
  -- the output
  have dL := snf_det_snoc2 (Det.var' (P := P) (env := e10) (i := 2) rfl)
    (Det.var' (P := P) (env := e10) (i := 3) rfl) (Det.var' (P := P) (env := e10) (i := 7) rfl)
    (Det.var' (P := P) (env := e10) (i := 5) rfl) (darg _ 2 _ rfl) (darg _ 3 _ rfl)
  have dR := snf_det_snoc2 hnf_det_one (Det.var' (P := P) (env := e10) (i := 9) rfl) hnf_det_one
    (Det.var' (P := P) (env := e10) (i := 10) rfl) (darg _ 2 _ rfl) (darg _ 3 _ rfl)
  have dout := Det.mk2 dL dR
  have dall := Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE d4 (Det.letE d5 (Det.letE d6
    (Det.letE d7 (Det.letE d8 (Det.letE d9 (Det.letE d10 dout)))))))))
  have eout : Val.list [.list [encInt x, encInt y, encInt (0 - b / g), encInt (a / g), .nat p, .nat q],
      .list [encInt 1, encInt (0 - y * (b / g)), encInt 1, encInt (x * (a / g)), .nat p, .nat q]] =
      snfCoefVal a b p q := by
    simp only [snfCoefVal, snfEmbCtx, zero_sub, hx, hy, hg]
  apply FunDet.intro hf
  rw [← eout]
  refine dall.mono ?_
  -- the weights of the output
  have l1 := wt_list_le [encInt x, encInt y, encInt (0 - b / g), encInt (a / g), .nat p, .nat q]
  have l2 := wt_list_le [encInt 1, encInt (0 - y * (b / g)), encInt 1, encInt (x * (a / g)),
    .nat p, .nat q]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at l1 l2
  have l3 := wt_list2_le
    (.list [encInt x, encInt y, encInt (0 - b / g), encInt (a / g), .nat p, .nat q])
    (.list [encInt 1, encInt (0 - y * (b / g)), encInt 1, encInt (x * (a / g)), .nat p, .nat q])
  have l4 := wt_list3_le (.nat 2) (.nat 1) (.list [.list [encInt a], .list [encInt b]])
  have l5 := wt_list2_le (.list [encInt a]) (.list [encInt b])
  have l6 := wt_list_le [encInt a]
  have l7 := wt_list_le [encInt b]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at l6 l7
  have n2 : (Val.nat 2).wt ≤ 4 := wt_nat_le 2
  have n1 : (Val.nat 1).wt ≤ 3 := wt_nat_le 1
  have m1 := wt_list2_le (encInt a) (encInt g)
  have m2 := wt_list2_le (encInt b) (encInt g)
  have m3 := wt_list2_le (encInt 0) (encInt (b / g))
  have m4 := wt_list2_le (encInt y) (encInt (b / g))
  have m5 := wt_list2_le (encInt 0) (encInt (y * (b / g)))
  have m6 := wt_list2_le (encInt x) (encInt (a / g))
  have r1 : (Val.list ((List.finRange 2).map fun i =>
      Val.list ((List.finRange 2).map fun j => encInt (snfBU a b i j)))).wt =
      (encIntMatrix (snfBU a b)).wt := rfl
  have r2 : (Val.list ((List.finRange 2).map fun i => encInt (snfBU a b 0 i))).wt =
      (linVecVal (snfBU a b 0)).wt := rfl
  have r3 : (Val.list ((List.finRange 2).map fun i =>
      Val.list ((List.finRange 1).map fun j => encInt (snfBH a b i j)))).wt =
      (encIntMatrix (snfBH a b)).wt := rfl
  have r4 : (Val.list ((List.finRange 1).map fun i => encInt (snfBH a b 0 i))).wt =
      (linVecVal (snfBH a b 0)).wt := rfl
  have r5 : snfG K D (1 + 1) Z = G2 := rfl
  have r6 : snfG K D (2 + 1) Z = G3 := rfl
  have r7 : snfG K D (3 + 1) Z = G4 := rfl
  clear_value G1 G2 G3 G4 v1 x y g e4 e6 e7 e8 e9 e10
  omega

end GI.Impl
