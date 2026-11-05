module

public import Workspace.Impl.TermRun
public import Workspace.Impl.TermAsm
public import Workspace.Impl.RowSpecTerm

@[expose] public section

/-!
# The terminal row function (T1 with the assembly as a hypothesis)

The terminal function `tmTermBody pr d g` does three things on the input
`tin = [sv, lv, coordsVal e S E, a18Out σH σN σS 0, encFun (rowLab e L.con.blocks)]`:

1. `pr` computes the context of the calls (`tmPrep_spec`): the colorings, the coordinates, and
   generators of `N` and `H` cut down to at most `m²` elements (cited `PointwiseStab`);
2. the driver `d` runs the `5q²` calls of the terminal script (`tm_stepOK`, `run_spec`) and
   returns their canonical answers;
3. `g` assembles the answer of the state from these answers (`TermAsmSpec`, T2–T7).

`tm_rowTermSpec` proves `RowTermSpec` for this function from `TermAsmSpec`, with
the work bound `tmWt hst A nd = expLogSq A N + tmTermW hst N`: the assembly bound plus a
polynomial in `N` for steps 1 and 2 (given the cost of the cited primitive).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens PointwiseStab)

/-! ### Cost bounds -/

/-- The weight bound of the context on an input of weight `W`. -/
def tmWc (W : ℕ) : ℕ := 10 ^ 4 * (W + 1) ^ 6

/-- The bound `B` of the driver on an input of weight `W`. -/
def tmDrvB (W : ℕ) : ℕ := tmStepB (tmWc W) W (ansW W)

/-- The cost of steps 1 and 2 on an input of weight `W`. -/
noncomputable def tmTermC (hst : PointwiseStab) (W : ℕ) : ℕ :=
  tmPrepC hst W + (5 * W ^ 2 + 1) * (runK * (tmDrvB W + 1)) + 40 * tmDrvB W + 40 * tmWc W +
    40 * W + 2000

theorem tm_ansW_mono {a b : ℕ} (h : a ≤ b) : ansW a ≤ ansW b := by
  unfold ansW groupW
  have h1 : (a + 1) ^ 2 ≤ (b + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : a ^ 2 + 2 ≤ b ^ 2 + 2 := by have := Nat.pow_le_pow_left h 2; omega
  have h3 : (a ^ 2 + 2) * (a + 1) ≤ (b ^ 2 + 2) * (b + 1) := Nat.mul_le_mul h2 (by omega)
  have h4 := Nat.pow_le_pow_left h3 2
  omega

theorem tmStW_mono {a b q q' x y : ℕ} (h1 : a ≤ b) (h2 : q ≤ q') (h3 : x ≤ y) :
    tmStW a q x ≤ tmStW b q' y := by
  unfold tmStW
  have := Nat.pow_le_pow_left (show q + 1 ≤ q' + 1 by omega) 2
  have := Nat.mul_le_mul this (show x + 1 ≤ y + 1 by omega)
  have e1 : 100 * (q + 1) ^ 2 * (x + 1) = 100 * ((q + 1) ^ 2 * (x + 1)) := by ring
  have e2 : 100 * (q' + 1) ^ 2 * (y + 1) = 100 * ((q' + 1) ^ 2 * (y + 1)) := by ring
  omega

theorem tmStepB_mono {a b q q' x y : ℕ} (h1 : a ≤ b) (h2 : q ≤ q') (h3 : x ≤ y) :
    tmStepB a q x ≤ tmStepB b q' y := by
  unfold tmStepB
  have := Nat.pow_le_pow_left (show a + 1 ≤ b + 1 by omega) 6
  have := Nat.mul_le_mul_left tmAskK this
  have := Nat.pow_le_pow_left (show tmStW a q x + 1 ≤ tmStW b q' y + 1 by
    have := tmStW_mono h1 h2 h3; omega) 2
  omega

theorem tmWc_mono {a b : ℕ} (h : a ≤ b) : tmWc a ≤ tmWc b := by
  unfold tmWc
  have := Nat.pow_le_pow_left (show a + 1 ≤ b + 1 by omega) 6
  omega

theorem tmDrvB_mono {a b : ℕ} (h : a ≤ b) : tmDrvB a ≤ tmDrvB b :=
  tmStepB_mono (tmWc_mono h) h (tm_ansW_mono h)

theorem tmTermC_mono (hst : PointwiseStab) {a b : ℕ} (h : a ≤ b) :
    tmTermC hst a ≤ tmTermC hst b := by
  unfold tmTermC
  have h1 := tmPrepC_mono hst h
  have h2 := tmDrvB_mono h
  have h3 := tmWc_mono h
  have h4 : 5 * a ^ 2 + 1 ≤ 5 * b ^ 2 + 1 := by have := Nat.pow_le_pow_left h 2; omega
  have h5 := Nat.mul_le_mul h4 (Nat.mul_le_mul_left runK (show tmDrvB a + 1 ≤ tmDrvB b + 1 by
    omega))
  omega

/-! ### The cost is polynomial

`tmTermC hst W ≤ tmK hst (W + 1)^(tmD hst)`, where the constants depend on those of the cited
primitive. -/

/-- The constant of the polynomial bound of `tmTermC`. -/
noncomputable def tmK (hst : PointwiseStab) : ℕ :=
  10 ^ 52 + 2 * (pointwiseStabPrim hst).c * 402 ^ (pointwiseStabPrim hst).k

/-- The degree of the polynomial bound of `tmTermC`. -/
noncomputable def tmD (hst : PointwiseStab) : ℕ := 38 + 4 * (pointwiseStabPrim hst).k

theorem tm_pow_mono {X a b : ℕ} (hX : 1 ≤ X) (h : a ≤ b) : X ^ a ≤ X ^ b :=
  Nat.pow_le_pow_right hX h

theorem tmDrvB_le (W : ℕ) : tmDrvB W ≤ 10 ^ 48 * (W + 1) ^ 36 := by
  have hX : 1 ≤ W + 1 := by omega
  have hA : ansW W ≤ 1000 * (W + 1) ^ 6 := ansW_le W
  have h6 : (W + 1) ^ 2 * (W + 1) ^ 6 = (W + 1) ^ 8 := by ring
  have hS : tmStW (tmWc W) W (ansW W) ≤ 2 * 10 ^ 5 * (W + 1) ^ 8 := by
    unfold tmStW tmWc
    have h1 : (W + 1) ^ 2 * (ansW W + 1) ≤ (W + 1) ^ 2 * (1001 * (W + 1) ^ 6) :=
      Nat.mul_le_mul le_rfl (by have := tm_pow_mono hX (show 0 ≤ 6 by omega); simp at this; omega)
    have h2 := tm_pow_mono hX (show 6 ≤ 8 by omega)
    have e1 : 100 * (W + 1) ^ 2 * (ansW W + 1) = 100 * ((W + 1) ^ 2 * (ansW W + 1)) := by ring
    have e2 : (W + 1) ^ 2 * (1001 * (W + 1) ^ 6) = 1001 * (W + 1) ^ 8 := by ring
    omega
  have hS2 : (tmStW (tmWc W) W (ansW W) + 1) ^ 2 ≤ 10 ^ 11 * (W + 1) ^ 36 := by
    have h1 : tmStW (tmWc W) W (ansW W) + 1 ≤ 3 * 10 ^ 5 * (W + 1) ^ 8 := by
      have := tm_pow_mono hX (show 0 ≤ 8 by omega); simp at this; omega
    have h2 := Nat.pow_le_pow_left h1 2
    have e : (3 * 10 ^ 5 * (W + 1) ^ 8) ^ 2 = 9 * 10 ^ 10 * (W + 1) ^ 16 := by ring
    have h3 := tm_pow_mono hX (show 16 ≤ 36 by omega)
    omega
  have hW6 : (tmWc W + 1) ^ 6 ≤ 64 * 10 ^ 24 * (W + 1) ^ 36 := by
    have h1 : tmWc W + 1 ≤ 2 * 10 ^ 4 * (W + 1) ^ 6 := by
      unfold tmWc; have := tm_pow_mono hX (show 0 ≤ 6 by omega); simp at this; omega
    have h2 := Nat.pow_le_pow_left h1 6
    have e : (2 * 10 ^ 4 * (W + 1) ^ 6) ^ 6 = 64 * 10 ^ 24 * (W + 1) ^ 36 := by ring
    omega
  unfold tmDrvB tmStepB tmAskK
  omega

theorem tmTermC_le (hst : PointwiseStab) (W : ℕ) :
    tmTermC hst W ≤ tmK hst * (W + 1) ^ tmD hst := by
  have hX : 1 ≤ W + 1 := by omega
  have hD := tmDrvB_le W
  -- the primitive
  have hP : tmPrimC (pointwiseStabPrim hst) (400 * (W + 1) ^ 4) ≤ (pointwiseStabPrim hst).c * 402 ^ (pointwiseStabPrim hst).k * (W + 1) ^ (4 * (pointwiseStabPrim hst).k) := by
    unfold tmPrimC
    have h1 : 400 * (W + 1) ^ 4 + 2 ≤ 402 * (W + 1) ^ 4 := by
      have := tm_pow_mono hX (show 0 ≤ 4 by omega); simp at this; omega
    have h2 := Nat.pow_le_pow_left h1 (pointwiseStabPrim hst).k
    have e : (402 * (W + 1) ^ 4) ^ (pointwiseStabPrim hst).k = 402 ^ (pointwiseStabPrim hst).k * (W + 1) ^ (4 * (pointwiseStabPrim hst).k) := by rw [mul_pow, ← pow_mul]
    rw [e] at h2
    calc (pointwiseStabPrim hst).c * (400 * (W + 1) ^ 4 + 2) ^ (pointwiseStabPrim hst).k ≤ (pointwiseStabPrim hst).c * (402 ^ (pointwiseStabPrim hst).k * (W + 1) ^ (4 * (pointwiseStabPrim hst).k)) :=
          Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  have hPr : tmPrepC hst W ≤ 10 ^ 13 * (W + 1) ^ 9 + 2 * ((pointwiseStabPrim hst).c * 402 ^ (pointwiseStabPrim hst).k * (W + 1) ^ (4 * (pointwiseStabPrim hst).k)) := by
    unfold tmPrepC; omega
  -- the driver
  have hDr : (5 * W ^ 2 + 1) * (runK * (tmDrvB W + 1)) ≤ 10 ^ 51 * (W + 1) ^ 38 := by
    have h1 : 5 * W ^ 2 + 1 ≤ 6 * (W + 1) ^ 2 := by
      have : W ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have := tm_pow_mono hX (show 0 ≤ 2 by omega); simp at this; omega
    have h2 : runK * (tmDrvB W + 1) ≤ 40 * (2 * 10 ^ 48 * (W + 1) ^ 36) := by
      unfold runK
      have := tm_pow_mono hX (show 0 ≤ 36 by omega); simp at this
      omega
    have h3 := Nat.mul_le_mul h1 h2
    have e : 6 * (W + 1) ^ 2 * (40 * (2 * 10 ^ 48 * (W + 1) ^ 36)) = 480 * 10 ^ 48 * (W + 1) ^ 38 := by ring
    omega
  -- all to degree `tmD`
  have d38 := tm_pow_mono hX (show 38 ≤ tmD hst by unfold tmD; omega)
  have d36 := tm_pow_mono hX (show 36 ≤ tmD hst by unfold tmD; omega)
  have d9 := tm_pow_mono hX (show 9 ≤ tmD hst by unfold tmD; omega)
  have d6 := tm_pow_mono hX (show 6 ≤ tmD hst by unfold tmD; omega)
  have d1 := tm_pow_mono hX (show 1 ≤ tmD hst by unfold tmD; omega)
  have d0 := tm_pow_mono hX (show 0 ≤ tmD hst by omega)
  have dk := tm_pow_mono hX (show 4 * (pointwiseStabPrim hst).k ≤ tmD hst by unfold tmD; omega)
  simp only [pow_one, pow_zero] at d1 d0
  have hk : (pointwiseStabPrim hst).c * 402 ^ (pointwiseStabPrim hst).k * (W + 1) ^ (4 * (pointwiseStabPrim hst).k) ≤ (pointwiseStabPrim hst).c * 402 ^ (pointwiseStabPrim hst).k * (W + 1) ^ tmD hst :=
    Nat.mul_le_mul_left _ dk
  have m1 : 10 ^ 51 * (W + 1) ^ 38 ≤ 10 ^ 51 * (W + 1) ^ tmD hst := Nat.mul_le_mul_left _ d38
  have m2 : 10 ^ 48 * (W + 1) ^ 36 ≤ 10 ^ 48 * (W + 1) ^ tmD hst := Nat.mul_le_mul_left _ d36
  have m3 : 10 ^ 13 * (W + 1) ^ 9 ≤ 10 ^ 13 * (W + 1) ^ tmD hst := Nat.mul_le_mul_left _ d9
  have m4 : (W + 1) ^ 6 ≤ (W + 1) ^ tmD hst := d6
  have eK : tmK hst * (W + 1) ^ tmD hst = 10 ^ 52 * (W + 1) ^ tmD hst +
      2 * ((pointwiseStabPrim hst).c * 402 ^ (pointwiseStabPrim hst).k * (W + 1) ^ tmD hst) := by unfold tmK; ring
  rw [eK]
  unfold tmTermC tmWc
  omega

/-! ### The function -/

/-- **The terminal function**: the context, the driver from the empty answer lists, then the
assembly on `[tin, us, vs]`. -/
def tmTermBody (pr d g : ℕ) : Expr :=
  .letE (.call pr (.var 0))
    (.letE (.call d (mk2 (mk4 (.var 1) (.nat 0) .nil .nil) .nil))
      (.call g (mk3 (.var 0) (.get (.var 2) (.nat 0)) (.get (.var 2) (.nat 1)))))

/-- Where the functions of the terminal are. -/
structure TmFuns (Pg : Program) (F : Funs) (hst : PointwiseStab)
    (f pr br jx rp d stp ak rw vf ga dd ap g : ℕ) : Prop where
  main : Pg.funs[f]? = some (tmTermBody pr d g)
  prep : Pg.funs[pr]? = some (tmPrepBody br rp)
  red : Pg.HasAt br (redFuns br jx)
  prim : Pg.prims[jx]? = some (pointwiseStabPrim hst)
  repl : Pg.HasAt rp (replicateFuns rp)
  drv : Pg.funs[d]? = some (runBody F d stp)
  step : TmAt Pg stp ak rw vf ga dd ap

/-! ### The specification -/

theorem tm_m_lt_N {Ω C : Type} {S : State Ω C} {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    (hq : 5 ≤ q) (h0 : 0 < m) (hs : S.size ≤ S.N) : m < S.N := by
  have : S.size = m * q := by
    unfold State.size
    rw [← Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
  have : m * 5 ≤ m * q := Nat.mul_le_mul_left _ hq
  omega

/-- The weight bound of the input of the terminal function in the phase size `N`. -/
def tmInB (N : ℕ) : ℕ := 10 ^ 6 * (N + 2) ^ 6

/-- **The weight of the input of the terminal function** is polynomial in `N`. -/
theorem wt_tmIn_le {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C}
    {sv lv : Val} {L : SuppliedLabels S} (hsv : Canon e c sv S) (hlv : LabValStd e S lv L)
    {m : ℕ} (E : Fin m × Fin L.q ≃ S.dom) (hq : 0 < L.q) {σH σN σS : List (Perm (Fin m))}
    (hlH : σH.length ≤ (k + L.q) ^ 2) (hlN : σN.length ≤ (k + L.q) ^ 2)
    (hlS : σS.length ≤ (k + L.q) ^ 2) :
    (Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
      encFun (rowLab e L.con.blocks)]).wt ≤ tmInB S.N := by
  set P := S.N + 2 with hP
  have hk : k ≤ S.N := hsv.fits
  have hqk : L.q ≤ k + 2 := GiantLabels.q_le e L.toGiantLabels
  have hmk : m ≤ k := m_le_n e E ⟨0, hq⟩
  have hP1 : 1 ≤ P := by omega
  have p6 : P ^ 2 ≤ P ^ 6 := Nat.pow_le_pow_right hP1 (by omega)
  have p36 : P ^ 3 ≤ P ^ 6 := Nat.pow_le_pow_right hP1 (by omega)
  have p46 : P ^ 4 ≤ P ^ 6 := Nat.pow_le_pow_right hP1 (by omega)
  have p16 : P ≤ P ^ 6 := Nat.le_self_pow (by norm_num) _
  -- the five entries
  have w1 : sv.wt ≤ 10 ^ 4 * P ^ 6 := hsv.wt_le_poly
  have w2 : lv.wt ≤ labWStd k S.N := hlv.wt_le hsv.small'.1
  have w2' : lv.wt ≤ 3000 * P ^ 6 := by
    have := Nat.pow_le_pow_left (show k + 1 ≤ P by omega) 4
    unfold labWStd at w2
    omega
  have w3 : (coordsVal e S E).wt ≤ 15 * (k + L.q + 2) ^ 3 + 4 := wt_coordsVal_le E
  have w3' : (coordsVal e S E).wt ≤ 200 * P ^ 6 := by
    have h1 := Nat.pow_le_pow_left (show k + L.q + 2 ≤ 2 * P by omega) 3
    have h2 : (2 * P) ^ 3 = 8 * P ^ 3 := by ring
    omega
  have w4 : (a18Out σH σN σS 0).wt ≤ 400 * (k + L.q + 1) ^ 6 + 20 := by
    have hM : (k + L.q) ^ 2 + 1 ≤ 2 * (k + L.q + 1) ^ 2 := by nlinarith
    exact wt_a18Out_le (by omega) (Nat.zero_le _) (by omega) (by omega) (by omega)
  have w4' : (a18Out σH σN σS 0).wt ≤ 30000 * P ^ 6 := by
    have h1 := Nat.pow_le_pow_left (show k + L.q + 1 ≤ 2 * P by omega) 6
    have h2 : (2 * P) ^ 6 = 64 * P ^ 6 := by ring
    omega
  have w5 : (encFun (rowLab e L.con.blocks)).wt ≤ 5 * (k + L.q + 1) ^ 2 :=
    wt_encFun_le' _ (fun i => by
      have := Nat.mod_lt (lblOf e L.con.blocks i + L.q) (show 0 < L.q + 1 by omega)
      unfold rowLab; omega) (by omega)
  have w5' : (encFun (rowLab e L.con.blocks)).wt ≤ 20 * P ^ 6 := by
    have h1 := Nat.pow_le_pow_left (show k + L.q + 1 ≤ 2 * P by omega) 2
    have h2 : (2 * P) ^ 2 = 4 * P ^ 2 := by ring
    omega
  have := wt_list_le [sv, lv, coordsVal e S E, a18Out σH σN σS 0, encFun (rowLab e L.con.blocks)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at this
  show _ ≤ 10 ^ 6 * P ^ 6
  omega

/-- The input of the terminal function bounds `m` and `q`. -/
theorem tm_mq_lt {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) {S : State Ω C} {m q : ℕ}
    (E : Fin m × Fin q ≃ S.dom) (hq : 0 < q) (sv lv av rv : Val) :
    m < (Val.list [sv, lv, coordsVal e S E, av, rv]).wt ∧
      q < (Val.list [sv, lv, coordsVal e S E, av, rv]).wt := by
  have wc : (coordsVal e S E).wt < (Val.list [sv, lv, coordsVal e S E, av, rv]).wt :=
    wt_le_wt_list (by simp)
  constructor
  · have h2 : (natList ((List.finRange m).map fun β => ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))).wt <
        (coordsVal e S E).wt := by
      rw [coordsVal_eq_list]
      exact wt_le_wt_list (List.mem_map.2 ⟨⟨0, hq⟩, List.mem_finRange _, rfl⟩)
    have h3 := length_lt_wt_natList ((List.finRange m).map fun β =>
      ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))
    simp only [List.length_map, List.length_finRange] at h3
    omega
  · have := length_lt_wt_list ((List.finRange q).map fun j =>
      natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))
    simp only [List.length_map, List.length_finRange] at this
    have e1 : (coordsVal e S E).wt = (Val.list ((List.finRange q).map fun j =>
      natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))).wt := by
      rw [coordsVal_eq_list]
    omega

/-- **The weight of the context** on an input of weight `W`. -/
theorem wt_tmCtxOf_le {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) {S : State Ω C}
    {L : GiantLabels S} {m : ℕ} (E : Fin m × Fin L.q ≃ S.dom) (hq : 0 < L.q)
    (hsN hsH : List (Perm (Fin m))) (hlN : hsN.length ≤ m ^ 2) (hlH : hsH.length ≤ m ^ 2)
    {sv lv av rv : Val} (hsv : Canon e c sv S) :
    (tmCtxOf e c E hsN hsH).wt ≤ tmWc (Val.list [sv, lv, coordsVal e S E, av, rv]).wt := by
  set W := (Val.list [sv, lv, coordsVal e S E, av, rv]).wt with hW
  obtain ⟨hmW, hqW⟩ := tm_mq_lt e E hq sv lv av rv
  obtain ⟨gv, dv, xv, yv, hv, rv', -, -, hx, hy, -, -, hsv'⟩ := hsv.val
  have hx' : xv = colVal e c S.x := hx
  have hy' : yv = colVal e c S.y := hy
  subst hx' hy'
  have wsv : sv.wt < W := wt_le_wt_list (by simp)
  have wc : (coordsVal e S E).wt < W := wt_le_wt_list (by simp)
  have wxv : (colVal e c S.x).wt < sv.wt := by rw [hsv']; exact wt_le_wt_list (by simp)
  have wyv : (colVal e c S.y).wt < sv.wt := by rw [hsv']; exact wt_le_wt_list (by simp)
  have p6 : (m + 1) ^ 6 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_left (by omega) _
  have p16 : W + 1 ≤ (W + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have wN : (encGroup hsN).wt ≤ 320 * (W + 1) ^ 6 := (wt_encGroup_le_sq hlN).trans (by omega)
  have wH : (encGroup hsH).wt ≤ 320 * (W + 1) ^ 6 := (wt_encGroup_le_sq hlH).trans (by omega)
  have := wt_tmCtx_le (xv := colVal e c S.x) (yv := colVal e c S.y) (cv := coordsVal e S E)
    (gN := encGroup hsN) (gH := encGroup hsH) (m := m) (q := L.q) (X := 320 * (W + 1) ^ 6)
    (by omega) (by omega) (by omega) wN wH (by omega) (by omega)
  unfold tmCtxOf tmWc
  omega

namespace Iface

variable (I : Iface) (Pg : Program) (F : Funs)

/-- **The terminal function meets its specification, with the cost in the input weight.** -/
theorem tm_term_main (hst : PointwiseStab) {f pr br jx rp d stp ak rw vf ga dd ap g : ℕ}
    (hF : TmFuns Pg F hst f pr br jx rp d stp ak rw vf ga dd ap g) {Aa : ℝ}
    (hasm : TermAsmSpec Pg Aa g)
    {Ω C : Type} [Finite Ω] (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ)
    (hc : Function.Injective c) (sv lv : Val) (L : SuppliedLabels S) (hsv : Canon e c sv S)
    (hlv : LabValStd e S lv L) (hq0 : P₀.q₀ < L.q) (hgood : Good P₀ .giant S)
    (hrow : RowCase P₀.α S L.toGiantLabels) (ih : I.IH Pg F .giant S)
    (label : Ω → Fin L.q) (hnat : NaturalRows S L.toGiantLabels label) (hq : 5 ≤ L.q)
    {m : ℕ} (h0 : 0 < m) (E : Fin m × Fin L.q ≃ S.dom)
    (hP : PureCoords S L.toGiantLabels label E)
    (σH σN σS : List (Perm (Fin m)))
    (hH : Subgroup.closure {σ | σ ∈ σH} = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb)
    (hN : Subgroup.closure {σ | σ ∈ σN} = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb)
    (hS : Subgroup.closure {σ | σ ∈ σS} = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype)
    (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
    (hlH : σH.length ≤ (k + L.q) ^ 2) (hlN : σN.length ≤ (k + L.q) ^ 2)
    (hlS : σS.length ≤ (k + L.q) ^ 2) :
    FunAll Pg f (.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
        encFun (rowLab e L.con.blocks)])
      (fun u cost => ∃ (A : Set (Perm Ω)) (r : Run P₀ .giant S (some L) A),
        r.kind = .rowTerminal ∧ AnsC e u A ∧
        (cost : ℝ) ≤ expLogSq Aa S.N + (tmTermC hst
          (Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
            encFun (rowLab e L.con.blocks)]).wt : ℕ) + (3 * ansW k : ℕ) + I.childCost r) := by
  have hgood' : Good P₀ .giant S := hgood
  obtain ⟨hN0, hsize, htrans, hγ, -, -⟩ := hgood
  have hq1 : 0 < L.q := by omega
  have hcard : Fintype.card (Fin m) * L.q = S.size := by
    unfold State.size
    rw [← Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
  have hNpos : 0 < S.N := by omega
  set T0 := (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P₀ htr hcard hsize hNpos hrow.1
    with hT0
  have hmN : m < S.N := tm_m_lt_N E hq h0 hsize
  have hTN : ∀ ac, T0.typeCall ac = tmTestState S E σN ac := fun ac =>
    tm_typeCall_eq hnat hq h0 E hP P₀ htr hcard hsize hNpos hrow.1 σN hN ac
  have hTH : ∀ ij, T0.cosetCall ij = tmCosetState S E σH ij := fun ij =>
    tm_cosetCall_eq hnat hq h0 E hP P₀ htr hcard hsize hNpos hrow.1 σH hH ij
  set tin := Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
    encFun (rowLab e L.con.blocks)] with htin
  refine FunAll.intro hF.main ?_
  unfold tmTermBody
  -- step 1: the context
  refine EvalAll.letE (Ra := fun ctx c1 => ∃ hsN hsH : List (Perm (Fin m)),
      ctx = tmCtxOf e c E hsN hsH ∧ gens hsN = gens σN ∧ hsN.length ≤ m ^ 2 ∧
      gens hsH = gens σH ∧ hsH.length ≤ m ^ 2 ∧
      c1 ≤ tmPrepC hst tin.wt + 2 * ctx.wt + 2 * tin.wt + 5)
    (EvalAll.call_funAll (Det.var' (P := Pg) (i := 0) rfl) fun v ca hv => ?_) ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine (tmPrep_spec e S E hst hF.prep hF.red hF.prim hF.repl c sv lv _ hsv hq1 σH σN σS).mono
      fun w cb ⟨hsN, hsH, hw, h1, h2, h3, h4, hcb⟩ => ⟨hsN, hsH, hw, h1, h2, h3, h4, by
        have hcb' : cb ≤ tmPrepC hst tin.wt := hcb
        omega⟩
  rintro ctx c1 ⟨hsN, hsH, rfl, hgN, hlN', hgH, hlH', hc1⟩
  -- step 2: the driver
  have hcol := hsv.colors
  have hOK := tm_stepOK e c T0 (Equiv.refl (Fin m)) E hsN hsH hF.step hcol hq1
    (μ := measure P₀ .giant S)
    (fun a b ha hb => ⟨tmCode c (tmRowStr S E (tmRowAt L.q a ha)) (tmRowStr S E (tmRowAt L.q b hb)),
      tmCode_injective hc _ _, by
        rw [hTN]; unfold tmTestState; rw [← hgN]
        exact tm_canon_row hsN hlN' c _ _,
      by rw [hTN]; exact tm_mlt_row (B := Fin m) _ _ _ (by rw [Fintype.card_fin]; exact hmN)⟩)
    (fun i j => ⟨tmCode c (tmRowStr S E (.inl i)) (tmRowStr S E (.inr j)),
      tmCode_injective hc _ _, by
        rw [hTH]; unfold tmCosetState; rw [← hgH]
        exact tm_canon_row hsH hlH' c _ _,
      by rw [hTH]; exact tm_mlt_row (B := Fin m) _ _ _ (by rw [Fintype.card_fin]; exact hmN)⟩)
  set ctx := tmCtxOf e c E hsN hsH with hctx
  set B := tmStepB ctx.wt L.q (ansW m) with hB
  have hrun := I.run_spec Pg F hF.drv hOK ih.below _ _
    (tmRep_start e c T0 (Equiv.refl (Fin m)) E hsN hsH hq1)
  have darg := Det.mk2 (Det.mk4 (Det.var' (P := Pg) (env := [tin, ctx]) (i := 1) (v := ctx) rfl)
    (Det.nat 0) Det.nil Det.nil) Det.nil
  refine EvalAll.letE (Ra := fun out c2 => ∃ (ex : Exec P₀ (tmWithOrder T0).script S.answer)
      (us vs : List Val), out = .list [.list us, .list vs] ∧
      List.Forall₂ (fun v ac => AnsC (Equiv.refl (Fin m)) v (T0.typeCall ac).answer) us
        (tmTests L.q) ∧
      List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (T0.cosetCall ij).answer) vs
        (tmCosets L.q) ∧ out.wt ≤ B ∧
      (c2 : ℝ) ≤ ((30 * ctx.wt + 1000 + 2 * B + 1 : ℕ) : ℝ) +
        ((5 * L.q ^ 2 : ℕ) + 1) * (runK * ((B : ℝ) + 1)) + I.execCost ex)
    (EvalAll.call_funAll darg fun v ca hv => ?_) ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine hrun.mono fun out cd ⟨a, ex, ⟨ha, us, vs, hout, hus, hvs⟩, hwo, hcd⟩ => ?_
    subst ha
    refine ⟨ex, us, vs, hout, hus, hvs, hwo, ?_⟩
    rw [Exec.calls_length, RowTerminal.numCalls_eq] at hcd
    have w4 := wt_list4_le ctx (.nat 0) (.list []) (.list [])
    have w2 := wt_list2_le (.list [ctx, .nat 0, .list [], .list []]) (.list [])
    have w0 : (Val.nat 0).wt ≤ 3 := by decide
    have wl : (Val.list []).wt ≤ 5 := by decide
    have : ca ≤ 30 * ctx.wt + 1000 := by omega
    have : ca + out.wt + 1 ≤ 30 * ctx.wt + 1000 + 2 * B + 1 := by omega
    have h' : ((ca + cd + out.wt + 1 : ℕ) : ℝ) = ((ca + out.wt + 1 : ℕ) : ℝ) + (cd : ℝ) := by
      push_cast; ring
    rw [h']
    have : ((ca + out.wt + 1 : ℕ) : ℝ) ≤ ((30 * ctx.wt + 1000 + 2 * B + 1 : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at hcd this ⊢
    linarith
  rintro out c2 ⟨ex, us, vs, rfl, hus, hvs, hwo, hc2⟩
  -- step 3: the assembly
  have hus' : List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (tmTestState S E σN ac).answer)
      us (tmTests L.q) := hus.imp fun u ac h => by rwa [hTN] at h
  have hvs' : List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (tmCosetState S E σH ij).answer)
      vs (tmCosets L.q) := hvs.imp fun v ij h => by rwa [hTH] at h
  have dlist := Det.mk3
    (Det.var' (P := Pg) (env := [tin, ctx, .list [.list us, .list vs]]) (i := 0) (v := tin) rfl)
    (Det.get' (Det.var' (P := Pg) (env := [tin, ctx, .list [.list us, .list vs]]) (i := 2) rfl)
      (Det.nat 0) (v := .list us) rfl)
    (Det.get' (Det.var' (P := Pg) (env := [tin, ctx, .list [.list us, .list vs]]) (i := 2) rfl)
      (Det.nat 1) (v := .list vs) rfl)
  refine EvalAll.call_funAll dlist fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine (hasm S k e c hc sv lv L hsv hlv hq0 hgood' hrow label hnat hq h0 E hP σH σN σS hH hN hS
    htr hlH hlN hlS us vs hus' hvs').mono fun u cg ⟨hu, hcg⟩ => ?_
  refine ⟨S.answer, Run.rowTerminal hγ htrans L hrow (tmWithOrder T0) ex, rfl, hu, ?_⟩
  have hcc : I.childCost (Run.rowTerminal hγ htrans L hrow (tmWithOrder T0) ex) =
      I.execCost ex := rfl
  rw [hcc]
  -- the cost
  set W := tin.wt with hW
  obtain ⟨hmW, hqW⟩ := tm_mq_lt e E hq1 sv lv (a18Out σH σN σS 0) (encFun (rowLab e L.con.blocks))
  have hmW' : m < W := hmW
  have hqW' : L.q < W := hqW
  have hctxW : ctx.wt ≤ tmWc W := wt_tmCtxOf_le e c E hq1 hsN hsH hlN' hlH' hsv
  have hBW : B ≤ tmDrvB W := tmStepB_mono hctxW hqW'.le (tm_ansW_mono hmW'.le)
  have huw := hu.wt_le
  have wus : (Val.list us).wt < (Val.list [.list us, .list vs]).wt := wt_le_wt_list (by simp)
  have wvs : (Val.list vs).wt < (Val.list [.list us, .list vs]).wt := wt_le_wt_list (by simp)
  have w3 := wt_list3_le tin (.list us) (.list vs)
  have w0 : (Val.nat 0).wt ≤ 3 := by decide
  have w1 : (Val.nat 1).wt ≤ 3 := by decide
  have hD : (5 * L.q ^ 2 + 1) * (runK * (B + 1)) ≤ (5 * W ^ 2 + 1) * (runK * (tmDrvB W + 1)) :=
    Nat.mul_le_mul (by have := Nat.pow_le_pow_left hqW'.le 2; omega)
      (Nat.mul_le_mul_left _ (by omega))
  have hsum : c1 + ca + 3 * u.wt + 3 + (30 * ctx.wt + 1000 + 2 * B + 1) +
      (5 * L.q ^ 2 + 1) * (runK * (B + 1)) ≤ tmTermC hst W + 3 * ansW k := by
    have : c1 ≤ tmPrepC hst W + 2 * ctx.wt + 2 * W + 5 := hc1
    unfold tmTermC
    omega
  have hD' : (((5 * L.q ^ 2 : ℕ) : ℝ) + 1) * ((runK : ℝ) * ((B : ℝ) + 1)) =
      (((5 * L.q ^ 2 + 1) * (runK * (B + 1)) : ℕ) : ℝ) := by push_cast; ring
  rw [hD'] at hc2
  have hsum' : ((c1 + ca + 3 * u.wt + 3 + (30 * ctx.wt + 1000 + 2 * B + 1) +
      (5 * L.q ^ 2 + 1) * (runK * (B + 1)) : ℕ) : ℝ) ≤ ((tmTermC hst W + 3 * ansW k : ℕ) : ℝ) := by
    exact_mod_cast hsum
  push_cast at hsum' hc2 ⊢
  linarith

/-- **The work bound of the terminal function**: the assembly bound `expLogSq A N`, plus a
polynomial in `N` for the context and the driver, plus three answer weights. -/
noncomputable def tmWt (hst : PointwiseStab) (Aa : ℝ) (nd : Node P₀) : ℝ :=
  expLogSq Aa nd.S.N + (tmTermC hst (tmInB nd.S.N) : ℕ) + (3 * ansW nd.S.N : ℕ)

/-- **The terminal function meets `RowTermSpec`** (Theorem `thm:transitive-gat-terminal`), given
the assembly `TermAsmSpec` (T2–T7) and the cited `PointwiseStab`. -/
theorem tm_rowTermSpec (hst : PointwiseStab) {f pr br jx rp d stp ak rw vf ga dd ap g : ℕ}
    (hF : TmFuns Pg F hst f pr br jx rp d stp ak rw vf ga dd ap g) {Aa : ℝ}
    (hasm : TermAsmSpec Pg Aa g) : I.RowTermSpec Pg F (tmWt hst Aa) f := by
  intro Ω C _ S k e c hc sv lv L hsv hlv hq0 hgood hrow ih label hnat hq m h0 E hP σH σN σS t
    hH hN hS ht htr hlH hlN hlS
  subst ht
  refine (I.tm_term_main Pg F hst hF hasm S k e c hc sv lv L hsv hlv hq0 hgood hrow ih label hnat
    hq h0 E hP σH σN σS hH hN hS htr hlH hlN hlS).mono ?_
  rintro u cost ⟨A, r, hk, hu, hcost⟩
  refine ⟨A, r, hk, hu, hcost.trans ?_⟩
  have h1 := tmTermC_mono hst (wt_tmIn_le hsv hlv E (by omega) hlH hlN hlS)
  have h2 := tm_ansW_mono hsv.fits
  have h1' : ((tmTermC hst (Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
      encFun (rowLab e L.con.blocks)]).wt : ℕ) : ℝ) ≤ ((tmTermC hst (tmInB S.N) : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h2' : ((3 * ansW k : ℕ) : ℝ) ≤ ((3 * ansW S.N : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left 3 h2
  show _ ≤ expLogSq Aa S.N + ((tmTermC hst (tmInB S.N) : ℕ) : ℝ) + ((3 * ansW S.N : ℕ) : ℝ) + _
  linarith

end Iface

/-! ### The work bound fits in `E_N` -/

/-- The constant of the polynomial part of `tmWt` in `N + 2`. -/
noncomputable def tmKN (hst : PointwiseStab) : ℕ := tmK hst * (2 * 10 ^ 6) ^ tmD hst + 3000

/-- The constant `A'` with `tmWt hst A ≤ expLogSq A' N`. -/
noncomputable def tmA (hst : PointwiseStab) (Aa : ℝ) : ℝ :=
  Aa + 3 * (Real.log (tmKN hst) + (6 * tmD hst : ℕ)) + 3

theorem tm_poly_le (hst : PointwiseStab) (N : ℕ) :
    tmTermC hst (tmInB N) + 3 * ansW N ≤ tmKN hst * (N + 2) ^ (6 * tmD hst) := by
  set P := N + 2 with hP
  have hP1 : 1 ≤ P := by omega
  have h1 := tmTermC_le hst (tmInB N)
  have h2 : tmInB N + 1 ≤ 2 * 10 ^ 6 * P ^ 6 := by
    have : 1 ≤ P ^ 6 := Nat.one_le_pow _ _ hP1
    show 10 ^ 6 * P ^ 6 + 1 ≤ _
    omega
  have h3 := Nat.pow_le_pow_left h2 (tmD hst)
  have e : (2 * 10 ^ 6 * P ^ 6) ^ tmD hst = (2 * 10 ^ 6) ^ tmD hst * P ^ (6 * tmD hst) := by
    rw [mul_pow, ← pow_mul]
  rw [e] at h3
  have h4 := Nat.mul_le_mul_left (tmK hst) h3
  have h5 : 3 * ansW N ≤ 3000 * P ^ (6 * tmD hst) := by
    have := ansW_le N
    have h6 := Nat.pow_le_pow_left (show N + 1 ≤ P by omega) 6
    have h7 : P ^ 6 ≤ P ^ (6 * tmD hst) := Nat.pow_le_pow_right hP1 (by unfold tmD; omega)
    omega
  have e2 : tmKN hst * P ^ (6 * tmD hst) =
      tmK hst * ((2 * 10 ^ 6) ^ tmD hst * P ^ (6 * tmD hst)) + 3000 * P ^ (6 * tmD hst) := by
    unfold tmKN; ring
  rw [e2]
  omega

/-- **The work bound of the terminal function is at most `E_N`**: `tmWt hst A nd ≤
expLogSq (tmA hst A) N` for `A ≥ 0`. This is the form `Rest.Req` asks for `Wrow` at
`rowTerminal` nodes. -/
theorem tmWt_le (hst : PointwiseStab) {Aa : ℝ} (hA : 0 ≤ Aa) (nd : Node P₀) :
    Iface.tmWt hst Aa nd ≤ expLogSq (tmA hst Aa) nd.S.N := by
  unfold Iface.tmWt tmA
  have hK : (1 : ℝ) ≤ tmKN hst := by
    have : 1 ≤ tmKN hst := by unfold tmKN; omega
    exact_mod_cast this
  have h1 := pow_le_expLogSq hK (6 * tmD hst) nd.S.N
  have h2 := tm_poly_le hst nd.S.N
  have h2' : ((tmTermC hst (tmInB nd.S.N) : ℕ) : ℝ) + ((3 * ansW nd.S.N : ℕ) : ℝ) ≤
      (tmKN hst : ℝ) * ((nd.S.N : ℝ) + 2) ^ (6 * tmD hst) := by
    have := (Nat.cast_le (α := ℝ)).2 h2
    push_cast at this ⊢
    linarith
  have h3 := expLogSq_add_le hA (by
    have := Real.log_nonneg hK
    positivity : (0 : ℝ) ≤ 3 * (Real.log (tmKN hst) + (6 * tmD hst : ℕ))) nd.S.N
  linarith

end GI.Impl
