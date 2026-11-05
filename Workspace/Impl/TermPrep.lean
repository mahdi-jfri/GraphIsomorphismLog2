module

public import Workspace.Impl.TermStep
public import Workspace.Impl.Reduce

@[expose] public section

/-!
# The context of the terminal calls (T1)

On the input `[sv, lv, cv, av, rl]` of the terminal function (`Iface.RowTermSpec`), with
`cv = coordsVal e S E` and `av = a18Out σH σN σS 0`, the function `tmPrepF` computes the context
`tmCtx xv yv cv gN gH m q` of the calls (`Workspace/Impl/TermStep.lean`):

* `xv`, `yv`: entries `3` and `4` of the state value;
* `m`, `q`: the length of the first row of `cv` and the number of rows;
* `gN`, `gH`: the generators `σN`, `σH` of Theorem A.18 as group values (`mkGroup`), cut to at
  most `m²` generators by the cited task **PointwiseStab** with no points (`red_spec`). A call of
  `Solve` needs at most `m²` generators (`GroupValC`), while A.18 gives up to `(k + q)²`.
* `ones`: the list of `m` ones (`replicate`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens PointwiseStab)

variable {Ω C : Type}

/-- The number `m` of points of a row: the length of the first row of `cv`. -/
def tmMExpr : Expr := .length (.get (arg 2) (.nat 0))

/-- The group value of the generators at entry `i` of `av`, cut to at most `m²` generators. -/
def tmGrpExpr (br i : ℕ) : Expr :=
  .call br (mk2 tmMExpr (.call (br + 1) (mk2 tmMExpr (.get (arg 3) (.nat i)))))

/-- **The body of `tmPrepF`**, with the reduction module at `br` (`redFuns`, whose `mkGroup` is
at `br + 1`) and `replicate` at `rp`. -/
def tmPrepBody (br rp : ℕ) : Expr :=
  .letE (tmGrpExpr br 1)
  (.letE (tmGrpExpr br 0)
  (.letE (.call rp (mk2 tmMExpr (.nat 1)))
  (Expr.mkList [.get (arg 0) (.nat 3), .get (arg 0) (.nat 4), arg 2, .var 1, .var 2, .var 3,
    tmMExpr, .length (arg 2)])))

/-- The cost of a primitive on arguments of size at most `X`. -/
def tmPrimC (p : Prim) (X : ℕ) : ℕ := p.c * (X + 2) ^ p.k

theorem prim_bound_le (p : Prim) {v : Val} {X : ℕ} (h : v.wt ≤ X) : p.bound v ≤ tmPrimC p X :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := v.size_le_wt; omega) _)

/-- The cost bound of `tmPrepF` on an input of weight `W`. -/
noncomputable def tmPrepC (hst : PointwiseStab) (W : ℕ) : ℕ :=
  10 ^ 13 * (W + 1) ^ 9 + 2 * tmPrimC (pointwiseStabPrim hst) (400 * (W + 1) ^ 4)

theorem tmPrimC_mono (p : Prim) {X Y : ℕ} (h : X ≤ Y) : tmPrimC p X ≤ tmPrimC p Y :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem tmPrepC_mono (hst : PointwiseStab) {W W' : ℕ} (h : W ≤ W') :
    tmPrepC hst W ≤ tmPrepC hst W' := by
  unfold tmPrepC
  have h1 : (W + 1) ^ 9 ≤ (W' + 1) ^ 9 := Nat.pow_le_pow_left (by omega) _
  have h2 : (W + 1) ^ 4 ≤ (W' + 1) ^ 4 := Nat.pow_le_pow_left (by omega) _
  have h3 := tmPrimC_mono (pointwiseStabPrim hst) (Nat.mul_le_mul_left 400 h2)
  omega

section Prep

variable {P : Program} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) {m q : ℕ}
  (E : Fin m × Fin q ≃ S.dom)

/-- The first row of `cv` has `m` entries. -/
theorem tmM_det (sv lv av rv : Val) (rest : List Val) (hq : 0 < q) :
    Det P (.list [sv, lv, coordsVal e S E, av, rv] :: rest) tmMExpr (.nat m)
      (4 * (Val.list [sv, lv, coordsVal e S E, av, rv]).wt + 20) := by
  set tin := Val.list [sv, lv, coordsVal e S E, av, rv]
  have wc : (coordsVal e S E).wt < tin.wt := wt_le_wt_list (by simp)
  have d2 := Det.arg' (P := P) (vs := [sv, lv, coordsVal e S E, av, rv]) (rest := rest) (j := 2)
    (v := coordsVal e S E) rfl
  replace d2 : Det P _ _ (.list ((List.finRange q).map fun j =>
      natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ))))
      (2 * tin.wt + 2 + 5) := d2
  have hrow := coordsVal_get? e S E ⟨0, hq⟩
  have d0 := Det.get' d2 (Det.nat 0) hrow
  have dl := Det.length d0
  have hwr : (natList ((List.finRange m).map fun β => ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))).wt <
      (coordsVal e S E).wt := by
    rw [coordsVal_eq_list]
    exact wt_le_wt_list (List.mem_map.2 ⟨⟨0, hq⟩, List.mem_finRange _, rfl⟩)
  have hlen := length_lt_wt_list (((List.finRange m).map fun β =>
    ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ)).map Val.nat)
  simp only [List.length_map, List.length_finRange] at hlen dl
  refine dl.mono ?_
  have : (Val.list (((List.finRange m).map fun β => ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ)).map
    Val.nat)).wt = (natList ((List.finRange m).map fun β =>
      ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))).wt := rfl
  have e1 : (coordsVal e S E).wt = (Val.list ((List.finRange q).map fun j =>
      natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))).wt := by
    rw [coordsVal_eq_list]
  omega

theorem wt_a18Out_entry {σH σN σS : List (Perm (Fin m))} {t : ℕ} {i : ℕ} {σ : List (Perm (Fin m))}
    (hi : [Val.list (σH.map encPerm), .list (σN.map encPerm), .list (σS.map encPerm), .nat t][i]? =
      some (.list (σ.map encPerm))) :
    σ.length < (a18Out σH σN σS t).wt := by
  have h1 : (Val.list (σ.map encPerm)).wt < (a18Out σH σN σS t).wt :=
    wt_le_wt_list (List.mem_of_getElem? hi)
  have h2 := length_lt_wt_list (σ.map encPerm)
  simp only [List.length_map] at h2
  omega

/-- **The group value at entry `i` of `av`**, cut to at most `m²` generators. -/
theorem tmGrp_spec (hst : PointwiseStab) {br j : ℕ} (hr : P.HasAt br (redFuns br j))
    (hj : P.prims[j]? = some (pointwiseStabPrim hst)) (sv lv rv : Val) (rest : List Val)
    (hq : 0 < q) (σH σN σS σ : List (Perm (Fin m))) (i : ℕ)
    (hi : [Val.list (σH.map encPerm), .list (σN.map encPerm), .list (σS.map encPerm), .nat 0][i]? =
      some (.list (σ.map encPerm))) :
    EvalAll P (.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rv] :: rest) (tmGrpExpr br i)
      (fun v cost => ∃ hs : List (Perm (Fin m)), v = encGroup hs ∧ gens hs = gens σ ∧
        hs.length ≤ m ^ 2 ∧ cost ≤ 10 ^ 12 * ((Val.list [sv, lv, coordsVal e S E,
          a18Out σH σN σS 0, rv]).wt + 1) ^ 9 + tmPrimC (pointwiseStabPrim hst)
            (400 * ((Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rv]).wt + 1) ^ 4)) := by
  set av := a18Out σH σN σS 0
  set tin := Val.list [sv, lv, coordsVal e S E, av, rv] with htin
  set W := tin.wt with hW
  have hmk : P.HasAt (br + 1) (mkGroupFuns (br + 1)) := hr.block 1 (by rfl)
  have dm := tmM_det (P := P) e S E sv lv av rv rest hq
  have d3 := Det.arg' (P := P) (vs := [sv, lv, coordsVal e S E, av, rv]) (rest := rest) (j := 3)
    (v := av) rfl
  have dσ := Det.get' d3 (Det.nat i) hi
  have hmkg := mkGroup_spec hmk σ
  have dg := Det.call (Det.mk2 dm dσ) hmkg
  have hG : GroupVal m (encGroup σ) (gens σ) := ⟨σ, rfl, rfl⟩
  refine EvalAll.call_funAll (Det.mk2 dm dg) fun v ca h => ?_
  obtain ⟨rfl, hca⟩ := h
  refine (red_spec hst hr hj hG).mono fun w cw ⟨hs, hw, hg, hl, hc⟩ => ⟨hs, hw, hg, hl, ?_⟩
  -- the cost
  have wav : av.wt < W := wt_le_wt_list (by simp)
  have wc : (coordsVal e S E).wt < W := wt_le_wt_list (by simp)
  have hlσ : σ.length < W := (wt_a18Out_entry hi).trans wav
  have hmW : m < W := by
    have := length_lt_wt_list ((List.finRange q).map fun j =>
      natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))
    have h2 : (natList ((List.finRange m).map fun β => ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))).wt <
        (coordsVal e S E).wt := by
      rw [coordsVal_eq_list]
      exact wt_le_wt_list (List.mem_map.2 ⟨⟨0, hq⟩, List.mem_finRange _, rfl⟩)
    have h3 := length_lt_wt_natList ((List.finRange m).map fun β =>
      ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))
    simp only [List.length_map, List.length_finRange] at h3
    omega
  have hY : 1 ≤ W + 1 := by omega
  have wσ : (Val.list (σ.map encPerm)).wt < av.wt := wt_le_wt_list (List.mem_of_getElem? hi)
  have wg := wt_encGroup_le σ
  have hgl : (σ.length + 2) * (m + 1) ≤ 2 * (W + 1) ^ 2 := by
    have h1 : (σ.length + 2) * (m + 1) ≤ (2 * (W + 1)) * (W + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (2 * (W + 1)) * (W + 1) = 2 * (W + 1) ^ 2 := by ring
    omega
  have wg' : (encGroup σ).wt ≤ 160 * (W + 1) ^ 4 := by
    have h1 := Nat.pow_le_pow_left hgl 2
    have h2 : (2 * (W + 1) ^ 2) ^ 2 = 4 * (W + 1) ^ 4 := by ring
    omega
  have hb := prim_bound_le (pointwiseStabPrim hst) (v := .list [encGroup σ, .list []])
    (X := 400 * (W + 1) ^ 4) (by
      have := wt_list2_le (encGroup σ) (.list [])
      have : (Val.list []).wt ≤ 5 := by decide
      have : 1 ≤ (W + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      omega)
  have hmkc : ((σ.length + 2) * (m + 1)) ^ 3 ≤ 8 * (W + 1) ^ 6 := by
    have h1 := Nat.pow_le_pow_left hgl 3
    have h2 : (2 * (W + 1) ^ 2) ^ 3 = 8 * (W + 1) ^ 6 := by ring
    omega
  have hm9 : (m + 1) ^ 9 ≤ (W + 1) ^ 9 := Nat.pow_le_pow_left (by omega) _
  have p49 : (W + 1) ^ 4 ≤ (W + 1) ^ 9 := Nat.pow_le_pow_right hY (by omega)
  have p69 : (W + 1) ^ 6 ≤ (W + 1) ^ 9 := Nat.pow_le_pow_right hY (by omega)
  have p19 : W + 1 ≤ (W + 1) ^ 9 := Nat.le_self_pow (by norm_num) _
  have wl2 := wt_list2_le (.nat m) (Val.list (σ.map encPerm))
  have wl3 := wt_list2_le (.nat m) (encGroup σ)
  have wm := wt_nat_le m
  have hwo : w.wt ≤ 320 * (W + 1) ^ 6 := by
    rw [hw]
    have h1 := wt_encGroup_le_sq hl
    have h2 : (m + 1) ^ 6 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_left (by omega) _
    omega
  have hWe : (Val.list [sv, lv, coordsVal e S E, av, rv]).wt = W := rfl
  have hi4 : i < 4 := by
    have := (List.getElem?_eq_some_iff.1 hi).1
    simpa using this
  simp only [mkGroupK] at *
  omega

theorem wt_tmCtx_le {xv yv cv gN gH : Val} {m q X : ℕ} (hx : xv.wt ≤ X) (hy : yv.wt ≤ X)
    (hc : cv.wt ≤ X) (hn : gN.wt ≤ X) (hh : gH.wt ≤ X) (hm : m ≤ X) (hq : q ≤ X) :
    (tmCtx xv yv cv gN gH m q).wt ≤ 30 * X + 40 := by
  have := wt_list_le [xv, yv, cv, gN, gH, tmOnes m, .nat m, .nat q]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at this
  have := wt_tmOnes_le m
  have := wt_nat_le m
  have := wt_nat_le q
  unfold tmCtx
  omega

/-- **The context of the calls.** `W` is the weight of the input. -/
theorem tmPrep_spec (hst : PointwiseStab) {f br rp j : ℕ}
    (hf : P.funs[f]? = some (tmPrepBody br rp)) (hr : P.HasAt br (redFuns br j))
    (hj : P.prims[j]? = some (pointwiseStabPrim hst)) (hrp : P.HasAt rp (replicateFuns rp))
    (c : C → ℕ) (sv lv rv : Val) (hsv : Canon e c sv S) (hq : 0 < q)
    (σH σN σS : List (Perm (Fin m))) :
    FunAll P f (.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rv]) (fun w cost =>
      ∃ hsN hsH : List (Perm (Fin m)), w = tmCtx (colVal e c S.x) (colVal e c S.y)
        (coordsVal e S E) (encGroup hsN) (encGroup hsH) m q ∧
        gens hsN = gens σN ∧ hsN.length ≤ m ^ 2 ∧ gens hsH = gens σH ∧ hsH.length ≤ m ^ 2 ∧
        cost ≤ tmPrepC hst (Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rv]).wt) := by
  set av := a18Out σH σN σS 0
  set tin := Val.list [sv, lv, coordsVal e S E, av, rv] with htin
  set W := tin.wt with hW
  obtain ⟨gv, dv, xv, yv, hv, rv', -, -, hx, hy, -, -, hsv'⟩ := hsv.val
  have hx' : xv = colVal e c S.x := hx
  have hy' : yv = colVal e c S.y := hy
  subst hx' hy'
  set G := 10 ^ 12 * (W + 1) ^ 9 + tmPrimC (pointwiseStabPrim hst) (400 * (W + 1) ^ 4) with hG
  refine FunAll.intro hf ?_
  unfold tmPrepBody
  refine EvalAll.letE (tmGrp_spec (P := P) e S E hst hr hj sv lv rv [] hq σH σN σS σN 1 rfl)
    fun gN ca ⟨hsN, hgN, hgsN, hlN, hca⟩ => ?_
  subst hgN
  refine EvalAll.letE (tmGrp_spec (P := P) e S E hst hr hj sv lv rv [encGroup hsN] hq σH σN σS σH
    0 rfl) fun gH cb ⟨hsH, hgH, hgsH, hlH, hcb⟩ => ?_
  subst hgH
  -- the weights
  have wsv : sv.wt < W := wt_le_wt_list (by simp)
  have wc : (coordsVal e S E).wt < W := wt_le_wt_list (by simp)
  have wxv : (colVal e c S.x).wt < W := by
    have : (colVal e c S.x).wt < sv.wt := by rw [hsv']; exact wt_le_wt_list (by simp)
    omega
  have wyv : (colVal e c S.y).wt < W := by
    have : (colVal e c S.y).wt < sv.wt := by rw [hsv']; exact wt_le_wt_list (by simp)
    omega
  have hmW : m < W := by
    have h2 : (natList ((List.finRange m).map fun β => ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))).wt <
        (coordsVal e S E).wt := by
      rw [coordsVal_eq_list]
      exact wt_le_wt_list (List.mem_map.2 ⟨⟨0, hq⟩, List.mem_finRange _, rfl⟩)
    have h3 := length_lt_wt_natList ((List.finRange m).map fun β =>
      ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))
    simp only [List.length_map, List.length_finRange] at h3
    omega
  have hqW : q < W := by
    have := length_lt_wt_list ((List.finRange q).map fun j =>
      natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))
    simp only [List.length_map, List.length_finRange] at this
    have e1 : (coordsVal e S E).wt = (Val.list ((List.finRange q).map fun j =>
      natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))).wt := by
      rw [coordsVal_eq_list]
    omega
  have hY : 1 ≤ W + 1 := by omega
  have p6 : (m + 1) ^ 6 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_left (by omega) _
  have wN : (encGroup hsN).wt ≤ 320 * (W + 1) ^ 6 := (wt_encGroup_le_sq hlN).trans (by omega)
  have wH : (encGroup hsH).wt ≤ 320 * (W + 1) ^ 6 := (wt_encGroup_le_sq hlH).trans (by omega)
  have p16 : W + 1 ≤ (W + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have p69 : (W + 1) ^ 6 ≤ (W + 1) ^ 9 := Nat.pow_le_pow_right hY (by omega)
  -- the list of ones
  have hrep : FunDet P rp (.list [.nat m, .nat 1]) (tmOnes m) (loopModK * (W + 1) * (20 * W + 20)) := by
    refine FunAll.mono (replicate_spec hrp m (.nat 1)) fun w cw ⟨hw, hcw⟩ => ⟨hw, ?_⟩
    have e1 : w = tmOnes m := hw
    subst e1
    refine hcw.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) ?_)
    have := wt_list2_le (.nat m) (.nat 1)
    have := wt_nat_le m
    have := wt_tmOnes_le m
    have : (Val.nat 1).wt ≤ 3 := by decide
    omega
  set env := [tin, encGroup hsN, encGroup hsH]
  have dm := tmM_det (P := P) e S E sv lv av rv [encGroup hsN, encGroup hsH] hq
  refine EvalAll.letE ((Det.call (Det.mk2 dm (Det.nat 1)) hrep)) fun ones cc h => ?_
  obtain ⟨rfl, hcc⟩ := h
  -- the output list
  set env' := [tin, encGroup hsN, encGroup hsH, tmOnes m]
  have hWe : (Val.list [sv, lv, coordsVal e S E, av, rv]).wt = W := rfl
  have hpieces : ∀ p ∈ [(Expr.get (arg 0) (.nat 3), colVal e c S.x),
      (Expr.get (arg 0) (.nat 4), colVal e c S.y), (arg 2, coordsVal e S E),
      (Expr.var 1, encGroup hsN), (Expr.var 2, encGroup hsH), (Expr.var 3, tmOnes m),
      (tmMExpr, Val.nat m), (Expr.length (arg 2), Val.nat q)],
      Det P env' p.1 p.2 (1000 * (W + 1) ^ 6) := by
    intro p hp
    have d0 := Det.arg' (P := P) (vs := [sv, lv, coordsVal e S E, av, rv])
      (rest := [encGroup hsN, encGroup hsH, tmOnes m]) (j := 0) (v := sv) rfl
    have d2 := Det.arg' (P := P) (vs := [sv, lv, coordsVal e S E, av, rv])
      (rest := [encGroup hsN, encGroup hsH, tmOnes m]) (j := 2) (v := coordsVal e S E) rfl
    rw [hWe] at d0 d2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have d0x : Det P env' (arg 0) (.list [.nat k, gv, dv, colVal e c S.x, colVal e c S.y, hv, rv',
          boolVal S.floor, .nat S.h, .nat S.N]) (2 * W + 0 + 5) := by rw [← hsv']; exact d0
      exact (Det.get' d0x (Det.nat 3) rfl).mono (by omega)
    · have d0x : Det P env' (arg 0) (.list [.nat k, gv, dv, colVal e c S.x, colVal e c S.y, hv, rv',
          boolVal S.floor, .nat S.h, .nat S.N]) (2 * W + 0 + 5) := by rw [← hsv']; exact d0
      exact (Det.get' d0x (Det.nat 4) rfl).mono (by omega)
    · exact d2.mono (by omega)
    · exact (Det.var' (P := P) (env := env') (i := 1) rfl).mono (by omega)
    · exact (Det.var' (P := P) (env := env') (i := 2) rfl).mono (by omega)
    · exact (Det.var' (P := P) (env := env') (i := 3) rfl).mono (by have := wt_tmOnes_le m; omega)
    · exact (tmM_det (P := P) e S E sv lv av rv [encGroup hsN, encGroup hsH, tmOnes m] hq).mono
        (by rw [hWe]; omega)
    · replace d2 : Det P env' (arg 2) (.list ((List.finRange q).map fun j =>
          natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ))))
          (2 * W + 2 + 5) := d2
      have dl := Det.length d2
      simp only [List.length_map, List.length_finRange] at dl
      exact dl.mono (by omega)
  have dl := Det.mkList _ hpieces
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at dl
  refine dl.post fun cw hcw => ⟨hsN, hsH, rfl, hgsN, hlN, hgsH, hlH, ?_⟩
  -- the cost
  have wout := wt_tmCtx_le (X := 320 * (W + 1) ^ 6) (xv := colVal e c S.x) (yv := colVal e c S.y)
    (cv := coordsVal e S E) (gN := encGroup hsN) (gH := encGroup hsH) (m := m) (q := q)
    (by omega) (by omega) (by omega) wN wH (by omega) (by omega)
  have hwo1 : (tmOnes m).wt ≤ 7 * W + 4 := by have := wt_tmOnes_le m; omega
  have hrc : loopModK * (W + 1) * (20 * W + 20) ≤ 20000 * (W + 1) ^ 6 := by
    have : loopModK * (W + 1) * (20 * W + 20) = 20000 * (W + 1) ^ 2 := by simp only [loopModK]; ring
    have : (W + 1) ^ 2 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_right hY (by omega)
    omega
  have hm2 := wt_list2_le (.nat m) (.nat 1)
  have : (Val.nat 1).wt ≤ 3 := by decide
  have := wt_nat_le m
  have wout' : (Val.list [colVal e c S.x, colVal e c S.y, coordsVal e S E, encGroup hsN,
      encGroup hsH, tmOnes m, .nat m, .nat q]).wt ≤ 30 * (320 * (W + 1) ^ 6) + 40 := wout
  unfold tmPrepC
  have hWe' : (Val.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0, rv]).wt = W := rfl
  rw [hWe'] at hca hcb
  generalize tmPrimC (pointwiseStabPrim hst) (400 * (W + 1) ^ 4) = Pc at hG ⊢
  omega

end Prep

end GI.Impl
