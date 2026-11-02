import Workspace.Impl.TermGlueLabQMath
import Workspace.Impl.LinNormal
import Workspace.Impl.LinIntSolverCost
import Workspace.Lang.Lib.LinIntTake

/-!
# The quotient program: moduli and coordinate map of `ℤ^c / ⟨rows of M⟩`

On `[r, c, M]` (`fullRankInput`), a relation matrix of full column rank, the
program `tmGLQF` makes one Hermite call (HermiteFullRank), keeps the top `c × c` block, makes
one Smith call (SmithNonsingular) on it, and reads off the diagonal. It returns `[d, V]`
(`TmGLQOut`): `x ↦ ((x V)_i mod d_i)_i` is the isomorphism `ℤ^c / ⟨rows of M⟩ ≃+ ∏_i ℤ/d_i`
(`tmGLQOutEquiv`). No other cited call is made.

Layout `tmGLQFuns b jh js` (9 functions): `0` the entry, `1` the Hermite call (primitive `jh`),
`2` take (3), `5` the Smith call (primitive `js`), `6` the diagonal loop (3).
-/

namespace GI.Impl

open GI.Cited GI.Lang Matrix

/-! ### The diagonal of a square matrix -/

/-- One step of the diagonal loop: add entry `(i, i)`. -/
def tmGLQDiagStep : Expr := .snoc (arg 2) (.get (.get (arg 0) (arg 1)) (arg 1))

/-- The diagonal loop module (3 functions). -/
def tmGLQDiagFuns (b : ℕ) : List Expr := loopFuns b (.length (.var 0)) .nil tmGLQDiagStep

/-- The cost of the diagonal loop. -/
def tmGLQDiagCost (W : ℕ) : ℕ := 100000 * (W + 1) ^ 3

private theorem tmGLQ_diag_take {c : ℕ} (D : Matrix (Fin c) (Fin c) ℤ) (i : ℕ) (hi : i < c) :
    ((List.finRange c).map fun j => encInt (D j j)).take (i + 1) =
      ((List.finRange c).map fun j => encInt (D j j)).take i ++ [encInt (D ⟨i, hi⟩ ⟨i, hi⟩)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hi)]
  simp

private theorem tmGLQ_entry_lt {c : ℕ} (D : Matrix (Fin c) (Fin c) ℤ) (j : Fin c) :
    (encInt (D j j)).wt < (encIntMatrix D).wt := by
  have h1 : (encInt (D j j)).wt < (linVecVal (D j)).wt := linVecEntryWt (D j) j
  have h2 : (linVecVal (D j)).wt < (encIntMatrix D).wt := by
    apply wt_le_wt_list
    simp only [List.mem_map, List.mem_finRange, true_and]
    exact ⟨j, rfl⟩
  omega

/-- **The diagonal.** On `encIntMatrix D` the loop returns `linVecVal (i ↦ D i i)`. -/
theorem tmGLQDiag_spec {P : Program} {b : ℕ} (hp : P.HasAt b (tmGLQDiagFuns b)) {c : ℕ}
    (D : Matrix (Fin c) (Fin c) ℤ) :
    FunDet P b (encIntMatrix D) (linVecVal (fun i => D i i))
      (tmGLQDiagCost (encIntMatrix D).wt) := by
  let a := encIntMatrix D
  let W := a.wt
  let ds := (List.finRange c).map fun j => encInt (D j j)
  have hrows : a = .list ((List.finRange c).map fun i => linVecVal (D i)) := rfl
  have hcW : c < W := by
    have := length_lt_wt_list ((List.finRange c).map fun i => linVecVal (D i))
    simpa [W, a, encIntMatrix] using this
  have hacc (i : ℕ) : (Val.list (ds.take i)).wt ≤ 2 * (W * W) + W + 4 := by
    have hl := linWtList (vs := ds.take i) (B := W) (by
      intro v hv
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hv)
      exact (tmGLQ_entry_lt D j).le)
    have hlen : (ds.take i).length ≤ W := by
      simp only [List.length_take, List.length_map, List.length_finRange, ds]; omega
    have : (ds.take i).length * W ≤ W * W := Nat.mul_le_mul_right _ hlen
    omega
  have dk : Det P [a] (.length (.var 0)) (.nat c) (W + 1 + c + 3) := by
    have := Det.length (Det.var' (P := P) (env := [a]) (i := 0) (v := a) rfl)
    rw [hrows] at this
    simpa [W, a, hrows] using this
  have hlp : P.HasAt b (loopFuns b (.length (.var 0)) .nil tmGLQDiagStep) := hp
  have hloop := loopBdd_spec hlp dk Det.nil (by omega)
    (Inv := fun i acc => acc = .list (ds.take i)) (M := 2 * (W * W) + W + 4)
    (D := fun _ => 1000 * (W + 2 * (W * W) + W + 4 + 1)) (by simp)
    (fun i acc _ he => he ▸ hacc i) (fun i acc hi he => ?_)
  · refine hloop.mono fun w cost hw => ⟨?_, ?_⟩
    · rw [hw.1]
      simp [ds, linVecVal]
    · have hc := hw.2
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, loopModK] at hc
      unfold tmGLQDiagCost
      change cost ≤ 100000 * (W + 1) ^ 3
      generalize hX : W * W = X at hc
      have hX3 : (W + 1) ^ 3 = W * X + 3 * X + 3 * W + 1 := by rw [← hX]; ring
      have h1 : c * (1000 * (W + 2 * X + W + 4 + 1)) ≤ W * (1000 * (W + 2 * X + W + 4 + 1)) :=
        Nat.mul_le_mul_right _ hcW.le
      have h2 : 1000 * (c + 1) * (W + c + (2 * X + W + 4) + 1) ≤
          1000 * (W + 1) * (W + W + (2 * X + W + 4) + 1) := by
        apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      have h3 : W * (1000 * (W + 2 * X + W + 4 + 1)) = 1000 * W * W + 2000 * (W * X) +
          1000 * W * W + 5000 * W := by ring
      have h4 : 1000 * (W + 1) * (W + W + (2 * X + W + 4) + 1) =
          3000 * W * W + 2000 * (W * X) + 8000 * W + 2000 * X + 5000 := by ring
      have h5 : W * W = X := hX
      rw [hX3]
      nlinarith
  · subst he
    have hi' : i < c := by simpa using hi
    have hrow : (List.map (fun i => linVecVal (D i)) (List.finRange c))[i]? =
        some (linVecVal (D ⟨i, hi'⟩)) := by simp [hi']
    have hent : ((List.finRange c).map fun j => encInt (D ⟨i, hi'⟩ j))[i]? =
        some (encInt (D ⟨i, hi'⟩ ⟨i, hi'⟩)) := by simp [hi']
    have darg := Det.arg' (P := P) (vs := [a, .nat i, .list (ds.take i)]) (rest := []) (j := 0) rfl
    rw [hrows] at darg
    have di := Det.arg' (P := P) (vs := [a, .nat i, .list (ds.take i)]) (rest := []) (j := 1) rfl
    have drow := Det.get' darg di hrow
    have dx := Det.get' drow di hent
    have da := Det.arg' (P := P) (vs := [a, .nat i, .list (ds.take i)]) (rest := []) (j := 2) rfl
    have dres := Det.snoc da dx
    refine dres.post fun cost hc => ⟨?_, ?_⟩
    · show Val.list (ds.take i ++ [encInt (D ⟨i, hi'⟩ ⟨i, hi'⟩)]) = Val.list (ds.take (i + 1))
      rw [tmGLQ_diag_take D i hi']
    · have wi := wt_nat_le i
      have ws := wt_list3_le a (.nat i) (.list (ds.take i))
      have wa := hacc i
      have wo := hacc (i + 1)
      rw [tmGLQ_diag_take D i hi'] at wo
      have we := tmGLQ_entry_lt D ⟨i, hi'⟩
      have wr : (linVecVal (D ⟨i, hi'⟩)).wt < W := by
        apply wt_le_wt_list
        simp only [List.mem_map, List.mem_finRange, true_and]
        exact ⟨⟨i, hi'⟩, rfl⟩
      have hpW : (Val.list ((List.finRange c).map fun i => linVecVal (D i))).wt = W := rfl
      have hfg : (Val.list [a, .nat i, .list (ds.take i)]).wt = (Val.list
          [Val.list ((List.finRange c).map fun i => linVecVal (D i)), .nat i,
            .list (ds.take i)]).wt := rfl
      have hoW : (encIntMatrix D).wt = W := rfl
      have hjp : (Val.list (ds.take i ++ [encInt (D ⟨i, hi'⟩ ⟨i, hi'⟩)])).wt = (Val.list
          (((List.finRange c).map fun j => encInt (D j j)).take i ++
            [encInt (D ⟨i, hi'⟩ ⟨i, hi'⟩)])).wt := rfl
      beta_reduce at hc ⊢
      generalize W * W = X at *
      omega

/-! ### The program -/

/-- **The quotient program** on `[r, c, M]`: Hermite, take the top `c` rows, Smith, diagonal;
return `[d, V]`. -/
def tmGLQF (hermite take smith diag : ℕ) : Expr :=
  .letE (.call hermite (.var 0))
    (.letE (.call take (mk2 (arg 1) (.get (.var 1) (.nat 1))))
      (.letE (.call smith (mk2 (arg 1) (.var 2)))
        (.letE (.call diag (.get (.var 3) (.nat 1)))
          (mk2 (.var 4) (.get (.var 3) (.nat 2))))))

/-- The quotient module at base `b`, with HermiteFullRank at primitive `jh` and
SmithNonsingular at primitive `js` (9 functions). -/
def tmGLQFuns (b jh js : ℕ) : List Expr :=
  [tmGLQF (b + 1) (b + 2) (b + 5) (b + 6), linHermiteF jh] ++ linTakeFuns (b + 2) ++
    [linSmithF js] ++ tmGLQDiagFuns (b + 6)

theorem length_tmGLQFuns (b jh js : ℕ) : (tmGLQFuns b jh js).length = 9 := rfl

/-- The Hermite budget in the input weight (as for the row solver). -/
noncomputable def tmGLQHW (hH : HermiteFullRank) (W : ℕ) : ℕ := linRowSolverHermiteBudget hH W

/-- The weight budget of the Smith input. -/
noncomputable def tmGLQSW (hH : HermiteFullRank) (W : ℕ) : ℕ := 10 * (W + tmGLQHW hH W + 1)

/-- The weight budget of the Smith output. -/
noncomputable def tmGLQSB (hS : SmithNonsingular) (hH : HermiteFullRank) (W : ℕ) : ℕ :=
  6 * linMatrixWt W W (tmGLQSW hH W ^ linSmithDegree hS) + 7

/-- **The cost budget of the quotient program**, in the input weight `W`. -/
noncomputable def tmGLQBudget (hH : HermiteFullRank) (hS : SmithNonsingular) (W : ℕ) : ℕ :=
  1000 * (W + (linHermitePrim hH).boundSize W + tmGLQHW hH W +
    linTakeCost (tmGLQSW hH W) + (linSmithPrim hS).boundSize (tmGLQSW hH W) + tmGLQSW hH W +
    tmGLQSB hS hH W + tmGLQDiagCost (tmGLQSB hS hH W) + 1)

theorem tmGLQBudget_poly (hH : HermiteFullRank) (hS : SmithNonsingular) :
    PBU (fun _ W _ => tmGLQBudget hH hS W) := by
  unfold tmGLQBudget tmGLQSB tmGLQSW tmGLQHW linRowSolverHermiteBudget linMatrixWt
    tmGLQDiagCost linTakeCost Prim.boundSize
  norm_poly

set_option maxHeartbeats 2000000 in
/-- **The quotient program.** On `fullRankInput I` it returns `[d, V]` with `TmGLQOut I.A`,
at cost at most `tmGLQBudget` of the input weight. -/
theorem tmGLQ_spec (hH : HermiteFullRank) (hS : SmithNonsingular) {P : Program} {b jh js : ℕ}
    (hp : P.HasAt b (tmGLQFuns b jh js)) (hjh : P.prims[jh]? = some (linHermitePrim hH))
    (hjs : P.prims[js]? = some (linSmithPrim hS)) (I : FullRankInst) :
    FunAll P b (fullRankInput I) (fun out cost =>
      TmGLQOut I.A out ∧ cost ≤ tmGLQBudget hH hS (fullRankInput I).wt) := by
  let a := fullRankInput I
  let W := a.wt
  have hf : P.funs[b]? = some (tmGLQF (b + 1) (b + 2) (b + 5) (b + 6)) :=
    (hp.block 0 (gs := [tmGLQF (b + 1) (b + 2) (b + 5) (b + 6)]) rfl).single
  have hh : P.funs[b + 1]? = some (linHermiteF jh) := (hp.block 1 (gs := [linHermiteF jh]) rfl).single
  have ht : P.HasAt (b + 2) (linTakeFuns (b + 2)) := hp.block 2 rfl
  have hsm : P.funs[b + 5]? = some (linSmithF js) := (hp.block 5 (gs := [linSmithF js]) rfl).single
  have hd : P.HasAt (b + 6) (tmGLQDiagFuns (b + 6)) := hp.block 6 rfl
  -- sizes of the input
  have wm : (encIntMatrix I.A).wt < W := wt_le_wt_list (by simp)
  have hr : I.r ≤ W := by
    have hl := length_lt_wt_list ((List.finRange I.r).map fun i => linVecVal (I.A i))
    simp only [List.length_map, List.length_finRange] at hl
    exact (hl.trans wm).le
  have hc : I.c ≤ W := I.c_le.trans hr
  have hs : (fullRankInput I).cells.length ≤ W := (fullRankInput I).size_le_wt
  have hbits : (fullRankInput I).cells.length ^ linHermiteDegree hH ≤ W ^ linHermiteDegree hH :=
    Nat.pow_le_pow_left hs _
  have hmat : linMatrixWt I.r I.r ((fullRankInput I).cells.length ^ linHermiteDegree hH) ≤
      linMatrixWt W W (W ^ linHermiteDegree hH) := by unfold linMatrixWt; gcongr
  have hmat' : linMatrixWt I.r I.c ((fullRankInput I).cells.length ^ linHermiteDegree hH) ≤
      linMatrixWt W W (W ^ linHermiteDegree hH) := by unfold linMatrixWt; gcongr
  have hHW : linHermiteWt (linHermiteDegree hH) I ≤ tmGLQHW hH W := by
    unfold linHermiteWt tmGLQHW linRowSolverHermiteBudget
    omega
  have hpH := (linHermitePrim hH).bound_le hs
  -- the Hermite call
  have dh : EvalAll P [a] (.call (b + 1) (.var 0)) (fun v cost =>
      linHermiteOut (linHermiteDegree hH) I v ∧
        cost ≤ 10 * (W + (linHermitePrim hH).boundSize W + tmGLQHW hH W + 1)) := by
    apply EvalAll.call_funAll (Det.var' (P := P) (env := [a]) (i := 0) rfl)
    intro v ca hv
    obtain ⟨rfl, hca⟩ := hv
    refine (linHermite_spec hH hh hjh I).mono fun out cost ho => ⟨ho.1, ?_⟩
    have wo := linHermiteOut_wt ho.1
    have hc2 := ho.2
    unfold linHermiteCost at hc2
    simp only [W, a] at *
    omega
  apply FunAll.intro hf
  apply EvalAll.letE dh
  intro v cv hv
  obtain ⟨U, H, rfl, hU, hUM, hHerm, hUB, hHB⟩ := hv.1
  have hcv := hv.2
  have wUH : (Val.list [encIntMatrix U, encIntMatrix H]).wt ≤ tmGLQHW hH W :=
    (linHermiteOut_wt (d := linHermiteDegree hH) (I := I)
      ⟨U, H, rfl, hU, hUM, hHerm, hUB, hHB⟩).trans hHW
  have wH : (encIntMatrix H).wt < (Val.list [encIntMatrix U, encIntMatrix H]).wt :=
    wt_le_wt_list (by simp)
  -- take the top block
  let Hb := linHermiteBlock I.c_le H
  have hHb : encIntMatrix Hb = .list (((List.finRange I.r).map fun i => linVecVal (H i)).take I.c) := by
    rw [linTakeFinMap I.c_le]
    rfl
  have hlenH : I.c ≤ ((List.finRange I.r).map fun i => linVecVal (H i)).length := by
    simpa using I.c_le
  have tk := linTake_spec ht ((List.finRange I.r).map fun i => linVecVal (H i)) I.c hlenH
  rw [← hHb] at tk
  have dc := Det.arg' (P := P) (vs := [.nat I.r, .nat I.c, encIntMatrix I.A])
    (rest := [.list [encIntMatrix U, encIntMatrix H]]) (j := 1) rfl
  have dHv := Det.get' (Det.var' (P := P) (env := [a, .list [encIntMatrix U, encIntMatrix H]])
    (i := 1) rfl) (Det.nat 1) (show [encIntMatrix U, encIntMatrix H][1]? = some (encIntMatrix H) from rfl)
  have dtk := Det.call (Det.mk2 dc dHv) tk
  apply EvalAll.letE dtk
  -- the Smith call on the block
  let I' : NonsingularInst := ⟨I.c, I.c_pos, Hb, linHermiteBlock_det_ne I.c_le H hHerm⟩
  have wHb : (encIntMatrix Hb).wt ≤ (encIntMatrix H).wt := by
    rw [hHb]
    exact wt_list_sublist (List.take_sublist _ _)
  have wtkin := wt_list2_le (.nat I.c) (encIntMatrix H)
  have wc := wt_nat_le I.c
  have wtk : (Val.list [.nat I.c, encIntMatrix H]).wt ≤ tmGLQSW hH W := by
    unfold tmGLQSW; omega
  have wsin : (nonsingularInput I').wt ≤ tmGLQSW hH W := by
    have := wt_list2_le (.nat I.c) (encIntMatrix Hb)
    show (Val.list [.nat I.c, encIntMatrix Hb]).wt ≤ _
    unfold tmGLQSW; omega
  have hs' : (nonsingularInput I').cells.length ≤ tmGLQSW hH W :=
    (nonsingularInput I').size_le_wt.trans wsin
  have hpS := (linSmithPrim hS).bound_le hs'
  have hSW : linSmithWt (linSmithDegree hS) I' ≤ tmGLQSB hS hH W := by
    unfold linSmithWt tmGLQSB
    have : linMatrixWt I'.n I'.n ((nonsingularInput I').cells.length ^ linSmithDegree hS) ≤
        linMatrixWt W W (tmGLQSW hH W ^ linSmithDegree hS) := by
      unfold linMatrixWt
      have h1 : I'.n ≤ W := hc
      have h2 := Nat.pow_le_pow_left hs' (linSmithDegree hS)
      gcongr
    omega
  have dsm : EvalAll P [a, .list [encIntMatrix U, encIntMatrix H], encIntMatrix Hb]
      (.call (b + 5) (mk2 (arg 1) (.var 2))) (fun v cost =>
        linSmithOut (linSmithDegree hS) I' v ∧
          cost ≤ 10 * (W + tmGLQSW hH W + (linSmithPrim hS).boundSize (tmGLQSW hH W) +
            tmGLQSB hS hH W + 1)) := by
    have dc' := Det.arg' (P := P) (vs := [.nat I.r, .nat I.c, encIntMatrix I.A])
      (rest := [.list [encIntMatrix U, encIntMatrix H], encIntMatrix Hb]) (j := 1) rfl
    have db := Det.var' (P := P) (env := [a, .list [encIntMatrix U, encIntMatrix H],
      encIntMatrix Hb]) (i := 2) rfl
    apply EvalAll.call_funAll (Det.mk2 dc' db)
    intro v ca hv
    obtain ⟨rfl, hca⟩ := hv
    refine (linSmith_spec hS hsm hjs I').mono fun out cost ho => ⟨ho.1, ?_⟩
    have wo := linSmithOut_wt ho.1
    have hc3 : cost ≤ (linSmithPrim hS).bound (nonsingularInput I') +
        (Val.list [.nat I.c, encIntMatrix Hb]).wt + linSmithWt (linSmithDegree hS) I' + 2 := by
      have := ho.2; unfold linSmithCost at this
      have e : (nonsingularInput I').wt = (Val.list [.nat I.c, encIntMatrix Hb]).wt := rfl
      omega
    have w2 := wt_list2_le (.nat I.c) (encIntMatrix Hb)
    change (Val.list [.nat I.c, encIntMatrix Hb]).wt ≤ _ at wsin
    have eW : (Val.list [.nat I.r, .nat I.c, encIntMatrix I.A]).wt = W := rfl
    have hSWd : tmGLQSW hH W = 10 * (W + tmGLQHW hH W + 1) := rfl
    clear ho
    omega
  intro vt ct hvt
  obtain ⟨rfl, hct⟩ := hvt
  apply EvalAll.letE dsm
  intro vs cs hvs
  obtain ⟨U', V, D, rfl, hU', hV, hS', hD, hUB', hDB, hVB⟩ := hvs.1
  have hcs := hvs.2
  have wSo : (Val.list [encIntMatrix U', encIntMatrix D, encIntMatrix V]).wt ≤ tmGLQSB hS hH W :=
    (linSmithOut_wt (d := linSmithDegree hS) (I := I')
      ⟨U', V, D, rfl, hU', hV, hS', hD, hUB', hDB, hVB⟩).trans hSW
  have wD : (encIntMatrix D).wt < (Val.list [encIntMatrix U', encIntMatrix D, encIntMatrix V]).wt :=
    wt_le_wt_list (by simp)
  have wV : (encIntMatrix V).wt < (Val.list [encIntMatrix U', encIntMatrix D, encIntMatrix V]).wt :=
    wt_le_wt_list (by simp)
  -- the diagonal
  have dg := (tmGLQDiag_spec hd D).mono (c' := tmGLQDiagCost (tmGLQSB hS hH W)) (by
    unfold tmGLQDiagCost
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
  have dS := Det.var' (P := P) (env := [a, .list [encIntMatrix U, encIntMatrix H], encIntMatrix Hb,
    .list [encIntMatrix U', encIntMatrix D, encIntMatrix V]]) (i := 3) rfl
  have dDv := Det.get' dS (Det.nat 1)
    (show [encIntMatrix U', encIntMatrix D, encIntMatrix V][1]? = some (encIntMatrix D) from rfl)
  have ddg := Det.call dDv dg
  apply EvalAll.letE ddg
  intro vd cd hvd
  obtain ⟨rfl, hcd⟩ := hvd
  -- the output
  have wdg := dg.wt_lt
  have dS' := Det.var' (P := P) (env := [a, .list [encIntMatrix U, encIntMatrix H], encIntMatrix Hb,
    .list [encIntMatrix U', encIntMatrix D, encIntMatrix V], linVecVal fun i => D i i]) (i := 3) rfl
  have dVv := Det.get' dS' (Det.nat 2)
    (show [encIntMatrix U', encIntMatrix D, encIntMatrix V][2]? = some (encIntMatrix V) from rfl)
  have dd := Det.var' (P := P) (env := [a, .list [encIntMatrix U, encIntMatrix H], encIntMatrix Hb,
    .list [encIntMatrix U', encIntMatrix D, encIntMatrix V], linVecVal fun i => D i i]) (i := 4) rfl
  have dout := Det.mk2 dd dVv
  refine dout.post fun cost hcost => ⟨⟨V, D, rfl, hV, fun i =>
    tmGLQ_diag_pos I.c_le H hHerm U' V D hU' hV hS' hD i,
    tmGLQ_rel_iff I.c_le I.A H U hU hUM hHerm U' V D hU' hV hS' hD⟩, ?_⟩
  have w2 := wt_list2_le (linVecVal fun i => D i i) (encIntMatrix V)
  have hn1 : (Val.nat 1).wt = 3 := rfl
  have hn2 := wt_nat_le 2
  have htk := tk.wt_lt
  have hcl : linTakeCost (Val.list [.nat I.c,
      .list ((List.finRange I.r).map fun i => linVecVal (H i))]).wt ≤ linTakeCost (tmGLQSW hH W) :=
    linTakeCost_mono wtk
  have eW : (Val.list [.nat I.r, .nat I.c, encIntMatrix I.A]).wt = W := rfl
  change _ ≤ tmGLQBudget hH hS W
  unfold tmGLQBudget
  clear dh dtk dsm ddg dout dS dS' dVv dd dDv dc dHv tk dg
  generalize tmGLQHW hH W = A1 at *
  generalize tmGLQSW hH W = A2 at *
  generalize tmGLQSB hS hH W = A3 at *
  generalize linTakeCost A2 = A4 at *
  generalize tmGLQDiagCost A3 = A5 at *
  generalize (linHermitePrim hH).boundSize W = A6 at *
  generalize (linSmithPrim hS).boundSize A2 = A7 at *
  simp only [W, a] at *
  omega

end GI.Impl
