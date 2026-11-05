module

public import Workspace.Impl.AggRectCertC

@[expose] public section

/-!
# The certificate search as a program: one candidate

`rcCandF` runs the test `rcCand` of `AggRectCertMath.lean` on `[[D, x, n], t]`, where `D` holds a
square table `ds` of size `n`. It reads the points `a, b, u` of `t`, the colors `v_L, v_R, v_E`,
the two sides (two `filter`s of `rcEqT`), the matrix (a `map` of `rcBRowF`), and calls the
conditions `rcCondF`. `rc_cand_spec`: the result is `boolVal (rcCand ds x n t)` at a cost
`10²⁴ (W + 1)¹²` for a weight bound `W` of the input.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)
open GI.Machine (BinOp)

/-- **Filter over a list of numbers.** -/
theorem rc_filterN {P : Program} {b p : ℕ} (h : P.HasAt b (filterFuns b p)) {c : Val}
    {xs : List ℕ} {t : ℕ → Bool} {B : ℕ} (hp : ∀ x ∈ xs, FunDet P p (.list [c, .nat x]) (boolVal (t x)) B) :
    FunDet P b (.list [c, natList xs]) (natList (xs.filter t))
      (xs.length * B + loopModK * (xs.length + 1) * ((Val.list [c, natList xs]).wt + xs.length +
        (natList (xs.filter t)).wt + 1)) := by
  have hf := filter_spec h (c := c) (xs := xs.map Val.nat) (q := fun v => t (rcNatOf v))
    (B := fun _ => B) (fun v hv => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
      exact hp x hx)
  have e : (xs.map Val.nat).filter (fun v => t (rcNatOf v)) = (xs.filter t).map Val.nat := by
    rw [List.filter_map]; rfl
  refine hf.mono fun w cost hw => ⟨by rw [hw.1, e]; rfl, ?_⟩
  have h2 := hw.2
  rw [hw.1, e] at h2
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map] at h2
  exact h2

/-- A cost bound may be raised. -/
theorem rc_fd_mono {P : Program} {f : ℕ} {v w : Val} {c c' : ℕ} (h : FunDet P f v w c)
    (hc : c ≤ c') : FunDet P f v w c' := h.mono hc

/-- The sides are sublists of `range n`. -/
theorem rc_wt_side {xs : List ℕ} {n W : ℕ} (hs : xs.Sublist (List.range n)) (hn : n ≤ W) :
    (natList xs).wt ≤ 5 * (W + 1) ^ 2 :=
  rc_wt_natList (fun x hx => by have := List.mem_range.1 (hs.subset hx); omega)
    (by have := hs.length_le; simp at this; omega)

/-- The expressions of the input `[[D, x, n], t]`. -/
def rcED : Expr := .get (arg 0) (.nat 0)
def rcEI : Expr := .get (arg 0) (.nat 1)
def rcEN : Expr := .get (arg 0) (.nat 2)

/-- The body after the points `a, b, u` (variables `1, 2, 3`). -/
def rcCandBody (flt rng mb cond : ℕ) : Expr :=
  .letE (.get rcED rcEI)
  (.letE (.get (.var 4) (.var 1))
  (.letE (.get (.var 4) (.var 2))
  (.letE (.get (.get rcED (.var 3)) (.var 2))
  (.letE (.call flt (mk2 (mk2 (.var 4) (.var 5)) (.call rng rcEN)))
  (.letE (.call flt (mk2 (mk2 (.var 4) (.var 6)) (.call rng rcEN)))
  (.letE (.call mb (mk2 (mk3 rcED (.var 7) (.var 9)) (.var 8)))
  (.call cond (.snoc (.snoc (.snoc (.snoc (mk4 rcEN (.var 5) (.var 6) (.get (.var 4) rcEI))
    (.get (.var 4) (.var 3))) (.var 8)) (.var 9)) (.var 10)))))))))

/-- **One candidate** on `[[D, x, n], t]` (`flt`: filter of `rcEqT`; `rng`: range; `mb`: map of
`rcBRowF`; `cond`: `rcCondF`). -/
def rcCandF (flt rng mb cond : ℕ) : Expr :=
  .letE (.arith .div (arg 1) (.arith .mul rcEN rcEN))
  (.letE (.arith .mod (.arith .div (arg 1) rcEN) rcEN)
  (.letE (.arith .mod (arg 1) rcEN) (rcCandBody flt rng mb cond)))

/-- The functions the candidate test calls. -/
structure RcCandOk (P : Program) (cf flt et rng mb br mbe cond mc mcd al cnt cd mg gt tw fe en : ℕ) :
    Prop where
  hcf : P.funs[cf]? = some (rcCandF flt rng mb cond)
  hflt : P.HasAt flt (filterFuns flt et)
  het : P.funs[et]? = some rcEqT
  hrng : P.HasAt rng (rangeFuns rng)
  hmb : P.HasAt mb (mapFuns mb br)
  hbr : P.funs[br]? = some (rcBRowF mbe)
  hmbe : P.HasAt mbe (mapFuns mbe et)
  hcond : P.funs[cond]? = some (rcCondF mc mcd rng al cnt)
  hmc : P.HasAt mc (mapFuns mc cnt)
  hcnt : P.HasAt cnt (countFuns cnt)
  hmcd : P.HasAt mcd (mapFuns mcd cd)
  hcd : P.funs[cd]? = some (rcColDegF cnt mg)
  hmg : P.HasAt mg (mapFuns mg gt)
  hgt : P.funs[gt]? = some rcGetT
  hal : P.HasAt al (allFuns al tw)
  htw : P.funs[tw]? = some (rcTwT fe)
  hfe : P.HasAt fe (filterFuns fe en)
  hen : P.HasAt en (eqNatsFuns en)

/-- The input of one candidate. -/
def rcCandIn (ds : List (List ℕ)) (x n t : ℕ) : Val :=
  .list [.list [rcTV ds, .nat x, .nat n], .nat t]

theorem rc_mul_lin {n W c d : ℕ} (hn : n ≤ W + 1) : n * (c * W + d) ≤ (c + d) * (W + 1) ^ 2 := by
  calc n * (c * W + d) ≤ (W + 1) * ((c + d) * (W + 1)) :=
        Nat.mul_le_mul hn (by nlinarith)
    _ = (c + d) * (W + 1) ^ 2 := by ring

theorem rc_pow_le {W i j : ℕ} (h : i ≤ j) : (W + 1) ^ i ≤ (W + 1) ^ j :=
  Nat.pow_le_pow_right (by omega) h

set_option maxHeartbeats 8000000 in
/-- **One candidate as a program.** -/
theorem rc_cand_spec {P : Program} {cf flt et rng mb br mbe cond mc mcd al cnt cd mg gt tw fe en : ℕ}
    (hP : RcCandOk P cf flt et rng mb br mbe cond mc mcd al cnt cd mg gt tw fe en)
    (ds : List (List ℕ)) (x n t : ℕ) (hds : ds.length = n) (hrow : ∀ row ∈ ds, row.length = n)
    (hx : x < n) (ht : t < n * n * n) {W : ℕ} (hW : (rcCandIn ds x n t).wt ≤ W) (h20 : 20 ≤ W) :
    FunDet P cf (rcCandIn ds x n t) (boolVal (rcCand ds x n t)) (10 ^ 24 * (W + 1) ^ 12) := by
  -- sizes
  have hA0 : (Val.list [rcTV ds, .nat x, .nat n]).wt < (rcCandIn ds x n t).wt :=
    wt_le_wt_list (by simp)
  have hAt : (Val.nat t).wt < (rcCandIn ds x n t).wt := wt_le_wt_list (by simp)
  have hDw : (rcTV ds).wt < (Val.list [rcTV ds, .nat x, .nat n]).wt := wt_le_wt_list (by simp)
  have hxw : (Val.nat x).wt < (Val.list [rcTV ds, .nat x, .nat n]).wt := wt_le_wt_list (by simp)
  have hnw : (Val.nat n).wt < (Val.list [rcTV ds, .nat x, .nat n]).wt := wt_le_wt_list (by simp)
  have hnW : n < W := by have := rc_len_lt_tv ds; omega
  set a := rcPa n t with ha_def
  set b := rcPb n t with hb_def
  set u := rcPu n t with hu_def
  have ha : a < n := rc_pa_lt ht
  have hb : b < n := rc_pb_lt ht
  have hu : u < n := rc_pu_lt ht
  set X := ds.getD x [] with hX_def
  have hXl : X.length = n := by
    rw [hX_def, List.getD_eq_getElem _ _ (by omega)]; exact hrow _ (List.getElem_mem _)
  have hXw : (natList X).wt < (rcTV ds).wt := rc_wt_row_lt (by omega)
  set U := ds.getD u [] with hU_def
  have hUl : U.length = n := by
    rw [hU_def, List.getD_eq_getElem _ _ (by omega)]; exact hrow _ (List.getElem_mem _)
  have hUw : (natList U).wt < (rcTV ds).wt := rc_wt_row_lt (by omega)
  set vL := X.getD a 0 with hvL
  set vR := X.getD b 0 with hvR
  set vE := U.getD b 0 with hvE
  have hvLw : (Val.nat vL).wt < (natList X).wt := rc_wt_nat_lt (by omega)
  have hvRw : (Val.nat vR).wt < (natList X).wt := rc_wt_nat_lt (by omega)
  have hvEw : (Val.nat vE).wt < (natList U).wt := rc_wt_nat_lt (by omega)
  have hv0w : (Val.nat (X.getD x 0)).wt < (natList X).wt := rc_wt_nat_lt (by omega)
  have hvUw : (Val.nat (X.getD u 0)).wt < (natList X).wt := rc_wt_nat_lt (by omega)
  have hDW : (rcTV ds).wt < W := by omega
  have hXW : (natList X).wt < W := by omega
  have hUW : (natList U).wt < W := by omega
  have htW : (Val.nat t).wt < W := by omega
  set wl := (List.range n).filter fun k => decide (X.getD k 0 = vL) with hwl
  set rl := (List.range n).filter fun k => decide (X.getD k 0 = vR) with hrl
  set bm := wl.map (rcBits ds vE rl) with hbm
  have hwls : wl.Sublist (List.range n) := List.filter_sublist
  have hrls : rl.Sublist (List.range n) := List.filter_sublist
  have hwlw := rc_wt_side hwls hnW.le
  have hrlw := rc_wt_side hrls hnW.le
  have hrnw : (natList (List.range n)).wt ≤ 5 * (W + 1) ^ 2 := rc_wt_side (List.Sublist.refl _) hnW.le
  have hwll : wl.length ≤ n := by have := hwls.length_le; simpa using this
  have hrll : rl.length ≤ n := by have := hrls.length_le; simpa using this
  have hbmrow : ∀ row ∈ bm, (natList row).wt ≤ 5 * (W + 1) ^ 2 := by
    intro row hr
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
    refine rc_wt_natList (fun y hy => ?_) (by simp [rcBits]; omega)
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hy
    split <;> omega
  have hW2 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hW3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := rc_pow_le (by omega)
  have hbmw : (rcTV bm).wt ≤ 20 * (W + 1) ^ 3 := by
    have := rc_wt_list (vs := bm.map natList) (c := 5 * (W + 1) ^ 2) (L := W + 1) (by
      intro v hv
      obtain ⟨row, hr, rfl⟩ := List.mem_map.1 hv
      exact hbmrow row hr) (by simp [bm]; omega)
    have e : (Val.list (bm.map natList)).wt = (rcTV bm).wt := rfl
    rw [e] at this
    nlinarith
  set M := 400 * (W + 1) ^ 3 with hM
  have hCw : (rcCondIn n vL vR (X.getD x 0) (X.getD u 0) wl rl bm).wt ≤ M := by
    have := rc_wt_list (vs := [.nat n, .nat vL, .nat vR, .nat (X.getD x 0), .nat (X.getD u 0),
      natList wl, natList rl, rcTV bm]) (c := 20 * (W + 1) ^ 3) (L := 8) (by
      intro v hv
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega) (by simp)
    exact this.trans (by omega)
  set Z := 1000 * (W + 1) ^ 3 with hZ
  set A := rcCandIn ds x n t with hA_def
  have hnn : n * n ≤ (W + 1) ^ 2 := by nlinarith
  have hAe : (Val.list [.list [rcTV ds, .nat x, .nat n], .nat t]).wt = A.wt := rfl
  -- leaves
  have g0 : ∀ rest, StDC P (A :: rest) (arg 0) (.list [rcTV ds, .nat x, .nat n]) 3 0 Z :=
    fun rest => StDC.arg (vs := [.list [rcTV ds, .nat x, .nat n], .nat t]) rfl (by omega)
      (by omega) (by omega)
  have g1 : ∀ rest, StDC P (A :: rest) (arg 1) (.nat t) 3 0 Z :=
    fun rest => StDC.arg (vs := [.list [rcTV ds, .nat x, .nat n], .nat t]) rfl (by omega)
      (by omega) (by omega)
  have gD : ∀ rest, StDC P (A :: rest) rcED (rcTV ds) 5 0 Z := by
    intro rest
    have h := StDC.get (g0 rest) (StDC.nat (env := A :: rest) 0 (W := Z) (by omega)) (v := rcTV ds) rfl (by omega)
    exact h
  have gI : ∀ rest, StDC P (A :: rest) rcEI (.nat x) 5 0 Z := by
    intro rest
    have h := StDC.get (g0 rest) (StDC.nat (env := A :: rest) 1 (W := Z) (by omega)) (v := .nat x) rfl (by omega)
    exact h
  have gN : ∀ rest, StDC P (A :: rest) rcEN (.nat n) 5 0 Z := by
    intro rest
    have h := StDC.get (g0 rest) (StDC.nat (env := A :: rest) 2 (W := Z) (by omega)) (v := .nat n) rfl (by omega)
    exact h
  -- the points
  have gpa := StDC.arith' (op := .div) (g1 []) (StDC.arith' (op := .mul) (gN []) (gN []) rfl
    (by simp only [BinOp.eval]; omega)) (show BinOp.eval .div t (n * n) = a from rfl) (by omega)
  have gpb := StDC.arith' (op := .mod) (StDC.arith' (op := .div) (g1 [.nat a]) (gN [.nat a]) rfl
    (by simp only [BinOp.eval]; have := Nat.div_le_self t n; nlinarith))
    (gN [.nat a]) (show BinOp.eval .mod (t / n) n = b from rfl) (by omega)
  have gpu := StDC.arith' (op := .mod) (g1 [.nat a, .nat b]) (gN [.nat a, .nat b])
    (show BinOp.eval .mod t n = u from rfl) (by omega)
  have hW12 : ∀ i ≤ 12, (W + 1) ^ i ≤ (W + 1) ^ 12 := fun i hi => rc_pow_le hi
  have hW1 : W + 1 ≤ (W + 1) ^ 12 := by simpa using hW12 1 (by omega)
  -- the calls, with clean costs
  have frng : FunDet P rng (.nat n) (natList (List.range n)) (10 ^ 4 * (W + 1) ^ 12) :=
    rc_fd_mono (st_range_det hP.hrng n) (by
      have : (n + 1) ^ 3 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      have := hW12 3 (by omega)
      norm_num; omega)
  have fflt : ∀ v : ℕ, (Val.nat v).wt < (natList X).wt →
      FunDet P flt (.list [.list [natList X, .nat v], natList (List.range n)])
        (natList ((List.range n).filter fun k => decide (X.getD k 0 = v))) (10 ^ 5 * (W + 1) ^ 12) := by
    intro v hv
    have hf := rc_filterN hP.hflt (c := .list [natList X, .nat v]) (xs := List.range n)
      (t := fun k => decide (X.getD k 0 = v)) (B := 20 * (10 * W + 23)) (fun k hk => by
        have hk' := List.mem_range.1 hk
        refine rc_eqT_spec hP.het (by omega) (W := 10 * W + 22) ?_ (by omega)
        have := wt_list2_le (.list [natList X, .nat v]) (.nat k)
        have := wt_list2_le (natList X) (.nat v)
        have := wt_nat_le k
        omega)
    refine rc_fd_mono hf ?_
    have h1 := wt_list2_le (.list [natList X, .nat v]) (natList (List.range n))
    have h2 := wt_list2_le (natList X) (.nat v)
    have hout := rc_wt_side (xs := (List.range n).filter fun k => decide (X.getD k 0 = v))
      List.filter_sublist hnW.le
    simp only [List.length_range]
    have e1 : n * (20 * (10 * W + 23)) ≤ 1000 * (W + 1) ^ 2 := by
      have := rc_mul_lin (c := 200) (d := 460) (show n ≤ W + 1 by omega)
      have e : 20 * (10 * W + 23) = 200 * W + 460 := by ring
      rw [e]; omega
    have e2 : loopModK * (n + 1) * ((Val.list [.list [natList X, .nat v],
        natList (List.range n)]).wt + n + (natList ((List.range n).filter fun k =>
          decide (X.getD k 0 = v))).wt + 1) ≤ 1000 * (W + 1) * (50 * (W + 1) ^ 2) := by
      unfold loopModK
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by linarith)
    have e3 : 1000 * (W + 1) * (50 * (W + 1) ^ 2) = 50000 * (W + 1) ^ 3 := by ring
    have := hW12 2 (by omega)
    have := hW12 3 (by omega)
    linarith
  have hwlr : ∀ w ∈ wl, w < n := fun w hw => List.mem_range.1 (hwls.subset hw)
  have hrlr : ∀ r ∈ rl, r < n := fun r hr => List.mem_range.1 (hrls.subset hr)
  have hc3 : (Val.list [rcTV ds, .nat vE, natList rl]).wt ≤ 20 * (W + 1) ^ 2 := by
    have := wt_list3_le (rcTV ds) (.nat vE) (natList rl); omega
  have fmb : FunDet P mb (.list [.list [rcTV ds, .nat vE, natList rl], natList wl]) (rcTV bm)
      (10 ^ 12 * (W + 1) ^ 12) := by
    have hf := rc_mapN hP.hmb (c := .list [rcTV ds, .nat vE, natList rl]) (xs := wl)
      (g := fun w => natList (rcBits ds vE rl w)) (B := 10 ^ 6 * (50 * (W + 1) ^ 2 + 1) ^ 3)
      (fun w hw => by
        have hw' := hwlr w hw
        refine rc_bRow_spec hP.hbr hP.hmbe hP.het ds vE rl w (by omega) (fun r hr => by
          have := hrlr r hr
          rw [List.getD_eq_getElem _ _ (by omega), hrow _ (List.getElem_mem _)]; exact this)
          (W := 50 * (W + 1) ^ 2) ?_ (by linarith)
        have := wt_list2_le (.list [rcTV ds, .nat vE, natList rl]) (.nat w)
        have := wt_nat_le w
        linarith)
    have e : Val.list (wl.map fun w => natList (rcBits ds vE rl w)) = rcTV bm := by
      show _ = Val.list (bm.map natList)
      rw [hbm, List.map_map]; rfl
    rw [e] at hf
    refine rc_fd_mono hf ?_
    have h1 := wt_list2_le (.list [rcTV ds, .nat vE, natList rl]) (natList wl)
    have hp : (50 * (W + 1) ^ 2 + 1) ^ 3 ≤ 132651 * (W + 1) ^ 6 := by
      calc (50 * (W + 1) ^ 2 + 1) ^ 3 ≤ (51 * (W + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        _ = 132651 * (W + 1) ^ 6 := by ring
    have e1 : wl.length * (10 ^ 6 * (50 * (W + 1) ^ 2 + 1) ^ 3) ≤
        (W + 1) * (10 ^ 6 * (132651 * (W + 1) ^ 6)) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hp)
    have e1' : (W + 1) * (10 ^ 6 * (132651 * (W + 1) ^ 6)) = 132651 * 10 ^ 6 * (W + 1) ^ 7 := by ring
    have e2 : mapK * (wl.length + 1) * ((Val.list [.list [rcTV ds, .nat vE, natList rl],
        natList wl]).wt + (rcTV bm).wt + 1) ≤ 1000 * (W + 1) * (100 * (W + 1) ^ 3) := by
      unfold mapK
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by linarith)
    have e3 : 1000 * (W + 1) * (100 * (W + 1) ^ 3) = 100000 * (W + 1) ^ 4 := by ring
    have := hW12 4 (by omega)
    have := hW12 7 (by omega)
    linarith
  have hwne : wl ≠ [] := List.ne_nil_of_mem (a := a)
    (List.mem_filter.2 ⟨List.mem_range.2 ha, by simp [vL]⟩)
  have hrne : rl ≠ [] := List.ne_nil_of_mem (a := b)
    (List.mem_filter.2 ⟨List.mem_range.2 hb, by simp [vR]⟩)
  have fcond : FunDet P cond (rcCondIn n vL vR (X.getD x 0) (X.getD u 0) wl rl bm)
      (boolVal (rcCand ds x n t)) (10 ^ 23 * (W + 1) ^ 12) := by
    have hf := rc_cond_spec hP.hcond hP.hmc hP.hcnt hP.hmcd hP.hcd hP.hmg hP.hgt hP.hrng hP.hal
      hP.htw hP.hfe hP.hen n vL vR (X.getD x 0) (X.getD u 0) wl rl bm (by simp [bm])
      (fun row hr => by obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr; simp [rcBits])
      (fun row hr y hy => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
        obtain ⟨r, -, rfl⟩ := List.mem_map.1 hy
        split <;> omega) hwne hrne (M := M) hCw (by omega) (by omega)
    have hval : rcCond n vL vR (X.getD x 0) (X.getD u 0) wl rl bm = rcCand ds x n t := by
      unfold rcCand rcSide; rfl
    rw [hval] at hf
    refine rc_fd_mono hf ?_
    have h1 : (M + 1) ^ 4 ≤ 401 ^ 4 * (W + 1) ^ 12 := by
      calc (M + 1) ^ 4 ≤ (401 * (W + 1) ^ 3) ^ 4 := Nat.pow_le_pow_left (by omega) 4
        _ = 401 ^ 4 * (W + 1) ^ 12 := by ring
    have : 10 ^ 12 * (M + 1) ^ 4 ≤ 10 ^ 12 * (401 ^ 4 * (W + 1) ^ 12) := Nat.mul_le_mul_left _ h1
    norm_num at this ⊢
    linarith
  -- the body
  have hb3 : (boolVal (rcCand ds x n t)).wt ≤ Z := by
    have := wt_boolVal_le (rcCand ds x n t); omega
  have hrng_w : (natList (List.range n)).wt ≤ Z := by omega
  set E4 : List Val := [.nat a, .nat b, .nat u] with hE4
  have gX : StDC P (A :: E4) (.get rcED rcEI) (natList X) (5 + 5 + 1) (0 + 0) Z :=
    StDC.get (gD E4) (gI E4) (rc_tv_get (show x < ds.length by omega)) (by omega)
  have gvL := StDC.get (vs := X.map Val.nat) (v := .nat vL)
    (StDC.var' (P := P) (env := A :: (E4 ++ [natList X])) (i := 4) (v := natList X) (W := Z) rfl (by omega))
    (StDC.var' (P := P) (env := A :: (E4 ++ [natList X])) (i := 1) (v := .nat a) (W := Z) rfl (by have := wt_nat_le a; omega))
    (rc_natList_get (show a < X.length by omega)) (by omega)
  have gvR := StDC.get (vs := X.map Val.nat) (v := .nat vR)
    (StDC.var' (P := P) (env := A :: (E4 ++ [natList X, .nat vL])) (i := 4) (v := natList X) (W := Z) rfl (by omega))
    (StDC.var' (P := P) (env := A :: (E4 ++ [natList X, .nat vL])) (i := 2) (v := .nat b) (W := Z) rfl
      (by have := wt_nat_le b; omega))
    (rc_natList_get (show b < X.length by omega)) (by omega)
  set E7 : List Val := E4 ++ [natList X, .nat vL, .nat vR] with hE7
  have gvE := StDC.get (vs := U.map Val.nat) (v := .nat vE)
    (show StDC P (A :: E7) (.get rcED (.var 3)) (natList U) (5 + 1 + 1) (0 + 0) Z from
      StDC.get (gD E7) (StDC.var' (P := P) (env := A :: E7) (i := 3) (v := .nat u) (W := Z) rfl
      (by have := wt_nat_le u; omega)) (rc_tv_get (show u < ds.length by omega)) (by omega))
    (StDC.var' (P := P) (env := A :: E7) (i := 2) (v := .nat b) (W := Z) rfl (by have := wt_nat_le b; omega))
    (rc_natList_get (show b < U.length by omega)) (by omega)
  set E8 : List Val := E7 ++ [.nat vE] with hE8
  have gWl := StDC.call (StDC.mk2 (StDC.mk2
      (StDC.var' (P := P) (env := A :: E8) (i := 4) (v := natList X) (W := Z) rfl (by omega))
      (StDC.var' (P := P) (env := A :: E8) (i := 5) (v := .nat vL) (W := Z) rfl (by omega))
      (by have := wt_list2_le (natList X) (.nat vL); omega) (by omega))
    (StDC.call (gN E8) frng hrng_w)
    (by have := wt_list2_le (.list [natList X, .nat vL]) (natList (List.range n))
        have := wt_list2_le (natList X) (.nat vL); omega) (by omega))
    (fflt vL hvLw) (show (natList wl).wt ≤ Z by omega)
  set E9 : List Val := E8 ++ [natList wl] with hE9
  have gRl := StDC.call (StDC.mk2 (StDC.mk2
      (StDC.var' (P := P) (env := A :: E9) (i := 4) (v := natList X) (W := Z) rfl (by omega))
      (StDC.var' (P := P) (env := A :: E9) (i := 6) (v := .nat vR) (W := Z) rfl (by omega))
      (by have := wt_list2_le (natList X) (.nat vR); omega) (by omega))
    (StDC.call (gN E9) frng hrng_w)
    (by have := wt_list2_le (.list [natList X, .nat vR]) (natList (List.range n))
        have := wt_list2_le (natList X) (.nat vR); omega) (by omega))
    (fflt vR hvRw) (show (natList rl).wt ≤ Z by omega)
  set E10 : List Val := E9 ++ [natList rl] with hE10
  have gBm := StDC.call (StDC.mk2 (StDC.mk3 (gD E10)
      (StDC.var' (P := P) (env := A :: E10) (i := 7) (v := .nat vE) (W := Z) rfl (by omega))
      (StDC.var' (P := P) (env := A :: E10) (i := 9) (v := natList rl) (W := Z) rfl (by omega))
      (by omega) (by omega))
      (StDC.var' (P := P) (env := A :: E10) (i := 8) (v := natList wl) (W := Z) rfl (by omega))
      (by have := wt_list2_le (.list [rcTV ds, .nat vE, natList rl]) (natList wl); omega)
      (by omega))
    fmb (by omega)
  set E11 : List Val := E10 ++ [rcTV bm] with hE11
  set CL : List Val := [.nat n, .nat vL, .nat vR, .nat (X.getD x 0), .nat (X.getD u 0),
    natList wl, natList rl, rcTV bm] with hCL
  have hCLw : (Val.list CL).wt ≤ M := hCw
  have hpre : ∀ k, (Val.list (CL.take k)).wt ≤ Z := fun k =>
    (wt_list_sublist (List.take_sublist k CL)).trans (by omega)
  have gN11 := gN E11
  have g4 := StDC.mk4 gN11
    (StDC.var' (P := P) (env := A :: E11) (i := 5) (v := .nat vL) (W := Z) rfl (by omega))
    (StDC.var' (P := P) (env := A :: E11) (i := 6) (v := .nat vR) (W := Z) rfl (by omega))
    (StDC.get (vs := X.map Val.nat) (v := .nat (X.getD x 0))
      (StDC.var' (P := P) (env := A :: E11) (i := 4) (v := natList X) (W := Z) rfl (by omega))
      (gI E11) (rc_natList_get (show x < X.length by omega)) (by omega))
    (hpre 4) (by omega)
  have g5 := StDC.snoc g4 (StDC.get (vs := X.map Val.nat) (v := .nat (X.getD u 0))
      (StDC.var' (P := P) (env := A :: E11) (i := 4) (v := natList X) (W := Z) rfl (by omega))
      (StDC.var' (P := P) (env := A :: E11) (i := 3) (v := .nat u) (W := Z) rfl
        (by have := wt_nat_le u; omega))
      (rc_natList_get (show u < X.length by omega)) (by omega)) (hpre 5)
  have g6 := StDC.snoc g5
    (StDC.var' (P := P) (env := A :: E11) (i := 8) (v := natList wl) (W := Z) rfl (by omega))
    (hpre 6)
  have g7 := StDC.snoc g6
    (StDC.var' (P := P) (env := A :: E11) (i := 9) (v := natList rl) (W := Z) rfl (by omega))
    (hpre 7)
  have g8 := StDC.snoc g7
    (StDC.var' (P := P) (env := A :: E11) (i := 10) (v := rcTV bm) (W := Z) rfl (by omega))
    (hpre 8)
  have gC := StDC.call (f := cond) g8 fcond hb3
  have gbody := StDC.letE gX (StDC.letE gvL (StDC.letE gvR (StDC.letE gvE (StDC.letE gWl
    (StDC.letE gRl (StDC.letE gBm gC hb3) hb3) hb3) hb3) hb3) hb3) hb3
  have gall := StDC.letE gpa (StDC.letE gpb (StDC.letE gpu gbody hb3) hb3) hb3
  refine StDC.funDet hP.hcf gall ?_
  have hZ12 : Z + 1 ≤ 1001 * (W + 1) ^ 12 := by have := hW12 3 (by omega); omega
  norm_num only [Nat.add_zero, Nat.zero_add] at hZ12 ⊢
  linarith

end GI.Impl
