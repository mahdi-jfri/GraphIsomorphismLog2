module

public import Workspace.Impl.AggRectCertQ
public import Workspace.Impl.AggStructDesSplit

@[expose] public section

/-!
# The certificate search as a program

`rcCertF` on `[T, j, x₀]`, for the table `T` of the pair colors:

1. `F`: the points `y` with `T[y][y] = j` (a `filter` of `rcDiagT` over `range q`);
2. `D`: the rows `T[a]` restricted to `F`, for `a ∈ F` (a `map` of `rcDRowF`);
3. `i₀`: the position of `x₀` in `F` (`findEq`), and `n = |F|`;
4. `t`: the first candidate `t < n³` that passes `rcCandF` (`find`);
5. the output `[D[i₀][a], D[i₀][b], D[u][b], F[a], F[b]]` for the points `a, b, u` of `t`, or `[]`
   if no candidate passes.

`rc_certF_spec` (general tables): the output is `rcOut D F i₀ n` at cost `10⁵⁰ (W + 1)⁴⁰`.
`rc_cert_spec`: `RcCertSpec P f rcCertB`, with the certificate function `rcCertFn`.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)
open GI.Machine (BinOp)

/-- The points of `t = var 5` with `n = var 4`. -/
def rcEA : Expr := .arith .div (.var 5) (.arith .mul (.var 4) (.var 4))
def rcEB : Expr := .arith .mod (.arith .div (.var 5) (.var 4)) (.var 4)
def rcEU : Expr := .arith .mod (.var 5) (.var 4)
def rcENNN : Expr := .arith .mul (.arith .mul (.var 4) (.var 4)) (.var 4)

/-- The output for the candidate `t`. -/
def rcOutE : Expr :=
  .snoc (mk4 (.get (.get (.var 2) (.var 3)) rcEA) (.get (.get (.var 2) (.var 3)) rcEB)
    (.get (.get (.var 2) rcEU) rcEB) (.get (.var 1) rcEA)) (.get (.var 1) rcEB)

/-- **The certificate search** (`flt2`: filter of `rcDiagT`; `rng`: range; `md`: map of
`rcDRowF`; `fq`: findEq; `fnd`: find of `rcCandF`). -/
def rcCertF (flt2 rng md fq fnd : ℕ) : Expr :=
  .letE (.call flt2 (mk2 (mk2 (arg 0) (arg 1)) (.call rng (.length (arg 0)))))
  (.letE (.call md (mk2 (mk2 (arg 0) (.var 1)) (.var 1)))
  (.letE (.call fq (mk2 (arg 2) (.var 1)))
  (.letE (.length (.var 1))
  (.letE (.call fnd (mk2 (mk3 (.var 2) (.var 3) (.var 4)) (.call rng rcENNN)))
  (.ite (.arith .lt (.var 5) rcENNN) rcOutE .nil)))))

/-- The functions of the certificate search. -/
structure RcCertOk (P : Program) (f flt2 dg md dr gth fq fnd cf flt et rng mb br mbe cond mc mcd al
    cnt cd mg gt tw fe en : ℕ) : Prop where
  hcand : RcCandOk P cf flt et rng mb br mbe cond mc mcd al cnt cd mg gt tw fe en
  hf : P.funs[f]? = some (rcCertF flt2 rng md fq fnd)
  hflt2 : P.HasAt flt2 (filterFuns flt2 dg)
  hdg : P.funs[dg]? = some rcDiagT
  hmd : P.HasAt md (mapFuns md dr)
  hdr : P.funs[dr]? = some (rcDRowF gth)
  hgth : P.HasAt gth (gatherFuns gth)
  hfq : P.HasAt fq (findEqFuns fq)
  hfnd : P.HasAt fnd (findFuns fnd cf)

/-- A table entry has a smaller weight than the table. -/
theorem rc_find_le (D : List (List ℕ)) (x n : ℕ) : rcFind D x n ≤ n * n * n := by
  unfold rcFind
  have := List.findIdx_le_length (p := rcCand D x n) (xs := List.range (n * n * n))
  simpa using this

theorem rc_wt_entry {ts : List (List ℕ)} {a k : ℕ} (ha : a < ts.length)
    (hk : k < (ts.getD a []).length) : (Val.nat (rcAt ts a k)).wt < (rcTV ts).wt :=
  (rc_wt_nat_lt hk).trans (rc_wt_row_lt ha)

set_option maxHeartbeats 8000000 in
/-- **The certificate search on a square table.** -/
theorem rc_certF_spec {P : Program} {f flt2 dg md dr gth fq fnd cf flt et rng mb br mbe cond mc
    mcd al cnt cd mg gt tw fe en : ℕ}
    (hP : RcCertOk P f flt2 dg md dr gth fq fnd cf flt et rng mb br mbe cond mc mcd al cnt cd mg gt
      tw fe en)
    (ts : List (List ℕ)) (j x₀ : ℕ) (hrow : ∀ row ∈ ts, row.length = ts.length)
    (hx₀ : x₀ < ts.length)
    (hi : ((List.range ts.length).filter fun y => decide (rcAt ts y y = j)).findIdx
      (fun y => decide (y = x₀)) <
      ((List.range ts.length).filter fun y => decide (rcAt ts y y = j)).length)
    {W : ℕ} (hW : (Val.list [rcTV ts, .nat j, .nat x₀]).wt ≤ W) (h20 : 20 ≤ W) :
    FunDet P f (.list [rcTV ts, .nat j, .nat x₀])
      (rcOut (((List.range ts.length).filter fun y => decide (rcAt ts y y = j)).map fun a =>
          ((List.range ts.length).filter fun y => decide (rcAt ts y y = j)).map (rcAt ts a))
        ((List.range ts.length).filter fun y => decide (rcAt ts y y = j))
        (((List.range ts.length).filter fun y => decide (rcAt ts y y = j)).findIdx
          (fun y => decide (y = x₀)))
        ((List.range ts.length).filter fun y => decide (rcAt ts y y = j)).length)
      (10 ^ 50 * (W + 1) ^ 40) ∧
    (rcOut (((List.range ts.length).filter fun y => decide (rcAt ts y y = j)).map fun a =>
          ((List.range ts.length).filter fun y => decide (rcAt ts y y = j)).map (rcAt ts a))
        ((List.range ts.length).filter fun y => decide (rcAt ts y y = j))
        (((List.range ts.length).filter fun y => decide (rcAt ts y y = j)).findIdx
          (fun y => decide (y = x₀)))
        ((List.range ts.length).filter fun y => decide (rcAt ts y y = j)).length).wt ≤
      1000 * (W + 1) ^ 6 := by
  set q := ts.length with hq
  set F := (List.range q).filter fun y => decide (rcAt ts y y = j) with hF
  set n := F.length with hn
  set D := F.map fun a => F.map (rcAt ts a) with hD
  set i₀ := F.findIdx (fun y => decide (y = x₀)) with hi₀
  -- sizes
  set A := Val.list [rcTV ts, .nat j, .nat x₀] with hA
  have hTw : (rcTV ts).wt < A.wt := wt_le_wt_list (by simp)
  have hjw : (Val.nat j).wt < A.wt := wt_le_wt_list (by simp)
  have hxw : (Val.nat x₀).wt < A.wt := wt_le_wt_list (by simp)
  have hqW : q < W := by have := rc_len_lt_tv ts; omega
  have hFs : F.Sublist (List.range q) := List.filter_sublist
  have hFr : ∀ a ∈ F, a < q := fun a ha => List.mem_range.1 (hFs.subset ha)
  have hnq : n ≤ q := by have := hFs.length_le; simpa using this
  have hrl : ∀ a < q, (ts.getD a []).length = q := fun a ha => by
    rw [List.getD_eq_getElem _ _ ha]; exact hrow _ (List.getElem_mem _)
  have hW2 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hW3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := rc_pow_le (by omega)
  have hW40 : ∀ i ≤ 40, (W + 1) ^ i ≤ (W + 1) ^ 40 := fun i hi => rc_pow_le hi
  have hFw : (natList F).wt ≤ 5 * (W + 1) ^ 2 := rc_wt_side hFs hqW.le
  have hrw : (natList (List.range q)).wt ≤ 5 * (W + 1) ^ 2 :=
    rc_wt_side (List.Sublist.refl _) hqW.le
  have hDrow : ∀ a ∈ F, (natList (F.map (rcAt ts a))).wt ≤ 3 * (W + 1) ^ 2 := by
    intro a ha
    have := rc_wt_list (vs := (F.map (rcAt ts a)).map Val.nat) (c := W) (L := W) (by
      intro v hv
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
      have := rc_wt_entry (ts := ts) (a := a) (k := k) (hFr a ha) (by rw [hrl a (hFr a ha)]; exact hFr k hk)
      omega) (by simp; omega)
    have e : (Val.list ((F.map (rcAt ts a)).map Val.nat)).wt = (natList (F.map (rcAt ts a))).wt := rfl
    rw [e] at this
    nlinarith
  have hDw : (rcTV D).wt ≤ 10 * (W + 1) ^ 3 := by
    have := rc_wt_list (vs := D.map natList) (c := 3 * (W + 1) ^ 2) (L := W) (by
      intro v hv
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
      exact hDrow a ha) (by simp [D]; omega)
    have e : (Val.list (D.map natList)).wt = (rcTV D).wt := rfl
    rw [e] at this
    nlinarith
  have hW1 : W + 1 ≤ (W + 1) ^ 40 := by simpa using hW40 1 (by omega)
  have hTW : (rcTV ts).wt < W := by omega
  -- the fiber
  have fflt : FunDet P flt2 (.list [.list [rcTV ts, .nat j], natList (List.range q)]) (natList F)
      (10 ^ 5 * (W + 1) ^ 40) := by
    have hf := rc_filterN hP.hflt2 (c := .list [rcTV ts, .nat j]) (xs := List.range q)
      (t := fun y => decide (rcAt ts y y = j)) (B := 20 * (10 * W + 23)) (fun y hy => by
        have hy' := List.mem_range.1 hy
        refine rc_diagT_spec hP.hdg hy' (by rw [hrl y hy']; exact hy') (W := 10 * W + 22) ?_
          (by omega)
        have := wt_list2_le (.list [rcTV ts, .nat j]) (.nat y)
        have := wt_list2_le (rcTV ts) (.nat j)
        have := wt_nat_le y
        omega)
    refine rc_fd_mono hf ?_
    have h1 := wt_list2_le (.list [rcTV ts, .nat j]) (natList (List.range q))
    have h2 := wt_list2_le (rcTV ts) (.nat j)
    simp only [List.length_range]
    rw [← hF]
    have e1 : q * (20 * (10 * W + 23)) ≤ 1000 * (W + 1) ^ 2 := by
      have := rc_mul_lin (c := 200) (d := 460) (show q ≤ W + 1 by omega)
      have e : 20 * (10 * W + 23) = 200 * W + 460 := by ring
      rw [e]; omega
    have e2 : loopModK * (q + 1) * ((Val.list [.list [rcTV ts, .nat j],
        natList (List.range q)]).wt + q + (natList F).wt + 1) ≤
        1000 * (W + 1) * (50 * (W + 1) ^ 2) := by
      unfold loopModK
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by linarith)
    have e3 : 1000 * (W + 1) * (50 * (W + 1) ^ 2) = 50000 * (W + 1) ^ 3 := by ring
    have := hW40 2 (by omega)
    have := hW40 3 (by omega)
    linarith
  -- the rows
  have hc2 : (Val.list [rcTV ts, natList F]).wt ≤ 20 * (W + 1) ^ 2 := by
    have := wt_list2_le (rcTV ts) (natList F); omega
  have fmd : FunDet P md (.list [.list [rcTV ts, natList F], natList F]) (rcTV D)
      (10 ^ 14 * (W + 1) ^ 40) := by
    have hf := rc_mapN hP.hmd (c := .list [rcTV ts, natList F]) (xs := F)
      (g := fun a => natList (F.map (rcAt ts a))) (B := 10 ^ 8 * (50 * (W + 1) ^ 2 + 1) ^ 3)
      (fun a ha => by
        have ha' := hFr a ha
        refine rc_dRow_spec hP.hdr hP.hgth ts F a ha' (fun k hk => by
          rw [hrl a ha']; exact hFr k hk) (W := 50 * (W + 1) ^ 2) ?_ (by linarith)
        have := wt_list2_le (.list [rcTV ts, natList F]) (.nat a)
        have := wt_nat_le a
        linarith)
    have e : Val.list (F.map fun a => natList (F.map (rcAt ts a))) = rcTV D := by
      show _ = Val.list (D.map natList)
      rw [hD, List.map_map]; rfl
    rw [e] at hf
    refine rc_fd_mono hf ?_
    have h1 := wt_list2_le (.list [rcTV ts, natList F]) (natList F)
    have hp : (50 * (W + 1) ^ 2 + 1) ^ 3 ≤ 132651 * (W + 1) ^ 6 := by
      calc (50 * (W + 1) ^ 2 + 1) ^ 3 ≤ (51 * (W + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        _ = 132651 * (W + 1) ^ 6 := by ring
    have e1 : F.length * (10 ^ 8 * (50 * (W + 1) ^ 2 + 1) ^ 3) ≤
        (W + 1) * (10 ^ 8 * (132651 * (W + 1) ^ 6)) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hp)
    have e1' : (W + 1) * (10 ^ 8 * (132651 * (W + 1) ^ 6)) = 132651 * 10 ^ 8 * (W + 1) ^ 7 := by ring
    have e2 : mapK * (F.length + 1) * ((Val.list [.list [rcTV ts, natList F], natList F]).wt +
        (rcTV D).wt + 1) ≤ 1000 * (W + 1) * (100 * (W + 1) ^ 3) := by
      unfold mapK
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by linarith)
    have e3 : 1000 * (W + 1) * (100 * (W + 1) ^ 3) = 100000 * (W + 1) ^ 4 := by ring
    have := hW40 4 (by omega)
    have := hW40 7 (by omega)
    linarith
  -- the position of `x₀`
  have ffq : FunDet P fq (.list [.nat x₀, natList F]) (.nat i₀) (10 ^ 5 * (W + 1) ^ 40) := by
    refine rc_fd_mono (findEq_spec hP.hfq (xs := F) (j := x₀) (B := W)
      (fun y hy => (hFr y hy).le.trans (by omega)) (by omega) (by omega)) ?_
    have := hW40 3 (by omega)
    unfold findEqK; linarith
  -- the search
  have hDl : D.length = n := by simp [D, n]
  have hDr : ∀ row ∈ D, row.length = n := by
    intro row hr; obtain ⟨a, -, rfl⟩ := List.mem_map.1 hr; simp [n]
  have hnW : n ≤ W := by omega
  have hN : n * n * n + 1 ≤ (W + 1) ^ 3 := by
    have : n * n * n ≤ W * W * W := Nat.mul_le_mul (Nat.mul_le_mul hnW hnW) hnW
    have : (W + 1) ^ 3 = W * W * W + 3 * (W * W) + 3 * W + 1 := by ring
    omega
  have hW6 : (W + 1) ^ 3 ≤ (W + 1) ^ 6 := rc_pow_le (by omega)
  set N := n * n * n with hNdef
  have hi₀n : i₀ < n := hi
  have hcw : (Val.list [rcTV D, .nat i₀, .nat n]).wt ≤ 30 * (W + 1) ^ 3 := by
    have := wt_list3_le (rcTV D) (.nat i₀) (.nat n)
    have := wt_nat_le i₀
    have := wt_nat_le n
    omega
  have hRN : (natList (List.range N)).wt ≤ 5 * (W + 1) ^ 6 := by
    have := rc_wt_natList (xs := List.range N) (B := N)
      (fun x hx => (List.mem_range.1 hx).le) (by simp)
    have : (N + 1) ^ 2 ≤ ((W + 1) ^ 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have e : ((W + 1) ^ 3) ^ 2 = (W + 1) ^ 6 := by ring
    omega
  have ffnd : FunDet P fnd (.list [.list [rcTV D, .nat i₀, .nat n], natList (List.range N)])
      (.nat (rcFind D i₀ n)) (10 ^ 49 * (W + 1) ^ 40) := by
    have hf := st_find_det hP.hfnd (c := .list [rcTV D, .nat i₀, .nat n]) (n := N)
      (t := rcCand D i₀ n) (B := 10 ^ 24 * (100 * (W + 1) ^ 3 + 1) ^ 12)
      (X := 100 * (W + 1) ^ 6) (fun i hi' => by
        refine rc_cand_spec hP.hcand D i₀ n i hDl hDr hi₀n hi' (W := 100 * (W + 1) ^ 3) ?_
          (by linarith)
        have := wt_list2_le (.list [rcTV D, .nat i₀, .nat n]) (.nat i)
        have := wt_nat_le i
        show (Val.list [.list [rcTV D, .nat i₀, .nat n], .nat i]).wt ≤ _
        omega) (by
        have := wt_list2_le (.list [rcTV D, .nat i₀, .nat n]) (natList (List.range N))
        linarith) (by linarith)
    refine rc_fd_mono hf ?_
    have hp : (100 * (W + 1) ^ 3 + 1) ^ 12 ≤ 101 ^ 12 * (W + 1) ^ 36 := by
      calc (100 * (W + 1) ^ 3 + 1) ^ 12 ≤ (101 * (W + 1) ^ 3) ^ 12 :=
            Nat.pow_le_pow_left (by omega) 12
        _ = 101 ^ 12 * (W + 1) ^ 36 := by ring
    have e1 : N * (10 ^ 24 * (100 * (W + 1) ^ 3 + 1) ^ 12) ≤
        (W + 1) ^ 3 * (10 ^ 24 * (101 ^ 12 * (W + 1) ^ 36)) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hp)
    have e1' : (W + 1) ^ 3 * (10 ^ 24 * (101 ^ 12 * (W + 1) ^ 36)) =
        10 ^ 24 * 101 ^ 12 * (W + 1) ^ 39 := by ring
    have e2 : loopModK * (100 * (W + 1) ^ 6 + 1) * (3 * (100 * (W + 1) ^ 6) + 3) ≤
        1000 * (101 * (W + 1) ^ 6) * (303 * (W + 1) ^ 6) := by
      unfold loopModK
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e3 : 1000 * (101 * (W + 1) ^ 6) * (303 * (W + 1) ^ 6) = 30603000 * (W + 1) ^ 12 := by ring
    have := hW40 12 (by omega)
    have := hW40 39 (by omega)
    norm_num at e1' ⊢
    linarith
  -- the program
  have htfN : rcFind D i₀ n ≤ N := by rw [hNdef]; exact rc_find_le D i₀ n
  clear_value N i₀ D n F
  set Z := 1000 * (W + 1) ^ 6 with hZ
  set tf := rcFind D i₀ n with htf
  have hAe : (Val.list [rcTV ts, .nat j, .nat x₀]).wt = A.wt := rfl
  have frng : ∀ m : ℕ, m + 1 ≤ (W + 1) ^ 3 →
      FunDet P rng (.nat m) (natList (List.range m)) (10 ^ 4 * (W + 1) ^ 40) := fun m hm =>
    rc_fd_mono (st_range_det hP.hcand.hrng m) (by
      have : (m + 1) ^ 3 ≤ ((W + 1) ^ 3) ^ 3 := Nat.pow_le_pow_left hm 3
      have e : ((W + 1) ^ 3) ^ 3 = (W + 1) ^ 9 := by ring
      have := hW40 9 (by omega)
      norm_num; omega)
  have hFe : ∀ a ∈ F, a ≤ W := fun a ha => (hFr a ha).le.trans (by omega)
  have g0 : ∀ rest, StDC P (A :: rest) (arg 0) (rcTV ts) 3 0 Z := fun rest =>
    StDC.arg (vs := [rcTV ts, .nat j, .nat x₀]) rfl (by omega) (by omega) (by omega)
  have g1 : ∀ rest, StDC P (A :: rest) (arg 1) (.nat j) 3 0 Z := fun rest =>
    StDC.arg (vs := [rcTV ts, .nat j, .nat x₀]) rfl (by omega) (by omega) (by omega)
  have g2 : ∀ rest, StDC P (A :: rest) (arg 2) (.nat x₀) 3 0 Z := fun rest =>
    StDC.arg (vs := [rcTV ts, .nat j, .nat x₀]) rfl (by omega) (by omega) (by omega)
  -- `F`
  have glen : StDC P [A] (.length (arg 0)) (.nat q) 4 0 Z := by
    have h := StDC.length (vs := ts.map natList) (g0 []) (by
      simp only [List.length_map]; omega)
    rw [List.length_map] at h
    exact h
  have gF := StDC.call (StDC.mk2 (StDC.mk2 (g0 []) (g1 [])
      (by have := wt_list2_le (rcTV ts) (.nat j); omega) (by omega))
    (StDC.call glen (frng q (by omega)) (by omega))
    (by have := wt_list2_le (.list [rcTV ts, .nat j]) (natList (List.range q))
        have := wt_list2_le (rcTV ts) (.nat j); omega) (by omega))
    fflt (show (natList F).wt ≤ Z by omega)
  -- `D`
  have gD := StDC.call (StDC.mk2 (StDC.mk2 (g0 [natList F])
      (StDC.var' (P := P) (env := A :: [natList F]) (i := 1) (v := natList F) (W := Z) rfl (by omega))
      (by omega) (by omega))
      (StDC.var' (P := P) (env := A :: [natList F]) (i := 1) (v := natList F) (W := Z) rfl (by omega))
      (by have := wt_list2_le (.list [rcTV ts, natList F]) (natList F); omega) (by omega))
    fmd (show (rcTV D).wt ≤ Z by omega)
  -- `i₀`
  have gi := StDC.call (StDC.mk2 (g2 [natList F, rcTV D])
      (StDC.var' (P := P) (env := A :: [natList F, rcTV D]) (i := 1) (v := natList F) (W := Z) rfl
        (by omega))
      (by have := wt_list2_le (.nat x₀) (natList F); omega) (by omega))
    ffq (show (Val.nat i₀).wt ≤ Z by have := wt_nat_le i₀; omega)
  -- `n`
  have gn : StDC P (A :: [natList F, rcTV D, .nat i₀]) (.length (.var 1)) (.nat n) 2 0 Z := by
    have h := StDC.length (vs := F.map Val.nat)
      (StDC.var' (P := P) (env := A :: [natList F, rcTV D, .nat i₀]) (i := 1) (v := natList F)
        (W := Z) rfl (by omega)) (by simp only [List.length_map]; omega)
    rw [List.length_map, ← hn] at h
    exact h
  -- `t`
  set E4 : List Val := [natList F, rcTV D, .nat i₀, .nat n] with hE4
  have gv : ∀ (i : ℕ) (v : Val), (A :: E4)[i]? = some v → v.wt ≤ Z → StDC P (A :: E4) (.var i) v 1 0 Z :=
    fun i v h hw => StDC.var' h hw
  have hn2 : n * n ≤ (W + 1) ^ 2 := by
    calc n * n ≤ (W + 1) * (W + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ = (W + 1) ^ 2 := by ring
  have hnZ4 : (Val.nat n).wt ≤ Z := by have := wt_nat_le n; omega
  have gv4 : StDC P (A :: E4) (.var 4) (.nat n) 1 0 Z := gv 4 (.nat n) rfl hnZ4
  have hz1 : BinOp.eval .mul n n = n * n := by simp only [BinOp.eval]
  have hz2 : BinOp.eval .mul (n * n) n = N := by simp only [BinOp.eval]; exact hNdef.symm
  have hw1 : n * n + 2 ≤ Z := by omega
  have hw2 : N + 2 ≤ Z := by omega
  have gnn := StDC.arith' (op := .mul) gv4 gv4 hz1 hw1
  have gNNN := StDC.arith' (op := .mul) gnn gv4 hz2 hw2
  have gt := StDC.call (StDC.mk2 (StDC.mk3 (gv 2 (rcTV D) rfl (by omega))
      (gv 3 (.nat i₀) rfl (by have := wt_nat_le i₀; omega))
      (gv 4 (.nat n) rfl (by have := wt_nat_le n; omega)) (by omega) (by omega))
      (StDC.call gNNN (frng N (by omega)) (by omega))
      (by have := wt_list2_le (.list [rcTV D, .nat i₀, .nat n]) (natList (List.range N)); omega)
      (by omega))
    ffnd (show (Val.nat tf).wt ≤ Z by
      have := wt_nat_le tf
      omega)
  -- the test and the output
  set E5 : List Val := E4 ++ [.nat tf] with hE5
  have gw : ∀ (i : ℕ) (v : Val), (A :: E5)[i]? = some v → v.wt ≤ Z → StDC P (A :: E5) (.var i) v 1 0 Z :=
    fun i v h hw => StDC.var' h hw
  have hnZ : (Val.nat n).wt ≤ Z := by have := wt_nat_le n; omega
  have htf : tf ≤ N := htfN
  have htfZ : (Val.nat tf).wt ≤ Z := by have := wt_nat_le tf; omega
  have gw4 : StDC P (A :: E5) (.var 4) (.nat n) 1 0 Z := gw 4 (.nat n) rfl hnZ
  have gw5 : StDC P (A :: E5) (.var 5) (.nat tf) 1 0 Z := gw 5 (.nat tf) rfl htfZ
  have gnn5 := StDC.arith' (op := .mul) gw4 gw4 hz1 hw1
  have gN5 := StDC.arith' (op := .mul) gnn5 gw4 hz2 hw2
  have gcmp := StDC.arith' (op := .lt) gw5 gN5 rfl
    (by simp only [BinOp.eval]; split_ifs <;> omega)
  have hDrl : ∀ i < n, (D.getD i []).length = n := fun i hi' => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hDr _ (List.getElem_mem _)
  have hDe : ∀ i < n, ∀ k < n, (Val.nat (rcAt D i k)).wt ≤ 10 * (W + 1) ^ 3 := fun i hi' k hk =>
    (rc_wt_entry (ts := D) (by omega) (by rw [hDrl i hi']; exact hk)).le.trans hDw
  have hFe' : ∀ k < n, (Val.nat (F.getD k 0)).wt ≤ 10 * (W + 1) ^ 3 := fun k hk =>
    (rc_wt_nat_lt (xs := F) (by rw [← hn]; exact hk)).le.trans (by omega)
  have hlist5 : ∀ v1 v2 v3 v4 v5 : Val, v1.wt ≤ 10 * (W + 1) ^ 3 → v2.wt ≤ 10 * (W + 1) ^ 3 →
      v3.wt ≤ 10 * (W + 1) ^ 3 → v4.wt ≤ 10 * (W + 1) ^ 3 → v5.wt ≤ 10 * (W + 1) ^ 3 →
      (Val.list [v1, v2, v3, v4, v5]).wt ≤ Z := by
    intro v1 v2 v3 v4 v5 h1 h2 h3 h4 h5
    have := rc_wt_list (vs := [v1, v2, v3, v4, v5]) (c := 10 * (W + 1) ^ 3) (L := 5) (by
      intro v hv
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption) (by simp)
    omega
  have hlist4 : ∀ v1 v2 v3 v4 : Val, v1.wt ≤ 10 * (W + 1) ^ 3 → v2.wt ≤ 10 * (W + 1) ^ 3 →
      v3.wt ≤ 10 * (W + 1) ^ 3 → v4.wt ≤ 10 * (W + 1) ^ 3 →
      (Val.list [v1, v2, v3, v4]).wt ≤ Z := by
    intro v1 v2 v3 v4 h1 h2 h3 h4
    have := rc_wt_list (vs := [v1, v2, v3, v4]) (c := 10 * (W + 1) ^ 3) (L := 4) (by
      intro v hv
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> assumption) (by simp)
    omega
  have hout_w : (rcOut D F i₀ n).wt ≤ Z := by
    unfold rcOut
    split_ifs with h
    · have ha := rc_pa_lt h
      have hb := rc_pb_lt h
      have hu := rc_pu_lt h
      exact hlist5 _ _ _ _ _ (hDe _ hi₀n _ ha) (hDe _ hi₀n _ hb) (hDe _ hu _ hb) (hFe' _ ha)
        (hFe' _ hb)
    · have := wt_list_le_of ([] : List Val) (c := 0) (by simp)
      simp only [List.length_nil, Nat.zero_mul, Nat.zero_add] at this; omega
  have gOut : tf < N → StDC P (A :: E5) rcOutE (rcOut D F i₀ n) 100 0 Z := by
    intro htN0
    have htN : tf < n * n * n := by rw [← hNdef]; exact htN0
    have ha := rc_pa_lt htN
    have hb := rc_pb_lt htN
    have hu := rc_pu_lt htN
    have hnn' : n * n + 2 ≤ Z := by omega
    have hza : BinOp.eval .div tf (n * n) = rcPa n tf := by simp only [BinOp.eval, rcPa]
    have hzb1 : BinOp.eval .div tf n = tf / n := by simp only [BinOp.eval]
    have hzb : BinOp.eval .mod (tf / n) n = rcPb n tf := by simp only [BinOp.eval, rcPb]
    have hzu : BinOp.eval .mod tf n = rcPu n tf := by simp only [BinOp.eval, rcPu]
    have hwa : rcPa n tf + 2 ≤ Z := by omega
    have hwb1 : tf / n + 2 ≤ Z := by have := Nat.div_le_self tf n; omega
    have hwb : rcPb n tf + 2 ≤ Z := by omega
    have hwu : rcPu n tf + 2 ≤ Z := by omega
    have gA := StDC.arith' (op := .div) gw5 gnn5 hza hwa
    have gB := StDC.arith' (op := .mod) (StDC.arith' (op := .div) gw5 gw4 hzb1 hwb1) gw4 hzb hwb
    have gU := StDC.arith' (op := .mod) gw5 gw4 hzu hwu
    have gR0 := StDC.get (v := natList (D.getD i₀ [])) (gw 2 (rcTV D) rfl (by omega)) (gw 3 (.nat i₀) rfl (by have := wt_nat_le i₀; omega))
        (rc_tv_get (show i₀ < D.length by omega))
        ((rc_wt_row_lt (ts := D) (show i₀ < D.length by omega)).le.trans (by omega))
    have gRU := StDC.get (v := natList (D.getD (rcPu n tf) [])) (gw 2 (rcTV D) rfl (by omega)) gU
        (rc_tv_get (show rcPu n tf < D.length by omega))
        ((rc_wt_row_lt (ts := D) (show rcPu n tf < D.length by omega)).le.trans (by omega))
    have e1 := StDC.get (vs := (D.getD i₀ []).map Val.nat) (v := .nat (rcAt D i₀ (rcPa n tf))) gR0 gA
      (rc_natList_get (by rw [hDrl i₀ hi₀n]; exact ha)) ((hDe _ hi₀n _ ha).trans (by omega))
    have e2 := StDC.get (vs := (D.getD i₀ []).map Val.nat) (v := .nat (rcAt D i₀ (rcPb n tf))) gR0 gB
      (rc_natList_get (by rw [hDrl i₀ hi₀n]; exact hb)) ((hDe _ hi₀n _ hb).trans (by omega))
    have e3 := StDC.get (vs := (D.getD (rcPu n tf) []).map Val.nat)
      (v := .nat (rcAt D (rcPu n tf) (rcPb n tf))) gRU gB
      (rc_natList_get (by rw [hDrl _ hu]; exact hb)) ((hDe _ hu _ hb).trans (by omega))
    have e4 := StDC.get (vs := F.map Val.nat) (v := .nat (F.getD (rcPa n tf) 0))
      (gw 1 (natList F) rfl (by omega)) gA (rc_natList_get (by rw [← hn]; exact ha)) ((hFe' _ ha).trans (by omega))
    have e5 := StDC.get (vs := F.map Val.nat) (v := .nat (F.getD (rcPb n tf) 0))
      (gw 1 (natList F) rfl (by omega)) gB (rc_natList_get (by rw [← hn]; exact hb)) ((hFe' _ hb).trans (by omega))
    have g4 := StDC.mk4 e1 e2 e3 e4 (hlist4 _ _ _ _ (hDe _ hi₀n _ ha) (hDe _ hi₀n _ hb)
      (hDe _ hu _ hb) (hFe' _ ha)) (by omega)
    have g5 := StDC.snoc g4 e5 (hlist5 _ _ _ _ _ (hDe _ hi₀n _ ha) (hDe _ hi₀n _ hb)
      (hDe _ hu _ hb) (hFe' _ ha) (hFe' _ hb))
    have hro : rcOut D F i₀ n = .list [.nat (rcAt D i₀ (rcPa n tf)), .nat (rcAt D i₀ (rcPb n tf)),
        .nat (rcAt D (rcPu n tf) (rcPb n tf)), .nat (F.getD (rcPa n tf) 0),
        .nat (F.getD (rcPb n tf) 0)] := by
      unfold rcOut; rw [if_pos htN]
    rw [hro]
    exact g5.mono (by norm_num) (by norm_num)
  have gite := StDC.ite (v := rcOut D F i₀ n) (nt := 100) (Et := 0) (ne := 1) (Ee := 0) gcmp
    (fun h => gOut (by
      by_contra h'
      simp only [BinOp.eval, if_neg h'] at h
      exact h rfl))
    (fun h => by
      have htN0 : ¬ tf < N := by
        intro h'
        simp only [BinOp.eval, if_pos h'] at h
        exact absurd h (by norm_num)
      have htN : ¬ tf < n * n * n := by rw [← hNdef]; exact htN0
      have hro : rcOut D F i₀ n = .list [] := by unfold rcOut; rw [if_neg htN]
      rw [hro]
      exact StDC.nil (by omega)) hout_w
  have gF' := gF.mono (n' := 1000) (E' := 10 ^ 4 * (W + 1) ^ 40 + 10 ^ 5 * (W + 1) ^ 40)
    (by norm_num) (by simp only [Nat.zero_add, Nat.add_zero]; omega)
  have gD' := gD.mono (n' := 1000) (E' := 10 ^ 14 * (W + 1) ^ 40)
    (by norm_num) (by simp only [Nat.zero_add, Nat.add_zero]; omega)
  have gi' := gi.mono (n' := 1000) (E' := 10 ^ 5 * (W + 1) ^ 40)
    (by norm_num) (by simp only [Nat.zero_add, Nat.add_zero]; omega)
  have gn' := gn.mono (n' := 1000) (E' := 0) (by norm_num) le_rfl
  have gt' := gt.mono (n' := 1000) (E' := 10 ^ 4 * (W + 1) ^ 40 + 10 ^ 49 * (W + 1) ^ 40)
    (by norm_num) (by simp only [Nat.zero_add, Nat.add_zero]; omega)
  have gite' := gite.mono (n' := 1000) (E' := 0) (by norm_num) (by simp)
  have gbody := StDC.letE gF' (StDC.letE gD' (StDC.letE gi' (StDC.letE gn' (StDC.letE gt' gite'
    hout_w) hout_w) hout_w) hout_w) hout_w
  refine ⟨StDC.funDet hP.hf gbody ?_, hout_w⟩
  have hZ40 : Z + 1 ≤ 1001 * (W + 1) ^ 40 := by have := hW40 6 (by omega); omega
  clear_value Z
  generalize (W + 1) ^ 40 = P40 at hZ40 ⊢
  omega

end GI.Impl
