module

public import Workspace.Impl.GenProdSq

@[expose] public section

/-!
# The product refinement: the coordinate intervals

Interval `i < r` of the split hierarchy has the partition `coordPart (i + 1)`: two positions
agree in all coordinates `j > i`. In the table of leading ones, this is
`r - i ≤ lead (p, q)` (`coordPart_iff_plead`). The label of a point `p` is the first point `q`
in its class (`firstLab`), found by a search over the points.

`coordVals_spec` computes the list of the `r` interval values
`[labels, ratio, cap, origin]` from the table of leading ones.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {k : ℕ}

/-- The label of `p` for interval `i`: the first `q` with `r - i - 1 < lead (p, q)`. -/
def coordLab (lead : Fin (k * k) → ℕ) (r i : ℕ) (p : Fin k) : ℕ :=
  (List.finRange k).findIdx fun q => decide (r - i - 1 < lead (finProdFinEquiv (p, q)))

/-- The context of the coordinate intervals: `[lead, k, r, c, cap, origin, ids]`. -/
def cvCtx (lead : Fin (k * k) → ℕ) (r c cm o : ℕ) : Val :=
  .list [encFun lead, .nat k, .nat r, .nat c, .nat cm, .nat o, encFun fun p : Fin k => (p : ℕ)]

/-- The test, on `[[cc, i, p], q]`: `r - i - 1 < lead (p k + q)`. -/
def cvTestF : Expr :=
  let C := Expr.get (arg 0) (.nat 0)
  let I := Expr.get (arg 0) (.nat 1)
  let Pp := Expr.get (arg 0) (.nat 2)
  let K := Expr.get C (.nat 1)
  let R := Expr.get C (.nat 2)
  .arith .lt (.arith .sub (.arith .sub R I) (.nat 1))
    (.get (.get C (.nat 0)) (.arith .add (.arith .mul Pp K) (arg 1)))

/-- The label, on `[[cc, i], p]`: search over the points. -/
def cvLabF (bfind : ℕ) : Expr :=
  .call bfind (mk2 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1))
    (.get (.get (arg 0) (.nat 0)) (.nat 6)))

/-- The interval value, on `[cc, i]`: `[labels, c, cap, origin]`. -/
def cvF (bmap : ℕ) : Expr :=
  mk4 (.call bmap (mk2 (mk2 (arg 0) (arg 1)) (.get (arg 0) (.nat 6))))
    (.get (arg 0) (.nat 3)) (.get (arg 0) (.nat 4)) (.get (arg 0) (.nat 5))

theorem pair_val (p q : Fin k) : ((finProdFinEquiv (p, q) : Fin (k * k)) : ℕ) = p * k + q := by
  simp [finProdFinEquiv_apply_val]; ring

set_option maxHeartbeats 1000000 in
theorem cvTest_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some cvTestF)
    (lead : Fin (k * k) → ℕ) (r c cm o i : ℕ) (p q : Fin k) :
    FunDet P f (.list [.list [cvCtx lead r c cm o, .nat i, .nat p], .nat q])
      (boolVal (decide (r - i - 1 < lead (finProdFinEquiv (p, q)))))
      (100 * ((cvCtx lead r c cm o).wt + i + r + k * k + 10)) := by
  set cc := cvCtx lead r c cm o
  have dA := Det.arg' (P := P) (vs := [.list [cc, .nat i, .nat p], .nat q]) (rest := []) (j := 0) rfl
  have dQ := Det.arg' (P := P) (vs := [.list [cc, .nat i, .nat p], .nat q]) (rest := []) (j := 1) rfl
  have dC := Det.get' dA (Det.nat 0) (v := cc) rfl
  have dI := Det.get' dA (Det.nat 1) (v := .nat i) rfl
  have dP := Det.get' dA (Det.nat 2) (v := .nat p) rfl
  have dK := Det.get' dC (Det.nat 1) (v := .nat k) rfl
  have dR := Det.get' dC (Det.nat 2) (v := .nat r) rfl
  have dL := Det.get' dC (Det.nat 0) (v := encFun lead) rfl
  have hidx : (p : ℕ) * k + q < k * k := by rw [← pair_val]; exact (finProdFinEquiv (p, q)).2
  have dE := Det.get' dL (Det.arith' (op := .add) (Det.arith' (op := .mul) dP dK (z := p * k) rfl)
    dQ (z := p * k + q) rfl) (v := .nat (lead (finProdFinEquiv (p, q)))) (by
      have hl : (p : ℕ) * k + q < (List.finRange (k * k)).length := by simpa using hidx
      show ((List.finRange (k * k)).map fun j => Val.nat (lead j))[(p : ℕ) * k + q]? = _
      rw [List.getElem?_map, List.getElem?_eq_getElem hl]
      simp only [Option.map_some, List.getElem_finRange]
      congr 3
      exact Fin.ext (by simp only [pair_val, Fin.coe_cast]))
  have d := Det.arith' (op := .lt) (Det.arith' (op := .sub) (Det.arith' (op := .sub) dR dI
    (z := r - i) rfl) (Det.nat 1) (z := r - i - 1) rfl) dE
    (z := (decide (r - i - 1 < lead (finProdFinEquiv (p, q)))).toNat) (by
      simp only [GI.Machine.BinOp.eval]; split_ifs with h <;> simp [h])
  refine FunDet.intro hf (d.mono ?_)
  have wl : (Val.nat (lead (finProdFinEquiv (p, q)))).wt < (encFun lead).wt :=
    wt_le_wt_list (by simp [encFun])
  have wcl : (encFun lead).wt < cc.wt := wt_le_wt_list (by simp [cc, cvCtx])
  have wk : (Val.nat k).wt < cc.wt := wt_le_wt_list (by simp [cc, cvCtx])
  have wr : (Val.nat r).wt < cc.wt := wt_le_wt_list (by simp [cc, cvCtx])
  have w1 := wt_list2_le (.list [cc, .nat i, .nat p]) (.nat q)
  have w2 := wt_list3_le cc (.nat i) (.nat p)
  have := wt_nat_le i
  have := wt_nat_le p
  have := wt_nat_le q
  have := wt_nat_le 1
  have := p.2
  have := q.2
  have hpk : (p : ℕ) * k + q ≤ k * k := hidx.le
  have := Bool.toNat_le (decide (r - i - 1 < lead (finProdFinEquiv (p, q))))
  have := Nat.le_mul_self k
  omega

/-- The test of `cvTestF` on values. -/
def cvQ (lead : Fin (k * k) → ℕ) (r i : ℕ) (p : Fin k) : Val → Bool
  | .nat q => if h : q < k then decide (r - i - 1 < lead (finProdFinEquiv (p, ⟨q, h⟩))) else false
  | _ => false

theorem findIdx_cvQ (lead : Fin (k * k) → ℕ) (r i : ℕ) (p : Fin k) :
    ((List.finRange k).map fun q : Fin k => Val.nat q).findIdx (cvQ lead r i p) =
      coordLab lead r i p := by
  rw [List.findIdx_map, coordLab]
  congr 1
  funext q
  simp [cvQ, q.2]

/-- The constant of the labels. -/
def cvLabK : ℕ := 10 ^ 5

set_option maxHeartbeats 1000000 in
theorem cvLab_spec {P : Program} {f bfind ft : ℕ} (hf : P.funs[f]? = some (cvLabF bfind))
    (hfind : P.HasAt bfind (findFuns bfind ft)) (hft : P.funs[ft]? = some cvTestF)
    (lead : Fin (k * k) → ℕ) (r c cm o i : ℕ) (p : Fin k) :
    FunDet P f (.list [.list [cvCtx lead r c cm o, .nat i], .nat p]) (.nat (coordLab lead r i p))
      (cvLabK * ((cvCtx lead r c cm o).wt + i + r + k * k + 10) ^ 2) := by
  set cc := cvCtx lead r c cm o
  set ids : List Val := (List.finRange k).map fun q : Fin k => Val.nat q
  have hF := find_spec hfind (c := .list [cc, .nat i, .nat p]) (xs := ids) (q := cvQ lead r i p)
    (B := fun _ => 100 * (cc.wt + i + r + k * k + 10)) (fun x hx => by
      obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
      have := cvTest_spec hft lead r c cm o i p q
      simpa [cvQ, q.2] using this)
  have dA := Det.arg' (P := P) (vs := [.list [cc, .nat i], .nat p]) (rest := []) (j := 0) rfl
  have dP := Det.arg' (P := P) (vs := [.list [cc, .nat i], .nat p]) (rest := []) (j := 1) rfl
  have dC := Det.get' dA (Det.nat 0) (v := cc) rfl
  have dI := Det.get' dA (Det.nat 1) (v := .nat i) rfl
  have dIds := Det.get' dC (Det.nat 6) (v := .list ids) rfl
  have d := Det.call (Det.mk2 (Det.mk3 dC dI dP) dIds) (hF.mono fun w c h => h)
  rw [findIdx_cvQ] at d
  refine FunDet.intro hf (d.mono ?_)
  · have hlen : ids.length = k := by simp [ids]
    rw [hlen]
    have hs : (ids.map fun _ => 100 * (cc.wt + i + r + k * k + 10)).sum =
        k * (100 * (cc.wt + i + r + k * k + 10)) := by
      rw [List.map_const', List.sum_replicate, smul_eq_mul, hlen]
    rw [hs]
    have wid : (Val.list ids).wt < cc.wt := wt_le_wt_list (by simp [cc, cvCtx, ids, encFun])
    have wlead : (encFun lead).wt < cc.wt := wt_le_wt_list (by simp [cc, cvCtx])
    have hkk : k * k < (encFun lead).wt := by
      have := length_lt_wt_list ((List.finRange (k * k)).map fun j => Val.nat (lead j))
      simpa [encFun] using this
    have w1 := wt_list2_le (.list [cc, .nat i]) (.nat p)
    have w2 := wt_list2_le cc (.nat i)
    have w3 := wt_list3_le cc (.nat i) (.nat p)
    have w4 := wt_list2_le (.list [cc, .nat i, .nat p]) (.list ids)
    have := wt_nat_le i
    have := wt_nat_le p
    have := p.2
    have hcl : coordLab lead r i p ≤ k := by
      rw [coordLab]; exact List.findIdx_le_length.trans (by simp)
    have := wt_nat_le (coordLab lead r i p)
    have := Nat.le_mul_self k
    set Z := cc.wt + i + r + k * k + 10
    have hZ : 10 ≤ Z := by omega
    have m1 : k * (100 * Z) ≤ 100 * (Z * Z) := by
      have : k * Z ≤ Z * Z := Nat.mul_le_mul_right _ (by omega)
      calc k * (100 * Z) = 100 * (k * Z) := by ring
        _ ≤ 100 * (Z * Z) := by omega
    have m2 : loopModK * (k + 1) * ((Val.list [Val.list [cc, Val.nat i, Val.nat p], Val.list ids]).wt +
        2 * k + 3) ≤ 20000 * (Z * Z) := by
      have : 1000 * (k + 1) ≤ 1000 * Z := Nat.mul_le_mul_left _ (by omega)
      calc _ ≤ 1000 * Z * (20 * Z) := by
            simp only [loopModK]
            exact Nat.mul_le_mul this (by omega)
        _ = 20000 * (Z * Z) := by ring
    have hZZ : 10 * Z ≤ Z * Z := Nat.mul_le_mul_right _ hZ
    have e1 : Z ^ 2 = Z * Z := by ring
    simp only [cvLabK]
    rw [e1]
    omega

/-- The value of interval `i`. -/
def cvVal (lead : Fin (k * k) → ℕ) (r c cm o i : ℕ) : Val :=
  .list [encFun (coordLab lead r i), .nat c, .nat cm, .nat o]

theorem coordLab_le (lead : Fin (k * k) → ℕ) (r i : ℕ) (p : Fin k) : coordLab lead r i p ≤ k := by
  rw [coordLab]; exact List.findIdx_le_length.trans (by simp)

theorem wt_cvVal_le (lead : Fin (k * k) → ℕ) (r c cm o i : ℕ) :
    (cvVal lead r c cm o i).wt ≤ 20 * ((cvCtx lead r c cm o).wt + k * k + 10) := by
  set cc := cvCtx lead r c cm o
  have h1 := wt_encFun_le (coordLab lead r i) (coordLab_le lead r i)
  have h2 := wt_list4_le (encFun (coordLab lead r i)) (.nat c) (.nat cm) (.nat o)
  have wc : (Val.nat c).wt < cc.wt := wt_le_wt_list (by simp [cc, cvCtx])
  have wcm : (Val.nat cm).wt < cc.wt := wt_le_wt_list (by simp [cc, cvCtx])
  have wo : (Val.nat o).wt < cc.wt := wt_le_wt_list (by simp [cc, cvCtx])
  have : k * (2 * k + 5) ≤ 7 * (k * k) := by nlinarith [Nat.le_mul_self k]
  show (Val.list [encFun (coordLab lead r i), .nat c, .nat cm, .nat o]).wt ≤ _
  omega

theorem kk_lt_wt_cvCtx (lead : Fin (k * k) → ℕ) (r c cm o : ℕ) :
    k * k < (cvCtx lead r c cm o).wt := by
  have wlead : (encFun lead).wt < (cvCtx lead r c cm o).wt := wt_le_wt_list (by simp [cvCtx])
  have := length_lt_wt_list ((List.finRange (k * k)).map fun j => Val.nat (lead j))
  simp only [List.length_map, List.length_finRange] at this
  exact this.trans wlead

/-- The constant of one interval. -/
def cvFK : ℕ := 10 ^ 6

set_option maxHeartbeats 2000000 in
theorem cvF_spec {P : Program} {f bmap fl bfind ft : ℕ} (hf : P.funs[f]? = some (cvF bmap))
    (hmap : P.HasAt bmap (mapFuns bmap fl)) (hfl : P.funs[fl]? = some (cvLabF bfind))
    (hfind : P.HasAt bfind (findFuns bfind ft)) (hft : P.funs[ft]? = some cvTestF)
    (lead : Fin (k * k) → ℕ) (r c cm o i : ℕ) :
    FunDet P f (.list [cvCtx lead r c cm o, .nat i]) (cvVal lead r c cm o i)
      (cvFK * ((cvCtx lead r c cm o).wt + i + r + 10) ^ 3) := by
  set cc := cvCtx lead r c cm o
  set Y := cc.wt + i + r + 10 with hY
  have hkk : k * k < cc.wt := kk_lt_wt_cvCtx lead r c cm o
  have hYY : cc.wt + i + r + k * k + 10 ≤ 2 * Y := by omega
  set ids : List Val := (List.finRange k).map fun q : Fin k => Val.nat q
  have hM := map_det hmap (c := .list [cc, .nat i]) (xs := ids) (F := fun x => match x with
      | .nat q => if h : q < k then .nat (coordLab lead r i ⟨q, h⟩) else .nat 0
      | _ => .nat 0) (B := cvLabK * (cc.wt + i + r + k * k + 10) ^ 2) (fun x hx => by
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
    simpa [q.2] using cvLab_spec hfl hfind hft lead r c cm o i q)
  have hmv : ids.map (fun x => match x with
      | .nat q => if h : q < k then .nat (coordLab lead r i ⟨q, h⟩) else .nat 0
      | _ => .nat 0) = (List.finRange k).map fun q => Val.nat (coordLab lead r i q) := by
    simp [ids, List.map_map, Function.comp_def]
  rw [hmv] at hM
  have dA := Det.arg' (P := P) (vs := [cc, .nat i]) (rest := []) (j := 0) rfl
  have dI := Det.arg' (P := P) (vs := [cc, .nat i]) (rest := []) (j := 1) rfl
  have dIds := Det.get' dA (Det.nat 6) (v := .list ids) rfl
  have dMap := Det.call (Det.mk2 (Det.mk2 dA dI) dIds) hM
  have d := Det.mk4 dMap (Det.get' dA (Det.nat 3) (v := .nat c) rfl)
    (Det.get' dA (Det.nat 4) (v := .nat cm) rfl) (Det.get' dA (Det.nat 5) (v := .nat o) rfl)
  refine FunDet.intro hf (d.mono ?_)
  have hlen : ids.length = k := by simp [ids]
  rw [hlen]
  have e0 : Val.list ((List.finRange k).map fun q => Val.nat (coordLab lead r i q)) =
    encFun (coordLab lead r i) := rfl
  rw [e0]
  have wv := wt_cvVal_le lead r c cm o i
  have ev : (cvVal lead r c cm o i).wt =
    (Val.list [encFun (coordLab lead r i), .nat c, .nat cm, .nat o]).wt := rfl
  have h1 := wt_encFun_le (coordLab lead r i) (coordLab_le lead r i)
  have wid : (Val.list ids).wt < cc.wt := wt_le_wt_list (by simp [cc, cvCtx, ids, encFun])
  have wc : (Val.nat c).wt < cc.wt := wt_le_wt_list (by simp [cc, cvCtx])
  have wcm : (Val.nat cm).wt < cc.wt := wt_le_wt_list (by simp [cc, cvCtx])
  have wo : (Val.nat o).wt < cc.wt := wt_le_wt_list (by simp [cc, cvCtx])
  have w1 := wt_list2_le cc (.nat i)
  have w2 := wt_list2_le (.list [cc, .nat i]) (.list ids)
  have := wt_nat_le i
  have := wt_nat_le c
  have := Nat.le_mul_self k
  have hk7 : k * (2 * k + 5) ≤ 7 * (k * k) := by nlinarith [Nat.le_mul_self k]
  have hY10 : 10 ≤ Y := by omega
  -- the products
  have p2 : (cc.wt + i + r + k * k + 10) ^ 2 ≤ 4 * (Y * Y) := by
    calc _ ≤ (2 * Y) ^ 2 := Nat.pow_le_pow_left hYY 2
      _ = 4 * (Y * Y) := by ring
  have m1 : k * (cvLabK * (cc.wt + i + r + k * k + 10) ^ 2) ≤ cvLabK * 4 * (Y * Y * Y) := by
    calc _ ≤ Y * (cvLabK * (4 * (Y * Y))) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ p2)
      _ = cvLabK * 4 * (Y * Y * Y) := by ring
  have m2 : mapK * (k + 1) * ((Val.list [Val.list [cc, Val.nat i], Val.list ids]).wt +
      (encFun (coordLab lead r i)).wt + 1) ≤ 100000 * (Y * Y) := by
    calc _ ≤ 1000 * Y * (100 * Y) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 100000 * (Y * Y) := by ring
  have hYY2 : 10 * Y ≤ Y * Y := Nat.mul_le_mul_right _ hY10
  have hY3 : 10 * (Y * Y) ≤ Y * Y * Y := by nlinarith
  have e3 : Y ^ 3 = Y * Y * Y := by ring
  have hj : (cvCtx lead r c cm o).wt = cc.wt := rfl
  rw [e3]
  simp only [cvFK, cvLabK] at m1 ⊢
  omega

/-- All `r` intervals at base `b`: a loop over `i < r` that appends interval `i`. -/
def cvAllFuns (b fcv : ℕ) : List Expr :=
  loopFuns b (.get (.var 0) (.nat 2)) .nil (.snoc (arg 2) (.call fcv (mk2 (arg 0) (arg 1))))

/-- The constant of all intervals. -/
def cvAllK : ℕ := 10 ^ 8

set_option maxHeartbeats 2000000 in
theorem cvAll_spec {P : Program} {b fcv bmap fl bfind ft : ℕ}
    (hb : P.HasAt b (cvAllFuns b fcv)) (hf : P.funs[fcv]? = some (cvF bmap))
    (hmap : P.HasAt bmap (mapFuns bmap fl)) (hfl : P.funs[fl]? = some (cvLabF bfind))
    (hfind : P.HasAt bfind (findFuns bfind ft)) (hft : P.funs[ft]? = some cvTestF)
    (lead : Fin (k * k) → ℕ) (r c cm o : ℕ) :
    FunDet P b (cvCtx lead r c cm o) (.list ((List.range r).map (cvVal lead r c cm o)))
      (cvAllK * ((cvCtx lead r c cm o).wt + r + 10) ^ 4) := by
  obtain ⟨W, hW⟩ : ∃ W, W = (cvCtx lead r c cm o).wt := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = W + r + 10 := ⟨_, rfl⟩
  rw [← hW, ← hZ]
  have hkk : k * k < W := hW ▸ kk_lt_wt_cvCtx lead r c cm o
  have wv : ∀ i, (cvVal lead r c cm o i).wt ≤ 40 * Z := fun i => by
    have := wt_cvVal_le lead r c cm o i; omega
  obtain ⟨M, hM⟩ : ∃ M, M = r * (80 * Z + 1) + 4 := ⟨_, rfl⟩
  have hwl : ∀ i, i ≤ r → (Val.list ((List.range i).map (cvVal lead r c cm o))).wt ≤ M := by
    intro i hi
    have := wt_list_le_of ((List.range i).map (cvVal lead r c cm o)) (c := 40 * Z) (by
      intro v hv; obtain ⟨j, -, rfl⟩ := List.mem_map.1 hv; exact wv j)
    simp only [List.length_map, List.length_range] at this
    have : i * (2 * (40 * Z) + 1) ≤ r * (80 * Z + 1) := Nat.mul_le_mul hi (by omega)
    omega
  have wr : (Val.nat r).wt < (cvCtx lead r c cm o).wt := wt_le_wt_list (by simp [cvCtx])
  have hk : Det P [cvCtx lead r c cm o] (.get (.var 0) (.nat 2)) (.nat r) _ :=
    Det.get' (Det.var' (P := P) (env := [cvCtx lead r c cm o]) (i := 0) rfl) (Det.nat 2) rfl
  obtain ⟨D, hD⟩ : ∃ D, D = cvFK * (2 * Z) ^ 3 + 400 * Z + 4 * M := ⟨_, rfl⟩
  refine (loopBdd_spec hb hk (Det.nil (P := P) (env := [cvCtx lead r c cm o])) ?_ (M := M)
    (Inv := fun i acc => acc = .list ((List.range i).map (cvVal lead r c cm o)))
    (D := fun _ => D) (by simp) ?_ ?_).mono ?_
  · have := wt_nat_le r
    have hW2 : (Val.list [encFun lead, .nat k, .nat r, .nat c, .nat cm, .nat o,
      encFun fun p : Fin k => (p : ℕ)]).wt = W := hW ▸ rfl
    omega
  · rintro i acc hi rfl; exact hwl i hi
  · rintro i acc hi rfl
    obtain ⟨acc, hacc⟩ : ∃ acc, acc = (List.range i).map (cvVal lead r c cm o) := ⟨_, rfl⟩
    rw [← hacc]
    have dA := Det.arg' (P := P) (vs := [cvCtx lead r c cm o, .nat i, .list acc]) (rest := []) (j := 0) rfl
    have dI := Det.arg' (P := P) (vs := [cvCtx lead r c cm o, .nat i, .list acc]) (rest := []) (j := 1) rfl
    have dL := Det.arg' (P := P) (vs := [cvCtx lead r c cm o, .nat i, .list acc]) (rest := []) (j := 2) rfl
    have dc := Det.call (Det.mk2 dA dI) (cvF_spec hf hmap hfl hfind hft lead r c cm o i)
    have d := Det.snoc dL dc
    have hsnoc : acc ++ [cvVal lead r c cm o i] = (List.range (i + 1)).map (cvVal lead r c cm o) := by
      rw [hacc, List.range_succ, List.map_append, List.map_singleton]
    rw [hsnoc] at d
    refine d.post fun c' hc' => ⟨rfl, ?_⟩
    beta_reduce
    have h1 := hwl i hi.le
    have h2 := hwl (i + 1) hi
    rw [← hacc] at h1
    have h3 := wv i
    have w3 := wt_list3_le (cvCtx lead r c cm o) (.nat i) (.list acc)
    have w2 := wt_list2_le (cvCtx lead r c cm o) (.nat i)
    have := wt_nat_le i
    have p3 : ((cvCtx lead r c cm o).wt + i + r + 10) ^ 3 ≤ (2 * Z) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    have : cvFK * ((cvCtx lead r c cm o).wt + i + r + 10) ^ 3 ≤ cvFK * (2 * Z) ^ 3 :=
      Nat.mul_le_mul_left _ p3
    omega
  · rintro w cost ⟨rfl, hcost⟩
    refine ⟨rfl, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hcost
    have hZ10 : 10 ≤ Z := by omega
    have hrZ : r ≤ Z := by omega
    have hZ2 : 10 * Z ≤ Z * Z := Nat.mul_le_mul_right _ hZ10
    have hZ3 : 10 * (Z * Z) ≤ Z * Z * Z := by nlinarith
    have hZ4 : 10 * (Z * Z * Z) ≤ Z * Z * Z * Z := by nlinarith
    have hMZ : M ≤ 90 * (Z * Z) := by
      have : r * (80 * Z + 1) ≤ Z * (81 * Z) := Nat.mul_le_mul hrZ (by omega)
      have : Z * (81 * Z) = 81 * (Z * Z) := by ring
      omega
    have e8 : (2 * Z) ^ 3 = 8 * (Z * Z * Z) := by ring
    have m1 : r * D ≤ Z * (cvFK * (8 * (Z * Z * Z)) + 400 * Z + 360 * (Z * Z)) := by
      rw [hD, e8]; exact Nat.mul_le_mul hrZ (by omega)
    have e1 : Z * (cvFK * (8 * (Z * Z * Z)) + 400 * Z + 360 * (Z * Z)) =
        8 * cvFK * (Z * Z * Z * Z) + 400 * (Z * Z) + 360 * (Z * Z * Z) := by ring
    have m2 : loopModK * (r + 1) * ((cvCtx lead r c cm o).wt + r + M + 1) ≤
        1000 * Z * (100 * (Z * Z)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e2 : 1000 * Z * (100 * (Z * Z)) = 100000 * (Z * Z * Z) := by ring
    have e4 : Z ^ 4 = Z * Z * Z * Z := by ring
    rw [e4]
    simp only [cvAllK, cvFK] at m1 e1 ⊢
    omega

/-! ### The values are the coordinate intervals -/

section math

variable {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S) {m l r : ℕ}
  (E : Fin Q.d ≃ (Fin r → Product.KSet m l)) (e : Ω ≃ Fin k)

theorem coordLab_leadF {i : ℕ} (hi : i < r) :
    coordLab (leadF Q E e) r i = firstLab e (Q.coordPart E (i + 1)) := by
  classical
  funext p
  unfold coordLab firstLab
  congr 1
  funext q
  have h := coordPart_iff_plead Q E (s := i + 1) (by omega) (e.symm p) (e.symm q)
  have hl : leadF Q E e (finProdFinEquiv (p, q)) = plead Q E (e.symm p) (e.symm q) := by
    simp [leadF]
  rw [hl]
  by_cases hr : (Q.coordPart E (i + 1)).r (e.symm p) (e.symm q)
  · have := h.1 hr
    simp only [hr, decide_true, decide_eq_true_eq]
    omega
  · have := mt h.2 hr
    simp only [hr, decide_false, decide_eq_false_iff_not, not_lt]
    omega

/-- **The interval values are the coordinate intervals.** -/
theorem hierValC_coord :
    HierValC e (.list ((List.range r).map (cvVal (leadF Q E e) r (m.choose l)
      (min Q.top.cap (m.choose l)) Q.top.origin))) (Q.coordHier E) := by
  refine ⟨_, rfl, ?_⟩
  unfold PrimitiveQuotient.coordHier
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.2 fun i hi => ?_
  have hi' : i < r := List.mem_range.1 hi
  refine ⟨_, firstLab_partitionValC e _, ?_⟩
  rw [cvVal, coordLab_leadF Q E e hi']

end math

end GI.Impl
