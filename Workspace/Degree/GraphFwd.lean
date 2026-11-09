module

public import Workspace.Degree.GraphBase

/-!
# The table of forward neighbours

`fwdFuns a`: on `[[bv, adjVal Y, encPerm U], ids n]`, the value `fwdV ℓ (pull U Y)`.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n D : ℕ}

/-- The test, on `[[[bv, A, U], u], w]`: `ℓ w = ℓ u + 1` and `A (U u) (U w)`. -/
def fwdTestE : Expr :=
  let c := Expr.get (arg 0) (.nat 0)
  let B := Expr.get c (.nat 0)
  let L := Expr.get B (.nat 4)
  let A := Expr.get c (.nat 1)
  let U := Expr.get c (.nat 2)
  let u := Expr.get (arg 0) (.nat 1)
  .arith .mul (.arith .eq (.get L (arg 1)) (.arith .add (.get L u) (.nat 1)))
    (adjE A (.get U u) (.get U (arg 1)))

/-- A row, on `[[bv, A, U], u]`. -/
def fwdRowE (flt : ℕ) : Expr :=
  .call flt (mk2 (mk2 (arg 0) (arg 1)) (.get (.get (arg 0) (.nat 0)) (.nat 5)))

/-- The functions of the table. Eight functions. -/
def fwdFuns (a : ℕ) : List Expr :=
  tabFuns a (fwdRowE (a + 4)) ++ filterFuns (a + 4) (a + 7) ++ [fwdTestE]

/-- The cost of the test. -/
def fwdT (n : ℕ) : ℕ := 100000 * (WB n)

open Classical in
theorem fwd_eq (ℓ : Fin n → ℕ) (X : SimpleGraph (Fin n)) (u : Fin n) :
    fwd ℓ X u = (List.finRange n).filter fun z : Fin n =>
      @decide (X.Adj u z ∧ ℓ z = ℓ u + 1) (Classical.propDecidable _) := by
  unfold fwd
  apply List.filter_congr
  intro z _
  simp

/-- The test. -/
theorem fwdTest_lv {P : Program} (hS : Sz n D) {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ}
    (hr : r ≤ n) (Y : SimpleGraph (Fin n)) (U : Perm (Fin n)) (u w : Fin n) :
    Lv P [.list [.list [.list [bv D ℓ r, adjVal Y, encPerm U], .nat u], .nat w]] (fwdT n) fwdTestE
      (boolVal (@decide ((pull U Y).Adj u w ∧ ℓ w = ℓ u + 1) (Classical.propDecidable _))) 500 := by
  have h0 := WB_ge n
  have w0 := bv_wt hS hℓ hr
  have w1 := adjVal_wt Y
  have w2 : (encPerm U).wt ≤ WB n := perm_wt (by omega) U
  have w3 : (Val.nat u).wt ≤ WB n := fin_wt (by omega) u
  have w4 : (Val.nat w).wt ≤ WB n := fin_wt (by omega) w
  set vw : Val := .list [bv D ℓ r, adjVal Y, encPerm U] with hvw
  have w5 : vw.wt ≤ 3 * (2 * (40 * WB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have w6 : (Val.list [vw, .nat u]).wt ≤ 2 * (2 * (vw.wt + WB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have w7 : (Val.list [Val.list [vw, .nat u], .nat w]).wt ≤
      2 * (2 * ((Val.list [vw, .nat u]).wt + WB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hTv : fwdT n = 100000 * WB n := rfl
  set E := [Val.list [Val.list [vw, .nat u], .nat w]] with hE
  have a0 : Lv P E (fwdT n) (arg 0) (.list [vw, .nat u]) 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (fwdT n) (arg 1) (.nat w) 1 := Lv.arg rfl (by omega)
  have n0 : ∀ k, k ≤ 5 → Lv P E (fwdT n) (.nat k) (.nat k) 1 := fun k hk => Lv.nat k (by omega)
  have c0 := Lv.get (vs := [vw, .nat u]) a0 (n0 0 (by omega)) rfl
  have c1 := Lv.get (vs := [vw, .nat u]) a0 (n0 1 (by omega)) rfl
  have g0 := Lv.get (vs := [bv D ℓ r, adjVal Y, encPerm U]) c0 (n0 0 (by omega)) rfl
  have g1 := Lv.get (vs := [bv D ℓ r, adjVal Y, encPerm U]) c0 (n0 1 (by omega)) rfl
  have g2 := Lv.get (vs := [bv D ℓ r, adjVal Y, encPerm U]) c0 (n0 2 (by omega)) rfl
  have gL : Lv P E (fwdT n) _ (encFun ℓ) _ := Lv.bvGet g0 (j := 4) (by omega) rfl (by omega)
  have lw := Lv.tget gL a1
  have lu := Lv.tget gL c1
  have lu1 := Lv.arith (op := .add) (z := ℓ u + 1) lu (n0 1 (by omega)) rfl (by
    have := hℓ u
    omega)
  have he := Lv.arith (op := .eq) (z := if ℓ w = ℓ u + 1 then 1 else 0) lw lu1 rfl (by
    split <;> omega)
  have hA := Lv.aget g1 (Lv.pget g2 c1) (Lv.pget g2 a1)
  have hm := Lv.arith (op := .mul)
    (z := (@decide ((pull U Y).Adj u w ∧ ℓ w = ℓ u + 1) (Classical.propDecidable _)).toNat) he hA (by
      simp only [BinOp.eval, adjN, pull_adj]
      by_cases h1 : ℓ w = ℓ u + 1 <;> by_cases h2 : Y.Adj (U u) (U w) <;> simp [h1, h2])
    (by
      have := Bool.toNat_le (@decide ((pull U Y).Adj u w ∧ ℓ w = ℓ u + 1) (Classical.propDecidable _))
      omega)
  exact Lv.mono (e := fwdTestE) hm (by norm_num)

/-- The weights of a row. -/
def fwdW (n : ℕ) : ℕ := fwdT n + (n + 1) * (2 * WB n + 1) + 5

/-- The bound of a row. -/
def fwdRowC (n : ℕ) : ℕ := n * (500 * fwdT n) + loopModK * (n + 1) * fwdW n

/-- The budget of a row. -/
def fwdT1 (n : ℕ) : ℕ := fwdRowC n + fwdT n

/-- The bound of the table. -/
def fwdC (n : ℕ) : ℕ := n * (1000 * fwdT1 n) + mapK * (n + 1) * fwdW n

theorem fwdC_poly : PolyB fwdC := by
  have := WB_poly
  unfold fwdC fwdT1 fwdRowC fwdW fwdT
  poly

/-- **The table of forward neighbours.** -/
theorem fwd_spec {P : Program} {a : ℕ} (h : P.HasAt a (fwdFuns a)) (hS : Sz n D) {ℓ : Fin n → ℕ}
    (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ} (hr : r ≤ n) (Y : SimpleGraph (Fin n)) (U : Perm (Fin n)) :
    FunDet P a (.list [.list [bv D ℓ r, adjVal Y, encPerm U], ids n]) (fwdV ℓ (pull U Y)) (fwdC n) := by
  classical
  have hflt : P.HasAt (a + 4) (filterFuns (a + 4) (a + 7)) := h.left.right
  have htest : P.funs[a + 7]? = some fwdTestE := h.right.single
  have htab : P.HasAt a (tabFuns a (fwdRowE (a + 4))) := h.left.left
  have h0 := WB_ge n
  have w0 := bv_wt hS hℓ hr
  have w1 := adjVal_wt Y
  have w2 : (encPerm U).wt ≤ WB n := perm_wt (by omega) U
  have wi : (ids n).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  set vw : Val := .list [bv D ℓ r, adjVal Y, encPerm U] with hvw
  have w5 : vw.wt ≤ 3 * (2 * (40 * WB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hTv : fwdT n = 100000 * WB n := rfl
  have hF := fwdV_wt ℓ (pull U Y)
  have hw2 : (Val.list [vw, ids n]).wt ≤ 2 * (2 * (vw.wt + WB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  refine (tab_spec (m := n) (K := 1000) (T := fwdT1 n) (W := fwdW n)
    (F := fun u => flist (fwd ℓ (pull U Y) u)) htab (fun u => ?_) ?_).mono le_rfl
  · have w3 : (Val.nat u).wt ≤ WB n := fin_wt (by omega) u
    have w6 : (Val.list [vw, .nat u]).wt ≤ 2 * (2 * (vw.wt + WB n) + 1) + 4 :=
      wt_lit _ (by simp; omega)
    have w7 : (Val.list [Val.list [vw, .nat u], ids n]).wt ≤
        2 * (2 * ((Val.list [vw, .nat u]).wt + WB n) + 1) + 4 := wt_lit _ (by simp; omega)
    have hfl := flist_wt (n := n) (fwd ℓ (pull U Y) u) (length_fwd_le _ _ _) (by omega)
    have hT1 : fwdT n ≤ fwdT1 n := by simp only [fwdT1]; omega
    set E := [Val.list [vw, .nat u]] with hE
    have a0 : Lv P E (fwdT1 n) (arg 0) vw 1 := Lv.arg rfl (by omega)
    have a1 : Lv P E (fwdT1 n) (arg 1) (.nat u) 1 := Lv.arg rfl (by omega)
    have g0 := Lv.get (vs := [bv D ℓ r, adjVal Y, encPerm U]) a0 (Lv.nat 0 (by omega)) rfl
    have gi : Lv P E (fwdT1 n) _ (ids n) _ := Lv.bvGet g0 (j := 5) (by omega) rfl (by omega)
    have hcall := Lv.call (Lv.mk2 (Lv.mk2 a0 a1 (by omega)) gi (by omega))
      (filterFin_spec (W := fwdW n) (c := .list [vw, .nat u]) hflt
        (fun z : Fin n => (pull U Y).Adj u z ∧ ℓ z = ℓ u + 1) (B := 500 * fwdT n)
        (fun z => funDet_of_lv htest (fwdTest_lv hS hℓ hr Y U u z)) (by
          have h3 : WB n ≤ (n + 1) * (2 * WB n + 1) := by nlinarith
          rw [← fwd_eq]
          simp only [fwdW]
          omega))
      (by simp only [fwdT1, fwdRowC]; omega)
    rw [← fwd_eq] at hcall
    exact Lv.mono (e := fwdRowE (a + 4)) hcall (by norm_num)
  · simp only [fwdW]
    have e : (Val.list ((List.finRange n).map fun u => flist (fwd ℓ (pull U Y) u))).wt =
      (fwdV ℓ (pull U Y)).wt := rfl
    omega

end GI.Degree
