module

public import Workspace.Degree.GraphColor

/-!
# The parent slots

`parFuns a`: on `[[bv, fV F], ids n]`, the table of `parNum`: for each vertex `w` the first slot of
level `r` whose target is `w`. `parSlot` is the same as a slot.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n D : ℕ}

/-- The slot `s` has level `r` and target `w`. -/
def parQ (D : ℕ) (ℓ : Fin n → ℕ) (r : ℕ) (F : Fin n → List (Fin n)) (w : Fin n)
    (s : Fin (n * D)) : Prop :=
  ℓ ((slotE n D).symm s).1 = r ∧ tgt F ((slotE n D).symm s) = some w

open Classical in
/-- The first such slot, or `n * D`. -/
noncomputable def parNum (D : ℕ) (ℓ : Fin n → ℕ) (r : ℕ) (F : Fin n → List (Fin n)) (w : Fin n) :
    ℕ :=
  (List.finRange (n * D)).findIdx fun s : Fin (n * D) => decide (parQ D ℓ r F w s)

/-- The parent as a slot. -/
noncomputable def parSlot (z : Fin n × Fin D) (ℓ : Fin n → ℕ) (r : ℕ) (F : Fin n → List (Fin n))
    (w : Fin n) : Fin n × Fin D :=
  if h : parNum D ℓ r F w < n * D then (slotE n D).symm ⟨_, h⟩ else z

theorem parNum_le (ℓ : Fin n → ℕ) (r : ℕ) (F : Fin n → List (Fin n)) (w : Fin n) :
    parNum D ℓ r F w ≤ n * D := findIdx_finRange_le _

/-- **The parents.** -/
theorem parSlot_ok {X : SimpleGraph (Fin n)} {ℓ : Fin n → ℕ} {r R : ℕ} (hX : HasLevels X ℓ R)
    (hr : r + 1 ≤ R) (z : Fin n × Fin D) (hD : ∀ u, (fwd ℓ X u).length ≤ D) {w : Fin n}
    (hw : ℓ w = r + 1) : parNum D ℓ r (fwd ℓ X) w < n * D ∧
      slotE n D (parSlot z ℓ r (fwd ℓ X) w) = parNum D ℓ r (fwd ℓ X) w ∧
      parQ D ℓ r (fwd ℓ X) w (slotE n D (parSlot z ℓ r (fwd ℓ X) w)) := by
  classical
  obtain ⟨par, hpar⟩ := exists_parOK hX hr z.2 hD
  have h1 : ∃ s, parQ D ℓ r (fwd ℓ X) w s := ⟨slotE n D (par w), by
    simpa [parQ] using hpar w hw⟩
  obtain ⟨hi, hq⟩ := findIdx_finRange (parQ D ℓ r (fwd ℓ X) w) h1
  have e : parSlot z ℓ r (fwd ℓ X) w = (slotE n D).symm ⟨_, hi⟩ := dif_pos hi
  refine ⟨hi, ?_, ?_⟩
  · rw [e]
    simp [parNum]
  · rw [e]
    simpa using hq

/-- `parSlot` satisfies `ParOK`. -/
theorem parSlot_parOK {X : SimpleGraph (Fin n)} {ℓ : Fin n → ℕ} {r R : ℕ} (hX : HasLevels X ℓ R)
    (hr : r + 1 ≤ R) (z : Fin n × Fin D) (hD : ∀ u, (fwd ℓ X u).length ≤ D) :
    ParOK ℓ r (fwd ℓ X) (parSlot z ℓ r (fwd ℓ X)) := fun w hw => by
  have := (parSlot_ok hX hr z hD hw).2.2
  simpa [parQ] using this

/-- The test, on `[[[bv, F], w], s]`. -/
def parTestE : Expr :=
  let c := Expr.get (arg 0) (.nat 0)
  let B := Expr.get c (.nat 0)
  let F := Expr.get c (.nat 1)
  let w := Expr.get (arg 0) (.nat 1)
  let dd := Expr.get B (.nat 1)
  let L := Expr.get B (.nat 4)
  let rr := Expr.get B (.nat 8)
  let u := divE (arg 1) dd
  let i := modE (arg 1) dd
  .ite (.arith .eq (.get L u) rr)
    (.ite (.arith .lt i (.length (.get F u))) (.arith .eq (.get (.get F u) i) w) (.nat 0)) (.nat 0)

/-- An entry, on `[[bv, F], w]`. -/
def parEntryE (fd : ℕ) : Expr :=
  .call fd (mk2 (mk2 (arg 0) (arg 1)) (.get (.get (arg 0) (.nat 0)) (.nat 6)))

/-- The functions of the table. Eight functions. -/
def parFuns (a : ℕ) : List Expr :=
  tabFuns a (parEntryE (a + 4)) ++ findFuns (a + 4) (a + 7) ++ [parTestE]

/-- The budget of the test. -/
def parT (n : ℕ) : ℕ := 1000 * VB n

theorem fV_wt {F : Fin n → List (Fin n)} (hF : ∀ u, (F u).length ≤ n) : (fV F).wt ≤ VB n := by
  have := wt_listFin_le (fun u => flist (F u)) (B := WB n) fun u => flist_wt _ (hF u) (by omega)
  refine this.trans ?_
  simp only [VB]
  nlinarith

set_option maxHeartbeats 1000000 in
/-- The test. -/
theorem parTest_lv {P : Program} (hS : Sz n D) {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ}
    (hr : r ≤ n) (F : Fin n → List (Fin n)) (hF : ∀ u, (F u).length ≤ n) (w : Fin n)
    (s : Fin (n * D)) :
    Lv P [.list [.list [.list [bv D ℓ r, fV F], .nat w], .nat s]] (parT n) parTestE
      (boolVal (@decide (parQ D ℓ r F w s) (Classical.propDecidable _))) 2000 := by
  classical
  have h0 := WB_ge n
  have hV := WB_le_VB n
  have w0 := bv_wt hS hℓ hr
  have w3 := fV_wt hF
  have hk := hS.k_le
  have hmk := hS.m_le_k
  have w4 : (Val.nat w).wt ≤ WB n := fin_wt (by omega) w
  have w5 : (Val.nat s).wt ≤ WB n := fin_wt (by omega) s
  set vw : Val := .list [bv D ℓ r, fV F] with hvw
  have w6 : vw.wt ≤ 2 * (2 * VB n + 1) + 4 := wt_lit _ (by simp; omega)
  have w7 : (Val.list [vw, .nat w]).wt ≤ 2 * (2 * (vw.wt + WB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have w8 : (Val.list [Val.list [vw, .nat w], .nat s]).wt ≤
      2 * (2 * ((Val.list [vw, .nat w]).wt + WB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hTv : parT n = 1000 * VB n := rfl
  set E := [Val.list [Val.list [vw, .nat w], .nat s]] with hE
  have hD : 0 < D := by have := hS.six; omega
  have hDm : D ≤ n * D := Nat.le_mul_of_pos_left _ hS.pos
  have a0 : Lv P E (parT n) (arg 0) (.list [vw, .nat w]) 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (parT n) (arg 1) (.nat s) 1 := Lv.arg rfl (by omega)
  have n0 : ∀ k, k ≤ 8 → Lv P E (parT n) (.nat k) (.nat k) 1 := fun k hk => Lv.nat k (by omega)
  have c0 := Lv.get (vs := [vw, .nat w]) a0 (n0 0 (by omega)) rfl
  have cw := Lv.get (vs := [vw, .nat w]) a0 (n0 1 (by omega)) rfl
  have gB := Lv.get (vs := [bv D ℓ r, fV F]) c0 (n0 0 (by omega)) rfl
  have gF := Lv.get (vs := [bv D ℓ r, fV F]) c0 (n0 1 (by omega)) rfl
  have gd : Lv P E (parT n) _ (.nat D) _ := Lv.bvGet gB (j := 1) (by omega) rfl (by omega)
  have gL : Lv P E (parT n) _ (encFun ℓ) _ := Lv.bvGet gB (j := 4) (by omega) rfl (by omega)
  have gr : Lv P E (parT n) _ (.nat r) _ := Lv.bvGet gB (j := 8) (by omega) rfl (by omega)
  set q := (slotE n D).symm s with hq
  have b3 := q.1.isLt
  have b4 := q.2.isLt
  have du := Lv.arith (op := .div) (z := q.1) a1 gd (slot_div s) (by omega)
  have di := Lv.arith (op := .mod) (z := q.2) a1 gd (slot_mod s) (by omega)
  have lu := Lv.tget gL du
  have e1 := Lv.arith (op := .eq) (z := if ℓ q.1 = r then 1 else 0) lu gr rfl (by split <;> omega)
  have fu := Lv.fget gF du
  have lf := Lv.flen fu (by omega)
  have c1 := Lv.arith (op := .lt) (z := if (q.2 : ℕ) < (F q.1).length then 1 else 0) di lf rfl
    (by split <;> omega)
  have hval : ∀ b : Prop, ¬b → boolVal (@decide b (Classical.propDecidable _)) = .nat 0 := by
    intro b hb
    simp [hb]
  by_cases hl : ℓ q.1 = r
  · rw [if_pos hl] at e1
    by_cases hi : (q.2 : ℕ) < (F q.1).length
    · rw [if_pos hi] at c1
      obtain ⟨w0, ht⟩ : ∃ w0, tgt F q = some w0 := ⟨_, List.getElem?_eq_getElem hi⟩
      have ew := Lv.felem fu di (w := w0) ht
      have eq1 := Lv.arith (op := .eq)
        (z := (@decide (parQ D ℓ r F w s) (Classical.propDecidable _)).toNat) ew cw (by
          simp only [BinOp.eval, parQ, ← hq, hl, ht, true_and, Option.some.injEq, Fin.ext_iff]
          by_cases h3 : (w0 : ℕ) = w <;> simp [h3]) (by
          have := Bool.toNat_le (@decide (parQ D ℓ r F w s) (Classical.propDecidable _))
          omega)
      exact Lv.mono (e := parTestE) (Lv.ite_pos e1 (by omega)
        (Lv.ite_pos (e := .nat 0) c1 (by omega) eq1)) (by norm_num)
    · rw [if_neg hi] at c1
      have ht : tgt F q = none := by
        simp [tgt, show (F q.1).length ≤ (q.2 : ℕ) by omega]
      rw [hval _ (by simp [parQ, ← hq, ht])]
      exact Lv.mono (e := parTestE) (Lv.ite_pos e1 (by omega)
        (Lv.ite_zero (t := _) c1 (n0 0 (by omega)))) (by norm_num)
  · rw [if_neg hl] at e1
    rw [hval _ (by simp [parQ, ← hq, hl])]
    exact Lv.mono (e := parTestE) (Lv.ite_zero (t := _) e1 (n0 0 (by omega))) (by norm_num)

/-- The weight of the context of the table. -/
def parW (n : ℕ) : ℕ := parT n

/-- The bound of an entry. -/
def parRowC (n : ℕ) : ℕ := kB n * (2000 * parT n) + loopModK * (kB n + 1) * (parT n + 2 * kB n + 3)

/-- The budget of an entry. -/
def parT1 (n : ℕ) : ℕ := parRowC n + parT n

/-- The bound of the table. -/
def parC (n : ℕ) : ℕ := n * (1000 * parT1 n) + mapK * (n + 1) * parT n

theorem parC_poly : PolyB parC := by
  have := VB_poly
  unfold parC parT1 parRowC parT kB
  poly

theorem parT_le_T1 (n : ℕ) : parT n ≤ parT1 n := by
  simp only [parT1]; omega

/-- **The table of the parents.** -/
theorem par_spec {P : Program} {a : ℕ} (h : P.HasAt a (parFuns a)) (hS : Sz n D) {ℓ : Fin n → ℕ}
    (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ} (hr : r ≤ n) (F : Fin n → List (Fin n))
    (hF : ∀ u, (F u).length ≤ n) :
    FunDet P a (.list [.list [bv D ℓ r, fV F], ids n]) (encFun (parNum D ℓ r F)) (parC n) := by
  classical
  have hfd : P.HasAt (a + 4) (findFuns (a + 4) (a + 7)) := h.left.right
  have htest : P.funs[a + 7]? = some parTestE := h.right.single
  have htab : P.HasAt a (tabFuns a (parEntryE (a + 4))) := h.left.left
  have h0 := WB_ge n
  have hV := WB_le_VB n
  have w0 := bv_wt hS hℓ hr
  have w3 := fV_wt hF
  have hk := hS.k_le
  have hmk := hS.m_le_k
  have hTv : parT n = 1000 * VB n := rfl
  have hT1 := parT_le_T1 n
  have wi : (ids n).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have wm : (ids (n * D)).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  set vw : Val := .list [bv D ℓ r, fV F] with hvw
  have w6 : vw.wt ≤ 2 * (2 * VB n + 1) + 4 := wt_lit _ (by simp; omega)
  have w7 : (Val.list [vw, ids n]).wt ≤ 2 * (2 * (vw.wt + WB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have w8 : (encFun (parNum D ℓ r F)).wt ≤ WB n :=
    table_wt' (B := n * D) (by omega) (by omega) fun w => parNum_le ℓ r F w
  refine (tabN_spec (W := parT n) (K := 1000) (T := parT1 n) htab (fun w => ?_) (by omega)).mono
    (by simp only [parC]; omega)
  have w4 : (Val.nat w).wt ≤ WB n := fin_wt (by omega) w
  have w9 : (Val.list [vw, .nat w]).wt ≤ 2 * (2 * (vw.wt + WB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have w10 : (Val.list [Val.list [vw, .nat w], ids (n * D)]).wt ≤
      2 * (2 * ((Val.list [vw, .nat w]).wt + WB n) + 1) + 4 := wt_lit _ (by simp; omega)
  set E := [Val.list [vw, .nat w]] with hE
  have a0 : Lv P E (parT1 n) (arg 0) vw 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (parT1 n) (arg 1) (.nat w) 1 := Lv.arg rfl (by omega)
  have g0 := Lv.get (vs := [bv D ℓ r, fV F]) a0 (Lv.nat 0 (by omega)) rfl
  have gi : Lv P E (parT1 n) _ (ids (n * D)) _ := Lv.bvGet g0 (j := 6) (by omega) rfl (by omega)
  have hcall := Lv.call (Lv.mk2 (Lv.mk2 a0 a1 (by omega)) gi (by omega))
    (findFin_spec (c := .list [vw, .nat w]) hfd (parQ D ℓ r F w) (B := 2000 * parT n)
      (fun s => funDet_of_lv htest (parTest_lv hS hℓ hr F hF w s)))
    (by
      have e1 := Nat.mul_le_mul_right (2000 * parT n) (show n * D ≤ kB n by omega)
      have e2 : loopModK * (n * D + 1) * ((Val.list [Val.list [vw, .nat w], ids (n * D)]).wt +
          2 * (n * D) + 3) ≤ loopModK * (kB n + 1) * (parT n + 2 * kB n + 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      simp only [parT1, parRowC]
      omega)
  exact Lv.mono (e := parEntryE (a + 4)) hcall (by norm_num)

end GI.Degree
