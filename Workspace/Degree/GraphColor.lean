module

public import Workspace.Degree.GraphFwd

/-!
# The string of a step

`colFuns a`: on `[[bv, adjVal Y, encPerm U, fV F], ids k]`, the table of `colorX` for the graph
`pull U Y`, where `F` is its table of forward neighbours.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n D : ℕ}

/-- `a / b`. -/
abbrev divE (a b : Expr) : Expr := .arith .div a b

/-- `a % b`. -/
abbrev modE (a b : Expr) : Expr := .arith .mod a b

/-- The entry of the string, on `[[bv, A, U, F], p]`. -/
def colE : Expr :=
  let c := arg 0
  let B := Expr.get c (.nat 0)
  let A := Expr.get c (.nat 1)
  let U := Expr.get c (.nat 2)
  let F := Expr.get c (.nat 3)
  let dd := Expr.get B (.nat 1)
  let mm := Expr.get B (.nat 2)
  let L := Expr.get B (.nat 4)
  let rr := Expr.get B (.nat 8)
  let s := divE (arg 1) mm
  let s' := modE (arg 1) mm
  let u := divE s dd
  let i := modE s dd
  let u' := divE s' dd
  let i' := modE s' dd
  let w := Expr.get (.get F u) i
  let w' := Expr.get (.get F u') i'
  .ite (.arith .mul (.arith .eq (.get L u) rr) (.arith .eq (.get L u') rr))
    (.ite (.arith .mul (.arith .lt i (.length (.get F u))) (.arith .lt i' (.length (.get F u'))))
      (.arith .add (.arith .add (.nat 2) (.arith .eq w w'))
        (.arith .mul (.nat 2) (adjE A (.get U w) (.get U w'))))
      (.nat 1))
    (.nat 0)

/-- The budget of an entry. -/
def colT (n : ℕ) : ℕ := 1000 * VB n

theorem Sz.five_le (h : Sz n D) : 5 ≤ n * D * (n * D) := by
  have h1 : 6 ≤ n * D := by
    have := Nat.le_mul_of_pos_left D h.pos
    have := h.six
    omega
  have := Nat.mul_le_mul h1 h1
  omega

set_option maxHeartbeats 1000000 in
/-- **An entry of the string.** -/
theorem colE_lv {P : Program} (hS : Sz n D) {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ}
    (hr : r ≤ n) (Y : SimpleGraph (Fin n)) (U : Perm (Fin n)) (F : Fin n → List (Fin n))
    (hF : ∀ u, (F u).length ≤ n) (p : Fin (n * D * (n * D))) :
    Lv P [.list [.list [bv D ℓ r, adjVal Y, encPerm U, fV F], .nat p]] (colT n) colE
      (.nat (colorX D ℓ r (pull U Y) F p)) 20000 := by
  classical
  have h0 := WB_ge n
  have hV := WB_le_VB n
  have w0 := bv_wt hS hℓ hr
  have w1 := adjVal_wt Y
  have w2 : (encPerm U).wt ≤ WB n := perm_wt (by omega) U
  have w3 : (fV F).wt ≤ VB n := by
    have := wt_listFin_le (fun u => flist (F u)) (B := WB n) fun u => flist_wt _ (hF u) (by omega)
    refine this.trans ?_
    simp only [VB]
    nlinarith
  have hk := hS.k_le
  have w4 : (Val.nat p).wt ≤ WB n := fin_wt (by omega) p
  set vw : Val := .list [bv D ℓ r, adjVal Y, encPerm U, fV F] with hvw
  have w5 : vw.wt ≤ 4 * (2 * VB n + 1) + 4 := wt_lit _ (by simp; omega)
  have w6 : (Val.list [vw, .nat p]).wt ≤ 2 * (2 * (vw.wt + WB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have hTv : colT n = 1000 * VB n := rfl
  set E := [Val.list [vw, .nat p]] with hE
  have hD : 0 < D := by have := hS.six; omega
  have hDm : D ≤ n * D := Nat.le_mul_of_pos_left _ hS.pos
  have a0 : Lv P E (colT n) (arg 0) vw 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (colT n) (arg 1) (.nat p) 1 := Lv.arg rfl (by omega)
  have n0 : ∀ k, k ≤ 8 → Lv P E (colT n) (.nat k) (.nat k) 1 := fun k hk => Lv.nat k (by omega)
  have gB := Lv.get (vs := [bv D ℓ r, adjVal Y, encPerm U, fV F]) a0 (n0 0 (by omega)) rfl
  have gA := Lv.get (vs := [bv D ℓ r, adjVal Y, encPerm U, fV F]) a0 (n0 1 (by omega)) rfl
  have gU := Lv.get (vs := [bv D ℓ r, adjVal Y, encPerm U, fV F]) a0 (n0 2 (by omega)) rfl
  have gF := Lv.get (vs := [bv D ℓ r, adjVal Y, encPerm U, fV F]) a0 (n0 3 (by omega)) rfl
  have gd : Lv P E (colT n) _ (.nat D) _ := Lv.bvGet gB (j := 1) (by omega) rfl (by omega)
  have gm : Lv P E (colT n) _ (.nat (n * D)) _ := Lv.bvGet gB (j := 2) (by omega) rfl (by omega)
  have gL : Lv P E (colT n) _ (encFun ℓ) _ := Lv.bvGet gB (j := 4) (by omega) rfl (by omega)
  have gr : Lv P E (colT n) _ (.nat r) _ := Lv.bvGet gB (j := 8) (by omega) rfl (by omega)
  -- the two slots
  set q := (pairE (n * D)).symm p with hq
  set s := (slotE n D).symm q.1 with hs
  set s' := (slotE n D).symm q.2 with hs'
  have hmk := hS.m_le_k
  have b1 := q.1.isLt
  have b2 := q.2.isLt
  have b3 := s.1.isLt
  have b4 := s'.1.isLt
  have ds := Lv.arith (op := .div) (z := q.1) a1 gm (pair_div p) (by omega)
  have ds' := Lv.arith (op := .mod) (z := q.2) a1 gm (pair_mod p) (by omega)
  have du := Lv.arith (op := .div) (z := s.1) ds gd (slot_div q.1) (by omega)
  have di := Lv.arith (op := .mod) (z := s.2) ds gd (slot_mod q.1) (by
    have := s.2.isLt; omega)
  have du' := Lv.arith (op := .div) (z := s'.1) ds' gd (slot_div q.2) (by omega)
  have di' := Lv.arith (op := .mod) (z := s'.2) ds' gd (slot_mod q.2) (by
    have := s'.2.isLt; omega)
  have lu := Lv.tget gL du
  have lu' := Lv.tget gL du'
  have e1 := Lv.arith (op := .eq) (z := if ℓ s.1 = r then 1 else 0) lu gr rfl (by split <;> omega)
  have e2 := Lv.arith (op := .eq) (z := if ℓ s'.1 = r then 1 else 0) lu' gr rfl (by split <;> omega)
  have hc : colorX D ℓ r (pull U Y) F p = slotColor ℓ r (pull U Y) F s s' := rfl
  rw [hc]
  by_cases hl : ℓ s.1 = r ∧ ℓ s'.1 = r
  · have t1 := Lv.arith (op := .mul) (z := 1) e1 e2 (by
      simp [BinOp.eval, hl.1, hl.2]) (by omega)
    have fu := Lv.fget gF du
    have fu' := Lv.fget gF du'
    have lf := Lv.flen fu (by omega)
    have lf' := Lv.flen fu' (by omega)
    have c1 := Lv.arith (op := .lt) (z := if (s.2 : ℕ) < (F s.1).length then 1 else 0) di lf rfl
      (by split <;> omega)
    have c2 := Lv.arith (op := .lt) (z := if (s'.2 : ℕ) < (F s'.1).length then 1 else 0) di' lf' rfl
      (by split <;> omega)
    by_cases h1 : (s.2 : ℕ) < (F s.1).length ∧ (s'.2 : ℕ) < (F s'.1).length
    · have t2 := Lv.arith (op := .mul) (z := 1) c1 c2 (by simp [BinOp.eval, h1.1, h1.2]) (by omega)
      obtain ⟨w, ht⟩ : ∃ w, tgt F s = some w := ⟨_, List.getElem?_eq_getElem h1.1⟩
      obtain ⟨w', ht'⟩ : ∃ w', tgt F s' = some w' := ⟨_, List.getElem?_eq_getElem h1.2⟩
      have ew := Lv.felem fu di (w := w) ht
      have ew' := Lv.felem fu' di' (w := w') ht'
      have eq1 := Lv.arith (op := .eq) (z := if w = w' then 1 else 0) ew ew' (by
        simp [BinOp.eval, Fin.ext_iff]) (by split <;> omega)
      have eA := Lv.aget gA (Lv.pget gU ew) (Lv.pget gU ew')
      have mA := Lv.arith (op := .mul) (n0 2 (by omega)) eA rfl (by
        have := adjN_le Y (U w) (U w')
        simp only [BinOp.eval]
        omega)
      have aA := Lv.arith (op := .add) (n0 2 (by omega)) eq1 rfl (by
        simp only [BinOp.eval]
        split <;> omega)
      have aB := Lv.arith (op := .add) (z := 2 + (if w = w' then 1 else 0) +
        2 * (if (pull U Y).Adj w w' then 1 else 0)) aA mA (by
          simp only [BinOp.eval, adjN, pull_adj]) (by
          split <;> split <;> omega)
      have hval : slotColor ℓ r (pull U Y) F s s' = 2 + (if w = w' then 1 else 0) +
          2 * (if (pull U Y).Adj w w' then 1 else 0) := by
        rw [slotColor_some hl.1 hl.2 ht ht']
        split_ifs <;> first | rfl | (exfalso; tauto)
      rw [hval]
      exact Lv.mono (e := colE) (Lv.ite_pos t1 (by omega) (Lv.ite_pos (e := .nat 1) t2 (by omega) aB))
        (by norm_num)
    · have h2 : tgt F s = none ∨ tgt F s' = none := by
        by_contra hc2
        push Not at hc2
        exact h1 ⟨by
          by_contra h3
          exact hc2.1 (by simp [tgt, show (F s.1).length ≤ (s.2 : ℕ) by omega]), by
          by_contra h3
          exact hc2.2 (by simp [tgt, show (F s'.1).length ≤ (s'.2 : ℕ) by omega])⟩
      have t2 := Lv.arith (op := .mul) (z := 0) c1 c2 (by
        simp only [BinOp.eval]
        by_cases h3 : (s.2 : ℕ) < (F s.1).length
        · by_cases h4 : (s'.2 : ℕ) < (F s'.1).length
          · exact absurd ⟨h3, h4⟩ h1
          · simp [h4]
        · simp [h3]) (by omega)
      rw [slotColor_none' hl.1 hl.2 h2]
      exact Lv.mono (e := colE) (Lv.ite_pos t1 (by omega)
        (Lv.ite_zero (t := _) t2 (n0 1 (by omega)))) (by norm_num)
  · have t1 := Lv.arith (op := .mul) (z := 0) e1 e2 (by
      simp only [BinOp.eval]
      by_cases h1 : ℓ s.1 = r <;> by_cases h2 : ℓ s'.1 = r <;> simp_all) (by omega)
    rw [slotColor_off hl]
    exact Lv.mono (e := colE) (Lv.ite_zero (t := _) t1 (n0 0 (by omega))) (by norm_num)

/-- The bound of the string. -/
def colC (n : ℕ) : ℕ := kB n * (20000 * colT n) + mapK * (kB n + 1) * colT n

theorem colC_poly : PolyB colC := by
  have := VB_poly
  unfold colC colT kB
  poly

/-- **The string.** -/
theorem col_spec {P : Program} {a : ℕ} (h : P.HasAt a (tabFuns a colE)) (hS : Sz n D)
    {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ} (hr : r ≤ n) (Y : SimpleGraph (Fin n))
    (U : Perm (Fin n)) (F : Fin n → List (Fin n)) (hF : ∀ u, (F u).length ≤ n) :
    FunDet P a (.list [.list [bv D ℓ r, adjVal Y, encPerm U, fV F], ids (n * D * (n * D))])
      (encFun (colorX D ℓ r (pull U Y) F)) (colC n) := by
  have h0 := WB_ge n
  have hV := WB_le_VB n
  have w0 := bv_wt hS hℓ hr
  have w1 := adjVal_wt Y
  have hk := hS.k_le
  have hk5 := hS.five_le
  have w2 : (encPerm U).wt ≤ WB n := perm_wt (by omega) U
  have w3 : (fV F).wt ≤ VB n := by
    have := wt_listFin_le (fun u => flist (F u)) (B := WB n) fun u => flist_wt _ (hF u) (by omega)
    refine this.trans ?_
    simp only [VB]
    nlinarith
  have w4 : (ids (n * D * (n * D))).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have w5 : (encFun (colorX D ℓ r (pull U Y) F)).wt ≤ WB n :=
    table_wt (by omega) fun p => (slotColor_le _ _).trans hk5
  have w6 : (Val.list [bv D ℓ r, adjVal Y, encPerm U, fV F]).wt ≤ 4 * (2 * VB n + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have w7 : (Val.list [Val.list [bv D ℓ r, adjVal Y, encPerm U, fV F], ids (n * D * (n * D))]).wt ≤
      2 * (2 * (4 * (2 * VB n + 1) + 4 + WB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hTv : colT n = 1000 * VB n := rfl
  refine (tabN_spec (W := colT n) h (fun p => colE_lv hS hℓ hr Y U F hF p) (by omega)).mono ?_
  have e1 := Nat.mul_le_mul_right (20000 * colT n) hk
  have e2 : mapK * (n * D * (n * D) + 1) * colT n ≤ mapK * (kB n + 1) * colT n :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  simp only [colC]
  omega

end GI.Degree
