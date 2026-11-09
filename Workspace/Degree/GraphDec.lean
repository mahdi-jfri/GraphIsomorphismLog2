module

public import Workspace.Degree.GraphGens

/-!
# Reading a map off a query answer

`decFuns a`: on `[[bv, fV F, encFun pn], encPerm (diag g)]`, the map `dec g` of Lemma 9.2 as a
permutation of the vertices.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n D : ℕ}

/-- The slot number of the image of the slot number `x`, under `t = diag g`. -/
def rdE (tt mm x : Expr) : Expr :=
  modE (.get tt (.arith .add x (.arith .mul mm x))) mm

/-- The entry of `dec`, on `[[[bv, F, pn], t], u]`. -/
def decE : Expr :=
  let c := Expr.get (arg 0) (.nat 0)
  let tt := Expr.get (arg 0) (.nat 1)
  let B := Expr.get c (.nat 0)
  let F := Expr.get c (.nat 1)
  let pn := Expr.get c (.nat 2)
  let dd := Expr.get B (.nat 1)
  let mm := Expr.get B (.nat 2)
  let L := Expr.get B (.nat 4)
  let rr := Expr.get B (.nat 8)
  let u := arg 1
  let z := rdE tt mm (.get pn u)
  let r1 := Expr.arith .add rr (.nat 1)
  .ite (.arith .lt (.get L u) r1) (divE (rdE tt mm (.arith .mul dd u)) dd)
    (.ite (.arith .eq (.get L u) r1)
      (.ite (.arith .lt (modE z dd) (.length (.get F (divE z dd))))
        (.get (.get F (divE z dd)) (modE z dd)) u)
      u)

/-- The action read off the diagonal. -/
theorem diag_rd (g : Perm (Fin n × Fin D)) (x : Fin (n * D)) :
    ((diag n D g (pairE (n * D) (x, x)) : ℕ)) % (n * D) = slotE n D (g ((slotE n D).symm x)) := by
  obtain ⟨s, rfl⟩ := (slotE n D).surjective x
  rw [diag_apply, pairE_val, Nat.add_mul_mod_self_left]
  simp [Nat.mod_eq_of_lt]

/-- The expression `rdE`. -/
theorem rdE_lv {P : Program} {env : List Val} {T : ℕ} (hS : Sz n D) {e tt mm : Expr}
    {x : Fin (n * D)} {g : Perm (Fin n × Fin D)} (he : Lv P env T e (.nat x) 40)
    (ht : Lv P env T tt (encPerm (diag n D g)) 40) (hm : Lv P env T mm (.nat (n * D)) 40)
    (hT : n * D * (n * D) + 10 ≤ T) :
    Lv P env T (rdE tt mm e) (.nat (slotE n D (g ((slotE n D).symm x)))) 800 := by
  have hx := x.isLt
  have hxm : n * D * (x : ℕ) ≤ n * D * (n * D) := Nat.mul_le_mul_left _ hx.le
  have mu := Lv.arith (op := .mul) hm he rfl (by simp only [BinOp.eval]; omega)
  have hp := (pairE (n * D) (x, x)).isLt
  have hv := pairE_val x x
  have ad := Lv.arith (op := .add) (z := pairE (n * D) (x, x)) he mu hv.symm (by omega)
  have gt := Lv.pget ht ad
  have hs := (slotE n D (g ((slotE n D).symm x))).isLt
  have hmk := hS.m_le_k
  have md := Lv.arith (op := .mod) (z := slotE n D (g ((slotE n D).symm x))) gt hm (diag_rd g x)
    (by omega)
  exact Lv.mono (e := rdE tt mm e) md (by norm_num)

/-- The context of `dec`. -/
def decCtx (D : ℕ) (ℓ : Fin n → ℕ) (r : ℕ) (F : Fin n → List (Fin n)) (pn : Fin n → ℕ) : Val :=
  .list [bv D ℓ r, fV F, encFun pn]

/-- The budget of an entry. -/
def decT (n : ℕ) : ℕ := 1000 * VB n

theorem decCtx_wt (hS : Sz n D) {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ} (hr : r ≤ n)
    {F : Fin n → List (Fin n)} (hF : ∀ u, (F u).length ≤ n) {pn : Fin n → ℕ}
    (hpn : ∀ u, pn u ≤ n * D) : (decCtx D ℓ r F pn).wt ≤ 3 * (2 * VB n + 1) + 4 := by
  have h0 := WB_ge n
  have hV := WB_le_VB n
  have w0 := bv_wt hS hℓ hr
  have w3 := fV_wt hF
  have hk := hS.k_le
  have hmk := hS.m_le_k
  have w4 : (encFun pn).wt ≤ WB n := table_wt' (B := n * D) (by omega) (by omega) hpn
  exact wt_lit _ (by simp; omega)

set_option maxHeartbeats 1000000 in
/-- **An entry of `dec`.** -/
theorem decE_lv {P : Program} (hS : Sz n D) (hD : 0 < D) {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n)
    {r : ℕ} (hr : r ≤ n) {F : Fin n → List (Fin n)} (hF : ∀ u, (F u).length ≤ n)
    {pn : Fin n → ℕ} (hpn : ∀ u, pn u ≤ n * D) {par : Fin n → Fin n × Fin D}
    (hpar : ∀ w, ℓ w = r + 1 → (slotE n D (par w) : ℕ) = pn w) (g : Perm (Fin n × Fin D))
    (u : Fin n) :
    Lv P [.list [.list [decCtx D ℓ r F pn, encPerm (diag n D g)], .nat u]] (decT n) decE
      (.nat ((decMap ℓ r F par (z0 hD) g u : Fin n) : ℕ)) 200000 := by
  classical
  have h0 := WB_ge n
  have hV := WB_le_VB n
  have hk := hS.k_le
  have hmk := hS.m_le_k
  have w0 := decCtx_wt hS hℓ hr hF hpn
  have w1 : (encPerm (diag n D g)).wt ≤ WB n := perm_wt (by omega) _
  have w2 : (Val.nat u).wt ≤ WB n := fin_wt (by omega) u
  set cv := decCtx D ℓ r F pn with hcv
  have w3 : (Val.list [cv, encPerm (diag n D g)]).wt ≤ 2 * (2 * (cv.wt + WB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have w4 : (Val.list [Val.list [cv, encPerm (diag n D g)], .nat u]).wt ≤
      2 * (2 * ((Val.list [cv, encPerm (diag n D g)]).wt + WB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have hTv : decT n = 1000 * VB n := rfl
  set E := [Val.list [Val.list [cv, encPerm (diag n D g)], .nat u]] with hE
  have hDm : D ≤ n * D := Nat.le_mul_of_pos_left _ hS.pos
  have a0 : Lv P E (decT n) (arg 0) (.list [cv, encPerm (diag n D g)]) 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (decT n) (arg 1) (.nat u) 1 := Lv.arg rfl (by omega)
  have n0 : ∀ k, k ≤ 8 → Lv P E (decT n) (.nat k) (.nat k) 1 := fun k hk => Lv.nat k (by omega)
  have c0 := Lv.get (vs := [cv, encPerm (diag n D g)]) a0 (n0 0 (by omega)) rfl
  have tt := Lv.get (vs := [cv, encPerm (diag n D g)]) a0 (n0 1 (by omega)) rfl
  have gB := Lv.get (vs := [bv D ℓ r, fV F, encFun pn]) c0 (n0 0 (by omega)) rfl
  have gF := Lv.get (vs := [bv D ℓ r, fV F, encFun pn]) c0 (n0 1 (by omega)) rfl
  have gp := Lv.get (vs := [bv D ℓ r, fV F, encFun pn]) c0 (n0 2 (by omega)) rfl
  have gd : Lv P E (decT n) _ (.nat D) _ := Lv.bvGet gB (j := 1) (by omega) rfl (by omega)
  have gm : Lv P E (decT n) _ (.nat (n * D)) _ := Lv.bvGet gB (j := 2) (by omega) rfl (by omega)
  have gL : Lv P E (decT n) _ (encFun ℓ) _ := Lv.bvGet gB (j := 4) (by omega) rfl (by omega)
  have gr : Lv P E (decT n) _ (.nat r) _ := Lv.bvGet gB (j := 8) (by omega) rfl (by omega)
  have lu := Lv.tget gL a1
  have r1 := Lv.arith (op := .add) (z := r + 1) gr (n0 1 (by omega)) rfl (by omega)
  by_cases h1 : ℓ u ≤ r
  · have t1 := Lv.arith (op := .lt) (z := 1) lu r1 (by simp [BinOp.eval, show ℓ u < r + 1 by omega])
      (by omega)
    have hzv : D * (u : ℕ) = (slotE n D (u, z0 hD) : ℕ) := by
      rw [slotE_val]
      simp [z0]
    have hzb := (slotE n D (u, z0 hD)).isLt
    have mu := Lv.arith (op := .mul) (z := slotE n D (u, z0 hD)) gd a1 hzv (by omega)
    have rd := rdE_lv hS (Lv.mono mu (by norm_num)) (Lv.mono tt (by norm_num))
      (Lv.mono gm (by norm_num)) (by omega)
    rw [Equiv.symm_apply_apply] at rd
    have dv := Lv.arith (op := .div) (z := (g (u, z0 hD)).1) rd gd (by
      have := slot_div (slotE n D (g (u, z0 hD)))
      rw [Equiv.symm_apply_apply] at this
      exact this) (by have := (g (u, z0 hD)).1.isLt; omega)
    have e1 : decMap ℓ r F par (z0 hD) g u = (g (u, z0 hD)).1 := by
      simp [decMap, h1]
    rw [e1]
    exact Lv.mono (e := decE) (Lv.ite_pos t1 (by omega) dv) (by norm_num)
  · have t1 := Lv.arith (op := .lt) (z := 0) lu r1 (by simp [BinOp.eval]; omega) (by omega)
    have e2 := Lv.arith (op := .eq) (z := if ℓ u = r + 1 then 1 else 0) lu r1 rfl (by
      split <;> omega)
    by_cases h2 : ℓ u = r + 1
    · rw [if_pos h2] at e2
      have hp := hpar u h2
      have pu := Lv.tget gp a1
      rw [← hp] at pu
      have rd := rdE_lv hS (Lv.mono pu (by norm_num)) (Lv.mono tt (by norm_num))
        (Lv.mono gm (by norm_num)) (by omega)
      rw [Equiv.symm_apply_apply] at rd
      set q := g (par u) with hq
      have hq1 := q.1.isLt
      have hq2 := q.2.isLt
      have du := Lv.arith (op := .div) (z := q.1) rd gd (by
        have := slot_div (slotE n D q)
        rw [Equiv.symm_apply_apply] at this
        exact this) (by omega)
      have di := Lv.arith (op := .mod) (z := q.2) rd gd (by
        have := slot_mod (slotE n D q)
        rw [Equiv.symm_apply_apply] at this
        exact this) (by omega)
      have fu := Lv.fget gF du
      have lf := Lv.flen fu (by omega)
      have hF1 := hF q.1
      by_cases h3 : (q.2 : ℕ) < (F q.1).length
      · have c1 := Lv.arith (op := .lt) (z := 1) di lf (by simp [BinOp.eval, h3]) (by omega)
        obtain ⟨w0', ht⟩ : ∃ w, tgt F q = some w := ⟨_, List.getElem?_eq_getElem h3⟩
        have ew := Lv.felem fu di (w := w0') ht
        have e3 : decMap ℓ r F par (z0 hD) g u = w0' := by
          simp [decMap, h1, h2, ← hq, ht]
        rw [e3]
        have i1 := Lv.ite_pos (e := arg 1) c1 (by omega) ew
        have i2 := Lv.ite_pos (e := arg 1) e2 (by omega) i1
        exact Lv.mono (e := decE) (Lv.ite_zero (t := _) t1 i2) (by norm_num)
      · have c1 := Lv.arith (op := .lt) (z := 0) di lf (by
          simp only [BinOp.eval]
          exact if_neg h3) (by omega)
        have ht : tgt F q = none := by
          simp [tgt, show (F q.1).length ≤ (q.2 : ℕ) by omega]
        have e3 : decMap ℓ r F par (z0 hD) g u = u := by
          simp [decMap, h1, h2, ← hq, ht]
        rw [e3]
        exact Lv.mono (e := decE) (Lv.ite_zero (t := _) t1 (Lv.ite_pos (e := arg 1) e2 (by omega)
          (Lv.ite_zero (t := _) c1 a1))) (by norm_num)
    · rw [if_neg h2] at e2
      have e3 : decMap ℓ r F par (z0 hD) g u = u := by
        simp [decMap, h1, h2]
      rw [e3]
      exact Lv.mono (e := decE) (Lv.ite_zero (t := _) t1 (Lv.ite_zero (t := _) e2 a1)) (by norm_num)

/-- A row of `dec`, on `[[bv, F, pn], t]`. -/
def decRowE (t : ℕ) : Expr :=
  .call t (mk2 (mk2 (arg 0) (arg 1)) (.get (.get (arg 0) (.nat 0)) (.nat 5)))

/-- The functions of `dec`. Five functions. -/
def decFuns (a : ℕ) : List Expr := [decRowE (a + 1)] ++ tabFuns (a + 1) decE

/-- The bound of the table. -/
def decTabC (n : ℕ) : ℕ := n * (200000 * decT n) + mapK * (n + 1) * decT n

/-- The budget of a row. -/
def decT1 (n : ℕ) : ℕ := decTabC n + decT n

/-- The bound of `dec`. -/
def decC (n : ℕ) : ℕ := 1000 * decT1 n

theorem decC_poly : PolyB decC := by
  have := VB_poly
  unfold decC decT1 decTabC decT
  poly

/-- **The map `dec`.** -/
theorem dec_spec {P : Program} {a : ℕ} (h : P.HasAt a (decFuns a)) (hS : Sz n D) (hD : 0 < D)
    {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ} (hr : r ≤ n) {F : Fin n → List (Fin n)}
    (hF : ∀ u, (F u).length ≤ n) {pn : Fin n → ℕ} (hpn : ∀ u, pn u ≤ n * D)
    {par : Fin n → Fin n × Fin D} (hpar : ∀ w, ℓ w = r + 1 → (slotE n D (par w) : ℕ) = pn w)
    (g : Perm (Fin n × Fin D)) {e : Perm (Fin n)}
    (he : ∀ u, e u = decMap ℓ r F par (z0 hD) g u) :
    FunDet P a (.list [decCtx D ℓ r F pn, encPerm (diag n D g)]) (encPerm e) (decC n) := by
  have hR : P.funs[a]? = some (decRowE (a + 1)) := h.left.single
  have hT : P.HasAt (a + 1) (tabFuns (a + 1) decE) := h.right
  have h0 := WB_ge n
  have hV := WB_le_VB n
  have hk := hS.k_le
  have hmk := hS.m_le_k
  have w0 := decCtx_wt hS hℓ hr hF hpn
  have w1 : (encPerm (diag n D g)).wt ≤ WB n := perm_wt (by omega) _
  have wi : (ids n).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have wb := bv_wt hS hℓ hr
  set cv := decCtx D ℓ r F pn with hcv
  have w3 : (Val.list [cv, encPerm (diag n D g)]).wt ≤ 2 * (2 * (cv.wt + WB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have w4 : (Val.list [Val.list [cv, encPerm (diag n D g)], ids n]).wt ≤
      2 * (2 * ((Val.list [cv, encPerm (diag n D g)]).wt + WB n) + 1) + 4 :=
    wt_lit _ (by simp; omega)
  have hTv : decT n = 1000 * VB n := rfl
  have we : (encFun fun u => (e u : ℕ)).wt ≤ WB n := table_wt (by omega) fun i => (e i).isLt.le
  have ht : FunDet P (a + 1) (.list [.list [cv, encPerm (diag n D g)], ids n])
      (encPerm e) (decTabC n) := by
    rw [encPerm_eq_encFun]
    refine tabN_spec (W := decT n) hT (fun u => ?_) (by
      change (Val.list [Val.list [cv, encPerm (diag n D g)], ids n]).wt +
        (encFun fun u => (e u : ℕ)).wt + 1 ≤ decT n
      omega)
    rw [he u]
    exact decE_lv hS hD hℓ hr hF hpn hpar g u
  have hT1 : decT n ≤ decT1 n := by simp only [decT1]; omega
  set E := [Val.list [cv, encPerm (diag n D g)]] with hE
  have a0 : Lv P E (decT1 n) (arg 0) cv 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (decT1 n) (arg 1) (encPerm (diag n D g)) 1 := Lv.arg rfl (by omega)
  have g0 := Lv.get (vs := [bv D ℓ r, fV F, encFun pn]) a0 (Lv.nat 0 (by omega)) rfl
  have gi : Lv P E (decT1 n) _ (ids n) _ := Lv.bvGet g0 (j := 5) (by omega) rfl (by omega)
  have hcall := Lv.call (Lv.mk2 (Lv.mk2 a0 a1 (by omega)) gi (by omega)) ht
    (by simp only [decT1]; omega)
  exact funDet_of_lv hR (T := decT1 n) (m := 1000) (Lv.mono (e := decRowE (a + 1)) hcall (by norm_num))

end GI.Degree
