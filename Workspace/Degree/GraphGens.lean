module

public import Workspace.Degree.GraphPar

/-!
# The generators of a query

`gensFuns a`: on `[bv, (1 :: gs).map encPerm]`, the list of the generators of `W(⟨gs⟩)`, acting on
pairs, with the identity first. The math part is `slotGens` and `gens_slotGens`.
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n D : ℕ}

/-- The slot number `0`. -/
def z0 (hD : 0 < D) : Fin D := ⟨0, hD⟩

/-- A transposition of a slot with the first slot of its vertex. -/
def slotSw (hD : 0 < D) (s : Fin n × Fin D) : Perm (Fin n × Fin D) := swap (s.1, z0 hD) s

/-- The generators of `W(⟨gs⟩)` on pairs. -/
def slotGens (hD : 0 < D) (gs : List (Perm (Fin n))) : List (Perm (Fin (n * D * (n * D)))) :=
  gs.map (fun a => diag n D (slotLift D a)) ++
    (List.finRange (n * D)).map fun x => diag n D (slotSw hD ((slotE n D).symm x))

theorem length_slotGens (hD : 0 < D) (gs : List (Perm (Fin n))) :
    (slotGens hD gs).length = gs.length + n * D := by
  simp [slotGens]

/-- **The group of a query.** -/
theorem gens_slotGens (hD : 0 < D) (gs : List (Perm (Fin n))) :
    gens (slotGens hD gs) = (slotGroup D (gens gs)).map (diag n D) := by
  rw [gens, gens, ← closure_slotGens (z0 hD), MonoidHom.map_closure]
  congr 1
  ext t
  simp only [slotGens, List.mem_append, List.mem_map, List.mem_finRange, true_and, Set.mem_setOf_eq,
    Set.mem_image, Set.mem_union, slotSwaps]
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨_, Or.inl ⟨a, ha, rfl⟩, rfl⟩
    · exact ⟨_, Or.inr ⟨_, rfl⟩, rfl⟩
  · rintro ⟨g, ⟨a, ha, rfl⟩ | ⟨s, rfl⟩, rfl⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨slotE n D s, by simp [slotSw]⟩

/-- The value of `diag` at a position. -/
theorem diag_val (g : Perm (Fin n × Fin D)) (p : Fin (n * D * (n * D))) :
    (diag n D g p : ℕ) =
      (slotE n D (g ((slotE n D).symm ((pairE (n * D)).symm p).2)) : ℕ) +
        n * D * (slotE n D (g ((slotE n D).symm ((pairE (n * D)).symm p).1)) : ℕ) := by
  obtain ⟨s, s', rfl⟩ := exists_pair p
  rw [diag_apply, pairE_val]
  simp

/-- The action of `a` on a slot number. -/
def actE (e dd aa : Expr) : Expr :=
  .arith .add (modE e dd) (.arith .mul dd (.get aa (divE e dd)))

/-- The entry of a lift, on `[[bv, a], p]`. -/
def liftE : Expr :=
  let c := arg 0
  let B := Expr.get c (.nat 0)
  let aa := Expr.get c (.nat 1)
  let dd := Expr.get B (.nat 1)
  let mm := Expr.get B (.nat 2)
  .arith .add (actE (modE (arg 1) mm) dd aa) (.arith .mul mm (actE (divE (arg 1) mm) dd aa))

/-- The action of a transposition on a slot number. -/
def swYE (y x base : Expr) : Expr :=
  .ite (.arith .eq y base) x (.ite (.arith .eq y x) base y)

/-- The entry of a transposition, on `[[bv, x], p]`. -/
def swE : Expr :=
  let c := arg 0
  let B := Expr.get c (.nat 0)
  let x := Expr.get c (.nat 1)
  let dd := Expr.get B (.nat 1)
  let mm := Expr.get B (.nat 2)
  let base := Expr.arith .mul dd (divE x dd)
  .arith .add (swYE (modE (arg 1) mm) x base) (.arith .mul mm (swYE (divE (arg 1) mm) x base))

/-- The budget of an entry. -/
def genT (n : ℕ) : ℕ := 1000 * VB n

theorem wt_ctx2 (hS : Sz n D) {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ} (hr : r ≤ n) {x y : Val}
    (hx : x.wt ≤ WB n) (hy : y.wt ≤ WB n) :
    2 * (Val.list [.list [bv D ℓ r, x], y]).wt + 10 ≤ genT n := by
  have h0 := WB_ge n
  have hV := WB_le_VB n
  have w0 := bv_wt hS hℓ hr
  have w6 : (Val.list [bv D ℓ r, x]).wt ≤ 2 * (2 * (40 * WB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have w7 : (Val.list [Val.list [bv D ℓ r, x], y]).wt ≤
      2 * (2 * ((Val.list [bv D ℓ r, x]).wt + WB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hTv : genT n = 1000 * VB n := rfl
  omega

/-- The action on a slot number. -/
theorem actE_lv {P : Program} {env : List Val} {T : ℕ} (hS : Sz n D) {e dd aa : Expr}
    {x : Fin (n * D)} {a : Perm (Fin n)} (he : Lv P env T e (.nat x) 40)
    (hd : Lv P env T dd (.nat D) 40) (ha : Lv P env T aa (encPerm a) 40)
    (hT : n * D + 10 ≤ T) :
    Lv P env T (actE e dd aa) (.nat (slotE n D (slotLift D a ((slotE n D).symm x)))) 500 := by
  set s := (slotE n D).symm x with hs
  have hD : D ≤ n * D := Nat.le_mul_of_pos_left _ hS.pos
  have b1 := s.2.isLt
  have du := Lv.arith (op := .div) (z := s.1) he hd (slot_div x) (by have := s.1.isLt; have := Nat.le_mul_of_pos_right n (show 0 < D by have := hS.six; omega); omega)
  have di := Lv.arith (op := .mod) (z := s.2) he hd (slot_mod x) (by omega)
  have ap := Lv.pget ha du
  have hb : (a s.1 : ℕ) * D ≤ (n - 1) * D := Nat.mul_le_mul_right _ (by have := (a s.1).isLt; omega)
  have hn1 : (n - 1) * D + D = n * D := by
    have := hS.pos
    rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
  have hbb : D * (a s.1 : ℕ) ≤ (n - 1) * D := by rw [Nat.mul_comm]; exact hb
  have mu := Lv.arith (op := .mul) (z := D * (a s.1 : ℕ)) hd ap rfl (by omega)
  have ad := Lv.arith (op := .add) (z := (s.2 : ℕ) + D * (a s.1 : ℕ)) di mu rfl (by omega)
  have e1 : slotE n D (slotLift D a s) = slotE n D (a s.1, s.2) := rfl
  rw [e1, slotE_val]
  exact Lv.mono (e := actE e dd aa) ad (by norm_num)

/-- A lift, entry by entry. -/
theorem liftE_lv {P : Program} (hS : Sz n D) {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ}
    (hr : r ≤ n) (a : Perm (Fin n)) (p : Fin (n * D * (n * D))) :
    Lv P [.list [.list [bv D ℓ r, encPerm a], .nat p]] (genT n) liftE
      (.nat (diag n D (slotLift D a) p)) 3000 := by
  have h0 := WB_ge n
  have hk := hS.k_le
  have hmk := hS.m_le_k
  have hT := wt_ctx2 hS hℓ hr (x := encPerm a) (y := .nat p) (perm_wt (by omega) a)
    (fin_wt (by omega) p)
  have hV := WB_le_VB n
  have hTv : genT n = 1000 * VB n := rfl
  set E := [Val.list [.list [bv D ℓ r, encPerm a], .nat p]] with hE
  have a0 : Lv P E (genT n) (arg 0) (.list [bv D ℓ r, encPerm a]) 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (genT n) (arg 1) (.nat p) 1 := Lv.arg rfl (by omega)
  have gB := Lv.get (vs := [bv D ℓ r, encPerm a]) a0 (Lv.nat 0 (by omega)) rfl
  have ga := Lv.get (vs := [bv D ℓ r, encPerm a]) a0 (Lv.nat 1 (by omega)) rfl
  have gd : Lv P E (genT n) _ (.nat D) _ := Lv.bvGet gB (j := 1) (by omega) rfl (by omega)
  have gm : Lv P E (genT n) _ (.nat (n * D)) _ := Lv.bvGet gB (j := 2) (by omega) rfl (by omega)
  set q := (pairE (n * D)).symm p with hq
  have b1 := q.1.isLt
  have b2 := q.2.isLt
  have ds := Lv.arith (op := .div) (z := q.1) a1 gm (pair_div p) (by omega)
  have ms := Lv.arith (op := .mod) (z := q.2) a1 gm (pair_mod p) (by omega)
  have h1 := actE_lv hS (Lv.mono ms (by norm_num)) (Lv.mono gd (by norm_num))
    (a := a) (Lv.mono ga (by norm_num)) (by omega)
  have h2 := actE_lv hS (Lv.mono ds (by norm_num)) (Lv.mono gd (by norm_num))
    (a := a) (Lv.mono ga (by norm_num)) (by omega)
  have hv := diag_val (slotLift D a) p
  have hp := (diag n D (slotLift D a) p).isLt
  have mu := Lv.arith (op := .mul) gm h2 rfl (by
    simp only [BinOp.eval]
    have := Nat.mul_le_mul_left (n * D)
      (slotE n D (slotLift D a ((slotE n D).symm q.1))).isLt.le
    omega)
  have ad := Lv.arith (op := .add) (z := (diag n D (slotLift D a) p : ℕ)) h1 mu hv.symm (by omega)
  exact Lv.mono (e := liftE) ad (by norm_num)

/-- The base of a slot number. -/
theorem base_val (hD : 0 < D) (x : Fin (n * D)) :
    D * ((x : ℕ) / D) = slotE n D (((slotE n D).symm x).1, z0 hD) := by
  rw [slot_div, slotE_val]
  simp [z0]

/-- The action of a transposition on a slot number. -/
theorem swYE_lv {P : Program} {env : List Val} {T : ℕ} (hD : 0 < D) {e xx base : Expr}
    {y x : Fin (n * D)} (he : Lv P env T e (.nat y) 40) (hx : Lv P env T xx (.nat x) 40)
    (hb : Lv P env T base (.nat (slotE n D (((slotE n D).symm x).1, z0 hD))) 100)
    (hT : n * D + 10 ≤ T) :
    Lv P env T (swYE e xx base)
      (.nat (slotE n D (slotSw hD ((slotE n D).symm x) ((slotE n D).symm y)))) 800 := by
  set s := (slotE n D).symm x with hs
  set b := slotE n D (s.1, z0 hD) with hbv
  have hbx := b.isLt
  have hxx := x.isLt
  have hyy := y.isLt
  by_cases h1 : y = b
  · have e1 := Lv.arith (op := .eq) (z := 1) he hb (by simp [BinOp.eval, h1]) (by omega)
    have e2 : slotE n D (slotSw hD s ((slotE n D).symm y)) = x := by
      rw [h1, hbv]
      simp [slotSw, hs]
    rw [e2]
    exact Lv.mono (e := swYE e xx base) (Lv.ite_pos (e := .ite (.arith .eq e xx) base e)
      e1 (by omega) hx) (by norm_num)
  · have hn1 : (y : ℕ) ≠ b := fun h => h1 (Fin.ext h)
    have e1 := Lv.arith (op := .eq) (z := 0) he hb (by simp [BinOp.eval, hn1]) (by omega)
    by_cases h2 : y = x
    · have e3 := Lv.arith (op := .eq) (z := 1) he hx (by simp [BinOp.eval, h2]) (by omega)
      have e2 : slotE n D (slotSw hD s ((slotE n D).symm y)) = b := by
        rw [h2, ← hs]
        simp [slotSw, hbv]
      rw [e2]
      exact Lv.mono (e := swYE e xx base) (Lv.ite_zero (t := _) e1
        (Lv.ite_pos (e := e) e3 (by omega) hb)) (by norm_num)
    · have hn2 : (y : ℕ) ≠ x := fun h => h2 (Fin.ext h)
      have e3 := Lv.arith (op := .eq) (z := 0) he hx (by simp [BinOp.eval, hn2]) (by omega)
      have e2 : slotE n D (slotSw hD s ((slotE n D).symm y)) = y := by
        have a1 : (slotE n D).symm y ≠ (s.1, z0 hD) := fun h => h1 (by
          rw [← (slotE n D).apply_symm_apply y, h])
        have a2 : (slotE n D).symm y ≠ s := fun h => h2 ((slotE n D).symm.injective h)
        simp only [slotSw]
        rw [swap_apply_of_ne_of_ne a1 a2]
        simp
      rw [e2]
      exact Lv.mono (e := swYE e xx base) (Lv.ite_zero (t := _) e1
        (Lv.ite_zero (t := _) e3 he)) (by norm_num)

/-- A transposition, entry by entry. -/
theorem swE_lv {P : Program} (hS : Sz n D) (hD : 0 < D) {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ}
    (hr : r ≤ n) (x : Fin (n * D)) (p : Fin (n * D * (n * D))) :
    Lv P [.list [.list [bv D ℓ r, .nat x], .nat p]] (genT n) swE
      (.nat (diag n D (slotSw hD ((slotE n D).symm x)) p)) 5000 := by
  have h0 := WB_ge n
  have hk := hS.k_le
  have hmk := hS.m_le_k
  have hT := wt_ctx2 hS hℓ hr (x := .nat x) (y := .nat p) (fin_wt (by omega) x)
    (fin_wt (by omega) p)
  have hV := WB_le_VB n
  have hTv : genT n = 1000 * VB n := rfl
  set E := [Val.list [.list [bv D ℓ r, .nat x], .nat p]] with hE
  have a0 : Lv P E (genT n) (arg 0) (.list [bv D ℓ r, .nat x]) 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (genT n) (arg 1) (.nat p) 1 := Lv.arg rfl (by omega)
  have gB := Lv.get (vs := [bv D ℓ r, .nat x]) a0 (Lv.nat 0 (by omega)) rfl
  have gx := Lv.get (vs := [bv D ℓ r, .nat x]) a0 (Lv.nat 1 (by omega)) rfl
  have gd : Lv P E (genT n) _ (.nat D) _ := Lv.bvGet gB (j := 1) (by omega) rfl (by omega)
  have gm : Lv P E (genT n) _ (.nat (n * D)) _ := Lv.bvGet gB (j := 2) (by omega) rfl (by omega)
  set q := (pairE (n * D)).symm p with hq
  have b1 := q.1.isLt
  have b2 := q.2.isLt
  have hxl := x.isLt
  have ds := Lv.arith (op := .div) (z := q.1) a1 gm (pair_div p) (by omega)
  have ms := Lv.arith (op := .mod) (z := q.2) a1 gm (pair_mod p) (by omega)
  have dx := Lv.arith (op := .div) gx gd rfl (show (x : ℕ) / D + 3 ≤ genT n by
    have := Nat.div_le_self (x : ℕ) D
    omega)
  have hbb := (slotE n D (((slotE n D).symm x).1, z0 hD)).isLt
  have bs := Lv.arith (op := .mul) (z := slotE n D (((slotE n D).symm x).1, z0 hD)) gd dx
    (base_val hD x) (by omega)
  have h1 := swYE_lv hD (Lv.mono ms (by norm_num)) (Lv.mono gx (by norm_num))
    (Lv.mono bs (by norm_num)) (by omega)
  have h2 := swYE_lv hD (Lv.mono ds (by norm_num)) (Lv.mono gx (by norm_num))
    (Lv.mono bs (by norm_num)) (by omega)
  have hv := diag_val (slotSw hD ((slotE n D).symm x)) p
  have hp := (diag n D (slotSw hD ((slotE n D).symm x)) p).isLt
  have mu := Lv.arith (op := .mul) gm h2 rfl (by
    simp only [BinOp.eval]
    have := Nat.mul_le_mul_left (n * D)
      (slotE n D (slotSw hD ((slotE n D).symm x) ((slotE n D).symm q.1))).isLt.le
    omega)
  have ad := Lv.arith (op := .add) (z := (diag n D (slotSw hD ((slotE n D).symm x)) p : ℕ))
    h1 mu hv.symm (by omega)
  exact Lv.mono (e := swE) ad (by norm_num)

/-- A row, on `[bv, x]`. -/
def rowE (t : ℕ) : Expr :=
  .call t (mk2 (mk2 (arg 0) (arg 1)) (.get (arg 0) (.nat 7)))

/-- The entry of the generators, on `[bv, list]`. -/
def gensMainE (a : ℕ) : Expr :=
  .call (a + 17) (mk2 (.call (a + 1) (mk2 (arg 0) (arg 1)))
    (.call (a + 9) (mk2 (arg 0) (.get (arg 0) (.nat 6)))))

/-- The functions of the generators. 20 functions. -/
def gensFuns (a : ℕ) : List Expr :=
  [gensMainE a] ++ mapFuns (a + 1) (a + 4) ++ [rowE (a + 5)] ++ tabFuns (a + 5) liftE ++
    mapFuns (a + 9) (a + 12) ++ [rowE (a + 13)] ++ tabFuns (a + 13) swE ++ appendFuns (a + 17)

/-- The bound of a table of a generator. -/
def genTabC (n : ℕ) : ℕ := kB n * (5000 * genT n) + mapK * (kB n + 1) * genT n

/-- The budget of a row. -/
def genT1 (n : ℕ) : ℕ := genTabC n + genT n

/-- The bound of a row. -/
def genRowC (n : ℕ) : ℕ := 300 * genT1 n

theorem genT_le_T1 (n : ℕ) : genT n ≤ genT1 n := by
  simp only [genT1]; omega

theorem genTab_le (hS : Sz n D) :
    (n * D * (n * D)) * (5000 * genT n) + mapK * (n * D * (n * D) + 1) * genT n ≤ genTabC n := by
  have hk := hS.k_le
  have e1 := Nat.mul_le_mul_right (5000 * genT n) hk
  have e2 : mapK * (n * D * (n * D) + 1) * genT n ≤ mapK * (kB n + 1) * genT n :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  simp only [genTabC]
  omega

/-- A table of a permutation of the positions, as a row. -/
theorem row_fun {P : Program} {c t : ℕ} (hc : P.funs[c]? = some (rowE t)) (hS : Sz n D)
    {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ} (hr : r ≤ n) {x w : Val} (hx : x.wt ≤ WB n)
    (ht : FunDet P t (.list [.list [bv D ℓ r, x], ids (n * D * (n * D))]) w (genTabC n)) :
    FunDet P c (.list [bv D ℓ r, x]) w (genRowC n) := by
  have h0 := WB_ge n
  have hk := hS.k_le
  have hT1 := genT_le_T1 n
  have hT0 := wt_ctx2 hS hℓ hr (x := x) (y := ids (n * D * (n * D))) hx
    (table_wt (by omega) fun i => i.isLt.le)
  have w0 := bv_wt hS hℓ hr
  have hV := WB_le_VB n
  have hTv : genT n = 1000 * VB n := rfl
  have w6 : (Val.list [bv D ℓ r, x]).wt ≤ 2 * (2 * (40 * WB n) + 1) + 4 := wt_lit _ (by simp; omega)
  set E := [Val.list [bv D ℓ r, x]] with hE
  have a0 : Lv P E (genT1 n) (arg 0) (bv D ℓ r) 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (genT1 n) (arg 1) x 1 := Lv.arg rfl (by omega)
  have gi : Lv P E (genT1 n) _ (ids (n * D * (n * D))) _ :=
    Lv.bvGet a0 (j := 7) (by omega) rfl (by omega)
  have hcall := Lv.call (Lv.mk2 (Lv.mk2 a0 a1 (by omega)) gi (by omega)) ht
    (by simp only [genT1]; omega)
  exact funDet_of_lv hc (T := genT1 n) (m := 300) (Lv.mono (e := rowE t) hcall (by norm_num))

/-- A bound on a list of generators. -/
def GB (n : ℕ) : ℕ := (n ^ 2 + n * (n + 6) + 2) * (2 * WB n + 1) + 4

/-- A bound on the weights of the list functions. -/
def gW (n : ℕ) : ℕ := 100 * GB n + 1000 * WB n

def genC1 (n : ℕ) : ℕ := (n ^ 2 + 1) * genRowC n + mapK * (n ^ 2 + 2) * (2 * gW n)

def genC2 (n : ℕ) : ℕ := (n * (n + 6)) * genRowC n + mapK * (n * (n + 6) + 1) * (2 * gW n)

def genC3 (n : ℕ) : ℕ := loopModK * (n * (n + 6) + 1) * (2 * gW n + n * (n + 6) + 1)

def gsT (n : ℕ) : ℕ := genC1 n + genC2 n + genC3 n + gW n

/-- The bound of the generators. -/
def gensC (n : ℕ) : ℕ := 1000 * gsT n

theorem gensC_poly : PolyB gensC := by
  have := VB_poly
  have := WB_poly
  unfold gensC gsT genC1 genC2 genC3 gW GB genRowC genT1 genTabC genT kB
  poly

/-- **The generators of a query.** -/
theorem gens_spec {P : Program} {a : ℕ} (h : P.HasAt a (gensFuns a)) (hS : Sz n D) (hD : 0 < D)
    {ℓ : Fin n → ℕ} (hℓ : ∀ u, ℓ u ≤ n) {r : ℕ} (hr : r ≤ n) {gs : List (Perm (Fin n))}
    (hgs : gs.length ≤ n ^ 2) :
    FunDet P a (.list [bv D ℓ r, .list ((1 :: gs).map encPerm)])
      (.list ((1 :: slotGens hD gs).map encPerm)) (gensC n) := by
  have hM : P.funs[a]? = some (gensMainE a) := h.left.left.left.left.left.left.left.single
  have hmL : P.HasAt (a + 1) (mapFuns (a + 1) (a + 4)) := h.left.left.left.left.left.left.right
  have hrL : P.funs[a + 4]? = some (rowE (a + 5)) := h.left.left.left.left.left.right.single
  have htL : P.HasAt (a + 5) (tabFuns (a + 5) liftE) := h.left.left.left.left.right
  have hmS : P.HasAt (a + 9) (mapFuns (a + 9) (a + 12)) := h.left.left.left.right
  have hrS : P.funs[a + 12]? = some (rowE (a + 13)) := h.left.left.right.single
  have htS : P.HasAt (a + 13) (tabFuns (a + 13) swE) := h.left.right
  have hap : P.HasAt (a + 17) (appendFuns (a + 17)) := h.right
  have h0 := WB_ge n
  have hV := WB_le_VB n
  have w0 := bv_wt hS hℓ hr
  have hk := hS.k_le
  have hmk := hS.m_le_k
  have hm := hS.m_le
  have hTv : genT n = 1000 * VB n := rfl
  have wk : (ids (n * D * (n * D))).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have wm : (ids (n * D)).wt ≤ WB n := table_wt (by omega) fun i => i.isLt.le
  have htab : ∀ (t e : ℕ) (E : Expr) (_ : P.HasAt t (tabFuns t E)) (x : Val)
      (g : Perm (Fin (n * D * (n * D)))), x.wt ≤ WB n →
      (∀ p : Fin (n * D * (n * D)),
        Lv P [.list [.list [bv D ℓ r, x], .nat p]] (genT n) E (.nat (g p)) 5000) →
      FunDet P t (.list [.list [bv D ℓ r, x], ids (n * D * (n * D))]) (encPerm g) (genTabC n) := by
    intro t _ E ht x g hx hl
    rw [encPerm_eq_encFun]
    refine (tabN_spec (W := genT n) ht hl ?_).mono (genTab_le hS)
    have hT0 := wt_ctx2 hS hℓ hr (x := x) (y := ids (n * D * (n * D))) hx wk
    have := perm_wt (n := n) (by omega) g
    rw [encPerm_eq_encFun] at this
    omega
  have hperm : ∀ {g : Perm (Fin (n * D * (n * D)))}, (encPerm g).wt ≤ WB n :=
    perm_wt (by omega) _
  set L1 : List (Perm (Fin n)) := 1 :: gs with hL1
  set res : Perm (Fin n) → Val := fun a => encPerm (diag n D (slotLift D a)) with hres
  set F : Fin (n * D) → Val := fun x => encPerm (diag n D (slotSw hD ((slotE n D).symm x)))
    with hF
  have hlen : L1.length ≤ n ^ 2 + 1 := by simp [hL1]; omega
  have wt1 : (Val.list (L1.map encPerm)).wt ≤ GB n := by
    have := wt_lit (L1.map encPerm) (c := WB n) (by
      intro v hv
      obtain ⟨g, -, rfl⟩ := List.mem_map.1 hv
      exact perm_wt (by omega) g)
    simp only [List.length_map] at this
    refine this.trans ?_
    simp only [GB]
    have := Nat.mul_le_mul_right (2 * WB n + 1)
      (show L1.length ≤ n ^ 2 + n * (n + 6) + 2 by omega)
    omega
  have wt2 : (Val.list (L1.map res)).wt ≤ GB n := by
    have := wt_lit (L1.map res) (c := WB n) (by
      intro v hv
      obtain ⟨g, -, rfl⟩ := List.mem_map.1 hv
      exact hperm)
    simp only [List.length_map] at this
    refine this.trans ?_
    simp only [GB]
    have := Nat.mul_le_mul_right (2 * WB n + 1)
      (show L1.length ≤ n ^ 2 + n * (n + 6) + 2 by omega)
    omega
  have wt3 : (Val.list ((List.finRange (n * D)).map F)).wt ≤ GB n := by
    have := wt_listFin_le F (B := WB n) fun _ => hperm
    refine this.trans ?_
    simp only [GB]
    have := Nat.mul_le_mul_right (2 * WB n + 1)
      (show n * D ≤ n ^ 2 + n * (n + 6) + 2 by omega)
    omega
  have hG0 : WB n ≤ GB n := by
    simp only [GB]
    nlinarith
  have hW1 : (Val.list [bv D ℓ r, .list (L1.map encPerm)]).wt ≤ gW n := by
    have : (Val.list [bv D ℓ r, .list (L1.map encPerm)]).wt ≤ 2 * (2 * (GB n + 40 * WB n) + 1) + 4 :=
      wt_lit _ (by simp; omega)
    simp only [gW]
    omega
  have hW2 : (Val.list [bv D ℓ r, ids (n * D)]).wt ≤ gW n := by
    have : (Val.list [bv D ℓ r, ids (n * D)]).wt ≤ 2 * (2 * (GB n + 40 * WB n) + 1) + 4 :=
      wt_lit _ (by simp; omega)
    simp only [gW]
    omega
  have hGW : ∀ x : ℕ, x ≤ 3 * GB n → x ≤ gW n := fun x hx => by
    simp only [gW]
    omega
  have hGG : GB n + 1 ≤ gW n := by
    simp only [gW]
    omega
  have hW0 : 1 ≤ gW n := by simp only [gW]; omega
  have f1 : FunDet P (a + 1) (.list [bv D ℓ r, .list (L1.map encPerm)]) (.list (L1.map res))
      (genC1 n) := by
    refine (mapInj_spec (W := 2 * gW n) hmL L1 encPerm res encPerm_injective (B := genRowC n) ?_
      (by omega)).mono ?_
    · intro b _
      refine row_fun hrL hS hℓ hr (perm_wt (by omega) b) ?_
      exact htab _ 0 _ htL _ _ (perm_wt (by omega) b) fun p =>
        Lv.mono (liftE_lv hS hℓ hr b p) (by norm_num)
    · have e1 := Nat.mul_le_mul_right (genRowC n) hlen
      have e2 : mapK * (L1.length + 1) * (2 * gW n) ≤ mapK * (n ^ 2 + 2) * (2 * gW n) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      simp only [genC1]
      omega
  have f2 : FunDet P (a + 9) (.list [bv D ℓ r, ids (n * D)])
      (.list ((List.finRange (n * D)).map F)) (genC2 n) := by
    refine (tab_cost (F := F) (W := 2 * gW n) (B := genRowC n) hmS (fun x => ?_) (by
      change (Val.list [bv D ℓ r, ids (n * D)]).wt + (Val.list ((List.finRange (n * D)).map F)).wt +
        1 ≤ 2 * gW n
      omega)).mono ?_
    · refine row_fun hrS hS hℓ hr (fin_wt (by omega) x) ?_
      exact htab _ 0 _ htS _ _ (fin_wt (by omega) x) fun p =>
        Lv.mono (swE_lv hS hD hℓ hr x p) (by norm_num)
    · have e1 := Nat.mul_le_mul_right (genRowC n) hm
      have e2 : mapK * (n * D + 1) * (2 * gW n) ≤ mapK * (n * (n + 6) + 1) * (2 * gW n) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      simp only [genC2]
      omega
  have hlen3 : (List.finRange (n * D)).length ≤ n * (n + 6) := by simpa using hm
  have f3 : FunDet P (a + 17)
      (.list [.list (L1.map res), .list ((List.finRange (n * D)).map F)])
      (.list (L1.map res ++ (List.finRange (n * D)).map F)) (genC3 n) := by
    refine (append_spec hap _ _).mono fun w c hc => ?_
    obtain ⟨rfl, hc⟩ := hc
    refine ⟨rfl, hc.trans ?_⟩
    have wt4 : (Val.list (L1.map res ++ (List.finRange (n * D)).map F)).wt ≤ GB n := by
      have := wt_lit (L1.map res ++ (List.finRange (n * D)).map F) (c := WB n) (by
        intro v hv
        rcases List.mem_append.1 hv with hv | hv
        · obtain ⟨g, -, rfl⟩ := List.mem_map.1 hv
          exact hperm
        · obtain ⟨g, -, rfl⟩ := List.mem_map.1 hv
          exact hperm)
      refine this.trans ?_
      simp only [GB, List.length_append, List.length_map, List.length_finRange]
      have := Nat.mul_le_mul_right (2 * WB n + 1)
        (show L1.length + n * D ≤ n ^ 2 + n * (n + 6) + 2 by omega)
      omega
    have wt5 : (Val.list [.list (L1.map res), .list ((List.finRange (n * D)).map F)]).wt ≤ gW n := by
      have : (Val.list [.list (L1.map res), .list ((List.finRange (n * D)).map F)]).wt ≤
          2 * (2 * GB n + 1) + 4 := wt_lit _ (by simp; omega)
      simp only [gW]
      omega
    simp only [genC3, List.length_map, List.length_finRange]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hval : L1.map res ++ (List.finRange (n * D)).map F = (1 :: slotGens hD gs).map encPerm := by
    have e1 : res 1 = encPerm (1 : Perm (Fin (n * D * (n * D)))) := by
      simp only [hres, map_one]
    simp [hL1, e1, slotGens, Function.comp_def, hres, hF]
  rw [← hval]
  have hT1 : gW n ≤ gsT n := by simp only [gsT]; omega
  have hT2 : genC1 n ≤ gsT n := by simp only [gsT]; omega
  have hT3 : genC2 n ≤ gsT n := by simp only [gsT]; omega
  have hT4 : genC3 n ≤ gsT n := by simp only [gsT]; omega
  set E := [Val.list [bv D ℓ r, .list (L1.map encPerm)]] with hE
  have a0 : Lv P E (3 * gsT n) (arg 0) (bv D ℓ r) 1 := Lv.arg rfl (by omega)
  have a1 : Lv P E (3 * gsT n) (arg 1) (.list (L1.map encPerm)) 1 := Lv.arg rfl (by omega)
  have gi : Lv P E (3 * gsT n) _ (ids (n * D)) _ := Lv.bvGet a0 (j := 6) (by omega) rfl (by omega)
  have c1 := Lv.call (Lv.mk2 a0 a1 (by omega)) f1 (show genC1 n ≤ 3 * gsT n by omega)
  have c2 := Lv.call (Lv.mk2 a0 gi (by omega)) f2 (show genC2 n ≤ 3 * gsT n by omega)
  have c3 := Lv.call (Lv.mk2 c1 c2 (by omega)) f3 (show genC3 n ≤ 3 * gsT n by omega)
  refine (funDet_of_lv hM (T := 3 * gsT n) (m := 300) (Lv.mono (e := gensMainE a) c3 (by norm_num))).mono ?_
  simp only [gensC]
  omega

end GI.Degree
