module

public import Workspace.Impl.VsWProgCo
public import Workspace.Proved.VsWAlgMath

@[expose] public section

/-!
# The identity and `A - c` as programs

* `vsWIdFuns b` (10 functions), `vsWId_spec`: on `.nat D` the identity `vsWVs (vsWId D)`, cost `2 · 10^8 (N + 1)^4`.
  Meaning: `GI.Proved.vsWId_span`.
* `vsWSubCFuns b` (19 functions), `vsWSubC_spec`: on `[p, c, vsWVs A]` the stored matrix
  `vsWVs (vsWSubC p c A)`. Meaning: `GI.Proved.vsWSubC_matrix`.
-/

namespace GI.Impl

open GI.Lang GI.Cited

/-- The unit vector, with a cost in terms of one size bound. -/
theorem vsWUnit_det {P : Program} {b : ℕ} (h : P.HasAt b (vsUnitFuns b)) {N m i : ℕ} (hm : m ≤ N)
    (hi : i ≤ N) : FunDet P b (.list [.nat m, .nat i]) (natList (vsUnit m i)) (10 ^ 5 * (N + 1) ^ 3) :=
  (vsUnit_spec h m i).mono fun w c hw => ⟨hw.1, by
    have := hw.2; rw [hw.1] at this
    exact this.trans (vsWUP_cost hm hi (wt_vsUnit_le m i))⟩

/-- The range, with a cost in terms of one size bound. -/
theorem vsWRange_det {P : Program} {b : ℕ} (h : P.HasAt b (rangeFuns b)) {N n : ℕ} (hn : n ≤ N) :
    FunDet P b (.nat n) (.list ((List.range n).map Val.nat)) (10 ^ 4 * (N + 1) ^ 3) :=
  (range_spec h n).mono fun w c hw => ⟨hw.1, by
    have h2 := hw.2; rw [hw.1] at h2
    have hK : loopModK = 1000 := rfl
    have wrg := wt_natList_le_sq (B := N) (xs := List.range n) (fun y hy => by simp at hy; omega)
      (by simp; omega)
    have := wt_nat_le n
    have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
    have k : loopModK * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1) ≤
        1000 * (N + 1) * (10 * (N + 1) ^ 2) := by
      rw [hK]; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e : 1000 * (N + 1) * (10 * (N + 1) ^ 2) = 10 ^ 4 * (N + 1) ^ 3 := by ring
    exact h2.trans (k.trans e.le)⟩

/-! ### The identity -/

/-- The identity, on `D`. -/
def vsWIdF (mp rng : ℕ) : Expr := .call mp (mk2 (.var 0) (.call rng (.var 0)))

/-- The identity program at base `b` (10 functions). -/
def vsWIdFuns (b : ℕ) : List Expr :=
  [vsWIdF (b + 1) (b + 7)] ++ mapFuns (b + 1) (b + 4) ++ vsUnitFuns (b + 4) ++ rangeFuns (b + 7)

theorem vsWIdFuns_length (b : ℕ) : (vsWIdFuns b).length = 10 := rfl

/-- **The identity program.** -/
theorem vsWId_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWIdFuns b)) {N D : ℕ} (hD : D ≤ N) :
    FunDet P b (.nat D) (vsWVs (vsWId D)) (2 * 10 ^ 8 * (N + 1) ^ 4) := by
  have h0 : P.funs[b]? = some (vsWIdF (b + 1) (b + 7)) := h.get (j := 0) (by simp [vsWIdFuns])
  have hm : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hu : P.HasAt (b + 4) (vsUnitFuns (b + 4)) := h.block 4 rfl
  have hr : P.HasAt (b + 7) (rangeFuns (b + 7)) := h.block 7 rfl
  have v0 : Det P [.nat D] (.var 0) (.nat D) _ := Det.var' rfl
  have drg := Det.call v0 (vsWRange_det hr hD)
  have dmap := vsQ_map hm (List.range D) Val.nat (fun i => natList (vsUnit D i)) valNat_injective
    (c := .nat D) fun i hi => vsWUnit_det hu hD (by simp at hi; omega)
  have e1 : (List.range D).map (fun i => natList (vsUnit D i)) = (vsWId D).map natList := by
    simp [vsWId]
  rw [e1] at dmap
  refine FunDet.intro h0 ((Det.call (Det.mk2 v0 drg) dmap).mono ?_)
  have hf := GI.Proved.vsWId_fit (p := 2) (by omega) D
  have wI := wt_vsWVs_le (N := N) (us := vsWId D)
    (fun u hu => ⟨fun y hy => by
      have h1 := (hf u hu).1 y hy; have h2 := (hf u hu).2
      have : 0 < u.length := List.length_pos_of_mem hy
      omega, by rw [(hf u hu).2]; exact hD⟩)
    (by simp [vsWId]; omega)
  have eI : (vsWVs (vsWId D)).wt = (Val.list ((vsWId D).map natList)).wt := rfl
  have wrg := wt_natList_le_sq (B := N) (xs := List.range D) (fun y hy => by simp at hy; omega)
    (by simp; omega)
  have eN : natList (List.range D) = .list ((List.range D).map Val.nat) := rfl
  rw [eN] at wrg
  have wd := wt_nat_le D
  have w2 := wt_list2_le (.nat D) (.list ((List.range D).map Val.nat))
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have kmap := vsW_mapCost (N := N) (n := (List.range D).length) (B := 10 ^ 5 * (N + 1) ^ 3)
    (c := 10 ^ 5) (k := 3) (W := (Val.list [.nat D, .list ((List.range D).map Val.nat)]).wt +
      (Val.list ((vsWId D).map natList)).wt) (by simp; omega) le_rfl (by omega)
  have e5 : (N + 1) ^ (3 + 1) = (N + 1) ^ 4 := rfl
  omega

/-! ### A stored matrix minus a scalar -/

/-- Row `j` of `A - c`, on `[[p, c, A], j]`. -/
def vsWSubCItemF (lin unit : ℕ) : Expr :=
  .call lin (.snoc (mk4 (.get (arg 0) (.nat 0)) (.nat 1)
      (.arith .sub (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)))
      (.get (.get (arg 0) (.nat 2)) (arg 1)))
    (.call unit (mk2 (.length (.get (arg 0) (.nat 2))) (arg 1))))

/-- `A - c`, on `[p, c, A]`. -/
def vsWSubCF (mp rng : ℕ) : Expr := .call mp (mk2 (.var 0) (.call rng (.length (arg 2))))

/-- The program of `A - c` at base `b` (19 functions). -/
def vsWSubCFuns (b : ℕ) : List Expr :=
  [vsWSubCF (b + 1) (b + 5)] ++ mapFuns (b + 1) (b + 4) ++ [vsWSubCItemF (b + 8) (b + 16)] ++
    rangeFuns (b + 5) ++ vsLinFuns (b + 8) ++ vsUnitFuns (b + 16)

theorem vsWSubCFuns_length (b : ℕ) : (vsWSubCFuns b).length = 19 := rfl

theorem vsWSubCItem_spec {P : Program} {f lin unit : ℕ} (hf : P.funs[f]? = some (vsWSubCItemF lin unit))
    (hl : P.HasAt lin (vsLinFuns lin)) (hu : P.HasAt unit (vsUnitFuns unit)) {p N d c : ℕ}
    (hp : 0 < p) (hpN : p ≤ N) (hdN : d ≤ N) (hc : c ≤ p) {A : List (List ℕ)}
    (hA : GI.Proved.VsWSq p d A) {j : ℕ} (hj : j < A.length) :
    FunDet P f (.list [.list [.nat p, .nat c, vsWVs A], .nat j])
      (natList (vsLin p 1 (p - c) (A.getD j []) (vsUnit A.length j))) (2 * 10 ^ 6 * (N + 1) ^ 3) := by
  set X := Val.list [.nat p, .nat c, vsWVs A]
  have a0 := Det.arg' (P := P) (rest := []) (vs := [X, .nat j]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [X, .nat j]) (j := 1) rfl
  have g0 := Det.get' a0 (Det.nat 0) (show [Val.nat p, .nat c, vsWVs A][0]? = some (.nat p) from rfl)
  have g1 := Det.get' a0 (Det.nat 1) (show [Val.nat p, .nat c, vsWVs A][1]? = some (.nat c) from rfl)
  have g2 := Det.get' a0 (Det.nat 2)
    (show [Val.nat p, .nat c, vsWVs A][2]? = some (.list (A.map natList)) from rfl)
  have hv : (A.map natList)[j]? = some (natList (A.getD j [])) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]; rfl
  have gA := Det.get' g2 a1 hv
  have dsub := Det.arith' g0 g1 (op := .sub) rfl
  have dl := Det.length g2
  rw [List.length_map] at dl
  have hAl : A.length = d := hA.2
  have du := Det.call (Det.mk2 dl a1) (vsWUnit_det hu (N := N) (by omega) (by omega))
  have d5 := Det.snoc (Det.mk4 g0 (Det.nat 1) dsub gA) du
  simp only [List.cons_append, List.nil_append] at d5
  have hrow := (hA.1 (A.getD j []) (by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj))
  have dlin := Det.call d5 (vsLin_spec hl (p := p) (a := 1) (b := p - c) (N := N) hp
    (fun y hy => (hrow.1 y hy).le.trans hpN)
    (fun y hy => (vsUnit_le_one _ _ y hy).trans (by omega))
    (by rw [hrow.2]; exact hdN) (by rw [vsUnit_length]; omega)
    (by rw [hrow.2, vsUnit_length, hAl]) hpN (by omega) (by omega))
  refine FunDet.intro hf (dlin.mono ?_)
  have wA := wt_vsWVs_le (VsWFit.bnd hA.1 hpN hdN) (show A.length ≤ N + 1 by omega)
  have eA : (vsWVs A).wt = (Val.list (A.map natList)).wt := rfl
  have wX := wt_list3_le (.nat p) (.nat c) (vsWVs A)
  have eX : X.wt = (Val.list [.nat p, .nat c, vsWVs A]).wt := rfl
  have wa := wt_list2_le X (.nat j)
  have wp := wt_nat_le p
  have wc := wt_nat_le c
  have wj := wt_nat_le j
  have w1 := wt_nat_le 1
  have wpc := wt_nat_le (p - c)
  have hsub : GI.Machine.BinOp.sub.eval p c = p - c := rfl
  have wrow := wt_natList_le_sq (B := N) (xs := A.getD j []) (fun y hy => (hrow.1 y hy).le.trans hpN)
    (by rw [hrow.2]; exact hdN)
  have wu := wt_vsUnit_le A.length j
  have wu' : 5 * (A.length + 2) ^ 2 ≤ 20 * (N + 1) ^ 2 := by
    have : (A.length + 2) ^ 2 ≤ (2 * (N + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  have wo := wt_natList_le_sq (B := N) (xs := vsLin p 1 (p - c) (A.getD j []) (vsUnit A.length j))
    (fun y hy => (vsLin_lt hp _ _ y hy).le.trans hpN) (by rw [vsLin_length, hrow.2]; exact hdN)
  have w5 := wt_list_le [Val.nat p, .nat 1, .nat (p - c), natList (A.getD j []),
    natList (vsUnit A.length j)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w5
  have w4 := wt_list4_le (.nat p) (.nat 1) (.nat (p - c)) (natList (A.getD j []))
  have w2 := wt_list2_le (.nat A.length) (.nat j)
  have wl := wt_nat_le A.length
  have hlA := length_lt_wt_list (A.map natList)
  rw [List.length_map] at hlA
  have q0 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have eL : vsLinArg p 1 (p - c) (A.getD j []) (vsUnit A.length j) =
    .list [.nat p, .nat 1, .nat (p - c), natList (A.getD j []), natList (vsUnit A.length j)] := rfl
  simp only [eL, hsub] at *
  omega

/-- **The program of `A - c`.** -/
theorem vsWSubC_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWSubCFuns b)) {p N d c : ℕ}
    (hp : 0 < p) (hpN : p ≤ N) (hdN : d ≤ N) (hc : c ≤ p) {A : List (List ℕ)}
    (hA : GI.Proved.VsWSq p d A) :
    FunDet P b (.list [.nat p, .nat c, vsWVs A]) (vsWVs (vsWSubC p c A)) (10 ^ 10 * (N + 1) ^ 4) := by
  have h0 : P.funs[b]? = some (vsWSubCF (b + 1) (b + 5)) := h.get (j := 0) (by simp [vsWSubCFuns])
  have hm : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hit : P.funs[b + 4]? = some (vsWSubCItemF (b + 8) (b + 16)) :=
    h.get (j := 4) (by rw [vsWSubCFuns_length]; omega)
  have hr : P.HasAt (b + 5) (rangeFuns (b + 5)) := h.block 5 rfl
  have hl : P.HasAt (b + 8) (vsLinFuns (b + 8)) := h.block 8 rfl
  have hu : P.HasAt (b + 16) (vsUnitFuns (b + 16)) := h.block 16 rfl
  set X := Val.list [.nat p, .nat c, vsWVs A]
  have hAl : A.length = d := hA.2
  have v0 : Det P [X] (.var 0) X _ := Det.var' rfl
  have a2 : Det P [X] (arg 2) (.list (A.map natList)) _ :=
    Det.arg' (P := P) (rest := []) (vs := [Val.nat p, .nat c, vsWVs A]) (j := 2) rfl
  have dl := Det.length a2
  rw [List.length_map] at dl
  have drg := Det.call dl (vsWRange_det hr (N := N) (by omega))
  have dmap := vsQ_map hm (List.range A.length) Val.nat
    (fun j => natList (vsLin p 1 (p - c) (A.getD j []) (vsUnit A.length j))) valNat_injective
    (c := X) fun j hj => vsWSubCItem_spec hit hl hu hp hpN hdN hc hA (by simpa using hj)
  have e1 : (List.range A.length).map (fun j => natList (vsLin p 1 (p - c) (A.getD j [])
      (vsUnit A.length j))) = (vsWSubC p c A).map natList := by simp [vsWSubC]
  rw [e1] at dmap
  refine FunDet.intro h0 ((Det.call (Det.mk2 v0 drg) dmap).mono ?_)
  have hS := GI.Proved.vsWSubC_fit (c := c) hp hA
  have wS := wt_vsWVs_le (VsWFit.bnd hS.1 hpN hdN) (show (vsWSubC p c A).length ≤ N + 1 by
    rw [hS.2]; omega)
  have eS : (vsWVs (vsWSubC p c A)).wt = (Val.list ((vsWSubC p c A).map natList)).wt := rfl
  have wA := wt_vsWVs_le (VsWFit.bnd hA.1 hpN hdN) (show A.length ≤ N + 1 by omega)
  have eA : (vsWVs A).wt = (Val.list (A.map natList)).wt := rfl
  have wX := wt_list3_le (.nat p) (.nat c) (vsWVs A)
  have eX : X.wt = (Val.list [.nat p, .nat c, vsWVs A]).wt := rfl
  have wrg := wt_natList_le_sq (B := N) (xs := List.range A.length) (fun y hy => by simp at hy; omega)
    (by simp; omega)
  have eN : natList (List.range A.length) = .list ((List.range A.length).map Val.nat) := rfl
  rw [eN] at wrg
  have wp := wt_nat_le p
  have wc := wt_nat_le c
  have w2 := wt_list2_le X (.list ((List.range A.length).map Val.nat))
  have hlA := length_lt_wt_list (A.map natList)
  rw [List.length_map] at hlA
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have kmap := vsW_mapCost (N := N) (n := (List.range A.length).length)
    (B := 2 * 10 ^ 6 * (N + 1) ^ 3) (c := 2 * 10 ^ 6) (k := 3)
    (W := (Val.list [X, .list ((List.range A.length).map Val.nat)]).wt +
      (Val.list ((vsWSubC p c A).map natList)).wt) (by simp; omega) le_rfl (by omega)
  have e5 : (N + 1) ^ (3 + 1) = (N + 1) ^ 4 := rfl
  omega

end GI.Impl
