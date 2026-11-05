module

public import Workspace.Impl.AggCaseMath
public import Workspace.Impl.AggStructDC
public import Workspace.Impl.GenProdNum
public import Workspace.Lang.Prims.Ops
public import Workspace.Lang.Lib.Orbit

@[expose] public section

/-!
# The case test of the items, as a program

On the group value `encGroup gs` of `H = ⟨gs⟩ = π(F_x)` the program returns the code of
`aggCase H` (`AggCase.code`). It follows the list form of `AggCaseMath.lean` (`acCaseL`,
`ac_aggCase_eq`):

1. orbit labels `lab` by the orbit program (`orbits_spec`);
2. the dominant points `D` (orbit size above `q/2`), as the filter of `[0, …, q-1]` by a count of
   labels (`acpDomF`), and the number of points in nontrivial orbits (`acpSuppF`);
3. if `D` is empty: Case 1 or 3 by that number;
4. otherwise (`acpGiantF`): one call of the pointwise stabilizer `H_(D)` (`pstab_spec`, the cited
   task **PointwiseStab**), the orders `|H|` and `|H_(D)|` (two calls of the cited task
   **GroupOrder**), the factorial `|D|!`, and the test `|D|! · |H_(D)| ≤ 2 |H|`: Case 2a or 2b.

The pointwise stabilizer is a relational task (its generators are not fixed), but the result of
the test is, so the whole program is deterministic (`acp_case_spec`).
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms gens encGroup encPts PointwiseStab GroupOrder)
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### The two tests on a point -/

/-- The labels as a list of numbers. -/
def acpLabs (lab : Fin n → ℕ) : List ℕ := (List.finRange n).map lab

/-- On `[[n, labV], i]`: whether the orbit of `i` has more than `n/2` points. -/
def acpDomF (cnt : ℕ) : Expr :=
  .arith .lt (.get (arg 0) (.nat 0))
    (.arith .mul (.nat 2)
      (.call cnt (mk2 (.get (.get (arg 0) (.nat 1)) (arg 1)) (.get (arg 0) (.nat 1)))))

/-- On `[[n, labV], i]`: whether the orbit of `i` has more than one point. -/
def acpSuppF (cnt : ℕ) : Expr :=
  .arith .sub (.nat 1)
    (.arith .eq (.nat 1)
      (.call cnt (mk2 (.get (.get (arg 0) (.nat 1)) (arg 1)) (.get (arg 0) (.nat 1)))))

/-- The test of `acpDomF` on a value. -/
def acpDomQ (lab : Fin n → ℕ) : Val → Bool
  | .nat i => decide (n < 2 * (acpLabs lab).count ((acpLabs lab).getD i 0))
  | .list _ => false

/-- The test of `acpSuppF` on a value. -/
def acpSuppQ (lab : Fin n → ℕ) : Val → Bool
  | .nat i => decide ((acpLabs lab).count ((acpLabs lab).getD i 0) ≠ 1)
  | .list _ => false

/-- The constant of the tests. -/
def acpTK : ℕ := 10 ^ 7

theorem acp_labs_le {lab : Fin n → ℕ} (hlab : ∀ x, lab x < n) : ∀ x ∈ acpLabs lab, x ≤ n := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
  exact (hlab y).le

theorem acp_labs_length (lab : Fin n → ℕ) : (acpLabs lab).length = n := by
  simp [acpLabs]

theorem acp_encFun (lab : Fin n → ℕ) : encFun lab = natList (acpLabs lab) :=
  encFun_eq_natList lab

/-- The count of a label in the list is at most `n`. -/
theorem acp_count_le (lab : Fin n → ℕ) (j : ℕ) : (acpLabs lab).count j ≤ n :=
  (List.count_le_length).trans (acp_labs_length lab).le

/-- The shared part of the two tests: the count of the label of `i`. -/
theorem acp_cnt_det {P : Program} {cnt : ℕ} (hcnt : P.HasAt cnt (countFuns cnt))
    {lab : Fin n → ℕ} (hlab : ∀ x, lab x < n) {i : ℕ} (hi : i < n) {W : ℕ}
    (hW : 4 * (Val.list [.list [.nat n, encFun lab], .nat i]).wt + 10 ≤ W) :
    StDC P [.list [.list [.nat n, encFun lab], .nat i]]
      (.call cnt (mk2 (.get (.get (arg 0) (.nat 1)) (arg 1)) (.get (arg 0) (.nat 1))))
      (.nat ((acpLabs lab).count ((acpLabs lab).getD i 0))) 20 (countK * (n + 1) ^ 3) W := by
  have hc : (Val.list [.nat n, encFun lab]).wt <
      (Val.list [.list [.nat n, encFun lab], .nat i]).wt := wt_le_wt_list (by simp)
  have hl : (encFun lab).wt < (Val.list [.nat n, encFun lab]).wt := wt_le_wt_list (by simp)
  have hiw : (Val.nat i).wt < (Val.list [.list [.nat n, encFun lab], .nat i]).wt :=
    wt_le_wt_list (by simp)
  have hlen : (acpLabs lab).length = n := acp_labs_length lab
  have hgi : (acpLabs lab).getD i 0 < n := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp only [acpLabs, List.getElem_map, List.getElem_finRange]
    exact hlab _
  have hgetv : ((acpLabs lab).map Val.nat)[i]? = some (.nat ((acpLabs lab).getD i 0)) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem (by omega),
      List.getD_eq_getElem _ _ (by omega)]
    rfl
  have e : (natList (acpLabs lab)).wt = (encFun lab).wt := by rw [acp_encFun]
  have hnA : n < (encFun lab).wt := by
    have := length_lt_wt_list ((acpLabs lab).map Val.nat)
    simp only [List.length_map, hlen] at this
    have e' : (Val.list ((acpLabs lab).map Val.nat)).wt = (natList (acpLabs lab)).wt := rfl
    omega
  have d0 : StDC P [.list [.list [.nat n, encFun lab], .nat i]] (arg 0)
      (.list [.nat n, encFun lab]) 3 0 W :=
    StDC.arg rfl (by omega) (by omega) (by omega)
  have d1 : StDC P [.list [.list [.nat n, encFun lab], .nat i]] (.get (arg 0) (.nat 1))
      (natList (acpLabs lab)) 5 0 W := by
    rw [← acp_encFun]
    exact (StDC.get d0 (StDC.nat 1 (by omega)) rfl (by omega)).mono (by omega) (by omega)
  have d2 : StDC P [.list [.list [.nat n, encFun lab], .nat i]] (arg 1) (.nat i) 3 0 W :=
    StDC.arg rfl (by omega) (by omega) (by omega)
  have hgw := wt_nat_le ((acpLabs lab).getD i 0)
  have d3 : StDC P [.list [.list [.nat n, encFun lab], .nat i]]
      (.get (.get (arg 0) (.nat 1)) (arg 1)) (.nat ((acpLabs lab).getD i 0)) 9 0 W :=
    StDC.get d1 d2 hgetv (by omega)
  have hpair : (Val.list [.nat ((acpLabs lab).getD i 0), natList (acpLabs lab)]).wt ≤ W := by
    have := wt_list2_le (.nat ((acpLabs lab).getD i 0)) (natList (acpLabs lab))
    omega
  have d4 := StDC.mk2 d3 d1 hpair (by omega)
  have hC := count_spec hcnt (xs := acpLabs lab) (j := (acpLabs lab).getD i 0) (B := n)
    (acp_labs_le hlab) hgi.le hlen.le
  have h1 := wt_nat_le ((acpLabs lab).count ((acpLabs lab).getD i 0))
  have h2 := acp_count_le lab ((acpLabs lab).getD i 0)
  exact (StDC.call d4 hC (by omega)).mono (by omega) (by omega)

/-- The cost bound of one test, for a context of weight `w`. -/
def acpTB (n w : ℕ) : ℕ := 40 * (16 * w + 60) + countK * (n + 1) ^ 3

theorem acp_wt_pt {c : Val} {i : ℕ} (hi : i < n) (hn : n < c.wt) :
    4 * (Val.list [c, .nat i]).wt + 10 ≤ 16 * c.wt + 59 := by
  have := wt_list2_le c (.nat i)
  have := wt_nat_le i
  omega

theorem acp_n_lt {lab : Fin n → ℕ} : n < (Val.list [.nat n, encFun lab]).wt := by
  have hl : (encFun lab).wt < (Val.list [.nat n, encFun lab]).wt := wt_le_wt_list (by simp)
  have := length_lt_wt_list ((acpLabs lab).map Val.nat)
  simp only [List.length_map, acp_labs_length] at this
  have e : (Val.list ((acpLabs lab).map Val.nat)).wt = (encFun lab).wt := by
    rw [acp_encFun]; rfl
  omega

/-- **The dominance test** of a point. -/
theorem acp_dom_det {P : Program} {fd cnt : ℕ} (hfd : P.funs[fd]? = some (acpDomF cnt))
    (hcnt : P.HasAt cnt (countFuns cnt)) {lab : Fin n → ℕ} (hlab : ∀ x, lab x < n) {i : ℕ}
    (hi : i < n) :
    FunDet P fd (.list [.list [.nat n, encFun lab], .nat i]) (boolVal (acpDomQ lab (.nat i)))
      (acpTB n (Val.list [.nat n, encFun lab]).wt) := by
  have hn := acp_n_lt (lab := lab)
  have hW := acp_wt_pt (c := .list [.nat n, encFun lab]) hi hn
  set W := 16 * (Val.list [.nat n, encFun lab]).wt + 59 with hWdef
  have hc : (Val.list [.nat n, encFun lab]).wt <
      (Val.list [.list [.nat n, encFun lab], .nat i]).wt := wt_le_wt_list (by simp)
  have hnw := wt_nat_le n
  have d0 : StDC P [.list [.list [.nat n, encFun lab], .nat i]] (arg 0)
      (.list [.nat n, encFun lab]) 3 0 W :=
    StDC.arg rfl (by omega) (by omega) (by omega)
  have d1 : StDC P [.list [.list [.nat n, encFun lab], .nat i]] (.get (arg 0) (.nat 0))
      (.nat n) 5 0 W :=
    (StDC.get d0 (StDC.nat 0 (by omega)) rfl (by omega)).mono (by omega) (by omega)
  have dc := acp_cnt_det hcnt hlab hi (W := W) (by omega)
  have hcl := acp_count_le lab ((acpLabs lab).getD i 0)
  have d2 := StDC.arith' (op := .mul)
    (z := 2 * (acpLabs lab).count ((acpLabs lab).getD i 0)) (StDC.nat (P := P)
    (env := [.list [.list [.nat n, encFun lab], .nat i]]) 2 (by omega)) dc rfl (by omega)
  have d3 := StDC.arith' (op := .lt) d1 d2 rfl
    (by simp only [BinOp.eval]; split_ifs <;> omega)
  refine FunDet.intro hfd (d3.det.mono ?_ |>.post fun c hc => ⟨?_, hc⟩)
  · simp only [acpTB]; omega
  · show Val.nat (if _ then 1 else 0) = Val.nat (decide _).toNat
    split_ifs with h
    · rw [decide_eq_true h]; rfl
    · rw [decide_eq_false h]; rfl

/-- **The support test** of a point. -/
theorem acp_supp_det {P : Program} {fs cnt : ℕ} (hfs : P.funs[fs]? = some (acpSuppF cnt))
    (hcnt : P.HasAt cnt (countFuns cnt)) {lab : Fin n → ℕ} (hlab : ∀ x, lab x < n) {i : ℕ}
    (hi : i < n) :
    FunDet P fs (.list [.list [.nat n, encFun lab], .nat i]) (boolVal (acpSuppQ lab (.nat i)))
      (acpTB n (Val.list [.nat n, encFun lab]).wt) := by
  have hn := acp_n_lt (lab := lab)
  have hW := acp_wt_pt (c := .list [.nat n, encFun lab]) hi hn
  set W := 16 * (Val.list [.nat n, encFun lab]).wt + 59 with hWdef
  have dc := acp_cnt_det hcnt hlab hi (W := W) (by omega)
  have d1 := StDC.arith' (op := .eq) (StDC.nat (P := P)
    (env := [.list [.list [.nat n, encFun lab], .nat i]]) 1 (by omega)) dc rfl
    (by simp only [BinOp.eval]; split_ifs <;> omega)
  have d2 := StDC.arith' (op := .sub) (StDC.nat (P := P)
    (env := [.list [.list [.nat n, encFun lab], .nat i]]) 1 (by omega)) d1 rfl
    (by simp only [BinOp.eval]; split_ifs <;> omega)
  refine FunDet.intro hfs (d2.det.mono ?_ |>.post fun c hc => ⟨?_, hc⟩)
  · simp only [acpTB]; omega
  · show Val.nat (1 - if _ then 1 else 0) = Val.nat (decide _).toNat
    split_ifs with h
    · have h2 : ¬ ((acpLabs lab).count ((acpLabs lab).getD i 0) ≠ 1) := fun h' => h' h.symm
      rw [decide_eq_false h2]; rfl
    · have h2 : (acpLabs lab).count ((acpLabs lab).getD i 0) ≠ 1 := fun h' => h h'.symm
      rw [decide_eq_true h2]; rfl

/-! ### The filters -/

theorem acp_getD (lab : Fin n → ℕ) (b : Fin n) : (acpLabs lab).getD b 0 = lab b := by
  rw [List.getD_eq_getElem _ _ (by simp [acp_labs_length])]
  simp [acpLabs]

theorem acp_range : (List.range n).map Val.nat = ((List.finRange n).map Fin.val).map Val.nat := by
  rw [List.map_coe_finRange_eq_range]

theorem acp_encPts_eq (l : List (Fin n)) :
    encPts l = Val.list (List.map (fun i : Fin n => Val.nat i.val) l) := by
  unfold encPts; congr 1; induction l <;> simp_all

/-- The filter of the dominance test is the list of dominant points. -/
theorem acp_filter_dom (lab : Fin n → ℕ) :
    Val.list (((List.range n).map Val.nat).filter (acpDomQ lab)) = encPts (acDom lab) := by
  rw [acp_encPts_eq, acp_range, List.map_map, List.filter_map, acDom]
  refine congrArg (fun l => Val.list (List.map (fun i : Fin n => Val.nat i.val) l))
    (List.filter_congr fun b _ => ?_)
  simp only [Function.comp, acpDomQ, acSize]
  rw [acp_getD]; rfl

/-- The filter of the support test has `acSupp lab` entries. -/
theorem acp_filter_supp (lab : Fin n → ℕ) :
    (((List.range n).map Val.nat).filter (acpSuppQ lab)).length = acSupp lab := by
  rw [acp_range, List.map_map, List.filter_map, acSupp, List.length_map]
  congr 2
  funext b
  simp only [Function.comp, acpSuppQ, acSize]
  rw [acp_getD]; rfl

/-! ### The giant test -/

/-- The bound of a primitive on values of weight at most `B`. -/
def acpPB (p : Prim) (B : ℕ) : ℕ := p.c * (B + 2) ^ p.k

theorem acp_bound_le (p : Prim) {v : Val} {B : ℕ} (h : v.wt ≤ B) : p.bound v ≤ acpPB p B := by
  unfold Prim.bound acpPB
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := v.size_le_wt; omega) _)

theorem acp_pb_mono (p : Prim) {B B' : ℕ} (h : B ≤ B') : acpPB p B ≤ acpPB p B' :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-- On `[gv, D]`: `2` if `2 |H| < |D|! · |H_(D)|`, else `1`. -/
def acpGiantF (pst fac jo : ℕ) : Expr :=
  .letE (.call pst (.var 0))
    (.ite (.arith .lt (.arith .mul (.nat 2) (.prim jo (arg 0)))
        (.arith .mul (.call fac (.length (arg 1))) (.prim jo (.var 1))))
      (.nat 2) (.nat 1))

theorem acp_wt_fact (r : ℕ) : (Val.nat r.factorial).wt ≤ r ^ 2 + 3 := by
  rw [wt_nat]
  have h1 : r.factorial < 2 ^ (r ^ 2) + 1 := by
    have := Nat.factorial_le_pow r
    have h2 : r ^ r ≤ (2 ^ r) ^ r := Nat.pow_le_pow_left Nat.lt_two_pow_self.le r
    rw [← pow_mul, ← sq] at h2
    omega
  have : GI.Machine.len r.factorial ≤ r ^ 2 + 1 := by
    apply GI.Machine.len_le_iff.mpr
    have := Nat.one_le_two_pow (n := r ^ 2)
    rw [pow_succ]; omega
  omega

theorem acp_wt_mul_lt {a b : ℕ} {i j : ℕ} (ha : a < 2 ^ i) (hb : b < 2 ^ j) :
    (Val.nat (a * b)).wt ≤ i + j + 2 := by
  rw [wt_nat]
  have : a * b < 2 ^ (i + j) := by
    rw [pow_add]
    exact lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le ha hb.le (by positivity))
      (le_refl _) |>.trans_le (le_refl _)
  have := GI.Machine.len_le_iff.mpr this
  omega

/-- An order call, in units of a weight bound. -/
theorem acp_ord_dc (hO : GroupOrder) {P : Program} {env : List Val} {jo : ℕ} {a : Expr} {gv : Val}
    {G : Subgroup (Perm (Fin n))} {na Ea W : ℕ} (hjo : P.prims[jo]? = some (groupOrderPrim hO))
    (ha : StDC P env a gv na Ea W) (hG : GroupVal n gv G) :
    StDC P env (.prim jo a) (.nat (Nat.card G)) na (Ea + (groupOrderPrim hO).bound gv + n ^ 2 + 4)
      W :=
  (order_det hO hjo ha.det hG).mono (by omega)

/-- The cost bound of the giant test, for an argument of weight `a`. -/
def acpGC (p o : Prim) (a : ℕ) : ℕ :=
  acpPB p a + pstabK * a ^ 9 + acpPB o a + acpPB o (400 * (a + 1) ^ 6) + 10 ^ 8 * (a + 1) ^ 8

theorem acpGC_mono (p o : Prim) {a b : ℕ} (h : a ≤ b) : acpGC p o a ≤ acpGC p o b := by
  unfold acpGC
  have h1 := acp_pb_mono p h
  have h2 : a ^ 9 ≤ b ^ 9 := Nat.pow_le_pow_left h 9
  have h3 := acp_pb_mono o h
  have h4 := acp_pb_mono o (Nat.mul_le_mul_left 400 (Nat.pow_le_pow_left (show a + 1 ≤ b + 1 by omega) 6))
  have h5 : (a + 1) ^ 8 ≤ (b + 1) ^ 8 := Nat.pow_le_pow_left (by omega) 8
  have := Nat.mul_le_mul_left pstabK h2
  have := Nat.mul_le_mul_left (10 ^ 8) h5
  omega

/-- The value of the giant test. -/
noncomputable def acpGiantV (H : Subgroup (Perm (Fin n))) (D : List (Fin n)) : ℕ :=
  if 2 * Nat.card H < D.length.factorial * Nat.card (GI.Cited.pointwiseStab H D) then 2 else 1

set_option maxHeartbeats 1000000 in
/-- **The giant test**: on `[encGroup gs, D]`, one pointwise stabilizer, two orders and a
factorial. -/
theorem acp_giant_spec (hst : PointwiseStab) (hO : GroupOrder) {P : Program} {g pst fac jp jo : ℕ}
    (hg : P.funs[g]? = some (acpGiantF pst fac jo)) (hpst : P.HasAt pst (pstabFuns pst jp))
    (hjp : P.prims[jp]? = some (pointwiseStabPrim hst)) (hfac : P.HasAt fac (factFuns fac))
    (hjo : P.prims[jo]? = some (groupOrderPrim hO)) (gs : List (Perm (Fin n))) (D : List (Fin n)) :
    FunDet P g (.list [encGroup gs, encPts D]) (.nat (acpGiantV (gens gs) D))
      (acpGC (pointwiseStabPrim hst) (groupOrderPrim hO)
        (Val.list [encGroup gs, encPts D]).wt) := by
  have hP := pstab_spec hst hpst hjp (G := gens gs) ⟨gs, rfl, rfl⟩ D
  set A := Val.list [encGroup gs, encPts D] with hA
  set a := A.wt with ha
  clear_value a
  -- weights of the argument
  have hgv : (encGroup gs).wt < a := by
    rw [ha]; exact wt_le_wt_list (vs := [encGroup gs, encPts D]) (List.mem_cons_self ..)
  have hDv : (encPts D).wt < a := by
    rw [ha]
    exact wt_le_wt_list (vs := [encGroup gs, encPts D]) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hDl : D.length < a := by
    have := length_lt_wt_list (D.map fun i => Val.nat i.val)
    rw [← acp_encPts_eq, List.length_map] at this
    omega
  have hn : n + 1 ≤ a := by
    have := S_le_wt_encGroup gs
    have : n + 1 ≤ (gs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hcall : EvalAll P [A] (.call pst (.var 0)) (fun w c =>
      GroupVal n w (GI.Cited.pointwiseStab (gens gs) D) ∧ w.wt ≤ 320 * (n + 1) ^ 6 ∧
      c ≤ (A.wt + 1) + ((pointwiseStabPrim hst).bound A + pstabK * a ^ 9) + w.wt + 1) :=
    EvalAll.call_funAll (Det.var' (P := P) (env := [A]) (i := 0) rfl) fun v ca hv => by
      obtain ⟨rfl, hca⟩ := hv
      exact hP.mono fun w cb hw => ⟨hw.1, hw.2.1, by omega⟩
  refine FunAll.intro hg (EvalAll.letE hcall fun w0 c0 hw0 => ?_)
  obtain ⟨hG0, hw0, hc0⟩ := hw0
  -- the deterministic rest, in units of `W`
  obtain ⟨W, hWdef⟩ : ∃ W, W = 400 * (a + 1) ^ 6 := ⟨_, rfl⟩
  have hm1 : 1 ≤ (a + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have ha6 : a + 1 ≤ (a + 1) ^ 6 := Nat.le_self_pow (by omega) _
  have ha2 : (a + 1) ^ 2 ≤ (a + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn6 : (n + 1) ^ 6 ≤ (a + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hn2 : n ^ 2 ≤ (a + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hD2 : D.length ^ 2 ≤ (a + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hAW : A.wt ≤ W := by omega
  have hw0W : w0.wt ≤ W := by omega
  have hcH := GI.CitedChecks.card_lt_two_pow (gens gs)
  have hcS := GI.CitedChecks.card_lt_two_pow (GI.Cited.pointwiseStab (gens gs) D)
  have hfl : D.length.factorial < 2 ^ (D.length ^ 2 + 1) := by
    have := acp_wt_fact D.length
    rw [wt_nat] at this
    exact GI.Machine.len_le_iff.mp (by omega)
  have env1 : ([A, w0] : List Val)[1]? = some w0 := rfl
  have d0 : StDC P [A, w0] (arg 0) (encGroup gs) 3 0 W :=
    StDC.arg rfl hAW (by omega) (by omega)
  have d1 : StDC P [A, w0] (arg 1) (encPts D) 3 0 W :=
    StDC.arg rfl hAW (by omega) (by omega)
  have dH := acp_ord_dc hO hjo d0 ⟨gs, rfl, rfl⟩
  have w2H := acp_wt_mul_lt (a := 2) (b := Nat.card (gens gs)) (i := 2) (j := n ^ 2 + 1)
    (by norm_num) hcH
  have hpm : n ^ 2 ≤ (a + 1) ^ 6 := hn2.trans ha2
  have hqm : D.length ^ 2 ≤ (a + 1) ^ 6 := hD2.trans ha2
  have d2 := StDC.arith (op := .mul) (z := 2 * Nat.card (gens gs))
    (StDC.nat (P := P) (env := [A, w0]) 2 (by omega)) dH rfl (by omega)
  have dlen : StDC P [A, w0] (.length (arg 1)) (.nat D.length) 4 0 W := by
    rw [acp_encPts_eq] at d1
    have := StDC.length d1 (by rw [List.length_map]; omega)
    rwa [List.length_map] at this
  have hF := fact_spec hfac D.length
  have hfw := acp_wt_fact D.length
  have df := StDC.call dlen hF (by omega)
  have dS := acp_ord_dc hO hjo (StDC.var' (P := P) env1 hw0W) hG0
  have wFS := acp_wt_mul_lt hfl hcS
  have d3 := StDC.arith (op := .mul)
    (z := D.length.factorial * Nat.card (GI.Cited.pointwiseStab (gens gs) D)) df dS rfl (by omega)
  have d4 := StDC.arith (op := .lt) d2 d3 rfl
    (by simp only [BinOp.eval]; split_ifs <;> simp [wt_nat, GI.Machine.len_zero] <;> omega)
  have hv2 : StDC P [A, w0] (.nat 2) (.nat 2) 1 0 W := StDC.nat 2 (by omega)
  have hv1 : StDC P [A, w0] (.nat 1) (.nat 1) 1 0 W := StDC.nat 1 (by omega)
  have hvw : (Val.nat (acpGiantV (gens gs) D)).wt ≤ 4 := by
    have := wt_nat_le (acpGiantV (gens gs) D)
    have : acpGiantV (gens gs) D ≤ 2 := by unfold acpGiantV; split_ifs <;> omega
    omega
  have d5 := StDC.ite (v := .nat (acpGiantV (gens gs) D)) (nt := 1) (ne := 1) (Et := 0) (Ee := 0)
    d4
    (fun hx => by
      simp only [BinOp.eval] at hx
      unfold acpGiantV
      rw [if_pos (by by_contra h'; rw [if_neg h'] at hx; exact hx rfl)]
      exact hv2)
    (fun hx => by
      simp only [BinOp.eval] at hx
      unfold acpGiantV
      rw [if_neg (by intro h'; rw [if_pos h'] at hx; exact absurd hx (by norm_num))]
      exact hv1)
    (by omega)
  refine d5.det.post ?_
  intro c hc
  refine ⟨rfl, ?_⟩
  -- the cost
  have b1 := acp_bound_le (pointwiseStabPrim hst) (show A.wt ≤ a by omega)
  have b2 := acp_bound_le (groupOrderPrim hO) (show (encGroup gs).wt ≤ a by omega)
  have b3 := acp_bound_le (groupOrderPrim hO) hw0W
  rw [hWdef] at b3
  have hfc : numK * (D.length + 1) * (D.length + (Val.nat D.length.factorial).wt + 10) ≤
      numK * ((a + 1) * (2 * (a + 1) ^ 2 + 13)) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by nlinarith))
  have hfc' : (a + 1) * (2 * (a + 1) ^ 2 + 13) ≤ 15 * (a + 1) ^ 3 := by nlinarith
  have h38 : (a + 1) ^ 3 ≤ (a + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h68 : (a + 1) ^ 6 ≤ (a + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hnk : numK = 10 ^ 5 := rfl
  have hfc2 : numK * ((a + 1) * (2 * (a + 1) ^ 2 + 13)) ≤ 15 * 10 ^ 5 * (a + 1) ^ 8 := by
    rw [hnk]; nlinarith
  unfold acpGC
  omega

/-! ### The case test -/

/-- **The case test** on `encGroup gs`: orbit labels (`orb`), the list `[0, …, n-1]` (`rng`), the
dominant points (`fd`), the number of points in nontrivial orbits (`fs`), then the giant test
(`g`) or the comparison `2 · supp < n`. -/
def acpCaseF (orb rng fd fs g : ℕ) : Expr :=
  .letE (.call orb (.var 0))
    (.letE (.call rng (.get (.var 0) (.nat 0)))
      (.letE (.call fd (mk2 (mk2 (.get (.var 0) (.nat 0)) (.var 1)) (.var 2)))
        (.letE (.length (.call fs (mk2 (mk2 (.get (.var 0) (.nat 0)) (.var 1)) (.var 2))))
          (.ite (.length (.var 3))
            (.call g (mk2 (.var 0) (.var 3)))
            (.ite (.arith .lt (.arith .mul (.nat 2) (.var 4)) (.get (.var 0) (.nat 0)))
              (.nat 3) (.nat 0))))))

/-- The cost bound of the case test on a group value of weight `G`. -/
def acpCC (p o : Prim) (G : ℕ) : ℕ := acpGC p o (40 * (G + 1) ^ 2) + 10 ^ 15 * (G + 1) ^ 6

/-- The case code from the labels and two orders. -/
theorem acp_code_eq (lab : Fin n → ℕ) (oH oD : ℕ) :
    AggCase.code (acCaseL lab oH oD) = if (acDom lab).length = 0 then
      (if 2 * acSupp lab < n then 3 else 0)
      else (if 2 * oH < (acDom lab).length.factorial * oD then 2 else 1) := by
  unfold acCaseL
  split_ifs <;> simp_all [AggCase.code] <;> omega

theorem acp_filter_natList (q : Val → Bool) :
    ((List.range n).map Val.nat).filter q = ((List.range n).filter (q ∘ Val.nat)).map Val.nat :=
  List.filter_map

theorem acp_wt_filter (q : Val → Bool) :
    (Val.list (((List.range n).map Val.nat).filter q)).wt ≤ 5 * (n + 1) ^ 2 := by
  rw [acp_filter_natList]
  exact wt_natList_le_sq (B := n)
    (fun x hx => (List.mem_range.1 (List.mem_of_mem_filter hx)).le)
    ((List.length_filter_le _ _).trans (by simp))

set_option maxHeartbeats 2000000 in
/-- **The case test as a program**: on `encGroup gs` it returns the code of `aggCase ⟨gs⟩`. The
cost is at most `acpCC` of the weight of the input; it contains the bounds of one call of
**PointwiseStab** and two calls of **GroupOrder**. -/
theorem acp_case_spec (hst : PointwiseStab) (hO : GroupOrder) {P : Program}
    {b orb rng fd pd fs ps cnt g pst fac jp jo : ℕ}
    (hb : P.funs[b]? = some (acpCaseF orb rng fd fs g)) (horb : P.HasAt orb (orbitFuns orb))
    (hrng : P.HasAt rng (rangeFuns rng)) (hfd : P.HasAt fd (filterFuns fd pd))
    (hpd : P.funs[pd]? = some (acpDomF cnt)) (hfs : P.HasAt fs (filterFuns fs ps))
    (hps : P.funs[ps]? = some (acpSuppF cnt)) (hcnt : P.HasAt cnt (countFuns cnt))
    (hg : P.funs[g]? = some (acpGiantF pst fac jo)) (hpst : P.HasAt pst (pstabFuns pst jp))
    (hjp : P.prims[jp]? = some (pointwiseStabPrim hst)) (hfac : P.HasAt fac (factFuns fac))
    (hjo : P.prims[jo]? = some (groupOrderPrim hO)) (gs : List (Perm (Fin n))) :
    FunDet P b (encGroup gs) (.nat (AggCase.code (aggCase (gens gs))))
      (acpCC (pointwiseStabPrim hst) (groupOrderPrim hO) (encGroup gs).wt) := by
  obtain ⟨lab, hO1, hlab, hlt⟩ := orbits_spec horb (1 :: gs)
  have hlab' : ∀ x, lab x < n := fun x => (hlt x).1
  have hcase : aggCase (gens gs) = acCaseL lab (Nat.card (gens gs))
      (Nat.card (GI.Cited.pointwiseStab (gens gs) (acDom lab))) :=
    ac_aggCase_eq (gs := 1 :: gs) (gens_one_cons gs) hlab
  -- weights
  obtain ⟨G, hGdef⟩ : ∃ G, G = (encGroup gs).wt := ⟨_, rfl⟩
  have hSG : (gs.length + 2) * (n + 1) ≤ G := hGdef ▸ S_le_wt_encGroup gs
  have hnG : n + 1 ≤ G := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hSG
  obtain ⟨W, hWdef⟩ : ∃ W, W = 100 * (G + 1) ^ 2 := ⟨_, rfl⟩
  have hn2 : (n + 1) ^ 2 ≤ (G + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hG2 : G + 1 ≤ (G + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hlabw : (encFun lab).wt ≤ 4 * (n + 1) ^ 2 := wt_encFun_le_sq lab fun x => (hlab' x).le
  have hrw : (natList (List.range n)).wt ≤ 5 * (n + 1) ^ 2 :=
    wt_natList_le_sq (B := n) (fun x hx => (List.mem_range.1 hx).le) (by simp)
  have hnw := wt_nat_le n
  have egv : (Val.list [.nat n, .list ((1 :: gs).map encPerm)]).wt = (encGroup gs).wt := rfl
  have hcw := wt_list2_le (.nat n) (encFun lab)
  have hcw2 := wt_list2_le (.list [.nat n, encFun lab]) (natList (List.range n))
  have hdw := acp_wt_filter (n := n) (acpDomQ lab)
  have hsw := acp_wt_filter (n := n) (acpSuppQ lab)
  rw [acp_filter_dom] at hdw
  have hgw := wt_list2_le (encGroup gs) (encPts (acDom lab))
  -- the steps
  have d0 : StDC P [encGroup gs] (.var 0) (encGroup gs) 1 0 W := StDC.var' rfl (by omega)
  have d1 := StDC.call d0 hO1 (by omega)
  refine FunDet.intro hb ?_
  have dn : ∀ rest : List Val, StDC P (encGroup gs :: rest) (.get (.var 0) (.nat 0)) (.nat n) 3 0 W :=
    fun rest => StDC.get (StDC.var' (v := Val.list [.nat n, .list ((1 :: gs).map encPerm)]) rfl
      (by omega)) (StDC.nat 0 (by omega)) rfl (by omega)
  have hR : FunDet P rng (.nat n) (natList (List.range n))
      (loopModK * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1)) :=
    (range_spec hrng n).mono fun w c ⟨h1, h2⟩ => ⟨h1, h1 ▸ h2⟩
  have d2 := StDC.call (dn [encFun lab]) hR (by omega)
  -- the context of the filters
  set E3 : List Val := [encGroup gs, encFun lab, natList (List.range n)] with hE3
  have dctx : ∀ rest : List Val, StDC P (E3 ++ rest)
      (mk2 (mk2 (.get (.var 0) (.nat 0)) (.var 1)) (.var 2))
      (.list [.list [.nat n, encFun lab], natList (List.range n)]) 11 0 W := fun rest =>
    (StDC.mk2 (StDC.mk2 (dn _) (StDC.var' (i := 1) rfl (by omega)) (by omega) (by omega))
      (StDC.var' (i := 2) rfl (by omega)) (by omega) (by omega)).mono (by omega) le_rfl
  have hxs : natList (List.range n) = .list ((List.range n).map Val.nat) := rfl
  have hFd := filter_spec hfd (c := .list [.nat n, encFun lab]) (xs := (List.range n).map Val.nat)
    (q := acpDomQ lab) (B := fun _ => acpTB n (Val.list [.nat n, encFun lab]).wt) (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact acp_dom_det hpd hcnt hlab' (List.mem_range.1 hi))
  have hFs := filter_spec hfs (c := .list [.nat n, encFun lab]) (xs := (List.range n).map Val.nat)
    (q := acpSuppQ lab) (B := fun _ => acpTB n (Val.list [.nat n, encFun lab]).wt) (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact acp_supp_det hps hcnt hlab' (List.mem_range.1 hi))
  rw [← hxs] at hFd hFs
  set CF := (((List.range n).map Val.nat).map
      fun _ => acpTB n (Val.list [.nat n, encFun lab]).wt).sum with hCF
  have hFd' : FunDet P fd (.list [.list [.nat n, encFun lab], natList (List.range n)])
      (encPts (acDom lab)) (CF + loopModK * (((List.range n).map Val.nat).length + 1) *
        ((Val.list [.list [.nat n, encFun lab], natList (List.range n)]).wt +
          ((List.range n).map Val.nat).length + (encPts (acDom lab)).wt + 1)) :=
    hFd.mono fun w c ⟨h1, h2⟩ => by
      rw [acp_filter_dom] at h1; subst h1; exact ⟨rfl, h2⟩
  have hFs' : FunDet P fs (.list [.list [.nat n, encFun lab], natList (List.range n)])
      (.list (((List.range n).map Val.nat).filter (acpSuppQ lab)))
      (CF + loopModK * (((List.range n).map Val.nat).length + 1) *
        ((Val.list [.list [.nat n, encFun lab], natList (List.range n)]).wt +
          ((List.range n).map Val.nat).length +
          (Val.list (((List.range n).map Val.nat).filter (acpSuppQ lab))).wt + 1)) :=
    hFs.mono fun w c ⟨h1, h2⟩ => by subst h1; exact ⟨rfl, h2⟩
  have d3 := StDC.call (dctx []) hFd' (by omega)
  rw [List.append_nil] at d3
  have hsl : (((List.range n).map Val.nat).filter (acpSuppQ lab)).length + 2 ≤ W := by
    have := length_lt_wt_list (((List.range n).map Val.nat).filter (acpSuppQ lab))
    omega
  have d4 := StDC.length (StDC.call (dctx [encPts (acDom lab)]) hFs' (by omega)) hsl
  rw [acp_filter_supp] at d4
  -- the branch
  set E5 : List Val := [encGroup gs, encFun lab, natList (List.range n), encPts (acDom lab),
    .nat (acSupp lab)] with hE5
  have hlenD : (acDom lab).length ≤ n := (List.length_filter_le _ _).trans (by simp)
  have dlen : StDC P E5 (.length (.var 3)) (.nat (acDom lab).length) 2 0 W := by
    have hv : (Val.list ((acDom lab).map fun i => Val.nat i.val)).wt ≤ W := by
      rw [← acp_encPts_eq]; omega
    have := StDC.length (P := P) (env := E5) (W := W) (vs := (acDom lab).map fun i => Val.nat i.val)
      (StDC.var' (i := 3) (by rw [hE5, acp_encPts_eq]; rfl) hv) (by simp; omega)
    simpa using this
  have hsupp : acSupp lab ≤ n := (List.length_filter_le _ _).trans (by simp)
  have hgiant := acp_giant_spec hst hO hg hpst hjp hfac hjo gs (acDom lab)
  have hGC := acpGC_mono (pointwiseStabPrim hst) (groupOrderPrim hO)
    (show (Val.list [encGroup gs, encPts (acDom lab)]).wt ≤ 40 * (G + 1) ^ 2 by omega)
  have dif := StDC.ite (v := .nat (AggCase.code (aggCase (gens gs)))) dlen
    (nt := 6) (Et := acpGC (pointwiseStabPrim hst) (groupOrderPrim hO)
      (Val.list [encGroup gs, encPts (acDom lab)]).wt)
    (ne := 10) (Ee := 0)
    (fun hx => by
      have v0 : StDC P E5 (.var 0) (encGroup gs) 1 0 W := StDC.var' (i := 0) rfl (by omega)
      have v3 : StDC P E5 (.var 3) (encPts (acDom lab)) 1 0 W := StDC.var' (i := 3) rfl (by omega)
      have dg := StDC.call (StDC.mk2 v0 v3 (by omega) (by omega)) hgiant (by
          have := wt_nat_le (acpGiantV (gens gs) (acDom lab))
          have : acpGiantV (gens gs) (acDom lab) ≤ 2 := by unfold acpGiantV; split_ifs <;> omega
          omega)
      rw [hcase, acp_code_eq, if_neg hx]
      exact dg.mono (by omega) (by omega))
    (fun hx => by
      have := wt_nat_le (acSupp lab)
      have da := StDC.arith' (op := .mul) (z := 2 * acSupp lab)
        (StDC.nat (P := P) (env := E5) (W := W) 2 (by omega))
        (StDC.var' (i := 4) (v := .nat (acSupp lab)) rfl (by omega)) rfl (by omega)
      have dl := StDC.arith' (op := .lt) da (dn _) rfl
        (by simp only [BinOp.eval]; split_ifs <;> omega)
      have d := StDC.ite (v := .nat (if 2 * acSupp lab < n then 3 else 0)) dl
        (fun hy => by
          simp only [BinOp.eval] at hy
          rw [if_pos (by by_contra h'; rw [if_neg h'] at hy; exact hy rfl)]
          exact StDC.nat 3 (by omega))
        (fun hy => by
          simp only [BinOp.eval] at hy
          rw [if_neg (by intro h'; rw [if_pos h'] at hy; exact absurd hy (by norm_num))]
          exact StDC.nat 0 (by omega))
        (by split_ifs <;> exact (wt_nat_le _).trans (by omega))
      rw [hcase, acp_code_eq, if_pos hx]
      exact d.mono (by omega) (by omega))
    (by
      have : AggCase.code (aggCase (gens gs)) ≤ 3 := by
        cases aggCase (gens gs) <;> simp [AggCase.code]
      have := wt_nat_le (AggCase.code (aggCase (gens gs)))
      omega)
  have hcodew : (Val.nat (AggCase.code (aggCase (gens gs)))).wt ≤ 5 := by
    have : AggCase.code (aggCase (gens gs)) ≤ 3 := by
      cases aggCase (gens gs) <;> simp [AggCase.code]
    have := wt_nat_le (AggCase.code (aggCase (gens gs)))
    omega
  have hW100 : 100 ≤ W := by rw [hWdef]; have : 1 ≤ (G + 1) ^ 2 := Nat.one_le_pow _ _ (by omega); omega
  have dall := StDC.letE d1 (StDC.letE d2 (StDC.letE d3 (StDC.letE d4 dif (by omega))
    (by omega)) (by omega)) (by omega)
  refine dall.det.mono ?_
  -- the cost: every piece is at most a multiple of `(G + 1) ^ 6`
  have hlen : (List.map Val.nat (List.range n)).length = n := by simp
  have hl1 : (1 :: gs).length + 1 = gs.length + 2 := by simp
  have hX1 : 1 ≤ G + 1 := by omega
  have p13 : (G + 1) ^ 1 ≤ (G + 1) ^ 3 := Nat.pow_le_pow_right hX1 (by omega)
  have p23 : (G + 1) ^ 2 ≤ (G + 1) ^ 3 := Nat.pow_le_pow_right hX1 (by omega)
  have p36 : (G + 1) ^ 3 ≤ (G + 1) ^ 6 := Nat.pow_le_pow_right hX1 (by omega)
  have p46 : (G + 1) ^ 4 ≤ (G + 1) ^ 6 := Nat.pow_le_pow_right hX1 (by omega)
  have p56 : (G + 1) ^ 5 ≤ (G + 1) ^ 6 := Nat.pow_le_pow_right hX1 (by omega)
  have e3 : (G + 1) * (G + 1) ^ 2 = (G + 1) ^ 3 := by ring
  have e4 : (G + 1) * (G + 1) ^ 3 = (G + 1) ^ 4 := by ring
  have hOrb : orbitK * (((1 :: gs).length + 1) * (n + 1)) ^ 5 ≤ 1000000 * (G + 1) ^ 6 := by
    rw [hl1]
    show 1000000 * _ ≤ _
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) 5).trans p56)
  have hRng : loopModK * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1) ≤
      8000 * (G + 1) ^ 6 := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul_left loopModK (show n + 1 ≤ G + 1 by omega))
      (show (Val.nat n).wt + n + (natList (List.range n)).wt + 1 ≤ 8 * (G + 1) ^ 2 by omega)
    have : loopModK * (G + 1) * (8 * (G + 1) ^ 2) = 8000 * (G + 1) ^ 3 := by
      simp only [loopModK]; ring
    omega
  have hLp : ∀ v : Val, v.wt ≤ 5 * (n + 1) ^ 2 →
      loopModK * ((List.map Val.nat (List.range n)).length + 1) *
        ((Val.list [Val.list [Val.nat n, encFun lab], natList (List.range n)]).wt +
          (List.map Val.nat (List.range n)).length + v.wt + 1) ≤ 60000 * (G + 1) ^ 6 := by
    intro v hv
    rw [hlen]
    have h := Nat.mul_le_mul (Nat.mul_le_mul_left loopModK (show n + 1 ≤ G + 1 by omega))
      (show (Val.list [Val.list [Val.nat n, encFun lab], natList (List.range n)]).wt + n + v.wt + 1
        ≤ 60 * (G + 1) ^ 2 by omega)
    have : loopModK * (G + 1) * (60 * (G + 1) ^ 2) = 60000 * (G + 1) ^ 3 := by
      simp only [loopModK]; ring
    omega
  have hL1 := hLp _ hdw
  have hL2 := hLp _ hsw
  have hCF' : CF = n * acpTB n (Val.list [.nat n, encFun lab]).wt := by
    rw [hCF, List.map_const', List.sum_replicate, List.length_map, List.length_range, smul_eq_mul]
  have hTB : acpTB n (Val.list [.nat n, encFun lab]).wt ≤ 120000 * (G + 1) ^ 3 := by
    unfold acpTB
    have : (n + 1) ^ 3 ≤ (G + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have := Nat.mul_le_mul_left countK this
    simp only [countK] at this ⊢
    omega
  have hCFb : CF ≤ 120000 * (G + 1) ^ 6 := by
    rw [hCF']
    have h := Nat.mul_le_mul (show n ≤ G + 1 by omega) hTB
    have : (G + 1) * (120000 * (G + 1) ^ 3) = 120000 * (G + 1) ^ 4 := by ring
    omega
  have hacc : acpCC (pointwiseStabPrim hst) (groupOrderPrim hO) (encGroup gs).wt =
      acpGC (pointwiseStabPrim hst) (groupOrderPrim hO) (40 * (G + 1) ^ 2) +
        10 ^ 15 * (G + 1) ^ 6 := by
    rw [← hGdef]; rfl
  rw [hacc]
  omega

end GI.Impl
