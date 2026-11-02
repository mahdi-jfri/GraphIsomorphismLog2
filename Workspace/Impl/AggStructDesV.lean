import Workspace.Impl.AggStructDesCol

/-!
# The Case 3 test as a program: vertex colors and class sizes

For a prefix length `m`, the program lists the vertex colors `stDV` of the `q` labels (a map
over `[0, …, q - 1]` of the color program, `stDV_spec`) and tests whether the class of a color
has at least `3q/4` points (one count, `stDDomV_spec`; for the color of a label, `stDDom_spec`).
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)
open GI.Machine (BinOp)

/-! ### Weights in a context with the facts -/

theorem StDCtx.dl_le {dl tl : List ℕ} {q κ : ℕ} (hc : StDCtx dl tl q κ) :
    ∀ x ∈ dl, x ≤ 2 * (stDA dl tl q κ).wt := fun x hx => by
  have := hc.dl_lt x hx; have := hc.le_wt.1; omega

theorem StDCtx.stDV_le {dl tl : List ℕ} {q κ : ℕ} (hc : StDCtx dl tl q κ) (m : ℕ) :
    ∀ x ∈ stDV dl tl q κ m, x ≤ 2 * (stDA dl tl q κ).wt := by
  intro x hx
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx
  unfold stDCol
  rw [List.getD_eq_getElem?_getD]
  cases h : dl[stDHor q κ (stDE tl m z z) κ]? with
  | none => simp
  | some y => exact hc.dl_le y (List.mem_of_getElem? h)

theorem StDCtx.wt_stDV {dl tl : List ℕ} {q κ : ℕ} (hc : StDCtx dl tl q κ) (m : ℕ) :
    (natList (stDV dl tl q κ m)).wt ≤ 5 * (2 * (stDA dl tl q κ).wt + 1) ^ 2 := by
  refine wt_natList_le_sq (hc.stDV_le m) ?_
  rw [stDV_length]; have := hc.le_wt.2.2; omega

/-! ### The list of vertex colors -/

/-- The function of the map: on `[[A, m], z]`, the color `c(x, z, …, z)`. -/
def stDVF (cf : ℕ) : Expr :=
  .call cf (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1) (arg 1))

/-- On `[A, m]`: the vertex colors, a map (at `mb`) over the range (at `rb`) of `q`. -/
def stDVMapF (mb rb : ℕ) : Expr :=
  .call mb (mk2 (.var 0) (.call rb (.get (arg 0) (.nat 2))))

/-- The cost constant of the vertex colors. -/
def stDVK : ℕ := 10 ^ 12

theorem stDVF_spec {P : Program} {f cf h : ℕ} (hf : P.funs[f]? = some (stDVF cf))
    (hcf : P.funs[cf]? = some (stDColF h)) (hh : P.HasAt h (stDHorFuns h)) {dl tl : List ℕ}
    {q κ : ℕ} (hc : StDCtx dl tl q κ) {m z : ℕ} (hz : z < q) {M : ℕ}
    (hM : (Val.list [stDA dl tl q κ, .nat m]).wt ≤ M) :
    FunDet P f (.list [.list [stDA dl tl q κ, .nat m], .nat z])
      (.nat (stDCol dl tl q κ m z z)) (stDVK * (M + 1) ^ 2) := by
  have hA : (stDA dl tl q κ).wt < (Val.list [stDA dl tl q κ, .nat m]).wt := wt_le_wt_list (by simp)
  have hm : (Val.nat m).wt < (Val.list [stDA dl tl q κ, .nat m]).wt := wt_le_wt_list (by simp)
  have hq := hc.le_wt.2.2
  have hzw := wt_nat_le z
  have hca : (stDCA dl tl q κ m z z).wt ≤ 8 * M + 8 := by
    have := wt_list4_le (stDA dl tl q κ) (.nat m) (.nat z) (.nat z); unfold stDCA; omega
  have hcol := stDCol_spec hcf hh hc m hz hz
  obtain ⟨x, hx⟩ : ∃ x, stDCol dl tl q κ m z z = x := ⟨_, rfl⟩
  rw [hx] at hcol ⊢
  have hxw : (Val.nat x).wt ≤ 2 * M + 2 := by
    have := wt_nat_le x
    have : x ≤ 2 * (stDA dl tl q κ).wt := by
      rw [← hx]
      exact hc.stDV_le m _ (List.mem_map.2 ⟨z, List.mem_range.2 hz, rfl⟩)
    omega
  set W := 30 * M + 60 with hW
  have hvs : (Val.list [.list [stDA dl tl q κ, .nat m], .nat z]).wt ≤ W := by
    have := wt_list2_le (.list [stDA dl tl q κ, .nat m]) (.nat z); omega
  have g0 : StDC P [.list [.list [stDA dl tl q κ, .nat m], .nat z]] (arg 0)
      (.list [stDA dl tl q κ, .nat m]) 3 0 W := StDC.arg rfl hvs (by omega) (by omega)
  have gA := StDC.get (v := stDA dl tl q κ) g0 (StDC.nat 0 (by omega)) rfl (by omega)
  have gm := StDC.get (v := .nat m) g0 (StDC.nat 1 (by omega)) rfl (by omega)
  have gz : StDC P [.list [.list [stDA dl tl q κ, .nat m], .nat z]] (arg 1) (.nat z) 3 0 W :=
    StDC.arg rfl hvs (by omega) (by omega)
  have g4 := StDC.mk4 gA gm gz gz (by
    have := wt_list4_le (stDA dl tl q κ) (.nat m) (.nat z) (.nat z); omega) (by omega)
  have gc := StDC.call g4 hcol (by omega)
  refine StDC.funDet hf gc ?_
  have h1 : (8 * M + 8 + 1) ^ 2 ≤ 81 * (M + 1) ^ 2 := by nlinarith
  have h3 : ((stDCA dl tl q κ m z z).wt + 1) ^ 2 ≤ (8 * M + 8 + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have h5 : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  generalize (M + 1) ^ 2 = X at *
  generalize ((stDCA dl tl q κ m z z).wt + 1) ^ 2 = Y at *
  have h6 : stDColK * Y ≤ stDColK * (81 * X) := Nat.mul_le_mul_left _ (h3.trans h1)
  unfold stDVK
  unfold stDColK at h6 ⊢
  omega

/-- **Range**, with a polynomial bound. -/
theorem st_range_det {P : Program} {b : ℕ} (h : P.HasAt b (rangeFuns b)) (n : ℕ) :
    FunDet P b (.nat n) (natList (List.range n)) (10000 * (n + 1) ^ 3) := by
  refine (range_spec h n).mono fun w c hw => ⟨hw.1, ?_⟩
  obtain ⟨rfl, hc⟩ := hw
  have h1 : (natList (List.range n)).wt ≤ 5 * (n + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => (List.mem_range.1 hx).le) (by simp)
  have h2 := wt_nat_le n
  have h3 : loopModK * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1) ≤
      loopModK * (n + 1) * (10 * (n + 1) ^ 2) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  have e : loopModK * (n + 1) * (10 * (n + 1) ^ 2) = 10000 * (n + 1) ^ 3 := by
    unfold loopModK; ring
  omega

theorem st_natList_range (n : ℕ) : natList (List.range n) = .list ((List.range n).map .nat) := rfl

/-- The cost constant of the list of vertex colors. -/
def stDVMK : ℕ := 10 ^ 15

/-- **The vertex colors**: on `[A, m]`, the list `stDV`. -/
theorem stDV_spec {P : Program} {f mb rb vf cf h : ℕ} (hf : P.funs[f]? = some (stDVMapF mb rb))
    (hmb : P.HasAt mb (mapFuns mb vf)) (hrb : P.HasAt rb (rangeFuns rb))
    (hvf : P.funs[vf]? = some (stDVF cf)) (hcf : P.funs[cf]? = some (stDColF h))
    (hh : P.HasAt h (stDHorFuns h)) {dl tl : List ℕ} {q κ : ℕ} (hc : StDCtx dl tl q κ) (m : ℕ)
    {M : ℕ} (hM : (Val.list [stDA dl tl q κ, .nat m]).wt ≤ M) :
    FunDet P f (.list [stDA dl tl q κ, .nat m]) (natList (stDV dl tl q κ m))
      (stDVMK * (M + 1) ^ 3) := by
  have hA : (stDA dl tl q κ).wt < (Val.list [stDA dl tl q κ, .nat m]).wt := wt_le_wt_list (by simp)
  have hq := hc.le_wt.2.2
  have hqw : (Val.nat q).wt < (stDA dl tl q κ).wt := wt_stDA_ge.2.2.2.2.1
  have hX1 : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hX2 : (M + 1) ^ 2 ≤ (M + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hX3 : (M + 1) * (M + 1) ^ 2 = (M + 1) ^ 3 := by ring
  -- the map
  have hmap := map_spec hmb (c := .list [stDA dl tl q κ, .nat m]) (xs := (List.range q).map .nat)
    (R := fun x w => ∃ z, x = Val.nat z ∧ w = Val.nat (stDCol dl tl q κ m z z))
    (B := fun _ => stDVK * (M + 1) ^ 2) (fun x hx => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
      exact FunAll.mono (stDVF_spec hvf hcf hh hc (List.mem_range.1 hz) hM) fun w c hw =>
        ⟨⟨z, rfl, hw.1⟩, hw.2⟩)
  have hV : ∀ ws, List.Forall₂ (fun x w => ∃ z, x = Val.nat z ∧ w = Val.nat (stDCol dl tl q κ m z z))
      ((List.range q).map .nat) ws → Val.list ws = natList (stDV dl tl q κ m) := by
    intro ws hws
    have := forall₂_map_eq (l := List.range q) (f := Val.nat)
      (g := fun z => Val.nat (stDCol dl tl q κ m z z)) (fun z _ w ⟨z', h1, h2⟩ => by
        cases h1; exact h2) hws
    rw [this]; simp [natList, stDV, List.map_map, Function.comp_def]
  have hVw := hc.wt_stDV m
  have hRw : (natList (List.range q)).wt ≤ 5 * (M + 1) ^ 2 := by
    have := wt_natList_le_sq (xs := List.range q) (B := q) (fun x hx => (List.mem_range.1 hx).le)
      (by simp)
    have : (q + 1) ^ 2 ≤ (M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hcw : (Val.list [.list [stDA dl tl q κ, .nat m], natList (List.range q)]).wt ≤
      16 * (M + 1) ^ 2 := by
    have := wt_list2_le (.list [stDA dl tl q κ, .nat m]) (natList (List.range q)); omega
  have hVw' : (natList (stDV dl tl q κ m)).wt ≤ 20 * (M + 1) ^ 2 := by
    have : (2 * (stDA dl tl q κ).wt + 1) ^ 2 ≤ (2 * (M + 1)) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have e : (2 * (M + 1)) ^ 2 = 4 * (M + 1) ^ 2 := by ring
    omega
  have hmapD : FunDet P mb (.list [.list [stDA dl tl q κ, .nat m], natList (List.range q)])
      (natList (stDV dl tl q κ m)) ((M + 1) * (stDVK * (M + 1) ^ 2) +
        mapK * (M + 1) * (40 * (M + 1) ^ 2)) := by
    refine hmap.mono fun w c hw => ?_
    obtain ⟨ws, rfl, hws, hcost⟩ := hw
    have hw' := hV ws hws
    refine ⟨hw', ?_⟩
    rw [hw'] at hcost
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map,
      List.length_range] at hcost
    have h1 : q * (stDVK * (M + 1) ^ 2) ≤ (M + 1) * (stDVK * (M + 1) ^ 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : mapK * (q + 1) * ((Val.list [.list [stDA dl tl q κ, .nat m],
        .list ((List.range q).map .nat)]).wt + (natList (stDV dl tl q κ m)).wt + 1) ≤
        mapK * (M + 1) * (40 * (M + 1) ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by
        rw [← st_natList_range]; omega)
    omega
  -- the body
  set W := 40 * (M + 1) ^ 2 with hW
  have g0 : StDC P [.list [stDA dl tl q κ, .nat m]] (arg 0) (stDA dl tl q κ) 3 0 W :=
    StDC.arg rfl (by omega) (by omega) (by omega)
  have gq := StDC.get (v := .nat q) g0 (StDC.nat 2 (by omega)) rfl (by omega)
  have gr := StDC.call gq (st_range_det hrb q) (by omega)
  have gv : StDC P [.list [stDA dl tl q κ, .nat m]] (.var 0) (.list [stDA dl tl q κ, .nat m]) 1 0
    W := StDC.var' rfl (by omega)
  have g2 := StDC.mk2 gv gr (hcw.trans (by omega)) (by omega)
  have gm := StDC.call g2 hmapD (by omega)
  refine StDC.funDet hf gm ?_
  have hd : 10000 * (q + 1) ^ 3 ≤ 10000 * (M + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have e1 : (M + 1) * (stDVK * (M + 1) ^ 2) = stDVK * (M + 1) ^ 3 := by rw [← hX3]; ring
  have e2 : mapK * (M + 1) * (40 * (M + 1) ^ 2) = 40 * mapK * (M + 1) ^ 3 := by rw [← hX3]; ring
  rw [e1, e2] at *
  generalize (M + 1) ^ 3 = Y at *
  generalize (M + 1) ^ 2 = X at *
  unfold stDVMK stDVK mapK
  omega

/-! ### Large classes -/

/-- On `[[V, q], j]`: whether `3q < 4 · (count of j in V) + 1`, with the count module at
`cb`. -/
def stDDomVF (cb : ℕ) : Expr :=
  .arith .lt (.arith .mul (.nat 3) (.get (arg 0) (.nat 1)))
    (.arith .add (.arith .mul (.nat 4) (.call cb (mk2 (arg 1) (.get (arg 0) (.nat 0))))) (.nat 1))

/-- On `[[V, q], z]`: the test of `stDDomVF` (at `dv`) on the color of label `z`. -/
def stDDomF (dv : ℕ) : Expr :=
  .call dv (mk2 (arg 0) (.get (.get (arg 0) (.nat 0)) (arg 1)))

/-- The cost constant of the class tests. -/
def stDDomK : ℕ := 10 ^ 8

theorem st_lt_toNat (a b : ℕ) : BinOp.eval .lt a (b + 1) = (decide (a ≤ b)).toNat := by
  simp only [BinOp.eval]
  by_cases h : a ≤ b
  · rw [if_pos (by omega), decide_eq_true h]; rfl
  · rw [if_neg (by omega), decide_eq_false h]; rfl

theorem st_wt_ctxV {V : List ℕ} {q B : ℕ} (hV : ∀ x ∈ V, x ≤ B) (hl : V.length = q)
    (hq : q ≤ B) : (Val.list [natList V, .nat q]).wt ≤ 20 * (B + 1) ^ 2 := by
  have h1 := wt_natList_le_sq hV (by omega)
  have h2 := wt_nat_le q
  have h3 := wt_list2_le (natList V) (.nat q)
  have : B + 1 ≤ (B + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

theorem stDDomV_spec {P : Program} {f cb : ℕ} (hf : P.funs[f]? = some (stDDomVF cb))
    (hcb : P.HasAt cb (countFuns cb)) {V : List ℕ} {q B : ℕ} (hV : ∀ x ∈ V, x ≤ B)
    (hl : V.length = q) (hq : q ≤ B) {j : ℕ} (hj : j ≤ B) :
    FunDet P f (.list [.list [natList V, .nat q], .nat j]) (boolVal (stDDomV V q j))
      (stDDomK * (B + 1) ^ 3) := by
  have hc := st_wt_ctxV hV hl hq
  have hVc : (natList V).wt < (Val.list [natList V, .nat q]).wt := wt_le_wt_list (by simp)
  have hqc : (Val.nat q).wt < (Val.list [natList V, .nat q]).wt := wt_le_wt_list (by simp)
  have hX : B + 1 ≤ (B + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hX3 : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hcnt := count_spec hcb hV hj (by omega) (xs := V)
  have hcle : V.count j ≤ B := (List.count_le_length).trans (by omega)
  set W := 100 * (B + 1) ^ 2 + 10 with hW
  have hjw := wt_nat_le j
  have hvs : (Val.list [.list [natList V, .nat q], .nat j]).wt ≤ W := by
    have := wt_list2_le (.list [natList V, .nat q]) (.nat j); omega
  have g0 : StDC P [.list [.list [natList V, .nat q], .nat j]] (arg 0)
      (.list [natList V, .nat q]) 3 0 W := StDC.arg rfl hvs (by omega) (by omega)
  have g1 : StDC P [.list [.list [natList V, .nat q], .nat j]] (arg 1) (.nat j) 3 0 W :=
    StDC.arg rfl hvs (by omega) (by omega)
  have gV := StDC.get (v := natList V) g0 (StDC.nat 0 (by omega)) rfl (by omega)
  have gq := StDC.get (v := .nat q) g0 (StDC.nat 1 (by omega)) rfl (by omega)
  have g2 := StDC.mk2 g1 gV (by have := wt_list2_le (.nat j) (natList V); omega) (by omega)
  have gc := StDC.call g2 hcnt (by have := wt_nat_le (V.count j); omega)
  have g3q := StDC.arith' (StDC.nat 3 (by omega)) gq (op := .mul)
    (show BinOp.eval .mul 3 q = 3 * q from rfl) (by omega)
  have g4c := StDC.arith' (StDC.nat 4 (by omega)) gc (op := .mul)
    (show BinOp.eval .mul 4 (V.count j) = 4 * V.count j from rfl) (by omega)
  have g4c1 := StDC.arith' g4c (StDC.nat 1 (by omega)) (op := .add)
    (show BinOp.eval .add (4 * V.count j) 1 = 4 * V.count j + 1 from rfl) (by omega)
  have gr := StDC.arith' g3q g4c1 (op := .lt) (st_lt_toNat _ _) (by
    have : (decide (3 * q ≤ 4 * V.count j)).toNat ≤ 1 := Bool.toNat_le _; omega)
  refine StDC.funDet hf gr ?_
  unfold stDDomK
  unfold countK at *
  generalize (B + 1) ^ 3 = Y at *
  generalize (B + 1) ^ 2 = X at *
  omega

theorem stDDom_spec {P : Program} {f dv cb : ℕ} (hf : P.funs[f]? = some (stDDomF dv))
    (hdv : P.funs[dv]? = some (stDDomVF cb))
    (hcb : P.HasAt cb (countFuns cb)) {V : List ℕ} {q B : ℕ} (hV : ∀ x ∈ V, x ≤ B)
    (hl : V.length = q) (hq : q ≤ B) {z : ℕ} (hz : z < q) :
    FunDet P f (.list [.list [natList V, .nat q], .nat z]) (boolVal (stDDom V q z))
      (2 * stDDomK * (B + 1) ^ 3) := by
  have hc := st_wt_ctxV hV hl hq
  have hVc : (natList V).wt < (Val.list [natList V, .nat q]).wt := wt_le_wt_list (by simp)
  have hqc : (Val.nat q).wt < (Val.list [natList V, .nat q]).wt := wt_le_wt_list (by simp)
  have hX : B + 1 ≤ (B + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hX3 : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hzl : z < V.length := by omega
  have hjB : V.getD z 0 ≤ B := by
    rw [List.getD_eq_getElem _ _ hzl]; exact hV _ (List.getElem_mem hzl)
  have hd := stDDomV_spec hdv hcb hV hl hq hjB
  set W := 100 * (B + 1) ^ 2 + 10 with hW
  have hzw := wt_nat_le z
  have hjw := wt_nat_le (V.getD z 0)
  have hvs : (Val.list [.list [natList V, .nat q], .nat z]).wt ≤ W := by
    have := wt_list2_le (.list [natList V, .nat q]) (.nat z); omega
  have g0 : StDC P [.list [.list [natList V, .nat q], .nat z]] (arg 0)
      (.list [natList V, .nat q]) 3 0 W := StDC.arg rfl hvs (by omega) (by omega)
  have g1 : StDC P [.list [.list [natList V, .nat q], .nat z]] (arg 1) (.nat z) 3 0 W :=
    StDC.arg rfl hvs (by omega) (by omega)
  have gV := StDC.get (v := natList V) g0 (StDC.nat 0 (by omega)) rfl (by omega)
  have gj := StDC.get (v := .nat (V.getD z 0)) gV g1
    (by simp [List.getElem?_eq_getElem hzl]) (by omega)
  have g2 := StDC.mk2 g0 gj (by
    have := wt_list2_le (.list [natList V, .nat q]) (.nat (V.getD z 0)); omega) (by omega)
  have gc := StDC.call g2 hd (by have := wt_boolVal_le (stDDomV V q (V.getD z 0)); omega)
  refine StDC.funDet hf gc ?_
  unfold stDDomK
  generalize (B + 1) ^ 3 = Y at *
  generalize (B + 1) ^ 2 = X at *
  omega

end GI.Impl
