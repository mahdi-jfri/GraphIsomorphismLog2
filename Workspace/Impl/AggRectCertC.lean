import Workspace.Impl.AggRectCertT

/-!
# The certificate search as a program: the conditions

`rcCondF` checks the conditions `rcCond` of a candidate (`AggRectCertMath.lean`) on
`[n, v_L, v_R, v_0, v_U, W, R, Bm]`: it computes the row degrees (a `map` of `count`), the
column degrees (a `map` of `rcColDegF` over the columns) and the twin test (an `all` of
`rcTwT`), and multiplies the eleven `0/1` tests. `rc_cond_spec`: it returns
`boolVal (rcCond …)` at cost `10¹² (M + 1)⁴` for a weight bound `M` of the input.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)
open GI.Machine (BinOp)

/-- The input of the conditions. -/
def rcCondIn (n vL vR v0 vU : ℕ) (wl rl : List ℕ) (bm : List (List ℕ)) : Val :=
  .list [.nat n, .nat vL, .nat vR, .nat v0, .nat vU, natList wl, natList rl, rcTV bm]

/-- The product of the eleven tests, in the environment `[input, rs, cs, tw]`. -/
def rcProdE (cnt : ℕ) : Expr :=
  let nW : Expr := .length (arg 5)
  let nR : Expr := .length (arg 6)
  let c1 : Expr := .arith .lt (.arith .mul (.nat 3) (arg 0)) (.arith .mul (.nat 4) nW)
  let c2 : Expr := .arith .lt (.arith .eq (arg 2) (arg 1)) (.nat 1)
  let c3 : Expr := .arith .lt (.arith .eq (arg 1) (arg 3)) (.nat 1)
  let c4 : Expr := .arith .lt (.arith .eq (arg 2) (arg 3)) (.nat 1)
  let c5 : Expr := .arith .eq (.call cnt (mk2 (.get (.var 1) (.nat 0)) (.var 1))) nW
  let c6 : Expr := .arith .eq (.call cnt (mk2 (.get (.var 2) (.nat 0)) (.var 2))) nR
  let c7 : Expr := .arith .eq (arg 4) (arg 1)
  let c8 : Expr := .arith .lt (.get (.var 2) (.nat 0)) nW
  let c9 : Expr := .var 3
  let c10 : Expr := .arith .lt (.arith .add nW nR) (.arith .add (arg 0) (.nat 1))
  let c11 : Expr := .arith .lt (.arith .mul (.nat 16) (.arith .mul nW nR))
    (.arith .add (.arith .mul (.nat 3) (.arith .mul (arg 0) (arg 0))) (.nat 1))
  .arith .mul (.arith .mul (.arith .mul (.arith .mul (.arith .mul (.arith .mul (.arith .mul
    (.arith .mul (.arith .mul (.arith .mul c1 c2) c3) c4) c5) c6) c7) c8) c9) c10) c11

/-- **The conditions of a candidate** (modules: `mc` map of count, `mcd` map of the column
degree, `rng` range, `al` all of the twin test, `cnt` count). -/
def rcCondF (mc mcd rng al cnt : ℕ) : Expr :=
  .letE (.call mc (mk2 (.nat 1) (arg 7)))
    (.letE (.call mcd (mk2 (arg 7) (.call rng (.length (arg 6)))))
      (.letE (.call al (mk2 (arg 7) (arg 7))) (rcProdE cnt)))

theorem rc_toNat_and (a b : Bool) : (a && b).toNat = a.toNat * b.toNat := by
  cases a <;> cases b <;> rfl

theorem rc_lt_eq_one (a b : ℕ) : BinOp.eval .lt (BinOp.eval .eq a b) 1 = (decide (a ≠ b)).toNat := by
  simp only [BinOp.eval]
  by_cases h : a = b <;> simp [h]

theorem rc_lt_toNat' (a b : ℕ) : BinOp.eval .lt a b = (decide (a < b)).toNat := by
  simp only [BinOp.eval]
  by_cases h : a < b <;> simp [h]

theorem rc_lt_le (a b : ℕ) : BinOp.eval .lt a (b + 1) = (decide (a ≤ b)).toNat := by
  simp only [BinOp.eval]
  by_cases h : a ≤ b
  · rw [if_pos (by omega), decide_eq_true h]; rfl
  · rw [if_neg (by omega), decide_eq_false h]; rfl

theorem rc_toNat_le (b : Bool) : b.toNat + 2 ≤ 3 := by cases b <;> decide

/-! ### The three calls -/

section Calls

variable {P : Program}

theorem rc_len_lt_natList (xs : List ℕ) : xs.length < (natList xs).wt := by
  have := length_lt_wt_list (xs.map Val.nat)
  simpa using this

theorem rc_len_lt_tv (ts : List (List ℕ)) : ts.length < (rcTV ts).wt := by
  have := length_lt_wt_list (ts.map natList)
  simpa using this

set_option maxHeartbeats 1000000 in
/-- The row degrees. -/
theorem rc_rs_det {mc cnt : ℕ} (hmc : P.HasAt mc (mapFuns mc cnt)) (hcnt : P.HasAt cnt (countFuns cnt))
    (bm : List (List ℕ)) (m : ℕ) (hrow : ∀ row ∈ bm, row.length = m)
    (hbit : ∀ row ∈ bm, ∀ x ∈ row, x ≤ 1) {M : ℕ} (hb : (rcTV bm).wt ≤ M) (hm : m ≤ M)
    (h20 : 20 ≤ M) :
    FunDet P mc (.list [.nat 1, rcTV bm]) (natList (bm.map fun row => row.count 1))
      (10 ^ 7 * (M + 1) ^ 4) := by
  have hbl := rc_len_lt_tv bm
  have hm' := rc_mapL hmc (c := .nat 1) (ts := bm) (g := fun row => .nat (row.count 1))
    (B := countK * (M + 1) ^ 3) (fun row hrow' => count_spec hcnt (B := M)
      (fun x hx => (hbit row hrow' x hx).trans (by omega)) (by omega)
      (by rw [hrow row hrow']; exact hm))
  have e : (bm.map fun row => Val.nat (row.count 1)) = (bm.map fun row => row.count 1).map Val.nat := by
    simp [List.map_map]
  rw [e] at hm'
  have hout : (natList (bm.map fun row => row.count 1)).wt ≤ 5 * (M + 1) ^ 2 :=
    rc_wt_natList (fun x hx => by
      obtain ⟨row, hr, rfl⟩ := List.mem_map.1 hx
      have := List.count_le_length (a := 1) (l := row)
      rw [hrow row hr] at this; omega) (by simp; omega)
  refine hm'.mono ?_
  have e2 : (Val.list ((bm.map fun row => row.count 1).map Val.nat)).wt =
    (natList (bm.map fun row => row.count 1)).wt := rfl
  rw [e2]
  have hc := wt_list2_le (.nat 1) (rcTV bm)
  have h1 := wt_nat_le 1
  have hW2 : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hW3 : (M + 1) ^ 2 ≤ (M + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hW4 : (M + 1) ^ 3 ≤ (M + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have e3 : bm.length * (countK * (M + 1) ^ 3) ≤ 10 ^ 5 * (M + 1) ^ 4 := by
    unfold countK
    calc bm.length * (100000 * (M + 1) ^ 3) ≤ (M + 1) * (100000 * (M + 1) ^ 3) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 5 * (M + 1) ^ 4 := by ring
  have e4 : mapK * (bm.length + 1) * ((Val.list [.nat 1, rcTV bm]).wt +
      (natList (bm.map fun row => row.count 1)).wt + 1) ≤ 10 ^ 5 * (M + 1) ^ 4 := by
    unfold mapK
    have : (Val.list [.nat 1, rcTV bm]).wt + (natList (bm.map fun row => row.count 1)).wt + 1 ≤
        20 * (M + 1) ^ 2 := by nlinarith
    calc 1000 * (bm.length + 1) * ((Val.list [.nat 1, rcTV bm]).wt +
        (natList (bm.map fun row => row.count 1)).wt + 1) ≤ 1000 * (M + 1) * (20 * (M + 1) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) this
      _ = 20000 * (M + 1) ^ 3 := by ring
      _ ≤ 10 ^ 5 * (M + 1) ^ 4 := by nlinarith
  omega

set_option maxHeartbeats 1000000 in
/-- The column degrees. -/
theorem rc_cs_det {mcd cd cnt mg gt : ℕ} (hmcd : P.HasAt mcd (mapFuns mcd cd))
    (hcd : P.funs[cd]? = some (rcColDegF cnt mg)) (hcnt : P.HasAt cnt (countFuns cnt))
    (hmg : P.HasAt mg (mapFuns mg gt)) (hgt : P.funs[gt]? = some rcGetT)
    (bm : List (List ℕ)) (m : ℕ) (hrow : ∀ row ∈ bm, row.length = m)
    (hbit : ∀ row ∈ bm, ∀ x ∈ row, x ≤ 1) {M : ℕ} (hb : (rcTV bm).wt ≤ M) (hm : m ≤ M)
    (h20 : 20 ≤ M) :
    FunDet P mcd (.list [rcTV bm, natList (List.range m)]) (natList (rcCols bm m))
      (10 ^ 10 * (M + 1) ^ 4) := by
  have hbl := rc_len_lt_tv bm
  have hm' := rc_mapN hmcd (c := rcTV bm) (xs := List.range m)
    (g := fun j => .nat ((rcCol bm j).count 1)) (B := 10 ^ 6 * (4 * M + 11) ^ 3) (fun j hj => by
      have hj' := List.mem_range.1 hj
      refine rc_colDeg_spec hcd hcnt hmg hgt bm j (fun row hr => by rw [hrow row hr]; exact hj')
        hbit (W := 4 * M + 10) ?_ (by omega)
      have := wt_list2_le (rcTV bm) (.nat j)
      have := wt_nat_le j
      omega)
  have e : ((List.range m).map fun j => Val.nat ((rcCol bm j).count 1)) =
      (rcCols bm m).map Val.nat := by
    simp [rcCols, List.map_map]
  rw [e, List.length_range] at hm'
  have hcb : ∀ x ∈ rcCols bm m, x ≤ M := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    have := List.count_le_length (a := 1) (l := rcCol bm j)
    have e : (rcCol bm j).length = bm.length := by simp [rcCol]
    omega
  have hout : (natList (rcCols bm m)).wt ≤ 5 * (M + 1) ^ 2 :=
    rc_wt_natList hcb (by simp [rcCols]; omega)
  refine hm'.mono ?_
  have e2 : (Val.list ((rcCols bm m).map Val.nat)).wt = (natList (rcCols bm m)).wt := rfl
  rw [e2]
  have hc := wt_list2_le (rcTV bm) (natList (List.range m))
  have hr : (natList (List.range m)).wt ≤ 5 * (M + 1) ^ 2 :=
    rc_wt_natList (fun x hx => by have := List.mem_range.1 hx; omega) (by simp; omega)
  have hW2 : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hW3 : (M + 1) ^ 2 ≤ (M + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hW4 : (M + 1) ^ 3 ≤ (M + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have e3 : m * (10 ^ 6 * (4 * M + 11) ^ 3) ≤ 2 * 10 ^ 9 * (M + 1) ^ 4 := by
    have h1 : (4 * M + 11) ^ 3 ≤ 1331 * (M + 1) ^ 3 := by
      calc (4 * M + 11) ^ 3 ≤ (11 * (M + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        _ = 1331 * (M + 1) ^ 3 := by ring
    calc m * (10 ^ 6 * (4 * M + 11) ^ 3) ≤ (M + 1) * (10 ^ 6 * (1331 * (M + 1) ^ 3)) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ h1)
      _ = 1331 * 10 ^ 6 * (M + 1) ^ 4 := by ring
      _ ≤ 2 * 10 ^ 9 * (M + 1) ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
  have e4 : mapK * (m + 1) * ((Val.list [rcTV bm, natList (List.range m)]).wt +
      (natList (rcCols bm m)).wt + 1) ≤ 10 ^ 5 * (M + 1) ^ 4 := by
    unfold mapK
    have : (Val.list [rcTV bm, natList (List.range m)]).wt + (natList (rcCols bm m)).wt + 1 ≤
        20 * (M + 1) ^ 2 := by nlinarith
    calc 1000 * (m + 1) * ((Val.list [rcTV bm, natList (List.range m)]).wt +
        (natList (rcCols bm m)).wt + 1) ≤ 1000 * (M + 1) * (20 * (M + 1) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) this
      _ = 20000 * (M + 1) ^ 3 := by ring
      _ ≤ 10 ^ 5 * (M + 1) ^ 4 := by nlinarith
  omega

set_option maxHeartbeats 1000000 in
/-- The twin test of all rows. -/
theorem rc_tw_det {al tw fe en : ℕ} (hal : P.HasAt al (allFuns al tw))
    (htw : P.funs[tw]? = some (rcTwT fe)) (hfe : P.HasAt fe (filterFuns fe en))
    (hen : P.HasAt en (eqNatsFuns en)) (bm : List (List ℕ)) {M : ℕ} (hb : (rcTV bm).wt ≤ M)
    (h20 : 20 ≤ M) :
    FunDet P al (.list [rcTV bm, rcTV bm]) (boolVal (bm.all (rcTw bm)))
      (10 ^ 10 * (M + 1) ^ 4) := by
  have hbl := rc_len_lt_tv bm
  have hA := all_spec hal (c := rcTV bm) (xs := bm.map natList) (q := fun v => rcTw bm (rcNats v))
    (B := fun _ => 10 ^ 6 * (4 * M + 11) ^ 3) (fun x hx => by
      obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hx
      have hρw : (natList ρ).wt < (rcTV bm).wt := wt_le_wt_list (List.mem_map_of_mem hρ)
      simp only [rcNats_natList]
      refine rc_twT_spec htw hfe hen bm ρ (W := 4 * M + 10) ?_ (by omega)
      have := wt_list2_le (rcTV bm) (natList ρ)
      omega)
  have e : (bm.map natList).all (fun v => rcTw bm (rcNats v)) = bm.all (rcTw bm) := by
    rw [List.all_map]
    congr 1
    funext ρ
    simp [rcNats_natList]
  refine hA.mono fun w c ⟨h1, h2⟩ => ⟨by rw [h1, e], ?_⟩
  simp only [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at h2
  have hc := wt_list2_le (rcTV bm) (rcTV bm)
  have hW2 : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hW3 : (M + 1) ^ 2 ≤ (M + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hW4 : (M + 1) ^ 3 ≤ (M + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have e3 : bm.length * (10 ^ 6 * (4 * M + 11) ^ 3) ≤ 2 * 10 ^ 9 * (M + 1) ^ 4 := by
    have h1 : (4 * M + 11) ^ 3 ≤ 1331 * (M + 1) ^ 3 := by
      calc (4 * M + 11) ^ 3 ≤ (11 * (M + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        _ = 1331 * (M + 1) ^ 3 := by ring
    calc bm.length * (10 ^ 6 * (4 * M + 11) ^ 3) ≤ (M + 1) * (10 ^ 6 * (1331 * (M + 1) ^ 3)) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ h1)
      _ = 1331 * 10 ^ 6 * (M + 1) ^ 4 := by ring
      _ ≤ 2 * 10 ^ 9 * (M + 1) ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
  have e4 : loopModK * (bm.length + 1) * ((Val.list [rcTV bm, .list (bm.map natList)]).wt +
      bm.length + 4) ≤ 10 ^ 5 * (M + 1) ^ 4 := by
    unfold loopModK
    have e5 : (Val.list [rcTV bm, .list (bm.map natList)]).wt = (Val.list [rcTV bm, rcTV bm]).wt :=
      rfl
    rw [e5]
    have : (Val.list [rcTV bm, rcTV bm]).wt + bm.length + 4 ≤ 10 * (M + 1) := by omega
    calc 1000 * (bm.length + 1) * ((Val.list [rcTV bm, rcTV bm]).wt + bm.length + 4) ≤
        1000 * (M + 1) * (10 * (M + 1)) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) this
      _ = 10000 * (M + 1) ^ 2 := by ring
      _ ≤ 10 ^ 5 * (M + 1) ^ 4 := by nlinarith
  omega

end Calls

/-! ### The conditions -/

set_option maxHeartbeats 4000000 in
/-- **The conditions as a program.** -/
theorem rc_cond_spec {P : Program} {f mc mcd rng al cnt cd mg gt tw fe en : ℕ}
    (hf : P.funs[f]? = some (rcCondF mc mcd rng al cnt))
    (hmc : P.HasAt mc (mapFuns mc cnt)) (hcnt : P.HasAt cnt (countFuns cnt))
    (hmcd : P.HasAt mcd (mapFuns mcd cd)) (hcd : P.funs[cd]? = some (rcColDegF cnt mg))
    (hmg : P.HasAt mg (mapFuns mg gt)) (hgt : P.funs[gt]? = some rcGetT)
    (hrng : P.HasAt rng (rangeFuns rng)) (hal : P.HasAt al (allFuns al tw))
    (htw : P.funs[tw]? = some (rcTwT fe)) (hfe : P.HasAt fe (filterFuns fe en))
    (hen : P.HasAt en (eqNatsFuns en))
    (n vL vR v0 vU : ℕ) (wl rl : List ℕ) (bm : List (List ℕ))
    (hbl : bm.length = wl.length) (hrow : ∀ row ∈ bm, row.length = rl.length)
    (hbit : ∀ row ∈ bm, ∀ x ∈ row, x ≤ 1) (hwne : wl ≠ []) (hrne : rl ≠ []) {M : ℕ}
    (hM : (rcCondIn n vL vR v0 vU wl rl bm).wt ≤ M) (hn : n ≤ M) (h20 : 20 ≤ M) :
    FunDet P f (rcCondIn n vL vR v0 vU wl rl bm) (boolVal (rcCond n vL vR v0 vU wl rl bm))
      (10 ^ 12 * (M + 1) ^ 4) := by
  set vs : List Val := [.nat n, .nat vL, .nat vR, .nat v0, .nat vU, natList wl, natList rl, rcTV bm]
  have hI : (Val.list vs).wt ≤ M := hM
  have hmem : ∀ v ∈ vs, v.wt < (Val.list vs).wt := fun v hv => wt_le_wt_list hv
  have hbw : (rcTV bm).wt < M := (hmem _ (by simp [vs])).trans_le hI
  have hww : (natList wl).wt < M := (hmem _ (by simp [vs])).trans_le hI
  have hrw : (natList rl).wt < M := (hmem _ (by simp [vs])).trans_le hI
  have hwl := rc_len_lt_natList wl
  have hrl := rc_len_lt_natList rl
  have hW2 : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hW3 : (M + 1) ^ 2 ≤ (M + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hW4 : (M + 1) ^ 3 ≤ (M + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hMM : M * M ≤ (M + 1) ^ 2 := by nlinarith
  set Z := 100 * (M + 1) ^ 2 + 100 with hZ
  -- the three calls
  have hrs := rc_rs_det hmc hcnt bm rl.length hrow hbit hbw.le (by omega) h20
  have hcs := rc_cs_det hmcd hcd hcnt hmg hgt bm rl.length hrow hbit hbw.le (by omega) h20
  have htwd := rc_tw_det hal htw hfe hen bm hbw.le h20
  set rs := bm.map fun row => row.count 1 with hrsd
  set cs := rcCols bm rl.length with hcsd
  have hrsb : ∀ x ∈ rs, x ≤ M := by
    intro x hx
    obtain ⟨row, hr, rfl⟩ := List.mem_map.1 hx
    have := List.count_le_length (a := 1) (l := row)
    rw [hrow row hr] at this; omega
  have hcsb : ∀ x ∈ cs, x ≤ M := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    have := List.count_le_length (a := 1) (l := rcCol bm j)
    have e : (rcCol bm j).length = bm.length := by simp [rcCol]
    omega
  have hrsl : rs.length = wl.length := by simp [rs, hbl]
  have hcsl : cs.length = rl.length := by simp [cs, rcCols]
  have hrsw : (natList rs).wt ≤ 5 * (M + 1) ^ 2 := rc_wt_natList hrsb (by omega)
  have hcsw : (natList cs).wt ≤ 5 * (M + 1) ^ 2 := rc_wt_natList hcsb (by omega)
  have hrs0 : 0 < rs.length := by
    rw [hrsl]; exact List.length_pos_of_ne_nil hwne
  have hcs0 : 0 < cs.length := by
    rw [hcsl]; exact List.length_pos_of_ne_nil hrne
  have hcntr := count_spec hcnt (xs := rs) (j := rs.getD 0 0) (B := M) hrsb
    (by rw [List.getD_eq_getElem _ _ hrs0]; exact hrsb _ (List.getElem_mem _)) (by omega)
  have hcntc := count_spec hcnt (xs := cs) (j := cs.getD 0 0) (B := M) hcsb
    (by rw [List.getD_eq_getElem _ _ hcs0]; exact hcsb _ (List.getElem_mem _)) (by omega)
  -- the arguments, in any environment
  have ga : ∀ (rest : List Val) (j : ℕ) (v : Val), vs[j]? = some v → j ≤ 7 →
      StDC P (.list vs :: rest) (arg j) v 3 0 Z := fun rest j v h hj =>
    StDC.arg h (by omega) (by omega) ((hmem v (List.mem_of_getElem? h)).le.trans (by omega))
  -- the first three calls
  have g1 := StDC.call (StDC.mk2 (StDC.nat (env := [.list vs]) 1 (by omega))
    (ga [] 7 _ rfl (by omega)) (by have := wt_list2_le (.nat 1) (rcTV bm); have := wt_nat_le 1; omega)
    (by omega)) hrs (by omega)
  have grng := StDC.call (StDC.length (ga [natList rs] 6 _ rfl (by omega)) (by
      simp only [List.length_map]
      omega)) (st_range_det hrng (rl.map Val.nat).length) (by
    have := rc_wt_natList (xs := List.range rl.length) (B := M)
      (fun x hx => by have := List.mem_range.1 hx; omega) (by simp; omega)
    simp only [List.length_map]
    omega)
  simp only [List.length_map] at grng
  have g2 := StDC.call (StDC.mk2 (ga [natList rs] 7 _ rfl (by omega)) grng (by
    have := wt_list2_le (rcTV bm) (natList (List.range rl.length))
    have := rc_wt_natList (xs := List.range rl.length) (B := M)
      (fun x hx => by have := List.mem_range.1 hx; omega) (by simp; omega)
    omega) (by omega)) hcs (by omega)
  have g3 := StDC.call (StDC.mk2 (ga [natList rs, natList cs] 7 _ rfl (by omega))
    (ga [natList rs, natList cs] 7 _ rfl (by omega)) (by
      have := wt_list2_le (rcTV bm) (rcTV bm); omega) (by omega)) htwd (by
    have := wt_boolVal_le (bm.all (rcTw bm)); simp only [boolVal] at this ⊢; omega)
  -- the product
  set env : List Val := [.list vs, natList rs, natList cs, boolVal (bm.all (rcTw bm))]
  have gA : ∀ (j : ℕ) (v : Val), vs[j]? = some v → j ≤ 7 → StDC P env (arg j) v 3 0 Z :=
    fun j v h hj => ga _ j v h hj
  have gnW : StDC P env (.length (arg 5)) (.nat wl.length) 4 0 Z := by
    have h := StDC.length (vs := wl.map Val.nat) (gA 5 _ rfl (by omega)) (by simp; omega)
    rw [List.length_map] at h
    exact h
  have gnR : StDC P env (.length (arg 6)) (.nat rl.length) 4 0 Z := by
    have h := StDC.length (vs := rl.map Val.nat) (gA 6 _ rfl (by omega)) (by simp; omega)
    rw [List.length_map] at h
    exact h
  have gn := gA 0 (.nat n) rfl (by omega)
  have gvL := gA 1 (.nat vL) rfl (by omega)
  have gvR := gA 2 (.nat vR) rfl (by omega)
  have gv0 := gA 3 (.nat v0) rfl (by omega)
  have gvU := gA 4 (.nat vU) rfl (by omega)
  have hb3 : ∀ b : Bool, b.toNat + 2 ≤ Z := fun b => by have := rc_toNat_le b; omega
  have c1 := StDC.arith' (op := .lt)
    (StDC.arith' (op := .mul) (StDC.nat (env := env) 3 (by omega)) gn rfl (by simp only [BinOp.eval]; omega))
    (StDC.arith' (op := .mul) (StDC.nat (env := env) 4 (by omega)) gnW rfl (by simp only [BinOp.eval]; omega))
    (rc_lt_toNat' _ _) (hb3 _)
  have c2 := StDC.arith' (op := .lt) (StDC.arith' (op := .eq) gvR gvL rfl
      (by simp only [BinOp.eval]; split_ifs <;> omega)) (StDC.nat (env := env) 1 (by omega))
    (rc_lt_eq_one _ _) (hb3 _)
  have c3 := StDC.arith' (op := .lt) (StDC.arith' (op := .eq) gvL gv0 rfl
      (by simp only [BinOp.eval]; split_ifs <;> omega)) (StDC.nat (env := env) 1 (by omega))
    (rc_lt_eq_one _ _) (hb3 _)
  have c4 := StDC.arith' (op := .lt) (StDC.arith' (op := .eq) gvR gv0 rfl
      (by simp only [BinOp.eval]; split_ifs <;> omega)) (StDC.nat (env := env) 1 (by omega))
    (rc_lt_eq_one _ _) (hb3 _)
  have grs : StDC P env (.var 1) (natList rs) 1 0 Z := StDC.var' rfl (by omega)
  have gcs : StDC P env (.var 2) (natList cs) 1 0 Z := StDC.var' rfl (by omega)
  have grs0 := StDC.get (vs := rs.map Val.nat) grs (StDC.nat 0 (by omega))
    (rc_natList_get hrs0) (by have := wt_nat_le (rs.getD 0 0)
                              have : rs.getD 0 0 ≤ M := by
                                rw [List.getD_eq_getElem _ _ hrs0]; exact hrsb _ (List.getElem_mem _)
                              omega)
  have gcs0 := StDC.get (vs := cs.map Val.nat) gcs (StDC.nat 0 (by omega))
    (rc_natList_get hcs0) (by have := wt_nat_le (cs.getD 0 0)
                              have : cs.getD 0 0 ≤ M := by
                                rw [List.getD_eq_getElem _ _ hcs0]; exact hcsb _ (List.getElem_mem _)
                              omega)
  have c5 := StDC.arith' (op := .eq) (StDC.call (StDC.mk2 grs0 grs (by
      have := wt_list2_le (.nat (rs.getD 0 0)) (natList rs); have := wt_nat_le (rs.getD 0 0)
      have : rs.getD 0 0 ≤ M := by
        rw [List.getD_eq_getElem _ _ hrs0]; exact hrsb _ (List.getElem_mem _)
      omega) (by omega)) hcntr (by
        have := wt_nat_le (rs.count (rs.getD 0 0)); have := List.count_le_length (a := rs.getD 0 0) (l := rs)
        omega)) gnW (st_eq_toNat _ _) (hb3 _)
  have c6 := StDC.arith' (op := .eq) (StDC.call (StDC.mk2 gcs0 gcs (by
      have := wt_list2_le (.nat (cs.getD 0 0)) (natList cs); have := wt_nat_le (cs.getD 0 0)
      have : cs.getD 0 0 ≤ M := by
        rw [List.getD_eq_getElem _ _ hcs0]; exact hcsb _ (List.getElem_mem _)
      omega) (by omega)) hcntc (by
        have := wt_nat_le (cs.count (cs.getD 0 0)); have := List.count_le_length (a := cs.getD 0 0) (l := cs)
        omega)) gnR (st_eq_toNat _ _) (hb3 _)
  have c7 := StDC.arith' (op := .eq) gvU gvL (st_eq_toNat _ _) (hb3 _)
  have c8 := StDC.arith' (op := .lt) gcs0 gnW (rc_lt_toNat' _ _) (hb3 _)
  have c9 : StDC P env (.var 3) (.nat (bm.all (rcTw bm)).toNat) 1 0 Z :=
    StDC.var' rfl (by have := wt_boolVal_le (bm.all (rcTw bm)); simp only [boolVal] at this ⊢; omega)
  have c10 := StDC.arith' (op := .lt) (StDC.arith' (op := .add) gnW gnR rfl (by simp only [BinOp.eval]; omega))
    (StDC.arith' (op := .add) gn (StDC.nat (env := env) 1 (by omega)) rfl (by simp only [BinOp.eval]; omega))
    (rc_lt_le _ _) (hb3 _)
  have c11 := StDC.arith' (op := .lt)
    (StDC.arith' (op := .mul) (StDC.nat (env := env) 16 (by omega))
      (StDC.arith' (op := .mul) gnW gnR rfl (by
        show wl.length * rl.length + 2 ≤ Z
        have : wl.length * rl.length ≤ M * M := Nat.mul_le_mul (by omega) (by omega)
        omega)) rfl (by
        show 16 * (wl.length * rl.length) + 2 ≤ Z
        have : wl.length * rl.length ≤ M * M := Nat.mul_le_mul (by omega) (by omega)
        omega))
    (StDC.arith' (op := .add) (StDC.arith' (op := .mul) (StDC.nat (env := env) 3 (by omega))
      (StDC.arith' (op := .mul) gn gn rfl (by
        show n * n + 2 ≤ Z
        have : n * n ≤ M * M := Nat.mul_le_mul hn hn
        omega)) rfl (by
        show 3 * (n * n) + 2 ≤ Z
        have : n * n ≤ M * M := Nat.mul_le_mul hn hn
        omega)) (StDC.nat (env := env) 1 (by omega)) rfl (by
        show 3 * (n * n) + 1 + 2 ≤ Z
        have : n * n ≤ M * M := Nat.mul_le_mul hn hn
        omega))
    (rc_lt_le _ _) (hb3 _)
  have hm01 : ∀ a b : Bool, BinOp.eval .mul a.toNat b.toNat = (a && b).toNat := by
    intro a b; simp only [BinOp.eval, rc_toNat_and]
  have p2 := StDC.arith' (op := .mul) c1 c2 (hm01 _ _) (hb3 _)
  have p3 := StDC.arith' (op := .mul) p2 c3 (hm01 _ _) (hb3 _)
  have p4 := StDC.arith' (op := .mul) p3 c4 (hm01 _ _) (hb3 _)
  have p5 := StDC.arith' (op := .mul) p4 c5 (hm01 _ _) (hb3 _)
  have p6 := StDC.arith' (op := .mul) p5 c6 (hm01 _ _) (hb3 _)
  have p7 := StDC.arith' (op := .mul) p6 c7 (hm01 _ _) (hb3 _)
  have p8 := StDC.arith' (op := .mul) p7 c8 (hm01 _ _) (hb3 _)
  have p9 := StDC.arith' (op := .mul) p8 c9 (hm01 _ _) (hb3 _)
  have p10 := StDC.arith' (op := .mul) p9 c10 (hm01 _ _) (hb3 _)
  have p11 := StDC.arith' (op := .mul) p10 c11 (hm01 _ _) (hb3 _)
  have hw : (Val.nat (rcCond n vL vR v0 vU wl rl bm).toNat).wt ≤ Z := by
    have := wt_boolVal_le (rcCond n vL vR v0 vU wl rl bm); simp only [boolVal] at this ⊢; omega
  have hbody := StDC.letE g1 (StDC.letE g2 (StDC.letE g3 p11 hw) hw) hw
  refine StDC.funDet hf (show StDC P [rcCondIn n vL vR v0 vU wl rl bm] (rcCondF mc mcd rng al cnt)
    (boolVal (rcCond n vL vR v0 vU wl rl bm)) _ _ Z from hbody) ?_
  have hr3 : 10000 * (rl.length + 1) ^ 3 ≤ 10000 * (M + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have hc3 : countK * (M + 1) ^ 3 = 100000 * (M + 1) ^ 3 := rfl
  have hZ4 : Z + 1 ≤ 201 * (M + 1) ^ 4 := by omega
  have hk : (100 : ℕ) * (Z + 1) ≤ 100 * (201 * (M + 1) ^ 4) := Nat.mul_le_mul_left _ hZ4
  norm_num only [Nat.add_zero, Nat.zero_add] at hk ⊢
  omega

end GI.Impl
