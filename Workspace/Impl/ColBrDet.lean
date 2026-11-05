module

public import Workspace.Impl.ColBr

@[expose] public section

/-!
# The value that the column branch computes

`colChild_det`: on `[sv, q, rows, σN, rl]`, the expression `colChildE b` computes the child value
`colChildVal`, at cost at most the cost of the orbit labels plus `colBrK (X + 1)^5`, where `X`
bounds the numbers and weights (`ColBrB`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms)

section Helpers

variable {P : Program}

/-- The keep test on an interval value. -/
theorem colKeep_det {f : ℕ} (hf : P.funs[f]? = some colKeepF) {n : ℕ} (c : Val) (lab : Fin n → ℕ)
    (r cap o : ℕ) :
    FunDet P f (.list [c, colIV lab r cap o]) (boolVal (colKeep (colIV lab r cap o)))
      (10 * (Val.list [c, colIV lab r cap o]).wt + 50) := by
  refine FunDet.intro hf ?_
  have d1 := Det.arg' (P := P) (rest := []) (j := 1) (v := colIV lab r cap o)
    (vs := [c, colIV lab r cap o]) rfl
  have d2 := colGet d1 (Det.nat 1) (v := .nat r) (vs := [encFun lab, .nat r, .nat cap, .nat o]) rfl
  have d3 := Det.arith' (op := .lt) (z := if 1 < r then 1 else 0) (Det.nat 1) d2 rfl
  have e : boolVal (colKeep (colIV lab r cap o)) = .nat (if 1 < r then 1 else 0) := by
    simp only [boolVal, colKeep, colIV]
    by_cases h : 2 ≤ r
    · simp [h, show 1 < r by omega]
    · simp [h, show ¬ 1 < r by omega]
  rw [e]
  refine d3.mono ?_
  have : (if 1 < r then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have w := colWt_nat_mono (show r ≤ r from le_refl _)
  have w1 : (Val.nat r).wt < (Val.list [encFun lab, .nat r, .nat cap, .nat o]).wt :=
    wt_le_wt_list (by simp)
  have w2 : (Val.list [encFun lab, .nat r, .nat cap, .nat o]).wt <
      (Val.list [c, colIV lab r cap o]).wt := wt_le_wt_list (by simp [colIV])
  have := wt_nat_le 1
  omega

/-- **Tabulating values** over `[0, …, k - 1]`. -/
theorem colTabV_det {b f k : ℕ} (hmap : P.HasAt b (mapFuns b f)) {c : Val} {F : Fin k → Val}
    {B X : ℕ} (hF : ∀ i : Fin k, FunDet P f (.list [c, .nat i]) (F i) B) (hcX : c.wt ≤ B)
    (hkX : k ≤ X) (hXB : (X + 1) ^ 2 ≤ B) :
    FunDet P b (.list [c, natList (List.range k)]) (.list ((List.finRange k).map F))
      (40 * mapK * (X + 1) ^ 2 * B) := by
  have hT := tabulate_spec hmap hF
  rw [natList_range_eq]
  refine hT.mono ?_
  have w1 : (Val.list ((List.finRange k).map F)).wt ≤ k * (2 * B + 1) + 4 := by
    have := wt_list_map_le' (List.finRange k) F (W := B) (fun i _ => (hF i).wt_lt.le)
    simpa using this
  have w2 := wt_list2_le c (encFun fun i : Fin k => (i : ℕ))
  have w3 : (encFun fun i : Fin k => (i : ℕ)).wt ≤ 4 * (k + 1) ^ 2 := wt_ids_le k
  have w4 : (k + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have e1 : k * B ≤ (X + 1) * B := Nat.mul_le_mul_right _ (by omega)
  have e2 : (X + 1) * B ≤ (X + 1) ^ 2 * B :=
    Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) _)
  generalize (Val.list [c, encFun fun i : Fin k => (i : ℕ)]).wt = a at *
  generalize (Val.list ((List.finRange k).map F)).wt = d at *
  generalize (encFun fun i : Fin k => (i : ℕ)).wt = g at *
  have hX1 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have e7 : k * (2 * B + 1) ≤ (X + 1) * (2 * B + 1) := Nat.mul_le_mul_right _ (by omega)
  have e9 : X + 1 ≤ (X + 1) * B := Nat.le_mul_of_pos_right _ (by
    have : 0 < (X + 1) ^ 2 := by positivity
    omega)
  have e10 : B ≤ (X + 1) * B := Nat.le_mul_of_pos_left _ (by omega)
  have hsum : a + d + 1 ≤ 32 * ((X + 1) * B) := by
    have : (X + 1) * (2 * B + 1) = 2 * ((X + 1) * B) + (X + 1) := by ring
    omega
  have e3 : mapK * (k + 1) * (a + d + 1) ≤ mapK * (X + 1) * (32 * ((X + 1) * B)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hsum
  have e4 : mapK * (X + 1) * (32 * ((X + 1) * B)) = 32 * mapK * (X + 1) ^ 2 * B := by ring
  have e5 : (X + 1) ^ 2 * B ≤ mapK * (X + 1) ^ 2 * B := by
    simp only [mapK]; nlinarith
  have e6 : 40 * mapK * (X + 1) ^ 2 * B = 32 * mapK * (X + 1) ^ 2 * B +
      8 * (mapK * (X + 1) ^ 2 * B) := by ring
  omega

end Helpers

/-! ### The values -/

section Vals

variable {n m len : ℕ}

/-- The argument of the column branch. -/
def colBrIn (sv : Val) (q : ℕ) (R : List (List ℕ)) (σN : List (Perm (Fin m))) (rl : Fin n → ℕ) :
    Val :=
  .list [sv, .nat q, .list (R.map natList), .list (σN.map encPerm), encFun rl]

/-- A state value with the given entries. -/
def colSV (n : ℕ) (gv : Val) (dv : Fin n → ℕ) (xv yv hv rv fv : Val) (hh N : ℕ) : Val :=
  .list [.nat n, gv, encFun dv, xv, yv, hv, rv, fv, .nat hh, .nat N]

/-- The interval values of the child hierarchy, before the filter: the lower pieces, the row
interval of level `J`, the upper pieces. -/
def colHierL (labs : ℕ → Fin n → ℕ) (caps origs : Fin len → ℕ) (r0 : Fin m → Fin n)
    (ol : Fin m → ℕ) (cf : Fin n → Fin m) (rl dv : Fin n → ℕ) (h0 : 0 < m) (q : ℕ)
    (J : Fin len) : List Val :=
  (List.finRange len).map (fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k) ++
    [colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)] ++
    (List.finRange len).map (fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k)

/-- **The child value.** -/
def colChildVal (gv : Val) (dv rl : Fin n → ℕ) (xv yv fv : Val) (hh N q : ℕ) (hier : List Val)
    (cols : Fin n → ℕ) : Val :=
  .list [.nat n, gv, encFun dv, xv, yv, .list (hier.filter colKeep),
    .list [.list [.nat q, encFun rl, .list [encFun cols]]], fv, .nat (hh - 1), .nat N]

end Vals

/-! ### The last part: levels, row interval and the child value -/

section Lev

variable {P : Program} {b fc : ℕ} {n m len X q hh N : ℕ} {gv xv yv rv fv : Val}
  {labs : ℕ → Fin n → ℕ} {rats caps origs : Fin len → ℕ} {r0 : Fin m → Fin n} {ol : Fin m → ℕ}
  {cf : Fin n → Fin m} {rl dv : Fin n → ℕ} {R : List (List ℕ)} {σN : List (Perm (Fin m))}

/-- The weight bound of the values in the environment. -/
def colU (X : ℕ) : ℕ := 10 ^ 12 * (X + 1) ^ 4

set_option maxHeartbeats 2000000 in
theorem colLev_det (hA : ColBrAt P b fc) (h0 : 0 < m)
    (hB : ColLevB (X := X) labs rats caps origs ol rl dv) (J : Fin len)
    {V2 V3 V4 V5 V6 V7 V8 V11 V12 V13 : Val}
    (e2 : V2 = encFun fun c => (r0 c : ℕ)) (e3 : V3 = .nat m) (e4 : V4 = encFun ol)
    (e5 : V5 = natList (List.range m)) (e6 : V6 = natList (List.range n))
    (e7 : V7 = encFun fun i => (cf i : ℕ)) (e8 : V8 = encFun fun i => ol (cf i))
    (e11 : V11 = natList (List.range len)) (e13 : V13 = .nat J)
    (hW : (colBrIn (colSV n gv dv xv yv (colHV (fun k : Fin len => labs k) rats caps origs) rv fv
      hh N) q R σN rl).wt ≤ X) (hqX : q ≤ X) (hhX : hh ≤ X)
    (hV : ∀ v ∈ [V2, V3, V4, V5, V6, V7, V8, encFun (colColsLab ol cf dv), V11, V12, V13],
      v.wt ≤ colU X) :
    Det P [colBrIn (colSV n gv dv xv yv (colHV (fun k : Fin len => labs k) rats caps origs) rv fv
        hh N) q R σN rl, .nat n, V2, V3, V4, V5, V6, V7, V8, encFun (colColsLab ol cf dv),
        colHV (fun k : Fin len => labs k) rats caps origs, V11, V12, V13] (colLevE b)
      (colChildVal gv dv rl xv yv fv hh N q (colHierL labs caps origs r0 ol cf rl dv h0 q J)
        (colColsLab ol cf dv))
      (10 ^ 30 * (X + 1) ^ 6) := by
  subst e2 e3 e4 e5 e6 e7 e8 e11 e13
  have hn := hB.n_le
  have h8 := hB.one_le
  have hlen := hB.len_le
  have hm := hB.m_le
  obtain ⟨p23, p34, p12⟩ := colPow_facts X
  have p45 : (X + 1) ^ 4 ≤ (X + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have p56 : (X + 1) ^ 5 ≤ (X + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hU : colU X = 10 ^ 12 * (X + 1) ^ 4 := rfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hV
  obtain ⟨w2, w3, w4, w5, w6, w7, w8, w9, w11, w12, w13⟩ := hV
  have whv := hB.hv_le
  generalize hAv : colBrIn (colSV n gv dv xv yv (colHV (fun k : Fin len => labs k) rats caps origs)
    rv fv hh N) q R σN rl = A at hW
  -- reading the argument
  have dArg : ∀ rest j v, [colSV n gv dv xv yv (colHV (fun k : Fin len => labs k) rats caps origs)
      rv fv hh N, .nat q, .list (R.map natList), .list (σN.map encPerm), encFun rl][j]? = some v →
      j ≤ 4 → Det P (A :: rest) (arg j) v (2 * X + 10) := fun rest j v h hj => by
    subst hAv; exact (Det.arg' h).mono (by unfold colBrIn at hW; omega)
  have dSv : ∀ rest j v, [.nat n, gv, encFun dv, xv, yv,
      colHV (fun k : Fin len => labs k) rats caps origs, rv, fv, .nat hh, .nat N][j]? = some v →
      j ≤ 9 → Det P (A :: rest) (colSvE j) v (5 * X + 40) := fun rest j v h hj =>
    (colGet (dArg rest 0 _ rfl (by omega)) (Det.nat j) h).mono (by omega)
  -- step 14: the context of the levels
  have s14 := Det.mkList (P := P) (env := [A, .nat n, encFun fun c => (r0 c : ℕ), .nat m,
      encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ),
      encFun fun i => ol (cf i), encFun (colColsLab ol cf dv),
      colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len),
      V12, .nat J]) (c := colU X + 5 * X + 40)
    [(.var 10, colHV (fun k : Fin len => labs k) rats caps origs),
      (.var 2, encFun fun c => (r0 c : ℕ)), (.var 4, encFun ol),
      (.var 8, encFun fun i => ol (cf i)), (.var 7, encFun fun i => (cf i : ℕ)),
      (arg 4, encFun rl), (colSvE 2, encFun dv), (.var 5, natList (List.range m)),
      (.var 3, .nat m), (.var 1, .nat n), (.var 6, natList (List.range n))] (by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    have wn := wt_nat_le n
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact colVar rfl (by dsimp only; omega)
    · exact colVar rfl (by dsimp only; omega)
    · exact colVar rfl (by dsimp only; omega)
    · exact colVar rfl (by dsimp only; omega)
    · exact colVar rfl (by dsimp only; omega)
    · exact (dArg _ 4 _ rfl (by omega)).mono (by omega)
    · exact (dSv _ 2 _ rfl (by omega)).mono (by omega)
    · exact colVar rfl (by dsimp only; omega)
    · exact colVar rfl (by dsimp only; omega)
    · exact colVar rfl (by dsimp only; omega)
    · exact colVar rfl (by dsimp only; omega))
  have wctx := hB.ctx_wt (r0 := r0) (cf := cf)
  have hLK : colLevK = 10 ^ 17 := rfl
  -- steps 15 and 16: the lower and the upper pieces
  have t15 := colTabV_det (P := P) hA.mLow (c := .list (colLevC labs rats caps origs r0 ol cf rl dv))
    (fun k => colLow_det (r0 := r0) (cf := cf) hA.low hA.mPick hA.pick hA.mEq hA.eq hA.mKey hA.key
      hA.cls h0 hB k) (by simp only [colLevK]; omega) hlen (by simp only [colLevK]; omega)
  have t16 := colTabV_det (P := P) hA.mUp (c := .list (colLevC labs rats caps origs r0 ol cf rl dv))
    (fun k => colUp_det (r0 := r0) (cf := cf) hA.up hA.mPick hA.pick hA.mEq hA.eq hA.mMin hA.min
      hA.iter hA.minStep hA.cls h0 hB k) (by simp only [colLevK]; omega) hlen (by simp only [colLevK]; omega)
  have s15 := colCall (colMk2 (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), V12, .nat J, .list (colLevC labs rats caps origs r0 ol cf rl dv)]) (i := 14) rfl (le_refl _))
    (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), V12, .nat J, .list (colLevC labs rats caps origs r0 ol cf rl dv)]) (i := 11) rfl (le_refl _))) t15
  have s16 := colCall (colMk2 (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), V12, .nat J, .list (colLevC labs rats caps origs r0 ol cf rl dv), .list ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k)]) (i := 14) rfl (le_refl _))
    (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), V12, .nat J, .list (colLevC labs rats caps origs r0 ol cf rl dv), .list ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k)]) (i := 11) rfl (le_refl _))) t16
  -- step 17: the row interval
  have dJ := colGet (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), V12, .nat J, .list (colLevC labs rats caps origs r0 ol cf rl dv), .list ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k), .list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k)]) (i := 10) rfl (le_refl _))
    (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), V12, .nat J, .list (colLevC labs rats caps origs r0 ol cf rl dv), .list ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k), .list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k)]) (i := 13) rfl (le_refl _))
    (colHV_get (fun k : Fin len => labs k) rats caps origs J)
  have dcap := colGet dJ (Det.nat 2) (v := .nat (caps J)) rfl
  have dq := dArg [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), V12, .nat J, .list (colLevC labs rats caps origs r0 ol cf rl dv), .list ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k), .list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k)] 1 (.nat q) rfl (by omega)
  have dcap' := Det.arith' (op := .sub) (z := min (caps J) q) dcap
    (Det.arith' (op := .sub) (z := caps J - q) dcap dq rfl)
    (by simp only [GI.Machine.BinOp.eval]; omega)
  have dorig := colGet dJ (Det.nat 3) (v := .nat (origs J)) rfl
  have s17 := colMk4 (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), V12, .nat J, .list (colLevC labs rats caps origs r0 ol cf rl dv), .list ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k), .list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k)]) (i := 9) rfl (le_refl _)) dq dcap' dorig
  -- the child value
  have wlow : (Val.list ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k)).wt ≤ 3 * colLevK * (X + 1) ^ 5 := by
    have := wt_list_map_le' (List.finRange len)
      (fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k) (W := colLevK * (X + 1) ^ 4)
      (fun k _ => (colLow_det (r0 := r0) (cf := cf) hA.low hA.mPick hA.pick hA.mEq hA.eq hA.mKey
        hA.key hA.cls h0 hB k).wt_lt.le)
    simp only [List.length_finRange] at this
    have e : (X + 1) * (3 * (colLevK * (X + 1) ^ 4)) = 3 * colLevK * (X + 1) ^ 5 := by ring
    have hK : X + 4 ≤ colLevK * (X + 1) ^ 4 := by simp only [colLevK]; nlinarith
    have h1 : len * (2 * (colLevK * (X + 1) ^ 4) + 1) ≤ X * (2 * (colLevK * (X + 1) ^ 4) + 1) :=
      Nat.mul_le_mul_right _ hlen
    rw [← e]
    generalize colLevK * (X + 1) ^ 4 = W at *
    nlinarith
  have wup : (Val.list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k)).wt ≤ 3 * colLevK * (X + 1) ^ 5 := by
    have := wt_list_map_le' (List.finRange len)
      (fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k) (W := colLevK * (X + 1) ^ 4)
      (fun k _ => (colUp_det (r0 := r0) (cf := cf) hA.up hA.mPick hA.pick hA.mEq hA.eq hA.mMin
        hA.min hA.iter hA.minStep hA.cls h0 hB k).wt_lt.le)
    simp only [List.length_finRange] at this
    have e : (X + 1) * (3 * (colLevK * (X + 1) ^ 4)) = 3 * colLevK * (X + 1) ^ 5 := by ring
    have hK : X + 4 ≤ colLevK * (X + 1) ^ 4 := by simp only [colLevK]; nlinarith
    have h1 : len * (2 * (colLevK * (X + 1) ^ 4) + 1) ≤ X * (2 * (colLevK * (X + 1) ^ 4) + 1) :=
      Nat.mul_le_mul_right _ hlen
    rw [← e]
    generalize colLevK * (X + 1) ^ 4 = W at *
    nlinarith
  have wrow := s17.wt_lt
  -- the weights of the hierarchy, before and after the filter
  have hH : (colHierL labs caps origs r0 ol cf rl dv h0 q J) = ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k) ++ [colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)] ++ ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k) := rfl
  have sL := sum_wt_lt_wt_list ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k)
  have sU := sum_wt_lt_wt_list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k)
  have lL : ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k).length = len := by simp
  have lU : ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k).length = len := by simp
  have sH : ((colHierL labs caps origs r0 ol cf rl dv h0 q J).map Val.wt).sum ≤ (((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k).map Val.wt).sum + (colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)).wt + (((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k).map Val.wt).sum := by
    rw [hH]; simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]; omega
  have lH : (colHierL labs caps origs r0 ol cf rl dv h0 q J).length = 2 * len + 1 := by
    rw [hH]
    simp only [List.length_append, lL, lU, List.length_cons, List.length_nil]
    omega
  have wH := wt_list_le (colHierL labs caps origs r0 ol cf rl dv h0 q J)
  have sF : (((colHierL labs caps origs r0 ol cf rl dv h0 q J).filter colKeep).map Val.wt).sum ≤ ((colHierL labs caps origs r0 ol cf rl dv h0 q J).map Val.wt).sum :=
    ((List.filter_sublist (p := colKeep)).map _).sum_le_sum (fun _ _ => Nat.zero_le _)
  have lF : ((colHierL labs caps origs r0 ol cf rl dv h0 q J).filter colKeep).length ≤ (colHierL labs caps origs r0 ol cf rl dv h0 q J).length := List.length_filter_le _ _
  have wF := wt_list_le ((colHierL labs caps origs r0 ol cf rl dv h0 q J).filter colKeep)
  have hcapJ : caps J ≤ X := hB.caps_le J
  have wq := wt_nat_le q
  have hrowZ : (colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)).wt ≤ 10 ^ 14 * (X + 1) ^ 4 := by
    have := wt_nat_le (min (caps J) q)
    have := wt_nat_le (caps J - q)
    have := wt_nat_le (caps J)
    have := wt_nat_le (origs J)
    have := min_le_left (caps J) q
    have : (Val.nat (origs J)).wt ≤ X := by
      have h1 : (Val.nat (origs J)).wt < (Val.list [encFun (labs J), .nat (rats J), .nat (caps J),
          .nat (origs J)]).wt := wt_le_wt_list (by simp)
      have h2 : (Val.list [encFun (labs J), .nat (rats J), .nat (caps J), .nat (origs J)]).wt <
          (colHV (fun k : Fin len => labs k) rats caps origs).wt := by
        unfold colHV
        exact wt_le_wt_list (List.mem_map.2 ⟨J, List.mem_finRange J, rfl⟩)
      omega
    have : (colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)).wt = (Val.list [encFun (colColsLab ol cf dv), .nat q, .nat (min (caps J) q),
      .nat (origs J)]).wt := rfl
    generalize min (caps J) q = u at *
    omega
  have hZ1 : (X + 1) ^ 4 ≤ (X + 1) ^ 5 := p45
  have wHZ : (Val.list (colHierL labs caps origs r0 ol cf rl dv h0 q J)).wt ≤ (10 ^ 20 * (X + 1) ^ 5) := by
    simp only [colLevK] at wlow wup
    omega
  have wFZ : (Val.list ((colHierL labs caps origs r0 ol cf rl dv h0 q J).filter colKeep)).wt ≤ (10 ^ 20 * (X + 1) ^ 5) := by
    simp only [colLevK] at wlow wup
    omega
  have wLR : (Val.list (((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k) ++ [colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)])).wt ≤ (10 ^ 20 * (X + 1) ^ 5) := by
    have := wt_list_le (((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k) ++ [colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)])
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.length_append, lL, List.length_cons, List.length_nil] at this
    simp only [colLevK] at wlow wup
    omega
  -- append, then filter
  have appF : FunDet P (b + 45) (.list [.list (((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k) ++ [colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)]), .list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k)]) (.list (colHierL labs caps origs r0 ol cf rl dv h0 q J))
      (10 ^ 4 * (X + 1) * (5 * (10 ^ 20 * (X + 1) ^ 5))) := by
    refine (append_spec hA.app (((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k) ++ [colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)]) ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k)).mono fun w c hw => ⟨hw.1, ?_⟩
    obtain ⟨rfl, hc⟩ := hw
    have := wt_list2_le (.list (((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k) ++ [colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)])) (.list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k))
    simp only [colLevK] at wlow wup
    have h1 : loopModK * (((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k).length + 1) * ((Val.list [.list (((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k) ++ [colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)]), .list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k)]).wt +
        ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k).length + (Val.list (((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k) ++ [colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)] ++ ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k))).wt + 1) ≤ 10 ^ 4 * (X + 1) * (5 * (10 ^ 20 * (X + 1) ^ 5)) := by
      rw [lU]
      apply Nat.mul_le_mul (by simp only [loopModK]; omega)
      have : (Val.list (((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k) ++ [colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)] ++ ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k))).wt = (Val.list (colHierL labs caps origs r0 ol cf rl dv h0 q J)).wt := rfl
      omega
    omega
  have hKeep : ∀ x ∈ (colHierL labs caps origs r0 ol cf rl dv h0 q J), FunDet P (b + 11) (.list [.nat 0, x]) (boolVal (colKeep x))
      (40 * (10 ^ 20 * (X + 1) ^ 5) + 200) := by
    intro x hx
    have hxw : x.wt < (Val.list (colHierL labs caps origs r0 ol cf rl dv h0 q J)).wt := wt_le_wt_list hx
    rw [hH] at hx
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hx
    have hw2 := wt_list2_le (.nat 0) x
    have := wt_nat_le 0
    rcases hx with (⟨k, -, rfl⟩ | rfl) | ⟨k, -, rfl⟩
    · exact (colKeep_det hA.keep (.nat 0) _ _ _ _).mono (by unfold colLowVal at hxw hw2; omega)
    · exact (colKeep_det hA.keep (.nat 0) _ _ _ _).mono (by omega)
    · exact (colKeep_det hA.keep (.nat 0) _ _ _ _).mono (by unfold colUpVal at hxw hw2; omega)
  have filtF : FunDet P (b + 42) (.list [.nat 0, .list (colHierL labs caps origs r0 ol cf rl dv h0 q J)]) (.list ((colHierL labs caps origs r0 ol cf rl dv h0 q J).filter colKeep))
      (10 ^ 4 * (X + 1) * (50 * (10 ^ 20 * (X + 1) ^ 5) + 300)) := by
    refine (filter_spec hA.filt (B := fun _ => 40 * (10 ^ 20 * (X + 1) ^ 5) + 200) hKeep).mono fun w c hw => ⟨hw.1, ?_⟩
    obtain ⟨rfl, hc⟩ := hw
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, lH] at hc
    have := wt_list2_le (.nat 0) (.list (colHierL labs caps origs r0 ol cf rl dv h0 q J))
    have := wt_nat_le 0
    have h1 : (2 * len + 1) * (40 * (10 ^ 20 * (X + 1) ^ 5) + 200) ≤ 3 * (X + 1) * (40 * (10 ^ 20 * (X + 1) ^ 5) + 200) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : loopModK * (2 * len + 1 + 1) * ((Val.list [.nat 0, .list (colHierL labs caps origs r0 ol cf rl dv h0 q J)]).wt + (2 * len + 1) +
        (Val.list ((colHierL labs caps origs r0 ol cf rl dv h0 q J).filter colKeep)).wt + 1) ≤ 3000 * (X + 1) * (5 * (10 ^ 20 * (X + 1) ^ 5) + 50) :=
      Nat.mul_le_mul (by simp only [loopModK]; omega) (by omega)
    have h3 : 3 * (X + 1) * (40 * (10 ^ 20 * (X + 1) ^ 5) + 200) + 3000 * (X + 1) * (5 * (10 ^ 20 * (X + 1) ^ 5) + 50) ≤
        10 ^ 4 * (X + 1) * (50 * (10 ^ 20 * (X + 1) ^ 5) + 300) := by nlinarith
    omega
  -- the pieces of the child value
  have dsn := Det.snoc (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), V12, .nat J, .list (colLevC labs rats caps origs r0 ol cf rl dv), .list ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k), .list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k), colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)]) (i := 15) rfl (le_refl _))
    (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), V12, .nat J, .list (colLevC labs rats caps origs r0 ol cf rl dv), .list ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k), .list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k), colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)]) (i := 17) rfl (le_refl _))
  have dap := colCall (colMk2 dsn (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), V12, .nat J, .list (colLevC labs rats caps origs r0 ol cf rl dv), .list ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k), .list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k), colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)]) (i := 16) rfl (le_refl _))) appF
  have dfil := colCall (colMk2 (Det.nat 0) dap) filtF
  have drow := Det.mk1 (colMk3 (dArg [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), V12, .nat J, .list (colLevC labs rats caps origs r0 ol cf rl dv), .list ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k), .list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k), colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)] 1 (.nat q) rfl (by omega))
    (dArg [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), V12, .nat J, .list (colLevC labs rats caps origs r0 ol cf rl dv), .list ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k), .list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k), colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)] 4 (encFun rl) rfl (by omega))
    (Det.mk1 (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), V12, .nat J, .list (colLevC labs rats caps origs r0 ol cf rl dv), .list ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k), .list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k), colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)]) (i := 9) rfl (le_refl _))))
  have dsub := Det.arith' (op := .sub) (z := hh - 1) (dSv [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), V12, .nat J, .list (colLevC labs rats caps origs r0 ol cf rl dv), .list ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k), .list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k), colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)] 8 (.nat hh) rfl (by omega))
    (Det.nat 1) rfl
  have hp45 : (X + 1) ^ 5 * (X + 1) = (X + 1) ^ 6 := by ring
  have hXZ : (X + 1) * (10 ^ 20 * (X + 1) ^ 5) = 10 ^ 20 * (X + 1) ^ 6 := by rw [← hp45]; ring
  have wq := wt_nat_le q
  have wrl : (encFun rl).wt ≤ X := by
    subst hAv
    have : (encFun rl).wt < (colBrIn (colSV n gv dv xv yv
      (colHV (fun k : Fin len => labs k) rats caps origs) rv fv hh N) q R σN rl).wt :=
      wt_le_wt_list (by simp [colBrIn])
    omega
  have wsn := dsn.wt_lt
  have eA : 10 ^ 4 * (X + 1) * (5 * (10 ^ 20 * (X + 1) ^ 5)) = 5 * 10 ^ 24 * (X + 1) ^ 6 := by ring
  have eF : 10 ^ 4 * (X + 1) * (50 * (10 ^ 20 * (X + 1) ^ 5) + 300) = 5 * 10 ^ 25 * (X + 1) ^ 6 + 3 * 10 ^ 6 * (X + 1) :=
    by ring
  have p16 : X + 1 ≤ (X + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  rw [eA] at appF dap
  rw [eF] at filtF dfil
  simp only [colLevK] at wlow wup
  have body := Det.mkList (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), V12, .nat J, .list (colLevC labs rats caps origs r0 ol cf rl dv), .list ((List.finRange len).map fun k => colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k), .list ((List.finRange len).map fun k => colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k), colIV (colColsLab ol cf dv) q (min (caps J) q) (origs J)]) (c := (10 ^ 27 * (X + 1) ^ 6))
    [(colSvE 0, .nat n), (colSvE 1, gv), (colSvE 2, encFun dv), (colSvE 3, xv), (colSvE 4, yv),
      (.call (b + 42) (mk2 (.nat 0) (.call (b + 45) (mk2 (.snoc (.var 15) (.var 17)) (.var 16)))),
        .list ((colHierL labs caps origs r0 ol cf rl dv h0 q J).filter colKeep)),
      (mk1 (mk3 (arg 1) (arg 4) (mk1 (.var 9))),
        .list [.list [.nat q, encFun rl, .list [encFun (colColsLab ol cf dv)]]]),
      (colSvE 7, fv), (.arith .sub (colSvE 8) (.nat 1), .nat (hh - 1)), (colSvE 9, .nat N)] (by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (dSv _ 0 _ rfl (by omega)).mono (by omega)
    · exact (dSv _ 1 _ rfl (by omega)).mono (by omega)
    · exact (dSv _ 2 _ rfl (by omega)).mono (by omega)
    · exact (dSv _ 3 _ rfl (by omega)).mono (by omega)
    · exact (dSv _ 4 _ rfl (by omega)).mono (by omega)
    · refine dfil.mono ?_
      have := wt_nat_le 0
      omega
    · refine drow.mono ?_
      have a1 := wt_list_le [encFun (colColsLab ol cf dv)]
      have a2 := wt_list_le [.nat q, encFun rl, .list [encFun (colColsLab ol cf dv)]]
      have a3 := wt_list_le [.list [.nat q, encFun rl, .list [encFun (colColsLab ol cf dv)]]]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil] at a1 a2 a3
      omega
    · exact (dSv _ 7 _ rfl (by omega)).mono (by omega)
    · refine dsub.mono ?_
      omega
    · exact (dSv _ 9 _ rfl (by omega)).mono (by omega))
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, Nat.reduceAdd]
    at s14 body
  simp only [colLevC, colLevCtx] at wctx
  have d := colLet s14 (colLet s15 (colLet s16 (colLet s17 body)))
  subst hAv
  refine d.mono ?_
  have := s14.wt_lt
  have := s15.wt_lt
  have := s16.wt_lt
  have hsv : ∀ v ∈ [.nat n, gv, encFun dv, xv, yv,
      colHV (fun k : Fin len => labs k) rats caps origs, rv, fv, .nat hh, .nat N], v.wt ≤ X := by
    intro v hv
    have h1 : v.wt < (colSV n gv dv xv yv (colHV (fun k : Fin len => labs k) rats caps origs) rv fv
        hh N).wt := wt_le_wt_list hv
    have h2 : (colSV n gv dv xv yv (colHV (fun k : Fin len => labs k) rats caps origs) rv fv
        hh N).wt < (colBrIn (colSV n gv dv xv yv
        (colHV (fun k : Fin len => labs k) rats caps origs) rv fv hh N) q R σN rl).wt :=
      wt_le_wt_list (by simp [colBrIn])
    omega
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hsv
  obtain ⟨-, wg, wdv, wx, wy, -, -, wf, -, wN⟩ := hsv
  have wsub := wt_nat_le (hh - 1)
  have wn := wt_nat_le n
  have a1 := wt_list_le [encFun (colColsLab ol cf dv)]
  have a2 := wt_list_le [.nat q, encFun rl, .list [encFun (colColsLab ol cf dv)]]
  have a3 := wt_list_le [.list [.nat q, encFun rl, .list [encFun (colColsLab ol cf dv)]]]
  have a4 := wt_list_le [.nat n, gv, encFun dv, xv, yv, .list ((colHierL labs caps origs r0 ol cf rl dv h0 q J).filter colKeep),
    .list [.list [.nat q, encFun rl, .list [encFun (colColsLab ol cf dv)]]], fv, .nat (hh - 1),
    .nat N]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at a1 a2 a3 a4
  have e15 : 40 * mapK * (X + 1) ^ 2 * (colLevK * (X + 1) ^ 4) = 4 * 10 ^ 21 * (X + 1) ^ 6 := by
    simp only [mapK, colLevK]; ring
  rw [e15] at s15 s16 ⊢
  have wctx2 := hB.ctx_wt (r0 := r0) (cf := cf)
  omega


end Lev

/-! ### The whole child value -/

section Child

variable {P : Program} {b fc : ℕ} {n m len X q hh N Co : ℕ} {gv xv yv rv fv : Val}
  {labs : ℕ → Fin n → ℕ} {rats caps origs : Fin len → ℕ} {r0 : Fin m → Fin n} {ol : Fin m → ℕ}
  {cf : Fin n → Fin m} {rl dv : Fin n → ℕ} {R : List (List ℕ)} {σN : List (Perm (Fin m))}

set_option maxHeartbeats 4000000 in
/-- **The child value of the column branch.** -/
theorem colChild_det (hA : ColBrAt P b fc) (h0 : 0 < m)
    (hB : ColLevB (X := X) labs rats caps origs ol rl dv) (J : Fin len)
    (hJ : ((List.finRange len).map (colNotLowv (fun k : Fin len => labs k) dv rl (r0 ⟨0, h0⟩))).findIdx
      (fun x => decide (x = 1)) = J)
    (hol : FunDet P (b + 79) (encPerms σN) (encFun ol) Co)
    (hR0 : R[0]? = some ((List.finRange m).map fun c => (r0 c : ℕ)))
    (hRB : ∀ r ∈ R, (∀ x ∈ r, x ≤ X) ∧ r.length ≤ X) (hrl : ∀ i, dv i ≠ 0 → rl i < R.length)
    (hcf : ∀ i, (cf i : ℕ) = colInvv R dv rl i)
    (hW : (colBrIn (colSV n gv dv xv yv (colHV (fun k : Fin len => labs k) rats caps origs) rv fv
      hh N) q R σN rl).wt ≤ X) (hqX : q ≤ X) (hhX : hh ≤ X) :
    Det P [colBrIn (colSV n gv dv xv yv (colHV (fun k : Fin len => labs k) rats caps origs) rv fv
        hh N) q R σN rl] (colChildE b)
      (colChildVal gv dv rl xv yv fv hh N q (colHierL labs caps origs r0 ol cf rl dv h0 q J)
        (colColsLab ol cf dv))
      (16 * Co + 10 ^ 34 * (X + 1) ^ 6) := by
  have hn := hB.n_le
  have h8 := hB.one_le
  have h2n := hB.two_n
  have hlen := hB.len_le
  have hm := hB.m_le
  obtain ⟨p23, p34, p12⟩ := colPow_facts X
  have whv := hB.hv_le
  have hAin : ∀ v ∈ [colSV n gv dv xv yv (colHV (fun k : Fin len => labs k) rats caps origs) rv fv
      hh N, .nat q, .list (R.map natList), .list (σN.map encPerm), encFun rl], v.wt ≤ X :=
    fun v hv => ((wt_le_wt_list hv).trans_le hW).le
  have hSin : ∀ v ∈ [.nat n, gv, encFun dv, xv, yv,
      colHV (fun k : Fin len => labs k) rats caps origs, rv, fv, .nat hh, .nat N], v.wt ≤ X :=
    fun v hv => ((wt_le_wt_list hv).trans_le (hAin _ (by simp [colSV]))).le
  have wrows := hAin (.list (R.map natList)) (by simp)
  have wrl := hAin (encFun rl) (by simp)
  have wdv := hSin (encFun dv) (by simp)
  generalize hAv : colBrIn (colSV n gv dv xv yv (colHV (fun k : Fin len => labs k) rats caps origs)
    rv fv hh N) q R σN rl = A at hW
  have dArg : ∀ rest j v, [colSV n gv dv xv yv (colHV (fun k : Fin len => labs k) rats caps origs)
      rv fv hh N, .nat q, .list (R.map natList), .list (σN.map encPerm), encFun rl][j]? = some v →
      j ≤ 4 → Det P (A :: rest) (arg j) v (2 * X + 10) := fun rest j v h hj => by
    subst hAv; exact (Det.arg' h).mono (by unfold colBrIn at hW; omega)
  have dSv : ∀ rest j v, [.nat n, gv, encFun dv, xv, yv,
      colHV (fun k : Fin len => labs k) rats caps origs, rv, fv, .nat hh, .nat N][j]? = some v →
      j ≤ 9 → Det P (A :: rest) (colSvE j) v (5 * X + 40) := fun rest j v h hj =>
    (colGet (dArg rest 0 _ rfl (by omega)) (Det.nat j) h).mono (by omega)
  -- steps 1 to 3: `n`, row `0`, `m`
  have s1 := dSv [] 0 (.nat n) rfl (by omega)
  have hR0' : (R.map natList)[0]? = some (encFun fun c => (r0 c : ℕ)) := by
    rw [List.getElem?_map, hR0, encFun_eq_natList]; rfl
  have s2 := colGet (dArg [.nat n] 2 _ rfl (by omega)) (Det.nat 0) hR0'
  have s3 := colLength (vs := (List.finRange m).map fun c => Val.nat (r0 c : ℕ)) (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ)]) (i := 2) rfl (le_refl _))
  have e3 : ((List.finRange m).map fun c => Val.nat (r0 c : ℕ)).length = m := by simp
  rw [e3] at s3
  -- step 4: the orbit labels
  have s4 := colCall (colMk2 (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m]) (i := 3) rfl (le_refl _)) (dArg [.nat n, encFun fun c => (r0 c : ℕ), .nat m] 3 _ rfl (by omega))) hol
  -- steps 5 and 6: `range m`, `range n`
  have s5 := colCall (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol]) (i := 3) rfl (le_refl _)) (GI.Impl.range_det hA.rng m)
  have s6 := colCall (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m)]) (i := 1) rfl (le_refl _)) (GI.Impl.range_det hA.rng n)
  -- step 7: the column coordinate of each position
  have hcfX : ∀ i, colInvv R dv rl i ≤ X := fun i => by
    rw [← hcf i]; have := (cf i).2; omega
  have wc7 := wt_list3_le (encFun dv) (encFun rl) (.list (R.map natList))
  have t7 := tab_det hA.mInv (F := colInvv R dv rl) (B := 10 ^ 6 * (X + 1) ^ 3)
    (fun i => (colInv_det hA.inv hA.fEq R dv rl hRB hn hrl i).mono (by
      have := wt_list2_le (.list [encFun dv, encFun rl, .list (R.map natList)]) (.nat i)
      have := wt_nat_le i
      have := i.2
      simp only [findEqK]
      omega)) hcfX (by omega) hn
  have ecf : encFun (colInvv R dv rl) = encFun fun i => (cf i : ℕ) := by
    congr 1; funext i; exact (hcf i).symm
  rw [ecf] at t7
  have s7 := colCall (colMk2 (colMk3 (dSv [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n)] 2 _ rfl (by omega)) (dArg [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n)] 4 _ rfl (by omega))
    (dArg [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n)] 2 _ rfl (by omega))) (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n)]) (i := 6) rfl (le_refl _))) t7
  -- step 8: the orbit label of the column of each position
  have hol : ∀ c, ol c ≤ X := fun c => by have := hB.ol_le c; omega
  have t8 := colTabPick_det hA.mPick hA.pick ol cf 0 (X := X) (fun j => by have := hol j; omega)
    (by omega) (by omega) hn
  have s8 := colCall (colMk2 (colMk3 (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ)]) (i := 4) rfl (le_refl _)) (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ)]) (i := 7) rfl (le_refl _)) (Det.nat 0)) (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ)]) (i := 6) rfl (le_refl _))) t8
  have e8 : (encFun fun i => ol (cf i) + 0) = encFun fun i => ol (cf i) := rfl
  rw [e8] at s8
  -- step 9: the column labels
  have t9 := colTabPick_det hA.mPick hA.pick ol cf (n + 1) (X := X)
    (fun j => by have := hB.ol_le j; omega) (by omega) (by omega) hn
  have s9 := colLabs_det hA.cls (fun i => ol (cf i) + (n + 1)) dv
    (colMk2 (colCall (colMk2 (colMk3 (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i)]) (i := 4) rfl (le_refl _)) (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i)]) (i := 7) rfl (le_refl _))
      (Det.arith' (op := .add) (z := n + 1) (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i)]) (i := 1) rfl (le_refl _)) (Det.nat 1) rfl)) (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i)]) (i := 6) rfl (le_refl _))) t9)
      (dSv [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i)] 2 _ rfl (by omega)))
    (fun i => by show ol (cf i) + (n + 1) ≤ X; have := hB.ol_le (cf i); omega) hB.dv_le hn
  -- step 10: the stored hierarchy; step 11: `range len`
  have s10 := dSv [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv)] 5 _ rfl (by omega)
  have s11 := colCall (colLength (vs := (List.finRange len).map fun k : Fin len =>
      Val.list [encFun (labs k), .nat (rats k), .nat (caps k), .nat (origs k)]) (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs]) (i := 10) rfl (le_refl _)))
    (GI.Impl.range_det hA.rng ((List.finRange len).map fun k : Fin len =>
      Val.list [encFun (labs k), .nat (rats k), .nat (caps k), .nat (origs k)]).length)
  have e11 : ((List.finRange len).map fun k : Fin len =>
      Val.list [encFun (labs k), .nat (rats k), .nat (caps k), .nat (origs k)]).length = len := by
    simp
  rw [e11] at s11
  -- step 12: which levels do not refine the rows
  have hp00 : ((List.finRange m).map fun c => Val.nat (r0 c : ℕ))[0]? = some (.nat (r0 ⟨0, h0⟩)) := by
    simp [List.getElem?_map, h0]
  have d12 := Det.snoc (colMk4 (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len)]) (i := 10) rfl (le_refl _)) (dSv [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len)] 2 _ rfl (by omega))
    (dArg [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len)] 4 _ rfl (by omega))
    (colGet (vs := (List.finRange m).map fun c => Val.nat (r0 c : ℕ)) (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len)]) (i := 2) rfl (le_refl _)) (Det.nat 0) hp00))
    (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len)]) (i := 6) rfl (le_refl _))
  have hc12 : (Val.list [colHV (fun k : Fin len => labs k) rats caps origs, encFun dv, encFun rl,
      .nat (r0 ⟨0, h0⟩), natList (List.range n)]).wt ≤ 100 * (X + 1) ^ 2 := by
    have := wt_list_le [colHV (fun k : Fin len => labs k) rats caps origs, encFun dv, encFun rl,
      .nat (r0 ⟨0, h0⟩), natList (List.range n)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    have := wt_range_le n
    have := wt_nat_le (r0 ⟨0, h0⟩ : ℕ)
    have := (r0 ⟨0, h0⟩).2
    have : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have t12 := tab_det hA.mNot (F := (colNotLowv (fun k : Fin len => labs k) dv rl (r0 ⟨0, h0⟩))) (B := 10 ^ 9 * (X + 1) ^ 3)
    (fun k => (colNotLow_det hA.notLow hA.all hA.lowPos (fun k : Fin len => labs k) rats caps origs
      dv rl hB.dv_le (r0 ⟨0, h0⟩) k).mono (by
        have := wt_list2_le (.list [colHV (fun k : Fin len => labs k) rats caps origs, encFun dv,
          encFun rl, .nat (r0 ⟨0, h0⟩), natList (List.range n)]) (.nat k)
        have := wt_nat_le k
        have := k.2
        have h1 : colNotLowK * (n + 1) * ((Val.list [.list [colHV (fun k : Fin len => labs k) rats
            caps origs, encFun dv, encFun rl, .nat (r0 ⟨0, h0⟩), natList (List.range n)], .nat k]).wt
            + n + 1) ≤ colNotLowK * (X + 1) * (300 * (X + 1) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
        have h2 : colNotLowK * (X + 1) * (300 * (X + 1) ^ 2) = 3 * 10 ^ 8 * (X + 1) ^ 3 := by
          simp only [colNotLowK]; ring
        omega))
    (fun k => by unfold colNotLowv; split_ifs <;> omega) (by omega) hlen
  have s12 := colCall (colMk2 d12 (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len)]) (i := 11) rfl (le_refl _))) t12
  -- step 13: the first level that does not refine the rows
  have hNL : ∀ k, (colNotLowv (fun k : Fin len => labs k) dv rl (r0 ⟨0, h0⟩)) k ≤ 1 := fun k => by unfold colNotLowv; split_ifs <;> omega
  have t13 := findEq_spec hA.fEq (xs := (List.finRange len).map (colNotLowv (fun k : Fin len => labs k) dv rl (r0 ⟨0, h0⟩))) (j := 1) (B := X)
    (fun x hx => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      have := hNL k; omega) (by omega) (by simp; omega)
  rw [← encFun_eq_natList, hJ] at t13
  have s13 := colCall (colMk2 (Det.nat 1) (colVar (P := P) (env := A :: [.nat n, encFun fun c => (r0 c : ℕ), .nat m, encFun ol, natList (List.range m), natList (List.range n), encFun fun i => (cf i : ℕ), encFun fun i => ol (cf i), encFun (colColsLab ol cf dv), colHV (fun k : Fin len => labs k) rats caps origs, natList (List.range len), encFun (colNotLowv (fun k : Fin len => labs k) dv rl (r0 ⟨0, h0⟩))]) (i := 12) rfl (le_refl _))) t13
  -- the rest
  have wV12 : (encFun (colNotLowv (fun k : Fin len => labs k) dv rl (r0 ⟨0, h0⟩))).wt ≤ 5 * (X + 1) ^ 2 := wt_encFun_le' _ (fun k => by have := hNL k; omega) hlen
  have w9 := s9.wt_lt
  have ecol : (encFun (colColsLab ol cf dv)).wt =
      (encFun (Cls.repOf (Cls.keyOf (fun i => ol (cf i) + (n + 1)) dv))).wt := rfl
  have hU : colU X = 10 ^ 12 * (X + 1) ^ 4 := rfl
  have wcol : (encFun (colColsLab ol cf dv)).wt ≤ 5 * (X + 1) ^ 2 :=
    wt_encFun_le' _ (fun i => by
      have := Cls.repOf_lt (Cls.keyOf (fun i => ol (cf i) + (n + 1)) dv) i
      unfold colColsLab; omega) hn
  have wr0 := colWt_fin_le r0 (p := n) (show n ≤ X by omega) (show m ≤ X by omega)
  have wol := wt_encFun_le' ol (B := X) hol (by omega)
  have wcf := colWt_fin_le cf (p := m) (show m ≤ X by omega) hn
  have woc := wt_encFun_le' (fun i => ol (cf i)) (B := X) (fun i => hol (cf i)) hn
  have wrm := wt_range_le m
  have wrn := wt_range_le n
  have wrlen := wt_range_le len
  have e8' : (m + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have e9' : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have e10' : (len + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have wJ := wt_nat_le (J : ℕ)
  have wm := wt_nat_le m
  have wn := wt_nat_le n
  have hJl := J.2
  have dL := colLev_det (P := P) (b := b) (gv := gv) (xv := xv) (yv := yv) (rv := rv) (fv := fv)
    (R := R) (σN := σN) (q := q) (hh := hh) (N := N) (r0 := r0) (cf := cf) (ol := ol) (rl := rl)
    (dv := dv) (labs := labs) hA h0 hB J
    (V12 := encFun (colNotLowv (fun k : Fin len => labs k) dv rl (r0 ⟨0, h0⟩))) rfl rfl rfl rfl rfl rfl rfl rfl rfl (by subst hAv; exact hW) hqX hhX
    (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
  subst hAv
  have d := colLet s1 (colLet s2 (colLet s3 (colLet s4 (colLet s5 (colLet s6 (colLet s7 (colLet s8
    (colLet s9 (colLet s10 (colLet s11 (colLet s12 (colLet s13 dL))))))))))))
  refine d.mono ?_
  have := s2.wt_lt
  have := s4.wt_lt
  have := s7.wt_lt
  have := s8.wt_lt
  have := s12.wt_lt
  have := s13.wt_lt
  have p46 : (X + 1) ^ 4 ≤ (X + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have e7 : n * (10 ^ 6 * (X + 1) ^ 3) ≤ 10 ^ 6 * (X + 1) ^ 4 := mul_le_pow_succ _ 3 (by omega)
  have e12 : len * (10 ^ 9 * (X + 1) ^ 3) ≤ 10 ^ 9 * (X + 1) ^ 4 := mul_le_pow_succ _ 3 (by omega)
  have := wt_nat_le (J : ℕ)
  have : findEqK * (X + 1) ^ 3 = 100000 * (X + 1) ^ 3 := rfl
  have : (m + 1) ^ 3 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have : (n + 1) ^ 3 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have : (len + 1) ^ 3 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have : (Val.list ([colHV (fun k : Fin len => labs k) rats caps origs, encFun dv, encFun rl,
      .nat (r0 ⟨0, h0⟩ : ℕ)] ++ [natList (List.range n)])).wt =
    (Val.list [colHV (fun k : Fin len => labs k) rats caps origs, encFun dv, encFun rl,
      .nat (r0 ⟨0, h0⟩ : ℕ), natList (List.range n)]).wt := rfl
  omega

end Child

end GI.Impl
