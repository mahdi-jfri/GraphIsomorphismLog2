module

public import Workspace.Impl.HNFBar

@[expose] public section

/-!
# The sum of the absolute values of the entries, as a program

`T = 1 + Σ |A i j|` bounds every entry of `A`; it fixes the multiplier `K` of
`GI.Proved.hnfRect_spec`. The sum is a natural number, computed by two folds that decode each
entry (`linIntDecode`, which gives `[z⁺, z⁻]` with `|z| = z⁺ + z⁻`).
-/

namespace GI.Impl

variable {r c : ℕ}

open GI.Cited GI.Lang
open GI.Machine (BinOp len len_le_iff)

/-- The decoder of the integer library at `ints`. -/
structure hnfDecAt (P : Program) (ints : ℕ) : Prop where
  dec : P.funs[ints + 2]? = some (linIntDecodeF ints)
  bits : P.funs[ints]? = some (linBitsDecodeF ints)

theorem hnfDecAt_of {P : Program} {ints : ℕ} (h : P.HasAt ints (linIntFuns ints)) :
    hnfDecAt P ints where
  dec := by simpa [linIntFuns] using h 2 (by simp [linIntFuns])
  bits := by simpa [linIntFuns] using h 0 (by simp [linIntFuns])

/-- The partial sum of `|x j|` over `j < i`. -/
def hnfAbsSum {n : ℕ} (x : Fin n → ℤ) (i : ℕ) : ℕ :=
  (((List.finRange n).take i).map fun j => (x j).natAbs).sum

theorem hnfAbsSum_succ {n : ℕ} (x : Fin n → ℤ) (i : ℕ) (hi : i < n) :
    hnfAbsSum x (i + 1) = hnfAbsSum x i + (x ⟨i, hi⟩).natAbs := by
  unfold hnfAbsSum
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hi)]
  simp

theorem hnfAbsSum_le {n : ℕ} (x : Fin n → ℤ) (i : ℕ) {B : ℕ} (hB : ∀ j, (x j).natAbs ≤ B) :
    hnfAbsSum x i ≤ n * B := by
  unfold hnfAbsSum
  have h := List.sum_le_card_nsmul (((List.finRange n).take i).map fun j => (x j).natAbs) B
    (fun y hy => by obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy; exact hB j)
  simp only [List.length_map, List.length_take, List.length_finRange, smul_eq_mul] at h
  exact h.trans (Nat.mul_le_mul_right _ (min_le_right _ _))

theorem hnfAbsSum_le_mul {n : ℕ} (x : Fin n → ℤ) (i : ℕ) {B : ℕ} (hB : ∀ j, (x j).natAbs ≤ B) :
    hnfAbsSum x i ≤ i * B := by
  unfold hnfAbsSum
  have h := List.sum_le_card_nsmul (((List.finRange n).take i).map fun j => (x j).natAbs) B
    (fun y hy => by obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy; exact hB j)
  simp only [List.length_map, List.length_take, List.length_finRange, smul_eq_mul] at h
  exact h.trans (Nat.mul_le_mul_right _ (min_le_left _ _))

/-! ### One entry -/

/-- On `[c, a, z]`: the number `a + |z|`. -/
def hnfAbsStepF (ints : ℕ) : Expr :=
  .letE (.call (ints + 2) (arg 2))
    (.arith .add (arg 1) (.arith .add (.get (.var 1) (.nat 0)) (.get (.var 1) (.nat 1))))

def hnfAbsStepCost (Y : ℕ) : ℕ := linIntCodecCost Y + 100 * (Y + 1)

theorem hnf_nat_wt_le {a k : ℕ} (h : a < 2 ^ k) : (Val.nat a).wt ≤ k + 2 := by
  rw [wt_nat]; have := len_le_iff.mpr h; omega

set_option maxHeartbeats 1000000 in
theorem hnfAbsStep_spec {P : Program} {ints g : ℕ} (hD : hnfDecAt P ints)
    (hg : P.funs[g]? = some (hnfAbsStepF ints)) (c : Val) (a : ℕ) (z : ℤ) {Y : ℕ}
    (hY : (Val.list [c, .nat a, encInt z]).wt ≤ Y) (hres : a + z.natAbs < 2 ^ Y) :
    FunDet P g (.list [c, .nat a, encInt z]) (.nat (a + z.natAbs)) (hnfAbsStepCost Y) := by
  set vs := [c, Val.nat a, encInt z] with hvs
  have dz := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have ddec := Det.call dz (linIntDecode_spec hD.dec hD.bits z)
  set env := [Val.list vs, linIntParts z] with henv
  have dp := Det.get' (Det.var' (P := P) (env := env) (i := 1) rfl) (Det.nat 0)
    (show [Val.nat z.toNat, .nat (-z).toNat][0]? = some (.nat z.toNat) from rfl)
  have dn := Det.get' (Det.var' (P := P) (env := env) (i := 1) rfl) (Det.nat 1)
    (show [Val.nat z.toNat, .nat (-z).toNat][1]? = some (.nat (-z).toNat) from rfl)
  have da := Det.arg' (P := P) (vs := vs) (rest := [linIntParts z]) (j := 1) rfl
  have dsum := Det.arith (op := .add) dp dn
  have e5 : BinOp.add.eval z.toNat (-z).toNat = z.natAbs := by
    show z.toNat + (-z).toNat = z.natAbs; rw [linIntAbsParts]
  rw [e5] at dsum
  have dout := Det.arith (op := .add) da dsum
  have e6 : BinOp.add.eval a z.natAbs = a + z.natAbs := rfl
  rw [e6] at dout
  apply FunDet.intro hg
  refine (Det.letE ddec dout).mono ?_
  have wz : (encInt z).wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have hc := linIntCodecCost_mono (show (encInt z).wt ≤ Y by omega)
  have wP : (linIntParts z).wt < linIntCodecCost (encInt z).wt :=
    (linIntDecode_spec hD.dec hD.bits z).wt_lt
  have h1 : z.natAbs < 2 ^ Y := by omega
  have h2 : z.toNat ≤ z.natAbs := by have := linIntAbsParts z; omega
  have h3 : (-z).toNat ≤ z.natAbs := by have := linIntAbsParts z; omega
  have w1 := hnf_nat_wt_le (show z.toNat < 2 ^ Y by omega)
  have w2 := hnf_nat_wt_le (show (-z).toNat < 2 ^ Y by omega)
  have w3 := hnf_nat_wt_le hres
  have hpY : 1 ≤ 2 ^ Y := Nat.one_le_two_pow
  have hpY' : Y < 2 ^ Y := Nat.lt_two_pow_self
  have e0 : (Val.nat 0).wt = 2 := rfl
  have e1 : (Val.nat 1).wt = 3 := rfl
  have wv : (Val.list vs).wt ≤ Y := hY
  have e7 : (Val.list [Val.nat z.toNat, Val.nat (-z).toNat]).wt = (linIntParts z).wt := rfl
  have w4 := hnf_nat_wt_le (show z.natAbs < 2 ^ Y by omega)
  have w5 := wt_list2_le (Val.nat z.toNat) (Val.nat (-z).toNat)
  unfold hnfAbsStepCost
  omega

/-! ### One row -/

def hnfRowAbsFuns (b ints : ℕ) : List Expr := foldlFuns b (b + 3) ++ [hnfAbsStepF ints]

def hnfRowAbsCost (Y : ℕ) : ℕ := Y * hnfAbsStepCost (5 * Y + 20) + 1000 * (Y + 1) * (6 * Y + 20)

theorem hnfAbsSum_full {n : ℕ} (x : Fin n → ℤ) :
    hnfAbsSum x n = ((List.finRange n).map fun j => (x j).natAbs).sum := by
  unfold hnfAbsSum; rw [List.take_of_length_le (by simp)]

set_option maxHeartbeats 2000000 in
theorem hnfRowAbs_spec {P : Program} {b ints : ℕ} (hD : hnfDecAt P ints)
    (h : P.HasAt b (hnfRowAbsFuns b ints)) {n : ℕ} (c : Val) (x : Fin n → ℤ) (a0 B Y : ℕ)
    (hxB : ∀ j, (x j).natAbs ≤ B) (hV : c.wt + (linVecVal x).wt ≤ Y) (hB : a0 + n * B < 2 ^ Y) :
    FunDet P b (.list [c, linVecVal x, .nat a0]) (.nat (a0 + hnfAbsSum x n)) (hnfRowAbsCost Y) := by
  have hfold : P.HasAt b (foldlFuns b (b + 3)) := h.left
  have hstep : P.funs[b + 3]? = some (hnfAbsStepF ints) := by
    simpa [hnfRowAbsFuns, foldlFuns, loopFuns] using h 3 (by simp [hnfRowAbsFuns, foldlFuns, loopFuns])
  have hn : n < (linVecVal x).wt := by
    have := length_lt_wt_list ((List.finRange n).map fun i => encInt (x i))
    simpa [linVecVal] using this
  have hsum : ∀ i, hnfAbsSum x i ≤ n * B := fun i => hnfAbsSum_le x i hxB
  have hacc : ∀ i, (Val.nat (a0 + hnfAbsSum x i)).wt ≤ Y + 2 := fun i =>
    hnf_nat_wt_le (by have := hsum i; omega)
  have hf := foldl_spec hfold (c := c) (xs := (List.finRange n).map fun i => encInt (x i))
    (acc0 := .nat a0) (M := Y + 2) (B := fun _ => hnfAbsStepCost (5 * Y + 20))
    (Inv := fun i acc => acc = .nat (a0 + hnfAbsSum x i)) (by simp [hnfAbsSum])
    (fun i acc _ hacc' => by rw [hacc']; exact hacc i)
    (fun i acc hi hacc' => by
      subst hacc'
      simp only [List.length_map, List.length_finRange] at hi
      have hs := hnfAbsStep_spec hD hstep c (a0 + hnfAbsSum x i) (x ⟨i, hi⟩) (Y := 5 * Y + 20)
        (by
          have := wt_list3_le c (.nat (a0 + hnfAbsSum x i)) (encInt (x ⟨i, hi⟩))
          have := linVecEntryWt x ⟨i, hi⟩
          have := hacc i
          omega)
        (by
          have := hsum i
          have := hxB ⟨i, hi⟩
          have : 2 ^ Y ≤ 2 ^ (5 * Y + 20) := Nat.pow_le_pow_right (by decide) (by omega)
          have : hnfAbsSum x i + B ≤ n * B := by
            have h8 := hnfAbsSum_le_mul x i hxB
            have h9 : i * B + B ≤ n * B := by
              rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
            omega
          omega)
      simp only [List.getElem_map, List.getElem_finRange]
      refine FunAll.mono hs fun w cst hw => ⟨?_, hw.2⟩
      rw [hw.1, hnfAbsSum_succ x i hi, Nat.add_assoc])
  have e1 : Val.list ((List.finRange n).map fun i => encInt (x i)) = linVecVal x := rfl
  rw [e1] at hf
  refine hf.mono fun w cst hw => ⟨by simpa using hw.1, ?_⟩
  have hc := hw.2
  simp only [List.length_map, List.length_finRange, Finset.sum_const, Finset.card_range,
    smul_eq_mul] at hc
  have w1 := wt_list3_le c (linVecVal x) (.nat a0)
  have w2 := hnf_nat_wt_le (show a0 < 2 ^ Y by have := Nat.zero_le (n * B); omega)
  have h5 : n * hnfAbsStepCost (5 * Y + 20) ≤ Y * hnfAbsStepCost (5 * Y + 20) :=
    Nat.mul_le_mul_right _ (by omega)
  have h6 : loopModK * (n + 1) * ((Val.list [c, linVecVal x, .nat a0]).wt + n + (Y + 2) + 1) ≤
      1000 * (Y + 1) * (6 * Y + 20) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  unfold hnfRowAbsCost
  omega

/-! ### The matrix -/

/-- The sum of `|A i j|` over all entries. -/
def hnfAbsTot (A : Matrix (Fin r) (Fin c) ℤ) (i : ℕ) : ℕ :=
  (((List.finRange r).take i).map fun i => hnfAbsSum (A i) c).sum

def hnfMatAbsStepF (row : ℕ) : Expr := .call row (mk3 (arg 0) (arg 2) (arg 1))

def hnfMatAbsFuns (b ints : ℕ) : List Expr :=
  foldlFuns b (b + 3) ++ [hnfMatAbsStepF (b + 4)] ++ hnfRowAbsFuns (b + 4) ints

theorem hnfMatAbsFuns_length (b ints : ℕ) : (hnfMatAbsFuns b ints).length = 8 := rfl

def hnfMatAbsCost (Y : ℕ) : ℕ :=
  Y * (2 * hnfRowAbsCost (3 * Y + 10) + 100 * (Y + 1)) + 1000 * (Y + 1) * (6 * Y + 20)

theorem hnfAbsTot_le (A : Matrix (Fin r) (Fin c) ℤ) {B : ℕ} (hB : ∀ i j, (A i j).natAbs ≤ B)
    (i : ℕ) : hnfAbsTot A i ≤ r * (c * B) := by
  unfold hnfAbsTot
  have h := List.sum_le_card_nsmul (((List.finRange r).take i).map fun i => hnfAbsSum (A i) c)
    (c * B) (fun y hy => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy; exact hnfAbsSum_le (A j) c (hB j))
  simp only [List.length_map, List.length_take, List.length_finRange, smul_eq_mul] at h
  exact h.trans (Nat.mul_le_mul_right _ (min_le_right _ _))

theorem hnfAbsTot_succ (A : Matrix (Fin r) (Fin c) ℤ) (i : ℕ) (hi : i < r) :
    hnfAbsTot A (i + 1) = hnfAbsTot A i + hnfAbsSum (A ⟨i, hi⟩) c := by
  unfold hnfAbsTot
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hi)]
  simp

set_option maxHeartbeats 2000000 in
/-- **The sum of the absolute values.** On `[0, A, 0]`. -/
theorem hnfMatAbs_spec {P : Program} {b ints : ℕ} (hD : hnfDecAt P ints)
    (h : P.HasAt b (hnfMatAbsFuns b ints)) (A : Matrix (Fin r) (Fin c) ℤ) (B Y : ℕ)
    (hAB : ∀ i j, (A i j).natAbs ≤ B) (hV : (encIntMatrix A).wt ≤ Y) (hB : r * (c * B) < 2 ^ Y) :
    FunDet P b (.list [.nat 0, encIntMatrix A, .nat 0]) (.nat (hnfAbsTot A r)) (hnfMatAbsCost Y) := by
  have hfold : P.HasAt b (foldlFuns b (b + 3)) := h.left.left
  have hstep : P.funs[b + 3]? = some (hnfMatAbsStepF (b + 4)) := by
    simpa using (h.left.block (gs := [hnfMatAbsStepF (b + 4)]) 3 rfl).single
  have hrow : P.HasAt (b + 4) (hnfRowAbsFuns (b + 4) ints) := by simpa using h.block 4 rfl
  have hr : r < (encIntMatrix A).wt := by
    have := length_lt_wt_list ((List.finRange r).map fun i => linVecVal (A i))
    simpa [encIntMatrix, linVecVal] using this
  have htot : ∀ i, hnfAbsTot A i ≤ r * (c * B) := hnfAbsTot_le A hAB
  have hacc : ∀ i, (Val.nat (hnfAbsTot A i)).wt ≤ Y + 2 := fun i =>
    hnf_nat_wt_le (by have := htot i; omega)
  have hf := foldl_spec hfold (c := .nat 0) (xs := (List.finRange r).map fun i => linVecVal (A i))
    (acc0 := .nat 0) (M := Y + 2) (B := fun _ => 2 * hnfRowAbsCost (3 * Y + 10) + 100 * (Y + 1))
    (Inv := fun i acc => acc = .nat (hnfAbsTot A i)) (by simp [hnfAbsTot])
    (fun i acc _ hacc' => by rw [hacc']; exact hacc i)
    (fun i acc hi hacc' => by
      subst hacc'
      simp only [List.length_map, List.length_finRange] at hi
      have hwr := hnf_row_wt_lt A ⟨i, hi⟩
      have hs := hnfRowAbs_spec hD hrow (.nat 0) (A ⟨i, hi⟩) (hnfAbsTot A i) B (3 * Y + 10)
        (hAB ⟨i, hi⟩) (by have : (Val.nat 0).wt = 2 := rfl; omega)
        (by
          have h3 := htot (i + 1)
          rw [hnfAbsTot_succ A i hi] at h3
          have := hnfAbsSum_le (A ⟨i, hi⟩) c (B := B) (hAB ⟨i, hi⟩)
          have h4 : c * B ≤ r * (c * B) := Nat.le_mul_of_pos_left _ (by omega)
          have : 2 ^ Y ≤ 2 ^ (3 * Y + 10) := Nat.pow_le_pow_right (by decide) (by omega)
          have h5 : hnfAbsTot A i + c * B ≤ r * (c * B) := by
            have h6 : hnfAbsTot A i + hnfAbsSum (A ⟨i, hi⟩) c ≤ r * (c * B) := h3
            have h7 : hnfAbsTot A (i + 1) ≤ r * (c * B) := htot (i + 1)
            -- the partial sums over `i + 1 ≤ r` rows are at most `(i + 1) c B`
            have h8 : hnfAbsTot A i ≤ i * (c * B) := by
              unfold hnfAbsTot
              have h := List.sum_le_card_nsmul (((List.finRange r).take i).map
                fun i => hnfAbsSum (A i) c) (c * B) (fun y hy => by
                  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy; exact hnfAbsSum_le (A j) c (hAB j))
              simp only [List.length_map, List.length_take, List.length_finRange,
                smul_eq_mul] at h
              exact h.trans (Nat.mul_le_mul_right _ (min_le_left _ _))
            have h9 : i * (c * B) + c * B ≤ r * (c * B) := by
              rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
            omega
          omega)
      have dc := Det.arg' (P := P) (vs := [Val.nat 0, .nat (hnfAbsTot A i), linVecVal (A ⟨i, hi⟩)])
        (rest := []) (j := 0) rfl
      have dr := Det.arg' (P := P) (vs := [Val.nat 0, .nat (hnfAbsTot A i), linVecVal (A ⟨i, hi⟩)])
        (rest := []) (j := 2) rfl
      have da := Det.arg' (P := P) (vs := [Val.nat 0, .nat (hnfAbsTot A i), linVecVal (A ⟨i, hi⟩)])
        (rest := []) (j := 1) rfl
      have dout := Det.call (Det.mk3 dc dr da) hs
      rw [← hnfAbsTot_succ A i hi] at dout
      simp only [List.getElem_map, List.getElem_finRange]
      refine ⟨_, hstep, dout.mono ?_⟩
      have := hacc i
      have := hacc (i + 1)
      have w1 := wt_list3_le (.nat 0) (.nat (hnfAbsTot A i)) (linVecVal (A ⟨i, hi⟩))
      have w2 := wt_list3_le (.nat 0) (linVecVal (A ⟨i, hi⟩)) (.nat (hnfAbsTot A i))
      have := hs.wt_lt
      have e0 : (Val.nat 0).wt = 2 := rfl
      omega)
  have e1 : Val.list ((List.finRange r).map fun i => linVecVal (A i)) = encIntMatrix A := rfl
  rw [e1] at hf
  refine hf.mono fun w cst hw => ⟨by simpa using hw.1, ?_⟩
  have hc := hw.2
  simp only [List.length_map, List.length_finRange, Finset.sum_const, Finset.card_range,
    smul_eq_mul] at hc
  have w1 := wt_list3_le (.nat 0) (encIntMatrix A) (.nat 0)
  have e0 : (Val.nat 0).wt = 2 := rfl
  have h5 : r * (2 * hnfRowAbsCost (3 * Y + 10) + 100 * (Y + 1)) ≤
      Y * (2 * hnfRowAbsCost (3 * Y + 10) + 100 * (Y + 1)) := Nat.mul_le_mul_right _ (by omega)
  have h6 : loopModK * (r + 1) * ((Val.list [.nat 0, encIntMatrix A, .nat 0]).wt + r + (Y + 2) + 1) ≤
      1000 * (Y + 1) * (6 * Y + 20) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  unfold hnfMatAbsCost
  omega

end GI.Impl
