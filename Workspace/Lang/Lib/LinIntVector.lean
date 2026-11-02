import Workspace.Lang.Lib.LinInt

/-! Vector operations over the cited integer encoding. The scalar function is a
proved program, not a primitive. The shared loop applies it pointwise to two vectors. -/
namespace GI.Lang
open GI.Cited (Val encInt)

/-- Vector values use the same row format as encIntMatrix. -/
def linVecVal {n : ℕ} (x : Fin n → ℤ) : Val :=
  .list ((List.finRange n).map fun i => encInt (x i))

theorem linIntBinaryCost_mono {W V : ℕ} (h : W ≤ V) : linIntBinaryCost W ≤ linIntBinaryCost V := by
  have hD := linIntCodecCost_mono h
  have hC : linIntCoreBudget W ≤ linIntCoreBudget V := linIntPartsCost_mono (by omega)
  have hE := linIntCodecCost_mono hC
  unfold linIntBinaryCost
  omega

/-- The pointwise loop step on [original-input,index,accumulator]. -/
def linVectorBinaryStep (scalar : ℕ) : Expr :=
  .snoc (arg 2) (.call scalar (mk2
    (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.get (.get (arg 0) (.nat 1)) (arg 1))))

def linVectorBinaryFuns (b scalar : ℕ) : List Expr :=
  loopFuns b (.length (arg 0)) .nil (linVectorBinaryStep scalar)

/-- Bound for all partial output lists. B bounds the weight of one scalar output. -/
def linVectorAccWt (n B : ℕ) : ℕ := 2 * (n * B) + n + 4

def linVectorBinaryCost (W n B : ℕ) : ℕ :=
  let M := linVectorAccWt n B
  n * (linIntBinaryCost (4 * W + 6) + 1000 * (W + n + M + B + 1)) +
    loopModK * (n + 1) * (W + n + M + 1)

set_option maxHeartbeats 1000000 in
/-- Pointwise binary vector operations with a polynomial cost in input length and
one bound B on output-entry bit weight. Scalar correctness is supplied by the installed library. -/
theorem linVectorBinary_spec {P : Program} {b scalar n : ℕ}
    (hp : P.HasAt b (linVectorBinaryFuns b scalar)) (op : ℤ → ℤ → ℤ)
    (hs : ∀ x y : ℤ, FunDet P scalar (.list [encInt x, encInt y]) (encInt (op x y))
      (linIntBinaryCost (Val.list [encInt x, encInt y]).wt))
    (x y : Fin n → ℤ) (B : ℕ) (hB : ∀ i, (encInt (op (x i) (y i))).wt ≤ B) :
    FunDet P b (.list [linVecVal x, linVecVal y]) (linVecVal fun i => op (x i) (y i))
      (linVectorBinaryCost (Val.list [linVecVal x, linVecVal y]).wt n B) := by
  let a := Val.list [linVecVal x, linVecVal y]
  let outs := (List.finRange n).map fun i => encInt (op (x i) (y i))
  let M := linVectorAccWt n B
  have hn : n < a.wt := by
    have hl := length_lt_wt_list ((List.finRange n).map fun i => encInt (x i))
    have hv := wt_le_wt_list (vs := [linVecVal x, linVecVal y]) (v := linVecVal x) (by simp)
    simp only [List.length_map, List.length_finRange] at hl
    exact hl.trans hv
  have hacc (i : ℕ) : (Val.list (outs.take i)).wt ≤ M := by
    have ht := linWtList (vs := outs.take i) (B := B) (by
      intro v hv
      have hv' := List.mem_of_mem_take hv
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv'
      exact hB j)
    have hl : (outs.take i).length ≤ n := by
      have := List.length_take_le i outs
      simpa [outs] using this
    unfold M linVectorAccWt
    nlinarith
  have dk := Det.length (Det.arg' (P := P) (vs := [linVecVal x, linVecVal y])
    (rest := []) (j := 0) rfl)
  simp only [List.length_map, List.length_finRange] at dk
  have hlp : P.HasAt b (loopFuns b (.length (arg 0)) .nil (linVectorBinaryStep scalar)) := hp
  have hloop := loopBdd_spec hlp dk Det.nil (by
    change 2 * a.wt + 0 + 5 + n + 3 + 5 ≤ 10 * (a.wt + n + 1)
    have hw := a.two_le_size.trans a.size_le_wt
    omega)
    (Inv := fun i acc => acc = .list (outs.take i)) (M := M)
    (D := fun _ => linIntBinaryCost (4 * a.wt + 6) + 1000 * (a.wt + n + M + B + 1))
    (by simp) (fun i acc _ he => he ▸ hacc i) (fun i acc hi he => ?_)
  · refine hloop.mono fun w cost hw => ⟨?_, ?_⟩
    · have houtlen : outs.length = n := by simp [outs]
      have he := hw.1
      rw [← houtlen, List.take_length] at he
      exact he
    · simpa [linVectorBinaryCost, M, a, Finset.sum_const, Finset.card_range, smul_eq_mul] using hw.2
  · subst acc
    let j : Fin n := ⟨i, hi⟩
    have dax := Det.get' (Det.arg' (P := P) (vs := [a, .nat i, .list (outs.take i)])
      (rest := []) (j := 0) rfl) (Det.nat 0) (show [linVecVal x, linVecVal y][0]? = _ from rfl)
    have day := Det.get' (Det.arg' (P := P) (vs := [a, .nat i, .list (outs.take i)])
      (rest := []) (j := 0) rfl) (Det.nat 1) (show [linVecVal x, linVecVal y][1]? = _ from rfl)
    have di := Det.arg' (P := P) (vs := [a, .nat i, .list (outs.take i)]) (rest := []) (j := 1) rfl
    have hget : (List.finRange n)[i]? = some j := by
      rw [List.getElem?_eq_getElem (by simpa using hi)]
      simp [j]
    have dx := Det.get' dax di (by rw [List.getElem?_map, hget]; rfl)
    have dy := Det.get' day di (by rw [List.getElem?_map, hget]; rfl)
    have dcall := Det.call (Det.mk2 dx dy) (hs (x j) (y j))
    have da := Det.arg' (P := P) (vs := [a, .nat i, .list (outs.take i)]) (rest := []) (j := 2) rfl
    have dres := Det.snoc da dcall
    have heq : outs.take (i + 1) = outs.take i ++ [encInt (op (x j) (y j))] := by
      rw [List.take_add_one]
      have hget : outs[i]? = some (encInt (op (x j) (y j))) := by simp [outs, hi, j]
      rw [hget]; rfl
    refine dres.post fun cost hc => ⟨?_, ?_⟩
    · change Val.list (outs.take i ++ [encInt (op (x j) (y j))]) = Val.list (outs.take (i + 1))
      rw [heq]
    · have wx := wt_le_wt_list (vs := [linVecVal x, linVecVal y]) (v := linVecVal x) (by simp)
      have wy := wt_le_wt_list (vs := [linVecVal x, linVecVal y]) (v := linVecVal y) (by simp)
      have wxx := wt_le_wt_list (vs := (List.finRange n).map fun k => encInt (x k))
        (v := encInt (x j)) (by simp)
      have wyy := wt_le_wt_list (vs := (List.finRange n).map fun k => encInt (y k))
        (v := encInt (y j)) (by simp)
      change (linVecVal x).wt < a.wt at wx
      change (linVecVal y).wt < a.wt at wy
      change (encInt (x j)).wt < (linVecVal x).wt at wxx
      change (encInt (y j)).wt < (linVecVal y).wt at wyy
      have wxy := wt_list2_le (encInt (x j)) (encInt (y j))
      have hC := linIntBinaryCost_mono (show (Val.list [encInt (x j), encInt (y j)]).wt ≤
        4 * a.wt + 6 by omega)
      have wstep := wt_list3_le a (.nat i) (.list (outs.take i))
      have wi := wt_nat_le i
      have wi0 : (Val.nat 0).wt = 2 := rfl
      have wi1 : (Val.nat 1).wt = 3 := rfl
      have wacc := hacc i
      have wout := hacc (i + 1)
      rw [heq] at wout
      have wb := hB j
      beta_reduce at hc ⊢
      change cost ≤ (linIntBinaryCost (4 * a.wt + 6) + 1000 * (a.wt + n + M + B + 1)) +
        100 * (a.wt + n + M + 1)
      omega

/-- An encoded entry's magnitude has at most its value weight many bits. -/
theorem linEncIntAbs (z : ℤ) : z.natAbs < 2 ^ (encInt z).wt := by
  have hl := length_lt_wt_list (z.natAbs.bits.map fun b => Val.nat (linBit b))
  have hw := wt_le_wt_list
    (vs := [.nat (if z < 0 then 1 else 0), linBitsVal z.natAbs.bits])
    (v := linBitsVal z.natAbs.bits) (by simp)
  have hlen : z.natAbs.bits.length ≤ (encInt z).wt := by
    simp only [List.length_map] at hl
    exact (hl.trans hw).le
  calc
    z.natAbs = linBitsNat z.natAbs.bits := (linBitsNat_bits _).symm
    _ < 2 ^ z.natAbs.bits.length := linBitsNat_lt _
    _ ≤ 2 ^ (encInt z).wt := Nat.pow_le_pow_right (by decide) hlen

/-- A sum increases the bit bound by at most one. -/
theorem linEncIntAddWt (x y : ℤ) (W : ℕ) (hx : (encInt x).wt ≤ W) (hy : (encInt y).wt ≤ W) :
    (encInt (x + y)).wt ≤ 20 * (W + 2) := by
  apply linWtInt (B := W + 1)
  have hxa := (linEncIntAbs x).trans_le (Nat.pow_le_pow_right (by decide) hx)
  have hya := (linEncIntAbs y).trans_le (Nat.pow_le_pow_right (by decide) hy)
  have hsum := Int.natAbs_add_le x y
  rw [pow_succ]
  omega

theorem linEncIntSubWt (x y : ℤ) (W : ℕ) (hx : (encInt x).wt ≤ W) (hy : (encInt y).wt ≤ W) :
    (encInt (x - y)).wt ≤ 20 * (W + 2) := by
  apply linWtInt (B := W + 1)
  have hxa := (linEncIntAbs x).trans_le (Nat.pow_le_pow_right (by decide) hx)
  have hya := (linEncIntAbs y).trans_le (Nat.pow_le_pow_right (by decide) hy)
  have hsum := Int.natAbs_sub_le x y
  rw [pow_succ]
  omega

/-- A product adds the two operand bit bounds. -/
theorem linEncIntMulWt (x y : ℤ) (W : ℕ) (hx : (encInt x).wt ≤ W) (hy : (encInt y).wt ≤ W) :
    (encInt (x * y)).wt ≤ 20 * (2 * W + 1) := by
  apply linWtInt (B := 2 * W)
  have hxa := (linEncIntAbs x).trans_le (Nat.pow_le_pow_right (by decide) hx)
  have hya := (linEncIntAbs y).trans_le (Nat.pow_le_pow_right (by decide) hy)
  rw [Int.natAbs_mul, show 2 * W = W + W by omega, pow_add]
  exact Nat.mul_lt_mul'' hxa hya

theorem linVecEntryWt {n : ℕ} (x : Fin n → ℤ) (i : Fin n) : (encInt (x i)).wt < (linVecVal x).wt :=
  wt_le_wt_list (by simp)

/-- Vector addition on two encoded integer rows. -/
theorem linVectorAdd_spec {P : Program} {b ib n : ℕ} (h : linIntSpec P ib)
    (hp : P.HasAt b (linVectorBinaryFuns b (ib + 11))) (x y : Fin n → ℤ) :
    FunDet P b (.list [linVecVal x, linVecVal y]) (linVecVal fun i => x i + y i)
      (linVectorBinaryCost (Val.list [linVecVal x, linVecVal y]).wt n
        (20 * ((Val.list [linVecVal x, linVecVal y]).wt + 2))) := by
  apply linVectorBinary_spec hp (· + ·) h.add x y
  intro i
  have wx := wt_le_wt_list (vs := [linVecVal x, linVecVal y]) (v := linVecVal x) (by simp)
  have wy := wt_le_wt_list (vs := [linVecVal x, linVecVal y]) (v := linVecVal y) (by simp)
  exact linEncIntAddWt _ _ _ ((linVecEntryWt x i).trans wx).le ((linVecEntryWt y i).trans wy).le

/-- Vector subtraction on two encoded integer rows. -/
theorem linVectorSub_spec {P : Program} {b ib n : ℕ} (h : linIntSpec P ib)
    (hp : P.HasAt b (linVectorBinaryFuns b (ib + 12))) (x y : Fin n → ℤ) :
    FunDet P b (.list [linVecVal x, linVecVal y]) (linVecVal fun i => x i - y i)
      (linVectorBinaryCost (Val.list [linVecVal x, linVecVal y]).wt n
        (20 * ((Val.list [linVecVal x, linVecVal y]).wt + 2))) := by
  apply linVectorBinary_spec hp (· - ·) h.sub x y
  intro i
  have wx := wt_le_wt_list (vs := [linVecVal x, linVecVal y]) (v := linVecVal x) (by simp)
  have wy := wt_le_wt_list (vs := [linVecVal x, linVecVal y]) (v := linVecVal y) (by simp)
  exact linEncIntSubWt _ _ _ ((linVecEntryWt x i).trans wx).le ((linVecEntryWt y i).trans wy).le

/-- Scalar multiplication uses the list map module with the integer multiply function. -/
def linVectorScaleFuns (b ib : ℕ) : List Expr := mapFuns b (ib + 13)

def linVectorScaleCost (W n : ℕ) : ℕ :=
  n * linIntBinaryCost (4 * W + 6) + mapK * (n + 1) * (W + linVectorAccWt n (20 * (2 * W + 1)) + 1)

/-- Multiplication of a scalar and an integer row, with polynomial bit cost. -/
theorem linVectorScale_spec {P : Program} {b ib n : ℕ} (h : linIntSpec P ib)
    (hp : P.HasAt b (linVectorScaleFuns b ib)) (a : ℤ) (x : Fin n → ℤ) :
    FunDet P b (.list [encInt a, linVecVal x]) (linVecVal fun i => a * x i)
      (linVectorScaleCost (Val.list [encInt a, linVecVal x]).wt n) := by
  let W := (Val.list [encInt a, linVecVal x]).wt
  let C := linIntBinaryCost (4 * W + 6)
  have wa : (encInt a).wt < W := wt_le_wt_list (by simp)
  have wv : (linVecVal x).wt < W := wt_le_wt_list (by simp)
  have ho (i : Fin n) : (encInt (a * x i)).wt ≤ 20 * (2 * W + 1) :=
    linEncIntMulWt _ _ _ wa.le ((linVecEntryWt x i).trans wv).le
  have hs : ∀ v ∈ (List.finRange n).map (fun i => encInt (x i)),
      FunAll P (ib + 13) (.list [encInt a, v]) (fun w cost =>
        (∀ i : Fin n, v = encInt (x i) → w = encInt (a * x i)) ∧ cost ≤ C) := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    have wi := (linVecEntryWt x i).trans wv
    have warg := wt_list2_le (encInt a) (encInt (x i))
    have hcost := linIntBinaryCost_mono (show (Val.list [encInt a, encInt (x i)]).wt ≤ 4 * W + 6 by omega)
    refine FunAll.mono (h.mul a (x i)) fun w cost hw => ⟨?_, by omega⟩
    intro j hj
    have he := encInt_injective hj
    rw [hw.1, he]
  have hm := map_spec hp hs
  refine hm.mono fun w cost hw => ?_
  obtain ⟨ws, rfl, hws, hc⟩ := hw
  have he : ws = (List.finRange n).map (fun i => encInt (a * x i)) :=
    forall₂_map_eq (h := hws) (fun i _ w hw => hw i rfl)
  subst ws
  refine ⟨rfl, ?_⟩
  have wo := linWtList (vs := (List.finRange n).map (fun i => encInt (a * x i)))
    (B := 20 * (2 * W + 1)) (by
      intro v hv
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
      exact ho i)
  simp only [List.length_map, List.length_finRange, List.map_const', List.sum_replicate,
    smul_eq_mul] at hc wo
  unfold linVectorScaleCost linVectorAccWt
  change cost ≤ n * C + mapK * (n + 1) *
    (W + (Val.list ((List.finRange n).map fun i => encInt (a * x i))).wt + 1) at hc
  change cost ≤ n * C + mapK * (n + 1) * (W + (2 * (n * (20 * (2 * W + 1))) + n + 4) + 1)
  have hm := Nat.mul_le_mul_left (mapK * (n + 1)) wo
  nlinarith

attribute [gcongr] linIntBinaryCost_mono

theorem linVectorAccWt_mono {n m B C : ℕ} (hn : n ≤ m) (hB : B ≤ C) :
    linVectorAccWt n B ≤ linVectorAccWt m C := by unfold linVectorAccWt; gcongr

theorem linVectorScaleCost_mono {W V n m : ℕ} (hW : W ≤ V) (hn : n ≤ m) :
    linVectorScaleCost W n ≤ linVectorScaleCost V m := by
  unfold linVectorScaleCost linVectorAccWt
  gcongr

theorem linVectorBinaryCost_mono {W V n m B C : ℕ} (hW : W ≤ V) (hn : n ≤ m) (hB : B ≤ C) :
    linVectorBinaryCost W n B ≤ linVectorBinaryCost V m C := by
  dsimp only [linVectorBinaryCost, linVectorAccWt]
  gcongr

end GI.Lang
