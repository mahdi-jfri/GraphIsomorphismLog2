module

public import Workspace.Impl.GenSpecMath
public import Workspace.Impl.GenBranch

@[expose] public section

/-!
# The own cost of the general dispatcher, as a function of the number of points

The general step on a canonical state value of weight at most `Ws` on `k` points runs the
exposure, one `GroupOrder` call, the case decision and the branch. `gsOwn k Ws` bounds the cost
of all four besides the children. It depends only on `k` and `Ws`: the order `B = |ρ(G)|` that the
enumeration depends on and the `r!` of the product step are at most `gsBk k`
(`gs_card_le_Bk`, `gs_fact_le_Bk`), and the output of the case decision weighs at most `gsWc k`.

* `gsX`: the cost bound of the exposure (`expose_spec`), which also bounds its output weight;
* `gsWb`: the weight bound of the input `[v, x, w, B]` of the branch;
* `gsBr`: the own cost bound of the branch for every case (`gs_brCost_le`);
* `gsCase`: the case decision (`gs_caseCost_le`);
* `gsOwn`: the total, monotone in `Ws` (`gsOwn_mono`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val GroupOrder CameronRecognition MinimalBlocks Preimage Membership)

/-- The cost bound of the exposure on an input of weight at most `Ws`. -/
noncomputable def gsX (hmb : MinimalBlocks) (Ws : ℕ) : ℕ :=
  exposeK * (Ws + 1) ^ 8 + (minimalBlocksPrim hmb).c *
    (100 * (Ws + 1) ^ 4 + 2) ^ (minimalBlocksPrim hmb).k

/-- The weight bound of the input `[v, x, w, B]` of the branch. -/
def gsWb (k Ws X : ℕ) : ℕ := 2 * (Ws + X + gsWc k + (k ^ 2 + 3)) + 8

/-- The own cost bound of the branch on an input of weight at most `Wb`. -/
noncomputable def gsBr (hp : Preimage) (hm : Membership) (Cn : ℕ → ℕ → ℕ) (k Wb : ℕ) : ℕ :=
  enumCost hp hm k (2 * Wb + 10) (gsBk k) + prodCost hp hm k Wb (gsBk k) + Cn k Wb +
    40 * Wb + 3 * ansW k + 400

/-- The cost bound of the case decision on `[d, gv']` with `gv'` of weight at most `X`. -/
noncomputable def gsCase (hO : GroupOrder) (hC : CameronRecognition) (k X : ℕ) : ℕ :=
  (groupOrderPrim hO).c * (X + 2) ^ (groupOrderPrim hO).k +
    (cameronRecognitionPrim hC).c * (X + 2) ^ (cameronRecognitionPrim hC).k + caseZ k +
    400 * (X + k + 40) + 10 * k ^ 2

/-- **The own cost bound of the general step** on `k` points and an input of weight at most
`Ws`. -/
noncomputable def gsOwn (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition)
    (hp : Preimage) (hm : Membership) (Cn : ℕ → ℕ → ℕ) (k Ws : ℕ) : ℕ :=
  100 * (Ws + gsX hmb Ws + (k + 2) ^ 2 + gsWc k + ansW k + 100) +
    2 * (groupOrderPrim hO).c * (gsX hmb Ws + 2) ^ (groupOrderPrim hO).k +
    gsCase hO hC k (gsX hmb Ws) +
    10 * gsWb k Ws (gsX hmb Ws) + gsBr hp hm Cn k (gsWb k Ws (gsX hmb Ws))

theorem prodCost_mono_B (hp : Preimage) (hm : Membership) (k W : ℕ) {B B' : ℕ} (h : B ≤ B') :
    prodCost hp hm k W B ≤ prodCost hp hm k W B' := by
  unfold prodCost
  have h1 : prodY k W B ^ 48 ≤ prodY k W B' ^ 48 :=
    Nat.pow_le_pow_left (by unfold prodY; omega) 48
  have h2 := tailCost_mono hm k (Nat.mul_le_mul_left (10 ^ 105) h1)
  have h3 := Nat.mul_le_mul_left (10 ^ 110) h1
  omega

theorem enumCost_mono_B (hp : Preimage) (hm : Membership) (k W : ℕ) {B B' : ℕ} (h : B ≤ B') :
    enumCost hp hm k W B ≤ enumCost hp hm k W B' := by
  unfold enumCost
  have h1 := Nat.mul_le_mul_left cosetsK
    (Nat.pow_le_pow_left (show W + B + 4 * (k + 1) ^ 2 + 20 ≤ W + B' + 4 * (k + 1) ^ 2 + 20 by
      omega) 6)
  have hp' : pairsW k B ≤ pairsW k B' := by
    unfold pairsW; have := Nat.mul_le_mul_right (2 * (16 * (k + 1) ^ 2 + 6) + 1) h; omega
  have h3 : tailInW k W B ≤ tailInW k W B' := by unfold tailInW; omega
  have h4 := tailCost_mono hm k h3
  omega

/-- **The branch costs at most `gsBr`**, for an input weight `W ≤ Wb`, an order `B ≤ gsBk k` in
the enumeration (`r = 0`) and `r! ≤ gsBk k` otherwise. -/
theorem gs_brCost_le (hp : Preimage) (hm : Membership) {Cn : ℕ → ℕ → ℕ}
    (hCn : ∀ {k W W' : ℕ}, W ≤ W' → Cn k W ≤ Cn k W') {k W Wb B r : ℕ} (hW : W ≤ Wb)
    (hB : r = 0 → B ≤ gsBk k) (hr : r ≠ 0 → r.factorial ≤ gsBk k) :
    brCost hp hm Cn k W B r ≤ gsBr hp hm Cn k Wb := by
  unfold brCost gsBr
  by_cases h0 : r = 0
  · rw [if_pos h0]
    have h1 := enumCost_mono hp hm k B (show 2 * W + 10 ≤ 2 * Wb + 10 by omega)
    have h2 := enumCost_mono_B hp hm k (2 * Wb + 10) (hB h0)
    omega
  · rw [if_neg h0]
    have h1 := prodCost_mono hp hm k r.factorial hW
    have h2 := prodCost_mono_B hp hm k Wb (hr h0)
    have h3 : Cn k W ≤ Cn k Wb := hCn hW
    omega

theorem caseZ_mono {d d' : ℕ} (h : d ≤ d') : caseZ d ≤ caseZ d' := by
  unfold caseZ
  refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 2)
  have := Nat.pow_le_pow_left h 2
  omega

/-- **The case decision costs at most `gsCase`** when `d ≤ k` and `gv'` weighs at most `X`. -/
theorem gs_caseCost_le (hO : GroupOrder) (hC : CameronRecognition) {gv : Val} {d k X : ℕ}
    (hd : d ≤ k) (hX : gv.wt ≤ X) : caseCost hO hC gv d ≤ gsCase hO hC k X := by
  unfold caseCost gsCase
  have h1 := mb_bound_le (groupOrderPrim hO) hX
  have h2 := mb_bound_le (cameronRecognitionPrim hC) hX
  have h3 := caseZ_mono hd
  have h4 := Nat.pow_le_pow_left hd 2
  omega

theorem gsX_mono (hmb : MinimalBlocks) {W W' : ℕ} (h : W ≤ W') : gsX hmb W ≤ gsX hmb W' := by
  unfold gsX
  have h1 := Nat.mul_le_mul_left exposeK (Nat.pow_le_pow_left (show W + 1 ≤ W' + 1 by omega) 8)
  have h2 := Nat.pow_le_pow_left (show W + 1 ≤ W' + 1 by omega) 4
  have h3 := Nat.mul_le_mul_left (minimalBlocksPrim hmb).c (Nat.pow_le_pow_left
    (show 100 * (W + 1) ^ 4 + 2 ≤ 100 * (W' + 1) ^ 4 + 2 by omega) (minimalBlocksPrim hmb).k)
  omega

theorem gsOwn_mono (hmb : MinimalBlocks) (hO : GroupOrder) (hC : CameronRecognition)
    (hp : Preimage) (hm : Membership) {Cn : ℕ → ℕ → ℕ}
    (hCn : ∀ {k W W' : ℕ}, W ≤ W' → Cn k W ≤ Cn k W') (k : ℕ) {W W' : ℕ} (h : W ≤ W') :
    gsOwn hmb hO hC hp hm Cn k W ≤ gsOwn hmb hO hC hp hm Cn k W' := by
  have hX := gsX_mono hmb h
  have hWb : gsWb k W (gsX hmb W) ≤ gsWb k W' (gsX hmb W') := by unfold gsWb; omega
  have h1 := Nat.mul_le_mul_left (2 * (groupOrderPrim hO).c)
    (Nat.pow_le_pow_left (show gsX hmb W + 2 ≤ gsX hmb W' + 2 by omega) (groupOrderPrim hO).k)
  have h2 : gsCase hO hC k (gsX hmb W) ≤ gsCase hO hC k (gsX hmb W') := by
    unfold gsCase
    have := Nat.mul_le_mul_left (groupOrderPrim hO).c
      (Nat.pow_le_pow_left (show gsX hmb W + 2 ≤ gsX hmb W' + 2 by omega) (groupOrderPrim hO).k)
    have := Nat.mul_le_mul_left (cameronRecognitionPrim hC).c
      (Nat.pow_le_pow_left (show gsX hmb W + 2 ≤ gsX hmb W' + 2 by omega)
        (cameronRecognitionPrim hC).k)
    omega
  have h3 : gsBr hp hm Cn k (gsWb k W (gsX hmb W)) ≤ gsBr hp hm Cn k (gsWb k W' (gsX hmb W')) := by
    unfold gsBr
    have := enumCost_mono hp hm k (gsBk k) (show 2 * gsWb k W (gsX hmb W) + 10 ≤
      2 * gsWb k W' (gsX hmb W') + 10 by omega)
    have := prodCost_mono hp hm k (gsBk k) hWb
    have := hCn (k := k) hWb
    omega
  unfold gsOwn
  omega

end GI.Impl
