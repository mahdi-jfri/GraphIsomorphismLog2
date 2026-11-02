import Workspace.Proved.VsQMat
import Workspace.Impl.VsQPow

/-!
# Matrices as group elements

A matrix `M` is carried as `vsQE p d E M = [p, 0, E, Mᵀ]`: the prime, a zero vector of length
`d`, an exponent `E` (used for inverses), and the canonical list of the transpose. The rows of
`Mᵀ` are the images of the unit vectors under the row action `v ↦ M v`, written as rows.

* `vsQMulF`: the product, `vsQMul_spec`: on `[vsQE x, vsQE y]` it returns `vsQE (x * y)`
  (since `(xy)ᵀ = yᵀ xᵀ`, it multiplies the stored lists in the other order).
* `vsQInvF`: on `vsQE x`, `vsQE (x ^ (E + 1))`, by binary powering. In a group of exponent
  dividing `E + 2` this is `x⁻¹`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Matrix

/-- The carried form of a matrix. -/
def vsQE (p d E : ℕ) (M : Matrix (Fin d) (Fin d) (ZMod p)) : Val :=
  .list [.nat p, natList (List.replicate d 0), .nat E, .list ((vsQL Mᵀ).map natList)]

/-- The product, on `[vsQE x, vsQE y]`, calling the matrix product at `mm`. -/
def vsQMulF (mm : ℕ) : Expr :=
  mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2))
    (.call mm (mk2 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 3)) (.get (arg 0) (.nat 1)))
      (.get (arg 1) (.nat 3))))

/-- The product with a context, on `[c, x, y]`. -/
def vsQMul3F (mul : ℕ) : Expr := .call mul (mk2 (arg 1) (arg 2))

/-- The power `x ^ (E + 1)`, on `vsQE x`. -/
def vsQInvF (pow : ℕ) : Expr :=
  .call pow (mk4 (.nat 0) (.var 0) (.get (.var 0) (.nat 2)) (.var 0))

/-- The group operations at base `b` (20 functions): product at `b`, inverse at `b + 2`. -/
def vsQGLFuns (b : ℕ) : List Expr :=
  [vsQMulF (b + 4), vsQMul3F b, vsQInvF (b + 3), vsQPowF (b + 3) (b + 1)] ++ vsFMatMulFuns (b + 4)

theorem vsQGLFuns_length (b : ℕ) : (vsQGLFuns b).length = 20 := rfl

variable {p d E N : ℕ}

/-- The size hypotheses: `p, d ≤ N` and the exponent has weight at most `N`. -/
structure VsQSz (p d E N : ℕ) : Prop where
  pN : p ≤ N
  dN : d ≤ N
  eN : (Val.nat E).wt ≤ N
  p0 : 0 < p

theorem wt_vsQL_le [NeZero p] (h : VsQSz p d E N) (M : Matrix (Fin d) (Fin d) (ZMod p)) :
    (Val.list ((vsQL M).map natList)).wt ≤ 11 * (N + 1) ^ 3 + 4 :=
  wt_vsFSq_le h.pN h.dN (vsQL_sq M)

theorem wt_zero_le (h : VsQSz p d E N) : (natList (List.replicate d 0)).wt ≤ 5 * (N + 1) ^ 2 :=
  wt_natList_le_sq (fun y hy => by rw [List.eq_of_mem_replicate hy]; omega) (by simp [h.dN])

theorem wt_vsQE_le [NeZero p] (h : VsQSz p d E N) (M : Matrix (Fin d) (Fin d) (ZMod p)) :
    (vsQE p d E M).wt ≤ 100 * (N + 1) ^ 3 := by
  have w1 := wt_vsQL_le h Mᵀ
  have w2 := wt_zero_le h
  have w3 := wt_nat_le p
  have w4 := wt_list4_le (.nat p) (natList (List.replicate d 0)) (.nat E)
    (.list ((vsQL Mᵀ).map natList))
  have q2 := vsQ_powle (c := 1) (by omega : 1 ≤ N + 1) (show 2 ≤ 3 by omega) (Q := N + 1)
  have q1 := vsQ_le_pow N (k := 3) (by omega)
  have := h.pN
  have := h.eN
  unfold vsQE
  omega

set_option maxHeartbeats 1000000 in
/-- **The product.** -/
theorem vsQMul_spec [NeZero p] {P : Program} {b : ℕ} (hb : P.HasAt b (vsQGLFuns b))
    (h : VsQSz p d E N) (x y : Matrix (Fin d) (Fin d) (ZMod p)) :
    FunDet P b (.list [vsQE p d E x, vsQE p d E y]) (vsQE p d E (x * y))
      (6 * 10 ^ 6 * (N + 1) ^ 5) := by
  have h0 : P.funs[b]? = some (vsQMulF (b + 4)) := hb.get (j := 0) (by rw [vsQGLFuns_length]; omega)
  have hmm : P.HasAt (b + 4) (vsFMatMulFuns (b + 4)) := hb.block 4 rfl
  have hz : ∀ y ∈ List.replicate d 0, y < p := by
    intro y hy; rw [List.eq_of_mem_replicate hy]; exact h.p0
  have sx := vsQL_sq xᵀ
  have sy := vsQL_sq yᵀ
  have HB : VsFMatFits p N (vsQL xᵀ) (List.replicate d 0) :=
    ⟨hz, by simp [h.dN], fun r hr y hy => ((sx.rows r hr).1 y hy).le.trans h.pN,
      fun r hr => (sx.rows r hr).2.trans_le h.dN,
      fun r hr => by rw [(sx.rows r hr).2]; simp, by rw [sx.len]; exact h.dN⟩
  have HA : ∀ a ∈ vsQL yᵀ, (∀ z ∈ a, z < p) ∧ a.length ≤ N ∧ (vsQL xᵀ).length ≤ a.length :=
    fun a ha => ⟨(sy.rows a ha).1, (sy.rows a ha).2.trans_le h.dN, by
      rw [(sy.rows a ha).2, sx.len]⟩
  have dmm := vsFMatMul_spec hmm h.p0 h.pN HB HA (by rw [sy.len]; exact h.dN)
  have eprod : (vsQL yᵀ).map (fun a => natList (vsFRowMul p a (vsQL xᵀ) (List.replicate d 0))) =
      (vsQL (x * y)ᵀ).map natList := by
    have := vsQL_mul yᵀ xᵀ
    rw [transpose_mul, ← this]
    simp [vsFMatMulL, List.map_map, Function.comp_def]
  rw [eprod] at dmm
  set vx := vsQE p d E x
  set vy := vsQE p d E y
  have ga (j : ℕ) {v : Val} (hv : [Val.nat p, natList (List.replicate d 0), .nat E,
      .list ((vsQL xᵀ).map natList)][j]? = some v) :
      Det P [.list [vx, vy]] (.get (arg 0) (.nat j)) v _ :=
    Det.get' (Det.arg' (P := P) (vs := [vx, vy]) (rest := []) (j := 0) rfl) (Det.nat j) hv
  have gb := Det.get' (Det.arg' (P := P) (vs := [vx, vy]) (rest := []) (j := 1) rfl) (Det.nat 3)
    (show [Val.nat p, natList (List.replicate d 0), .nat E,
      .list ((vsQL yᵀ).map natList)][3]? = some (.list ((vsQL yᵀ).map natList)) from rfl)
  have dc := Det.call (Det.mk2 (Det.mk3 (ga 0 rfl) (ga 3 rfl) (ga 1 rfl)) gb) dmm
  have dr := Det.mk4 (ga 0 rfl) (ga 1 rfl) (ga 2 rfl) dc
  apply FunDet.intro h0
  refine dr.mono ?_
  have wx := wt_vsQE_le h x
  have wy := wt_vsQE_le h y
  have wxy := wt_vsQE_le h (x * y)
  have wl := wt_list2_le vx vy
  have wlx := wt_vsQL_le h xᵀ
  have wly := wt_vsQL_le h yᵀ
  have wlxy := wt_vsQL_le h (x * y)ᵀ
  have wz := wt_zero_le h
  have wp := wt_nat_le p
  have we := h.eN
  have wctx := wt_list3_le (.nat p) (.list ((vsQL xᵀ).map natList)) (natList (List.replicate d 0))
  have wa2 := wt_list2_le (.list [.nat p, .list ((vsQL xᵀ).map natList),
    natList (List.replicate d 0)]) (.list ((vsQL yᵀ).map natList))
  have e1 : vsQE p d E (x * y) = .list [.nat p, natList (List.replicate d 0), .nat E,
    .list ((vsQL (x * y)ᵀ).map natList)] := rfl
  have w4 := wt_list4_le (.nat p) (natList (List.replicate d 0)) (.nat E)
    (.list ((vsQL (x * y)ᵀ).map natList))
  have q1 := vsQ_le_pow N (k := 5) (by omega)
  have q3 : 1 * (N + 1) ^ 3 ≤ 1 * (N + 1) ^ 5 := vsQ_powle (by omega : 1 ≤ N + 1) (by omega)
  have q2 : 1 * (N + 1) ^ 2 ≤ 1 * (N + 1) ^ 5 := vsQ_powle (by omega : 1 ≤ N + 1) (by omega)
  have := h.pN
  have o3 := vsQ_one_le_pow N 3
  have gx : vx.wt = (vsQE p d E x).wt := rfl
  have gy : vy.wt = (vsQE p d E y).wt := rfl
  rw [← e1]
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at *
  omega

/-- The weight bound of carried matrices. -/
abbrev vsQW (N : ℕ) : ℕ := 100 * (N + 1) ^ 3

set_option maxHeartbeats 1000000 in
/-- **The inverse.** On `vsQE x` it returns `vsQE (x ^ (E + 1))`. -/
theorem vsQInv_spec [NeZero p] {P : Program} {b : ℕ} (hb : P.HasAt b (vsQGLFuns b))
    (h : VsQSz p d E N) (x : Matrix (Fin d) (Fin d) (ZMod p)) :
    FunDet P (b + 2) (vsQE p d E x) (vsQE p d E (x ^ (E + 1))) (10 ^ 8 * (N + 1) ^ 6) := by
  have h1 : P.funs[b + 1]? = some (vsQMul3F b) := hb.get (j := 1) (by rw [vsQGLFuns_length]; omega)
  have h2 : P.funs[b + 2]? = some (vsQInvF (b + 3)) :=
    hb.get (j := 2) (by rw [vsQGLFuns_length]; omega)
  have h3 : P.funs[b + 3]? = some (vsQPowF (b + 3) (b + 1)) :=
    hb.get (j := 3) (by rw [vsQGLFuns_length]; omega)
  have hm3 : ∀ u v : Matrix (Fin d) (Fin d) (ZMod p), FunDet P (b + 1)
      (.list [.nat 0, vsQE p d E u, vsQE p d E v]) (vsQE p d E (u * v)) (7 * 10 ^ 6 * (N + 1) ^ 5) := by
    intro u v
    apply FunDet.intro h1
    have d1 := Det.arg' (P := P) (vs := [.nat 0, vsQE p d E u, vsQE p d E v]) (rest := []) (j := 1) rfl
    have d2 := Det.arg' (P := P) (vs := [.nat 0, vsQE p d E u, vsQE p d E v]) (rest := []) (j := 2) rfl
    refine (Det.call (Det.mk2 d1 d2) (vsQMul_spec hb h u v)).mono ?_
    have wu := wt_vsQE_le h u
    have wv := wt_vsQE_le h v
    have wuv := wt_vsQE_le h (u * v)
    have w3 := wt_list3_le (.nat 0) (vsQE p d E u) (vsQE p d E v)
    have w2 := wt_list2_le (vsQE p d E u) (vsQE p d E v)
    have q3 : 1 * (N + 1) ^ 3 ≤ 1 * (N + 1) ^ 5 := vsQ_powle (by omega : 1 ≤ N + 1) (by omega)
    have w0 : (Val.nat 0).wt = 2 := rfl
    have o3 := vsQ_one_le_pow N 3
    omega
  have hp := vsQPow_spec h3 (vsQE p d E) (.nat 0) (fun u => wt_vsQE_le h u) hm3 E x x
  apply FunDet.intro h2
  have dv := Det.var' (P := P) (env := [vsQE p d E x]) (i := 0) (v := vsQE p d E x) rfl
  have de := Det.get' dv (Det.nat 2) (show [Val.nat p, natList (List.replicate d 0), .nat E,
      .list ((vsQL xᵀ).map natList)][2]? = some (.nat E) from rfl)
  have dc := Det.call (Det.mk4 (Det.nat 0) dv de dv) hp
  rw [← pow_succ] at dc
  refine dc.mono ?_
  have wx := wt_vsQE_le h x
  have wo := wt_vsQE_le h (x ^ (E + 1))
  have w4 := wt_list4_le (.nat 0) (vsQE p d E x) (.nat E) (vsQE p d E x)
  have hbits : E.bits.length ≤ N := by
    have := h.eN; rw [wt_nat, linLenBits] at this; omega
  have hE := h.eN
  have w0 : (Val.nat 0).wt = 2 := rfl
  have c1 : (E.bits.length + 1) * vsQPowUnit (Val.nat 0).wt (100 * (N + 1) ^ 3)
      (7 * 10 ^ 6 * (N + 1) ^ 5) E.bits.length ≤ (N + 1) * (3 * 10 ^ 7 * (N + 1) ^ 5) := by
    apply Nat.mul_le_mul (by omega)
    unfold vsQPowUnit
    have q3 : 1 * (N + 1) ^ 3 ≤ 1 * (N + 1) ^ 5 := vsQ_powle (by omega : 1 ≤ N + 1) (by omega)
    have q1 := vsQ_le_pow N (k := 5) (by omega)
    omega
  have e6 : (N + 1) * (3 * 10 ^ 7 * (N + 1) ^ 5) = 3 * 10 ^ 7 * (N + 1) ^ 6 := by ring
  have q3 : 1 * (N + 1) ^ 3 ≤ 1 * (N + 1) ^ 6 := vsQ_powle (by omega : 1 ≤ N + 1) (by omega)
  have q1 := vsQ_le_pow N (k := 6) (by omega)
  omega

end GI.Impl
