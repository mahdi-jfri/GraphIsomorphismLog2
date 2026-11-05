module

public import Workspace.Impl.ColTab

@[expose] public section

/-!
# The per-level functions of the column program

For each stored level `k`, the column program computes two interval values of the child
hierarchy: the lower piece (`colLowF`) and the upper piece (`colUpF`). Both run on `[ctx, k]`
with the context `colLevCtx`:

`[hv, r0, ol, oc, cf, rl, dv, [0..m-1], m, n, [0..n-1]]`,

where `hv` is the stored hierarchy value, `r0` the positions of row `0`, `ol` the orbit labels of
`N` on the row coordinates, `oc = ol ∘ cf`, `cf` the column coordinate of each position, `rl` the
row labels and `dv` the domain indicator. The values are those of `Workspace/Impl/ColSpec.lean`
(`colLowVal`, `colUpVal`); `colChild_hierVal` says what they mean.

Cost: at most `colLevK (X + 1)^4`, where `X ≥ (n + 2)^3` bounds the weight of `hv` and the
number of levels.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

/-! ### The functions -/

/-- The context of the per-level functions. -/
def colLevCtx (hv r0v olv ocv cfv rlv dvv : Val) (m n : ℕ) : List Val :=
  [hv, r0v, olv, ocv, cfv, rlv, dvv, natList (List.range m), .nat m, .nat n,
    natList (List.range n)]

/-- Entry `j` of the stored interval `k` (`k` is entry `1` of the argument). -/
def colHvE (j : ℕ) : Expr := .get (.get (colC 0) (arg 1)) (.nat j)

/-- The labels of the stored level of the row-`0` points: `labs k (r0 c)`. -/
def colBkE (mp : ℕ) : Expr := .call mp (mk2 (mk3 (.var 1) (colC 1) (.nat 0)) (colC 7))

/-- `m + 1`. -/
def colM1E : Expr := .arith .add (colC 8) (.nat 1)

/-- `n + 1`. -/
def colN1E : Expr := .arith .add (colC 9) (.nat 1)

/-- The keys `colAk + m + 1` of the level below. -/
def colAkE (mp : ℕ) : Expr :=
  .ite (arg 1)
    (.call mp (mk2 (mk3 (.get (.get (colC 0) (.arith .sub (arg 1) (.nat 1))) (.nat 0)) (colC 1)
      colM1E) (colC 7)))
    (.call mp (mk2 (mk3 (colC 7) (colC 7) colM1E) (colC 7)))

/-- `min cap r` as `cap - (cap - r)`, with `r` in the environment at `i`. -/
def colMinCapE (i : ℕ) : Expr := .arith .sub (colHvE 2) (.arith .sub (colHvE 2) (.var i))

/-- **The lower piece of level `k`.** -/
def colLowF (mp me mk cl : ℕ) : Expr :=
  .letE (colHvE 0)
  (.letE (colBkE mp)
  (.letE (colAkE mp)
  (.letE (.call me (mk2 (mk2 (.var 2) (colC 2)) (colC 7)))
  (.letE (.length (.get (.call cl (mk2 (.var 3) (.var 4))) (.nat 1)))
  (.letE (.call mk (mk2 (mk4 (colC 5) (.var 1) (colC 3) colN1E) (colC 10)))
  (mk4 (.get (.call cl (mk2 (.var 6) (colC 6))) (.nat 2)) (.var 5) (colMinCapE 5)
    (colHvE 3)))))))

/-- **The upper piece of level `k`.** -/
def colUpF (mp me mmin cl : ℕ) : Expr :=
  .letE (colHvE 0)
  (.letE (colBkE mp)
  (.letE (colAkE mp)
  (.letE (.call me (mk2 (mk2 (.var 2) (colC 2)) (colC 7)))
  (.letE (.call me (mk2 (mk2 (.var 2) (.var 2)) (colC 7)))
  (.letE (.arith .div (.length (.get (.call cl (mk2 (.var 3) (.var 5))) (.nat 1)))
      (.length (.get (.call cl (mk2 (.var 3) (.var 4))) (.nat 1))))
  (.letE (.call mmin (mk2 (mk2 (colC 2) (.var 2)) (colC 7)))
  (.letE (.call mp (mk2 (mk3 (.var 7) (colC 4) colN1E) (colC 10)))
  (mk4 (.get (.call cl (mk2 (.var 8) (colC 6))) (.nat 2)) (.var 6) (colMinCapE 6)
    (colHvE 3)))))))))

/-! ### The values -/

/-- The value of the lower piece of level `k`. -/
def colLowVal {n m : ℕ} (labs : ℕ → Fin n → ℕ) (r0 : Fin m → Fin n) (ol : Fin m → ℕ)
    (cf : Fin n → Fin m) (rl dv : Fin n → ℕ) (h0 : 0 < m) (cap orig : ℕ) (k : ℕ) : Val :=
  colIV (colLowLab labs ol cf rl dv k) (colLowRat labs r0 ol h0 k)
    (min cap (colLowRat labs r0 ol h0 k)) orig

/-- The value of the upper piece of level `k`. -/
def colUpVal {n m : ℕ} (labs : ℕ → Fin n → ℕ) (r0 : Fin m → Fin n) (ol : Fin m → ℕ)
    (cf : Fin n → Fin m) (dv : Fin n → ℕ) (h0 : 0 < m) (cap orig : ℕ) (k : ℕ) : Val :=
  colIV (colUpLab labs r0 ol cf dv k) (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k)
    (min cap (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k)) orig

/-- The cost constant of the per-level functions. -/
def colLevK : ℕ := 10 ^ 17

/-! ### The specifications -/

section Spec

variable {P : Program} {n m len X : ℕ} (labs : ℕ → Fin n → ℕ) (rats caps origs : Fin len → ℕ)
  (r0 : Fin m → Fin n) (ol : Fin m → ℕ) (cf : Fin n → Fin m) (rl dv : Fin n → ℕ) (h0 : 0 < m)

/-- The context, as values. -/
def colLevC : List Val :=
  colLevCtx (colHV (fun k : Fin len => labs k) rats caps origs) (encFun fun c => (r0 c : ℕ))
    (encFun ol) (encFun fun i => ol (cf i)) (encFun fun i => (cf i : ℕ)) (encFun rl) (encFun dv) m n

/-- The bounds that the per-level functions need. -/
structure ColLevB : Prop where
  cube : (n + 2) ^ 3 ≤ X
  m_le : m ≤ n
  len_le : len ≤ X
  labs_le : ∀ k i, labs k i ≤ n
  ol_le : ∀ c, ol c ≤ n
  rl_le : ∀ i, rl i ≤ n
  dv_le : ∀ i, dv i ≤ 1
  hv_le : (colHV (fun k : Fin len => labs k) rats caps origs).wt ≤ X
  caps_le : ∀ k, caps k ≤ X

variable {labs rats caps origs r0 ol cf rl dv}

theorem ColLevB.n_le (hB : ColLevB (X := X) labs rats caps origs ol rl dv) : n ≤ X := by
  have := hB.cube
  have : n + 2 ≤ (n + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  omega

theorem ColLevB.one_le (hB : ColLevB (X := X) labs rats caps origs ol rl dv) : 8 ≤ X := by
  have h1 : 2 ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have := hB.cube
  norm_num at h1
  omega

theorem ColLevB.two_n (hB : ColLevB (X := X) labs rats caps origs ol rl dv) :
    2 * n + 2 ≤ X := by
  have e : (n + 2) ^ 3 = (n + 2) * ((n + 2) * (n + 2)) := by ring
  have := hB.cube
  have : 2 * n + 2 ≤ (n + 2) * ((n + 2) * (n + 2)) := by nlinarith
  omega

theorem ColLevB.key_le (hB : ColLevB (X := X) labs rats caps origs ol rl dv) (k : ℕ)
    (i : Fin n) :
    colKeyv rl (labs k) (fun i => ol (cf i)) (n + 1) i ≤ X := by
  have h1 := hB.rl_le i
  have h2 := hB.labs_le k i
  have h3 := hB.ol_le (cf i)
  have hc := hB.cube
  show (rl i * (n + 1) + labs k i) * (n + 1) + ol (cf i) + (n + 1) ≤ X
  have a1 : rl i * (n + 1) + labs k i ≤ n * (n + 1) + n :=
    Nat.add_le_add (Nat.mul_le_mul_right _ h1) h2
  have a2 : (rl i * (n + 1) + labs k i) * (n + 1) ≤ (n * (n + 1) + n) * (n + 1) :=
    Nat.mul_le_mul_right _ a1
  have a3 : (n * (n + 1) + n) * (n + 1) + n + (n + 1) ≤ (n + 2) ^ 3 := by ring_nf; omega
  generalize (n * (n + 1) + n) * (n + 1) = A at a2 a3
  generalize (rl i * (n + 1) + labs k i) * (n + 1) = B at a2 ⊢
  omega

/-- The weight of the context. -/
theorem ColLevB.ctx_wt (hB : ColLevB (X := X) labs rats caps origs ol rl dv) :
    (Val.list (colLevC labs rats caps origs r0 ol cf rl dv)).wt ≤ 100 * (X + 1) ^ 2 := by
  have hn := hB.n_le
  have hm := hB.m_le
  have hX := colSq_ge X
  have h8 := hB.one_le
  have w1 := hB.hv_le
  have w2 := colWt_fin_le r0 (p := n) (show n ≤ X by omega) (show m ≤ X by omega)
  have w3 := wt_encFun_le' ol (B := X) (fun c => (hB.ol_le c).trans hn) (by omega)
  have w4 := wt_encFun_le' (fun i => ol (cf i)) (B := X) (fun c => (hB.ol_le _).trans hn) hn
  have w5 := colWt_fin_le cf (p := m) (show m ≤ X by omega) hn
  have w6 := wt_encFun_le' rl (B := X) (fun c => (hB.rl_le c).trans hn) hn
  have w7 := wt_encFun_le' dv (B := X) (fun c => (hB.dv_le c).trans (by omega)) hn
  have w8 := wt_range_le m
  have w9 := wt_range_le n
  have e8 : (m + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have e9 : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have wm := wt_nat_le m
  have wn := wt_nat_le n
  have h := wt_list_le (colLevC labs rats caps origs r0 ol cf rl dv)
  simp only [colLevC, colLevCtx, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil] at h ⊢
  omega

end Spec

/-! ### Reading the context -/

section Access

variable {P : Program} {n m len X : ℕ} {labs : ℕ → Fin n → ℕ} {rats caps origs : Fin len → ℕ}
  {r0 : Fin m → Fin n} {ol : Fin m → ℕ} {cf : Fin n → Fin m} {rl dv : Fin n → ℕ}

/-- The argument of a per-level function. -/
abbrev colLevA (labs : ℕ → Fin n → ℕ) (rats caps origs : Fin len → ℕ) (r0 : Fin m → Fin n)
    (ol : Fin m → ℕ) (cf : Fin n → Fin m) (rl dv : Fin n → ℕ) (k : ℕ) : Val :=
  .list [.list (colLevC labs rats caps origs r0 ol cf rl dv), .nat k]

theorem colLevA_wt (hB : ColLevB (X := X) labs rats caps origs ol rl dv) {k : ℕ} (hk : k ≤ X) :
    (colLevA labs rats caps origs r0 ol cf rl dv k).wt ≤ 300 * (X + 1) ^ 2 := by
  have h1 := hB.ctx_wt (r0 := r0) (cf := cf)
  have h2 := wt_list2_le (.list (colLevC labs rats caps origs r0 ol cf rl dv)) (.nat k)
  have h3 := wt_nat_le k
  have := colSq_ge X
  have : (colLevA labs rats caps origs r0 ol cf rl dv k).wt =
    (Val.list [.list (colLevC labs rats caps origs r0 ol cf rl dv), .nat k]).wt := rfl
  omega

theorem colLev_ctx {rest : List Val} {k j : ℕ} {v : Val}
    (h : (colLevC labs rats caps origs r0 ol cf rl dv)[j]? = some v) (hj : j ≤ 10) :
    Det P (colLevA labs rats caps origs r0 ol cf rl dv k :: rest) (colC j) v
      (4 * (colLevA labs rats caps origs r0 ol cf rl dv k).wt + 20) :=
  (colC_det' (more := [.nat k]) h).mono (by
    have : (colLevA labs rats caps origs r0 ol cf rl dv k).wt =
      (Val.list (.list (colLevC labs rats caps origs r0 ol cf rl dv) :: [.nat k])).wt := rfl
    omega)

theorem colLev_k {rest : List Val} {k : ℕ} :
    Det P (colLevA labs rats caps origs r0 ol cf rl dv k :: rest) (arg 1) (.nat k)
      (2 * (colLevA labs rats caps origs r0 ol cf rl dv k).wt + 6) :=
  Det.arg' (vs := [.list (colLevC labs rats caps origs r0 ol cf rl dv), .nat k]) rfl

theorem colLev_hv {rest : List Val} (k : Fin len) (j : ℕ) {v : Val} (hj : j ≤ 3)
    (hv : [encFun (labs k), .nat (rats k), .nat (caps k), .nat (origs k)][j]? = some v) :
    Det P (colLevA labs rats caps origs r0 ol cf rl dv k :: rest) (colHvE j) v
      (20 * (colLevA labs rats caps origs r0 ol cf rl dv k).wt + 110) := by
  have d0 := colLev_ctx (P := P) (labs := labs) (rats := rats) (caps := caps) (origs := origs)
    (r0 := r0) (ol := ol) (cf := cf) (rl := rl) (dv := dv) (rest := rest) (k := k) (j := 0)
    (v := colHV (fun k : Fin len => labs k) rats caps origs) rfl (by omega)
  have d1 := colGet d0 colLev_k (colHV_get (fun k : Fin len => labs k) rats caps origs k)
  exact (colGet d1 (Det.nat j) hv).mono (by omega)

end Access

/-! ### The lower and upper pieces -/

section Pieces

variable {P : Program} {n m len X : ℕ} {labs : ℕ → Fin n → ℕ} {rats caps origs : Fin len → ℕ}
  {r0 : Fin m → Fin n} {ol : Fin m → ℕ} {cf : Fin n → Fin m} {rl dv : Fin n → ℕ}

theorem colPow_facts (X : ℕ) : (X + 1) ^ 2 ≤ (X + 1) ^ 3 ∧ (X + 1) ^ 3 ≤ (X + 1) ^ 4 ∧
    X + 1 ≤ (X + 1) ^ 2 :=
  ⟨Nat.pow_le_pow_right (by omega) (by omega), Nat.pow_le_pow_right (by omega) (by omega),
    colSq_ge X⟩

/-- The keys `colAk + m + 1` of the level below. -/
theorem colAk_det {mp fp : ℕ} (hmp : P.HasAt mp (mapFuns mp fp))
    (hfp : P.funs[fp]? = some colPickF) (hB : ColLevB (X := X) labs rats caps origs ol rl dv)
    (k : Fin len) (rest : List Val) :
    Det P (colLevA labs rats caps origs r0 ol cf rl dv k :: rest) (colAkE mp)
      (encFun fun c => colAk labs r0 k c + (m + 1)) (10 ^ 8 * (X + 1) ^ 3) := by
  have hW := colLevA_wt (r0 := r0) (cf := cf) hB (k := k)
    (by have := hB.len_le; have := k.2; omega)
  have hn := hB.n_le
  have hm := hB.m_le
  have h8 := hB.one_le
  obtain ⟨p23, p34, p12⟩ := colPow_facts X
  have h2n := hB.two_n
  have hlab : ∀ j i, labs j i + (m + 1) ≤ X := fun j i => by
    have := hB.labs_le j i
    omega
  generalize hA : colLevA labs rats caps origs r0 ol cf rl dv k = A at hW
  have dk : Det P (A :: rest) (arg 1) (.nat k) (2 * A.wt + 6) := hA ▸ colLev_k
  have dC : ∀ j v, (colLevC labs rats caps origs r0 ol cf rl dv)[j]? = some v → j ≤ 10 →
      Det P (A :: rest) (colC j) v (4 * A.wt + 20) := fun j v h hj => hA ▸ colLev_ctx h hj
  have d8 := dC 8 (.nat m) rfl (by omega)
  have dm1 := Det.arith' (op := .add) (z := m + 1) d8 (Det.nat 1) rfl
  have d7 := dC 7 (natList (List.range m)) rfl (by omega)
  have d1 := dC 1 (encFun fun c => (r0 c : ℕ)) rfl (by omega)
  have dH := dC 0 (colHV (fun k : Fin len => labs k) rats caps origs) rfl (by omega)
  have dk1 := Det.arith' (op := .sub) (z := k - 1) dk (Det.nat 1) rfl
  have hk1 : (k : ℕ) - 1 < len := by have := k.2; omega
  have dHk := colGet dH dk1 (colHV_get (fun k : Fin len => labs k) rats caps origs ⟨k - 1, hk1⟩)
  have dL := colGet dHk (Det.nat 0) (v := encFun (labs ((k : ℕ) - 1))) rfl
  have tPos := colCall (colMk2 (colMk3 dL d1 dm1) d7)
    (colTabPick_det hmp hfp (labs ((k : ℕ) - 1)) r0 (m + 1) (X := X) (fun j => hlab _ j)
      (by omega) hn (by omega))
  have d7' := d7
  rw [natList_range_eq] at d7'
  have tZero := colCall (colMk2 (colMk3 d7' d7' dm1) d7)
    (colTabPick_det hmp hfp (fun c : Fin m => (c : ℕ)) (fun c => c) (m + 1) (X := X)
      (fun j => by show (j : ℕ) + (m + 1) ≤ X; have := j.2; omega) (by omega) (by omega)
      (by omega))
  have w1 := tPos.wt_lt
  have w2 := tZero.wt_lt
  have hval0 : (k : ℕ) = 0 → (encFun fun i : Fin m => (i : ℕ) + (m + 1)) =
      encFun fun c => colAk labs r0 k c + (m + 1) := fun h => by
    unfold colAk; simp only [h, if_true]
  have hval1 : (k : ℕ) ≠ 0 → (encFun fun i => labs ((k : ℕ) - 1) (r0 i) + (m + 1)) =
      encFun fun c => colAk labs r0 k c + (m + 1) := fun h => by
    unfold colAk; simp only [h, if_false]
  by_cases hk0 : (k : ℕ) = 0
  · have d := Det.ite_zero (t := .call mp (mk2 (mk3 (.get (.get (colC 0) (.arith .sub (arg 1)
      (.nat 1))) (.nat 0)) (colC 1) colM1E) (colC 7))) (hk0 ▸ dk) tZero
    have w3 := tZero.wt_lt
    rw [hval0 hk0] at d w3
    refine d.mono ?_
    omega
  · have d := Det.ite_pos (e := .call mp (mk2 (mk3 (colC 7) (colC 7) colM1E) (colC 7))) dk
      hk0 tPos
    have w3 := tPos.wt_lt
    rw [hval1 hk0] at d w3
    refine d.mono ?_
    have := k.2
    have := hB.len_le
    omega

/-- The shared bounds of the per-level proofs. -/
theorem colLev_pre (hB : ColLevB (X := X) labs rats caps origs ol rl dv) (k : Fin len) :
    (colLevA labs rats caps origs r0 ol cf rl dv k).wt ≤ 300 * (X + 1) ^ 2 ∧ n ≤ X ∧ m ≤ n ∧
      2 * n + 2 ≤ X ∧ 8 ≤ X ∧ (k : ℕ) < len ∧ len ≤ X :=
  ⟨colLevA_wt hB (by have := hB.len_le; have := k.2; omega), hB.n_le, hB.m_le, hB.two_n,
    hB.one_le, k.2, hB.len_le⟩

/-- **The lower piece of level `k`.** -/
theorem colLow_det {f mp fp me fe mk fk cl : ℕ} (hf : P.funs[f]? = some (colLowF mp me mk cl))
    (hmp : P.HasAt mp (mapFuns mp fp)) (hfp : P.funs[fp]? = some colPickF)
    (hme : P.HasAt me (mapFuns me fe)) (hfe : P.funs[fe]? = some colEqF)
    (hmk : P.HasAt mk (mapFuns mk fk)) (hfk : P.funs[fk]? = some colKeyF)
    (hcl : P.HasAt cl (clsFuns cl)) (h0 : 0 < m)
    (hB : ColLevB (X := X) labs rats caps origs ol rl dv) (k : Fin len) :
    FunDet P f (colLevA labs rats caps origs r0 ol cf rl dv k)
      (colLowVal labs r0 ol cf rl dv h0 (caps k) (origs k) k) (colLevK * (X + 1) ^ 4) := by
  obtain ⟨hW, hn, hm, h2n, h8, hk, hlen⟩ := colLev_pre (r0 := r0) (cf := cf) hB k
  obtain ⟨p23, p34, p12⟩ := colPow_facts X
  have dAk := colAk_det (r0 := r0) (cf := cf) hmp hfp hB k
  generalize hA : colLevA labs rats caps origs r0 ol cf rl dv k = A at hW
  have dk : ∀ rest, Det P (A :: rest) (arg 1) (.nat k) (2 * A.wt + 6) := fun _ => hA ▸ colLev_k
  have dC : ∀ rest j v, (colLevC labs rats caps origs r0 ol cf rl dv)[j]? = some v → j ≤ 10 →
      Det P (A :: rest) (colC j) v (4 * A.wt + 20) := fun _ j v h hj => hA ▸ colLev_ctx h hj
  have dHv : ∀ rest j v, j ≤ 3 →
      [encFun (labs k), .nat (rats k), .nat (caps k), .nat (origs k)][j]? = some v →
      Det P (A :: rest) (colHvE j) v (20 * A.wt + 110) := fun _ j v hj h => hA ▸ colLev_hv k j hj h
  -- step 1: the labels of level `k`
  have s1 := dHv [] 0 (encFun (labs k)) (by omega) rfl
  -- step 2: `bk`
  have v1 := colVar (P := P) (env := [A, encFun (labs k)]) (i := 1) rfl (le_refl _)
  have s2 := colCall (colMk2 (colMk3 v1 (dC _ 1 (encFun fun c => (r0 c : ℕ)) rfl (by omega))
      (Det.nat 0)) (dC _ 7 (natList (List.range m)) rfl (by omega)))
    (colTabPick_det hmp hfp (labs k) r0 0 (X := X) (fun j => by have := hB.labs_le k j; omega)
      (by omega) hn (by omega))
  have ebk : (encFun fun i => labs k (r0 i) + 0) = encFun (colBk labs r0 k) := rfl
  rw [ebk] at s2
  -- step 3: `ak`
  have s3 := hA ▸ dAk [encFun (labs k), encFun (colBk labs r0 k)]
  -- step 4: the indicator of the fiber of `0` under `(bk, ol)`
  have hbk : ∀ c, colBk labs r0 k c ≤ X := fun c => by have := hB.labs_le k (r0 c); unfold colBk; omega
  have hol : ∀ c, ol c ≤ X := fun c => by have := hB.ol_le c; omega
  have s4 := colCall (colMk2 (colMk2
      (colVar (P := P) (env := [A, encFun (labs k), encFun (colBk labs r0 k),
        encFun fun c => colAk labs r0 k c + (m + 1)]) (i := 2) rfl (le_refl _))
      (dC _ 2 (encFun ol) rfl (by omega))) (dC _ 7 (natList (List.range m)) rfl (by omega)))
    (colTabEq_det hme hfe (colBk labs r0 k) ol h0 hbk hol (by omega))
  -- step 5: the lower ratio
  have hak : ∀ c, colAk labs r0 k c + (m + 1) ≤ X := fun c => by
    unfold colAk; split_ifs
    · have := c.2; omega
    · have := hB.labs_le ((k : ℕ) - 1) (r0 c); omega
  have s5 := colCount_det hcl (fun c => colAk labs r0 k c + (m + 1)) (colEqv (colBk labs r0 k) ol h0)
    (colMk2 (colVar (P := P) (env := [A, encFun (labs k), encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)), encFun (colEqv (colBk labs r0 k) ol h0)])
        (i := 3) rfl (le_refl _))
      (colVar (P := P) (env := [A, encFun (labs k), encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)), encFun (colEqv (colBk labs r0 k) ol h0)])
        (i := 4) rfl (le_refl _))) hak (colEqv_le _ _ h0) (by omega)
  -- step 6: the keys
  have dn1 := Det.arith' (op := .add) (z := n + 1) (dC [encFun (labs k), encFun (colBk labs r0 k),
    encFun (fun c => colAk labs r0 k c + (m + 1)), encFun (colEqv (colBk labs r0 k) ol h0),
    .nat (colLowRat labs r0 ol h0 k)] 9 (.nat n) rfl (by omega)) (Det.nat 1) rfl
  have s6 := colCall (colMk2 (colMk4 (dC _ 5 (encFun rl) rfl (by omega))
      (colVar (P := P) (env := [A, encFun (labs k), encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)), encFun (colEqv (colBk labs r0 k) ol h0),
        .nat (colLowRat labs r0 ol h0 k)]) (i := 1) rfl (le_refl _))
      (dC _ 3 (encFun fun i => ol (cf i)) rfl (by omega)) dn1)
      (dC _ 10 (natList (List.range n)) rfl (by omega)))
    (colTabKey_det hmk hfk rl (labs k) (fun i => ol (cf i)) (N1 := n + 1) (X := X) (by omega)
      (fun i => by have := hB.rl_le i; omega) (fun i => by have := hB.labs_le k i; omega)
      (fun i => by show ol (cf i) ≤ X; have := hB.ol_le (cf i); omega) (by omega)
      (fun i => hB.key_le k i) hn)
  -- step 7: the value
  have s7a := colLabs_det hcl (colKeyv rl (labs k) (fun i => ol (cf i)) (n + 1)) dv
    (colMk2 (colVar (P := P) (env := [A, encFun (labs k), encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)), encFun (colEqv (colBk labs r0 k) ol h0),
        .nat (colLowRat labs r0 ol h0 k), encFun (colKeyv rl (labs k) (fun i => ol (cf i)) (n + 1))])
        (i := 6) rfl (le_refl _))
      (dC [encFun (labs k), encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)), encFun (colEqv (colBk labs r0 k) ol h0),
        .nat (colLowRat labs r0 ol h0 k), encFun (colKeyv rl (labs k) (fun i => ol (cf i)) (n + 1))] 6 (encFun dv) rfl (by omega))) (fun i => hB.key_le k i) hB.dv_le hn
  have dlr := colVar (P := P) (env := [A, encFun (labs k), encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)), encFun (colEqv (colBk labs r0 k) ol h0),
        .nat (colLowRat labs r0 ol h0 k), encFun (colKeyv rl (labs k) (fun i => ol (cf i)) (n + 1))])
    (i := 5) (v := .nat (colLowRat labs r0 ol h0 k)) rfl (le_refl _)
  have dcap := dHv [encFun (labs k), encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)), encFun (colEqv (colBk labs r0 k) ol h0),
        .nat (colLowRat labs r0 ol h0 k), encFun (colKeyv rl (labs k) (fun i => ol (cf i)) (n + 1))] 2 (.nat (caps k)) (by omega) rfl
  have s7c := Det.arith' (op := .sub) (z := min (caps k) (colLowRat labs r0 ol h0 k)) dcap
    (Det.arith' (op := .sub) (z := caps k - colLowRat labs r0 ol h0 k) dcap dlr rfl)
    (by simp only [GI.Machine.BinOp.eval]; omega)
  have s7 := colMk4 s7a dlr s7c (dHv [encFun (labs k), encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)), encFun (colEqv (colBk labs r0 k) ol h0),
        .nat (colLowRat labs r0 ol h0 k), encFun (colKeyv rl (labs k) (fun i => ol (cf i)) (n + 1))] 3 (.nat (origs k)) (by omega) rfl)
  have d := colLet s1 (colLet s2 (colLet s3 (colLet s4 (colLet s5 (colLet s6 s7)))))
  refine FunDet.intro hf ?_
  refine d.mono ?_
  have := s1.wt_lt
  have := s2.wt_lt
  have := s3.wt_lt
  have := s4.wt_lt
  have := s5.wt_lt
  have := s6.wt_lt
  have := s7a.wt_lt
  have := hB.caps_le k
  have hlr : colLowRat labs r0 ol h0 k ≤ m := (Cls.repsOf_length_le _ _).trans (by simp)
  have := wt_nat_le (colLowRat labs r0 ol h0 k)
  simp only [colLevK]
  omega

/-- **The upper piece of level `k`.** -/
theorem colUp_det {f mp fp me fe mmin fmin it g cl : ℕ}
    (hf : P.funs[f]? = some (colUpF mp me mmin cl))
    (hmp : P.HasAt mp (mapFuns mp fp)) (hfp : P.funs[fp]? = some colPickF)
    (hme : P.HasAt me (mapFuns me fe)) (hfe : P.funs[fe]? = some colEqF)
    (hmmin : P.HasAt mmin (mapFuns mmin fmin)) (hfmin : P.funs[fmin]? = some (colMinF it))
    (hit : P.HasAt it (iterFuns it g)) (hg : P.funs[g]? = some colMinStepF)
    (hcl : P.HasAt cl (clsFuns cl)) (h0 : 0 < m)
    (hB : ColLevB (X := X) labs rats caps origs ol rl dv) (k : Fin len) :
    FunDet P f (colLevA labs rats caps origs r0 ol cf rl dv k)
      (colUpVal labs r0 ol cf dv h0 (caps k) (origs k) k) (colLevK * (X + 1) ^ 4) := by
  obtain ⟨hW, hn, hm, h2n, h8, hk, hlen⟩ := colLev_pre (r0 := r0) (cf := cf) hB k
  obtain ⟨p23, p34, p12⟩ := colPow_facts X
  have dAk := colAk_det (r0 := r0) (cf := cf) hmp hfp hB k
  generalize hA : colLevA labs rats caps origs r0 ol cf rl dv k = A at hW
  have dC : ∀ rest j v, (colLevC labs rats caps origs r0 ol cf rl dv)[j]? = some v → j ≤ 10 →
      Det P (A :: rest) (colC j) v (4 * A.wt + 20) := fun _ j v h hj => hA ▸ colLev_ctx h hj
  have dHv : ∀ rest j v, j ≤ 3 →
      [encFun (labs k), .nat (rats k), .nat (caps k), .nat (origs k)][j]? = some v →
      Det P (A :: rest) (colHvE j) v (20 * A.wt + 110) := fun _ j v hj h => hA ▸ colLev_hv k j hj h
  have hbk : ∀ c, colBk labs r0 k c ≤ X := fun c => by
    have := hB.labs_le k (r0 c); unfold colBk; omega
  have hol : ∀ c, ol c ≤ X := fun c => by have := hB.ol_le c; omega
  have hak : ∀ c, colAk labs r0 k c + (m + 1) ≤ X := fun c => by
    unfold colAk; split_ifs
    · have := c.2; omega
    · have := hB.labs_le ((k : ℕ) - 1) (r0 c); omega
  -- steps 1 to 3 as for the lower piece
  have s1 := dHv [] 0 (encFun (labs k)) (by omega) rfl
  have s2 := colCall (colMk2 (colMk3 (colVar (P := P) (env := [A,
        encFun (labs k)]) (i := 1) rfl (le_refl _))
      (dC _ 1 (encFun fun c => (r0 c : ℕ)) rfl (by omega))
      (Det.nat 0)) (dC _ 7 (natList (List.range m)) rfl (by omega)))
    (colTabPick_det hmp hfp (labs k) r0 0 (X := X) (fun j => by have := hB.labs_le k j; omega)
      (by omega) hn (by omega))
  have ebk : (encFun fun i => labs k (r0 i) + 0) = encFun (colBk labs r0 k) := rfl
  rw [ebk] at s2
  have s3 := hA ▸ dAk [encFun (labs k),
        encFun (colBk labs r0 k)]
  -- step 4: the fiber of `0` under `(bk, ol)`; step 5: under `bk`
  have s4 := colCall (colMk2 (colMk2
      (colVar (P := P) (env := [A,
        encFun (labs k),
        encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1))]) (i := 2) rfl (le_refl _))
      (dC _ 2 (encFun ol) rfl (by omega))) (dC _ 7 (natList (List.range m)) rfl (by omega)))
    (colTabEq_det hme hfe (colBk labs r0 k) ol h0 hbk hol (by omega))
  have s5 := colCall (colMk2 (colMk2
      (colVar (P := P) (env := [A,
        encFun (labs k),
        encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)),
        encFun (colEqv (colBk labs r0 k) ol h0)]) (i := 2) rfl (le_refl _))
      (colVar (P := P) (env := [A,
        encFun (labs k),
        encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)),
        encFun (colEqv (colBk labs r0 k) ol h0)]) (i := 2) rfl (le_refl _)))
      (dC _ 7 (natList (List.range m)) rfl (by omega)))
    (colTabEq_det hme hfe (colBk labs r0 k) (colBk labs r0 k) h0 hbk hbk (by omega))
  -- step 6: the upper ratio
  have s6a := colCount_det hcl (fun c => colAk labs r0 k c + (m + 1))
    (colEqv (colBk labs r0 k) (colBk labs r0 k) h0)
    (colMk2 (colVar (P := P) (env := [A,
        encFun (labs k),
        encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)),
        encFun (colEqv (colBk labs r0 k) ol h0),
        encFun (colEqv (colBk labs r0 k) (colBk labs r0 k) h0)]) (i := 3) rfl (le_refl _))
      (colVar (P := P) (env := [A,
        encFun (labs k),
        encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)),
        encFun (colEqv (colBk labs r0 k) ol h0),
        encFun (colEqv (colBk labs r0 k) (colBk labs r0 k) h0)]) (i := 5) rfl (le_refl _))) hak (colEqv_le _ _ h0) (by omega)
  have s6b := colCount_det hcl (fun c => colAk labs r0 k c + (m + 1))
    (colEqv (colBk labs r0 k) ol h0)
    (colMk2 (colVar (P := P) (env := [A,
        encFun (labs k),
        encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)),
        encFun (colEqv (colBk labs r0 k) ol h0),
        encFun (colEqv (colBk labs r0 k) (colBk labs r0 k) h0)]) (i := 3) rfl (le_refl _))
      (colVar (P := P) (env := [A,
        encFun (labs k),
        encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)),
        encFun (colEqv (colBk labs r0 k) ol h0),
        encFun (colEqv (colBk labs r0 k) (colBk labs r0 k) h0)]) (i := 4) rfl (le_refl _))) hak (colEqv_le _ _ h0) (by omega)
  have hr : colRat labs r0 h0 k ≤ m := (Cls.repsOf_length_le _ _).trans (by simp)
  have s6 := Det.arith' (op := .div) (z := colRat labs r0 h0 k / colLowRat labs r0 ol h0 k)
    s6a s6b rfl
  -- step 7: the least orbit label in each block
  have s7 := colCall (colMk2 (colMk2 (dC [encFun (labs k),
        encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)),
        encFun (colEqv (colBk labs r0 k) ol h0),
        encFun (colEqv (colBk labs r0 k) (colBk labs r0 k) h0),
        .nat (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k)] 2 (encFun ol) rfl (by omega))
      (colVar (P := P) (env := [A,
        encFun (labs k),
        encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)),
        encFun (colEqv (colBk labs r0 k) ol h0),
        encFun (colEqv (colBk labs r0 k) (colBk labs r0 k) h0),
        .nat (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k)]) (i := 2) rfl (le_refl _)))
      (dC _ 7 (natList (List.range m)) rfl (by omega)))
    (colTabMin_det hmmin hfmin hit hg ol (colBk labs r0 k) hol hbk (by omega))
  -- step 8: the keys of the positions
  have hgU : ∀ c, colMinv ol (colBk labs r0 k) c + (n + 1) ≤ X := fun c => by
    have := colMinAcc_le ol (colBk labs r0 k) c m
    have := hB.ol_le c
    unfold colMinv; omega
  have dn1 := Det.arith' (op := .add) (z := n + 1) (dC [encFun (labs k),
        encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)),
        encFun (colEqv (colBk labs r0 k) ol h0),
        encFun (colEqv (colBk labs r0 k) (colBk labs r0 k) h0),
        .nat (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k),
        encFun (colMinv ol (colBk labs r0 k))] 9 (.nat n) rfl (by omega))
    (Det.nat 1) rfl
  have s8 := colCall (colMk2 (colMk3
      (colVar (P := P) (env := [A,
        encFun (labs k),
        encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)),
        encFun (colEqv (colBk labs r0 k) ol h0),
        encFun (colEqv (colBk labs r0 k) (colBk labs r0 k) h0),
        .nat (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k),
        encFun (colMinv ol (colBk labs r0 k))]) (i := 7) rfl (le_refl _))
      (dC _ 4 (encFun fun i => (cf i : ℕ)) rfl (by omega)) dn1)
      (dC _ 10 (natList (List.range n)) rfl (by omega)))
    (colTabPick_det hmp hfp (colMinv ol (colBk labs r0 k)) cf (n + 1) (X := X) hgU (by omega)
      (by omega) hn)
  -- step 9: the value
  have s9a := colLabs_det hcl (fun i => colMinv ol (colBk labs r0 k) (cf i) + (n + 1)) dv
    (colMk2 (colVar (P := P) (env := [A,
        encFun (labs k),
        encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)),
        encFun (colEqv (colBk labs r0 k) ol h0),
        encFun (colEqv (colBk labs r0 k) (colBk labs r0 k) h0),
        .nat (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k),
        encFun (colMinv ol (colBk labs r0 k)),
        encFun (fun i => colMinv ol (colBk labs r0 k) (cf i) + (n + 1))]) (i := 8) rfl (le_refl _))
      (dC [encFun (labs k),
        encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)),
        encFun (colEqv (colBk labs r0 k) ol h0),
        encFun (colEqv (colBk labs r0 k) (colBk labs r0 k) h0),
        .nat (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k),
        encFun (colMinv ol (colBk labs r0 k)),
        encFun (fun i => colMinv ol (colBk labs r0 k) (cf i) + (n + 1))] 6 (encFun dv) rfl (by omega))) (fun i => hgU (cf i)) hB.dv_le hn
  have dur := colVar (P := P) (env := [A,
        encFun (labs k),
        encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)),
        encFun (colEqv (colBk labs r0 k) ol h0),
        encFun (colEqv (colBk labs r0 k) (colBk labs r0 k) h0),
        .nat (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k),
        encFun (colMinv ol (colBk labs r0 k)),
        encFun (fun i => colMinv ol (colBk labs r0 k) (cf i) + (n + 1))]) (i := 6)
    (v := .nat (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k)) rfl (le_refl _)
  have dcap := dHv [encFun (labs k),
        encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)),
        encFun (colEqv (colBk labs r0 k) ol h0),
        encFun (colEqv (colBk labs r0 k) (colBk labs r0 k) h0),
        .nat (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k),
        encFun (colMinv ol (colBk labs r0 k)),
        encFun (fun i => colMinv ol (colBk labs r0 k) (cf i) + (n + 1))] 2 (.nat (caps k)) (by omega) rfl
  have s9c := Det.arith' (op := .sub)
    (z := min (caps k) (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k)) dcap
    (Det.arith' (op := .sub) (z := caps k - colRat labs r0 h0 k / colLowRat labs r0 ol h0 k)
      dcap dur rfl)
    (by
      simp only [GI.Machine.BinOp.eval]
      generalize colRat labs r0 h0 k / colLowRat labs r0 ol h0 k = u
      omega)
  have s9 := colMk4 s9a dur s9c (dHv [encFun (labs k),
        encFun (colBk labs r0 k),
        encFun (fun c => colAk labs r0 k c + (m + 1)),
        encFun (colEqv (colBk labs r0 k) ol h0),
        encFun (colEqv (colBk labs r0 k) (colBk labs r0 k) h0),
        .nat (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k),
        encFun (colMinv ol (colBk labs r0 k)),
        encFun (fun i => colMinv ol (colBk labs r0 k) (cf i) + (n + 1))] 3 (.nat (origs k)) (by omega) rfl)
  have d := colLet s1 (colLet s2 (colLet s3 (colLet s4 (colLet s5 (colLet s6 (colLet s7
    (colLet s8 s9)))))))
  refine FunDet.intro hf ?_
  refine d.mono ?_
  have := s1.wt_lt
  have := s2.wt_lt
  have := s3.wt_lt
  have := s4.wt_lt
  have := s5.wt_lt
  have := s6a.wt_lt
  have := s6b.wt_lt
  have := s7.wt_lt
  have := s8.wt_lt
  have := s9a.wt_lt
  have := hB.caps_le k
  have hdiv : colRat labs r0 h0 k / colLowRat labs r0 ol h0 k ≤ m :=
    (Nat.div_le_self _ _).trans hr
  have := wt_nat_le (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k)
  have := min_le_left (caps k) (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k)
  have := Nat.sub_le (caps k) (colRat labs r0 h0 k / colLowRat labs r0 ol h0 k)
  generalize colRat labs r0 h0 k / colLowRat labs r0 ol h0 k = u at *
  generalize min (caps k) u = u' at *
  simp only [colLevK]
  omega

end Pieces

end GI.Impl
