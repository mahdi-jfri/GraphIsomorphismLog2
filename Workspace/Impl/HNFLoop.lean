module

public import Workspace.Impl.HNFCol

@[expose] public section

/-!
# The modular Hermite form, as a program

The loop over the columns `k < n` of `GI.Proved.hnfModIter`, with the column program of
`Workspace/Impl/HNFCol.lean` as its step. On `[m, n, M mod m]` the program returns
`encIntMatrix (GI.Proved.hnfModMat m M)`.
-/

namespace GI.Impl

open GI.Cited GI.Lang
open GI.Proved (hnfRed hnfStep hnfFoldStep hnfModIter hnfModInit hnfModMat hnfSpan hnfV HnfModInv
  HnfDone HnfWork)

/-! ### The shape of the state -/

/-- The invariant holds for the lattice of the starting rows, whatever the input. So the shape of
the state after `k` columns does not need any hypothesis on the lattice. -/
theorem hnfModIter_shape {n : ℕ} {m : ℤ} (hm : 0 < m) (M : Matrix (Fin n) (Fin n) ℤ) :
    ∀ k, k ≤ n → HnfModInv k m (hnfSpan (hnfModInit m M) ⊔ hnfV n m 0) (hnfModIter m M k) ∧
      (hnfModIter m M k).2.length = n := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨⟨⟨rfl, fun i j hi => absurd hi (by simp [hnfModIter])⟩, ?_, by simp [hnfModIter]⟩,
      by simp [hnfModIter, hnfModInit]⟩
    intro g hg
    simp only [hnfModIter, hnfModInit, List.mem_map, List.mem_finRange, true_and] at hg
    obtain ⟨i, rfl⟩ := hg
    exact ⟨fun j hj => absurd hj (Nat.not_lt_zero _),
      fun j _ => ⟨Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm⟩⟩
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hs := GI.Proved.hnfStep_inv ⟨k, by omega⟩ hm h1
    have e : hnfModIter m M (k + 1) = hnfStep ⟨k, by omega⟩ m (hnfModIter m M k) := by
      simp [hnfModIter, show k < n by omega]
    rw [e]
    refine ⟨hs, ?_⟩
    rw [hnfStep_eq]
    simp only
    rw [hnfFold_len]
    simp [h2]

/-! ### The loop -/

/-- The step of the loop, on `[[m, n, R], k, state]`. -/
def hnfLoopStepF (col : ℕ) : Expr :=
  .call col (mk3 (mk3 (arg 1) (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)))
    (.get (arg 2) (.nat 0)) (.get (arg 2) (.nat 1)))

/-- The entry: the finished rows at the end of the loop. -/
def hnfModF (loop : ℕ) : Expr := .get (.call loop (.var 0)) (.nat 0)

def hnfLoopKE : Expr := .get (.var 0) (.nat 1)
def hnfLoopInitE : Expr := mk2 .nil (.get (.var 0) (.nat 2))

/-- The functions of the modular Hermite form at base `b`, with the integer library at `ints`. -/
def hnfModFuns (b ints : ℕ) : List Expr :=
  [hnfModF (b + 1)] ++ loopFuns (b + 1) hnfLoopKE hnfLoopInitE (hnfLoopStepF (b + 4)) ++
    hnfColFuns (b + 4) ints

theorem hnfModFuns_length (b ints : ℕ) : (hnfModFuns b ints).length = 32 := rfl

structure hnfModAt (P : Program) (b ints : ℕ) : Prop where
  entry : P.funs[b]? = some (hnfModF (b + 1))
  loop : P.HasAt (b + 1) (loopFuns (b + 1) hnfLoopKE hnfLoopInitE (hnfLoopStepF (b + 4)))
  col : hnfColAt P (b + 4) ints

theorem hnfModAt_of {P : Program} {b ints : ℕ} (hI : linIntSpec P ints)
    (h : P.HasAt b (hnfModFuns b ints)) : hnfModAt P b ints where
  entry := (h.block (gs := [hnfModF (b + 1)]) 0 rfl).single
  loop := by simpa using h.block 1 rfl
  col := hnfColAt_of hI (by simpa using h.block 4 rfl)

/-- The argument `[m, n, M mod m]`. -/
def hnfModArg {n : ℕ} (m : ℤ) (M : Matrix (Fin n) (Fin n) ℤ) : Val :=
  .list [encInt m, .nat n, encIntMatrix (fun i j => M i j % m)]

theorem hnf_init_val {n : ℕ} (m : ℤ) (M : Matrix (Fin n) (Fin n) ℤ) :
    hnfRowsVal (hnfModInit m M) = encIntMatrix (fun i j => M i j % m) := by
  simp [hnfRowsVal, hnfModInit, encIntMatrix, linVecVal, List.map_map, Function.comp_def]

theorem hnf_rows_matrix {n : ℕ} (H : List (Fin n → ℤ)) (hH : H.length = n) :
    hnfRowsVal H = encIntMatrix (fun i : Fin n => H.getD i 0) := by
  simp only [hnfRowsVal, encIntMatrix, Val.list.injEq]
  apply List.ext_getElem (by simp [hH])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_finRange]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]
  rfl

theorem hnf_encInt_wt_ge (z : ℤ) : 8 ≤ (encInt z).wt := by
  unfold encInt
  rw [wt_list_eq]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have h1 := (Val.nat (if z < 0 then 1 else 0)).two_le_size
  have h2 := (Val.nat (if z < 0 then 1 else 0)).size_le_wt
  have h3 := (Val.list ((Nat.bits z.natAbs).map fun b => Val.nat (if b then 1 else 0))).two_le_size
  have h4 := (Val.list ((Nat.bits z.natAbs).map fun b => Val.nat (if b then 1 else 0))).size_le_wt
  omega

def hnfModCost (X : ℕ) : ℕ := X * hnfColCost X + 1000 * (X + 1) * (20 * (X * X) + 20)

set_option maxHeartbeats 4000000 in
/-- **The modular Hermite form.** -/
theorem hnfMod_spec {P : Program} {b ints : ℕ} (h : hnfModAt P b ints) {n : ℕ} {m : ℤ} {L X : ℕ}
    (hm0 : 0 < m) (hmL : m.natAbs < 2 ^ L) (hX : 1000 * ((n + 1) * (L + 1)) ≤ X)
    (M : Matrix (Fin n) (Fin n) ℤ) :
    FunDet P b (hnfModArg m M) (encIntMatrix (hnfModMat m M)) (hnfModCost X) := by
  set a := hnfModArg m M with ha
  have hsh := hnfModIter_shape hm0 M
  obtain ⟨hXX, hXL, hXn⟩ := hnf_X_facts hX
  have hQ : 1 ≤ (n + 1) * (L + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hstw : ∀ i, i ≤ n → (hnfStateVal (hnfModIter m M i)).wt ≤ 5 * (X * X) := by
    intro i hi
    obtain ⟨⟨hD, hW, -⟩, hl⟩ := hsh i hi
    exact hnf_state_wt hmL hm0.le hX _ (hnfDone_bound hm0.le hD hi)
      (fun v hv j => hnfWork_bound hm0.le (hW v hv) j) (by have := hD.1; omega) (by omega)
  have e0 : encIntMatrix (fun i j => M i j % m) = hnfRowsVal (hnfModInit m M) :=
    (hnf_init_val m M).symm
  have wR := hnf_rows_wt (L := L) (hnfModInit m M) (fun v hv j => by
      obtain ⟨⟨-, hW, -⟩, -⟩ := hsh 0 (Nat.zero_le _)
      have := hnfWork_bound hm0.le (hW v hv) j
      exact hnf_entry_lt this.1 this.2 hmL) (by simp [hnfModInit]; omega) hX
  have wa : a.wt ≤ 3 * (X * X) := by
    have w1 := wt_list3_le (encInt m) (.nat n) (encIntMatrix (fun i j => M i j % m))
    have w2 := hnf_wt_int hmL
    have w3 := wt_nat_le n
    have e : (Val.list [encInt m, .nat n, encIntMatrix (fun i j => M i j % m)]).wt = a.wt := rfl
    rw [e0] at w1 e
    omega
  have wR' : (hnfRowsVal (hnfModInit m M)).wt < a.wt := by
    rw [← e0]; exact wt_le_wt_list (by simp [ha, hnfModArg])
  have wn' : (Val.nat n).wt < a.wt := wt_le_wt_list (by simp [ha, hnfModArg])
  have hk : Det P [a] hnfLoopKE (.nat n) _ :=
    Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat 1)
      (show [encInt m, .nat n, encIntMatrix (fun i j => M i j % m)][1]? = some (.nat n) from rfl)
  have hacc : Det P [a] hnfLoopInitE (.list [.list [], hnfRowsVal (hnfModInit m M)]) _ :=
    Det.mk2 Det.nil (Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat 2)
      (show [encInt m, .nat n, encIntMatrix (fun i j => M i j % m)][2]? =
        some (hnfRowsVal (hnfModInit m M)) by rw [e0]; rfl))
  have hl := loopBdd_spec h.loop hk hacc (M := 5 * (X * X))
    (Inv := fun i acc => acc = hnfStateVal (hnfModIter m M i)) (D := fun _ => hnfColCost X)
    (by
      have w1 := wt_list2_le (.list []) (hnfRowsVal (hnfModInit m M))
      have w2 : (Val.list []).wt ≤ 4 := by decide
      have w3 := wt_nat_le n
      have s1 := sum_wt_lt_wt_list [encInt m, .nat n, encIntMatrix (fun i j => M i j % m)]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at s1
      have s2 := hnf_encInt_wt_ge m
      have s3 := (encIntMatrix (fun i j => M i j % m)).two_le_size
      have s4 := (encIntMatrix (fun i j => M i j % m)).size_le_wt
      have s5 := (Val.nat n).two_le_size
      have s6 := (Val.nat n).size_le_wt
      have e7 : (Val.list [encInt m, .nat n, encIntMatrix (fun i j => M i j % m)]).wt = a.wt := rfl
      have e9 : (hnfRowsVal (hnfModInit m M)).wt = (encIntMatrix (fun i j => M i j % m)).wt := by
        rw [e0]
      have e1 : (Val.nat 1).wt = 3 := wt_nat_one
      have e2 : (Val.nat 2).wt = 4 := rfl
      omega)
    rfl
    (fun i acc hi hacc => by rw [hacc]; exact hstw i hi)
    (by
      intro i acc hi hacc
      subst hacc
      obtain ⟨⟨hD, hW, -⟩, hlen⟩ := hsh i hi.le
      set st := hnfModIter m M i with hst
      have hcol := hnfCol_spec h.col ⟨i, hi⟩ hm0 hmL hX st hD hW (by omega)
      set vs := [a, Val.nat i, hnfStateVal st] with hvs
      have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
      have d0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
      have d2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
      have dm := Det.get' d0 (Det.nat 0) (show [encInt m, .nat n,
        encIntMatrix (fun i j => M i j % m)][0]? = some (encInt m) from rfl)
      have dn := Det.get' d0 (Det.nat 1) (show [encInt m, .nat n,
        encIntMatrix (fun i j => M i j % m)][1]? = some (.nat n) from rfl)
      have dD := Det.get' d2 (Det.nat 0)
        (show [hnfRowsVal st.1, hnfRowsVal st.2][0]? = some (hnfRowsVal st.1) from rfl)
      have dW := Det.get' d2 (Det.nat 1)
        (show [hnfRowsVal st.1, hnfRowsVal st.2][1]? = some (hnfRowsVal st.2) from rfl)
      have dc := Det.mk3 d1 dm dn
      have ec : Val.list [.nat i, encInt m, .nat n] = hnfColCtx i m n := rfl
      rw [ec] at dc
      have dout := Det.call (Det.mk3 dc dD dW) hcol
      have es : hnfStep ⟨i, hi⟩ m st = hnfModIter m M (i + 1) := by
        simp [hst, hnfModIter, hi]
      rw [es] at dout
      refine dout.post fun c hc => ⟨rfl, hc.trans ?_⟩
      have w1 : (hnfStateVal st).wt ≤ 5 * (X * X) := hstw i hi.le
      have w2 := hstw (i + 1) hi
      have wC := hnf_colCtx_wt hi hmL hX
      have wvs := wt_list3_le a (.nat i) (hnfStateVal st)
      have wi := wt_nat_le i
      have e3 : (Val.list vs).wt = (Val.list [a, .nat i, hnfStateVal st]).wt := rfl
      have w4 := wt_list3_le (hnfColCtx i m n) (hnfRowsVal st.1) (hnfRowsVal st.2)
      have w5 := wt_list3_le (.nat i) (encInt m) (.nat n)
      have w6 := wt_list2_le (hnfRowsVal st.1) (hnfRowsVal st.2)
      have e6 : (Val.list [hnfRowsVal st.1, hnfRowsVal st.2]).wt = (hnfStateVal st).wt := rfl
      have w9 : (hnfRowsVal st.1).wt < (hnfStateVal st).wt := wt_le_wt_list (by simp [hnfStateVal])
      have w10 : (hnfRowsVal st.2).wt < (hnfStateVal st).wt := wt_le_wt_list (by simp [hnfStateVal])
      have w7 : (encInt m).wt < a.wt := wt_le_wt_list (by simp [ha, hnfModArg])
      have e7 : (Val.list [encInt m, .nat n, encIntMatrix (fun i j => M i j % m)]).wt = a.wt := rfl
      have ez : (Val.nat 0).wt = 2 := wt_nat_zero
      have eo : (Val.nat 1).wt = 3 := wt_nat_one
      have e8 : (Val.list [Val.nat i, encInt m, Val.nat n]).wt = (hnfColCtx i m n).wt := rfl
      beta_reduce
      omega)
  have hl' : FunDet P (b + 1) a (hnfStateVal (hnfModIter m M n))
      (n * hnfColCost X + loopModK * (n + 1) * (a.wt + n + 5 * (X * X) + 1)) :=
    hl.mono fun w c hw => ⟨hw.1, by simpa using hw.2⟩
  have dcall := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hl'
  have dout := Det.get' dcall (Det.nat 0)
    (show [hnfRowsVal (hnfModIter m M n).1, hnfRowsVal (hnfModIter m M n).2][0]? =
      some (hnfRowsVal (hnfModIter m M n).1) from rfl)
  obtain ⟨⟨hD, -, -⟩, -⟩ := hsh n le_rfl
  rw [hnf_rows_matrix _ hD.1] at dout
  apply FunDet.intro h.entry
  refine dout.mono ?_
  have w1 := hstw n le_rfl
  have w2 : (encIntMatrix fun i : Fin n => (hnfModIter m M n).1.getD i 0).wt <
      (hnfStateVal (hnfModIter m M n)).wt := by
    rw [← hnf_rows_matrix _ hD.1]; exact wt_le_wt_list (by simp [hnfStateVal])
  have e2 : (encIntMatrix fun i : Fin n => (hnfModIter m M n).1.getD i 0) =
    encIntMatrix (hnfModMat m M) := rfl
  have h5 : n * hnfColCost X ≤ X * hnfColCost X := Nat.mul_le_mul_right _ (by omega)
  have h6 : loopModK * (n + 1) * (a.wt + n + 5 * (X * X) + 1) ≤
      1000 * (X + 1) * (10 * (X * X) + 10) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have h7 : 2 * (1000 * (X + 1) * (10 * (X * X) + 10)) = 1000 * (X + 1) * (20 * (X * X) + 20) := by
    ring
  have h8 : 1000 * (10 * (X * X) + 10) ≤ 1000 * (X + 1) * (10 * (X * X) + 10) :=
    Nat.mul_le_mul_right _ (by omega)
  have e2w : (encIntMatrix fun i : Fin n => (hnfModIter m M n).1.getD i 0).wt =
    (encIntMatrix (hnfModMat m M)).wt := by rw [e2]
  have ez : (Val.nat 0).wt = 2 := wt_nat_zero
  unfold hnfModCost
  rw [e2] at w2
  omega

end GI.Impl
