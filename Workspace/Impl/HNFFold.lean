import Workspace.Impl.HNFRed
import Workspace.Lang.Lib.Fold
import Workspace.Lang.Lib.LinIntColumn

/-!
# Clearing one column, as a program

At column `k`, the modular Hermite form (`GI.Proved.hnfStep`) starts with the pivot row
`m e_k` and runs Euclid's algorithm on it and each working row in turn
(`GI.Proved.hnfFoldStep`). This file gives the programs for the row `m e_k` and for this fold.

The context of a column is `[k, m, n]` (`hnfColCtx`). All rows have entries in `[0, m]` and
`m < 2 ^ L`. One number `X ≥ 1000 (n + 1) (L + 1)` bounds the costs.
-/

namespace GI.Impl

open GI.Cited GI.Lang
open GI.Proved (hnfRed hnfEuclid hnfFoldStep HnfPair HnfPiv HnfWork)

/-- The context `[k, m, n]` of a column. -/
def hnfColCtx (k : ℕ) (m : ℤ) (n : ℕ) : Val := .list [.nat k, encInt m, .nat n]

/-- A list of rows. -/
def hnfRowsVal {n : ℕ} (H : List (Fin n → ℤ)) : Val := .list (H.map linVecVal)

/-- The weight of a list of at most `2 n` rows with entries below `2 ^ L`. -/
theorem hnf_rows_wt {n L X : ℕ} (H : List (Fin n → ℤ)) (hH : ∀ h ∈ H, ∀ j, (h j).natAbs < 2 ^ L)
    (hlen : H.length ≤ 2 * n) (hX : 1000 * ((n + 1) * (L + 1)) ≤ X) :
    (hnfRowsVal H).wt ≤ X * X := by
  set Q := (n + 1) * (L + 1) with hQ
  have h1 := linWtList (vs := H.map linVecVal) (B := 45 * Q) (by
    intro v hv
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hv
    exact hnf_vec_wt h (hH h hh))
  simp only [List.length_map] at h1
  have e : (Val.list (H.map linVecVal)).wt = (hnfRowsVal H).wt := rfl
  have h2 : n + 1 ≤ Q := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : H.length * (45 * Q) ≤ (2 * Q) * (45 * Q) := Nat.mul_le_mul_right _ (by omega)
  have h4 : (2 * Q) * (45 * Q) = 90 * (Q * Q) := by ring
  have h5 : (1000 * Q) * (1000 * Q) ≤ X * X := Nat.mul_le_mul hX hX
  have h6 : (1000 * Q) * (1000 * Q) = 1000000 * (Q * Q) := by ring
  have h7 : Q ≤ Q * Q := Nat.le_mul_self Q
  omega

/-- Simple consequences of the bound on `X`. -/
theorem hnf_X_facts {n L X : ℕ} (hX : 1000 * ((n + 1) * (L + 1)) ≤ X) :
    1000 * X ≤ X * X ∧ 1000 * (L + 1) ≤ X ∧ 1000 * (n + 1) ≤ X := by
  have h4 : 1 ≤ (n + 1) * (L + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h5 : L + 1 ≤ (n + 1) * (L + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have h6 : n + 1 ≤ (n + 1) * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
  exact ⟨Nat.mul_le_mul_right _ (by omega), by omega, by omega⟩

/-- The weight of the context of a column. -/
theorem hnf_colCtx_wt {k n L X : ℕ} (hk : k < n) {m : ℤ} (hm : m.natAbs < 2 ^ L)
    (hX : 1000 * ((n + 1) * (L + 1)) ≤ X) : (hnfColCtx k m n).wt + n ≤ X := by
  have w1 := wt_list3_le (.nat k) (encInt m) (.nat n)
  have w2 := wt_nat_le k
  have w3 := wt_nat_le n
  have w4 := hnf_wt_int hm
  have e : (Val.list [.nat k, encInt m, .nat n]).wt = (hnfColCtx k m n).wt := rfl
  have h2 : n + 1 ≤ (n + 1) * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : L + 1 ≤ (n + 1) * (L + 1) := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-! ### The row `m e_k` -/

/-- Entry `j` of `m e_k`, on `[[k, m, n], j]`. -/
def hnfSingleCellF : Expr :=
  .ite (.arith .eq (arg 1) (.get (arg 0) (.nat 0))) (.get (arg 0) (.nat 1)) linIntZeroE

/-- The row `m e_k`, on `[k, m, n]`. -/
def hnfSingleF (tab : ℕ) : Expr := .call tab (mk2 (.var 0) (.get (.var 0) (.nat 2)))

def hnfSingleFuns (b : ℕ) : List Expr :=
  [hnfSingleF (b + 1)] ++ linTabulateFuns (b + 1) (b + 8) ++ [hnfSingleCellF]

theorem hnfSingleFuns_length (b : ℕ) : (hnfSingleFuns b).length = 9 := rfl

structure hnfSingleAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (hnfSingleF (b + 1))
  tab : linTabulateAt P (b + 1) (b + 8)
  cell : P.funs[b + 8]? = some hnfSingleCellF

theorem hnfSingleAt_of {P : Program} {b : ℕ} (h : P.HasAt b (hnfSingleFuns b)) :
    hnfSingleAt P b where
  entry := (h.block (gs := [hnfSingleF (b + 1)]) 0 rfl).single
  tab := linTabulateAt_of (h.block 1 rfl)
  cell := (h.block (gs := [hnfSingleCellF]) 8 rfl).single

def hnfSingleCost (X : ℕ) : ℕ := 2 * linTabulateCost (4 * X + 20) X (1000 * (X + 1)) + 100 * (X + 1)

set_option maxHeartbeats 1000000 in
theorem hnfSingle_spec {P : Program} {b : ℕ} (h : hnfSingleAt P b) {n : ℕ} (k : Fin n) (m : ℤ)
    {X : ℕ} (hX : (hnfColCtx k m n).wt + n ≤ X) :
    FunDet P b (hnfColCtx k m n) (linVecVal (Pi.single k m : Fin n → ℤ)) (hnfSingleCost X) := by
  set C := hnfColCtx k m n with hC
  have hcell : ∀ j : Fin n, FunDet P (b + 8) (.list [C, .nat j])
      (encInt ((Pi.single k m : Fin n → ℤ) j)) (1000 * (X + 1)) := by
    intro j
    have dj := Det.arg' (P := P) (vs := [C, .nat j]) (rest := []) (j := 1) rfl
    have dc := Det.arg' (P := P) (vs := [C, .nat j]) (rest := []) (j := 0) rfl
    have dk := Det.get' dc (Det.nat 0) (show [Val.nat k, encInt m, .nat n][0]? = some (.nat k) from rfl)
    have dm := Det.get' dc (Det.nat 1)
      (show [Val.nat k, encInt m, .nat n][1]? = some (encInt m) from rfl)
    have deq := Det.arith (op := .eq) dj dk
    have dz : Det P [.list [C, .nat j]] linIntZeroE (encInt 0) _ :=
      Det.mk2 (Det.nat 0) Det.nil
    have d := Det.ite' deq dm dz
    have hv : (if GI.Machine.BinOp.eq.eval j k = 0 then encInt 0 else encInt m) =
        encInt ((Pi.single k m : Fin n → ℤ) j) := by
      by_cases hjk : j = k
      · subst hjk; simp
      · have : (j : ℕ) ≠ k := fun e => hjk (Fin.ext e)
        simp [this, hjk]
    rw [hv] at d
    apply FunDet.intro h.cell
    refine d.mono ?_
    have w0 := wt_list2_le C (.nat j)
    have w1 := wt_nat_le (j : ℕ)
    have w2 := wt_nat_le (GI.Machine.BinOp.eq.eval j k)
    have w3 : GI.Machine.BinOp.eq.eval j k ≤ 1 := by simp; split_ifs <;> omega
    have w4 : (encInt m).wt < C.wt := wt_le_wt_list (by simp)
    have w6 : (encInt 0).wt ≤ 100 := by decide
    have w5 : (encInt ((Pi.single k m : Fin n → ℤ) j)).wt ≤ (encInt m).wt + 100 := by
      by_cases hjk : j = k
      · subst hjk; simp
      · simp only [ne_eq, hjk, not_false_eq_true, Pi.single_eq_of_ne]; omega
    have hj := j.isLt
    have w8 : (Val.list [Val.nat 0, Val.list []]).wt ≤ 100 := by decide
    have e1 : (Val.list [Val.nat 0, Val.list ((Nat.bits (Int.natAbs 0)).map
      fun b => Val.nat (if b = true then 1 else 0))]).wt = (encInt 0).wt := rfl
    have w12 : (Val.nat k).wt < C.wt := wt_le_wt_list (by simp)
    have w9 : (Val.nat 0).wt = 2 := rfl
    have w10 : (Val.nat 1).wt = 3 := rfl
    have w11 : (Val.list []).wt ≤ 100 := by decide
    rw [max_def, max_def]
    split_ifs <;> omega
  have ht := linTabulate_spec h.tab C (fun j : Fin n => encInt ((Pi.single k m : Fin n → ℤ) j))
    (1000 * (X + 1)) hcell
  have dn := Det.get' (Det.var' (P := P) (env := [C]) (i := 0) rfl) (Det.nat 2)
    (show [Val.nat k, encInt m, .nat n][2]? = some (.nat n) from rfl)
  have dout := Det.call (Det.mk2 (Det.var' (P := P) (env := [C]) (i := 0) rfl) dn) ht
  apply FunDet.intro h.entry
  refine dout.mono ?_
  have wo := ht.wt_lt
  have w2 := wt_list2_le C (.nat n)
  have wn := wt_nat_le n
  have hm := linTabulateCost_mono (show (Val.list [C, .nat n]).wt ≤ 4 * X + 20 by omega)
    (show n ≤ X by omega) (le_refl (1000 * (X + 1)))
  have e4 : (Val.list ((List.finRange n).map fun j =>
    encInt ((Pi.single k m : Fin n → ℤ) j))).wt = (linVecVal (Pi.single k m : Fin n → ℤ)).wt := rfl
  have e5 : (Val.list [Val.nat k, encInt m, .nat n]).wt = C.wt := rfl
  have w6 : (Val.nat n).wt < C.wt := wt_le_wt_list (by simp)
  have e2 : (Val.nat 2).wt = 4 := rfl
  unfold hnfSingleCost
  omega

/-! ### Shapes and weights of the rows -/

theorem hnfWork_bound {n : ℕ} {k : ℕ} {m : ℤ} (hm : 0 ≤ m) {g : Fin n → ℤ} (h : HnfWork k m g)
    (j : Fin n) : 0 ≤ g j ∧ g j ≤ m := by
  by_cases hj : (j : ℕ) < k
  · rw [h.1 j hj]; exact ⟨le_rfl, hm⟩
  · have := h.2 j (by omega); omega

theorem hnfPiv_bound {n : ℕ} {k : Fin n} {m : ℤ} {a : Fin n → ℤ} (h : HnfPiv k m a) (j : Fin n) :
    0 ≤ a j ∧ a j ≤ m := by
  rcases lt_trichotomy (j : ℕ) k with hj | hj | hj
  · rw [h.1 j hj]; have := h.2.1; omega
  · rw [show j = k from Fin.ext hj]; have := h.2.1; omega
  · have := h.2.2 j hj; omega

/-- A fold accumulator: the pivot row and the finished working rows. -/
def hnfAccVal {n : ℕ} (st : (Fin n → ℤ) × List (Fin n → ℤ)) : Val :=
  .list [linVecVal st.1, hnfRowsVal st.2]

theorem hnf_acc_wt {n L X : ℕ} {m : ℤ} (hm : m.natAbs < 2 ^ L)
    (hX : 1000 * ((n + 1) * (L + 1)) ≤ X) (st : (Fin n → ℤ) × List (Fin n → ℤ))
    (h1 : ∀ j, 0 ≤ st.1 j ∧ st.1 j ≤ m) (h2 : ∀ v ∈ st.2, ∀ j, 0 ≤ v j ∧ v j ≤ m)
    (hlen : st.2.length ≤ 2 * n) : (hnfAccVal st).wt ≤ 3 * (X * X) := by
  have w1 := hnf_vec_wt (L := L) st.1 fun j => hnf_entry_lt (h1 j).1 (h1 j).2 hm
  have w2 := hnf_rows_wt st.2 (fun v hv j => hnf_entry_lt (h2 v hv j).1 (h2 v hv j).2 hm) hlen hX
  have w3 := wt_list2_le (linVecVal st.1) (hnfRowsVal st.2)
  have e : (Val.list [linVecVal st.1, hnfRowsVal st.2]).wt = (hnfAccVal st).wt := rfl
  have h3 : 1000 * X ≤ X * X := Nat.mul_le_mul_right _ (le_trans (by
    have : 1 ≤ (n + 1) * (L + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega) hX)
  have h4 : 1 ≤ (n + 1) * (L + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  omega

/-! ### One step of the fold -/

/-- One step of the fold, on `[[k, m, n], acc, g]`. -/
def hnfFoldStepF (euc : ℕ) : Expr :=
  .letE (.call euc (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 0))
      (arg 2)))
    (mk2 (.get (.var 1) (.nat 0)) (.snoc (.get (arg 1) (.nat 1)) (.get (.var 1) (.nat 1))))

/-- The functions of the fold at base `b`, calling Euclid's algorithm at `euc`. -/
def hnfFoldFuns (b euc : ℕ) : List Expr := foldlFuns b (b + 3) ++ [hnfFoldStepF euc]

theorem hnfFoldFuns_length (b euc : ℕ) : (hnfFoldFuns b euc).length = 4 := rfl

structure hnfFoldAt (P : Program) (b e red ints : ℕ) : Prop where
  euc : hnfEucAt P e red ints
  fold : P.HasAt b (foldlFuns b (b + 3))
  step : P.funs[b + 3]? = some (hnfFoldStepF e)

theorem hnfFoldAt_of {P : Program} {b e red ints : ℕ} (he : hnfEucAt P e red ints)
    (h : P.HasAt b (hnfFoldFuns b e)) : hnfFoldAt P b e red ints where
  euc := he
  fold := h.block 0 rfl
  step := (h.block (gs := [hnfFoldStepF e]) 3 rfl).single

def hnfFoldStepCost (X : ℕ) : ℕ := (2 * X + 2) * hnfEucStepCost X + 1000 * (X * X + 1)

theorem wt_nat_zero : (Val.nat 0).wt = 2 := rfl
theorem wt_nat_one : (Val.nat 1).wt = 3 := rfl

set_option maxHeartbeats 4000000 in
theorem hnfFoldStep_spec {P : Program} {b e red ints : ℕ} (h : hnfFoldAt P b e red ints)
    {n : ℕ} (k : Fin n) {m : ℤ} {L X : ℕ} (hm0 : 0 < m) (hmL : m.natAbs < 2 ^ L)
    (hX : 1000 * ((n + 1) * (L + 1)) ≤ X) (st : (Fin n → ℤ) × List (Fin n → ℤ)) (g : Fin n → ℤ)
    (hpiv : HnfPiv k m st.1) (hacc : ∀ v ∈ st.2, HnfWork (k + 1) m v) (hlen : st.2.length < n)
    (hg : HnfWork k m g) :
    FunDet P (b + 3) (.list [hnfColCtx k m n, hnfAccVal st, linVecVal g])
      (hnfAccVal (hnfFoldStep k m st g)) (hnfFoldStepCost X) := by
  have hpair : HnfPair k m st.1 g :=
    ⟨fun j hj => ⟨hpiv.1 j hj, hg.1 j hj⟩, hpiv.2.1, hg.2 k le_rfl,
      fun j hj => ⟨hpiv.2.2 j hj, hg.2 j hj.le⟩⟩
  have hE := hnfEuc_spec h.euc k hm0 hmL hX st.1 g hpair
  set C := hnfColCtx k m n with hC
  set A := hnfAccVal st with hA
  set E := hnfEuclid k m st.1 g with hEdef
  have d0 := Det.get' (Det.arg' (P := P) (vs := [C, A, linVecVal g]) (rest := []) (j := 0) rfl)
    (Det.nat 0) (show [Val.nat k, encInt m, .nat n][0]? = some (.nat k) from rfl)
  have d1 := Det.get' (Det.arg' (P := P) (vs := [C, A, linVecVal g]) (rest := []) (j := 0) rfl)
    (Det.nat 1) (show [Val.nat k, encInt m, .nat n][1]? = some (encInt m) from rfl)
  have d2 := Det.get' (Det.arg' (P := P) (vs := [C, A, linVecVal g]) (rest := []) (j := 1) rfl)
    (Det.nat 0) (show [linVecVal st.1, hnfRowsVal st.2][0]? = some (linVecVal st.1) from rfl)
  have d3 := Det.arg' (P := P) (vs := [C, A, linVecVal g]) (rest := []) (j := 2) rfl
  have dmk := Det.mk4 d0 d1 d2 d3
  have de := Det.call dmk hE
  set env2 := [Val.list [C, A, linVecVal g], hnfPairVal E] with henv2
  have dE0 := Det.get' (Det.var' (P := P) (env := env2) (i := 1) rfl) (Det.nat 0)
    (show [linVecVal E.1, linVecVal E.2][0]? = some (linVecVal E.1) from rfl)
  have dE1 := Det.get' (Det.var' (P := P) (env := env2) (i := 1) rfl) (Det.nat 1)
    (show [linVecVal E.1, linVecVal E.2][1]? = some (linVecVal E.2) from rfl)
  have dA1 := Det.get' (Det.arg' (P := P) (vs := [C, A, linVecVal g]) (rest := [hnfPairVal E])
    (j := 1) rfl) (Det.nat 1)
    (show [linVecVal st.1, hnfRowsVal st.2][1]? = some (.list (st.2.map linVecVal)) from rfl)
  have dout := Det.mk2 dE0 (Det.snoc dA1 dE1)
  have hv : Val.list [linVecVal E.1, .list (st.2.map linVecVal ++ [linVecVal E.2])] =
      hnfAccVal (hnfFoldStep k m st g) := by
    simp [hnfAccVal, hnfFoldStep, hnfRowsVal, hEdef]
  rw [hv] at dout
  apply FunDet.intro h.step
  refine (Det.letE de dout).mono ?_
  -- weights
  have hres := GI.Proved.hnfEuclid_spec k hm0 _ st.1 g rfl hpair
  rw [← hEdef] at hres
  have wE := hnf_pairVal_wt (L := L) hmL (fun j => (hnfPair_bound hres.1 j).1)
    (fun j => (hnfPair_bound hres.1 j).2)
  have wE' : (hnfPairVal E).wt ≤ 200 * ((n + 1) * (L + 1)) := wE
  have h4 : 1 ≤ (n + 1) * (L + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hst2 : ∀ v ∈ st.2, ∀ j, 0 ≤ v j ∧ v j ≤ m := fun v hv j => hnfWork_bound hm0.le (hacc v hv) j
  have wA := hnf_acc_wt hmL hX st (hnfPiv_bound hpiv) hst2 (by omega)
  have wA' := hnf_acc_wt hmL hX (hnfFoldStep k m st g)
    (fun j => (hnfPair_bound hres.1 j).1)
    (by
      intro v hv j
      simp only [hnfFoldStep, List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact hst2 v hv j
      · exact (hnfPair_bound hres.1 j).2)
    (by simp [hnfFoldStep]; omega)
  have wC := hnf_colCtx_wt k.isLt hmL hX
  have wg := hnf_vec_wt (L := L) g fun j => hnf_entry_lt (hnfWork_bound hm0.le hg j).1
    (hnfWork_bound hm0.le hg j).2 hmL
  have w1 := wt_list3_le C A (linVecVal g)
  have w2 := wt_list4_le (.nat k) (encInt m) (linVecVal st.1) (linVecVal g)
  have e2 : (Val.list [.nat k, encInt m, linVecVal st.1, linVecVal g]).wt =
    (hnfCtx k m st.1 g).wt := rfl
  have w3 : (Val.nat k).wt < C.wt := wt_le_wt_list (by simp)
  have w4 : (encInt m).wt < C.wt := wt_le_wt_list (by simp)
  have w5 : (linVecVal st.1).wt < A.wt := wt_le_wt_list (by simp)
  have w6 : (hnfRowsVal st.2).wt < A.wt := wt_le_wt_list (by simp)
  have e6 : (Val.list (st.2.map linVecVal)).wt = (hnfRowsVal st.2).wt := rfl
  have w7 : (linVecVal E.1).wt < (hnfPairVal E).wt := wt_le_wt_list (by simp [hnfPairVal])
  have w8 : (linVecVal E.2).wt < (hnfPairVal E).wt := wt_le_wt_list (by simp [hnfPairVal])
  have w9 := wt_list_snoc_le (st.2.map linVecVal) (linVecVal E.2)
  have w10 := wt_list2_le (linVecVal E.1) (.list (st.2.map linVecVal ++ [linVecVal E.2]))
  have e10 : (Val.list [linVecVal E.1, .list (st.2.map linVecVal ++ [linVecVal E.2])]).wt =
    (hnfAccVal (hnfFoldStep k m st g)).wt := by rw [hv]
  obtain ⟨h3, h5, h6⟩ := hnf_X_facts hX
  have hL : (2 * L + 2) * hnfEucStepCost X ≤ (2 * X + 2) * hnfEucStepCost X :=
    Nat.mul_le_mul_right _ (by omega)
  have e0 : (Val.nat 0).wt = 2 := wt_nat_zero
  have e1' : (Val.nat 1).wt = 3 := wt_nat_one
  have f1 : (hnfAccVal st).wt = A.wt := rfl
  have f2 : (hnfColCtx k m n).wt = C.wt := rfl
  have f3 : (hnfPairVal (E.1, E.2)).wt = (hnfPairVal E).wt := rfl
  have f4 : (Val.list [linVecVal E.1, linVecVal E.2]).wt = (hnfPairVal E).wt := rfl
  unfold hnfFoldStepCost
  omega

/-! ### The fold -/

theorem hnfFold_len {n : ℕ} (k : Fin n) (m : ℤ) (G : List (Fin n → ℤ)) :
    ∀ acc : (Fin n → ℤ) × List (Fin n → ℤ),
      (G.foldl (hnfFoldStep k m) acc).2.length = acc.2.length + G.length := by
  induction G with
  | nil => intro acc; simp
  | cons g G ih =>
    intro acc
    simp only [List.foldl_cons, ih, hnfFoldStep, List.length_append, List.length_cons, List.length_nil,
      List.length_singleton]
    omega

theorem hnfPiv_single {n : ℕ} (k : Fin n) {m : ℤ} (hm : 0 < m) :
    HnfPiv k m (Pi.single k m : Fin n → ℤ) := by
  refine ⟨fun j hj => ?_, by simp [hm, le_refl], fun j hj => ?_⟩
  · have : j ≠ k := fun e => by rw [e] at hj; omega
    simp [this]
  · have : j ≠ k := fun e => by rw [e] at hj; omega
    simp [this, hm]

def hnfFoldCost (X : ℕ) : ℕ := X * hnfFoldStepCost X + 1000 * (X + 1) * (20 * (X * X) + 20)

set_option maxHeartbeats 2000000 in
theorem hnfFold_run {P : Program} {b e red ints : ℕ} (h : hnfFoldAt P b e red ints)
    {n : ℕ} (k : Fin n) {m : ℤ} {L X : ℕ} (hm0 : 0 < m) (hmL : m.natAbs < 2 ^ L)
    (hX : 1000 * ((n + 1) * (L + 1)) ≤ X) (G : List (Fin n → ℤ)) (hG : ∀ g ∈ G, HnfWork k m g)
    (hGlen : G.length ≤ n) :
    FunDet P b (.list [hnfColCtx k m n, hnfRowsVal G, hnfAccVal (Pi.single k m, [])])
      (hnfAccVal (G.foldl (hnfFoldStep k m) (Pi.single k m, []))) (hnfFoldCost X) := by
  set init : (Fin n → ℤ) × List (Fin n → ℤ) := (Pi.single k m, []) with hinit
  have hpre : ∀ i, HnfPiv k m ((G.take i).foldl (hnfFoldStep k m) init).1 ∧
      (∀ v ∈ ((G.take i).foldl (hnfFoldStep k m) init).2, HnfWork (k + 1) m v) ∧
      ((G.take i).foldl (hnfFoldStep k m) init).2.length ≤ i := by
    intro i
    obtain ⟨h1, h2, -⟩ := GI.Proved.hnfFold_spec k hm0 (G.take i) init (hnfPiv_single k hm0)
      (by simp [hinit]) (fun g hg => hG g (List.mem_of_mem_take hg))
    refine ⟨h1, h2, ?_⟩
    rw [hnfFold_len]
    simp [hinit]
  obtain ⟨hXX, hXL, hXn⟩ := hnf_X_facts hX
  have hM : ∀ i, i ≤ G.length →
      (hnfAccVal ((G.take i).foldl (hnfFoldStep k m) init)).wt ≤ 3 * (X * X) := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hpre i
    exact hnf_acc_wt hmL hX _ (hnfPiv_bound h1) (fun v hv j => hnfWork_bound hm0.le (h2 v hv) j)
      (by omega)
  have hf := foldl_spec h.fold (c := hnfColCtx k m n) (xs := G.map linVecVal)
    (acc0 := hnfAccVal init) (M := 3 * (X * X)) (B := fun _ => hnfFoldStepCost X)
    (Inv := fun i acc => acc = hnfAccVal ((G.take i).foldl (hnfFoldStep k m) init))
    (by simp) (fun i acc hi hacc => by
      rw [hacc]; simp only [List.length_map] at hi; exact hM i hi)
    (fun i acc hi hacc => by
      simp only [List.length_map] at hi
      subst hacc
      obtain ⟨h1, h2, h3⟩ := hpre i
      have hs := hnfFoldStep_spec h k hm0 hmL hX _ G[i] h1 h2 (by omega)
        (hG _ (List.getElem_mem hi))
      rw [List.getElem_map]
      refine FunAll.mono hs fun w c hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
        List.foldl_append]
      rfl)
  have e1 : Val.list (G.map linVecVal) = hnfRowsVal G := rfl
  rw [e1] at hf
  refine hf.mono fun w c hw => ⟨?_, ?_⟩
  · rw [hw.1, List.length_map, List.take_length]
  · have hc := hw.2
    simp only [List.length_map, Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have w1 := wt_list3_le (hnfColCtx k m n) (hnfRowsVal G) (hnfAccVal init)
    have w2 := hnf_colCtx_wt k.isLt hmL hX
    have w3 := hnf_rows_wt G (fun v hv j => hnf_entry_lt (hnfWork_bound hm0.le (hG v hv) j).1
      (hnfWork_bound hm0.le (hG v hv) j).2 hmL) (by omega) hX
    have w4 := hM 0 (Nat.zero_le _)
    simp only [List.take_zero, List.foldl_nil] at w4
    have h5 : G.length * hnfFoldStepCost X ≤ X * hnfFoldStepCost X :=
      Nat.mul_le_mul_right _ (by omega)
    have h6 : loopModK * (G.length + 1) * ((Val.list [hnfColCtx k m n, hnfRowsVal G,
        hnfAccVal init]).wt + G.length + 3 * (X * X) + 1) ≤
        1000 * (X + 1) * (20 * (X * X) + 20) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    unfold hnfFoldCost
    omega

end GI.Impl
