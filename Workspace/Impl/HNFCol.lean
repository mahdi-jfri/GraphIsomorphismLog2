module

public import Workspace.Impl.HNFFold
public import Workspace.Impl.LinMapEncoded

@[expose] public section

/-!
# One column of the modular Hermite form, as a program

`GI.Proved.hnfStep k m (D, W)` clears column `k` in the working rows `W` (the fold of
`Workspace/Impl/HNFFold.lean`), gets the new pivot row `f`, reduces each finished row `h ∈ D` by
`f` (`hnfRed k m h f (h k / f k)`) and adds `f` at the end of `D`. This file gives the program for
the reduction of the finished rows and for the whole column.
-/

namespace GI.Impl

open GI.Cited GI.Lang
open GI.Proved (hnfRed hnfEuclid hnfFoldStep hnfStep HnfPair HnfPiv HnfWork HnfDone)

/-! ### Reducing one finished row -/

/-- On `[[k, m, f], h]`: the row `hnfRed k m h f (h k / f k)`. -/
def hnfRowRedF (red quo : ℕ) : Expr :=
  .call red (mk2 (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1) (.get (arg 0) (.nat 2)))
    (.call quo (mk2 (.get (arg 1) (.get (arg 0) (.nat 0)))
      (.get (.get (arg 0) (.nat 2)) (.get (arg 0) (.nat 0))))))

def hnfRowRedCost (X : ℕ) : ℕ := hnfRedCost X + linIntBinaryCost (1000 * (X + 1)) + 1000 * (X + 1)

theorem hnf_quo_bound {m x y : ℤ} (hx : 0 ≤ x ∧ x ≤ m) (hy : 0 < y) : 0 ≤ x / y ∧ x / y ≤ m :=
  ⟨Int.ediv_nonneg hx.1 hy.le, (Int.ediv_le_self y hx.1).trans hx.2⟩

set_option maxHeartbeats 2000000 in
theorem hnfRowRed_spec {P : Program} {f red ints : ℕ} (hR : hnfRedAt P red ints)
    (hf : P.funs[f]? = some (hnfRowRedF red (ints + 14))) {n : ℕ} (k : Fin n) {m : ℤ} {L X : ℕ}
    (hm0 : 0 < m) (hmL : m.natAbs < 2 ^ L) (hX : 1000 * ((n + 1) * (L + 1)) ≤ X)
    (piv h : Fin n → ℤ) (hpiv : HnfPiv k m piv) (hh : ∀ j, 0 ≤ h j ∧ h j ≤ m) :
    FunDet P f (.list [.list [.nat k, encInt m, linVecVal piv], linVecVal h])
      (linVecVal (hnfRed k m h piv (h k / piv k))) (hnfRowRedCost X) := by
  have hI := hR.hI
  set c := Val.list [.nat k, encInt m, linVecVal piv] with hc
  have hpb := hnfPiv_bound hpiv
  have hq := hnf_quo_bound (hh k) hpiv.2.1.1
  have hql := hnf_entry_lt hq.1 hq.2 hmL
  have hhl : ∀ j, (h j).natAbs < 2 ^ L := fun j => hnf_entry_lt (hh j).1 (hh j).2 hmL
  have hpl : ∀ j, (piv j).natAbs < 2 ^ L := fun j => hnf_entry_lt (hpb j).1 (hpb j).2 hmL
  have hXr := hnf_redArg_wt (k : ℕ) k.isLt m h piv (h k / piv k) hmL hhl hpl hql
  have dred := hnfRed_spec hR (k : ℕ) m h piv (h k / piv k) hmL hhl hpl hql (hXr.trans hX)
  have dc := Det.arg' (P := P) (vs := [c, linVecVal h]) (rest := []) (j := 0) rfl
  have dh := Det.arg' (P := P) (vs := [c, linVecVal h]) (rest := []) (j := 1) rfl
  have dk := Det.get' dc (Det.nat 0)
    (show [Val.nat k, encInt m, linVecVal piv][0]? = some (.nat k) from rfl)
  have dm := Det.get' dc (Det.nat 1)
    (show [Val.nat k, encInt m, linVecVal piv][1]? = some (encInt m) from rfl)
  have dp := Det.get' dc (Det.nat 2)
    (show [Val.nat k, encInt m, linVecVal piv][2]? = some (linVecVal piv) from rfl)
  have dhk := Det.get' dh dk (hnf_vec_get h k)
  have dpk := Det.get' dp dk (hnf_vec_get piv k)
  have dquo := Det.call (Det.mk2 dhk dpk) (hI.quo (h k) (piv k))
  have dout := Det.call (Det.mk2 (Det.mk4 dk dm dh dp) dquo) dred
  apply FunDet.intro hf
  refine dout.mono ?_
  obtain ⟨hXX, hXL, hXn⟩ := hnf_X_facts hX
  have wh := hnf_vec_wt h hhl
  have wp := hnf_vec_wt piv hpl
  have wm := hnf_wt_int hmL
  have wq := hnf_wt_int hql
  have whk := hnf_wt_int (hhl k)
  have wpk := hnf_wt_int (hpl k)
  have wk := wt_nat_le (k : ℕ)
  have hkn := k.isLt
  have w1 := wt_list3_le (.nat k) (encInt m) (linVecVal piv)
  have w2 := wt_list2_le c (linVecVal h)
  have w3 := wt_list2_le (encInt (h k)) (encInt (piv k))
  have w4 := wt_list4_le (.nat k) (encInt m) (linVecVal h) (linVecVal piv)
  have e4 : (Val.list [.nat k, encInt m, linVecVal h, linVecVal piv]).wt =
    (hnfCtx k m h piv).wt := rfl
  have w5 := wt_list2_le (hnfCtx k m h piv) (encInt (h k / piv k))
  have c1 := linIntBinaryCost_mono (show (Val.list [encInt (h k), encInt (piv k)]).wt ≤
    1000 * (X + 1) by omega)
  have wo := hnf_vec_wt (L := 2 * L + 1) (hnfRed k m h piv (h k / piv k)) (fun j => by
    unfold hnfRed
    have h1 := hnf_abs_mul hql (hpl j)
    have h2 := hnf_abs_sub (L := 2 * L) ((hhl j).trans_le (Nat.pow_le_pow_right (by decide)
      (by omega))) h1
    split_ifs
    · have h3 := Int.emod_nonneg (h j - h k / piv k * piv j) hm0.ne'
      have h4 := Int.emod_lt_of_pos (h j - h k / piv k * piv j) hm0
      exact (hnf_entry_lt h3 h4.le hmL).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    · exact h2)
  have e0 : (Val.nat 0).wt = 2 := wt_nat_zero
  have e1 : (Val.nat 1).wt = 3 := wt_nat_one
  have e2 : (Val.nat 2).wt = 4 := rfl
  have f1 : (Val.list [.nat k, encInt m, linVecVal piv]).wt = c.wt := rfl
  have f2 : (n + 1) * (2 * L + 1 + 1) = 2 * ((n + 1) * (L + 1)) := by ring
  have f3 : (Val.list [Val.list [Val.nat ↑k, encInt m, linVecVal h, linVecVal piv],
    encInt (h k / piv k)]).wt = (Val.list [hnfCtx k m h piv, encInt (h k / piv k)]).wt := rfl
  unfold hnfRowRedCost
  omega

/-! ### Reducing all finished rows -/

/-- The finished rows have entries in `[0, m]`. -/
theorem hnfDone_bound {n k : ℕ} {m : ℤ} (hm : 0 ≤ m) {H : List (Fin n → ℤ)} (h : HnfDone k m H)
    (hk : k ≤ n) : ∀ v ∈ H, ∀ j, 0 ≤ v j ∧ v j ≤ m := by
  intro v hv j
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have hin : i < n := by have := h.1; omega
  obtain ⟨h1, h2, h3, h4⟩ := h.2 ⟨i, hin⟩ j hi
  simp only at h1 h2 h3 h4
  rcases lt_trichotomy (j : ℕ) i with hji | hji | hji
  · rw [h1 hji]; exact ⟨le_rfl, hm⟩
  · have := h2 hji; exact ⟨this.1.le, this.2⟩
  · by_cases hjk : (j : ℕ) < H.length
    · have h5 := h3 hjk hji
      have hd := ((h.2 j j hjk).2.1 rfl).2
      exact ⟨h5.1, (h5.2.trans_le hd).le⟩
    · have := h4 (by have := h.1; omega); exact ⟨this.1, this.2.le⟩

/-- The context `[k, m, f]` of the reduction of the finished rows by the pivot row `f`. -/
def hnfRedCtx {n : ℕ} (k : ℕ) (m : ℤ) (f : Fin n → ℤ) : Val := .list [.nat k, encInt m, linVecVal f]

def hnfMapRedCost (X : ℕ) : ℕ := linMapBudget (3 * (X * X)) (hnfRowRedCost X)

theorem hnf_mapBudget_mono {W W' B B' : ℕ} (hW : W ≤ W') (hB : B ≤ B') :
    linMapBudget W B ≤ linMapBudget W' B' := by
  unfold linMapBudget
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)) (by omega)

set_option maxHeartbeats 1000000 in
theorem hnfMapRed_spec {P : Program} {b f red ints : ℕ} (hR : hnfRedAt P red ints)
    (hf : P.funs[f]? = some (hnfRowRedF red (ints + 14))) (hmap : P.HasAt b (mapFuns b f))
    {n : ℕ} (k : Fin n) {m : ℤ} {L X : ℕ}
    (hm0 : 0 < m) (hmL : m.natAbs < 2 ^ L) (hX : 1000 * ((n + 1) * (L + 1)) ≤ X)
    (piv : Fin n → ℤ) (hpiv : HnfPiv k m piv) (D : List (Fin n → ℤ))
    (hD : ∀ v ∈ D, ∀ j, 0 ≤ v j ∧ v j ≤ m) (hlen : D.length ≤ n) :
    FunDet P b (.list [hnfRedCtx k m piv, hnfRowsVal D])
      (hnfRowsVal (D.map fun h => hnfRed k m h piv (h k / piv k))) (hnfMapRedCost X) := by
  have hs := linMapEncoded_spec hmap linVecVal linVecVal_injective
    (fun h => linVecVal (hnfRed k m h piv (h k / piv k))) (hnfRedCtx k m piv) D (hnfRowRedCost X)
    (fun h hh => hnfRowRed_spec hR hf k hm0 hmL hX piv h hpiv (hD h hh))
  have e1 : Val.list (D.map linVecVal) = hnfRowsVal D := rfl
  have e2 : Val.list (D.map fun h => linVecVal (hnfRed k m h piv (h k / piv k))) =
      hnfRowsVal (D.map fun h => hnfRed k m h piv (h k / piv k)) := by
    simp [hnfRowsVal, List.map_map, Function.comp_def]
  rw [e1, e2] at hs
  refine hs.mono ?_
  apply hnf_mapBudget_mono _ le_rfl
  have hpb := hnfPiv_bound hpiv
  have w1 := hnf_rows_wt (L := L) D (fun v hv j => hnf_entry_lt (hD v hv j).1 (hD v hv j).2 hmL)
    (by omega) hX
  have w2 := wt_list2_le (hnfRedCtx k m piv) (hnfRowsVal D)
  have w3 := wt_list3_le (.nat k) (encInt m) (linVecVal piv)
  have e3 : (Val.list [.nat k, encInt m, linVecVal piv]).wt = (hnfRedCtx k m piv).wt := rfl
  have w4 := wt_nat_le (k : ℕ)
  have w5 := hnf_wt_int hmL
  have w6 := hnf_vec_wt (L := L) piv fun j => hnf_entry_lt (hpb j).1 (hpb j).2 hmL
  have hk := k.isLt
  obtain ⟨hXX, hXL, hXn⟩ := hnf_X_facts hX
  have h4 : 1 ≤ (n + 1) * (L + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  omega

/-! ### One column -/

/-- The state of the algorithm: the finished rows and the working rows. -/
def hnfStateVal {n : ℕ} (st : List (Fin n → ℤ) × List (Fin n → ℤ)) : Val :=
  .list [hnfRowsVal st.1, hnfRowsVal st.2]

/-- Column `k`, on `[[k, m, n], D, W]`. -/
def hnfColF (fold single map : ℕ) : Expr :=
  .letE (.call fold (mk3 (arg 0) (arg 2) (mk2 (.call single (arg 0)) .nil)))
    (mk2 (.snoc (.call map (mk2 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
        (.get (.var 1) (.nat 0))) (arg 1))) (.get (.var 1) (.nat 0)))
      (.get (.var 1) (.nat 1)))

/-- The functions of one column at base `b`, with the integer library at `ints`. -/
def hnfColFuns (b ints : ℕ) : List Expr :=
  [hnfColF (b + 1) (b + 5) (b + 14)] ++ hnfFoldFuns (b + 1) (b + 17) ++ hnfSingleFuns (b + 5) ++
    mapFuns (b + 14) (b + 18) ++ [hnfEucF (b + 17) (b + 19) (ints + 14)] ++
    [hnfRowRedF (b + 19) (ints + 14)] ++ hnfRedFuns (b + 19) ints

theorem hnfColFuns_length (b ints : ℕ) : (hnfColFuns b ints).length = 28 := rfl

structure hnfColAt (P : Program) (b ints : ℕ) : Prop where
  entry : P.funs[b]? = some (hnfColF (b + 1) (b + 5) (b + 14))
  fold : hnfFoldAt P (b + 1) (b + 17) (b + 19) ints
  single : hnfSingleAt P (b + 5)
  map : P.HasAt (b + 14) (mapFuns (b + 14) (b + 18))
  rr : P.funs[b + 18]? = some (hnfRowRedF (b + 19) (ints + 14))
  red : hnfRedAt P (b + 19) ints

theorem hnfColAt_of {P : Program} {b ints : ℕ} (hI : linIntSpec P ints)
    (h : P.HasAt b (hnfColFuns b ints)) : hnfColAt P b ints := by
  have hred : hnfRedAt P (b + 19) ints := hnfRedAt_of hI (by simpa using h.block 19 rfl)
  have heuc : hnfEucAt P (b + 17) (b + 19) ints :=
    ⟨hred, by simpa using (h.block (gs := [hnfEucF (b + 17) (b + 19) (ints + 14)]) 17 rfl).single⟩
  exact
    { entry := (h.block (gs := [hnfColF (b + 1) (b + 5) (b + 14)]) 0 rfl).single
      fold := hnfFoldAt_of heuc (by simpa using h.block 1 rfl)
      single := hnfSingleAt_of (by simpa using h.block 5 rfl)
      map := by simpa using h.block 14 rfl
      rr := by simpa using (h.block (gs := [hnfRowRedF (b + 19) (ints + 14)]) 18 rfl).single
      red := hred }

theorem hnf_state_wt {n L X : ℕ} {m : ℤ} (hm : m.natAbs < 2 ^ L) (hm0 : 0 ≤ m)
    (hX : 1000 * ((n + 1) * (L + 1)) ≤ X) (st : List (Fin n → ℤ) × List (Fin n → ℤ))
    (h1 : ∀ v ∈ st.1, ∀ j, 0 ≤ v j ∧ v j ≤ m) (h2 : ∀ v ∈ st.2, ∀ j, 0 ≤ v j ∧ v j ≤ m)
    (hl1 : st.1.length ≤ 2 * n) (hl2 : st.2.length ≤ 2 * n) : (hnfStateVal st).wt ≤ 5 * (X * X) := by
  have w1 := hnf_rows_wt st.1 (fun v hv j => hnf_entry_lt (h1 v hv j).1 (h1 v hv j).2 hm) hl1 hX
  have w2 := hnf_rows_wt st.2 (fun v hv j => hnf_entry_lt (h2 v hv j).1 (h2 v hv j).2 hm) hl2 hX
  have w3 := wt_list2_le (hnfRowsVal st.1) (hnfRowsVal st.2)
  have e : (Val.list [hnfRowsVal st.1, hnfRowsVal st.2]).wt = (hnfStateVal st).wt := rfl
  obtain ⟨hXX, -, -⟩ := hnf_X_facts hX
  have h4 : 1 ≤ (n + 1) * (L + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  omega

def hnfColCost (X : ℕ) : ℕ :=
  hnfFoldCost X + 2 * hnfSingleCost X + 10 * hnfMapRedCost X + 1000 * (X * X + 1)

theorem hnfStep_eq {n : ℕ} (k : Fin n) (m : ℤ) (st : List (Fin n → ℤ) × List (Fin n → ℤ)) :
    hnfStep k m st = (st.1.map (fun h => hnfRed k m h (st.2.foldl (hnfFoldStep k m)
        (Pi.single k m, [])).1 (h k / (st.2.foldl (hnfFoldStep k m) (Pi.single k m, [])).1 k)) ++
      [(st.2.foldl (hnfFoldStep k m) (Pi.single k m, [])).1],
      (st.2.foldl (hnfFoldStep k m) (Pi.single k m, [])).2) := rfl

set_option maxHeartbeats 4000000 in
/-- **One column.** -/
theorem hnfCol_spec {P : Program} {b ints : ℕ} (h : hnfColAt P b ints) {n : ℕ} (k : Fin n)
    {m : ℤ} {L X : ℕ} (hm0 : 0 < m) (hmL : m.natAbs < 2 ^ L) (hX : 1000 * ((n + 1) * (L + 1)) ≤ X)
    (st : List (Fin n → ℤ) × List (Fin n → ℤ)) (hD : HnfDone k m st.1)
    (hW : ∀ g ∈ st.2, HnfWork k m g) (hlen : st.2.length ≤ n) :
    FunDet P b (.list [hnfColCtx k m n, hnfRowsVal st.1, hnfRowsVal st.2])
      (hnfStateVal (hnfStep k m st)) (hnfColCost X) := by
  rw [hnfStep_eq]
  set C := hnfColCtx k m n with hC
  set F := st.2.foldl (hnfFoldStep k m) (Pi.single k m, []) with hF
  have hkn := k.isLt
  have hsp := hnfSingle_spec h.single k m (hnf_colCtx_wt k.isLt hmL hX)
  have hfold := hnfFold_run h.fold k hm0 hmL hX st.2 hW hlen
  rw [← hF] at hfold
  obtain ⟨hFp, hFw, -⟩ := GI.Proved.hnfFold_spec k hm0 st.2 (Pi.single k m, [])
    (hnfPiv_single k hm0) (by simp) hW
  rw [← hF] at hFp hFw
  have hFl : F.2.length = st.2.length := by rw [hF, hnfFold_len]; simp
  have hDl := hD.1
  have hDb := hnfDone_bound hm0.le hD hkn.le
  have hmap := hnfMapRed_spec h.red h.rr h.map k hm0 hmL hX F.1 hFp st.1 hDb (by omega)
  set vs := [C, hnfRowsVal st.1, hnfRowsVal st.2] with hvs
  have da0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have da2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have dsing := Det.call da0 hsp
  have dacc := Det.mk2 dsing (Det.nil (P := P) (env := [Val.list vs]))
  have e0 : Val.list [linVecVal (Pi.single k m : Fin n → ℤ), .list []] =
    hnfAccVal ((Pi.single k m : Fin n → ℤ), []) := rfl
  rw [e0] at dacc
  have dfold := Det.call (Det.mk3 da0 da2 dacc) hfold
  set env2 := [Val.list vs, hnfAccVal F] with henv2
  have dF0 := Det.get' (Det.var' (P := P) (env := env2) (i := 1) rfl) (Det.nat 0)
    (show [linVecVal F.1, hnfRowsVal F.2][0]? = some (linVecVal F.1) from rfl)
  have dF1 := Det.get' (Det.var' (P := P) (env := env2) (i := 1) rfl) (Det.nat 1)
    (show [linVecVal F.1, hnfRowsVal F.2][1]? = some (hnfRowsVal F.2) from rfl)
  have db0 := Det.arg' (P := P) (vs := vs) (rest := [hnfAccVal F]) (j := 0) rfl
  have db1 := Det.arg' (P := P) (vs := vs) (rest := [hnfAccVal F]) (j := 1) rfl
  have dk := Det.get' db0 (Det.nat 0) (show [Val.nat k, encInt m, .nat n][0]? = some (.nat k) from rfl)
  have dm := Det.get' db0 (Det.nat 1)
    (show [Val.nat k, encInt m, .nat n][1]? = some (encInt m) from rfl)
  have dctx := Det.mk3 dk dm dF0
  have e1 : Val.list [.nat k, encInt m, linVecVal F.1] = hnfRedCtx k m F.1 := rfl
  rw [e1] at dctx
  have dmap := Det.call (Det.mk2 dctx db1) hmap
  set D' := st.1.map (fun h => hnfRed k m h F.1 (h k / F.1 k)) with hD'
  have e2 : hnfRowsVal D' = .list (D'.map linVecVal) := rfl
  rw [e2] at dmap
  have dsn := Det.snoc dmap dF0
  have dout := Det.mk2 dsn dF1
  have e3 : Val.list [.list (D'.map linVecVal ++ [linVecVal F.1]), hnfRowsVal F.2] =
      hnfStateVal (D' ++ [F.1], F.2) := by
    simp [hnfStateVal, hnfRowsVal]
  rw [e3] at dout
  apply FunDet.intro h.entry
  refine (Det.letE dfold dout).mono ?_
  -- weights
  have wsp := hsp.wt_lt
  have wmap := hmap.wt_lt
  have hFb : ∀ v ∈ F.2, ∀ j, 0 ≤ v j ∧ v j ≤ m := fun v hv j => hnfWork_bound hm0.le (hFw v hv) j
  have wF := hnf_acc_wt hmL hX F (hnfPiv_bound hFp) hFb (by omega)
  have wF0 : (linVecVal F.1).wt < (hnfAccVal F).wt := wt_le_wt_list (by simp [hnfAccVal])
  have wF1 : (hnfRowsVal F.2).wt < (hnfAccVal F).wt := wt_le_wt_list (by simp [hnfAccVal])
  have wC := hnf_colCtx_wt k.isLt hmL hX
  have wD := hnf_rows_wt (L := L) st.1
    (fun v hv j => hnf_entry_lt (hDb v hv j).1 (hDb v hv j).2 hmL) (by omega) hX
  have wW := hnf_rows_wt (L := L) st.2 (fun v hv j => hnf_entry_lt (hnfWork_bound hm0.le (hW v hv) j).1
    (hnfWork_bound hm0.le (hW v hv) j).2 hmL) (by omega) hX
  have wvs := wt_list3_le C (hnfRowsVal st.1) (hnfRowsVal st.2)
  have wA0 := hnf_acc_wt hmL hX ((Pi.single k m : Fin n → ℤ), [])
    (hnfPiv_bound (hnfPiv_single k hm0)) (by simp) (by simp)
  have w3 := wt_list3_le C (hnfRowsVal st.2) (hnfAccVal ((Pi.single k m : Fin n → ℤ), []))
  have w4 := wt_list2_le (linVecVal (Pi.single k m : Fin n → ℤ)) (.list [])
  have e4 : (Val.list [linVecVal (Pi.single k m : Fin n → ℤ), .list []]).wt =
    (hnfAccVal ((Pi.single k m : Fin n → ℤ), [])).wt := rfl
  have w5 := wt_list3_le (.nat k) (encInt m) (linVecVal F.1)
  have e5 : (Val.list [.nat k, encInt m, linVecVal F.1]).wt = (hnfRedCtx k m F.1).wt := rfl
  have wk : (Val.nat k).wt < C.wt := wt_le_wt_list (by simp [hC, hnfColCtx])
  have wm : (encInt m).wt < C.wt := wt_le_wt_list (by simp [hC, hnfColCtx])
  have w6 := wt_list2_le (hnfRedCtx k m F.1) (hnfRowsVal st.1)
  have w7 := wt_list_snoc_le (D'.map linVecVal) (linVecVal F.1)
  have w8 := wt_list2_le (.list (D'.map linVecVal ++ [linVecVal F.1])) (hnfRowsVal F.2)
  have e8 : (Val.list [.list (D'.map linVecVal ++ [linVecVal F.1]), hnfRowsVal F.2]).wt =
    (hnfStateVal (D' ++ [F.1], F.2)).wt := by rw [e3]
  have e9 : (Val.list [linVecVal F.1, hnfRowsVal F.2]).wt = (hnfAccVal F).wt := rfl
  have e10 : (Val.list vs).wt = (Val.list [C, hnfRowsVal st.1, hnfRowsVal st.2]).wt := rfl
  have e11 : (Val.list (D'.map linVecVal)).wt = (hnfRowsVal D').wt := rfl
  have ez : (Val.nat 0).wt = 2 := wt_nat_zero
  have eo : (Val.nat 1).wt = 3 := wt_nat_one
  have ec : (hnfColCtx k m n).wt = C.wt := rfl
  have hl : (Val.list []).wt ≤ 100 := by decide
  obtain ⟨hXX, hXL, hXn⟩ := hnf_X_facts hX
  unfold hnfColCost
  omega

end GI.Impl
