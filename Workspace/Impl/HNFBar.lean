import Workspace.Impl.HNFBarPiv

/-!
# Bareiss elimination, as a program

The state `[s, d, W]` of `GI.Proved.hnfBarIter` (`hnfBarVal`). Step `k` finds the pivot row `p`
(`Workspace/Impl/HNFBarPiv.lean`) and tabulates the update
`(W p k * W i j - W i k * W p j) / d` (`GI.Proved.hnfBarUpd`). All entries are minors of `A`, so
they stay below `2 ^ L` for an `L` fixed by the input.
-/

namespace GI.Impl

open GI.Cited GI.Lang
open GI.Proved (hnfPivot hnfBarUpd hnfBarStep hnfBarIter HnfBar HnfBarInv)

variable {r c : ℕ}

/-! ### Weights of matrices -/

theorem hnf_mat_wt {L X : ℕ} (W : Matrix (Fin r) (Fin c) ℤ) (h : ∀ i j, (W i j).natAbs < 2 ^ L)
    (hX : 1000 * ((r + c + 1) * (L + 1)) ≤ X) : (encIntMatrix W).wt ≤ X * X := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (r + c + 1) * (L + 1) := ⟨_, rfl⟩
  rw [← hQ] at hX
  have h1 := linWtList (vs := (List.finRange r).map fun i => linVecVal (W i)) (B := 45 * Q) (by
    intro v hv
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
    refine (hnf_vec_wt (W i) (h i)).trans (Nat.mul_le_mul_left _ ?_)
    rw [hQ]; exact Nat.mul_le_mul_right _ (by omega))
  simp only [List.length_map, List.length_finRange] at h1
  have e : (Val.list ((List.finRange r).map fun i => linVecVal (W i))).wt = (encIntMatrix W).wt := rfl
  have h2 : r + 1 ≤ Q := by rw [hQ]; exact (Nat.le_mul_of_pos_right _ (Nat.succ_pos L)).trans' (by omega)
  have h3 : r * (45 * Q) ≤ Q * (45 * Q) := Nat.mul_le_mul_right _ (by omega)
  have h4 : Q * (45 * Q) = 45 * (Q * Q) := by ring
  have h5 : (1000 * Q) * (1000 * Q) ≤ X * X := Nat.mul_le_mul hX hX
  have h6 : (1000 * Q) * (1000 * Q) = 1000000 * (Q * Q) := by ring
  have h7 : Q ≤ Q * Q := Nat.le_mul_self Q
  omega

/-! ### One entry of the update -/

/-- The context `[W, p, k, d]` of an update. -/
def hnfUpdCtx (W : Matrix (Fin r) (Fin c) ℤ) (p : ℕ) (k : ℕ) (d : ℤ) : Val :=
  .list [encIntMatrix W, .nat p, .nat k, encInt d]

/-- The argument of the update cell: `[[[ctx, r, c], i], j]`. -/
def hnfUpdArg (W : Matrix (Fin r) (Fin c) ℤ) (p k : ℕ) (d : ℤ) (i j : ℕ) : Val :=
  .list [.list [.list [hnfUpdCtx W p k d, .nat r, .nat c], .nat i], .nat j]

def hnfUpdCtxE : Expr := .get (.get (arg 0) (.nat 0)) (.nat 0)

def hnfUpdEntE (x y : Expr) : Expr := .get (.get (.get hnfUpdCtxE (.nat 0)) x) y

/-- Entry `(i, j)` of the update. -/
def hnfUpdCellF (ints : ℕ) : Expr :=
  .call (ints + 14) (mk2
    (.call (ints + 12) (mk2
      (.call (ints + 13) (mk2 (hnfUpdEntE (.get hnfUpdCtxE (.nat 1)) (.get hnfUpdCtxE (.nat 2)))
        (hnfUpdEntE (.get (arg 0) (.nat 1)) (arg 1))))
      (.call (ints + 13) (mk2 (hnfUpdEntE (.get (arg 0) (.nat 1)) (.get hnfUpdCtxE (.nat 2)))
        (hnfUpdEntE (.get hnfUpdCtxE (.nat 1)) (arg 1))))))
    (.get hnfUpdCtxE (.nat 3)))

def hnfUpdCellCost (Y : ℕ) : ℕ := 6 * linIntBinaryCost (1000 * (Y + 1)) + 10000 * (Y + 1)

set_option maxHeartbeats 4000000 in
theorem hnfUpdCell_spec {P : Program} {ints f : ℕ} (hI : linIntSpec P ints)
    (hf : P.funs[f]? = some (hnfUpdCellF ints)) (W : Matrix (Fin r) (Fin c) ℤ) (p : Fin r)
    (k : Fin c) (d : ℤ) (i : Fin r) (j : Fin c) {L Y : ℕ}
    (hW : ∀ i j, (W i j).natAbs < 2 ^ L) (hd : d.natAbs < 2 ^ L)
    (hY : (hnfUpdArg W p k d i j).wt + 100 * (L + 1) ≤ Y) :
    FunDet P f (hnfUpdArg W p k d i j) (encInt (hnfBarUpd W d p k i j)) (hnfUpdCellCost Y) := by
  set C := hnfUpdCtx W p k d with hC
  set A3 := Val.list [C, .nat r, .nat c] with hA3
  set vs := [Val.list [A3, .nat i], .nat j] with hvs
  have d0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have dj := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have di := Det.get' d0 (Det.nat 1) (show [A3, Val.nat i][1]? = some (.nat i) from rfl)
  have dC := Det.get' (Det.get' d0 (Det.nat 0) (show [A3, Val.nat i][0]? = some A3 from rfl))
    (Det.nat 0) (show [C, Val.nat r, .nat c][0]? = some C from rfl)
  have dW := Det.get' dC (Det.nat 0)
    (show [encIntMatrix W, .nat p, .nat k, encInt d][0]? = some (encIntMatrix W) from rfl)
  have dp := Det.get' dC (Det.nat 1)
    (show [encIntMatrix W, .nat p, .nat k, encInt d][1]? = some (.nat p) from rfl)
  have dk := Det.get' dC (Det.nat 2)
    (show [encIntMatrix W, .nat p, .nat k, encInt d][2]? = some (.nat k) from rfl)
  have dd := Det.get' dC (Det.nat 3)
    (show [encIntMatrix W, .nat p, .nat k, encInt d][3]? = some (encInt d) from rfl)
  have ent : ∀ (x : Fin r) (y : Fin c) {ex ey : Expr} {cx cy : ℕ},
      Det P [Val.list vs] ex (.nat x) cx → Det P [Val.list vs] ey (.nat y) cy →
      Det P [Val.list vs] (hnfUpdEntE ex ey) (encInt (W x y)) _ :=
    fun x y _ _ _ _ hx hy => Det.get' (Det.get' dW hx (hnf_mat_get W x)) hy (hnf_vec_get (W x) y)
  have dpk := ent p k dp dk
  have dij := ent i j di dj
  have dik := ent i k di dk
  have dpj := ent p j dp dj
  have dm1 := Det.call (Det.mk2 dpk dij) (hI.mul (W p k) (W i j))
  have dm2 := Det.call (Det.mk2 dik dpj) (hI.mul (W i k) (W p j))
  have ds := Det.call (Det.mk2 dm1 dm2) (hI.sub (W p k * W i j) (W i k * W p j))
  have dq := Det.call (Det.mk2 ds dd) (hI.quo (W p k * W i j - W i k * W p j) d)
  apply FunDet.intro hf
  refine dq.mono ?_
  -- weights
  have wq := (hI.quo (W p k * W i j - W i k * W p j) d).wt_lt
  have wvs : (Val.list vs).wt = (hnfUpdArg W p k d i j).wt := rfl
  have w1 : A3.wt < (Val.list [A3, .nat i]).wt := wt_le_wt_list (by simp)
  have w2 : (Val.list [A3, .nat i]).wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have w3 : C.wt < A3.wt := wt_le_wt_list (by simp [hA3])
  have w4 : (encIntMatrix W).wt < C.wt := wt_le_wt_list (by simp [hC, hnfUpdCtx])
  have w5 : (encInt d).wt < C.wt := wt_le_wt_list (by simp [hC, hnfUpdCtx])
  have w6 : (Val.nat p).wt < C.wt := wt_le_wt_list (by simp [hC, hnfUpdCtx])
  have w7 : (Val.nat k).wt < C.wt := wt_le_wt_list (by simp [hC, hnfUpdCtx])
  have w8 : (Val.nat i).wt < (Val.list [A3, .nat i]).wt := wt_le_wt_list (by simp)
  have w9 : (Val.nat j).wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have wr : ∀ x : Fin r, (linVecVal (W x)).wt < (encIntMatrix W).wt := hnf_row_wt_lt W
  have we : ∀ x : Fin r, ∀ y : Fin c, (encInt (W x y)).wt < (linVecVal (W x)).wt :=
    fun x y => linVecEntryWt (W x) y
  have wi : ∀ x y, (encInt (W x y)).wt ≤ 20 * (L + 1) := fun x y => hnf_wt_int (hW x y)
  have hm1 := hnf_abs_mul (hW p k) (hW i j)
  have hm2 := hnf_abs_mul (hW i k) (hW p j)
  have hs := hnf_abs_sub hm1 hm2
  have wm1 := hnf_wt_int hm1
  have wm2 := hnf_wt_int hm2
  have wsb := hnf_wt_int hs
  have wdd := hnf_wt_int hd
  have a1 := wt_list2_le (encInt (W p k)) (encInt (W i j))
  have a2 := wt_list2_le (encInt (W i k)) (encInt (W p j))
  have a3 := wt_list2_le (encInt (W p k * W i j)) (encInt (W i k * W p j))
  have a4 := wt_list2_le (encInt (W p k * W i j - W i k * W p j)) (encInt d)
  have c1 := linIntBinaryCost_mono (show (Val.list [encInt (W p k), encInt (W i j)]).wt ≤
    1000 * (Y + 1) by have := wi p k; have := wi i j; omega)
  have c2 := linIntBinaryCost_mono (show (Val.list [encInt (W i k), encInt (W p j)]).wt ≤
    1000 * (Y + 1) by have := wi i k; have := wi p j; omega)
  have c3 := linIntBinaryCost_mono (show (Val.list [encInt (W p k * W i j),
    encInt (W i k * W p j)]).wt ≤ 1000 * (Y + 1) by omega)
  have c4 := linIntBinaryCost_mono (show (Val.list [encInt (W p k * W i j - W i k * W p j),
    encInt d]).wt ≤ 1000 * (Y + 1) by omega)
  have hupd : hnfBarUpd W d p k i j = (W p k * W i j - W i k * W p j) / d := rfl
  have e0 : (Val.nat 0).wt = 2 := rfl
  have e1 : (Val.nat 1).wt = 3 := rfl
  have e2 : (Val.nat 2).wt = 4 := rfl
  have e3 : (Val.nat 3).wt = 4 := rfl
  have f1 : (Val.list ((List.finRange c).map fun y => encInt (W p y))).wt = (linVecVal (W p)).wt := rfl
  have f2 : (Val.list ((List.finRange c).map fun y => encInt (W i y))).wt = (linVecVal (W i)).wt := rfl
  have f3 : (Val.list [C, .nat r, .nat c]).wt = A3.wt := rfl
  have := wr p; have := wr i; have := we p k; have := we i j; have := we i k; have := we p j
  unfold hnfUpdCellCost
  omega

/-! ### Bounds on the entries -/

theorem hnf_natAbs_lt {z B : ℤ} {L : ℕ} (h : |z| ≤ B) (hB : B < 2 ^ L) : z.natAbs < 2 ^ L := by
  have h2 : (z.natAbs : ℤ) < 2 ^ L := by rw [Int.natCast_natAbs]; linarith
  exact_mod_cast h2

theorem hnf_fact_pow_le {T : ℤ} (hT : 1 ≤ T) {n N : ℕ} (h : n ≤ N) :
    (n.factorial : ℤ) * T ^ n ≤ N.factorial * T ^ N :=
  mul_le_mul (by exact_mod_cast Nat.factorial_le h) (pow_le_pow_right₀ hT h)
    (pow_nonneg (zero_le_one.trans hT) _) (by positivity)

/-- All entries of the Bareiss state, and the last pivot, are at most `(c + 1)! T ^ (c + 1)`. -/
theorem hnfBar_entry_le (A : Matrix (Fin r) (Fin c) ℤ) (hA : Function.Injective A.mulVec)
    (x : Fin r) (y : Fin c) {T : ℤ} (hT1 : 1 ≤ T) (hT : ∀ i j, |A i j| ≤ T) (k : ℕ) (hk : k ≤ c) :
    (∀ i j, |(hnfBarIter A k).W i j| ≤ (c + 1).factorial * T ^ (c + 1)) ∧
      |(hnfBarIter A k).d| ≤ (c + 1).factorial * T ^ (c + 1) := by
  obtain ⟨hlen, hlead, -, hW⟩ := GI.Proved.hnfBarIter_spec A hA k hk
  refine ⟨fun i j => ?_, ?_⟩
  · rw [hW i j]
    exact (GI.Proved.hnfMin_abs_le A hT _ _ _ _ _).trans (hnf_fact_pow_le hT1 (by omega))
  · rw [hlead x y]
    exact (GI.Proved.hnfMin_abs_le A hT _ _ _ _ _).trans (hnf_fact_pow_le hT1 (by omega))

/-- Under full rank every step finds a pivot. -/
theorem hnfBar_pivot (A : Matrix (Fin r) (Fin c) ℤ) (hA : Function.Injective A.mulVec)
    (k : ℕ) (hk : k < c) : ∃ p, hnfPivot (hnfBarIter A k).W ⟨k, hk⟩ = some p := by
  have h1 := (GI.Proved.hnfBarIter_spec A hA (k + 1) hk).1
  have h0 := (GI.Proved.hnfBarIter_spec A hA k hk.le).1
  have e : hnfBarIter A (k + 1) = hnfBarStep (hnfBarIter A k) ⟨k, hk⟩ := by
    simp [GI.Proved.hnfBarIter, hk]
  rw [e] at h1
  cases hp : hnfPivot (hnfBarIter A k).W ⟨k, hk⟩ with
  | none => simp [hnfBarStep, hp] at h1; omega
  | some p => exact ⟨p, rfl⟩

/-! ### One step -/

/-- The chosen rows. -/
def hnfSVal (s : List (Fin r)) : Val := .list (s.map fun p : Fin r => Val.nat (p : ℕ))

/-- The state `[s, d, W]`. -/
def hnfBarVal (st : HnfBar r c) : Val := .list [hnfSVal st.s, encInt st.d, encIntMatrix st.W]

/-- Step `k`, on `[[r, c, A], k, [s, d, W]]`. -/
def hnfBarStepF (piv tab : ℕ) : Expr :=
  .letE (.call piv (mk3 (.get (arg 2) (.nat 2)) (arg 1) (.get (arg 0) (.nat 0))))
    (.ite (.var 1)
      (.letE (.arith .sub (.var 1) (.nat 1))
        (mk3 (.snoc (.get (arg 2) (.nat 0)) (.var 2))
          (.get (.get (.get (arg 2) (.nat 2)) (.var 2)) (arg 1))
          (.call tab (mk3 (mk4 (.get (arg 2) (.nat 2)) (.var 2) (arg 1) (.get (arg 2) (.nat 1)))
            (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))))))
      (arg 2))

theorem hnf_sVal_wt {X : ℕ} (s : List (Fin r)) (hs : s.length ≤ c)
    (hX : 1000 * (r + c + 1) ≤ X) : (hnfSVal s).wt ≤ 3 * (X * X) := by
  have h1 := linWtList (vs := s.map fun p : Fin r => Val.nat (p : ℕ)) (B := r + 2) (by
    intro v hv
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hv
    have := wt_nat_le (p : ℕ); have := p.isLt; omega)
  simp only [List.length_map] at h1
  have e : (Val.list (s.map fun p : Fin r => Val.nat (p : ℕ))).wt = (hnfSVal s).wt := rfl
  have h2 : s.length * (r + 2) ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
  have h3 : 1000 * X ≤ X * X := Nat.mul_le_mul_right _ (by omega)
  omega

theorem hnf_barVal_wt {L X : ℕ} (st : HnfBar r c) (hs : st.s.length ≤ c)
    (hW : ∀ i j, (st.W i j).natAbs < 2 ^ L) (hd : st.d.natAbs < 2 ^ L)
    (hX : 1000 * ((r + c + 1) * (L + 1)) ≤ X) : (hnfBarVal st).wt ≤ 10 * (X * X) := by
  have hQ1 : r + c + 1 ≤ (r + c + 1) * (L + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos L)
  have hQ2 : L + 1 ≤ (r + c + 1) * (L + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have w1 := hnf_sVal_wt st.s hs (X := X) (by omega)
  have w2 := hnf_wt_int hd
  have w3 := hnf_mat_wt st.W hW hX
  have w4 := wt_list3_le (hnfSVal st.s) (encInt st.d) (encIntMatrix st.W)
  have e : (Val.list [hnfSVal st.s, encInt st.d, encIntMatrix st.W]).wt = (hnfBarVal st).wt := rfl
  have h3 : 1000 * X ≤ X * X := Nat.mul_le_mul_right _ (by omega)
  omega

def hnfBarStepCost (X : ℕ) : ℕ :=
  hnfPivCost (20 * (X * X)) + hnfTabCost (20 * (X * X)) (hnfUpdCellCost (100 * (X * X))) +
    100000 * (X * X + 1)

structure hnfBarStepAt (P : Program) (piv tab ints : ℕ) : Prop where
  hI : linIntSpec P ints
  hpiv : P.HasAt piv (hnfPivFuns piv)
  htab : hnfTabAt P tab (tab + 16)
  hcell : P.funs[tab + 16]? = some (hnfUpdCellF ints)

set_option maxHeartbeats 8000000 in
/-- **One step of Bareiss elimination**, when a pivot row exists. -/
theorem hnfBarStep_spec {P : Program} {piv tab ints f : ℕ} (h : hnfBarStepAt P piv tab ints)
    (hf : P.funs[f]? = some (hnfBarStepF piv tab)) (A : Matrix (Fin r) (Fin c) ℤ)
    (st : HnfBar r c) (k : Fin c) (p : Fin r) (hp : hnfPivot st.W k = some p) {L X : ℕ}
    (hs : st.s.length < c) (hA : ∀ i j, (A i j).natAbs < 2 ^ L)
    (hW : ∀ i j, (st.W i j).natAbs < 2 ^ L) (hd : st.d.natAbs < 2 ^ L)
    (hW' : ∀ i j, (hnfBarUpd st.W st.d p k i j).natAbs < 2 ^ L)
    (hX : 1000 * ((r + c + 1) * (L + 1)) ≤ X) (E : Val) (hE : E.wt ≤ 10 * (X * X)) :
    FunDet P f (.list [.list [.nat r, .nat c, encIntMatrix A, E], .nat k, hnfBarVal st])
      (hnfBarVal (hnfBarStep st k)) (hnfBarStepCost X) := by
  have hQ1 : r + c + 1 ≤ (r + c + 1) * (L + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos L)
  have hQ2 : L + 1 ≤ (r + c + 1) * (L + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hXX : 1000 * X ≤ X * X := Nat.mul_le_mul_right _ (by omega)
  have hstep : hnfBarStep st k = ⟨st.s ++ [p], st.W p k, hnfBarUpd st.W st.d p k⟩ := by
    simp [hnfBarStep, hp]
  rw [hstep]
  -- the pivot code
  have hcode : hnfPivCode st.W k r = p + 1 := by
    rcases hc : hnfPivCode st.W k r with _ | q
    · rw [hnfPivot_of_code_zero st.W k hc] at hp; cases hp
    · obtain ⟨hq, hq'⟩ := hnfPivot_of_code_succ st.W k hc
      rw [hq'] at hp
      have := congrArg Fin.val (Option.some.inj hp)
      simp at this
      omega
  set a := Val.list [.nat r, .nat c, encIntMatrix A, E] with ha
  set S := hnfBarVal st with hS
  set vs := [a, Val.nat k, S] with hvs
  -- weights used below
  have wA := hnf_mat_wt A hA hX
  have wW := hnf_mat_wt st.W hW hX
  have wW' := hnf_mat_wt (hnfBarUpd st.W st.d p k) hW' hX
  have wS := hnf_barVal_wt st hs.le hW hd hX
  have wa := wt_list4_le (.nat r) (.nat c) (encIntMatrix A) E
  have wr := wt_nat_le r
  have wc := wt_nat_le c
  have wk := wt_nat_le (k : ℕ)
  have hk := k.isLt
  have wvs := wt_list3_le a (.nat k) S
  -- the pivot call
  have d0 := fun rest => Det.arg' (P := P) (vs := vs) (rest := rest) (j := 0) rfl
  have d1 := fun rest => Det.arg' (P := P) (vs := vs) (rest := rest) (j := 1) rfl
  have d2 := fun rest => Det.arg' (P := P) (vs := vs) (rest := rest) (j := 2) rfl
  have dSW := fun rest => Det.get' (d2 rest) (Det.nat 2)
    (show [hnfSVal st.s, encInt st.d, encIntMatrix st.W][2]? = some (encIntMatrix st.W) from rfl)
  have dSs := fun rest => Det.get' (d2 rest) (Det.nat 0)
    (show [hnfSVal st.s, encInt st.d, encIntMatrix st.W][0]? = some (hnfSVal st.s) from rfl)
  have dSd := fun rest => Det.get' (d2 rest) (Det.nat 1)
    (show [hnfSVal st.s, encInt st.d, encIntMatrix st.W][1]? = some (encInt st.d) from rfl)
  have dar := fun rest => Det.get' (d0 rest) (Det.nat 0)
    (show [Val.nat r, .nat c, encIntMatrix A, E][0]? = some (.nat r) from rfl)
  have dac := fun rest => Det.get' (d0 rest) (Det.nat 1)
    (show [Val.nat r, .nat c, encIntMatrix A, E][1]? = some (.nat c) from rfl)
  have hpivY : (Val.list [encIntMatrix st.W, .nat k, .nat r]).wt + r ≤ 20 * (X * X) := by
    have := wt_list3_le (encIntMatrix st.W) (.nat k) (.nat r); omega
  have hpiv := hnfPiv_spec h.hpiv st.W k hpivY
  rw [hcode] at hpiv
  have dpiv := Det.call (Det.mk3 (dSW []) (d1 []) (dar [])) hpiv
  -- the found branch
  set env2 := [Val.list vs, Val.nat (p + 1)] with henv2
  have dv1 := Det.var' (P := P) (env := env2) (i := 1) rfl
  have dsub := Det.arith' (op := .sub) (z := p) dv1 (Det.nat 1) (by simp [GI.Machine.BinOp.eval])
  set env3 := env2 ++ [Val.nat p] with henv3
  have dv2 := Det.var' (P := P) (env := env3) (i := 2) rfl
  have ds' := Det.snoc (dSs [Val.nat (p + 1), .nat p]) dv2
  have dWpk := Det.get' (Det.get' (dSW [Val.nat (p + 1), .nat p]) dv2 (hnf_mat_get st.W p))
    (d1 [Val.nat (p + 1), .nat p]) (hnf_vec_get (st.W p) k)
  have dctx := Det.mk4 (dSW [Val.nat (p + 1), .nat p]) dv2 (d1 [Val.nat (p + 1), .nat p])
    (dSd [Val.nat (p + 1), .nat p])
  have ectx : Val.list [encIntMatrix st.W, .nat p, .nat k, encInt st.d] =
    hnfUpdCtx st.W p k st.d := rfl
  rw [ectx] at dctx
  have dA3 := Det.mk3 dctx (dar [Val.nat (p + 1), .nat p]) (dac [Val.nat (p + 1), .nat p])
  have wA3 : (Val.list [hnfUpdCtx st.W p k st.d, .nat r, .nat c]).wt ≤ 20 * (X * X) := by
    have := wt_list3_le (hnfUpdCtx st.W p k st.d) (.nat r) (.nat c)
    have := wt_list4_le (encIntMatrix st.W) (.nat p) (.nat k) (encInt st.d)
    have : (Val.list [encIntMatrix st.W, .nat p, .nat k, encInt st.d]).wt =
      (hnfUpdCtx st.W p k st.d).wt := rfl
    have := wt_nat_le (p : ℕ); have := p.isLt
    have := hnf_wt_int hd
    omega
  have htab := hnfTab_spec h.htab (hnfUpdCtx st.W p k st.d) r c
    (fun i j => encInt (hnfBarUpd st.W st.d p k i j)) (hnfUpdCellCost (100 * (X * X)))
    (20 * (X * X)) wA3 (by omega) (by omega) (fun i j => by
      apply hnfUpdCell_spec h.hI h.hcell st.W p k st.d i j hW hd
      have := wt_list2_le (.list [.list [hnfUpdCtx st.W p k st.d, .nat r, .nat c], .nat i]) (.nat j)
      have := wt_list2_le (.list [hnfUpdCtx st.W p k st.d, .nat r, .nat c]) (.nat i)
      have := wt_nat_le (i : ℕ); have := i.isLt; have := wt_nat_le (j : ℕ); have := j.isLt
      have : (Val.list [.list [.list [hnfUpdCtx st.W p k st.d, .nat r, .nat c], .nat i], .nat j]).wt
        = (hnfUpdArg st.W p k st.d i j).wt := rfl
      omega)
  have dtab := Det.call dA3 htab
  have dtrip := Det.mk3 ds' dWpk dtab
  have eout : Val.list [.list ((st.s.map fun p : Fin r => Val.nat (p : ℕ)) ++ [.nat p]), encInt (st.W p k),
      .list ((List.finRange r).map fun i => .list ((List.finRange c).map
        fun j => encInt (hnfBarUpd st.W st.d p k i j)))] =
      hnfBarVal ⟨st.s ++ [p], st.W p k, hnfBarUpd st.W st.d p k⟩ := by
    simp [hnfBarVal, hnfSVal, encIntMatrix]
  rw [eout] at dtrip
  have dfound := Det.letE dsub dtrip
  have dite := Det.ite_pos (e := arg 2) dv1 (by omega) dfound
  apply FunDet.intro hf
  refine (Det.letE dpiv dite).mono ?_
  -- cost
  have wout := hnf_barVal_wt (L := L) ⟨st.s ++ [p], st.W p k, hnfBarUpd st.W st.d p k⟩
    (by simp; omega) hW' (hW p k) hX
  have wtab := htab.wt_lt
  have wpv := hpiv.wt_lt
  have wp := wt_nat_le (p + 1)
  have wp' := wt_nat_le (p : ℕ)
  have hpr := p.isLt
  have e1 : (Val.list vs).wt = (Val.list [a, .nat k, S]).wt := rfl
  have e2 : (Val.list [Val.nat r, .nat c, encIntMatrix A, E]).wt = a.wt := rfl
  have e3 : (Val.list [hnfSVal st.s, encInt st.d, encIntMatrix st.W]).wt = S.wt := rfl
  have w5 : (encIntMatrix st.W).wt < S.wt := wt_le_wt_list (by simp [hS, hnfBarVal])
  have w6 : (hnfSVal st.s).wt < S.wt := wt_le_wt_list (by simp [hS, hnfBarVal])
  have w7 : (encInt st.d).wt < S.wt := wt_le_wt_list (by simp [hS, hnfBarVal])
  have w8 := hnf_row_wt_lt st.W p
  have w9 := linVecEntryWt (st.W p) k
  have w10 := wt_list_snoc_le (st.s.map fun p : Fin r => Val.nat (p : ℕ)) (.nat p)
  have e10 : (Val.list (st.s.map fun p : Fin r => Val.nat (p : ℕ))).wt = (hnfSVal st.s).wt := rfl
  have w11 := wt_list3_le (encIntMatrix st.W) (.nat k) (.nat r)
  have w12 := wt_list4_le (encIntMatrix st.W) (.nat p) (.nat k) (encInt st.d)
  have e12 : (Val.list [encIntMatrix st.W, .nat p, .nat k, encInt st.d]).wt =
    (hnfUpdCtx st.W p k st.d).wt := rfl
  have w13 := wt_list3_le (.list ((st.s.map fun p : Fin r => Val.nat (p : ℕ)) ++ [.nat p])) (encInt (st.W p k))
    (.list ((List.finRange r).map fun i => .list ((List.finRange c).map
        fun j => encInt (hnfBarUpd st.W st.d p k i j))))
  have e13 : (Val.list ((List.finRange r).map fun i => .list ((List.finRange c).map
        fun j => encInt (hnfBarUpd st.W st.d p k i j)))).wt =
      (encIntMatrix (hnfBarUpd st.W st.d p k)).wt := rfl
  have e14 : (Val.list ((List.finRange c).map fun j => encInt (st.W p j))).wt =
    (linVecVal (st.W p)).wt := rfl
  have wsn : (Val.list ((st.s.map fun p : Fin r => Val.nat (p : ℕ)) ++ [.nat p])).wt ≤ 3 * (X * X) + 2 * (r + 2) + 2 := by
    have := hnf_sVal_wt st.s hs.le (X := X) (by omega)
    omega
  have hdw := hnf_wt_int hd
  have hWpk := hnf_wt_int (hW p k)
  have ez : (Val.nat 0).wt = 2 := rfl
  have eo : (Val.nat 1).wt = 3 := rfl
  have et : (Val.nat 2).wt = 4 := rfl
  have hp1 : p + 1 ≤ X := by omega
  have hr1 : r ≤ X := by omega
  have e15 : (Val.list ((List.finRange r).map fun i => Val.list ((List.finRange c).map
      ((fun i j => encInt (hnfBarUpd st.W st.d p k i j)) i)))).wt =
      (encIntMatrix (hnfBarUpd st.W st.d p k)).wt := rfl
  have e16 : (Val.list [.list ((st.s.map fun p : Fin r => Val.nat (p : ℕ)) ++ [.nat p]),
      encInt (st.W p k), .list ((List.finRange r).map fun i => .list ((List.finRange c).map
        fun j => encInt (hnfBarUpd st.W st.d p k i j)))]).wt =
      (hnfBarVal ⟨st.s ++ [p], st.W p k, hnfBarUpd st.W st.d p k⟩).wt := by rw [eout]
  have e17 : S.wt = (hnfBarVal st).wt := rfl
  unfold hnfBarStepCost
  omega

/-! ### The loop -/

def hnfBarKE : Expr := .get (.var 0) (.nat 1)
def hnfBarAccE : Expr := .get (.var 0) (.nat 3)
/-- The number `1`. -/
def hnfOneE : Expr := mk2 (.nat 0) (mk1 (.nat 1))

/-- The entry, on `[r, c, A]`: run the loop on `[r, c, A, [[], 1, A]]`. -/
def hnfBarF (loop : ℕ) : Expr :=
  .call loop (mk4 (.get (.var 0) (.nat 0)) (.get (.var 0) (.nat 1)) (.get (.var 0) (.nat 2))
    (mk3 .nil hnfOneE (.get (.var 0) (.nat 2))))

def hnfBarFuns (b ints : ℕ) : List Expr :=
  [hnfBarF (b + 1)] ++ loopFuns (b + 1) hnfBarKE hnfBarAccE (hnfBarStepF (b + 4) (b + 7)) ++
    hnfPivFuns (b + 4) ++ hnfTabFuns (b + 7) (b + 23) ++ [hnfUpdCellF ints]

theorem hnfBarFuns_length (b ints : ℕ) : (hnfBarFuns b ints).length = 24 := rfl

structure hnfBarAt (P : Program) (b ints : ℕ) : Prop where
  entry : P.funs[b]? = some (hnfBarF (b + 1))
  loop : P.HasAt (b + 1) (loopFuns (b + 1) hnfBarKE hnfBarAccE (hnfBarStepF (b + 4) (b + 7)))
  step : hnfBarStepAt P (b + 4) (b + 7) ints

theorem hnfBarAt_of {P : Program} {b ints : ℕ} (hI : linIntSpec P ints)
    (h : P.HasAt b (hnfBarFuns b ints)) : hnfBarAt P b ints where
  entry := (h.block (gs := [hnfBarF (b + 1)]) 0 rfl).single
  loop := by simpa using h.block 1 rfl
  step :=
    { hI := hI
      hpiv := by simpa using h.block 4 rfl
      htab := hnfTabAt_of (by simpa using h.block 7 rfl)
      hcell := by simpa using (h.block (gs := [hnfUpdCellF ints]) 23 rfl).single }

def hnfBarCost (X : ℕ) : ℕ := X * hnfBarStepCost X + 2 * (1000 * (X + 1) * (50 * (X * X) + 50))

theorem hnfBarVal_zero (A : Matrix (Fin r) (Fin c) ℤ) :
    Val.list [.list [], .list [.nat 0, .list [.nat 1]], encIntMatrix A] = hnfBarVal (hnfBarIter A 0) := by
  simp only [hnfBarVal, hnfSVal, GI.Proved.hnfBarIter, List.map_nil]
  rfl

set_option maxHeartbeats 8000000 in
/-- **Bareiss elimination.** -/
theorem hnfBar_spec {P : Program} {b ints : ℕ} (h : hnfBarAt P b ints)
    (A : Matrix (Fin r) (Fin c) ℤ) (hA : Function.Injective A.mulVec) (x : Fin r) (y : Fin c)
    {T : ℤ} (hT1 : 1 ≤ T) (hT : ∀ i j, |A i j| ≤ T) {L X : ℕ}
    (hB : ((c + 1).factorial : ℤ) * T ^ (c + 1) < 2 ^ L)
    (hX : 1000 * ((r + c + 1) * (L + 1)) ≤ X) :
    FunDet P b (.list [.nat r, .nat c, encIntMatrix A]) (hnfBarVal (hnfBarIter A c))
      (hnfBarCost X) := by
  have hQ1 : r + c + 1 ≤ (r + c + 1) * (L + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos L)
  have hQ2 : L + 1 ≤ (r + c + 1) * (L + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hXX : 1000 * X ≤ X * X := Nat.mul_le_mul_right _ (by omega)
  have hbd := hnfBar_entry_le A hA x y hT1 hT
  have hAL : ∀ i j, (A i j).natAbs < 2 ^ L := fun i j =>
    hnf_natAbs_lt ((hT i j).trans (by simpa using hnf_fact_pow_le hT1 (show 1 ≤ c + 1 by omega)))
      hB
  have hst : ∀ k, k ≤ c → (∀ i j, ((hnfBarIter A k).W i j).natAbs < 2 ^ L) ∧
      ((hnfBarIter A k).d).natAbs < 2 ^ L ∧ (hnfBarIter A k).s.length ≤ c := fun k hk =>
    ⟨fun i j => hnf_natAbs_lt ((hbd k hk).1 i j) hB, hnf_natAbs_lt (hbd k hk).2 hB,
      by rw [(GI.Proved.hnfBarIter_spec A hA k hk).1]; exact hk⟩
  have hstw : ∀ k, k ≤ c → (hnfBarVal (hnfBarIter A k)).wt ≤ 10 * (X * X) := fun k hk =>
    hnf_barVal_wt _ (hst k hk).2.2 (hst k hk).1 (hst k hk).2.1 hX
  set S0 := hnfBarVal (hnfBarIter A 0) with hS0
  set a := Val.list [.nat r, .nat c, encIntMatrix A, S0] with ha
  have wA := hnf_mat_wt A hAL hX
  have wS0 : S0.wt ≤ 10 * (X * X) := hstw 0 (Nat.zero_le _)
  have eS0 : S0.wt = (hnfBarVal (hnfBarIter A 0)).wt := rfl
  have wa : a.wt ≤ 30 * (X * X) := by
    have := wt_list4_le (.nat r) (.nat c) (encIntMatrix A) S0
    have := wt_nat_le r; have := wt_nat_le c
    have e : (Val.list [.nat r, .nat c, encIntMatrix A, S0]).wt = a.wt := rfl
    omega
  have hk : Det P [a] hnfBarKE (.nat c) _ :=
    Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat 1)
      (show [Val.nat r, .nat c, encIntMatrix A, S0][1]? = some (.nat c) from rfl)
  have hacc : Det P [a] hnfBarAccE S0 _ :=
    Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat 3)
      (show [Val.nat r, .nat c, encIntMatrix A, S0][3]? = some S0 from rfl)
  have hl := loopBdd_spec h.loop hk hacc (M := 10 * (X * X))
    (Inv := fun i acc => acc = hnfBarVal (hnfBarIter A i)) (D := fun _ => hnfBarStepCost X)
    (by
      have := wt_nat_le c
      have w1 : S0.wt < a.wt := wt_le_wt_list (by simp [ha])
      have w2 : (Val.nat c).wt < a.wt := wt_le_wt_list (by simp [ha])
      have e : (Val.list [Val.nat r, .nat c, encIntMatrix A, S0]).wt = a.wt := rfl
      have e1 : (Val.nat 1).wt = 3 := rfl
      have e3 : (Val.nat 3).wt = 4 := rfl
      omega)
    rfl
    (fun i acc hi hacc => by rw [hacc]; exact hstw i hi)
    (by
      intro i acc hi hacc
      subst hacc
      obtain ⟨p, hp⟩ := hnfBar_pivot A hA i hi
      have hs := GI.Proved.hnfBarIter_spec A hA i hi.le
      have hW' : ∀ i' j, (hnfBarUpd (hnfBarIter A i).W (hnfBarIter A i).d p ⟨i, hi⟩ i' j).natAbs
          < 2 ^ L := by
        have e : hnfBarIter A (i + 1) = hnfBarStep (hnfBarIter A i) ⟨i, hi⟩ := by
          simp [GI.Proved.hnfBarIter, hi]
        have h1 := (hst (i + 1) hi).1
        rw [e] at h1
        simpa [hnfBarStep, hp] using h1
      have hspec := hnfBarStep_spec h.step (h.loop.loopFuns_step) A (hnfBarIter A i) ⟨i, hi⟩ p hp
        (by rw [hs.1]; exact hi) hAL (hst i hi.le).1 (hst i hi.le).2.1 hW' hX S0 wS0
      obtain ⟨body, hb, hd⟩ := hspec
      rw [h.loop.loopFuns_step] at hb
      cases hb
      refine hd.mono fun w cst hw => ⟨?_, ?_⟩
      · rw [hw.1]
        simp [GI.Proved.hnfBarIter, hi]
      · have := hw.2
        beta_reduce
        omega)
  have hl' : FunDet P (b + 1) a (hnfBarVal (hnfBarIter A c))
      (c * hnfBarStepCost X + loopModK * (c + 1) * (a.wt + c + 10 * (X * X) + 1)) :=
    hl.mono fun w cst hw => ⟨hw.1, by simpa using hw.2⟩
  -- the entry
  have dv := Det.var' (P := P) (env := [Val.list [.nat r, .nat c, encIntMatrix A]]) (i := 0) rfl
  have dr := Det.get' dv (Det.nat 0)
    (show [Val.nat r, .nat c, encIntMatrix A][0]? = some (.nat r) from rfl)
  have dc := Det.get' dv (Det.nat 1)
    (show [Val.nat r, .nat c, encIntMatrix A][1]? = some (.nat c) from rfl)
  have dA := Det.get' dv (Det.nat 2)
    (show [Val.nat r, .nat c, encIntMatrix A][2]? = some (encIntMatrix A) from rfl)
  have done : Det P [Val.list [.nat r, .nat c, encIntMatrix A]] hnfOneE
      (.list [.nat 0, .list [.nat 1]]) _ := Det.mk2 (Det.nat 0) (Det.mk1 (Det.nat 1))
  have dinit := Det.mk3 Det.nil done dA
  rw [hnfBarVal_zero] at dinit
  have dout := Det.call (Det.mk4 dr dc dA dinit) hl'
  apply FunDet.intro h.entry
  refine dout.mono ?_
  have wo := hstw c le_rfl
  have w1 := wt_list3_le (.nat r) (.nat c) (encIntMatrix A)
  have w2 := wt_list4_le (.nat r) (.nat c) (encIntMatrix A) S0
  have e2 : (Val.list [.nat r, .nat c, encIntMatrix A, S0]).wt = a.wt := rfl
  have e2' : (Val.list [.nat r, .nat c, encIntMatrix A, hnfBarVal (hnfBarIter A 0)]).wt = a.wt := rfl
  have wr := wt_nat_le r
  have wc := wt_nat_le c
  have h5 : c * hnfBarStepCost X ≤ X * hnfBarStepCost X := Nat.mul_le_mul_right _ (by omega)
  have h6 : loopModK * (c + 1) * (a.wt + c + 10 * (X * X) + 1) ≤
      1000 * (X + 1) * (50 * (X * X) + 50) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have h7 : 1000 * (50 * (X * X) + 50) ≤ 1000 * (X + 1) * (50 * (X * X) + 50) :=
    Nat.mul_le_mul_right _ (by omega)
  have w3 : (Val.list [Val.nat 1]).wt ≤ 20 := by decide
  have w4 : (Val.list [Val.nat 0, .list [.nat 1]]).wt ≤ 30 := by decide
  have w5 : (Val.list []).wt ≤ 4 := by decide
  have ez : (Val.nat 0).wt = 2 := rfl
  have eo : (Val.nat 1).wt = 3 := rfl
  have et : (Val.nat 2).wt = 4 := rfl
  unfold hnfBarCost
  omega

end GI.Impl
