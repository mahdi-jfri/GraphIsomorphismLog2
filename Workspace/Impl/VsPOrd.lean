module

public import Workspace.Impl.VsPCtx
public import Workspace.Impl.VsQPow

@[expose] public section

/-!
# Powers of permutations, and an element of prime order
modulo `L`

* `vsPPowFuns`, `vsPPow_spec`: binary powers of permutations.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

/-- The product of permutations in the form the binary power wants: on `[c, x, y]`, `x * y`. -/
def vsPMulWF (comp : ℕ) : Expr := .call comp (mk2 (arg 1) (arg 2))

/-- The binary power of permutations at base `b` (6 functions): on `[c, a, e, r]`, `a^e * r`. -/
def vsPPowFuns (b : ℕ) : List Expr := [vsQPowF b (b + 1), vsPMulWF (b + 2)] ++ composeFuns (b + 2)

theorem vsPPowFuns_length (b : ℕ) : (vsPPowFuns b).length = 6 := rfl

/-- The cost of a product of permutations through the wrapper. -/
def vsPMulCost (n : ℕ) : ℕ := permK * (n + 1) ^ 3 + 1000 * (n + 1) ^ 2

theorem vsPMulW_spec {P : Program} {f comp : ℕ} {n : ℕ} (hf : P.funs[f]? = some (vsPMulWF comp))
    (hc : P.HasAt comp (composeFuns comp)) (x y : Perm (Fin n)) :
    FunDet P f (.list [.nat 0, encPerm x, encPerm y]) (encPerm (x * y)) (vsPMulCost n) := by
  have a1 := Det.arg' (P := P) (vs := [.nat 0, encPerm x, encPerm y]) (rest := []) (j := 1) rfl
  have a2 := Det.arg' (P := P) (vs := [.nat 0, encPerm x, encPerm y]) (rest := []) (j := 2) rfl
  refine FunDet.intro hf ((Det.call (Det.mk2 a1 a2) (compose_spec hc x y)).mono ?_)
  have w1 := wt_encPerm_le x
  have w2 := wt_encPerm_le y
  have w3 := wt_encPerm_le (x * y)
  have w4 := wt_list3_le (.nat 0) (encPerm x) (encPerm y)
  have w5 := wt_list2_le (encPerm x) (encPerm y)
  have w0 : (Val.nat 0).wt = 2 := rfl
  have w6 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [vsPMulCost]
  omega

/-- The cost of a power with exponent `e`. -/
def vsPPowCost (n e : ℕ) : ℕ :=
  (e.bits.length + 1) * vsQPowUnit 2 (4 * (n + 1) ^ 2) (vsPMulCost n) e.bits.length

/-- **Binary powers of permutations.** -/
theorem vsPPow_spec {P : Program} {b n : ℕ} (h : P.HasAt b (vsPPowFuns b)) (a r : Perm (Fin n))
    (e : ℕ) :
    FunDet P b (.list [.nat 0, encPerm a, .nat e, encPerm r]) (encPerm (a ^ e * r))
      (vsPPowCost n e) := by
  have h0 : P.funs[b]? = some (vsQPowF b (b + 1)) := h.get (j := 0) (by simp [vsPPowFuns])
  have h1 : P.funs[b + 1]? = some (vsPMulWF (b + 2)) := h.get (j := 1) (by simp [vsPPowFuns])
  have hc : P.HasAt (b + 2) (composeFuns (b + 2)) := h.block 2 rfl
  exact vsQPow_spec h0 (encPerm (n := n)) (.nat 0) (fun x => wt_encPerm_le x)
    (fun x y => vsPMulW_spec h1 hc x y) e a r

/-- The cost of a power, for exponents with at most `k` bits. -/
theorem vsPPowCost_le {n e k : ℕ} (he : e.bits.length ≤ k) :
    vsPPowCost n e ≤ 10 ^ 6 * (k + 1) ^ 2 * (n + 1) ^ 3 := by
  unfold vsPPowCost vsQPowUnit vsPMulCost permK
  have q1 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q0 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h1 : 3 * (30000 * (n + 1) ^ 3 + 1000 * (n + 1) ^ 2) +
      1000 * (2 + 4 * (n + 1) ^ 2 + e.bits.length + 10) ≤ 200000 * (k + 1) * (n + 1) ^ 3 := by
    have : e.bits.length + 12 ≤ 12 * (k + 1) * (n + 1) ^ 2 := by
      have : 1 ≤ (k + 1) * (n + 1) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    have : (n + 1) ^ 3 ≤ (k + 1) * (n + 1) ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
    have : (n + 1) ^ 2 ≤ (k + 1) * (n + 1) ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
    have : (k + 1) * (n + 1) ^ 2 ≤ (k + 1) * (n + 1) ^ 3 := Nat.mul_le_mul_left _ q1
    nlinarith
  calc (e.bits.length + 1) * (3 * (30000 * (n + 1) ^ 3 + 1000 * (n + 1) ^ 2) +
        1000 * (2 + 4 * (n + 1) ^ 2 + e.bits.length + 10))
      ≤ (k + 1) * (200000 * (k + 1) * (n + 1) ^ 3) := Nat.mul_le_mul (by omega) h1
    _ ≤ 10 ^ 6 * (k + 1) ^ 2 * (n + 1) ^ 3 := by nlinarith

theorem vsP_bits_le (e : ℕ) : e.bits.length ≤ e := by
  rw [Nat.size_eq_bits_len]; exact Nat.size_le.2 Nat.lt_two_pow_self

/-! ### The walk: the first `q` with `y^q ∈ L` -/

variable {I : VecStabInst}

/-- One step of the walk: while not found, test `y^(2+i)`; if it lies in `L`, stop with
`(y, 2 + i)`, else go on with `y^(2+i)`. -/
def vsPWStep {n : ℕ} (ib : Perm (Fin n) → Bool) (i : ℕ) (a : ℕ × Perm (Fin n) × ℕ) :
    ℕ × Perm (Fin n) × ℕ :=
  if a.1 = 0 then (if ib (a.2.1 ^ (2 + i)) then (1, a.2.1, 2 + i) else (0, a.2.1 ^ (2 + i), 0))
  else a

/-- The walk over `i < k` from `x`. -/
def vsPWalk {n : ℕ} (ib : Perm (Fin n) → Bool) (k : ℕ) (x : Perm (Fin n)) : ℕ × Perm (Fin n) × ℕ :=
  (List.range k).foldl (fun a i => vsPWStep ib i a) (0, x, 0)

/-- The value of an accumulator of the walk. -/
def vsPAccV {n : ℕ} (a : ℕ × Perm (Fin n) × ℕ) : Val := .list [.nat a.1, encPerm a.2.1, .nat a.2.2]

/-- The step of the walk, on `[ctx, i, acc]`. -/
def vsPWStepE (pow inl : ℕ) : Expr :=
  .ite (.get (arg 2) (.nat 0)) (arg 2)
    (.letE (.call pow (mk4 (.nat 0) (.get (arg 2) (.nat 1)) (.arith .add (.nat 1) (arg 1))
        (.get (arg 2) (.nat 1))))
      (.ite (.call inl (mk2 (arg 0) (.var 1)))
        (mk3 (.nat 1) (.get (arg 2) (.nat 1)) (.arith .add (.nat 2) (arg 1)))
        (mk3 (.nat 0) (.var 1) (.nat 0))))

theorem vsPWStep_fst {n : ℕ} (ib : Perm (Fin n) → Bool) (i : ℕ) (a : ℕ × Perm (Fin n) × ℕ)
    (ha : a.1 = 0 ∨ a.1 = 1) : (vsPWStep ib i a).1 = 0 ∨ (vsPWStep ib i a).1 = 1 := by
  unfold vsPWStep; split_ifs <;> simp_all

/-- The cost of a step of the walk. -/
def vsPWStepCost (Cφ N W : ℕ) : ℕ := vsPInLPCost Cφ N W + 10 ^ 8 * (N + 1) ^ 5 + 400 * W

set_option maxHeartbeats 2000000 in
theorem vsPWStep_spec {P : Program} {g pow inl phi Cφ N W : ℕ}
    (hg : P.funs[g]? = some (vsPWStepE pow inl)) (hpow : P.HasAt pow (vsPPowFuns pow))
    (hinl : P.HasAt inl (vsPInLPFuns inl phi))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {i : ℕ} (hi : i + 2 ≤ N)
    {a : ℕ × Perm (Fin I.n) × ℕ} (ha : a.2.1 ∈ gens I.gs) (hq : a.2.2 ≤ N) (hf1 : a.1 ≤ 1) :
    FunDet P g (.list [vsPCtx I ws' cs rows hs, .nat i, vsPAccV a])
      (vsPAccV (vsPWStep (vsPInLB I ws' cs rows) i a)) (vsPWStepCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set y := a.2.1
  have eA : vsPAccV a = .list [.nat a.1, encPerm y, .nat a.2.2] := rfl
  set vs := [C, Val.nat i, vsPAccV a] with hvs
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have a2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have d0 := Det.get' a2 (Det.nat 0) (show [Val.nat a.1, encPerm y, .nat a.2.2][0]? = some (.nat a.1)
    from rfl)
  -- weights
  have hn := H.n
  have wC : C.wt ≤ W := H.cw
  have wy := wt_encPerm_le y
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have wA := wt_list3_le (.nat a.1) (encPerm y) (.nat a.2.2)
  have wvs := wt_list3_le C (.nat i) (vsPAccV a)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have wi := wt_nat_le i
  have wq := wt_nat_le a.2.2
  have wf := wt_nat_le a.1
  have eAw : (vsPAccV a).wt = (Val.list [.nat a.1, encPerm y, .nat a.2.2]).wt := rfl
  apply FunDet.intro hg
  by_cases hf : a.1 = 0
  · -- not found yet
    rw [hf] at d0
    have dy := Det.get' a2 (Det.nat 1) (show [Val.nat a.1, encPerm y, .nat a.2.2][1]? =
      some (encPerm y) from rfl)
    have de := Det.arith' (op := .add) (Det.nat (P := P) (env := [.list vs]) 1) a1 rfl
    have dz := Det.call (Det.mk4 (Det.nat 0) dy de dy) (vsPPow_spec hpow y y (1 + i))
    have ez : y ^ (1 + i) * y = y ^ (2 + i) := by rw [← pow_succ]; ring_nf
    rw [ez] at dz
    have hz : y ^ (2 + i) ∈ gens I.gs := pow_mem ha _
    set env := [Val.list vs, encPerm (y ^ (2 + i))]
    have b0 := Det.arg' (P := P) (vs := vs) (rest := [encPerm (y ^ (2 + i))]) (j := 0) rfl
    have b1 := Det.arg' (P := P) (vs := vs) (rest := [encPerm (y ^ (2 + i))]) (j := 1) rfl
    have b2 := Det.arg' (P := P) (vs := vs) (rest := [encPerm (y ^ (2 + i))]) (j := 2) rfl
    have bz := Det.var' (P := P) (env := env) (i := 1) rfl
    have dt := Det.call (Det.mk2 b0 bz) (vsPInLP_spec hinl hphi H hz)
    have by' := Det.get' b2 (Det.nat 1) (show [Val.nat a.1, encPerm y, .nat a.2.2][1]? =
      some (encPerm y) from rfl)
    have dT := Det.mk3 (Det.nat (P := P) (env := env) 1) by'
      (Det.arith' (op := .add) (Det.nat (P := P) (env := env) 2) b1 rfl)
    have dF := Det.mk3 (Det.nat (P := P) (env := env) 0) bz (Det.nat (P := P) (env := env) 0)
    have hpc := vsPPowCost_le (n := I.n) (e := 1 + i) (k := N) (by
      have := vsP_bits_le (1 + i); omega)
    have hn5 : (I.n + 1) ^ 3 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hpc' : 10 ^ 6 * (N + 1) ^ 2 * (I.n + 1) ^ 3 ≤ 10 ^ 6 * (N + 1) ^ 5 := by
      calc 10 ^ 6 * (N + 1) ^ 2 * (I.n + 1) ^ 3 ≤ 10 ^ 6 * (N + 1) ^ 2 * (N + 1) ^ 3 :=
            Nat.mul_le_mul_left _ hn5
        _ = 10 ^ 6 * (N + 1) ^ 5 := by ring
    have wz := wt_encPerm_le (y ^ (2 + i))
    have w4 := wt_list4_le (.nat 0) (encPerm y) (.nat (1 + i)) (encPerm y)
    have w2 := wt_list2_le C (encPerm (y ^ (2 + i)))
    have w3t := wt_list3_le (.nat 1) (encPerm y) (.nat (2 + i))
    have w3f := wt_list3_le (.nat 0) (encPerm (y ^ (2 + i))) (.nat 0)
    have wb := wt_boolVal_le (vsPInLB I ws' cs rows (y ^ (2 + i)))
    have w0 : (Val.nat 0).wt = 2 := rfl
    have w1 : (Val.nat 1).wt ≤ 3 := wt_nat_le 1
    have wi1 := wt_nat_le (1 + i)
    have wi2 := wt_nat_le (2 + i)
    have hW1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hW2 : (N + 1) ^ 2 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
    have hLP : 0 ≤ vsPInLPCost Cφ N W := Nat.zero_le _
    have ev2 : (Val.list vs).wt = (Val.list [C, Val.nat i, vsPAccV a]).wt := rfl
    have ea1 : GI.Machine.BinOp.add.eval 1 i = 1 + i := rfl
    have ea2 : GI.Machine.BinOp.add.eval 2 i = 2 + i := rfl
    have wT := wt_boolVal_le true
    have wF := wt_boolVal_le false
    simp only [ea1, ea2] at *
    cases hb : vsPInLB I ws' cs rows (y ^ (2 + i)) with
    | true =>
      rw [hb] at dt
      have ev : vsPAccV (vsPWStep (vsPInLB I ws' cs rows) i a) =
          .list [.nat 1, encPerm y, .nat (2 + i)] := by
        simp only [vsPWStep, hf, if_true,
          show vsPInLB I ws' cs rows (a.2.1 ^ (2 + i)) = true from hb]; rfl
      rw [ev]
      refine (Det.ite_zero d0 (Det.letE dz (Det.ite_pos dt (by simp) dT))).mono ?_
      unfold vsPWStepCost
      omega
    | false =>
      rw [hb] at dt
      have ev : vsPAccV (vsPWStep (vsPInLB I ws' cs rows) i a) =
          .list [.nat 0, encPerm (y ^ (2 + i)), .nat 0] := by
        simp only [vsPWStep, hf, if_true,
          show vsPInLB I ws' cs rows (a.2.1 ^ (2 + i)) = false from hb]; rfl
      rw [ev]
      have dt0 : Det P env (.call inl (mk2 (arg 0) (.var 1))) (.nat 0) _ := dt
      refine (Det.ite_zero d0 (Det.letE dz (Det.ite_zero dt0 dF))).mono ?_
      unfold vsPWStepCost
      omega
  · -- found: keep the accumulator
    have ev : vsPWStep (vsPInLB I ws' cs rows) i a = a := by simp [vsPWStep, hf]
    rw [ev]
    have hpos : a.1 ≠ 0 := hf
    refine (Det.ite_pos d0 hpos a2).mono ?_
    have hW1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hW2 : (N + 1) ^ 2 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
    have ev2 : (Val.list vs).wt = (Val.list [C, Val.nat i, vsPAccV a]).wt := rfl
    unfold vsPWStepCost
    omega

/-! ### What the walk computes -/

section WalkMath

variable {n : ℕ} (ib : Perm (Fin n) → Bool)

theorem vsPWalk_zero (x : Perm (Fin n)) : vsPWalk ib 0 x = (0, x, 0) := rfl

theorem vsPWalk_succ (k : ℕ) (x : Perm (Fin n)) :
    vsPWalk ib (k + 1) x = vsPWStep ib k (vsPWalk ib k x) := by
  simp [vsPWalk, List.range_succ, List.foldl_append]

/-- The invariant of the walk. -/
theorem vsPWalk_inv {x : Perm (Fin n)} (hx : ib x = false) (k : ℕ) :
    ((vsPWalk ib k x).1 = 0 ∨ (vsPWalk ib k x).1 = 1) ∧
      (vsPWalk ib k x).2.1 ∈ Subgroup.zpowers x ∧ ib (vsPWalk ib k x).2.1 = false ∧
      (vsPWalk ib k x).2.2 ≤ k + 1 ∧
      ((vsPWalk ib k x).1 = 0 → (vsPWalk ib k x).2.1 = x ^ (k + 1).factorial) ∧
      ((vsPWalk ib k x).1 = 1 → ib ((vsPWalk ib k x).2.1 ^ (vsPWalk ib k x).2.2) = true ∧
        2 ≤ (vsPWalk ib k x).2.2) := by
  induction k with
  | zero => simp [vsPWalk_zero, hx, Subgroup.mem_zpowers]
  | succ k ih =>
    obtain ⟨h01, hz, hib, hq, h0, h1⟩ := ih
    rw [vsPWalk_succ]
    set a := vsPWalk ib k x
    unfold vsPWStep
    by_cases ha : a.1 = 0
    · rw [if_pos ha]
      have hy := h0 ha
      by_cases hb : ib (a.2.1 ^ (2 + k)) = true
      · rw [if_pos hb]
        exact ⟨Or.inr rfl, hz, hib, by simp; omega, by simp, fun _ => ⟨hb, by simp⟩⟩
      · rw [if_neg hb]
        refine ⟨Or.inl rfl, Subgroup.pow_mem _ hz _, by simpa using hb, by simp, fun _ => ?_,
          by simp⟩
        simp only
        rw [hy, ← pow_mul, show k + 1 + 1 = k + 2 from rfl, Nat.factorial_succ (k + 1),
          mul_comm]
        ring_nf
    · rw [if_neg ha]
      have ha1 : a.1 = 1 := by omega
      exact ⟨h01, hz, hib, by omega, fun h => absurd h ha, h1⟩

/-- **The walk finds a `q`.** With `ib 1 = true`, `ib x = false` and `n ≥ 2`, after `n - 1`
steps the walk has stopped. -/
theorem vsPWalk_found {x : Perm (Fin n)} (hx : ib x = false) (h1 : ib 1 = true) (hn : 2 ≤ n) :
    (vsPWalk ib (n - 1) x).1 = 1 := by
  obtain ⟨h01, -, hib, -, h0, -⟩ := vsPWalk_inv ib hx (n - 1)
  rcases h01 with h | h
  · exfalso
    have e := h0 h
    rw [show n - 1 + 1 = n by omega] at e
    have hpow : x ^ n.factorial = 1 := by
      have := pow_card_eq_one (G := Perm (Fin n)) (x := x)
      rwa [Fintype.card_perm, Fintype.card_fin] at this
    rw [e, hpow, h1] at hib
    exact Bool.noConfusion hib
  · exact h

end WalkMath

/-! ### The walk as a program -/

/-- The cost of the walk over `k ≤ N` steps. -/
def vsPWalkCost (Cφ N W : ℕ) : ℕ :=
  (N + 1) * vsPWStepCost Cφ N W + 2 * 10 ^ 5 * (N + 1) * (W + (N + 1) ^ 2)

theorem vsPWalk_spec {P : Program} {b g pow inl phi Cφ N W : ℕ}
    (hb : P.HasAt b (iterFuns b g))
    (hg : P.funs[g]? = some (vsPWStepE pow inl)) (hpow : P.HasAt pow (vsPPowFuns pow))
    (hinl : P.HasAt inl (vsPInLPFuns inl phi))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {k : ℕ} (hk : k + 2 ≤ N)
    {x : Perm (Fin I.n)} (hx : x ∈ gens I.gs) (hxb : vsPInLB I ws' cs rows x = false) :
    FunDet P b (.list [vsPCtx I ws' cs rows hs, .nat k, vsPAccV ((0, x, 0) : ℕ × Perm (Fin I.n) × ℕ)])
      (vsPAccV (vsPWalk (vsPInLB I ws' cs rows) k x)) (vsPWalkCost Cφ N W) := by
  set ib := vsPInLB I ws' cs rows
  have hn := H.n
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hM : ∀ i acc, i ≤ k → acc = vsPAccV (vsPWalk ib i x) → acc.wt ≤ 20 * (N + 1) ^ 2 := by
    rintro i acc hi rfl
    obtain ⟨h01, -, -, hq, -, -⟩ := vsPWalk_inv ib hxb i
    have w1 := wt_list3_le (.nat (vsPWalk ib i x).1) (encPerm (vsPWalk ib i x).2.1)
      (.nat (vsPWalk ib i x).2.2)
    have w2 := wt_encPerm_le (vsPWalk ib i x).2.1
    have w3 := wt_nat_le (vsPWalk ib i x).1
    have w4 := wt_nat_le (vsPWalk ib i x).2.2
    have : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
    unfold vsPAccV
    omega
  have hit := iter_spec hb (c := vsPCtx I ws' cs rows hs) (k := k)
    (acc0 := vsPAccV ((0, x, 0) : ℕ × Perm (Fin I.n) × ℕ))
    (Inv := fun i acc => acc = vsPAccV (vsPWalk ib i x)) (M := 20 * (N + 1) ^ 2)
    (B := fun _ => vsPWStepCost Cφ N W) rfl hM (fun i acc hi hacc => by
      subst hacc
      obtain ⟨h01, hz, -, hq, -, -⟩ := vsPWalk_inv ib hxb i
      have := (vsPWStep_spec hg hpow hinl hphi H (i := i) (by omega)
        (Subgroup.zpowers_le.2 hx hz) (by omega) (by omega)).mono (c' := vsPWStepCost Cφ N W) le_rfl
      refine FunAll.mono this fun w cost hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, vsPWalk_succ])
  refine FunDet.mono (FunAll.mono hit fun w cost hw => ⟨hw.1, hw.2⟩) ?_
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have w0 := wt_list3_le (vsPCtx I ws' cs rows hs) (.nat k)
    (vsPAccV ((0, x, 0) : ℕ × Perm (Fin I.n) × ℕ))
  have wa := hM 0 _ (Nat.zero_le _) rfl
  have wk := wt_nat_le k
  have wC := H.cw
  have h1 : k * vsPWStepCost Cφ N W ≤ (N + 1) * vsPWStepCost Cφ N W :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : loopModK * (k + 1) * ((Val.list [vsPCtx I ws' cs rows hs, .nat k,
      vsPAccV ((0, x, 0) : ℕ × Perm (Fin I.n) × ℕ)]).wt + k + 20 * (N + 1) ^ 2 + 1) ≤
      2 * 10 ^ 5 * (N + 1) * (W + (N + 1) ^ 2) := by
    have : (Val.list [vsPCtx I ws' cs rows hs, .nat k,
        vsPAccV ((0, x, 0) : ℕ × Perm (Fin I.n) × ℕ)]).wt + k + 20 * (N + 1) ^ 2 + 1 ≤
        200 * (W + (N + 1) ^ 2) := by
      have : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
      have : (vsPAccV ((0, x, 0) : ℕ × Perm (Fin I.n) × ℕ)).wt =
          (vsPAccV (vsPWalk ib 0 x)).wt := rfl
      omega
    calc loopModK * (k + 1) * _ ≤ 1000 * (N + 1) * (200 * (W + (N + 1) ^ 2)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) this
      _ = 2 * 10 ^ 5 * (N + 1) * (W + (N + 1) ^ 2) := by ring
  unfold vsPWalkCost
  omega

/-! ### The least `j` with `y^j ∈ L`, and its least prime factor -/

section JMath

variable {n : ℕ} (ib : Perm (Fin n) → Bool)

/-- The least `j ∈ [1, m]` with `ib (y^j)` (as `findIdx + 1`). -/
def vsPJ (m : ℕ) (y : Perm (Fin n)) : ℕ := (List.range m).findIdx (fun t => ib (y ^ (t + 1))) + 1

/-- The least divisor `≥ 2` of `j` (as `findIdx + 2`). -/
def vsPR (j : ℕ) : ℕ := (List.range j).findIdx (fun t => decide (j % (t + 2) = 0)) + 2

theorem vsP_findIdx_le {α : Type*} {p : α → Bool} {xs : List α} {i : ℕ} (hi : i < xs.length)
    (h : p xs[i] = true) : xs.findIdx p ≤ i := by
  by_contra hc
  have := List.not_of_lt_findIdx (p := p) (xs := xs) (i := i) (by omega)
  have e : p xs[i] = p (xs[i]'(Nat.le_trans (show i < xs.findIdx p by omega)
      List.findIdx_le_length)) := rfl
  rw [e, this] at h
  exact Bool.noConfusion h

theorem vsPR_eq {j : ℕ} (hj : 2 ≤ j) : vsPR j = j.minFac := by
  have hm2 : 2 ≤ j.minFac := (Nat.minFac_prime (by omega)).two_le
  have hmj : j.minFac ≤ j := Nat.minFac_le (by omega)
  have hle : (List.range j).findIdx (fun t => decide (j % (t + 2) = 0)) ≤ j.minFac - 2 :=
    vsP_findIdx_le (by simp; omega) (by
      simp only [List.getElem_range, decide_eq_true_eq]
      rw [show j.minFac - 2 + 2 = j.minFac by omega]
      exact Nat.dvd_iff_mod_eq_zero.mp (Nat.minFac_dvd j))
  have hlt : (List.range j).findIdx (fun t => decide (j % (t + 2) = 0)) < (List.range j).length :=
    lt_of_le_of_lt hle (by simp; omega)
  have hp := List.findIdx_getElem (p := fun t => decide (j % (t + 2) = 0)) (w := hlt)
  simp only [List.getElem_range, decide_eq_true_eq] at hp
  have hge := Nat.minFac_le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hp)
  unfold vsPR
  omega

/-- **The element of prime order modulo `L`.** -/
theorem vsPOrd_math {m : ℕ} {y : Perm (Fin n)} {q : ℕ} (hy : ib y = false)
    (hq : ib (y ^ q) = true) (h2 : 2 ≤ q) (hqm : q ≤ m) :
    2 ≤ vsPJ ib m y ∧ vsPJ ib m y ≤ m ∧ (vsPR (vsPJ ib m y)).Prime ∧
      vsPR (vsPJ ib m y) ≤ vsPJ ib m y ∧ vsPR (vsPJ ib m y) ∣ vsPJ ib m y ∧
      1 ≤ vsPJ ib m y / vsPR (vsPJ ib m y) ∧
      ib (y ^ (vsPJ ib m y / vsPR (vsPJ ib m y))) = false ∧
      ib ((y ^ (vsPJ ib m y / vsPR (vsPJ ib m y))) ^ vsPR (vsPJ ib m y)) = true := by
  set p := fun t => ib (y ^ (t + 1))
  have hle : (List.range m).findIdx p ≤ q - 1 :=
    vsP_findIdx_le (by simp; omega) (by
      simp only [List.getElem_range, p]; rw [show q - 1 + 1 = q by omega]; exact hq)
  have hlt : (List.range m).findIdx p < (List.range m).length := lt_of_le_of_lt hle (by simp; omega)
  have hJ := List.findIdx_getElem (p := p) (w := hlt)
  simp only [List.getElem_range, p] at hJ
  have eJ : vsPJ ib m y = (List.range m).findIdx p + 1 := rfl
  have hmin : ∀ j', 1 ≤ j' → j' < vsPJ ib m y → ib (y ^ j') = false := by
    intro j' h1 h2'
    have := List.not_of_lt_findIdx (p := p) (xs := List.range m) (i := j' - 1) (by omega)
    simp only [List.getElem_range, p] at this
    rwa [show j' - 1 + 1 = j' by omega] at this
  have hJ2 : 2 ≤ vsPJ ib m y := by
    by_contra hc
    have e' : (List.range m).findIdx p = 0 := by omega
    rw [e', zero_add, pow_one] at hJ
    rw [hJ] at hy
    exact Bool.noConfusion hy
  have hJm : vsPJ ib m y ≤ m := by simp only [List.length_range] at hlt; omega
  set j := vsPJ ib m y with hjdef
  have hR := vsPR_eq hJ2
  have hpr : j.minFac.Prime := Nat.minFac_prime (by omega)
  have hdvd : j.minFac ∣ j := Nat.minFac_dvd j
  have hr2 := hpr.two_le
  have hrj : j.minFac ≤ j := Nat.minFac_le (by omega)
  rw [hR]
  have hq1 : 1 ≤ j / j.minFac := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hqlt : j / j.minFac < j := Nat.div_lt_self (by omega) (by omega)
  refine ⟨hJ2, hJm, hpr, hrj, hdvd, hq1, hmin _ hq1 hqlt, ?_⟩
  rw [← pow_mul, Nat.div_mul_cancel hdvd]
  have : (List.range m).findIdx p + 1 = j := rfl
  rw [← this]
  exact hJ

end JMath

end GI.Impl
