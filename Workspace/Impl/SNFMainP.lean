import Workspace.Impl.SNFPairP
import Workspace.Impl.KRefLib
import Workspace.Proved.SNFBound

/-!
# The main function of the Smith form program

Function `227` takes `[n, A]`. It builds the identity with the block table (`p = q = n`), gets
`K = hnfKn A` from function `150`, computes the number of alternation steps `snfCount A` from
the bit length of `K`, runs the alternation loop (`iterFuns 218 221`) and then the pair loop
(`iterFuns 222 225`), and returns `[P, H, Q]` of `snfRes A` (`snfMain_spec`).

All states have weight at most `snfY W`, where `W` is the input weight (`snf_state_wt`). The
reason: by `snf_all_bits` every entry has fewer than `snfB2 W` bits, and `hnf_mat_wt` turns
bits into weight.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved

/-! ### The weight bound -/

/-- A bound on the number of alternation steps. -/
def snfCn (W : ℕ) : ℕ := 2 * ((W + 1) * (snfBeta W + 1) + 1)

/-- A bound on the bits of all entries. -/
def snfB2 (W : ℕ) : ℕ :=
  1 + snfCn W * (snfBeta (snfBeta W) + snfBeta W) + W * W * (snfBeta (snfBeta W) + 2 * snfBeta W)

def snfXw (W : ℕ) : ℕ := 1000 * ((2 * W + 1) * (snfB2 W + 1))

/-- A bound on the weight of all states, on the loop lengths, and on `n`. -/
def snfY (W : ℕ) : ℕ := 7 * (snfXw W * snfXw W) + 7 + snfCn W + W * W + W

theorem snf_state_wt {n : ℕ} {s : SnfSt n} {L W X : ℕ} (hnW : n ≤ W) (hH : SnfBits L s.H)
    (hP : SnfBits L s.P) (hQ : SnfBits L s.Q) (hX : 1000 * ((2 * W + 1) * (L + 1)) ≤ X) :
    (snfStVal s).wt ≤ 7 * (X * X) + 7 := by
  have h1 : 1000 * ((n + n + 1) * (L + 1)) ≤ X :=
    le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))) hX
  have a := hnf_mat_wt s.H hH h1
  have b := hnf_mat_wt s.P hP h1
  have c := hnf_mat_wt s.Q hQ h1
  have := wt_list3_le (encIntMatrix s.H) (encIntMatrix s.P) (encIntMatrix s.Q)
  show (Val.list [encIntMatrix s.H, encIntMatrix s.P, encIntMatrix s.Q]).wt ≤ _
  omega

/-- The facts on the input used by the main function. -/
theorem snf_input_facts {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.det ≠ 0)
    {W : ℕ} (hAW : (encIntMatrix A).wt < W) :
    n < W ∧ SnfE (snfBeta W) A ∧ hnfKn A ≤ 2 ^ (snfBeta W) ∧ snfCount A ≤ snfCn W := by
  have hnA := hnf_rows_lt_wt A
  have hnW : n < W := by omega
  have hent : ∀ i j, (A i j).natAbs < 2 ^ W := fun i j =>
    lt_of_lt_of_le (hnf_entry_lt_wt A i j) (Nat.pow_le_pow_right (by decide) hAW.le)
  have hK : hnfKn A ≤ 2 ^ (snfBeta W) := hnfKn_le A hnW.le le_rfl hent
  have hdet : A.det.natAbs < hnfKn A := by
    have h := snf_det_lt_K hn A
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  have hβ := snf_le_beta W
  have hE : SnfE (snfBeta W) A :=
    ⟨by unfold snfBeta; omega, by omega,
      fun i j => lt_of_lt_of_le (hent i j) (Nat.pow_le_pow_right (by decide) hβ), by omega⟩
  have hlen : (Nat.bits (hnfKn A)).length ≤ snfBeta W + 1 := by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    calc hnfKn A ≤ 2 ^ snfBeta W := hK
      _ < 2 ^ (snfBeta W + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hc : (n + 1) * (Nat.bits (hnfKn A)).length ≤ (W + 1) * (snfBeta W + 1) :=
    Nat.mul_le_mul (by omega) hlen
  refine ⟨hnW, hE, hK, ?_⟩
  unfold snfCount snfCn
  omega

/-- Every state has weight at most `snfY W`. -/
theorem snf_states_wt {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.det ≠ 0)
    {W : ℕ} (hAW : (encIntMatrix A).wt < W) :
    (∀ t ≤ snfCount A, (snfStVal (snfIt A t)).wt ≤ snfY W) ∧
      (∀ k ≤ n * n, (snfStVal (snfRes' A k)).wt ≤ snfY W) := by
  obtain ⟨hnW, hE, -, hc⟩ := snf_input_facts hn hA hAW
  have hB : 1 + snfCount A * (snfBeta (snfBeta W) + snfBeta W) +
      n * n * (snfBeta (snfBeta W) + 2 * snfBeta W) ≤ snfB2 W := by
    have h1 := Nat.mul_le_mul_right (snfBeta (snfBeta W) + snfBeta W) hc
    have h2 := Nat.mul_le_mul_right (snfBeta (snfBeta W) + 2 * snfBeta W)
      (Nat.mul_le_mul hnW.le hnW.le)
    unfold snfB2
    omega
  obtain ⟨h1, h2⟩ := snf_all_bits hn hA hE hB
  have hX : 1000 * ((2 * W + 1) * (snfB2 W + 1)) ≤ snfXw W := le_rfl
  refine ⟨fun t ht => ?_, fun k hk => ?_⟩
  · obtain ⟨a, b, c⟩ := h1 t ht
    have := snf_state_wt hnW.le a b c hX
    unfold snfY; omega
  · obtain ⟨a, b, c⟩ := h2 k hk
    have := snf_state_wt hnW.le a b c hX
    unfold snfY; omega

theorem snfY_big (W : ℕ) : 1000 * W + 1000 ≤ snfY W ∧ snfCn W ≤ snfY W ∧ W * W ≤ snfY W := by
  have h1 : 1000 * (2 * W + 1) ≤ snfXw W := by
    unfold snfXw
    exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
  have h2 : snfXw W * 1 ≤ snfXw W * snfXw W := Nat.mul_le_mul_left _ (by omega)
  unfold snfY
  omega

/-! ### The program -/

/-- The main function. -/
def snfMainE : Expr :=
  .letE (mk1 (arg 0))
  (.letE (.call 169 (mk3 (snfL6 hnfOneE hnfZeroE hnfZeroE hnfOneE (arg 0) (arg 0)) (arg 0) (arg 0)))
  (.letE (.call 150 (mk4 (arg 0) (arg 0) (arg 1) hnfOneE))
  (.letE (.arith .mul (.nat 2) (.arith .add (.arith .mul (.arith .add (arg 0) (.nat 1))
      (.length (.get (.get (.var 3) (.nat 0)) (.nat 1)))) (.nat 1)))
  (.letE (.call 218 (mk3 (.var 1) (.var 4) (mk3 (arg 1) (.var 2) (.var 2))))
  (.letE (.call 222 (mk3 (.var 1) (.arith .mul (arg 0) (arg 0)) (.var 5)))
    (mk3 (.get (.var 6) (.nat 1)) (.get (.var 6) (.nat 0)) (.get (.var 6) (.nat 2))))))))

/-- Where the main function and its pieces are. -/
structure snfMainAt (P : Program) : Prop where
  alt : snfAltAt P
  pair : snfPairAt P
  it1 : P.HasAt 218 (iterFuns 218 221)
  it2 : P.HasAt 222 (iterFuns 222 225)
  main : P.funs[227]? = some snfMainE

/-- The cost of the main function. -/
def snfMainCost (K D W : ℕ) : ℕ :=
  1000 * (snfF K D (100 * W + 1000) + snfF K D (hnfXW W) +
    loopModK * (snfAltCost K D (snfY W) + 20) * (snfY W + 1) ^ 2 +
    loopModK * (snfPairCost K D (snfY W) + 20) * (snfY W + 1) ^ 2 + snfY W + W + 100)

/-- The output of the main function. -/
def snfOut {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Val :=
  .list [encIntMatrix (snfRes A).P, encIntMatrix (snfRes A).H, encIntMatrix (snfRes A).Q]

set_option maxHeartbeats 16000000 in
/-- **The Smith form program.** -/
theorem snfMain_spec {P : Program} (h : snfMainAt P) {K D : ℕ} (hE : SnfEnv K D)
    (I : NonsingularInst) :
    FunDet P 227 (nonsingularInput I) (snfOut I.A) (snfMainCost K D (nonsingularInput I).wt) := by
  obtain ⟨n, hn, A, hA⟩ := I
  have hH := h.alt.hnf
  set W := (nonsingularInput ⟨n, hn, A, hA⟩).wt with hW
  set vs : List Val := [.nat n, encIntMatrix A] with hvs
  have eW : (Val.list vs).wt = W := rfl
  have wA : (encIntMatrix A).wt < W := wt_le_wt_list (by simp [hvs])
  have wnv : (Val.nat n).wt < W := wt_le_wt_list (by simp [hvs])
  obtain ⟨hnW, hEA, hKb, hcnt⟩ := snf_input_facts hn hA wA
  obtain ⟨hS1, hS2⟩ := snf_states_wt hn hA wA
  set Y := snfY W with hY
  obtain ⟨hY1, hY2, hY3⟩ := snfY_big W
  have wn := wt_nat_le n
  have darg : ∀ (rest : List Val) (j : ℕ) (v : Val), vs[j]? = some v →
      Det P (Val.list vs :: rest) (arg j) v (2 * W + 10) := fun rest j v hv =>
    (Det.arg' hv).mono (by have : j < 2 := (List.getElem?_eq_some_iff.mp hv).1; omega)
  -- `[n]`
  have d1 := Det.mk1 (darg [] 0 _ rfl)
  set c := Val.list [.nat n] with hc
  have wc : c.wt ≤ 2 * W + 10 := by
    have := wt_list_le [Val.nat n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    have e : c.wt = (Val.list [Val.nat n]).wt := rfl
    omega
  -- the identity
  have w0 : (encInt 0).wt ≤ 15 := by decide
  have w1 : (encInt 1).wt ≤ 21 := by decide
  have dctx := snf_det_snoc2 (hnf_det_one (P := P) (env := [Val.list vs, c])) hnf_det_zero
    hnf_det_zero hnf_det_one (darg [c] 0 _ rfl) (darg [c] 0 _ rfl)
  have wctx : (Val.list (snfEmbCtx n n 1 0 0 1)).wt ≤ 10 * W + 200 := by
    have := wt_list_le (snfEmbCtx n n 1 0 0 1)
    simp only [snfEmbCtx, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil] at this ⊢
    omega
  have wtin : (Val.list [.list (snfEmbCtx n n 1 0 0 1), .nat n, .nat n]).wt ≤ 100 * W + 1000 := by
    have := wt_list3_le (.list (snfEmbCtx n n 1 0 0 1)) (.nat n) (.nat n); omega
  have tI := (snfEmbTab_spec (n := n) h.pair.et h.pair.ecell n n 1 0 0 1 wtin (by omega)).mono
    (hE.emb _)
  rw [snfEmb_out] at tI
  have d2 := Det.call (Det.mk3 dctx (darg [c] 0 _ rfl) (darg [c] 0 _ rfl)) tI
  set v2 := encIntMatrix (1 : Matrix (Fin n) (Fin n) ℤ) with hv2
  -- `K`
  have hD := hnfDecAt_of hH.ints
  have hEn := hnfEncAt_of hH.ints
  obtain ⟨hX1, hX2, hX3, hX4⟩ := hnfXW_facts W
  have hm : hnfMn A 1 < 2 ^ hnfXW W := by
    have e : hnfMn A 1 = hnfKn A := by unfold hnfMn; simp
    rw [e]
    calc hnfKn A ≤ 2 ^ snfBeta W := hKb
      _ < 2 ^ hnfXW W := Nat.pow_lt_pow_right (by decide) (by unfold snfBeta hnfL at *; nlinarith)
  have wnin : (Val.list [.nat n, .nat n, encIntMatrix A, encInt 1]).wt ≤ hnfXW W := by
    have := wt_list_le [Val.nat n, .nat n, encIntMatrix A, encInt 1]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    omega
  have sn := (hnfNums_spec hD hEn hH.nums hH.abs hH.pow A 1 hn (by norm_num) (B := 2 ^ W)
    (Y := hnfXW W) (fun i j => (lt_of_lt_of_le (hnf_entry_lt_wt A i j)
      (Nat.pow_le_pow_right (by decide) wA.le)).le)
    (lt_of_lt_of_le (hnf_rcB hnW.le le_rfl) (Nat.pow_le_pow_right (by decide) hX4)) wnin hm).mono
    (hE.nums _)
  have d3 := Det.call (Det.mk4 (darg [c, v2] 0 _ rfl) (darg [c, v2] 0 _ rfl) (darg [c, v2] 1 _ rfl)
    hnf_det_one) sn
  set v3 := Val.list [encInt (hnfKn A : ℤ), encInt (hnfMn A 1 : ℤ)] with hv3
  have wv3 : v3.wt < snfF K D (hnfXW W) := sn.wt_lt
  -- the count
  set e3 : List Val := [Val.list vs, c, v2, v3] with he3
  set bl := (Nat.bits (hnfKn A)).length with hbl
  have dK : Det P e3 (.get (.get (.var 3) (.nat 0)) (.nat 1))
      (.list ((Nat.bits (hnfKn A)).map fun b => .nat (if b then 1 else 0)))
      (3 * v3.wt + 20) := by
    have dv := Det.get' (Det.var' (P := P) (env := e3) (i := 3) rfl) (Det.nat 0)
      (show [encInt (hnfKn A : ℤ), encInt (hnfMn A 1 : ℤ)][0]? = some (encInt (hnfKn A : ℤ)) from rfl)
    have dg := Det.get' dv (Det.nat 1) (show [Val.nat (if (hnfKn A : ℤ) < 0 then 1 else 0),
      Val.list ((Nat.bits (hnfKn A : ℤ).natAbs).map fun b => .nat (if b then 1 else 0))][1]? =
      some (.list ((Nat.bits (hnfKn A)).map fun b => .nat (if b then 1 else 0))) by simp)
    refine dg.mono ?_
    have a1 : (encInt (hnfKn A : ℤ)).wt < v3.wt := wt_le_wt_list (by simp [hv3])
    have a2 : (Val.list ((Nat.bits (hnfKn A)).map fun b => .nat (if b then 1 else 0))).wt <
        (encInt (hnfKn A : ℤ)).wt := wt_le_wt_list (by simp [encInt])
    have e : (Val.list [encInt (hnfKn A : ℤ), encInt (hnfMn A 1 : ℤ)]).wt = v3.wt := rfl
    omega
  have dl := Det.length dK
  rw [List.length_map, ← hbl] at dl
  have darg3 : ∀ j (v : Val), vs[j]? = some v → Det P e3 (arg j) v (2 * W + 10) :=
    fun j v hv => darg [c, v2, v3] j v hv
  have da1 := Det.arith' (op := .add) (darg3 0 _ rfl) (Det.nat 1) rfl
  have dm1 := Det.arith' (op := .mul) da1 dl rfl
  have da2 := Det.arith' (op := .add) dm1 (Det.nat 1) rfl
  have d4 := Det.arith' (op := .mul) (Det.nat 2) da2 rfl
  have ecnt : GI.Machine.BinOp.mul.eval 2 (GI.Machine.BinOp.add.eval
      (GI.Machine.BinOp.mul.eval (GI.Machine.BinOp.add.eval n 1) bl) 1) = snfCount A := rfl
  rw [ecnt] at d4
  set cnt := snfCount A with hcntd
  have hb1 : 1 ≤ bl := by
    rw [hbl, Nat.size_eq_bits_len]; exact Nat.size_pos.mpr (by unfold hnfKn; omega)
  have hcb : cnt = 2 * ((n + 1) * bl + 1) := rfl
  have hnb := Nat.mul_le_mul_left (n + 1) hb1
  have hbn : 1 * bl ≤ (n + 1) * bl := Nat.mul_le_mul_right _ (by omega)
  have emul1 : GI.Machine.BinOp.mul.eval (GI.Machine.BinOp.add.eval n 1) bl = (n + 1) * bl := rfl
  have eadd2 : GI.Machine.BinOp.add.eval (GI.Machine.BinOp.mul.eval
      (GI.Machine.BinOp.add.eval n 1) bl) 1 = (n + 1) * bl + 1 := rfl
  have eadd1 : GI.Machine.BinOp.add.eval n 1 = n + 1 := rfl
  have hn1 : n + 1 ≤ cnt := by omega
  -- the first loop
  set s0 : SnfSt n := ⟨A, 1, 1⟩ with hs0
  have hdetI : ∀ t, (snfIt A t).H.det ≠ 0 := fun t => by
    intro h0
    have := snfIt_det hn hA t
    rw [h0] at this
    exact hA (Int.natAbs_eq_zero.mp this.symm)
  have L1 : FunDet P 218 (.list [c, .nat cnt, snfStVal (snfIt A 0)]) (snfStVal (snfIt A cnt))
      (loopModK * (snfAltCost K D Y + 20) * (Y + 1) ^ (0 + 2)) :=
    kref_iter (accs := fun t => snfStVal (snfIt A t)) h.it1 (fun i hi => by
      beta_reduce; rw [snfIt_succ]
      exact (snfAlt_spec h.alt hE hn (snfIt A i) (hdetI i) i (hS1 i hi.le) (by omega)
        (by omega)).mono (by simp)) (fun i hi => hS1 i hi) (by omega) (by omega)
  have e0 : snfStVal (snfIt A 0) = .list [encIntMatrix A, v2, v2] := rfl
  rw [e0] at L1
  set e4 := e3 ++ [.nat cnt] with he4
  have d5 := Det.call (Det.mk3 (Det.var' (P := P) (env := e4) (i := 1) rfl)
    (Det.var' (P := P) (env := e4) (i := 4) rfl)
    (Det.mk3 (darg [c, v2, v3, .nat cnt] 1 _ rfl) (Det.var' (P := P) (env := e4) (i := 2) rfl)
      (Det.var' (P := P) (env := e4) (i := 2) rfl))) L1
  set v5 := snfStVal (snfIt A cnt) with hv5
  have wv5 : v5.wt ≤ Y := hS1 cnt le_rfl
  -- the second loop
  have L2 : FunDet P 222 (.list [c, .nat (n * n), snfStVal (snfRes' A 0)]) (snfStVal (snfRes' A (n * n)))
      (loopModK * (snfPairCost K D Y + 20) * (Y + 1) ^ (0 + 2)) :=
    kref_iter (accs := fun k => snfStVal (snfRes' A k)) h.it2 (fun k hk => by
      beta_reduce; rw [snfRes'_succ]
      exact (snfPairStep_spec h.pair hE (snfRes' A k) (snfRes'_pos hn hA hk.le) hk
        (hS2 k hk.le) (by omega) (by nlinarith)).mono (by simp)) (fun k hk => hS2 k hk)
      (by omega) (by nlinarith)
  have e0' : snfStVal (snfRes' A 0) = v5 := rfl
  rw [e0'] at L2
  set e5 := e4 ++ [v5] with he5
  have dnn := Det.arith' (op := .mul) (darg [c, v2, v3, .nat cnt, v5] 0 _ rfl)
    (darg [c, v2, v3, .nat cnt, v5] 0 _ rfl) rfl
  have d6 := Det.call (Det.mk3 (Det.var' (P := P) (env := e5) (i := 1) rfl) dnn
    (Det.var' (P := P) (env := e5) (i := 5) rfl)) L2
  set v6 := snfStVal (snfRes' A (n * n)) with hv6
  have wv6 : v6.wt ≤ Y := hS2 (n * n) le_rfl
  -- the output
  set e6 := e5 ++ [v6] with he6
  have dv6 : Det P e6 (.var 6) (.list [encIntMatrix (snfRes A).H, encIntMatrix (snfRes A).P,
      encIntMatrix (snfRes A).Q]) (v6.wt + 1) := Det.var' rfl
  have wH : (encIntMatrix (snfRes A).H).wt < v6.wt := wt_le_wt_list (by simp [hv6, snfStVal, snfRes_eq])
  have wP : (encIntMatrix (snfRes A).P).wt < v6.wt := wt_le_wt_list (by simp [hv6, snfStVal, snfRes_eq])
  have wQ : (encIntMatrix (snfRes A).Q).wt < v6.wt := wt_le_wt_list (by simp [hv6, snfStVal, snfRes_eq])
  have d7 := Det.mk3 (Det.get' dv6 (Det.nat 1) rfl) (Det.get' dv6 (Det.nat 0) rfl)
    (Det.get' dv6 (Det.nat 2) rfl)
  have dall := Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE d4 (Det.letE d5 (Det.letE d6 d7)))))
  apply FunDet.intro h.main
  refine dall.mono ?_
  -- the cost
  have o1 := wt_list3_le (encIntMatrix (snfRes A).P) (encIntMatrix (snfRes A).H)
    (encIntMatrix (snfRes A).Q)
  have o2 := wt_list3_le (.list (snfEmbCtx n n 1 0 0 1)) (.nat n) (.nat n)
  have o3 := wt_list_le [Val.nat n, .nat n, encIntMatrix A, encInt 1]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at o3
  have o4 := wt_list3_le c (.nat cnt) (.list [encIntMatrix A, v2, v2])
  have o5 := wt_list3_le (encIntMatrix A) v2 v2
  have o6 := wt_list3_le c (.nat (n * n)) v5
  have wv2 : v2.wt < snfF K D (100 * W + 1000) := tI.wt_lt
  have wcnt := wt_nat_le cnt
  have wnn := wt_nat_le (n * n)
  have wbl := wt_nat_le bl
  have f1 : snfF K D (100 * W + 1000) ≥ 0 := Nat.zero_le _
  have eo : snfOut A = .list [encIntMatrix (snfRes A).P, encIntMatrix (snfRes A).H,
    encIntMatrix (snfRes A).Q] := rfl
  have ef1 : snfF K D (100 * W + 1000) = K * (100 * W + 1000 + 2) ^ D := rfl
  have ef2 : snfF K D (hnfXW W) = K * (hnfXW W + 2) ^ D := rfl
  have emm : GI.Machine.BinOp.mul.eval n n = n * n := rfl
  have ectx : (Val.list [encInt 1, encInt 0, encInt 0, encInt 1, Val.nat n, Val.nat n]).wt =
    (Val.list (snfEmbCtx n n 1 0 0 1)).wt := rfl
  have q1 : loopModK * (snfAltCost K D Y + 20) * (Y + 1) ^ (0 + 2) =
    loopModK * (snfAltCost K D Y + 20) * (Y + 1) ^ 2 := rfl
  have q2 : loopModK * (snfPairCost K D Y + 20) * (Y + 1) ^ (0 + 2) =
    loopModK * (snfPairCost K D Y + 20) * (Y + 1) ^ 2 := rfl
  have q3 : (Val.list [c, Val.nat (GI.Machine.BinOp.mul.eval n n), v5]).wt =
    (Val.list [c, Val.nat (n * n), v5]).wt := rfl
  have q4 : (Val.list [Val.list [encInt 1, encInt 0, encInt 0, encInt 1, Val.nat n, Val.nat n],
    Val.nat n, Val.nat n]).wt = (Val.list [Val.list (snfEmbCtx n n 1 0 0 1), Val.nat n, Val.nat n]).wt := rfl
  have q5 : n * n ≤ W * W := Nat.mul_le_mul hnW.le hnW.le
  unfold snfMainCost
  try rw [← hW]
  try rw [← hY]
  clear_value Y v2 v3 v5 v6 cnt bl c
  omega

end GI.Impl
