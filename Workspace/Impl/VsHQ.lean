import Workspace.Impl.VsHCtx

/-!
# The numbers `Q = p^(dim L) - 1` and `dv = (r ∣ Q)`

On `[ctx, r]` the program `vsHC2E` computes `q = p^m` (`m` the number of rows, by `m`
multiplications), and returns the context of the goodness test `[ctx, r, q - 1, r ∣ q - 1]`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp len)

variable {I : VecStabInst}

/-- The step of the power, on `[p, i, acc]`. -/
def vsHMulE : Expr := .arith .mul (arg 2) (arg 0)

/-- On `[ctx, r]`: the context `[ctx, r, Q, dv]`. -/
def vsHC2E (it : ℕ) : Expr :=
  .letE (.call it (mk3 (.get (arg 0) (.nat 2)) (.length (.get (arg 0) (.nat 3))) (.nat 1)))
    (.letE (.arith .sub (.var 1) (.nat 1))
      (mk4 (arg 0) (arg 1) (.var 2) (.arith .eq (.arith .mod (.var 2) (arg 1)) (.nat 0))))

theorem vsH_len_pow {p m N : ℕ} (hp : p ≤ N) (hm : m ≤ N) : len (p ^ m) ≤ (N + 1) ^ 2 := by
  have h1 := GI.Machine.len_pow_le p m
  have h2 := GI.Machine.len_le_self p
  have : m * len p ≤ N * N := Nat.mul_le_mul hm (h2.trans hp)
  nlinarith

/-- The cost of `vsHC2E`. -/
def vsHC2Cost (N W : ℕ) : ℕ := 10 ^ 5 * (N + 1) * (W + 10 * (N + 1) ^ 2)

set_option maxHeartbeats 4000000 in
theorem vsHC2_spec {P : Program} {f it st : ℕ} (hf : P.funs[f]? = some (vsHC2E it))
    (hit : P.HasAt it (iterFuns it st)) (hst : P.funs[st]? = some vsHMulE)
    {N W : ℕ} {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {r : ℕ} (hr : r ≤ N) :
    FunDet P f (.list [vsPCtx I ws' cs rows hs, .nat r])
      (vsHGc (vsPCtx I ws' cs rows hs) r (I.p ^ rows.length - 1)
        (decide (r ∣ I.p ^ rows.length - 1))) (vsHC2Cost N W) := by
  set C := vsPCtx I ws' cs rows hs
  set cv := [vsQGam I, vsWFrVal I.p I.d ws' cs, .nat I.p, .list (rows.map VsRow.val),
    natList (vsWZ (cs.length * cs.length)), encGroup hs, .nat I.n] with hcv
  set m := rows.length
  set p := I.p
  have hpN : p ≤ N := H.sz.pN
  have hmN : m ≤ N := H.rl
  have hlq : ∀ i ≤ m, len (p ^ i) ≤ (N + 1) ^ 2 := fun i hi => vsH_len_pow hpN (hi.trans hmN)
  -- the power
  have hstep : ∀ i acc, i < m → acc = Val.nat (p ^ i) →
      FunAll P st (.list [.nat p, .nat i, acc])
        (fun w cost => w = Val.nat (p ^ (i + 1)) ∧ cost ≤ 40 * (N + 1) ^ 2 + 200) := by
    rintro i acc hi rfl
    have a2 := Det.arg' (P := P) (vs := [Val.nat p, .nat i, .nat (p ^ i)]) (rest := []) (j := 2) rfl
    have a0 := Det.arg' (P := P) (vs := [Val.nat p, .nat i, .nat (p ^ i)]) (rest := []) (j := 0) rfl
    refine FunDet.intro hst ((Det.arith (op := .mul) a2 a0).mono ?_)
    · show _ ≤ _
      have w3 := wt_list3_le (.nat p) (.nat i) (.nat (p ^ i))
      have l1 := hlq i hi.le
      have l2 := hlq (i + 1) hi
      have e1 : BinOp.eval .mul (p ^ i) p = p ^ (i + 1) := by simp [BinOp.eval, pow_succ]
      rw [e1]
      simp only [wt_nat'] at *
      have := GI.Machine.len_le_self p
      have := GI.Machine.len_le_self i
      have q : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
      omega
  set vs := [C, Val.nat r]
  have a0 : Det P [Val.list vs] (arg 0) (.list cv) _ := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have dp := Det.get' a0 (Det.nat 2) (show cv[2]? = some (.nat p) from rfl)
  have dr := Det.get' a0 (Det.nat 3) (show cv[3]? = some (.list (rows.map VsRow.val)) from rfl)
  have dm := Det.length dr
  rw [List.length_map] at dm
  obtain ⟨KA, hKA, dA⟩ : ∃ KA, KA = _ ∧ Det P [Val.list vs] (mk3 (.get (arg 0) (.nat 2))
      (.length (.get (arg 0) (.nat 3))) (.nat 1)) (.list [.nat p, .nat m, .nat 1]) KA :=
    ⟨_, rfl, Det.mk3 dp dm (Det.nat 1)⟩
  set KI := m * (40 * (N + 1) ^ 2 + 200) +
    loopModK * (m + 1) * ((Val.list [Val.nat p, Val.nat m, Val.nat 1]).wt + m + ((N + 1) ^ 2 + 2) + 1)
  have dI : Det P [Val.list vs] (.call it (mk3 (.get (arg 0) (.nat 2))
      (.length (.get (arg 0) (.nat 3))) (.nat 1))) (.nat (p ^ m)) (KA + KI + (Val.nat (p ^ m)).wt + 1) := by
    refine EvalAll.call_funAll dA fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (iter_spec hit (c := .nat p) (k := m) (acc0 := .nat 1)
      (Inv := fun i acc => acc = .nat (p ^ i)) (M := (N + 1) ^ 2 + 2)
      (B := fun _ => 40 * (N + 1) ^ 2 + 200) (by simp)
      (fun i acc hi h => by rw [h, wt_nat']; have := hlq i hi; omega)
      (fun i acc hi h => hstep i acc hi h)).mono fun w c hw => ⟨hw.1, ?_⟩
    have := hw.2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
    rw [hw.1]
    omega
  set E1 := [Val.list vs, Val.nat (p ^ m)]
  have dQ := Det.arith (op := .sub) (Det.var' (P := P) (env := E1) (i := 1) rfl) (Det.nat 1)
  set Q := p ^ m - 1
  have eQ : BinOp.eval .sub (p ^ m) 1 = Q := rfl
  rw [eQ] at dQ
  set E2 := [Val.list vs, Val.nat (p ^ m), Val.nat Q]
  have b0 := Det.arg' (P := P) (vs := vs) (rest := [Val.nat (p ^ m), Val.nat Q]) (j := 0) rfl
  have b1 := Det.arg' (P := P) (vs := vs) (rest := [Val.nat (p ^ m), Val.nat Q]) (j := 1) rfl
  have v2 := Det.var' (P := P) (env := E2) (i := 2) rfl
  have dmod := Det.arith (op := .mod) v2 b1
  have deq := Det.arith (op := .eq) dmod (Det.nat (P := P) (env := E2) 0)
  have ebool : Val.nat (BinOp.eval .eq (BinOp.eval .mod Q r) 0) = boolVal (decide (r ∣ Q)) := by
    simp only [BinOp.eval, Nat.dvd_iff_mod_eq_zero]
    split <;> simp_all
  rw [ebool] at deq
  have d4 := Det.mk4 b0 b1 v2 deq
  refine FunDet.intro hf ((Det.letE dI (Det.letE dQ d4)).mono ?_)
  have wC : C.wt ≤ W := H.cw
  have ecv : (Val.list cv).wt = C.wt := rfl
  have hp2 := hlq m le_rfl
  have hQl : len Q ≤ (N + 1) ^ 2 := (GI.Machine.len_sub_le _ _).trans hp2
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have lp := GI.Machine.len_le_self p
  have lm := GI.Machine.len_le_self m
  have lr := GI.Machine.len_le_self r
  have wmod := GI.Machine.len_mod_le Q r
  have l1 : len 1 = 1 := GI.Machine.len_one
  have l0 : len 0 = 0 := rfl
  have wvs := wt_list2_le C (.nat r)
  have evs : (Val.list vs).wt = (Val.list [C, Val.nat r]).wt := rfl
  have w3 := wt_list3_le (.nat p) (.nat m) (.nat 1)
  have hmp : (Val.nat p).wt < (Val.list cv).wt := wt_le_wt_list (by simp [hcv])
  have hmr : (Val.list (rows.map VsRow.val)).wt < (Val.list cv).wt := wt_le_wt_list (by simp [hcv])
  have w4 := wt_list_le [C, Val.nat r, Val.nat Q, boolVal (decide (r ∣ Q))]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w4
  have eG : (vsHGc C r Q (decide (r ∣ Q))).wt =
      (Val.list [C, Val.nat r, Val.nat Q, boolVal (decide (r ∣ Q))]).wt := rfl
  have wb := wt_boolVal_le (decide (r ∣ Q))
  have wb' : (Val.nat (BinOp.eval .eq (BinOp.eval .mod Q r) 0)).wt ≤ 3 := by
    rw [ebool]; exact wb
  have hlen := length_lt_wt_list (rows.map VsRow.val)
  rw [List.length_map] at hlen
  unfold vsHC2Cost
  simp only [wt_nat'] at *
  set T := W + 10 * (N + 1) ^ 2
  set Z := (N + 1) * T
  have hZd : Z = (N + 1) * T := rfl
  have hTd : T = W + 10 * (N + 1) ^ 2 := rfl
  have hTZ : T ≤ Z := Nat.le_mul_of_pos_left _ (by omega)
  have hK1 : m * (40 * (N + 1) ^ 2 + 200) ≤ 240 * Z := by
    calc m * (40 * (N + 1) ^ 2 + 200) ≤ (N + 1) * (240 * T) :=
          Nat.mul_le_mul (by omega) (by simp only [T]; omega)
      _ = 240 * Z := by simp only [Z]; ring
  have hK2 : loopModK * (m + 1) * ((Val.list [Val.nat p, Val.nat m, Val.nat 1]).wt + m +
      ((N + 1) ^ 2 + 2) + 1) ≤ 3000 * Z := by
    have lk : loopModK = 1000 := rfl
    calc loopModK * (m + 1) * ((Val.list [Val.nat p, Val.nat m, Val.nat 1]).wt + m +
          ((N + 1) ^ 2 + 2) + 1) ≤ 1000 * (N + 1) * (3 * T) :=
          Nat.mul_le_mul (Nat.mul_le_mul (le_of_eq lk) (by omega)) (by
            simp only [T]; omega)
      _ = 3000 * Z := by simp only [Z]; ring
  have eZ : 10 ^ 5 * (N + 1) * (W + 10 * (N + 1) ^ 2) = 10 ^ 5 * Z := by simp only [Z, T]; ring
  rw [eZ]
  have hKId : KI = m * (40 * (N + 1) ^ 2 + 200) + loopModK * (m + 1) *
      ((Val.list [Val.nat p, Val.nat m, Val.nat 1]).wt + m + ((N + 1) ^ 2 + 2) + 1) := rfl
  have hKI : KI ≤ 3240 * Z := by
    rw [hKId]; exact (Nat.add_le_add hK1 hK2).trans (by omega)
  clear hKId hK1 hK2
  have b1 : len p ≤ N := lp.trans hpN
  have b2 : len m ≤ N := lm.trans hmN
  have b3 : len r ≤ N := lr.trans hr
  have b4 : len (Q % r) ≤ (N + 1) ^ 2 := wmod.trans hQl
  have b5 : (Val.list cv).wt ≤ W := ecv ▸ wC
  have b6 : (N + 1) ^ 2 ≤ T := by rw [hTd]; omega
  have b7 : W ≤ T := by rw [hTd]; omega
  have b8 : len (decide (r ∣ Q)).toNat ≤ 1 := by
    cases decide (r ∣ Q) <;> simp [Bool.toNat, GI.Machine.len] <;> rfl
  have b9 : len (BinOp.eval .eq (BinOp.eval .mod Q r) 0) ≤ 1 :=
    GI.Machine.len_ite_le_one (Q % r = 0)
  have b4' : len (BinOp.eval .mod Q r) ≤ (N + 1) ^ 2 := b4
  clear_value KI Z T
  omega

end GI.Impl
