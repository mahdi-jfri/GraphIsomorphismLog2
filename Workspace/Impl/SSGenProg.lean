module

public import Workspace.Impl.SSInsertProg

@[expose] public section

/-!
# Inserting the generators, as a program

`ssGenStepF ins` inserts generator `a` (`ssGenStep`), and the loop `iterFuns b (b + 3)` over
`a < |gs|` inserts them all (`ssGensLoop_spec`). Every state on the way satisfies `SsInv`, so all
values are small (`ssInv_small`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### Weights of states and of the context -/

theorem ss_st_wt {B : List (Fin n)} {gs : List (Perm (Fin n))} {st : SsState n}
    (hinv : SsInv B gs st) {Y : ℕ} (hY : n + B.length + gs.length + 2 ≤ Y) :
    (ssEncSt st).wt ≤ ssW Y := by
  obtain ⟨-, hTY, -, -, -⟩ := ss_Y_facts hY
  exact ((ssInv_small hinv hY).st (by omega) (by rw [hinv.len]; exact hTY)).wt_le

theorem ss_ctx_wt {B : List (Fin n)} {gs : List (Perm (Fin n))} {Y : ℕ}
    (hY : n + B.length + gs.length + 2 ≤ Y) : (ssCtx B gs).wt ≤ ssW Y :=
  (ssSmall_ctx' hY).wt_le

/-- Numbers below `ssW Y`. -/
theorem ss_W_facts {B : List (Fin n)} {gs : List (Perm (Fin n))} {Y : ℕ}
    (hY : n + B.length + gs.length + 2 ≤ Y) :
    B.length * n * (B.length * n) + 2 ≤ ssW Y ∧ gs.length + 2 ≤ ssW Y ∧
      (n + 1) ^ 4 ≤ ssW Y ∧ 1000 ≤ ssW Y := by
  have h1 : 1 ≤ Y := by omega
  have hZ := ssZ_le_ssW Y
  have e : B.length * n * (B.length * n) ≤ Y ^ 4 := by
    calc B.length * n * (B.length * n) ≤ Y * Y * (Y * Y) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (Nat.mul_le_mul (by omega) (by omega))
      _ = Y ^ 4 := by ring
  have e2 : (n + 1) ^ 4 ≤ Y ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have e3 : Y ≤ Y ^ 4 := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ Y ^ 4 := Nat.pow_le_pow_right h1 (by norm_num)
  have e4 : 1 ≤ Y ^ 4 := Nat.one_le_pow _ _ h1
  unfold ssZ at hZ
  omega

/-- The cost of a loop of `k` steps of cost at most `c V^p` each, with small values. -/
theorem ss_iter_cost {cost k Cs A Ma V c p : ℕ}
    (hc : cost ≤ k * Cs + loopModK * (k + 1) * (A + k + Ma + 1)) (hk : k + 1 ≤ V)
    (hCs : Cs ≤ c * V ^ p) (hA : A ≤ 7 * V) (hMa : Ma ≤ V) (hp : 1 ≤ p) :
    cost ≤ (c + 9000) * V ^ (p + 1) := by
  unfold loopModK at hc
  have e1 : k * Cs ≤ c * V ^ (p + 1) := by
    calc k * Cs ≤ V * (c * V ^ p) := Nat.mul_le_mul (by omega) hCs
      _ = c * V ^ (p + 1) := by ring
  have e2 : 1000 * (k + 1) * (A + k + Ma + 1) ≤ 9000 * (V * V) := by
    calc 1000 * (k + 1) * (A + k + Ma + 1) ≤ 1000 * V * (9 * V) :=
          Nat.mul_le_mul (Nat.mul_le_mul le_rfl hk) (by omega)
      _ = 9000 * (V * V) := by ring
  have e3 : V * V ≤ V ^ (p + 1) := by
    rw [← pow_two]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have e4 : (c + 9000) * V ^ (p + 1) = c * V ^ (p + 1) + 9000 * V ^ (p + 1) := by ring
  omega

theorem ss_add_cost {W0 E : ℕ} (hE : E ≤ 10 ^ 7 * (W0 + 1) ^ 2) :
    E + 300 * (10 * W0 + 10 + 1) ≤ 2 * 10 ^ 7 * (W0 + 1) ^ 2 := by
  have e : (W0 + 1) ^ 2 = (W0 + 1) * (W0 + 1) := by ring
  have := Nat.le_mul_of_pos_left (W0 + 1) (show 0 < W0 + 1 by omega)
  rw [e] at hE ⊢
  omega

/-! ### Inserting one generator -/

/-- The body of one generator step: `[c, a, st] ↦ insert [c, st, gs[a], gen a]`. -/
def ssGenStepF (ins : ℕ) : Expr :=
  .call ins (mk4 (arg 0) (arg 2) (.get (.get (arg 0) (.nat 2)) (.arith .add (arg 1) (.nat 1)))
    (mk2 (.nat 0) (arg 1)))

/-- The cost of one generator step. -/
def ssGenCost (Y : ℕ) : ℕ := 2 * 10 ^ 7 * (ssW Y + 1) ^ 2

theorem ssGenStepF_spec {P : Program} {f ins sift chain setb app comp inv : ℕ}
    (hf : P.funs[f]? = some (ssGenStepF ins)) (hP : SsInsAt P ins sift chain setb app comp inv)
    {B : List (Fin n)} {gs : List (Perm (Fin n))} {st : SsState n} (hinv : SsInv B gs st)
    {a : ℕ} (ha : a < gs.length) {Y : ℕ} (hY : n + B.length + gs.length + 2 ≤ Y) :
    FunDet P f (.list [ssCtx B gs, .nat a, ssEncSt st]) (ssEncSt (ssGenStep B gs st a))
      (ssGenCost Y) := by
  obtain ⟨es, hes, -⟩ := hinv.slp
  have hga : gs[a]?.getD 1 = gs[a] := by rw [List.getElem?_eq_getElem ha]; rfl
  have hins := ssInsertF_spec hP hinv hes (g := gs[a]) (ins0 := .gen a)
    (slpEntries_gen ha es) hY
  unfold ssGenStep
  rw [hga]
  obtain ⟨hMM, hG, -, h1000⟩ := ss_W_facts hY
  have hc := ss_ctx_wt hY
  have hs := ss_st_wt hinv hY
  have hs' := ss_st_wt (ssInsert_spec hinv hes (slpEntries_gen ha es)).1 hY
  obtain ⟨-, -, -, hY3, hZ⟩ := ss_Y_facts hY
  have hZW := ssZ_le_ssW Y
  have hp : (encPerm gs[a]).wt ≤ ssW Y :=
    (ssSmall_encPerm gs[a] (Z := ssZ Y) (by omega)).wt_le
  have haW : (Val.nat a).wt ≤ ssW Y := (wt_nat_le a).trans (by omega)
  have hiW : (encSlpInstr (.gen a)).wt ≤ ssW Y :=
    (ssSmall_instr (Z := ssZ Y) (ins := .gen a) (by simp only [ssInsMax]; omega) (by omega)).wt_le
  have hgsW : (Val.list ((1 :: gs).map encPerm)).wt ≤ ssW Y :=
    (le_of_lt (wt_le_wt_list (show Val.list ((1 :: gs).map encPerm) ∈
      [.nat n, ssEncB B, .list ((1 :: gs).map encPerm), .nat (B.length * n)] by simp))).trans hc
  have haw : (Val.list [ssCtx B gs, .nat a, ssEncSt st]).wt ≤ 10 * ssW Y + 10 :=
    (st_wt_list3 hc haW hs).trans (by omega)
  have dArg : ∀ j v, [ssCtx B gs, .nat a, ssEncSt st][j]? = some v → v.wt ≤ ssW Y →
      StDC P [.list [ssCtx B gs, .nat a, ssEncSt st]] (arg j) v 3 0 (10 * ssW Y + 10) :=
    fun j v hv hw => StDC.arg hv haw
      (by have := (List.getElem?_eq_some_iff.mp hv).1; simp at this; omega) (by omega)
  have hget : ((1 :: gs).map encPerm)[a + 1]? = some (encPerm gs[a]) := by simp [ha]
  have d2 := StDC.get (StDC.get (v := .list ((1 :: gs).map encPerm)) (dArg 0 _ rfl hc)
    (StDC.nat 2 (by omega)) rfl (by omega))
    (StDC.arith (op := .add) (z := a + 1) (dArg 1 _ rfl haW) (StDC.nat 1 (by omega)) rfl
      ((wt_nat_le _).trans (by omega))) hget (by omega)
  have d4 : StDC P [.list [ssCtx B gs, .nat a, ssEncSt st]] (mk2 (.nat 0) (arg 1))
      (encSlpInstr (.gen a)) 7 0 (10 * ssW Y + 10) :=
    StDC.mk2 (StDC.nat 0 (by omega)) (dArg 1 _ rfl haW) (by show (encSlpInstr (.gen a)).wt ≤ _; omega)
      (by omega)
  have dA := StDC.mk4 (dArg 0 _ rfl hc) (dArg 2 _ rfl hs) d2 d4
    ((st_wt_list4 hc hs hp hiW).trans (by omega)) (by omega)
  refine StDC.funDet hf (StDC.call dA hins (by omega)) (ss_cost_fin2 (by norm_num) ?_)
  unfold ssGenCost
  refine ss_add_cost ?_
  simp only [Nat.zero_add, Nat.add_zero, ssInsCost, le_refl]

/-! ### Inserting all generators -/

/-- Every state on the way satisfies the invariant. -/
theorem ssGens_inv {B : List (Fin n)} {gs : List (Perm (Fin n))} {st0 : SsState n}
    (h0 : SsInv B gs st0) : ∀ i, i ≤ gs.length →
      SsInv B gs ((List.range i).foldl (ssGenStep B gs) st0) := by
  intro i
  induction i with
  | zero => intro _; exact h0
  | succ i ih =>
    intro hi
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have h1 := ih (by omega)
    obtain ⟨es, hes, -⟩ := h1.slp
    have hga : gs[i]?.getD 1 = gs[i]'(by omega) := by
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    unfold ssGenStep
    rw [hga]
    exact (ssInsert_spec h1 hes (slpEntries_gen (by omega) es)).1

/-- The parts of the generator loop. -/
structure SsGenAt (P : Program) (b ins sift chain setb app comp inv : ℕ) : Prop where
  iter : P.HasAt b (iterFuns b (b + 3))
  step : P.funs[b + 3]? = some (ssGenStepF ins)
  insAt : SsInsAt P ins sift chain setb app comp inv

/-- The cost of inserting all generators. -/
def ssGensCost (Y : ℕ) : ℕ := (2 * 10 ^ 7 + 9000) * (ssW Y + 1) ^ 3

/-- **Inserting all generators.** -/
theorem ssGensLoop_spec {P : Program} {b ins sift chain setb app comp inv : ℕ}
    (hP : SsGenAt P b ins sift chain setb app comp inv) {B : List (Fin n)}
    {gs : List (Perm (Fin n))} {st0 : SsState n} (h0 : SsInv B gs st0) {Y : ℕ}
    (hY : n + B.length + gs.length + 2 ≤ Y) :
    FunDet P b (.list [ssCtx B gs, .nat gs.length, ssEncSt st0]) (ssEncSt (ssGens B gs st0))
      (ssGensCost Y) := by
  have hinv := ssGens_inv h0
  obtain ⟨-, hG, -, -⟩ := ss_W_facts hY
  refine (iter_spec hP.iter (Inv := fun i acc =>
      acc = ssEncSt ((List.range i).foldl (ssGenStep B gs) st0)) (M := ssW Y)
    (B := fun _ => ssGenCost Y) rfl (fun i acc hi h => by rw [h]; exact ss_st_wt (hinv i hi) hY)
    fun i acc hi h => ?_).mono fun w c ⟨hw, hc⟩ => ⟨hw, ?_⟩
  · rw [h]
    refine FunAll.mono (ssGenStepF_spec hP.step hP.insAt (hinv i hi.le) hi hY) fun w c ⟨hw, hc⟩ => ⟨?_, hc⟩
    show w = ssEncSt ((List.range (i + 1)).foldl (ssGenStep B gs) st0)
    rw [hw, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have hA : (Val.list [ssCtx B gs, .nat gs.length, ssEncSt st0]).wt ≤ 7 * (ssW Y + 1) :=
      (st_wt_list3 (ss_ctx_wt hY) ((wt_nat_le _).trans (by omega)) (ss_st_wt h0 hY)).trans
        (by omega)
    exact ss_iter_cost (V := ssW Y + 1) (c := 2 * 10 ^ 7) (p := 2) hc (by omega)
      (by unfold ssGenCost; exact le_rfl) hA (by omega) (by norm_num)

end GI.Impl
