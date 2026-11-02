import Workspace.Impl.SSRoundProg

/-!
# Rounds of pair steps, as programs

A round is the loop of `ssPairF` over `k < M²` (`ssRoundLoop_spec`). `ssRoundStepF` runs one
round, and the loop of it over `M + 1` rounds is `ssRoundsLoop_spec`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The parts of a round. -/
structure SsRoundAt (P : Program) (b ins sift chain setb app comp inv : ℕ) : Prop where
  iter : P.HasAt b (iterFuns b (b + 3))
  step : P.funs[b + 3]? = some (ssPairF ins comp)
  insAt : SsInsAt P ins sift chain setb app comp inv

/-- The cost of a round. -/
def ssRoundCost (Y : ℕ) : ℕ := (2 * 10 ^ 7 + 9000) * (ssW Y + 1) ^ 3

theorem ssPairs_inv {B : List (Fin n)} {gs : List (Perm (Fin n))} {st : SsState n}
    (h0 : SsInv B gs st) (i : ℕ) :
    SsInv B gs ((List.range i).foldl (ssPair B (B.length * n)) st) :=
  (ssPairs_spec rfl (List.range i) st h0).1

/-- **One round.** -/
theorem ssRoundLoop_spec {P : Program} {b ins sift chain setb app comp inv : ℕ}
    (hP : SsRoundAt P b ins sift chain setb app comp inv) {B : List (Fin n)}
    {gs : List (Perm (Fin n))} {st : SsState n} (h0 : SsInv B gs st) {Y : ℕ}
    (hY : n + B.length + gs.length + 2 ≤ Y) :
    FunDet P b (.list [ssCtx B gs, .nat (B.length * n * (B.length * n)), ssEncSt st])
      (ssEncSt (ssRound B (B.length * n) st)) (ssRoundCost Y) := by
  obtain ⟨hMM, -, -, -⟩ := ss_W_facts hY
  refine (iter_spec hP.iter (Inv := fun i acc =>
      acc = ssEncSt ((List.range i).foldl (ssPair B (B.length * n)) st)) (M := ssW Y)
    (B := fun _ => ssGenCost Y) rfl
    (fun i acc _ h => by rw [h]; exact ss_st_wt (ssPairs_inv h0 i) hY)
    fun i acc hi h => ?_).mono fun w c ⟨hw, hc⟩ => ⟨hw, ?_⟩
  · rw [h]
    refine FunAll.mono (ssPairF_spec hP.step hP.insAt (ssPairs_inv h0 i) hi hY)
      fun w c ⟨hw, hc⟩ => ⟨?_, hc⟩
    show w = ssEncSt ((List.range (i + 1)).foldl (ssPair B (B.length * n)) st)
    rw [hw, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have hA : (Val.list [ssCtx B gs, .nat (B.length * n * (B.length * n)), ssEncSt st]).wt ≤
        7 * (ssW Y + 1) :=
      (st_wt_list3 (ss_ctx_wt hY) ((wt_nat_le _).trans (by omega)) (ss_st_wt h0 hY)).trans
        (by omega)
    exact ss_iter_cost (V := ssW Y + 1) (c := 2 * 10 ^ 7) (p := 2) hc (by omega)
      (by unfold ssGenCost; exact le_rfl) hA (by omega) (by norm_num)

/-- The body of one round step, on `[c, r, st]`. -/
def ssRoundStepF (rb : ℕ) : Expr :=
  .call rb (mk3 (arg 0) (.arith .mul (.get (arg 0) (.nat 3)) (.get (arg 0) (.nat 3))) (arg 2))

/-- The cost of a round step. -/
def ssRoundStepCost (Y : ℕ) : ℕ := 3 * 10 ^ 7 * (ssW Y + 1) ^ 3

theorem ss_add_cost3 {W0 E : ℕ} (hE : E ≤ (2 * 10 ^ 7 + 9000) * (W0 + 1) ^ 3) :
    E + 300 * (10 * W0 + 10 + 1) ≤ 3 * 10 ^ 7 * (W0 + 1) ^ 3 := by
  have e : (W0 + 1) ^ 3 = (W0 + 1) * (W0 + 1) * (W0 + 1) := by ring
  have h1 := Nat.le_mul_of_pos_left (W0 + 1) (show 0 < W0 + 1 by omega)
  have h2 := Nat.le_mul_of_pos_right ((W0 + 1) * (W0 + 1)) (show 0 < W0 + 1 by omega)
  rw [e] at hE ⊢
  omega

theorem ssRoundStepF_spec {P : Program} {f rb ins sift chain setb app comp inv : ℕ}
    (hf : P.funs[f]? = some (ssRoundStepF rb)) (hP : SsRoundAt P rb ins sift chain setb app comp inv)
    {B : List (Fin n)} {gs : List (Perm (Fin n))} {st : SsState n} (h0 : SsInv B gs st)
    {Y : ℕ} (hY : n + B.length + gs.length + 2 ≤ Y) (r : ℕ) (hr : r + 2 ≤ ssW Y) :
    FunDet P f (.list [ssCtx B gs, .nat r, ssEncSt st])
      (ssEncSt (ssRound B (B.length * n) st)) (ssRoundStepCost Y) := by
  obtain ⟨hMM, -, -, h1000⟩ := ss_W_facts hY
  have hc := ss_ctx_wt hY
  have hs := ss_st_wt h0 hY
  have hs' : (ssEncSt (ssRound B (B.length * n) st)).wt ≤ ssW Y :=
    ss_st_wt (ssPairs_spec rfl (List.range (B.length * n * (B.length * n))) st h0).1 hY
  set W := 10 * ssW Y + 10 with hW
  clear_value W
  have hrW : (Val.nat r).wt ≤ ssW Y := (wt_nat_le r).trans hr
  have haw : (Val.list [ssCtx B gs, .nat r, ssEncSt st]).wt ≤ W :=
    (st_wt_list3 hc hrW hs).trans (by omega)
  have hMW : B.length * n + 2 ≤ W := by have := Nat.le_mul_self (B.length * n); omega
  have dArg : ∀ j v, [ssCtx B gs, .nat r, ssEncSt st][j]? = some v → v.wt ≤ ssW Y →
      StDC P [.list [ssCtx B gs, .nat r, ssEncSt st]] (arg j) v 3 0 W :=
    fun j v hv hw => StDC.arg hv haw
      (by have := (List.getElem?_eq_some_iff.mp hv).1; simp at this; omega) (by omega)
  have dM : StDC P [.list [ssCtx B gs, .nat r, ssEncSt st]] (.get (arg 0) (.nat 3))
      (.nat (B.length * n)) 5 0 W :=
    (StDC.get (v := .nat (B.length * n)) (dArg 0 _ rfl hc) (StDC.nat 3 (by omega)) rfl
      ((wt_nat_le _).trans hMW)).mono (by omega) le_rfl
  have dMM : StDC P [.list [ssCtx B gs, .nat r, ssEncSt st]]
      (.arith .mul (.get (arg 0) (.nat 3)) (.get (arg 0) (.nat 3)))
      (.nat (B.length * n * (B.length * n))) 11 0 W :=
    StDC.arith (op := .mul) dM dM rfl ((wt_nat_le _).trans (by omega))
  have dA := StDC.mk3 (dArg 0 _ rfl hc) dMM (dArg 2 _ rfl hs)
    ((st_wt_list3 hc ((wt_nat_le _).trans (by omega)) hs).trans (by omega)) (by omega)
  refine StDC.funDet hf (StDC.call dA (ssRoundLoop_spec hP h0 hY) (by omega))
    (ss_cost_fin2 (by norm_num) ?_)
  unfold ssRoundStepCost
  rw [hW]
  refine ss_add_cost3 ?_
  simp only [Nat.zero_add, Nat.add_zero, ssRoundCost, le_refl]

/-- The parts of the loop of rounds. -/
structure SsRoundsAt (P : Program) (b rb ins sift chain setb app comp inv : ℕ) : Prop where
  iter : P.HasAt b (iterFuns b (b + 3))
  step : P.funs[b + 3]? = some (ssRoundStepF rb)
  roundAt : SsRoundAt P rb ins sift chain setb app comp inv

theorem ssRounds_inv {B : List (Fin n)} {gs : List (Perm (Fin n))} {st : SsState n}
    (h0 : SsInv B gs st) (i : ℕ) :
    SsInv B gs ((List.range i).foldl (fun st _ => ssRound B (B.length * n) st) st) := by
  induction i with
  | zero => exact h0
  | succ i ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact (ssPairs_spec rfl _ _ ih).1

/-- The cost of all rounds. -/
def ssRoundsCost (Y : ℕ) : ℕ := (3 * 10 ^ 7 + 9000) * (ssW Y + 1) ^ 4

/-- **All rounds.** -/
theorem ssRoundsLoop_spec {P : Program} {b rb ins sift chain setb app comp inv : ℕ}
    (hP : SsRoundsAt P b rb ins sift chain setb app comp inv) {B : List (Fin n)}
    {gs : List (Perm (Fin n))} {st : SsState n} (h0 : SsInv B gs st) {Y : ℕ}
    (hY : n + B.length + gs.length + 2 ≤ Y) :
    FunDet P b (.list [ssCtx B gs, .nat (B.length * n + 1), ssEncSt st])
      (ssEncSt ((List.range (B.length * n + 1)).foldl
        (fun st _ => ssRound B (B.length * n) st) st)) (ssRoundsCost Y) := by
  obtain ⟨hMM, -, -, h1000⟩ := ss_W_facts hY
  have hMW : B.length * n + 1 + 2 ≤ ssW Y := by
    rcases Nat.lt_or_ge (B.length * n) 2 with h | h
    · omega
    · have := Nat.mul_le_mul_right (B.length * n) h; omega
  refine (iter_spec hP.iter (Inv := fun i acc =>
      acc = ssEncSt ((List.range i).foldl (fun st _ => ssRound B (B.length * n) st) st))
    (M := ssW Y) (B := fun _ => ssRoundStepCost Y) rfl
    (fun i acc _ h => by rw [h]; exact ss_st_wt (ssRounds_inv h0 i) hY)
    fun i acc hi h => ?_).mono fun w c ⟨hw, hc⟩ => ⟨hw, ?_⟩
  · rw [h]
    refine FunAll.mono (ssRoundStepF_spec hP.step hP.roundAt (ssRounds_inv h0 i) hY i
      (by omega)) fun w c ⟨hw, hc⟩ => ⟨?_, hc⟩
    show w = ssEncSt ((List.range (i + 1)).foldl (fun st _ => ssRound B (B.length * n) st) st)
    rw [hw, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have hA : (Val.list [ssCtx B gs, .nat (B.length * n + 1), ssEncSt st]).wt ≤
        7 * (ssW Y + 1) :=
      (st_wt_list3 (ss_ctx_wt hY) ((wt_nat_le _).trans (by omega)) (ss_st_wt h0 hY)).trans
        (by omega)
    exact ss_iter_cost (V := ssW Y + 1) (c := 3 * 10 ^ 7) (p := 3) hc (by omega)
      (by unfold ssRoundStepCost; exact le_rfl) hA (by omega) (by norm_num)

end GI.Impl
