import Workspace.Impl.AggCertPos
import Workspace.Impl.AggCertLoop

/-!
# The walk through the whole certificate phase

`AggCertPos.lean` names the remaining script inside the endpoint loop of one string of one test
set (`cpRound`, `cpWin`), for a continuation `K` that stands for the rest of the phase. This file
fixes that continuation and so names the remaining script at every position of the whole phase:

* `cpKx acc T Ts`: after the loop of `x` for the test set `T` ends at the stage `a`, the loop of
  `y` for `T`, then the other test sets `Ts`; the results `acc` of the earlier test sets come
  first in the output.
* `cpKy acc Ts a`: after the loop of `y` ends at the stage `b`, the other test sets.
* `CpPos`: the positions of the walk: the end (`fin`), the start of a round (`round`), and the
  inside of a round (`win`), with the results so far, the current test set, the other test sets,
  the string (`false` for `x`, `true` for `y`) and the round.
* `cpAt R p`: the remaining script at the position `p` for the coset representatives `R`.

The moves between positions that ask no call:

* `cpAt_start`: the phase itself is the start of the first round of `x` for the first test set;
* `cpAt_round_empty`: a round with an empty increment;
* `cpAt_x_end`: after the last round of `x`, the first round of `y`;
* `cpAt_y_end_cons`, `cpAt_y_end_nil`: after the last round of `y`, the next test set, or the end;
* `cpAt_close`: after the window calls of all representatives, the next round;
* `cpAt_narrow`: at the start of a round with a nonempty increment, the window calls of the
  representatives of a record.

`cpMeas` is a measure on positions that every move decreases (`cpMeas_*`): the number of
remaining positions, where one round counts for `D + 2` positions (`D` bounds the number of
representatives in one round). The step function of the phase recurses on it
(`stepOKC_of_move`), and it also bounds the number of remaining calls.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open scoped Pointwise

section Walk

variable {Ω C : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom] {q : ℕ}
  (πd : S.domGroup →* alternatingGroup (Fin q)) (x y : S.dom → C)

/-- The phase function `φ_T` of a test set. -/
noncomputable abbrev cpPhi (T : Finset (Fin q)) := phiT S.domGroup πd T

/-- The final continuation: the results `acc` of the finished test sets, then those of the
others. -/
def cpKfin (acc : List (StagePair S)) : List (StagePair S) → Script (List (StagePair S)) :=
  fun ps => Script.done (acc ++ ps)

/-- **After the loop of `y`** for a test set, with the final stage `a` of `x`: the other test
sets `Ts`. -/
noncomputable def cpKy (acc : List (StagePair S)) (Ts : List (Finset (Fin q)))
    (a : Subgroup (Perm S.dom) × Finset S.dom) :
    CosetRepFn S.dom → Subgroup (Perm S.dom) × Finset S.dom → Script (List (StagePair S)) :=
  fun R b => certFrom S πd R x y Ts (cpKfin S (acc ++ [(a, b)]))

/-- **After the loop of `x`** for the test set `T`: the loop of `y` for `T`, then the other test
sets `Ts`. -/
noncomputable def cpKx (acc : List (StagePair S)) (T : Finset (Fin q))
    (Ts : List (Finset (Fin q))) :
    CosetRepFn S.dom → Subgroup (Perm S.dom) × Finset S.dom → Script (List (StagePair S)) :=
  fun R a => (epFrom S R (cpPhi S πd T) y (Pgrp S.domGroup πd T, ∅)
    (Fintype.card S.dom)).bind (cpKy S πd x y acc Ts a R)

/-- **The positions of the walk.** -/
inductive CpPos (S : State Ω C) (q : ℕ) where
  /-- The end of the phase, with all results. -/
  | fin (acc : List (StagePair S))
  /-- The start of round `t` of the string `s` (`false` for `x`) for the test set `T`. -/
  | round (acc : List (StagePair S)) (T : Finset (Fin q)) (Ts : List (Finset (Fin q))) (s : Bool)
      (t : ℕ)
  /-- Inside round `t`, with the representatives `τs` still to come and the translated answers
  `acc'` collected so far. -/
  | win (acc : List (StagePair S)) (T : Finset (Fin q)) (Ts : List (Finset (Fin q))) (s : Bool)
      (t : ℕ) (τs : List (Perm S.dom)) (acc' : List (Set (Perm S.dom)))

/-- The string of a position: `x` for `false`, `y` for `true`. -/
def cpStr {V C' : Type} (x y : V → C') (s : Bool) : V → C' := if s then y else x

/-- The continuation of the loop of the string `s`. -/
noncomputable def cpK (acc : List (StagePair S)) (T : Finset (Fin q)) (Ts : List (Finset (Fin q))) :
    Bool → CosetRepFn S.dom → Subgroup (Perm S.dom) × Finset S.dom → Script (List (StagePair S))
  | false => cpKx S πd x y acc T Ts
  | true => cpKy S πd x y acc Ts (stage (cpPhi S πd T) x (Fintype.card S.dom))

/-- **The remaining script at a position**, for the coset representatives `R`. -/
noncomputable def cpAt (R : CosetRepFn S.dom) : CpPos S q → Script (List (StagePair S))
  | .fin acc => Script.done acc
  | .round acc T Ts s t => cpRound S (cpPhi S πd T) (cpStr x y s) (Fintype.card S.dom)
      (cpK S πd x y acc T Ts s) R t
  | .win acc T Ts s t τs acc' => cpWin S (cpPhi S πd T) (cpStr x y s) (Fintype.card S.dom)
      (cpK S πd x y acc T Ts s) R t τs acc'

/-! ### The moves -/

/-- **The start.** The certificate phase with the test sets `T :: Ts` is the start of the first
round of `x` for `T`. -/
theorem cpAt_start (κ : ℕ) (O : TestSetOrder q κ) (R : CosetRepFn S.dom) {T : Finset (Fin q)}
    {Ts : List (Finset (Fin q))} (hO : O.sets = T :: Ts) :
    certPhase S πd κ O R x y = cpAt S πd x y R (.round [] T Ts false 0) := by
  have h := certPhase_bind S πd R κ O x y Script.done
  rw [scr_bind_done] at h
  rw [h, hO, certFrom_cons]
  simp only [cpAt, cpRound, cpStr, cpK, Nat.sub_zero, Bool.false_eq_true, if_false]
  rfl

/-- **The start, without test sets.** -/
theorem cpAt_start_nil (κ : ℕ) (O : TestSetOrder q κ) (R : CosetRepFn S.dom)
    (hO : O.sets = []) : certPhase S πd κ O R x y = cpAt S πd x y R (.fin []) := by
  have h := certPhase_bind S πd R κ O x y Script.done
  rw [scr_bind_done] at h
  rw [h, hO, certFrom_nil]
  rfl

/-- **A round with an empty increment.** -/
theorem cpAt_round_empty (R : CosetRepFn S.dom) (acc : List (StagePair S)) (T : Finset (Fin q))
    (Ts : List (Finset (Fin q))) (s : Bool) {t : ℕ} (ht : t < Fintype.card S.dom)
    (h : inc (cpPhi S πd T) (cpStr x y s) t = ∅) :
    cpAt S πd x y R (.round acc T Ts s t) = cpAt S πd x y R (.round acc T Ts s (t + 1)) :=
  cpRound_empty S _ _ _ _ R ht h

/-- **The end of the loop of `x`**: the first round of `y`. -/
theorem cpAt_x_end (R : CosetRepFn S.dom) (acc : List (StagePair S)) (T : Finset (Fin q))
    (Ts : List (Finset (Fin q))) :
    cpAt S πd x y R (.round acc T Ts false (Fintype.card S.dom)) =
      cpAt S πd x y R (.round acc T Ts true 0) := by
  simp only [cpAt]
  rw [cpRound_end]
  simp only [cpK, cpKx, cpStr, cpRound, Nat.sub_zero, if_true, Bool.false_eq_true, if_false]
  rfl

/-- The pair of final stages of a test set. -/
noncomputable def cpPair (T : Finset (Fin q)) : StagePair S :=
  (stage (cpPhi S πd T) x (Fintype.card S.dom), stage (cpPhi S πd T) y (Fintype.card S.dom))

/-- **The end of the loop of `y`, with more test sets**: the first round of `x` for the next. -/
theorem cpAt_y_end_cons (R : CosetRepFn S.dom) (acc : List (StagePair S)) (T T' : Finset (Fin q))
    (Ts : List (Finset (Fin q))) :
    cpAt S πd x y R (.round acc T (T' :: Ts) true (Fintype.card S.dom)) =
      cpAt S πd x y R (.round (acc ++ [cpPair S πd x y T]) T' Ts false 0) := by
  simp only [cpAt]
  rw [cpRound_end]
  simp only [cpK, cpKy, cpStr, cpRound, Nat.sub_zero, if_true, Bool.false_eq_true, if_false]
  rw [certFrom_cons]
  refine scr_bind_congr _ fun a => scr_bind_congr _ fun b => ?_
  unfold cpKfin
  congr 1
  funext ps
  simp [cpPair, cpKfin]

/-- **The end of the loop of `y`, for the last test set**: the end of the phase. -/
theorem cpAt_y_end_nil (R : CosetRepFn S.dom) (acc : List (StagePair S)) (T : Finset (Fin q)) :
    cpAt S πd x y R (.round acc T [] true (Fintype.card S.dom)) =
      cpAt S πd x y R (.fin (acc ++ [cpPair S πd x y T])) := by
  simp only [cpAt]
  rw [cpRound_end]
  simp only [cpK, cpKy, certFrom_nil, cpKfin, List.append_nil]
  rfl

/-- **The next window call.** -/
theorem cpAt_win_cons (R : CosetRepFn S.dom) (acc : List (StagePair S)) (T : Finset (Fin q))
    (Ts : List (Finset (Fin q))) (s : Bool) (t : ℕ) (τ : Perm S.dom) (τs : List (Perm S.dom))
    (acc' : List (Set (Perm S.dom))) :
    cpAt S πd x y R (.win acc T Ts s t (τ :: τs) acc') =
      Script.ask .cont (windowCall S (kernelIn (cpPhi S πd T) (grp (cpPhi S πd T) (cpStr x y s) t))
          (inc (cpPhi S πd T) (cpStr x y s) t) (cpInv S (cpPhi S πd T) (cpStr x y s) t)
          (cpStr x y s) τ) fun B =>
        cpAt S πd x y R (.win acc T Ts s t τs (acc' ++ [winVal S τ B])) :=
  cpWin_cons S _ _ _ _ R t τ τs acc'

/-- **The end of a round**, for a candidate of a record that holds the representatives `l` of
the round: after the window calls of all of them, with the exact answers, the next round. -/
theorem cpAt_close {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) ×
    List (Perm S.dom))} {R : CosetRepFn S.dom} (hR : R ∈ Cands rec) (acc : List (StagePair S))
    (T : Finset (Fin q)) (Ts : List (Finset (Fin q))) (s : Bool) (t : ℕ) {l : List (Perm S.dom)}
    (hl : ((grp (cpPhi S πd T) (cpStr x y s) t,
      kernelIn (cpPhi S πd T) (grp (cpPhi S πd T) (cpStr x y s) t)), l) ∈ rec) :
    cpAt S πd x y R (.win acc T Ts s t [] (cpAcc S (cpPhi S πd T) (cpStr x y s) t l)) =
      cpAt S πd x y R (.round acc T Ts s (t + 1)) := by
  simp only [cpAt]
  rw [← cands_reps hR hl]
  exact cpWin_close S _ _ _ _ Pgrp_le R t

/-- **The start of a round with a nonempty increment**, narrowed to the candidates of a longer
record `rec'` that holds the representatives `l` of the round. -/
theorem cpAt_narrow {rec rec' : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) ×
    List (Perm S.dom))} (hsub : Cands rec' ⊆ Cands rec) (acc : List (StagePair S))
    (T : Finset (Fin q)) (Ts : List (Finset (Fin q))) (s : Bool) {t : ℕ}
    (ht : t < Fintype.card S.dom) (h : inc (cpPhi S πd T) (cpStr x y s) t ≠ ∅)
    {l : List (Perm S.dom)}
    (hl : ((grp (cpPhi S πd T) (cpStr x y s) t,
      kernelIn (cpPhi S πd T) (grp (cpPhi S πd T) (cpStr x y s) t)), l) ∈ rec') :
    (fun R => cpAt S πd x y R (.win acc T Ts s t l [])) '' Cands rec' ⊆
      (fun R => cpAt S πd x y R (.round acc T Ts s t)) '' Cands rec :=
  cpRound_narrow S _ _ _ _ hsub ht h hl

end Walk

/-! ### The measure -/

section Meas

variable {Ω C : Type} {S : State Ω C} {q : ℕ}

/-- The number of rounds before a round `t` of the string `s` ends the phase, counted in
blocks: the strings after it, each with `n + 1` round positions, and the rounds left in it. -/
def cpBase (n r : ℕ) (s : Bool) (t : ℕ) : ℕ := (2 * r + (if s then 0 else 1)) * (n + 1) + (n - t)

/-- **The measure of a position**: one round counts for `D + 2` positions. -/
def cpMeas (n D : ℕ) : CpPos S q → ℕ
  | .fin _ => 0
  | .round _ _ Ts s t => (cpBase n Ts.length s t + 1) * (D + 2)
  | .win _ _ Ts s t τs _ => cpBase n Ts.length s t * (D + 2) + τs.length + 1

variable {n D : ℕ}

theorem cpMeas_round_succ {acc : List (StagePair S)} {T : Finset (Fin q)}
    {Ts : List (Finset (Fin q))} {s : Bool} {t : ℕ} (ht : t < n) :
    cpMeas n D (.round acc T Ts s (t + 1)) < cpMeas n D (.round acc T Ts s t) := by
  simp only [cpMeas, cpBase]
  apply Nat.mul_lt_mul_of_pos_right _ (by omega)
  omega

theorem cpMeas_win_lt {acc : List (StagePair S)} {T : Finset (Fin q)}
    {Ts : List (Finset (Fin q))} {s : Bool} {t : ℕ} {τs : List (Perm S.dom)}
    {acc' : List (Set (Perm S.dom))} (hl : τs.length ≤ D) :
    cpMeas n D (.win acc T Ts s t τs acc') < cpMeas n D (.round acc T Ts s t) := by
  simp only [cpMeas]
  rw [Nat.add_mul, one_mul]
  omega

theorem cpMeas_win_cons {acc : List (StagePair S)} {T : Finset (Fin q)}
    {Ts : List (Finset (Fin q))} {s : Bool} {t : ℕ} {τ : Perm S.dom} {τs : List (Perm S.dom)}
    {acc' acc'' : List (Set (Perm S.dom))} :
    cpMeas n D (.win acc T Ts s t τs acc'') < cpMeas n D (.win acc T Ts s t (τ :: τs) acc') := by
  simp only [cpMeas, List.length_cons]
  omega

theorem cpMeas_close {acc : List (StagePair S)} {T : Finset (Fin q)}
    {Ts : List (Finset (Fin q))} {s : Bool} {t : ℕ} {acc' : List (Set (Perm S.dom))}
    (ht : t < n) :
    cpMeas n D (.round acc T Ts s (t + 1)) < cpMeas n D (.win acc T Ts s t [] acc') := by
  simp only [cpMeas, cpBase, List.length_nil]
  have : n - t = (n - (t + 1)) + 1 := by omega
  rw [this]
  nlinarith

theorem cpMeas_x_end {acc : List (StagePair S)} {T : Finset (Fin q)}
    {Ts : List (Finset (Fin q))} :
    cpMeas n D (.round acc T Ts true 0) < cpMeas n D (.round acc T Ts false n) := by
  simp only [cpMeas, cpBase, if_true, Bool.false_eq_true, if_false, Nat.sub_self, Nat.sub_zero]
  apply Nat.mul_lt_mul_of_pos_right _ (by omega)
  nlinarith

theorem cpMeas_y_end_cons {acc acc' : List (StagePair S)} {T T' : Finset (Fin q)}
    {Ts : List (Finset (Fin q))} :
    cpMeas n D (.round acc' T' Ts false 0) < cpMeas n D (.round acc T (T' :: Ts) true n) := by
  simp only [cpMeas, cpBase, if_true, Bool.false_eq_true, if_false, Nat.sub_self, Nat.sub_zero,
    List.length_cons]
  apply Nat.mul_lt_mul_of_pos_right _ (by omega)
  nlinarith

theorem cpMeas_y_end_nil {acc acc' : List (StagePair S)} {T : Finset (Fin q)} :
    cpMeas n D (.fin acc' : CpPos S q) < cpMeas n D (.round acc T [] true n) := by
  simp only [cpMeas]
  positivity

/-- The measure at the start of the phase. -/
theorem cpMeas_start {T : Finset (Fin q)} {Ts : List (Finset (Fin q))} :
    cpMeas n D (.round [] T Ts false 0 : CpPos S q) = (2 * Ts.length + 2) * (n + 1) * (D + 2) := by
  simp only [cpMeas, cpBase, Bool.false_eq_true, if_false, Nat.sub_zero]
  ring

end Meas

end GI.Impl
