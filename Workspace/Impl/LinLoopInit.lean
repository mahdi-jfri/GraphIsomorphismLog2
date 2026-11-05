module

public import Workspace.Lang.Lib.Loop

@[expose] public section

/-! A bounded-accumulator loop with an explicit initialization cost. The
primary loop computes its iteration count by a polynomial-time maximum. -/
namespace GI.Impl
open GI.Cited GI.Lang

theorem linLoopBddInit_spec {P : Program} {b : ℕ} {kE acc0E step : Expr}
    (h : P.HasAt b (loopFuns b kE acc0E step)) {a : Val} {k : ℕ} {acc0 : Val} {ck c0 : ℕ}
    (hk : Det P [a] kE (.nat k) ck) (hacc : Det P [a] acc0E acc0 c0)
    {M : ℕ} {Inv : ℕ → Val → Prop} (h0 : Inv 0 acc0)
    (hM : ∀ i acc, i ≤ k → Inv i acc → acc.wt ≤ M) {D : ℕ → ℕ}
    (hstep : ∀ i acc, i < k → Inv i acc → EvalAll P [.list [a, .nat i, acc]] step
      (fun acc' cb => Inv (i + 1) acc' ∧ cb ≤ D i + 100 * (a.wt + k + M + 1))) :
    FunAll P b a (fun w cost => Inv k w ∧ cost ≤ ck + c0 + ∑ i ∈ Finset.range k, D i +
      loopModK * (k + 1) * (a.wt + k + M + 1)) := by
  refine (loopFuns_spec h hk hacc (Inv := Inv)
    (Step := fun i acc acc' cb => cb ≤ D i + 100 * (a.wt + k + M + 1)) h0
    (fun i acc hi hinv => (hstep i acc hi hinv).mono fun acc' cb hs => hs)).mono ?_
  rintro w cost ⟨cl, hl, hcost⟩
  obtain ⟨hinv, hcl⟩ := hl.le (fun i a a' cb _ _ hs => hs) hM
  refine ⟨hinv, ?_⟩
  have hw := hM k w le_rfl hinv
  have hacc0 := hM 0 acc0 (Nat.zero_le _) h0
  have h4 := wt_list4_le a (.nat k) (.nat 0) acc0
  have := wt_nat_le k
  have := wt_nat_le 0
  have h5 : k * (100 * (a.wt + k + M + 1)) ≤ (k + 1) * (100 * (a.wt + k + M + 1)) :=
    Nat.mul_le_mul_right _ (Nat.le_succ k)
  have hb := collect_bound (k := k) (X := a.wt + k + M + 1)
    (Y := 100 * (a.wt + k + M + 1) + loopK * (a.wt + k + M + 1)) (K := 900) (K' := 100)
    (Z := 100 * (a.wt + k + M + 1)) (by simp only [loopK]; omega) (by omega)
  have e : (k + 1) * (100 * (a.wt + k + M + 1) + loopK * (a.wt + k + M + 1)) =
      (k + 1) * (100 * (a.wt + k + M + 1)) + loopK * (k + 1) * (a.wt + k + M + 1) := by ring
  simp only [show (900 : ℕ) + 100 = loopModK from rfl] at hb
  omega

end GI.Impl
