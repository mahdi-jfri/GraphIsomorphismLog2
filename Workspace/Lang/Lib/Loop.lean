/-
The basic loop of the library: `for i from i₀ to k - 1, acc := g [c, i, acc]`.

`forBody self g` is the body of a function that must sit at index `self`; it calls the step
function `g`. Its argument is `[c, k, i, acc]`: a context `c` that every step sees, the bound
`k`, the counter `i` and the accumulator `acc`. It returns the final accumulator.

`forBody_spec` turns a specification of the step into one of the loop. The step may be
nondeterministic: it is described by an invariant `Inv i acc` and a relation
`Step i acc acc' cost` between the accumulators before and after step `i` and the cost of the
step's body. The loop's result comes with a trace `accs, costs` of the run (`LoopPost`), and its
cost is at most the sum of the step costs plus `loopK * (k - i₀ + 1) * (c.wt + k + M + 1)`,
for any bound `M` on the weights of the accumulators of the trace.

All other loops of the library are built on this one.
-/
import Workspace.Lang.Lib.Basic

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val)

/-- The body of the loop function, placed at index `self`, with step function `g`. -/
def forBody (self g : ℕ) : Expr :=
  .ite (.arith .lt (arg 2) (arg 1))
    (.call self (mk4 (arg 0) (arg 1) (.arith .add (arg 2) (.nat 1))
      (.call g (mk3 (arg 0) (arg 2) (arg 3)))))
    (arg 3)

/-- The constant of the overhead of the loop. -/
def loopK : ℕ := 300

/-- The result `w` and cost `cost` of the loop from `i₀` to `k` that starts with `acc`: there is
a trace `accs, costs` of accumulators and step costs that starts at `acc`, ends at `w`, keeps
`Inv`, makes steps in `Step`, and pays the step costs plus the overhead. -/
def LoopPost (Inv : ℕ → Val → Prop) (Step : ℕ → Val → Val → ℕ → Prop) (c : Val) (k i₀ : ℕ)
    (acc w : Val) (cost : ℕ) : Prop :=
  ∃ accs : ℕ → Val, ∃ costs : ℕ → ℕ, accs i₀ = acc ∧ accs k = w ∧
    (∀ i, i₀ ≤ i → i ≤ k → Inv i (accs i)) ∧
    (∀ i, i₀ ≤ i → i < k → Step i (accs i) (accs (i + 1)) (costs i)) ∧
    ∀ M, (∀ i, i₀ ≤ i → i ≤ k → (accs i).wt ≤ M) →
      cost ≤ ∑ i ∈ Finset.Ico i₀ k, costs i + loopK * (k - i₀ + 1) * (c.wt + k + M + 1)

/-- **The loop.** If every step `i < k` from an accumulator with `Inv i` gives one with
`Inv (i + 1)`, related by `Step`, then the loop from any `i₀ ≤ k` and any `acc` with `Inv i₀`
gives a result described by `LoopPost`. -/
theorem forBody_spec {P : Program} {self g : ℕ} (hself : P.funs[self]? = some (forBody self g))
    {c : Val} {k : ℕ} {Inv : ℕ → Val → Prop} {Step : ℕ → Val → Val → ℕ → Prop}
    (hstep : ∀ i acc, i < k → Inv i acc → FunAll P g (.list [c, .nat i, acc])
      (fun acc' cb => Inv (i + 1) acc' ∧ Step i acc acc' cb)) :
    ∀ i₀ acc, i₀ ≤ k → Inv i₀ acc →
      FunAll P self (.list [c, .nat k, .nat i₀, acc]) (LoopPost Inv Step c k i₀ acc) := by
  intro i₀ acc hi h0
  induction hd : k - i₀ generalizing i₀ acc with
  | zero =>
    have : i₀ = k := by omega
    subst this
    refine FunAll.intro hself ?_
    have hc : Det P [.list [c, .nat i₀, .nat i₀, acc]] (.arith .lt (arg 2) (arg 1)) (.nat 0) _ :=
      Det.arith' (Det.arg' rfl) (Det.arg' rfl) (by simp [BinOp.eval])
    refine (Det.ite_zero hc (Det.arg' (j := 3) rfl)).post fun cost hcost => ?_
    refine ⟨fun _ => acc, fun _ => 0, rfl, rfl, fun i h1 h2 => ?_, fun i h1 h2 => by omega,
      fun M hM => ?_⟩
    · rw [show i = i₀ by omega]; exact h0
    · have hA := wt_list4_le c (.nat i₀) (.nat i₀) acc
      have := wt_nat_le i₀
      have := hM i₀ le_rfl le_rfl
      simp only at this
      simp only [Finset.Ico_self, Finset.sum_empty, Nat.sub_self, loopK]
      omega
  | succ n ih =>
    have hlt : i₀ < k := by omega
    refine FunAll.intro hself ?_
    set A : List Val := [c, .nat k, .nat i₀, acc] with hAdef
    have hc : Det P [.list A] (.arith .lt (arg 2) (arg 1)) (.nat 1) _ :=
      Det.arith' (Det.arg' rfl) (Det.arg' rfl) (by simp [BinOp.eval, hlt])
    refine EvalAll.ite hc (fun _ _ h => ⟨1, h.1⟩) fun x cc hx => ?_
    obtain ⟨hx1, hcc⟩ := hx
    cases hx1
    simp only [one_ne_zero, if_false]
    -- the step
    have hB := Det.mk3 (P := P) (Det.arg' (vs := A) (rest := []) (j := 0) rfl) (Det.arg' (vs := A) (rest := []) (j := 2) rfl)
      (Det.arg' (vs := A) (rest := []) (j := 3) rfl)
    obtain ⟨CB, hB, hCB⟩ : ∃ CB, Det P [.list A] (mk3 (arg 0) (arg 2) (arg 3))
        (.list [c, .nat i₀, acc]) CB ∧
        CB ≤ 6 * (Val.list A).wt + 3 * (Val.list [c, .nat i₀, acc]).wt + 30 :=
      ⟨_, hB, by omega⟩
    have hg := EvalAll.call_funAll (f := g) hB (Q := fun acc' cg => ∃ cb, Inv (i₀ + 1) acc' ∧
        Step i₀ acc acc' cb ∧ cg ≤ CB + cb + acc'.wt + 1)
      (fun v ca h => by
        obtain ⟨rfl, hca⟩ := h
        exact (hstep i₀ acc hlt h0).mono fun w cb h => ⟨cb, h.1, h.2, by omega⟩)
    have hL := EvalAll.mk4_last (Det.arg' (vs := A) (j := 0) rfl) (Det.arg' (vs := A) (j := 1) rfl)
      (Det.arith' (op := .add) (Det.arg' (vs := A) (j := 2) rfl) (Det.nat 1) (z := i₀ + 1) rfl) hg
    refine EvalAll.call_funAll hL fun v ca h => ?_
    obtain ⟨acc', cg, ⟨cb, hInv, hStep, hcg⟩, rfl, hca⟩ := h
    refine (ih (i₀ + 1) acc' hlt hInv (by omega)).mono fun w cr hpost => ?_
    obtain ⟨accs, costs, ha0, hak, hainv, hastep, hacost⟩ := hpost
    refine ⟨fun j => if j = i₀ then acc else accs j, fun j => if j = i₀ then cb else costs j,
      by simp, by simp [show k ≠ i₀ by omega, hak], fun i h1 h2 => ?_, fun i h1 h2 => ?_,
      fun M hM => ?_⟩
    · by_cases h : i = i₀
      · simp only [h, if_true]; exact h0
      · simp only [h, if_false]; exact hainv i (by omega) h2
    · by_cases h : i = i₀
      · subst h
        simp only [if_true, show i + 1 ≠ i by omega, if_false, ha0]
        exact hStep
      · simp only [h, if_false, show i + 1 ≠ i₀ by omega]
        exact hastep i (by omega) h2
    · have hM' : ∀ i, i₀ + 1 ≤ i → i ≤ k → (accs i).wt ≤ M := fun i h1 h2 => by
        have := hM i (by omega) h2
        simp only [show i ≠ i₀ by omega, if_false] at this
        exact this
      have hcr := hacost M hM'
      have hsum : ∑ i ∈ Finset.Ico i₀ k, (if i = i₀ then cb else costs i) =
          cb + ∑ i ∈ Finset.Ico (i₀ + 1) k, costs i := by
        rw [Finset.sum_eq_sum_Ico_succ_bot hlt, if_pos rfl]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_Ico] at hi
        rw [if_neg (by omega)]
      rw [hsum]
      have hacc := hM i₀ le_rfl hlt.le
      simp only [if_true] at hacc
      have hacc' := hM' (i₀ + 1) le_rfl hlt
      rw [ha0] at hacc'
      have hw := hM' k (by omega) le_rfl
      rw [hak] at hw
      have hK : loopK * (k - i₀ + 1) * (c.wt + k + M + 1) =
          loopK * (k - (i₀ + 1) + 1) * (c.wt + k + M + 1) + loopK * (c.wt + k + M + 1) := by
        rw [show k - i₀ + 1 = (k - (i₀ + 1) + 1) + 1 by omega]; ring
      rw [hK]
      generalize loopK * (k - (i₀ + 1) + 1) * (c.wt + k + M + 1) = Y at hcr ⊢
      have hA : (Val.list A).wt ≤ _ := wt_list4_le c (.nat k) (.nat i₀) acc
      have hA' := wt_list4_le c (.nat k) (.nat (i₀ + 1)) acc'
      have hB' := wt_list3_le c (.nat i₀) acc
      have := wt_nat_le i₀
      have := wt_nat_le k
      have := wt_nat_le (i₀ + 1)
      simp only [loopK] at *
      omega

/-! ### Reading off a bound from the trace -/

/-- The cost of a loop from 0, when every step costs at most `D i + E` and every accumulator
with `Inv` weighs at most `M`. -/
theorem LoopPost.le {Inv : ℕ → Val → Prop} {Step : ℕ → Val → Val → ℕ → Prop} {c : Val} {k : ℕ}
    {acc w : Val} {cost : ℕ} (h : LoopPost Inv Step c k 0 acc w cost) {D : ℕ → ℕ} {E M : ℕ}
    (hS : ∀ i a a' cb, i < k → Inv i a → Step i a a' cb → cb ≤ D i + E)
    (hM : ∀ i a, i ≤ k → Inv i a → a.wt ≤ M) :
    Inv k w ∧ cost ≤ ∑ i ∈ Finset.range k, D i + k * E + loopK * (k + 1) * (c.wt + k + M + 1) := by
  obtain ⟨accs, costs, -, hak, hinv, hstep, hcost⟩ := h
  refine ⟨hak ▸ hinv k (Nat.zero_le _) le_rfl, ?_⟩
  have h1 := hcost M fun i _ hi => hM i _ hi (hinv i (Nat.zero_le _) hi)
  have h2 : ∑ i ∈ Finset.Ico 0 k, costs i ≤ ∑ i ∈ Finset.range k, (D i + E) := by
    rw [← Finset.range_eq_Ico]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact hS i _ _ _ hi (hinv i (Nat.zero_le _) hi.le) (hstep i (Nat.zero_le _) hi)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
  simp only [Nat.sub_zero] at h1
  omega

/-- The cost of a loop from 0 whose accumulators never get lighter, when step `i` costs at most
`D i + E + F * w'` for the weight `w'` of its new accumulator: the final accumulator bounds the
weights of all of them. -/
theorem LoopPost.le_mono {Inv : ℕ → Val → Prop} {Step : ℕ → Val → Val → ℕ → Prop} {c : Val}
    {k : ℕ} {acc w : Val} {cost : ℕ} (h : LoopPost Inv Step c k 0 acc w cost) {D : ℕ → ℕ}
    {E F : ℕ} (hS : ∀ i a a' cb, i < k → Inv i a → Step i a a' cb →
      a.wt ≤ a'.wt ∧ cb ≤ D i + E + F * a'.wt) :
    Inv k w ∧ cost ≤ ∑ i ∈ Finset.range k, D i +
      (k + 1) * (E + F * w.wt + loopK * (c.wt + k + w.wt + 1)) := by
  obtain ⟨accs, costs, ha0, hak, hinv, hstep, hcost⟩ := h
  have hmono : ∀ d i, i + d = k → (accs i).wt ≤ w.wt := by
    intro d
    induction d with
    | zero => intro i hi; rw [← hak, show i = k by omega]
    | succ d ih =>
      intro i hi
      have := (hS i _ _ _ (by omega) (hinv i (Nat.zero_le _) (by omega))
        (hstep i (Nat.zero_le _) (by omega))).1
      have := ih (i + 1) (by omega)
      omega
  refine ⟨hak ▸ hinv k (Nat.zero_le _) le_rfl, ?_⟩
  have h1 := hcost w.wt fun i _ hi => hmono (k - i) i (by omega)
  have h2 : ∑ i ∈ Finset.Ico 0 k, costs i ≤ ∑ i ∈ Finset.range k, (D i + (E + F * w.wt)) := by
    rw [← Finset.range_eq_Ico]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_range] at hi
    have h3 := (hS i _ _ _ hi (hinv i (Nat.zero_le _) hi.le) (hstep i (Nat.zero_le _) hi)).2
    have h4 := Nat.mul_le_mul_left F (hmono (k - (i + 1)) (i + 1) (by omega))
    omega
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
  simp only [Nat.sub_zero] at h1
  have e1 : (k + 1) * (E + F * w.wt + loopK * (c.wt + k + w.wt + 1)) =
      (k + 1) * (E + F * w.wt) + loopK * (k + 1) * (c.wt + k + w.wt + 1) := by ring
  have e2 : k * (E + F * w.wt) ≤ (k + 1) * (E + F * w.wt) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- Collect a bound of the form `(k + 1) * Y + Z` into `C * (k + 1) * X`. -/
theorem collect_bound {k X Y Z K K' : ℕ} (hY : Y ≤ K * X) (hZ : Z ≤ K' * X) :
    (k + 1) * Y + Z ≤ (K + K') * (k + 1) * X := by
  have h1 : (k + 1) * Y ≤ (k + 1) * (K * X) := Nat.mul_le_mul_left _ hY
  have h2 : K' * X ≤ (k + 1) * (K' * X) := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
  have : (K + K') * (k + 1) * X = (k + 1) * (K * X) + (k + 1) * (K' * X) := by ring
  omega

/-! ### Loop modules

A loop module occupies three consecutive indices `b, b + 1, b + 2`: an entry function, the loop
`forBody (b + 1) (b + 2)` and the step. The entry, called on `a`, runs the loop with context `a`,
the bound given by `kE` and the start accumulator given by `acc0E`; both are expressions over the
environment `[a]`. The step's argument is `[a, i, acc]`. -/

/-- The three functions of a loop module at base `b`. -/
def loopFuns (b : ℕ) (kE acc0E step : Expr) : List Expr :=
  [.call (b + 1) (mk4 (.var 0) kE (.nat 0) acc0E), forBody (b + 1) (b + 2), step]

theorem Program.HasAt.loopFuns_entry {P : Program} {b : ℕ} {kE acc0E step : Expr}
    (h : P.HasAt b (loopFuns b kE acc0E step)) :
    P.funs[b]? = some (.call (b + 1) (mk4 (.var 0) kE (.nat 0) acc0E)) := by
  simpa [loopFuns] using h 0 (by simp [loopFuns])

theorem Program.HasAt.loopFuns_loop {P : Program} {b : ℕ} {kE acc0E step : Expr}
    (h : P.HasAt b (loopFuns b kE acc0E step)) : P.funs[b + 1]? = some (forBody (b + 1) (b + 2)) := by
  simpa [loopFuns] using h 1 (by simp [loopFuns])

theorem Program.HasAt.loopFuns_step {P : Program} {b : ℕ} {kE acc0E step : Expr}
    (h : P.HasAt b (loopFuns b kE acc0E step)) : P.funs[b + 2]? = some step := by
  simpa [loopFuns] using h 2 (by simp [loopFuns])

/-- **A loop module.** The entry on `a` runs the loop of `forBody_spec` from 0 to `k`, where `k`
and the start `acc0` are the values of `kE` and `acc0E`. -/
theorem loopFuns_spec {P : Program} {b : ℕ} {kE acc0E step : Expr}
    (h : P.HasAt b (loopFuns b kE acc0E step)) {a : Val} {k : ℕ} {acc0 : Val} {ck c0 : ℕ}
    (hk : Det P [a] kE (.nat k) ck) (hacc : Det P [a] acc0E acc0 c0)
    {Inv : ℕ → Val → Prop} {Step : ℕ → Val → Val → ℕ → Prop} (h0 : Inv 0 acc0)
    (hstep : ∀ i acc, i < k → Inv i acc → EvalAll P [.list [a, .nat i, acc]] step
      (fun acc' cb => Inv (i + 1) acc' ∧ Step i acc acc' cb)) :
    FunAll P b a (fun w cost => ∃ cl, LoopPost Inv Step a k 0 acc0 w cl ∧
      cost ≤ ck + c0 + cl + 4 * (Val.list [a, .nat k, .nat 0, acc0]).wt + a.wt + w.wt + 15) := by
  refine FunAll.intro h.loopFuns_entry ?_
  refine EvalAll.call_funAll (Det.mk4 (Det.var' rfl) hk (Det.nat 0) hacc) fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine (forBody_spec h.loopFuns_loop (fun i acc hi hacc =>
    FunAll.intro h.loopFuns_step (hstep i acc hi hacc)) 0 acc0 (Nat.zero_le _) h0).mono
    fun w cl hl => ⟨cl, hl, by omega⟩

/-! ### Loop modules with simple bounds -/

/-- The constant of `loopMono_spec` and `loopBdd_spec`. -/
def loopModK : ℕ := 1000

/-- **A loop module whose accumulator grows.** Every step keeps `Inv`, does not make the
accumulator lighter, and costs at most `D i + 100 * (a.wt + k + acc'.wt + 1)`. Then the module's
result `w` has `Inv k w`, at cost at most `∑ D i + loopModK * (k + 1) * (a.wt + k + w.wt + 1)`. -/
theorem loopMono_spec {P : Program} {b : ℕ} {kE acc0E step : Expr}
    (h : P.HasAt b (loopFuns b kE acc0E step)) {a : Val} {k : ℕ} {acc0 : Val} {ck c0 : ℕ}
    (hk : Det P [a] kE (.nat k) ck) (hacc : Det P [a] acc0E acc0 c0)
    (hc : ck + c0 ≤ 10 * (a.wt + k + 1)) (hacc0 : acc0.wt ≤ 2 * a.wt + 5)
    {Inv : ℕ → Val → Prop} (h0 : Inv 0 acc0) {D : ℕ → ℕ}
    (hstep : ∀ i acc, i < k → Inv i acc → EvalAll P [.list [a, .nat i, acc]] step
      (fun acc' cb => Inv (i + 1) acc' ∧ acc.wt ≤ acc'.wt ∧
        cb ≤ D i + 100 * (a.wt + k + acc'.wt + 1))) :
    FunAll P b a (fun w cost => Inv k w ∧
      cost ≤ ∑ i ∈ Finset.range k, D i + loopModK * (k + 1) * (a.wt + k + w.wt + 1)) := by
  refine (loopFuns_spec h hk hacc (Inv := Inv)
    (Step := fun i acc acc' cb => acc.wt ≤ acc'.wt ∧ cb ≤ D i + 100 * (a.wt + k + 1) + 100 * acc'.wt)
    h0 fun i acc hi hinv => (hstep i acc hi hinv).mono fun acc' cb h =>
      ⟨h.1, h.2.1, by omega⟩).mono ?_
  rintro w cost ⟨cl, hl, hcost⟩
  obtain ⟨hinv, hcl⟩ := hl.le_mono (fun i a a' cb _ _ hs => hs)
  refine ⟨hinv, ?_⟩
  have h4 := wt_list4_le a (.nat k) (.nat 0) acc0
  have := wt_nat_le k
  have := wt_nat_le 0
  have := a.two_le_size
  have := a.size_le_wt
  have hb := collect_bound (k := k) (X := a.wt + k + w.wt + 1)
    (Y := 100 * (a.wt + k + 1) + 100 * w.wt + loopK * (a.wt + k + w.wt + 1)) (K := 900) (K' := 100)
    (Z := 100 * (a.wt + k + w.wt + 1)) (by simp only [loopK]; omega) (by omega)
  simp only [show (900 : ℕ) + 100 = loopModK from rfl] at hb
  omega

/-- **A loop module with a bounded accumulator.** Every accumulator with `Inv` weighs at most
`M`, and every step keeps `Inv` and costs at most `D i + 100 * (a.wt + k + M + 1)`. Then the
module's result `w` has `Inv k w`, at cost at most
`∑ D i + loopModK * (k + 1) * (a.wt + k + M + 1)`. -/
theorem loopBdd_spec {P : Program} {b : ℕ} {kE acc0E step : Expr}
    (h : P.HasAt b (loopFuns b kE acc0E step)) {a : Val} {k : ℕ} {acc0 : Val} {ck c0 : ℕ}
    (hk : Det P [a] kE (.nat k) ck) (hacc : Det P [a] acc0E acc0 c0)
    (hc : ck + c0 ≤ 10 * (a.wt + k + 1)) {M : ℕ}
    {Inv : ℕ → Val → Prop} (h0 : Inv 0 acc0) (hM : ∀ i acc, i ≤ k → Inv i acc → acc.wt ≤ M)
    {D : ℕ → ℕ}
    (hstep : ∀ i acc, i < k → Inv i acc → EvalAll P [.list [a, .nat i, acc]] step
      (fun acc' cb => Inv (i + 1) acc' ∧ cb ≤ D i + 100 * (a.wt + k + M + 1))) :
    FunAll P b a (fun w cost => Inv k w ∧
      cost ≤ ∑ i ∈ Finset.range k, D i + loopModK * (k + 1) * (a.wt + k + M + 1)) := by
  refine (loopFuns_spec h hk hacc (Inv := Inv)
    (Step := fun i acc acc' cb => cb ≤ D i + 100 * (a.wt + k + M + 1))
    h0 fun i acc hi hinv => (hstep i acc hi hinv).mono fun acc' cb h => h).mono ?_
  rintro w cost ⟨cl, hl, hcost⟩
  obtain ⟨hinv, hcl⟩ := hl.le (fun i a a' cb _ _ hs => hs) hM
  refine ⟨hinv, ?_⟩
  have hw := hM k w le_rfl hinv
  have hacc0 := hM 0 acc0 (Nat.zero_le _) h0
  have h4 := wt_list4_le a (.nat k) (.nat 0) acc0
  have := wt_nat_le k
  have := wt_nat_le 0
  have := a.two_le_size
  have := a.size_le_wt
  have h5 : k * (100 * (a.wt + k + M + 1)) ≤ (k + 1) * (100 * (a.wt + k + M + 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  have hb := collect_bound (k := k) (X := a.wt + k + M + 1)
    (Y := 100 * (a.wt + k + M + 1) + loopK * (a.wt + k + M + 1)) (K := 900) (K' := 100)
    (Z := 100 * (a.wt + k + M + 1)) (by simp only [loopK]; omega) (by omega)
  simp only [show (900 : ℕ) + 100 = loopModK from rfl] at hb
  have e : (k + 1) * (100 * (a.wt + k + M + 1) + loopK * (a.wt + k + M + 1)) =
      (k + 1) * (100 * (a.wt + k + M + 1)) + loopK * (k + 1) * (a.wt + k + M + 1) := by ring
  omega

/-- The weight of the argument of a step. -/
theorem wt_stepArg_le (a : Val) (i : ℕ) (acc : Val) :
    (Val.list [a, .nat i, acc]).wt ≤ 2 * (a.wt + i + acc.wt) + 11 := by
  have := wt_list3_le a (.nat i) acc
  have := wt_nat_le i
  omega

end GI.Lang
