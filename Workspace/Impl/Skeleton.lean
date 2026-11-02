import Workspace.Impl.Canon

/-!
# The recursion skeleton of obligation (a)

Obligation (a) of `GI.Assembly.final` (`Implements .solve Pg fs w`) is about the whole
recursion of Section 6. This file reduces it to one statement per procedure: a function for
`Solve`, one for `Continue` and one for `GiantStep`. They call each other through the function
table of the program.

## The interface of the recursive functions

`F : Funs` gives the indices of the three functions. A call of procedure `m` on a state `S`
receives an input value (`Iface.InVal`):

* `Solve`: any value of the state (`StateVal`), with any injective color code;
* `Continue`: a canonical value (`Canon`, `Workspace/Impl/Canon.lean`);
* `GiantStep`: a pair `[sv, lv]` of a canonical value of the state and a value `lv` of the
  supplied labels (Algorithm 5 passes the labels of the normalization to `GiantStep`). How the
  labels are stored is a choice of the implementation (`Iface.LabVal`, with a weight bound
  `Iface.labW`).

Every call returns a canonical answer (`AnsC`) of some run of its procedure, at a cost bounded
through the total cost of that run (`Iface.Post`).

## The work function

The implementation chooses the work `Iface.W nd` of the case it runs at a `Continue` or
`GiantStep` node, and the work `Iface.selW` of choosing the case. A `Solve` call may receive a
value of any weight (the first call does), so its own cost is a polynomial in the weight of its
input: `Ks (wt v + 1)^ds` for choosing the case and for the case itself.

The work function of the cost analysis is `Iface.work`. It charges each child's setup to its
parent:

* a `Solve` node does no work of its own (`work = 0`); this is why the bound `NodeBound'.solve`
  holds although a `Solve` node must read a value with `|Ω|` positions;
* a `Continue` or `GiantStep` node pays its case, its choice of case, the overhead of the
  dispatch (`ovh`), and the setup cost `charge` of each of its `Solve` children: since the child
  receives a canonical value, this setup is at most `K₀ (stateW + 1)^d₀`, a function of the
  child's state.

The first `Solve` call is not a child; its setup is paid by the weight of the input in (a).

A `Continue` or `GiantStep` node whose type has more than `N` points, or whose state stores a
number above `N` (`Small`), gets work `0` (`Fits`). Such nodes do not occur in the runs the
implementation makes (canonical inputs ask `k ≤ N` and `SmallInv`, `Canon.fits`, `Canon.small'`),
and `NodeBound'` could not hold at them: reading their input costs more than
`exp(cw (log(N+2))²)` when the type is huge or the numbers are large and `N` is tiny.

## The statements

* `Iface.CallOK m S`: the function of `m` meets its specification on every input value of `S`.
* `Iface.IH m S`: `CallOK` holds for every call that is smaller in the termination measure
  of `run_exists` (`GI.Algorithm.measure`, `MLt`) and satisfies its invariant
  (`GI.Algorithm.Good`).
* `Iface.ModeOK m`: on every state with the invariant, `IH` gives `CallOK`. This is what the
  body of the function of `m` must satisfy; `Workspace/Impl/Dispatch.lean` reduces it to one
  step specification per case.
* `Iface.callOK_all` (**the skeleton theorem**): if `ModeOK` holds for the three procedures,
  `CallOK` holds on every state with the invariant. The proof is well-founded induction on the
  measure.
* `Iface.implements`: then `Implements .solve Pg F.solve I.work`, obligation (a).
* `Iface.workBound`: obligation (c) for `I.work` follows from a bound on the work of each
  `Continue` and `GiantStep` node (`Iface.WorkReq`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val)
open scoped Pointwise

/-- The indices of the three recursive functions in the program. -/
structure Funs where
  solve : ℕ
  cont : ℕ
  giant : ℕ

/-- The function of procedure `m`. -/
def Funs.get (F : Funs) : Mode → ℕ
  | .solve => F.solve
  | .cont => F.cont
  | .giant => F.giant

/-- **The choices of an implementation** that the skeleton needs.

* `LabVal e S lv L`: `lv` stores the supplied labels `L` of `S`; `labW k N` bounds the weight of
  such a value on `k` positions in a phase of size `N`.
* `Ks, ds`: every case of `Solve`, and the choice between them, costs at most
  `Ks (wt v + 1)^ds` on an input value `v`.
* `W nd`: the work of the case at a `Continue` or `GiantStep` node, without its recursive calls.
* `selW m S`: the work of choosing the case of a `Continue` or `GiantStep` call on `S`. -/
structure Iface where
  LabVal : ∀ {Ω C : Type} {k : ℕ}, (Ω ≃ Fin k) → (S : State Ω C) → Val → SuppliedLabels S → Prop
  labW : ℕ → ℕ → ℕ
  Ks : ℕ
  ds : ℕ
  W : Node P₀ → ℝ
  selW : Mode → ∀ {Ω C : Type}, State Ω C → ℝ

namespace Iface

variable (I : Iface)

/-- The constant of the setup cost of `Solve`. -/
def K₀ : ℕ := 2 * I.Ks + 20000

/-- The exponent of the setup cost of `Solve`. -/
def d₀ : ℕ := max I.ds 6

theorem one_le_d₀ : 1 ≤ I.d₀ := le_max_of_le_right (by norm_num)

/-- **The input value of a call** of procedure `m` on `S`. -/
def InVal (m : Mode) {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (v : Val)
    (S : State Ω C) : Prop :=
  match m with
  | .solve => StateVal e c v S
  | .cont => Canon e c v S
  | .giant => ∃ (sv lv : Val) (L : SuppliedLabels S), v = .list [sv, lv] ∧ Canon e c sv S ∧
      I.LabVal e S lv L ∧ P₀.q₀ < L.q ∧ lv.wt ≤ I.labW k S.N

/-- The weight bound of the input of a `Continue` or `GiantStep` call. -/
noncomputable def inW (m : Mode) {Ω C : Type} (S : State Ω C) : ℕ :=
  match m with
  | .giant => 2 * (stateW (Nat.card Ω) S + I.labW (Nat.card Ω) S.N) + 6
  | _ => stateW (Nat.card Ω) S

theorem card_eq {Ω : Type} {k : ℕ} (e : Ω ≃ Fin k) : Nat.card Ω = k := by
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem InVal.wt_le {I : Iface} {m : Mode} {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ}
    {v : Val} {S : State Ω C} (hm : m ≠ .solve) (h : I.InVal m e c v S) :
    v.wt ≤ I.inW m S := by
  cases m with
  | solve => exact absurd rfl hm
  | cont =>
    simp only [inW, card_eq e]
    exact Canon.wt_le h
  | giant =>
    obtain ⟨sv, lv, L, rfl, hs, -, -, hl⟩ := h
    simp only [inW, card_eq e]
    have := wt_list2_le sv lv
    have := Canon.wt_le hs
    omega

/-- The input of a `Solve` call is a state value. -/
theorem InVal.stateVal_solve {I : Iface} {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ}
    {v : Val} {S : State Ω C} (h : I.InVal .solve e c v S) : StateVal e c v S := h

/-- The overhead of the dispatch of a `Continue` or `GiantStep` call (`Workspace/Impl/Dispatch`):
reading the input twice and passing the answer through at most nine levels. -/
noncomputable def ovh (m : Mode) {Ω C : Type} (S : State Ω C) : ℝ :=
  3 * (I.inW m S : ℝ) + 11 * (ansW (Nat.card Ω) : ℝ) + 300

/-- The setup cost of a `Solve` child, paid by its parent: a `Solve` call on a canonical value
costs at most `K₀ (stateW + 1)^d₀` besides the total cost of its own run. -/
noncomputable def charge (nd : Node P₀) : ℝ :=
  if nd.m = .solve then (I.K₀ : ℝ) * ((stateW (Nat.card nd.Ω) nd.S : ℝ) + 1) ^ I.d₀ else 0

/-- The work of a node itself: none for `Solve`; the case, the choice of case and the dispatch
overhead for `Continue` and `GiantStep`. -/
noncomputable def base (nd : Node P₀) : ℝ :=
  if nd.m = .solve then 0 else max 0 (I.W nd) + max 0 (I.selW nd.m nd.S) + I.ovh nd.m nd.S

/-- A node whose type fits its phase: a `Solve` node, or a node with at most `N` points whose
state stores only numbers up to `N`. The implementation only makes such nodes (`Canon.fits`,
`Canon.small'`). -/
def Fits (nd : Node P₀) : Prop := nd.m = .solve ∨ (Nat.card nd.Ω ≤ nd.S.N ∧ Small nd.S)

open Classical in
/-- **The work function**: the node's own work and the setup of its `Solve` children, at a node
that fits its phase. Other nodes do not occur in the runs that the implementation produces, and
get work `0`; without this, `NodeBound'` would fail at `Continue` nodes on huge types with a
tiny `N`. -/
noncomputable def work (nd : Node P₀) : ℝ :=
  if Fits nd then I.base nd + (nd.run.children.map I.charge).sum else 0

/-- The cost of a `Solve` call beyond the total cost of its run: its own work, a polynomial in
the weight of its input. It is zero for the other procedures. -/
noncomputable def excess (m : Mode) (v : Val) : ℝ :=
  if m = .solve then (I.K₀ : ℝ) * ((v.wt : ℝ) + 1) ^ I.d₀ else 0

/-- **The labels of a call** with input value `v`, as the label index of its run: none for
`Solve` and `Continue`, and for `GiantStep` the supplied labels that `v` stores (Algorithm 5,
`GiantStep(S, Γ)`: "for the supplied alternating label set"). -/
def LabOf (m : Mode) {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (v : Val) (S : State Ω C)
    (L : Option (SuppliedLabels S)) : Prop :=
  match m with
  | .giant => ∃ (sv lv : Val) (L' : SuppliedLabels S), v = .list [sv, lv] ∧
      I.LabVal e S lv L' ∧ L = some L'
  | _ => L = none

/-- **What a call returns**: a canonical answer of some run `r` of the procedure on the state,
with the labels of the call, at a cost of at most the total cost of `r` plus the excess of the
call. -/
def Post (m : Mode) {Ω C : Type} {k : ℕ} (S : State Ω C) (e : Ω ≃ Fin k) (v : Val) :
    Val → ℕ → Prop :=
  fun u cost => ∃ (A : Set (Perm Ω)) (L : Option (SuppliedLabels S)) (r : Run P₀ m S L A),
    I.LabOf m e v S L ∧ AnsC e u A ∧ (cost : ℝ) ≤ r.total I.work + I.excess m v

variable (Pg : Program) (F : Funs)

/-- **The specification of a call**: on every input value of `S`, the function of `m` returns
what `Post` says. -/
def CallOK (m : Mode) {Ω C : Type} (S : State Ω C) : Prop :=
  ∀ (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ), Function.Injective c → ∀ v : Val, I.InVal m e c v S →
    FunAll Pg (F.get m) v (I.Post m S e v)

/-- **The induction hypothesis**: every call with the invariant `Good` and a smaller measure
meets its specification. -/
def IH (m : Mode) {Ω C : Type} (S : State Ω C) : Prop :=
  ∀ (m' : Mode) {Ω' C' : Type} (T : State Ω' C'), Good P₀ m' T →
    MLt (measure P₀ m' T) (measure P₀ m S) → I.CallOK Pg F m' T

/-- **The specification of the body of the function of `m`**: under the induction hypothesis,
the call meets its specification. -/
def ModeOK (m : Mode) : Prop :=
  ∀ {Ω C : Type} (S : State Ω C), Good P₀ m S → I.IH Pg F m S → I.CallOK Pg F m S

/-- **The skeleton theorem.** If the functions of the three procedures meet `ModeOK`, every
call with the invariant meets its specification. Well-founded induction on the termination
measure of `run_exists`. -/
theorem callOK_all (h : ∀ m, I.ModeOK Pg F m) :
    ∀ (m : Mode) {Ω C : Type} (S : State Ω C), Good P₀ m S → I.CallOK Pg F m S := by
  suffices H : ∀ x, ∀ (m : Mode) {Ω C : Type} (S : State Ω C), Good P₀ m S →
      measure P₀ m S = x → I.CallOK Pg F m S from fun m {_ _} S hg => H _ m S hg rfl
  intro x
  induction x using MLt_wf.induction with
  | _ x ih =>
  intro m Ω C S hg hx
  subst hx
  exact h m S hg fun m' Ω' C' T hg' hlt => ih _ hlt m' T hg' rfl

/-! ### Obligation (a) -/

theorem charge_nonneg (nd : Node P₀) : 0 ≤ I.charge nd := by
  unfold charge
  split_ifs
  · positivity
  · exact le_rfl

theorem base_nonneg (nd : Node P₀) : 0 ≤ I.base nd := by
  unfold base ovh
  split_ifs
  · exact le_rfl
  · have := le_max_left 0 (I.W nd)
    have := le_max_left 0 (I.selW nd.m nd.S)
    positivity

theorem work_nonneg (nd : Node P₀) : 0 ≤ I.work nd := by
  unfold work
  split_ifs
  · exact add_nonneg (I.base_nonneg nd) (List.sum_nonneg fun x hx => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      exact I.charge_nonneg c)
  · exact le_rfl

/-- `T + K (x + 1)^d ≤ (K + 1) (T + x + 1)^d` for `T, x ≥ 0` and `d ≥ 1`. -/
theorem poly_absorb {T x : ℝ} (hT : 0 ≤ T) (hx : 0 ≤ x) (K d : ℕ) (hd : 1 ≤ d) :
    T + K * (x + 1) ^ d ≤ ((K : ℝ) + 1) * (T + x + 1) ^ d := by
  have h1 : (1 : ℝ) ≤ T + x + 1 := by linarith
  have h2 : (x + 1) ^ d ≤ (T + x + 1) ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d
  have h3 : T + x + 1 ≤ (T + x + 1) ^ d := by
    calc T + x + 1 = (T + x + 1) ^ 1 := (pow_one _).symm
      _ ≤ (T + x + 1) ^ d := pow_le_pow_right₀ h1 hd
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith

/-- **Obligation (a).** If the functions of the three procedures meet `ModeOK`, then function
`F.solve` implements `Solve` with the work function `I.work`. -/
theorem implements (h : ∀ m, I.ModeOK Pg F m) : Implements .solve Pg F.solve I.work := by
  refine ⟨I.K₀ + 1, I.d₀, ?_⟩
  intro Ω C _ S k e c hc v hv
  refine (I.callOK_all Pg F h .solve S trivial k e c hc v hv).mono ?_
  rintro u cost ⟨A, L, r, hL, hA, hcost⟩
  have hL' : L = none := hL
  subst hL'
  refine ⟨A, r, hA.answerVal, ?_⟩
  have hT := r.total_nonneg I.work_nonneg
  have := poly_absorb hT (Nat.cast_nonneg v.wt) I.K₀ I.d₀ I.one_le_d₀
  simp only [excess, if_true] at hcost
  push_cast
  linarith

/-! ### Obligation (c) -/

/-- **What obligation (c) needs from the implementation.** There is `cw ≥ 0` such that at every
`Continue` or `GiantStep` node with at most `N` positions (`N` the phase size), the work
`I.work nd` is at most `exp(cw (log(N+2))²)`. This work is the sum of

* the work `W nd` of the case and `selW` of choosing it,
* the dispatch overhead `ovh`, linear in the weight bound of the input and in `ansW`,
* the setup `K₀ (stateW (|Ω'|, T) + 1)^d₀` of each `Solve` child `T` (the threshold child,
  and the fresh calls of the row terminal and of the aggregation scripts).

Only nodes whose type has at most `N` points and whose state is `Small` count (`Fits`; the
others have work `0`). There every term but `W` and `selW` is polynomial in `N`
(`Workspace/Impl/Weights.lean`). -/
def WorkReq : Prop :=
  ∃ cw : ℝ, 0 ≤ cw ∧ ∀ nd : Node P₀, nd.m ≠ .solve → nd.S.size ≤ nd.S.N →
    Nat.card nd.Ω ≤ nd.S.N → Small nd.S → I.work nd ≤ expLogSq cw nd.S.N

/-- The children of a `Solve` node are `Continue` nodes (the fresh phase), so a `Solve` node
pays no setup. -/
theorem work_solve (nd : Node P₀) (h : nd.m = .solve) : I.work nd = 0 := by
  obtain ⟨m, Ω, C, S, L, A, r⟩ := nd
  simp only at h
  subst h
  cases r with
  | direct => simp [work, base, Run.children, Fits]
  | fresh => simp [work, base, Run.children, charge, Fits]

/-- **Obligation (c)** from `WorkReq`. -/
theorem workBound (h : I.WorkReq) : WorkBound I.work := by
  obtain ⟨cw, hcw, hw⟩ := h
  refine ⟨cw, hcw, I.work_nonneg, fun nd hm hs => ?_, fun nd hnd => ?_⟩
  · by_cases hf : Nat.card nd.Ω ≤ nd.S.N ∧ Small nd.S
    · exact hw nd hm hs hf.1 hf.2
    · have : ¬ Fits nd := by rintro (h | h) <;> contradiction
      rw [work, if_neg this]
      exact (Real.exp_pos _).le
  · rw [I.work_solve nd hnd]
    exact (Real.exp_pos _).le

end Iface

end GI.Impl
