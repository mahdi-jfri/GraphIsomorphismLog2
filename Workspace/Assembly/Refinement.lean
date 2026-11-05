module

public import Workspace.Assembly.Encoding
public import Workspace.Lang.Lib.Graph

@[expose] public section

/-!
# What a stage 2 program must do

This file states the three obligations of stage 2 as definitions. `GI.Assembly.final`
(`Workspace/Assembly/Final.lean`) proves `GraphIsomorphismInQuasipolynomialTime` from them.

* **(a) `Implements .solve Pg fs w`.** Function `fs` of the program `Pg` implements `Solve`: on
  the value of every state `S`, every evaluation returns the value of the answer `A` of some run
  `r` of `Solve` on `S` (at the parameters `P₀`), at a language cost of at most
  `K (r.total w + wt v + 1)^d`.
* **(b) `GraphWrapper Pg fm fs`.** Function `fm` is Algorithm 1 around `fs`: it builds the value
  of the pair state `graphState G H` from the input value (`BuildSpec`), calls `fs`, and turns
  the answer into the output format of the statement (`ConvertSpec`), each at polynomial cost.
* **(c) `WorkBound w`.** The work function `w` satisfies the work bounds `NodeBound' w cw` of
  Section 7.4 for some `cw ≥ 0`.

**The work function.** `w : Node P₀ → ℝ` is chosen by the implementation. (a) and (c) must hold
for the same `w`. The theorem does not depend on how `w` is chosen, because (a) ties the language
cost to `w` and (c) bounds `w`.

`w` cannot simply be the language cost spent at each node itself. A
`Solve` node may have a tiny domain on a large type `Ω` (a threshold leaf on a one-point orbit),
so its bound in (c) is `exp(cw (log 3)²)`, but it must read its input and write its answer, which
store permutations of all of `Ω`. So the setup of each `Solve` child is charged to its parent,
which has the bound `E_N` of its phase: a `Solve` node gets `w = 0`, and a `Continue` or
`GiantStep` node pays its own case and the setup of its `Solve` children. The first `Solve` call
is paid by `wt v` in (a). This is the work function `GI.Impl.Iface.work`
(`Workspace/Impl/Skeleton.lean`), and `GI.Impl.Iface.implements` proves (a) for it from one step
specification per case of the recursion (`Workspace/Impl/Cases.lean`).

`Implements` is stated for `Solve` only. A `Continue` or `GiantStep` call has an invariant
(`GI.Algorithm.Good`) and receives a canonical value (`GI.Impl.Canon`), so the internal
specification of these calls is `GI.Impl.Iface.CallOK`, not `Implements .cont` or
`Implements .giant`.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val)
open scoped Pointwise

/-! ### (a) Implementing a procedure -/

/-- **Obligation (a), for procedure `m`.** Function `f` of the program `Pg` implements procedure
`m` of the recursion at the parameters `P₀`, with the language cost tied to the work function
`w`. There are constants `K, d` such that the following holds. Let `S` be a state on a finite
type `Ω`, with an enumeration `e : Ω ≃ Fin k` of the positions and an injective code `c` of the
colors, and let `v` be a value of `S` (`StateVal`). Then every evaluation of `f` on `v` finishes,
and its result `u` and cost `cost` satisfy: there is a run `r : Run P₀ m S none A` (no labels)
such that `u` is the value of `A` (`AnswerVal`) and `cost ≤ K (r.total w + wt v + 1)^d`.

For `m = .solve` this can hold for every state, because `Solve` starts a fresh phase on the
faithful image of the domain (`Run.direct`, `Run.fresh`). It is used only with `m = .solve`; the
specification of the internal `Continue` and `GiantStep` calls, which holds only on states with
the invariant `Good` and on canonical values, is `GI.Impl.Iface.CallOK`. -/
def Implements (m : Mode) (Pg : Program) (f : ℕ) (w : Node P₀ → ℝ) : Prop :=
  ∃ K d : ℕ, ∀ {Ω C : Type} [Finite Ω] (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ),
    Function.Injective c → ∀ v : Val, StateVal e c v S →
      FunAll Pg f v fun u cost => ∃ (A : Set (Perm Ω)) (r : Run P₀ m S none A),
        AnswerVal e u A ∧ (cost : ℝ) ≤ K * (r.total w + v.wt + 1) ^ d

/-! ### (b) Algorithm 1 -/

/-- The positions of the pair state on `n` vertices, `Fin n × Fin n`, as numbers: `(u, v)` is
`n u + v`. -/
def pairEnum (n : ℕ) : Fin n × Fin n ≃ Fin (n * n) := finProdFinEquiv

/-- The colors of the pair state, `(diagonal, adjacent)`, as numbers: `2 diagonal + adjacent`. -/
def pairCode : Bool × Bool → ℕ := fun p => 2 * p.1.toNat + p.2.toNat

theorem pairCode_injective : Function.Injective pairCode := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  cases a <;> cases b <;> cases a' <;> cases b' <;> simp_all [pairCode]

/-- **Algorithm 1 as a main function.** On the input value: build the value of the pair state
(function `fb`), call `Solve` (function `fs`) on it, and convert the answer (function `fc`, on
the pair `[input, answer]`). -/
def mainBody (fb fs fc : ℕ) : Expr :=
  .letE (.call fb (.var 0)) (.letE (.call fs (.var 1)) (.call fc (mk2 (.var 0) (.var 2))))

open Classical in
/-- **Building the pair state.** On the input value of two graphs `G, H` on `n` vertices,
function `fb` returns a value of the pair state `graphState G H` of Algorithm 1 (positions
enumerated by `pairEnum`, colors coded by `pairCode`), at cost at most `K (n + 1)^d`. -/
def BuildSpec (Pg : Program) (fb : ℕ) : Prop :=
  ∃ K d : ℕ, ∀ (n : ℕ) (G H : SimpleGraph (Fin n)),
    FunAll Pg fb (inputVal G H) fun v cost =>
      StateVal (pairEnum n) pairCode v (graphState G H) ∧ cost ≤ K * (n + 1) ^ d

open Classical in
/-- **Converting the answer.** On `[input, u]`, where `u` is a value of the answer of the pair
state (`AnswerVal`), function `fc` returns a correct output in the format of the statement
(`AnswerOK`: `[0]`, or `1`, an isomorphism and generators of `Aut(G)`), at cost at most
`K (wt u + n + 1)^d`. -/
def ConvertSpec (Pg : Program) (fc : ℕ) : Prop :=
  ∃ K d : ℕ, ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) (u : Val),
    AnswerVal (pairEnum n) u (graphState G H).answer →
      FunAll Pg fc (.list [inputVal G H, u]) fun out cost =>
        AnswerOK G H out ∧ cost ≤ K * (u.wt + n + 1) ^ d

/-- **Obligation (b).** Function `fm` of `Pg` is Algorithm 1 around function `fs`: its body is
`mainBody fb fs fc`, where `fb` builds the pair state (`BuildSpec`) and `fc` converts the answer
(`ConvertSpec`). -/
def GraphWrapper (Pg : Program) (fm fs : ℕ) : Prop :=
  ∃ fb fc : ℕ, Pg.funs[fm]? = some (mainBody fb fs fc) ∧ BuildSpec Pg fb ∧ ConvertSpec Pg fc

/-! ### (c) The work bounds -/

/-- **Obligation (c).** The work function satisfies the work bounds of Section 7.4 for some
constant `cw ≥ 0` (`NodeBound'`): `w ≥ 0`; a `Continue` or `GiantStep` node with phase size `N`
and at most `N` positions does work at most `exp(cw (log(N+2))²)`; a `Solve` node on `s`
positions does work at most `exp(cw (log(s+2))²)`. -/
def WorkBound (w : Node P₀ → ℝ) : Prop :=
  ∃ cw : ℝ, 0 ≤ cw ∧ NodeBound' w cw

end GI.Assembly
