import Workspace.Impl.TermCall
import Workspace.Impl.RowA18Prog
import Workspace.Impl.RowPart
import Workspace.Impl.Weights

/-!
# The assembly of the row terminal, as a hypothesis (T2–T7)

After its `(2q)² + q²` calls (`Workspace/Impl/TermCall.lean`), the row terminal computes its
answer from the two tables (Theorem A.23: the radical cosets, the solvable multicoset transport
of Theorem A.20, the labels and the lift). `TermAsmSpec` states what a program for that part must
do: on the input of the terminal function and the answers of the calls in the program's order
(`tmTests`, `tmCosets`), return a canonical value of the answer of the state, at a cost of at
most `expLogSq A N` (the work bound at `rowTerminal` nodes, Theorem A.23's additional time).

The calls of `RowTerminal.script` with the order `tmWithOrder` are the states `tmTestState` and
`tmCosetState` below (`tm_typeCall_eq`, `tm_cosetCall_eq` give the link for the row form built
from pure coordinates). Since the run of the script is exact, `AnsC e u S.answer` is what the
terminal function must return (`tm_final_exact`).

`TermAsmSpec` is the one explicit hypothesis for T2–T7. It asks no more than Theorem A.23 gives: the answer of the state, from the exact
tables, in `exp(O(log² N))` time.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

variable {Ω C : Type}

/-- A row string of the state: row `i` of `x` (`inl i`) or of `y` (`inr i`), on the row
coordinates `Fin m`. -/
def tmRowStr (S : State Ω C) {m q : ℕ} (E : Fin m × Fin q ≃ S.dom) :
    Fin q ⊕ Fin q → Fin m → C
  | .inl i => fun b => S.x (E (b, i))
  | .inr i => fun b => S.y (E (b, i))

/-- The `N`-test on the pair `ac` of rows, with `N = ⟨σN⟩`. -/
def tmTestState (S : State Ω C) {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    (σN : List (Perm (Fin m))) (ac : (Fin q ⊕ Fin q) × (Fin q ⊕ Fin q)) : State (Fin m) C :=
  rowState (gens σN) (tmRowStr S E ac.1) (tmRowStr S E ac.2)

/-- The coset call `Iso_H(x_i, y_j)`, with `H = ⟨σH⟩`. -/
def tmCosetState (S : State Ω C) {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    (σH : List (Perm (Fin m))) (ij : Fin q × Fin q) : State (Fin m) C :=
  rowState (gens σH) (tmRowStr S E (.inl ij.1)) (tmRowStr S E (.inr ij.2))

section Link

variable {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}

/-- **The `N`-tests of the terminal from pure coordinates are the states `tmTestState`.** -/
theorem tm_typeCall_eq (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {m : ℕ} (h0 : 0 < m)
    (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E) (P : Params)
    (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
    (hcard : Fintype.card (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B * L.q = S.size)
    (hsN : S.size ≤ S.N) (hN : 0 < S.N) (hqα : (S.N : ℝ) ^ P.α < L.q)
    (σN : List (Perm (Fin m))) (hσ : gens σN = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb)
    (ac : (Fin L.q ⊕ Fin L.q) × (Fin L.q ⊕ Fin L.q)) :
    (tmWithOrder ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P htr hcard hsN hN
      hqα)).typeCall ac = tmTestState S E σN ac := by
  obtain ⟨a, c⟩ := ac
  unfold RowTerminal.typeCall tmTestState
  rw [hσ]
  rcases a with a | a <;> rcases c with c | c <;> rfl

/-- **The coset calls of the terminal from pure coordinates are the states `tmCosetState`.** -/
theorem tm_cosetCall_eq (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {m : ℕ} (h0 : 0 < m)
    (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E) (P : Params)
    (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
      (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
    (hcard : Fintype.card (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B * L.q = S.size)
    (hsN : S.size ≤ S.N) (hN : 0 < S.N) (hqα : (S.N : ℝ) ^ P.α < L.q)
    (σH : List (Perm (Fin m))) (hσ : gens σH = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb)
    (ij : Fin L.q × Fin L.q) :
    (tmWithOrder ((RowForm.ofPure hnat hq E hP ⟨0, h0⟩).rowTerminal P htr hcard hsN hN
      hqα)).cosetCall ij = tmCosetState S E σH ij := by
  unfold RowTerminal.cosetCall tmCosetState
  rw [hσ]
  rfl

end Link

namespace Iface

variable (I : Iface) (Pg : Program)

/-- **The assembly of the row terminal** (T2–T7) at function `f`, with constant `A`: on the
input of the terminal function (`RowTermSpec`) and canonical answers `us`, `vs` of
the `N`-tests and the coset calls in the program's order, return a canonical value of the
answer of the state at a cost of at most `expLogSq A N`. The hypotheses are those of the
terminal function. -/
def TermAsmSpec (A : ℝ) (f : ℕ) : Prop :=
  ∀ {Ω C : Type} [Finite Ω] (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ),
    Function.Injective c →
    ∀ (sv lv : Val) (L : SuppliedLabels S), Canon e c sv S → LabValStd e S lv L →
    P₀.q₀ < L.q → Good P₀ .giant S → RowCase P₀.α S L.toGiantLabels →
    ∀ (label : Ω → Fin L.q) (hnat : NaturalRows S L.toGiantLabels label) (hq : 5 ≤ L.q)
      {m : ℕ} (h0 : 0 < m) (E : Fin m × Fin L.q ≃ S.dom)
      (hP : PureCoords S L.toGiantLabels label E)
      (σH σN σS : List (Perm (Fin m))),
      gens σH = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb →
      gens σN = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb →
      gens σS = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype →
      MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B →
      σH.length ≤ (k + L.q) ^ 2 → σN.length ≤ (k + L.q) ^ 2 → σS.length ≤ (k + L.q) ^ 2 →
      ∀ us vs : List Val,
      List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u (tmTestState S E σN ac).answer)
        us (tmTests L.q) →
      List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (tmCosetState S E σH ij).answer)
        vs (tmCosets L.q) →
      FunAll Pg f (.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
          encFun (rowLab e L.con.blocks)], .list us, .list vs])
        (fun u cost => AnsC e u S.answer ∧ (cost : ℝ) ≤ expLogSq A S.N)

end Iface

end GI.Impl
