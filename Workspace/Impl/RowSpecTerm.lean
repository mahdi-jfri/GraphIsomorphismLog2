import Workspace.Impl.Cases
import Workspace.Impl.RowA18Prog
import Workspace.Impl.RowPart
import Workspace.Impl.Weights

/-!
# The specification that the terminal row program must meet

The row step (`Iface.RowSpec`) first computes, on its input `[sv, lv]`,

* the row labels `rl = rowLab e L.con.blocks` of the positions (`rowPart_det`),
* pure coordinates `E : Fin m × Fin q ≃ dom` of Theorem A.17 (`coords_spec_good`), as the value
  `coordsVal e S E`,
* generators `σH`, `σN`, `σS` of `H`, `N`, `N*` and the number `t` of Theorem A.18
  (`a18_spec`), as the value `a18Out σH σN σS t`,

for the row form `RowForm.ofPure hnat hq E hP ⟨0, h0⟩`. If `t = 0` (`N` is transitive on the
row) it calls the terminal function `f` on

`[sv, lv, coordsVal e S E, a18Out σH σN σS t, encFun (rowLab e L.con.blocks)]`.

`RowTermSpec I Pg F Wt f` is what that call must do: return a canonical answer of a run that
starts with `Run.rowTerminal`, at a cost of at most `Wt r.node` plus the cost of the children of
the run (`Iface.childCost`). The work bound `Wt` is a parameter: the row step needs
`Wt nd + (the cost of the steps before the call) ≤ W nd` at `rowTerminal` nodes, and the
work requirement allows `expLogSq A N` there.

The hypotheses are those that the row step has at the call: the state invariant, the row case,
the input value, the induction hypothesis, and the facts that `coords_spec_good` and
`a18_spec` give about the values.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

namespace Iface

variable (I : Iface) (Pg : Program) (F : Funs)

/-- **The specification of the terminal row program** at function `f`, with work bound `Wt`. -/
def RowTermSpec (Wt : Node P₀ → ℝ) (f : ℕ) : Prop :=
  ∀ {Ω C : Type} [Finite Ω] (S : State Ω C) (k : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ),
    Function.Injective c →
    ∀ (sv lv : Val) (L : SuppliedLabels S), Canon e c sv S → LabValStd e S lv L →
    P₀.q₀ < L.q → Good P₀ .giant S → RowCase P₀.α S L.toGiantLabels →
    I.IH Pg F .giant S →
    ∀ (label : Ω → Fin L.q) (hnat : NaturalRows S L.toGiantLabels label) (hq : 5 ≤ L.q)
      {m : ℕ} (h0 : 0 < m) (E : Fin m × Fin L.q ≃ S.dom)
      (hP : PureCoords S L.toGiantLabels label E)
      (σH σN σS : List (Perm (Fin m))) (t : ℕ),
      Subgroup.closure {σ | σ ∈ σH} = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb →
      Subgroup.closure {σ | σ ∈ σN} = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nb →
      Subgroup.closure {σ | σ ∈ σS} = (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nstar.map
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Hb.subtype →
      t = 0 →
      MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
        (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B →
      σH.length ≤ (k + L.q) ^ 2 → σN.length ≤ (k + L.q) ^ 2 → σS.length ≤ (k + L.q) ^ 2 →
      FunAll Pg f (.list [sv, lv, coordsVal e S E, a18Out σH σN σS t,
          encFun (rowLab e L.con.blocks)])
        (fun u cost => ∃ (A : Set (Perm Ω)) (r : Run P₀ .giant S (some L) A),
          r.kind = .rowTerminal ∧ AnsC e u A ∧ (cost : ℝ) ≤ Wt r.node + I.childCost r)

end Iface

end GI.Impl
