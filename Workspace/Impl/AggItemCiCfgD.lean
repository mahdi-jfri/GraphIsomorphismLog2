module

public import Workspace.Impl.AggItemCiDisp
public import Workspace.Impl.AggItemCiTest

@[expose] public section

/-!
# The pair part split by the exact test

The pair part `ItciPairSpec` is split by the exact test `q⁵ ≤ N²` (`itci_rpow_iff`,
`itci_test_spec`):
* `ItciCfgSpec`: the configuration branch (`cfgItem`, `q⁵ ≤ N²`). It does not change the
  choices, so it is stated for **any** kept relation `Ki` whose values weigh at most `Bk`;
  its item relation is `Rc Ki`.
* `ItciSojSpec` (`AggItemCiSojSpec`): the branch `sojItem` (`N² < q⁵`), with
  its own kept relation and init program.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

/-- The type of the kept relations of the item stage. -/
abbrev ItciKiT : Type 1 := ∀ {Ω C : Type} {k : ℕ}, (Ω ≃ Fin k) → (C → ℕ) → (S : State Ω C) →
  (L : SuppliedLabels S) → ItSCtx k S L → Val → Set (ItCfCh S L.toGiantLabels) → Prop

/-- The type of the item relations of the item stage. -/
abbrev ItciRiT : Type 1 := ∀ {Ω C : Type} {k : ℕ}, (Ω ≃ Fin k) → (C → ℕ) → (S : State Ω C) →
  (L : SuppliedLabels S) → ItSCtx k S L → (Fin (P₀.κ + 1) → Fin L.q) → CfgOut L.q →
  CfgOut L.q → Val → Set (ItCfCh S L.toGiantLabels) →
  (ItCfCh S L.toGiantLabels → Script (Branches Ω)) → ℕ → Prop

variable {Ω C : Type} {k : ℕ}

section Defs

variable (I : Iface) (Pg : Program)

/-- **The configuration branch** at the start `fs` and the step `fk`, with the bound `B`:
the start for pair objects when `q⁵ ≤ N²`, the weight of item states, and the step. -/
structure ItciCfgAt (R : ItCfIRel) (fs fk : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
    (L : SuppliedLabels S) (K : ItSCtx k S L) (B : ℕ) : Prop where
  start : ∀ b X x₀ Y y₀ w E, ItCfObjOf K b (.pair X x₀) (.pair Y y₀) → R.Ki e c S L K w E →
    L.q ^ 5 ≤ S.N ^ 2 →
    FunAll Pg fs (.list [K.v, stTv b, itCfOutV (.pair X x₀), itCfOutV (.pair Y y₀), w])
      (fun w' cost => cost ≤ B ∧ ItCfIPost R e c S L K b (.pair X x₀) (.pair Y y₀) E
        (itCfSb e (.pair X x₀) (.pair Y y₀)) B B w')
  wtR : ∀ b oX oY ist E sb f, R.Ri e c S L K b oX oY ist E sb f → ist.wt ≤ B
  step : ∀ b oX oY ist E sb f, R.Ri e c S L K b oX oY ist E sb f →
    FunAll Pg fk ist (fun w cost => cost ≤ B ∧ ItCfIPost R e c S L K b oX oY E sb f B w)

/-- **The contract of the configuration branch** at `fs`, `fk`: for every kept relation `Ki`
whose values weigh at most `Bk`, at a context whose pair objects weigh at most `Bk` (the start
program reads both objects, so its cost needs their weight; the pair part has this bound as
`objW`), the branch works with the item relation `Rc Ki` and the bound
`Xc W Bk`. -/
def ItciCfgSpec (F : Funs) (fs fk : ℕ) (Xc : ℕ → ℕ → ℕ) : Prop :=
  ∃ Rc : ItciKiT → ItciRiT, ∀ (Ki : ItciKiT) (Bk : ℕ) {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k)
    (c : C → ℕ) (S : State Ω C) (sv lv : Val) (L : SuppliedLabels S), AsCall I Pg F e c S sv lv L →
    ∀ K : ItSCtx k S L, K.OK e c → (K.case = .twoB ∨ K.case = .three) →
      (∀ w E, Ki e c S L K w E → E.Nonempty) → (∀ w E, Ki e c S L K w E → w.wt ≤ Bk) →
      (∀ b oX oY, ItCfObjOf K b oX oY →
        (∀ X x₀, oX = .pair X x₀ → (itCfOutV oX).wt ≤ Bk) ∧
          ∀ Y y₀, oY = .pair Y y₀ → (itCfOutV oY).wt ≤ Bk) →
      ItciCfgAt Pg ⟨Ki, Rc Ki⟩ fs fk e c S L K (Xc (I.inW .giant S) Bk)

end Defs

end GI.Impl
