import Workspace.Impl.AggItemCiDisp
import Workspace.Impl.AggItemCfObW

/-!
# The contract of the first-rectangle pair branch

This is the pair-stage contract restricted to `q > N^α`. Its start script is the
paper's first-rectangle item. The kept relation applies between all branches,
so the certificate, alignment, imprimitive pair and representations form fixed functions.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val)

variable {Ω C : Type} {k : ℕ}

/-- The first-rectangle script for one source--target choice. -/
noncomputable def itcsSb (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S}
    (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q) (ch : ItCfCh S L) : Script (Branches Ω) :=
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  (sojItem (RectOracle.ofReps ch.2) ch.1 X Y x₀ y₀).script

/-- On the large-label side of the exact test, the pair script is `sojItem`. -/
theorem itcs_sb_eq (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S}
    (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q)
    (hq : ¬ (L.q : ℝ) ≤ (S.N : ℝ) ^ P₀.α) :
    itCfSb e (.pair X x₀) (.pair Y y₀) = itcsSb e X Y x₀ y₀ := by
  classical
  funext ch
  simp only [itCfSb, cfgOutItem, if_neg hq, itcsSb]

/-- The object-weight field follows from the bounded object interface. -/
theorem itcs_objW {S : State Ω C} {L : SuppliedLabels S} {K : ItSCtx k S L} {B : ℕ}
    (hB : itCfObjB L.q (2 * L.q ^ P₀.κ) ≤ B) :
    ∀ b oX oY, ItCfObjOf K b oX oY →
      (∀ X x₀, oX = .pair X x₀ → (itCfOutV oX).wt ≤ B) ∧
        ∀ Y y₀, oY = .pair Y y₀ → (itCfOutV oY).wt ≤ B := by
  intro b oX oY ho
  have hw := itCfObjOf_wt ho
  exact ⟨fun _ _ _ => hw.1.trans hB, fun _ _ _ => hw.2.trans hB⟩

variable (I : Iface) (Pg : Program)

/-- The pair-stage obligations for the first rectangle. The bound covers cost,
kept values, item states, output lists, calls, and the pair-object values. -/
structure ItciSojAt (R : ItCfIRel) (fi fs fk : ℕ) (e : Ω ≃ Fin k) (c : C → ℕ)
    (S : State Ω C) (L : SuppliedLabels S) (K : ItSCtx k S L) (B : ℕ) : Prop where
  init : FunAll Pg fi K.v (fun w cost => ∃ E, R.Ki e c S L K w E ∧ cost ≤ B)
  ne : ∀ w E, R.Ki e c S L K w E → E.Nonempty
  wtK : ∀ w E, R.Ki e c S L K w E → w.wt ≤ B
  start : ∀ b X x₀ Y y₀ w E, ItCfObjOf K b (.pair X x₀) (.pair Y y₀) →
    ¬ (L.q : ℝ) ≤ (S.N : ℝ) ^ P₀.α → R.Ki e c S L K w E →
    FunAll Pg fs (.list [K.v, stTv b, itCfOutV (.pair X x₀), itCfOutV (.pair Y y₀), w])
      (fun w' cost => cost ≤ B ∧ ItCfIPost R e c S L K b (.pair X x₀) (.pair Y y₀) E
        (itcsSb e X Y x₀ y₀) B B w')
  wtR : ∀ b oX oY ist E sb f, R.Ri e c S L K b oX oY ist E sb f → ist.wt ≤ B
  step : ∀ b oX oY ist E sb f, R.Ri e c S L K b oX oY ist E sb f →
    FunAll Pg fk ist (fun w cost => cost ≤ B ∧ ItCfIPost R e c S L K b oX oY E sb f B w)
  objW : ∀ b oX oY, ItCfObjOf K b oX oY →
    (∀ X x₀, oX = .pair X x₀ → (itCfOutV oX).wt ≤ B) ∧
      ∀ Y y₀, oY = .pair Y y₀ → (itCfOutV oY).wt ≤ B

/-- Short local name of the first-rectangle context contract. -/
abbrev itcsAt {Ω C : Type} {k : ℕ} := @ItciSojAt Ω C k

/-- The init, start and step contract for `sojItem` at indices `fi`, `fs`, `fk`.
Its start obligation is restricted to pairs with `q > N^α`. -/
def ItciSojSpec (F : Funs) (fi fs fk : ℕ) (Xs : ℕ → ℕ) : Prop :=
  ∃ R : ItCfIRel, ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
    (sv lv : Val) (L : SuppliedLabels S), AsCall I Pg F e c S sv lv L →
    ∀ K : ItSCtx k S L, K.OK e c → (K.case = .twoB ∨ K.case = .three) →
      itcsAt Pg R fi fs fk e c S L K (Xs (I.inW .giant S))

end GI.Impl
