module

public import Workspace.Assembly.ItemsReq
public import Workspace.Degree.Solved

@[expose] public section

/-!
# The contracts of the round in an extension of the final program

The degree-sensitive algorithm runs in a program `Pg'` that extends the final program `Pg` of the
general algorithm. Its round reuses the reading, the structure step and the three cases of the items
of the general algorithm. Their contracts (`RoundOK`, `Workspace/Assembly/ItemsReq.lean`) are proved
for `Pg`, and the chain of reductions returns them with `Solved` (`SolvedR`).

A contract of the round assumes a call `AsCall I Pg F …`, whose field `ih` is the induction
hypothesis of the general algorithm in the program `Pg`. In `Pg` this hypothesis holds at every
state, since every call of the general algorithm meets its specification (`callOK_all`). So a
contract moves from `Pg` to `Pg'`: the call in `Pg'` gives a call in `Pg` (`AsCall.down`), and the
result in `Pg` is a result in `Pg'` (`FunAll.of_sub`).

* `SolvedQ.ih_all`: the induction hypothesis of the general algorithm holds at every state.
* `IH.of_sub`: it moves to every extension.
* `RoundOK.of_sub`: the contracts of the round move to every extension.
* `SolvedR.parts`: what the degree-sensitive algorithm takes from the general algorithm, in one
  statement.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang
open GI.Cited (Val)

variable {Ω C : Type} {k : ℕ}

/-- **The induction hypothesis of the general algorithm holds at every state** of a solved program.
-/
theorem SolvedQ.ih_all {Pg : Program} {Q : Iface → Prop} (h : SolvedQ Pg Q) :
    ∃ R : Rest, Q R.iface ∧ ∀ (m : Mode) {Ω C : Type} (S : State Ω C), R.iface.IH Pg asmF m S := by
  obtain ⟨R, L, fm, hF, hL, -, -, hq⟩ := h
  refine ⟨R, hq, fun m Ω C S m' Ω' C' T hg _ => ?_⟩
  have hall := R.iface.callOK_all Pg L.F (Iface.Layout.modeOK R.iface Pg hL) m' T hg
  rwa [hF] at hall

/-- **The induction hypothesis moves to every extension of the program.** -/
theorem IH.of_sub {I : Iface} {Pg Pg' : Program} {F : Funs} (hs : Pg.Sub Pg') {m : Mode}
    {S : State Ω C} (h : I.IH Pg F m S) : I.IH Pg' F m S :=
  fun m' Ω' C' T hg hlt k e c hc v hv => (h m' T hg hlt k e c hc v hv).of_sub hs

/-- A call of the round in `Pg'` is a call in `Pg`, given the induction hypothesis in `Pg`. -/
theorem AsCall.down {I : Iface} {Pg Pg' : Program} {F : Funs} {e : Ω ≃ Fin k} {c : C → ℕ}
    {S : State Ω C} {sv lv : Val} {L : SuppliedLabels S} (h : AsCall I Pg' F e c S sv lv L)
    (hih : I.IH Pg F .giant S) : AsCall I Pg F e c S sv lv L :=
  ⟨h.inj, h.can, h.lab, h.q₀, h.lw, h.good, hih, h.hnot⟩

variable {I : Iface} {Pg Pg' : Program} {F : Funs}

/-- The hypothesis of the transfer: the induction hypothesis of the general algorithm in `Pg` at
every state. -/
def IHAll (I : Iface) (Pg : Program) (F : Funs) : Prop :=
  ∀ {Ω C : Type} (S : State Ω C), I.IH Pg F .giant S

theorem AsReadOK.of_sub (hs : Pg.Sub Pg') (hih : IHAll I Pg F) {H : AsHand} {X : ℕ → ℕ}
    {fr : ℕ} (h : AsReadOK I Pg F H X fr) : AsReadOK I Pg' F H X fr :=
  fun e c S sv lv L hc => (h e c S sv lv L (AsCall.down hc (hih S))).of_sub hs

theorem ItSStrOK.of_sub (hs : Pg.Sub Pg') (hih : IHAll I Pg F) {fstr : ℕ} {Xs : ℕ → ℕ}
    (h : ItSStrOK I Pg F fstr Xs) : ItSStrOK I Pg' F fstr Xs :=
  fun e c S sv lv L hc Ag sv' ps fx fy O h1 h2 h3 h4 h5 h6 =>
    (h e c S sv lv L (AsCall.down hc (hih S)) Ag sv' ps fx fy O h1 h2 h3 h4 h5 h6).of_sub hs

theorem ItSCaseAt.of_sub (hs : Pg.Sub Pg') {R : ItSCaseRel} {f0 fb : ℕ} {e : Ω ≃ Fin k}
    {c : C → ℕ} {S : State Ω C} {L : SuppliedLabels S} {K : ItSCtx k S L} {B : ℕ}
    (h : ItSCaseAt Pg R f0 fb e c S L K B) : ItSCaseAt Pg' R f0 fb e c S L K B :=
  ⟨FunAll.of_sub hs h.init, h.ne, h.wtK, h.start, h.wtR,
    fun b bst D sb f hb => FunAll.of_sub hs (h.step b bst D sb f hb)⟩

theorem ItSCaseOK.of_sub (hs : Pg.Sub Pg') (hih : IHAll I Pg F) {cs : AggCase → Prop}
    {f0 fb : ℕ} {Xc : ℕ → ℕ} (h : ItSCaseOK I Pg F cs f0 fb Xc) :
    ItSCaseOK I Pg' F cs f0 fb Xc := by
  obtain ⟨R, hR⟩ := h
  exact ⟨R, fun e c S sv lv L hc K hK hcs =>
    ItSCaseAt.of_sub hs (hR e c S sv lv L (AsCall.down hc (hih S)) K hK hcs)⟩

/-- **The contracts of the round move to every extension of the program.** -/
theorem RoundOK.of_sub (hs : Pg.Sub Pg') (hih : IHAll I Pg asmF) (h : RoundOK I Pg) :
    RoundOK I Pg' := by
  obtain ⟨⟨X, hX, hr⟩, ⟨Xs, hXs, hstr⟩, Xc, hXc, h1, h2, h3⟩ := h
  exact ⟨⟨X, hX, AsReadOK.of_sub hs hih hr⟩, ⟨Xs, hXs, ItSStrOK.of_sub hs hih hstr⟩, Xc, hXc,
    ItSCaseOK.of_sub hs hih h1, ItSCaseOK.of_sub hs hih h2, ItSCaseOK.of_sub hs hih h3⟩

/-- **What the degree-sensitive algorithm takes from the general algorithm**, for every extension
`Pg'` of a program with `SolvedR`: an interface `I = R.iface` whose labels are the standard ones,
the induction hypothesis of the general algorithm in `Pg'` at every state, the contracts of the
round in `Pg'`, and the general solver at `asmF.solve` in `Pg'`. -/
theorem SolvedR.parts {Pg : Program} (h : SolvedR Pg) (hs : Pg.Sub Pg') :
    ∃ R : Rest, (∀ k N, R.iface.labW k N = labWStd k N) ∧
      (∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) (lv : Val) (L : SuppliedLabels S),
        R.iface.LabVal e S lv L ↔ LabValStd e S lv L) ∧
      (∀ (m : Mode) {Ω C : Type} (S : State Ω C), R.iface.IH Pg' asmF m S) ∧
      RoundOK R.iface Pg' ∧ GeneralSolver Pg' asmF.solve := by
  obtain ⟨R, hq, hih⟩ := SolvedQ.ih_all h
  exact ⟨R, fun _ _ => rfl, fun _ _ _ _ => Iff.rfl, fun m _ _ S => IH.of_sub hs (hih m S),
    RoundOK.of_sub hs (fun S => hih .giant S) hq,
    (Solved.generalSolver (SolvedQ.solved h)).of_sub hs⟩

end GI.Degree
