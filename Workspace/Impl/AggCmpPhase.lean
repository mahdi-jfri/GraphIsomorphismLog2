module

public import Workspace.Impl.AggCmpHand
public import Workspace.Impl.AggCmpCall
public import Workspace.Impl.AggCmpWalk
public import Workspace.Impl.AggCertLoop

@[expose] public section

/-!
# The comparison phase, from a move function, and the hand-over to the items

This file does for the comparison phase what `AggCertPhase.lean` does for the certificate phase,
and closes the phase with the hand-over `ItHand` to the items.

* `CmCands Cs Ag₀ O rec`: the candidate rounds while the phase runs. They lie in `Cs`, have the
  certificate script of `Ag₀`, the order `O` of the test tuples, and representatives of the
  comparison cosets that agree with the record `rec` of the program's choices (`CmPicks`). For
  the empty record the set is nonempty (`cmCands_nonempty`, from `cmHand_mem`).
* `cmOutV`: the value the phase returns: the first five entries of the state, then the test
  tuples in the order `O` and the results of the comparisons, in the order of the run.
* `cm_out_itHand`: if the run of the comparison script of a candidate has result `a`, then
  `cmOutV … O.tuples a` meets `ItHand` for the candidates with the same comparison script. The
  results are the table of `CompareRel` (`Exec.exact`, `st_compTable`).
* `cm_phase_spec`: for any move function that meets the condition of `stepOKC_of_move` for a
  relation `Rep`, the runner returns a run of the comparison script of a candidate, with its
  output.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val)

variable {k : ℕ} {Ω C : Type}

/-! ### Candidates -/

/-- **The candidate rounds of the comparison phase.** -/
def CmCands {S : State Ω C} {L : SuppliedLabels S} (Cs : Set (Aggregation P₀ S L.toGiantLabels))
    (Ag₀ : Aggregation P₀ S L.toGiantLabels) (O : TestTupleOrder L.q P₀.κ)
    (rec : List (Set (Perm S.dom) × Option (Perm S.dom))) : Set (Aggregation P₀ S L.toGiantLabels) :=
  {Ag | Ag ∈ Cs ∧ Ag.certScript = Ag₀.certScript ∧ Ag.tests = O ∧ Ag.pick ∈ CmPicks rec}

/-- A longer record has fewer candidates. -/
theorem cmCands_cons {S : State Ω C} {L : SuppliedLabels S}
    {Cs : Set (Aggregation P₀ S L.toGiantLabels)} {Ag₀ : Aggregation P₀ S L.toGiantLabels}
    {O : TestTupleOrder L.q P₀.κ} {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    (p : Set (Perm S.dom) × Option (Perm S.dom)) :
    CmCands Cs Ag₀ O (p :: rec) ⊆ CmCands Cs Ag₀ O rec :=
  fun _ h => ⟨h.1, h.2.1, h.2.2.1, cmPicks_cons p h.2.2.2⟩

/-- **The candidates of the empty record**: `Ag₀` with the order `O` and any representatives. -/
theorem cmCands_nonempty {S : State Ω C} {L : SuppliedLabels S}
    {Cs : Set (Aggregation P₀ S L.toGiantLabels)} {Ag₀ : Aggregation P₀ S L.toGiantLabels}
    (hAg₀ : Ag₀ ∈ Cs) (hsub : Cs ⊆ asRounds L)
    (hcl : ∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag ∈ Cs)
    (O : TestTupleOrder L.q P₀.κ) : (CmCands Cs Ag₀ O []).Nonempty :=
  ⟨{ Ag₀ with tests := O, pick := PickFn.default S.dom },
    cmHand_mem hAg₀ hsub hcl O _, rfl, rfl, fun _ h => by cases h⟩

/-! ### The output of the phase -/

/-- **The value the phase returns**: `[sv, [k, q], ⟨ps⟩, ⟨fx⟩, ⟨fy⟩, [⟨tuples⟩, ⟨results⟩]]`. -/
noncomputable def cmOutV {q κ : ℕ} (sv : Val) (k : ℕ) (ps fx fy : GPairs k q)
    (tt : List (TestTuple q κ)) (a : List Bool) : Val :=
  .list [sv, .list [.nat k, .nat q], .list (ps.map pairV), .list (fx.map pairV),
    .list (fy.map pairV), .list [.list (tt.map stTT), .list (a.map boolVal)]]

/-- **The results of a run are the table of `CompareRel`.** -/
theorem cm_out_eq {S : State Ω C} {L : SuppliedLabels S} {Ag : Aggregation P₀ S L.toGiantLabels}
    {a : List Bool} (ex : Exec P₀ Ag.compScript a) (sv : Val) (ps fx fy : GPairs k L.q) :
    cmOutV sv k ps fx fy Ag.tests.tuples a =
      itSt sv k L.q ps fx fy Ag.tests.tuples (itCr Ag.fin S Ag.πd P₀.κ) := by
  have ha := ex.exact
  rw [st_compTable] at ha
  unfold cmOutV itSt stCv
  rw [ha]
  haveI := Ag.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  have hcr : ∀ x y, stCr S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y) x y =
      itCr Ag.fin S Ag.πd P₀.κ x y := by
    intro x y
    unfold itCr stCr
    congr 1
    convert rfl
  have hfun : stCr S Ag.πd P₀.κ (dstr S S.x) (dstr S S.y) = itCr Ag.fin S Ag.πd P₀.κ :=
    funext fun x => funext fun y => hcr x y
  rw [hfun]

/-- The candidates agree on `πd`, so on the lifts of the certificate groups. -/
theorem cm_certLift_eq {S : State Ω C} {L : SuppliedLabels S}
    {Ag Ag' : Aggregation P₀ S L.toGiantLabels} (h : Ag ∈ asRounds L) (h' : Ag' ∈ asRounds L)
    (z : Ω → C) : itCertLift Ag.fin S Ag.πd P₀.κ z = itCertLift Ag'.fin S Ag'.πd P₀.κ z := by
  rw [it_πd_eq h h']

/-- **The end of the phase meets `ItHand`.** Let `Cs`, `Ag₀` and the state data be those of
`CmHand`. If a candidate `Ag ∈ CmCands Cs Ag₀ O rec` has a run of its comparison script with
result `a`, then `cmOutV … O.tuples a` stands for the candidates of `Cs` with the comparison script
of `Ag`. -/
theorem cm_out_itHand {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {L : SuppliedLabels S}
    {Cs : Set (Aggregation P₀ S L.toGiantLabels)} {Ag₀ : Aggregation P₀ S L.toGiantLabels}
    (hAg₀ : Ag₀ ∈ Cs) (hsub : Cs ⊆ asRounds L)
    (hcl : ∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag ∈ Cs)
    {sv : Val} {ps fx fy : GPairs k L.q} (hcan : Canon e c sv S)
    (hps : PairGens e L.toGiantLabels S.G ps)
    (hfx : PairGens e L.toGiantLabels (itCertLift Ag₀.fin S Ag₀.πd P₀.κ S.x) fx)
    (hfy : PairGens e L.toGiantLabels (itCertLift Ag₀.fin S Ag₀.πd P₀.κ S.y) fy)
    {O : TestTupleOrder L.q P₀.κ} {rec : List (Set (Perm S.dom) × Option (Perm S.dom))}
    {Ag : Aggregation P₀ S L.toGiantLabels} (hAg : Ag ∈ CmCands Cs Ag₀ O rec) {a : List Bool}
    (ex : Exec P₀ Ag.compScript a) :
    ItHand e c S L {Ag' | Ag' ∈ Cs ∧ Ag'.compScript = Ag.compScript}
      (cmOutV sv k ps fx fy O.tuples a) := by
  obtain ⟨hCs, hcert, htests, -⟩ := hAg
  refine ⟨fun Ag' h => hsub h.1, Ag, ⟨hCs, rfl⟩, fun Ag' h' h1 h2 => ⟨hcl Ag' h' (h1.trans hcert),
    h2⟩, sv, ps, fx, fy, O, ?_, hcan, hps, ?_, ?_⟩
  · rw [← htests]
    exact cm_out_eq ex sv ps fx fy
  · rwa [cm_certLift_eq (hsub hCs) (hsub hAg₀)]
  · rwa [cm_certLift_eq (hsub hCs) (hsub hAg₀)]

/-- The comparison script of a candidate is the walk from its start. -/
theorem cm_compScript_eq {S : State Ω C} {L : SuppliedLabels S}
    (Ag : Aggregation P₀ S L.toGiantLabels) :
    Ag.compScript =
      (haveI := Ag.fin
       letI : Fintype S.dom := Fintype.ofFinite _
       letI : DecidableEq Ω := Classical.decEq _
       cmAt S Ag.πd (dstr S S.x) (dstr S S.y) Ag.pick (.pair [] (cmPairs Ag.tests))) :=
  haveI := Ag.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  cmAt_start _ _ _ _ _ _

/-! ### The phase from a move function -/

section Phase

variable (I : Iface) (Pg : Program) (F : Funs)

/-- **The comparison phase from a move function.** If a move function `mv` meets the condition of
`stepOKC_of_move` for a relation `Rep'` with output relation `Out`, and the initial state stands
for the comparison scripts of a set `Ds` of rounds, then the runner returns the output of a run of
the comparison script of some `Ag ∈ Ds`, with at most `f₀` calls. -/
theorem cm_phase_spec {S : State Ω C} {L : SuppliedLabels S} {d stp mv : ℕ}
    (hd : Pg.funs[d]? = some (runBody F d stp)) (hstp : Pg.funs[stp]? = some (cpLoopBody stp mv))
    {Out : List Bool → Val → Prop} {Rep' : ℕ → Val → Set (Script (List Bool)) → ℕ → Prop}
    {Bm Bw M₀ : ℕ}
    (hmv : ∀ m st Ss f, Rep' m st Ss f → FunAll Pg mv st (fun w c => c ≤ Bm ∧
      (Iface.StepPostC (measure P₀ .giant S) Out (fun st Ss f => ∃ m, Rep' m st Ss f) Ss f w ∨
        ∃ m' st' Ss', m' < m ∧ Ss' ⊆ Ss ∧ Rep' m' st' Ss' f ∧ w = .list [.nat 2, st'])))
    (hwt : ∀ m st Ss f, Rep' m st Ss f → st.wt ≤ Bw)
    (hM : ∀ m st Ss f, Rep' m st Ss f → m ≤ M₀)
    (ih : I.IHBelow Pg F (measure P₀ .giant S))
    (Ds : Set (Aggregation P₀ S L.toGiantLabels)) {st₀ : Val} {m₀ f₀ : ℕ}
    (h₀ : Rep' m₀ st₀ ((fun Ag => Ag.compScript) '' Ds) f₀) :
    FunAll Pg d st₀ (fun out cost => ∃ Ag ∈ Ds, ∃ (a : List Bool)
      (ex : Exec P₀ Ag.compScript a), Out a out ∧ ex.calls.length ≤ f₀ ∧
      (cost : ℝ) ≤ ((ex.calls.length : ℝ) + 1) *
        (runK * (((M₀ + 1) * cpLoopC Bm Bw + Bw : ℕ) + 1)) + I.execCost ex) := by
  have hs := stepOKC_of_move (M := M₀) hstp hmv hwt hM
  refine (I.run_specC Pg F hd hs ih f₀ st₀ _ ⟨m₀, h₀⟩).mono ?_
  rintro out cost ⟨s, ⟨Ag, hAg, rfl⟩, a, ex, hout, -, hlen, hc⟩
  exact ⟨Ag, hAg, a, ex, hout, hlen, by exact_mod_cast hc⟩

/-- **What the comparison program must do** at `fm`: on a hand-over state `cmSt …` of `CmHand`
(here unpacked), return `cmOutV … O.tuples a` for some order `O` and a run with result `a` of the
comparison script of a candidate of the empty record, at cost at most `X W₀` besides the calls of
the run, with output weight at most `X W₀`. -/
def CmRunOK (X : ℕ → ℕ) (fm : ℕ) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (sv' lv : Val)
    (L : SuppliedLabels S), AsCall I Pg F e c S sv' lv L →
    ∀ (Cs : Set (Aggregation P₀ S L.toGiantLabels)) (Ag₀ : Aggregation P₀ S L.toGiantLabels),
    Ag₀ ∈ Cs → Cs ⊆ asRounds L → (∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag ∈ Cs) →
    ∀ (sv : Val) (ps fx fy : GPairs k L.q) (logs : List (CmLog k L.q)),
    Canon e c sv S → PairGens e L.toGiantLabels S.G ps →
    PairGens e L.toGiantLabels (itCertLift Ag₀.fin S Ag₀.πd P₀.κ S.x) fx →
    PairGens e L.toGiantLabels (itCertLift Ag₀.fin S Ag₀.πd P₀.κ S.y) fy →
    ps.length ≤ (k + L.q) ^ 2 → fx.length ≤ (k + L.q) ^ 2 → fy.length ≤ (k + L.q) ^ 2 →
    (haveI := Ag₀.fin
     letI : Fintype S.dom := Fintype.ofFinite _
     letI : DecidableEq Ω := Classical.decEq _
     CmLogsOK e Ag₀.πd logs) →
    FunAll Pg fm (cmSt sv k L.q ps fx fy logs) (fun w cost => ∃ O : TestTupleOrder L.q P₀.κ,
      ∃ Ag ∈ CmCands Cs Ag₀ O [], ∃ (a : List Bool) (ex : Exec P₀ Ag.compScript a),
        w = cmOutV sv k ps fx fy O.tuples a ∧
        (cost : ℝ) ≤ X (I.inW .giant S) + I.execCost ex ∧ w.wt ≤ X (I.inW .giant S))

/-- **`AsCompOK` from the comparison program**: with the hand-over relations `CmHand` before the
phase and `ItHand` after it, `CmRunOK` gives `AsCompOK` (`cm_out_itHand`). -/
theorem asCompOK_of_run (H : AsHand) (X : ℕ → ℕ) (fm : ℕ)
    (hc : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) Cs st, H.comp e c S L Cs st → CmHand e c S L Cs st)
    (hi : ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)
      (L : SuppliedLabels S) Cs st, ItHand e c S L Cs st → H.items e c S L Cs st)
    (hrun : CmRunOK I Pg F X fm) : AsCompOK I Pg F H X fm := by
  intro Ω C k e c S sv' lv L hcall Cs st hst
  obtain ⟨hsub, Ag₀, hAg₀, hcl, sv, ps, fx, fy, logs, rfl, hcan, hps, hfx, hfy, hl1, hl2, hl3,
    hlogs⟩ := hc e c S L Cs st hst
  refine (hrun e c S sv' lv L hcall Cs Ag₀ hAg₀ hsub hcl sv ps fx fy logs hcan hps hfx hfy hl1 hl2
    hl3 hlogs).mono ?_
  rintro w cost ⟨O, Ag, hAg, a, ex, rfl, hcost, hw⟩
  exact ⟨Ag, hAg.1, a, ex, hi e c S L _ _ (cm_out_itHand hAg₀ hsub hcl hcan hps hfx hfy hAg ex),
    hcost, hw⟩

end Phase

end GI.Impl
