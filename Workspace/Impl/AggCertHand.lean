import Workspace.Impl.AggCertMvEntry
import Workspace.Impl.AggSubMath
import Workspace.Impl.AggSpecDefs
import Workspace.Impl.AggCmpHand

/-!
# The hand-over to the certificate phase

The certificate phase (`AsCertOK`, `Workspace/Impl/AggSpecDefs.lean`) starts from a program state
that the reading leaves. This file fixes what that state stands for (`CpHand`, the field `cert`
of `AsHand`), and proves the core of `AsCertOK`: the runner of the certificate phase returns a
run of the certificate script of a member of the candidate set (`cp_cert_core`).

The program fixes two choices of the round while it runs: the order of the test sets (the order
`sbOrder` of `AggSubMath.lean`, which the subset program `sb_spec` lists) and the coset
representatives (through its cache). The candidate set is the start set `asRounds L`: it
contains, with each member `Ag`, the round `cpWith Ag O R` that has the order `O` and the
representatives `R` and agrees with `Ag` otherwise (`cpWith_mem_asRounds`), and it contains every
round of the labels with a given certificate script, as the comparison phase asks (`CmHand`).

The label map `πd` of a candidate is read off the constituent of the labels, so it is the same
for all members of `asRounds L` (`cp_πd_eq`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

variable {Ω C : Type} {k : ℕ}

/-- **A round with another order of test sets and other coset representatives.** -/
def cpWith {S : State Ω C} {L : GiantLabels S} (Ag : Aggregation P₀ S L)
    (O : TestSetOrder L.q P₀.κ) (R : CosetRepFn S.dom) : Aggregation P₀ S L :=
  { Ag with sets := O, reps := R }

theorem cpWith_mem_asRounds {S : State Ω C} {L : SuppliedLabels S}
    {Ag : Aggregation P₀ S L.toGiantLabels} (h : Ag ∈ asRounds L) (O : TestSetOrder L.q P₀.κ)
    (R : CosetRepFn S.dom) : cpWith Ag O R ∈ asRounds L := h

/-- The label map of a round of the labels is the one of the labels' constituent. -/
theorem cp_πd_eq {S : State Ω C} {L : SuppliedLabels S} {Ag : Aggregation P₀ S L.toGiantLabels}
    (h : Ag ∈ asRounds L) : Ag.πd = L.toGiantLabels.domMap L.con.onDomain := by
  show L.toGiantLabels.domMap Ag.con.onDomain = _
  rw [h.2]

/-- **The certificate script of `cpWith Ag O R`** is the certificate phase with the order `O`
and the representatives `R`, for any instances. -/
theorem cpWith_certScript {S : State Ω C} {L : GiantLabels S} [DecidableEq Ω] [Fintype S.dom]
    (Ag : Aggregation P₀ S L) (O : TestSetOrder L.q P₀.κ) (R : CosetRepFn S.dom) :
    (cpWith Ag O R).certScript =
      certPhase S Ag.πd P₀.κ O R (dstr S S.x) (dstr S S.y) := by
  unfold Aggregation.certScript
  congr 1 <;> exact Subsingleton.elim _ _

/-- **The program state of the start of the certificate phase** for the context `sv`, `gp`,
`osA` (`CpCtx`) and the first test set `T` of `sbOrder` with the graph form `p0` of `P_T`. -/
noncomputable def cpInitV (sv : Val) (k q n : ℕ) (gp : GPairs k q) (osA : List (Fin (k + q)))
    (T : Finset (Fin q)) (Ts : List (Finset (Fin q))) (p0 : GPairs k q) : Val :=
  .list [(CpSt.init T Ts p0 osA).val (cpParV k q n (P₀.κ.factorial / 2) sv (gpV gp) (encPts osA))
    (.list []), .nat 0]

/-- **The hand-over relation of the certificate phase**: the state `st` stands for the
candidate set `Cs`.
* `Cs` is the nonempty set of all rounds of the labels;
* `st = cpInitV …` for a context `CpCtx` of the state (with the label map of the labels and
  `D = κ!/2`), the test sets of `sbOrder` and the graph form of `P_T` of the first one. -/
def CpHand (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (L : SuppliedLabels S)
    (Cs : Set (Aggregation P₀ S L.toGiantLabels)) (st : Val) : Prop :=
  Cs = asRounds L ∧ Cs.Nonempty ∧
    haveI : Finite Ω := Finite.of_equiv _ e.symm
    letI : Fintype S.dom := Fintype.ofFinite _
    letI : DecidableEq Ω := Classical.decEq _
    ∃ (sv : Val) (gp : GPairs k L.q) (osA : List (Fin (k + L.q))) (T : Finset (Fin L.q))
      (Ts : List (Finset (Fin L.q))) (p0 : GPairs k L.q),
      (sbOrder L.q P₀.κ).sets = T :: Ts ∧
      CpCtx e c S L.toGiantLabels (L.toGiantLabels.domMap L.con.onDomain) sv gp osA
        (P₀.κ.factorial / 2) ∧
      PairGens e L.toGiantLabels (S.liftGroup (Pgrp S.domGroup
        (L.toGiantLabels.domMap L.con.onDomain) T)) p0 ∧ p0.length ≤ (k + L.q) ^ 2 ∧
      st = cpInitV sv k L.q (Fintype.card S.dom) gp osA T Ts p0

/-- Moving a run along an equation of scripts keeps its calls. -/
theorem cp_exec_cast {α : Type} {s s' : Script α} (h : s = s') {a : α} (ex : Exec P₀ s a) :
    ∃ ex' : Exec P₀ s' a, ex'.calls = ex.calls := by
  subst h; exact ⟨ex, rfl⟩

/-- **The bound on one round of the loop of moves** (`cert_phase_spec`) for the parent data of
weight `P`, `NT` test sets, `n` domain points and `D` representatives per round: `f₀` bounds the
calls, `Bw` the weights of the program states, `W` the weights inside one move. -/
noncomputable def cpPhaseB (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)
    (k q P NT n D : ℕ) : ℕ :=
  let f₀ := (2 * (NT - 1) + 2) * (n + 1) * (D + 2)
  let Bw := cpBw k q P NT f₀ D
  (f₀ + 1) * cpLoopC (cpBm hst hpre hm (10 ^ 4 * (Bw + 2) ^ 2)) Bw + Bw

section Core

variable (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

/-- **The core of `AsCertOK`.** From a program state for the candidates `Cs` (`CpHand`), the
runner of the certificate phase returns the graph forms of the final stages (`CpOut`) of a run of
the certificate script of a member `Ag` of `Cs`. The cost is at most
`(calls + 1) runK (cpPhaseB … + 1)` plus the cost of the calls, for the weight `P` of the parent
data, `NT = binom(q, κ)` test sets and `D = κ!/2`. -/
theorem cp_cert_core (I : Iface) (Pg : Program) (F : Funs) {d stp b jp jpre jm : ℕ}
    (hd : Pg.funs[d]? = some (runBody F d stp)) (hstp : Pg.funs[stp]? = some (cpLoopBody stp b))
    (hat : CpMvAt Pg b jp jpre jm)
    (hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C} {L : SuppliedLabels S}
    {Cs : Set (Aggregation P₀ S L.toGiantLabels)} {st : Val} (h : CpHand e c S L Cs st)
    (ih : I.IHBelow Pg F (measure P₀ .giant S)) :
    FunAll Pg d st (fun out cost => ∃ Ag ∈ Cs, ∃ (a : List (StagePair S))
      (ex : Exec P₀ Ag.certScript a),
      (haveI : Finite Ω := Finite.of_equiv _ e.symm
       letI : Fintype S.dom := Fintype.ofFinite _
       letI : DecidableEq Ω := Classical.decEq _
       CpOut e S L.toGiantLabels (L.toGiantLabels.domMap L.con.onDomain) a out) ∧
      ∃ P n : ℕ, P < st.wt ∧ n ≤ k ∧
      ex.calls.length ≤ (2 * (L.q.choose P₀.κ - 1) + 2) * (n + 1) * (P₀.κ.factorial / 2 + 2) ∧
      (cost : ℝ) ≤ ((ex.calls.length : ℝ) + 1) * (runK *
        (cpPhaseB hst hpre hm k L.q P (L.q.choose P₀.κ) n (P₀.κ.factorial / 2) + 1)) +
          I.execCost ex) := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  obtain ⟨rfl, ⟨Ag₀, hAg₀⟩, sv, gp, osA, T, Ts, p0, hO, ctx, hp0, hp0l, rfl⟩ := h
  have hNT : Ts.length + 1 = L.q.choose P₀.κ := by
    rw [← (sbOrder L.q P₀.κ).length_eq, hO, List.length_cons]
  refine (cp_phase_spec hst hpre hm I Pg F hd hstp hat hjp hjpre hjm ctx ih
    (sbOrder L.q P₀.κ) hO hp0 hp0l le_rfl le_rfl).mono ?_
  rintro out cost ⟨R, a, ex, hout, hcl, hc⟩
  have hmem := cpWith_mem_asRounds hAg₀ (sbOrder L.q P₀.κ) R
  have hs : (cpWith Ag₀ (sbOrder L.q P₀.κ) R).certScript =
      certPhase S (L.toGiantLabels.domMap L.con.onDomain) P₀.κ (sbOrder L.q P₀.κ) R
        (dstr S S.x) (dstr S S.y) := by
    rw [cpWith_certScript]; show certPhase S Ag₀.πd _ _ _ _ _ = _; rw [cp_πd_eq hAg₀]
  obtain ⟨ex', hex'⟩ := cp_exec_cast hs.symm ex
  have hcost : I.execCost ex' = I.execCost ex := by unfold Iface.execCost; rw [hex']
  refine ⟨_, hmem, a, ex', hout, (cpParV k L.q (Fintype.card S.dom) (P₀.κ.factorial / 2) sv
    (gpV gp) (encPts osA)).wt, Fintype.card S.dom, ?_, cp_card_dom_le e, ?_, ?_⟩
  · exact (cp_wt_get (vs := (CpSt.init T Ts p0 osA).vals _ (.list [])) (j := 0) rfl).trans
      (cp_wt_get (vs := [(CpSt.init T Ts p0 osA).val _ (.list []), .nat 0]) (j := 0) rfl)
  · rw [hex', ← hNT, Nat.add_sub_cancel]; exact hcl
  · rw [hcost, hex', ← hNT]
    simp only [cpPhaseB, Nat.add_sub_cancel]
    exact hc

end Core

/-! ### The logs as the comparison phase reads them -/

section Logs

/-- A log of the certificate phase as a log of `CmHand`. -/
def cpCmLog {q : ℕ} (l : Finset (Fin q) × List (CpStgD k q) × List (CpStgD k q)) : CmLog k q :=
  ⟨l.1, l.2.1, l.2.2⟩

theorem cp_cmLogV {q : ℕ} (logs : List (Finset (Fin q) × List (CpStgD k q) × List (CpStgD k q))) :
    (logs.map cpCmLog).map cmLogV = logs.map cpLogV := by
  simp only [List.map_map]
  congr 1

/-- **The logs of the output are the logs `CmHand` asks for**: the stages of the certificate
phase (`CpStgs`) are the stages of the comparison phase (`CmStgs`), word for word. -/
theorem cp_cmLogsOK [DecidableEq Ω] (e : Ω ≃ Fin k) {S : State Ω C} [Fintype S.dom]
    {L : GiantLabels S} (πd : S.domGroup →* alternatingGroup (Fin L.q))
    {logs : List (Finset (Fin L.q) × List (CpStgD k L.q) × List (CpStgD k L.q))}
    (hO : ∃ O : TestSetOrder L.q P₀.κ, logs.map Prod.fst = O.sets)
    (h : ∀ l ∈ logs, CpStgs e πd l.1 S.x l.2.1 ∧ CpStgs e πd l.1 S.y l.2.2) :
    CmLogsOK e πd (logs.map cpCmLog) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨O, hO⟩ := hO
    exact ⟨O, by rw [← hO, List.map_map]; rfl⟩
  · intro l hl
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    exact h l' hl'

end Logs

end GI.Impl
