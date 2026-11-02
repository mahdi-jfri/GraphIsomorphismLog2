import Workspace.Impl.AggCertRep
import Workspace.Impl.AggItemHand

/-!
# The hand-over from the certificate phase to the comparison phase

The comparison phase (`AsCompOK`, `Workspace/Impl/AggSpecDefs.lean`) starts from the program
state that the certificate phase leaves. This file fixes that state (`cmSt`) and what it stands
for (`CmHand`). It is the field `comp` of `AsHand`.

What the comparison phase reads. The lockstep update of stage `j` of the comparison of
`(z, t)` with `(z', t')` asks `Continue` under the lift of the stage kernel
`N_j = ker(φ_T|_{A_j})` on the increment `V_j` of the endpoint procedure of `(z, T)`, `T = tset t`
(`compareCall`, `lockstepStepLift`). These stages are mathematical objects that only the window
calls of the certificate phase reveal: the comparison script asks no window call, so it cannot
compute them again. So the certificate phase must leave, for every test set `T` and both strings,
the stage of every round `j < n` (`n = |dom|`):
* the graph form of the lift of the group `A_j` (the value `ps` that the certificate program
  holds at the start of round `j`), and
* the domain positions of the increment `V_j` (the list that the increment program returns at
  the start of round `j`; empty when the increment is empty).

The comparison program computes the stage kernel and the window indicator itself (one
**PointwiseStab** call and the indicator, as the certificate phase does for its window calls), so
the certificate phase only records two values it already has at each round start.

What the comparison phase passes on to the items (`ItHand`, `AggItemHand.lean`): the state value
`sv`, the graph pairs `ps` of `G`, and the graph pairs `fx`, `fy` of the lifts of the certificate
groups. They sit in the same places as in `itSt`.

The candidate set: as in `ItHand`, a set of rounds of the labels that contains every round of the
labels with the certificate script of one of its members `Ag₀`. The comparison phase fixes the
order of the test tuples and the representatives of the comparison cosets; neither enters the
certificate script, so the round with these two fields replaced still lies in the set.

The length bounds bound the weight of the state, hence the cost of the comparison program.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPts)

/-! ### Values -/

section Values

variable {k q : ℕ}

/-- **One stage of a log**: the graph form of the lift of `A_j` and the domain positions of the
increment `V_j`. -/
abbrev CmStage (k q : ℕ) := GPairs k q × List (Fin (k + q))

/-- The value `[⟨pairs⟩, ⟨positions⟩]` of one stage. -/
def cmStgV (d : CmStage k q) : Val := .list [gpV d.1, encPts d.2]

/-- **The log of one test set**: the set, and the stages of the rounds `0, …, n - 1` of `x` and
of `y`. -/
structure CmLog (k q : ℕ) where
  T : Finset (Fin q)
  lx : List (CmStage k q)
  ly : List (CmStage k q)

/-- The value `[tsV T, ⟨stages of x⟩, ⟨stages of y⟩]` of the log of one test set. -/
noncomputable def cmLogV (l : CmLog k q) : Val :=
  .list [tsV k l.T, .list (l.lx.map cmStgV), .list (l.ly.map cmStgV)]

/-- **The program state handed to the comparison phase**:
`[sv, [k, q], ⟨ps⟩, ⟨fx⟩, ⟨fy⟩, ⟨logs⟩]`. The first five entries are those of `itSt`. -/
noncomputable def cmSt (sv : Val) (k q : ℕ) (ps fx fy : GPairs k q) (logs : List (CmLog k q)) :
    Val :=
  .list [sv, .list [.nat k, .nat q], .list (ps.map pairV), .list (fx.map pairV),
    .list (fy.map pairV), .list (logs.map cmLogV)]

end Values

/-! ### What the logs stand for -/

section Logs

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] (e : Ω ≃ Fin k) {S : State Ω C} [Fintype S.dom]
  {L : GiantLabels S} (πd : S.domGroup →* alternatingGroup (Fin L.q))

/-- **Stage `j` of the string `z` for the test set `T`**: `d.1` is a graph form of the lift of
`A_j` with at most `(k + q)²` pairs, and `d.2` lists the positions of the increment `V_j` once
each. -/
def CmStg (T : Finset (Fin L.q)) (z : Ω → C) (j : ℕ) (d : CmStage k L.q) : Prop :=
  PairGens e L (S.liftGroup (grp (cpPhi S πd T) (dstr S z) j)) d.1 ∧
    d.1.length ≤ (k + L.q) ^ 2 ∧
    ∃ incl : List S.dom, incl.Nodup ∧
      (∀ v, v ∈ incl ↔ v ∈ inc (cpPhi S πd T) (dstr S z) j) ∧ d.2 = incl.map (domPos e L.q)

/-- **The log of the string `z` for the test set `T`**: one stage for each round
`j < n = |dom|`, in order. -/
def CmStgs (T : Finset (Fin L.q)) (z : Ω → C) (l : List (CmStage k L.q)) : Prop :=
  l.length = Fintype.card S.dom ∧ ∀ j (h : j < l.length), CmStg e πd T z j l[j]

/-- **The logs of all test sets**: one log for each `κ`-subset, in the order of some
`TestSetOrder` (in practice the order `Ag₀.sets` of the certificate phase). -/
def CmLogsOK (logs : List (CmLog k L.q)) : Prop :=
  (∃ O : TestSetOrder L.q P₀.κ, logs.map CmLog.T = O.sets) ∧
    ∀ l ∈ logs, CmStgs e πd l.T S.x l.lx ∧ CmStgs e πd l.T S.y l.ly

end Logs

/-! ### The hand-over relation -/

variable {Ω C : Type} {k : ℕ}

/-- **The hand-over relation of the comparison phase**: the state `st` stands for the candidate
set `Cs`.
* `Cs` is a set of rounds of the labels, and contains every round of the labels with the
  certificate script of `Ag₀ ∈ Cs`;
* `st = cmSt sv k q ps fx fy logs` with `sv` the canonical value of `S`, `ps` graph pairs of `G`,
  `fx`, `fy` graph pairs of the lifts of `F_x`, `F_y` (as in `ItHand`), each list with at most
  `(k + q)²` pairs, and `logs` the stages of every test set and both strings (`CmLogsOK`). -/
def CmHand (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (L : SuppliedLabels S)
    (Cs : Set (Aggregation P₀ S L.toGiantLabels)) (st : Val) : Prop :=
  Cs ⊆ asRounds L ∧ ∃ Ag₀ ∈ Cs,
    (∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag ∈ Cs) ∧
    ∃ (sv : Val) (ps fx fy : GPairs k L.q) (logs : List (CmLog k L.q)),
      st = cmSt sv k L.q ps fx fy logs ∧
      Canon e c sv S ∧ PairGens e L.toGiantLabels S.G ps ∧
      PairGens e L.toGiantLabels (itCertLift Ag₀.fin S Ag₀.πd P₀.κ S.x) fx ∧
      PairGens e L.toGiantLabels (itCertLift Ag₀.fin S Ag₀.πd P₀.κ S.y) fy ∧
      ps.length ≤ (k + L.q) ^ 2 ∧ fx.length ≤ (k + L.q) ^ 2 ∧ fy.length ≤ (k + L.q) ^ 2 ∧
      (haveI := Ag₀.fin
       letI : Fintype S.dom := Fintype.ofFinite _
       letI : DecidableEq Ω := Classical.decEq _
       CmLogsOK e Ag₀.πd logs)

/-- The rounds of a candidate set agree on the certificate script of `Ag₀` exactly when they lie
in the fibre of `Ag₀`; in particular `Ag₀` with the order of the tests and the representatives of
the comparison cosets replaced is again a candidate (its certificate script is that of `Ag₀`). -/
theorem cmHand_mem {S : State Ω C} {L : SuppliedLabels S}
    {Cs : Set (Aggregation P₀ S L.toGiantLabels)} {Ag₀ : Aggregation P₀ S L.toGiantLabels}
    (hAg₀ : Ag₀ ∈ Cs) (hsub : Cs ⊆ asRounds L)
    (hcl : ∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag ∈ Cs)
    (O : TestTupleOrder L.q P₀.κ) (Pk : PickFn S.dom) :
    { Ag₀ with tests := O, pick := Pk } ∈ Cs :=
  hcl _ ⟨(hsub hAg₀).1, (hsub hAg₀).2⟩ rfl

end GI.Impl
