module

public import Workspace.Impl.AggSpecDefs
public import Workspace.Impl.AggStructRel

@[expose] public section

/-!
# The hand-over from the comparison phase to the items

The items of a round (`AsItemsOK`, `Workspace/Impl/AggSpecDefs.lean`) start from the program
state that the comparison phase leaves. This file fixes that state (`itSt`) and what it stands
for (`ItHand`). It is the field `items` of `AsHand`.

What the items read:
* the state value `sv` of the input (the positions, the two strings, the bookkeeping): the
  halving item asks `Continue` calls on children of the state;
* the graph pairs `ps` of `G` (`[g, π g]`, as in `lcCtx`): lifts of label permutations;
* for each string `z ∈ {x, y}`, graph pairs `fz` of the lift of the certificate group `F_z`
  (the elements of `G` whose restriction to the domain lies in `F_z`). Their second parts generate
  the ideal certificate group `π(F_z)`, from which the case and the items of Case 1 and 2a are
  read; their first parts give the group `A` of the halving item;
* the comparison context `stCv tt cr` of `AggStructRel.lean`: the ordered test tuples in some
  order `tt` and the table `cr` of `CompareRel`, from which the tuple colors are computed
  (`stRel_spec_round`, `stCols_spec`).

What the candidate set must be: it is a set of rounds of the labels (`asRounds L`), and it
contains every round of the labels with the certificate and comparison scripts of one of its
members `Ag₀`. The fields that the items choose (`num`, `hK`, `src`, `rep`, `tups`, `halv`, `soj`)
enter neither script (`stRound_certScript`, `stRound_compScript`), so the items may fix them
freely and still return a member of the set.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type} {k : ℕ}

/-- **The program state handed to the items**:
`[sv, [k, q], ⟨ps⟩, ⟨fx⟩, ⟨fy⟩, stCv tt cr]`. -/
noncomputable def itSt (sv : Val) (k q : ℕ) (ps fx fy : List (Perm (Fin k) × Perm (Fin q)))
    (tt : List (TestTuple q P₀.κ)) (cr : TestTuple q P₀.κ → TestTuple q P₀.κ → Bool) : Val :=
  .list [sv, .list [.nat k, .nat q], .list (ps.map pairV), .list (fx.map pairV),
    .list (fy.map pairV), stCv tt cr]

/-- **The lift of the certificate group** of the string `z`: the elements of `G` whose
restriction to the domain lies in `F_z` (`certLift` for `z = x`). -/
noncomputable def itCertLift (fin : Finite Ω) (S : State Ω C) {q : ℕ}
    (πd : S.domGroup →* alternatingGroup (Fin q)) (κ : ℕ) (z : Ω → C) : Subgroup (Perm Ω) :=
  haveI := fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  S.liftGroup (certGroup S πd κ (dstr S z))

/-- **The table of the comparison relation** of the round's strings. -/
noncomputable def itCr (fin : Finite Ω) (S : State Ω C) {q : ℕ}
    (πd : S.domGroup →* alternatingGroup (Fin q)) (κ : ℕ) :
    TestTuple q κ → TestTuple q κ → Bool :=
  haveI := fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  stCr S πd κ (dstr S S.x) (dstr S S.y)

/-- **The hand-over relation of the items**: the state `st` stands for the candidate set `Cs`.
* `Cs` is a set of rounds of the labels, and contains every round of the labels with the
  certificate and comparison scripts of `Ag₀ ∈ Cs`;
* `st = itSt sv k q ps fx fy tt cr` with `sv` the canonical value of `S`, `ps` graph pairs of
  `G`, `fx`, `fy` graph pairs of the lifts of `F_x`, `F_y`, `tt` the test tuples in the order of
  some `TestTupleOrder`, and `cr` the table of `CompareRel`. -/
def ItHand (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (L : SuppliedLabels S)
    (Cs : Set (Aggregation P₀ S L.toGiantLabels)) (st : Val) : Prop :=
  Cs ⊆ asRounds L ∧ ∃ Ag₀ ∈ Cs,
    (∀ Ag ∈ asRounds L, Ag.certScript = Ag₀.certScript → Ag.compScript = Ag₀.compScript →
      Ag ∈ Cs) ∧
    ∃ (sv : Val) (ps fx fy : List (Perm (Fin k) × Perm (Fin L.q))) (O : TestTupleOrder L.q P₀.κ),
      st = itSt sv k L.q ps fx fy O.tuples (itCr Ag₀.fin S Ag₀.πd P₀.κ) ∧
      Canon e c sv S ∧ PairGens e L.toGiantLabels S.G ps ∧
      PairGens e L.toGiantLabels (itCertLift Ag₀.fin S Ag₀.πd P₀.κ S.x) fx ∧
      PairGens e L.toGiantLabels (itCertLift Ag₀.fin S Ag₀.πd P₀.κ S.y) fy

/-- The candidates agree on the label map `πd` (it is read off the constituent of the labels). -/
theorem it_πd_eq {S : State Ω C} {L : SuppliedLabels S} {Ag Ag' : Aggregation P₀ S L.toGiantLabels}
    (h : Ag ∈ asRounds L) (h' : Ag' ∈ asRounds L) : Ag.πd = Ag'.πd := by
  show L.toGiantLabels.domMap Ag.con.onDomain = L.toGiantLabels.domMap Ag'.con.onDomain
  rw [h.2, h'.2]

end GI.Impl
