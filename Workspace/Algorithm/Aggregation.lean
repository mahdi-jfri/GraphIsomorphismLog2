module

public import Workspace.Algorithm.AggregationPlan
public import Workspace.Algorithm.AuxCases
public import Workspace.Algorithm.AuxCarrierRect
public import Workspace.Algorithm.CarrierOfState
public import Workspace.Algorithm.AggregationParams
public import Workspace.Algorithm.AuxOut
public import Workspace.Algorithm.LabelData
public import Workspace.Algorithm.CfgThreshold

@[expose] public section

/-!
# The interface of an aggregation round

The items of a round (`AuxItem`, `Workspace/Algorithm/AuxItems.lean`) are computed by the
paper's case analysis (`Workspace/Algorithm/AggregationPlan.lean`). This file holds the
interface `Aggregation` of the round, its script (the certificate phase, the ordered
comparisons, then the items), and the facts the recursion needs.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Rectangle
open scoped Pointwise

variable {Ω C : Type}

/-! ### The interface -/

/-- **Interface for an aggregation round** (Algorithm 5, `GiantStep` after "Freeze
`S_0 ← S`"; Section 4.1; Algorithm `alg:auxiliary`). The structural data of the paper's
aggregation step:
* the selected interval;
* the data of the selected Cameron constituent that the supplied labels carry (`con`,
  `GiantLabels.Constituent`, `Workspace/Algorithm/LabelData.lean`): the labels are read on the
  domain, so that `π` factors through the faithful image `G|_dom` (`πd`, on which the local
  certificates are computed), and the Johnson block map of the constituent (Lemma A.11, `blocks`);
* the cited inputs: the coherent refinement (`hK`) and the Design Lemma (`hD`);
* the parameter conditions `Params.Aggregates P` (Section 7.5, including `q₀ ≥ 2064`, the explicit
  label threshold of Lemma A.12) and the phase facts `q > q₀` and `N > N₀`;
* the state is not in the row case (`hnot`; Algorithm 5: `GiantStep` aggregates only when the
  labels are not natural or retained rows have degree at least `q`).

The data of Lemma A.30 for natural labels (`carrierData`: the carrier quotient, the column giant
and the chosen rows) are built from the carrier invariant of the state (`CarrierOK`) and the
labels above the retained columns (`Constituent.kills`), by `CarrierData.ofState`
(`Workspace/Algorithm/CarrierOfState.lean`). The rectangle oracle (`rect`) is built from them
(`RectRep.ofCarrier`, `Workspace/Algorithm/AuxCarrierRect.lean`) and from the cross-pair orbit of
Lemma A.27 (`rectRepOf`, `Workspace/Algorithm/AuxPairRect.lean`).

The bounded source tuple `src` of `ℓ = κ + 1` labels is defined: it is a tuple that makes the
object of the source string good in Cases 2b and 3 (`exists_src_good`). The object that ends
Cases 2b and 3 (`out`: a colored partition, or a coherent configuration with its source vertex)
is computed from the canonical structures of the two strings (`outPair`,
`Workspace/Algorithm/AuxOut.lean`; in Case 2b the binary colorings of the two strings are refined
jointly). It commutes with relabeling (`out_equivariant`) and is good for the source tuple
(`out_good`).

The item of the configuration branch (`cfg`) is built from the objects of the two strings by
Algorithm `alg:auxiliary` (`cfgOutItem`), and it is valid (`cfg_valid`, from
`cfgOutItem_valid_explicit`).

The item of a branch is computed by the paper's case analysis `plan`
(`Workspace/Algorithm/AggregationPlan.lean`) from the two canonical structures of the branch
(`structX`, `structY`: certificate group, refined comparison colors, individualized tuple), and
its facts
are proved in Cases 1 and 2a (`plan_valid`).

The script (`Aggregation.script`: the certificate phase, then the items), its covering, its
calls and counts, and the cap update are computed or proved from these data (`covers`,
`calls`, `calls_count`, `overs_count`, `capUpdate`). In particular the covering of the parent
answer by the branches is a theorem (`cover`), from the equivariance of the canonical
structures. -/
structure AggregationData (P : Params) {Ω C : Type} (S : State Ω C) (L : GiantLabels S) :
    Type 1 where
  /-- The interval of the selected Cameron constituent. -/
  sel : Fin S.hier.length
  /-- Section 7.2: "The old cap is at least `q` because the selected alternating section
  belongs to that whole constituent." -/
  sel_cap : L.q ≤ S.hier[sel].cap
  /-- Section 3.3: "every stored bound is at most its current interval ratio". -/
  sel_clamped : S.hier[sel].cap ≤ S.hier[sel].ratio
  /-- The labels index kernel orbits (Corollary A.25), so `q ≤ s ≤ N`. -/
  q_le : L.q ≤ S.N
  q_two : 2 ≤ L.q
  /-- The positions are finite. -/
  fin : Finite Ω
  /-- The current action is transitive on its domain (Lemma 4.1: "Suppose the physical parent
  action `G ≤ Sym(Ω)` is transitive"). -/
  htr : S.Transitive
  /-- The domain has at most `N` positions (Section 6: the phase size). -/
  size_le : S.size ≤ S.N
  /-- The parameter conditions (Section 7.5, items (i) and (iii), and the base size). -/
  params : P.Aggregates
  /-- `GiantStep` is asked with labels on `q > q₀` points (Section A.3: "When `m ≤ q₀`,
  enumerate the alternating quotient"). -/
  q_large : P.q₀ < L.q
  /-- The state lies inside a phase: `N > N₀` (Algorithm 5: "if `|Ω| ≤ N₀` then return the
  answer by direct enumeration"). -/
  N_large : P.N₀ < S.N
  /-- The data of the selected Cameron constituent, carried by the supplied labels
  (`SuppliedLabels.con`): the labels are read on the domain, so `π` factors through `G|_dom`
  (Section 3: "Every fresh call uses the faithful permutation image on its own active domain"),
  and the Johnson block map of Lemma A.11 ("the supplied map of a selected Cameron
  constituent"). -/
  con : L.Constituent
  /-- The joint coherent refinement of two colorings (cited, [H, Sections 2.3–2.5]), taken as
  data (`JointFn`). The round refines the colorings of the two strings together, with one
  palette (Section A.3: "Use the same palette for both inputs"). -/
  hK : JointFn
  /-- The Design Lemma behind Case 3 (cited, [H, Proposition 5.1]). -/
  hD : GI.Cited.DesignLemma
  /-- The state is not in the row case (Algorithm 5: "if this map is natural and (no rows are
  retained, or `q` exceeds their degree) then return `RowStep`"). -/
  hnot : ¬ RowCase P.α S L

namespace AggregationData

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : AggregationData P S L)

/-- The label map on the faithful image of the domain action. -/
noncomputable def πd : S.domGroup →* alternatingGroup (Fin L.q) := L.domMap I.con.onDomain

theorem πd_spec (g : S.G) : I.πd ⟨S.domHom g, g, rfl⟩ = L.π g := L.domMap_spec I.con.onDomain g

/-! #### The source tuple and the object that ends Cases 2b and 3 -/

/-- The length of the bounded source tuple (anchors, orbital endpoints, individualized points,
the source vertex of the first rectangle): `ℓ = κ + 1`. It is at least `6` and more than `κ`, as
`exists_src_good` needs. -/
def ℓ (_I : AggregationData P S L) : ℕ := P.κ + 1

include I in
/-- Section 7.2: "Fix an absolute exponent `a ≥ 1` bounding the polynomial numbers of local and
auxiliary calls"; here `a ≥ 2κ + ℓ + 4` for all the calls of the round, with the local
certificates and the ordered comparisons (`Params.Aggregates.a_cert`). -/
theorem a_cert : 2 * (P.κ : ℝ) + I.ℓ + 4 ≤ P.a := by
  have := I.params.a_cert
  simp only [AggregationData.ℓ]; push_cast; linarith

include I in
/-- `a ≥ ℓ + 2` for the auxiliary calls (from `a_cert`). -/
theorem ℓ_le : (I.ℓ : ℝ) + 2 ≤ P.a := by
  have := I.a_cert; have : (0 : ℝ) ≤ P.κ := Nat.cast_nonneg _; linarith

/-- **A good source tuple exists** (`exists_src_good`): some tuple makes the object of the source
string good in Cases 2b and 3. Such a tuple holds the anchors and the orbital pair of Case 2b ("Fix an ordered source
tuple of `d - 1` distinct points … Choose one proper non-diagonal source orbital"), and the
Design Lemma's tuple and the source vertex of the first rectangle in Case 3. The hypotheses
`q ≥ 24` and `2κ ≤ q` follow from `q > q₀ ≥ 4κ + 2` and `κ ≥ 7`, and `β ≥ 3/4` from
`β ≥ 13/16`. -/
theorem src_exists
    (nm : ClassNum S P.κ L.q) (hnm : ClassNum.OK I.fin S L I.πd P.κ nm) :
    ∃ src : Fin I.ℓ → Fin L.q,
    (aggCase (structX I.fin S L I.πd I.hK P.κ nm src).grp = .twoB ∨
      aggCase (structX I.fin S L I.πd I.hK P.κ nm src).grp = .three) →
    ∀ Y, (outPair I.hK (structX I.fin S L I.πd I.hK P.κ nm src) Y).1.Good P.β :=
  exists_src_good I.hK I.hD I.fin S L I.πd nm hnm I.params.κ_five
    (by have := I.params.q₀_cert; have := I.params.κ_seven; have := I.q_large; omega)
    (by have := I.params.q₀_cert; have := I.q_large; omega)
    (le_trans (by norm_num) I.params.β_cfg) (Nat.lt_succ_self P.κ)
    (by have := I.params.κ_seven; simp only [AggregationData.ℓ]; omega)

/-- **The objects that end Cases 2b and 3**, read off the canonical structures `X`, `Y` of the
two strings with their individualized tuples (`outPair`). Case 2b: "the canonical coherent
refinement … on `C = Φ \ A`"; Case 3: "Apply the Design Lemma"; outcome (a) gives a colored
partition, outcome (b) "the vertex class `C` … as a nontrivial coherent configuration". -/
noncomputable def out (X Y : Canon L.q P.κ I.ℓ) : CfgOut L.q × CfgOut L.q := outPair I.hK X Y

/-- **The objects are canonical** ("Every choice above is canonical, so these items commute
with relabeling", Section A.3, "Aggregation and orbital colors"): if `σ X = Y`, the object of
`Y` is `σ` applied to the object of `X` (`outPair_smul`). -/
theorem out_equivariant (σ : Perm (Fin L.q)) {X Y : Canon L.q P.κ I.ℓ} (h : σ • X = Y) :
    (I.out X Y).2 = σ • (I.out X Y).1 := by
  subst h
  exact outPair_smul I.hK σ X

/-! #### The parameter facts, from `Params.Aggregates` -/

include I in
theorem κ_five : 5 ≤ P.κ := I.params.κ_five

include I in
theorem θκ : 1 ≤ P.θ * P.κ := I.params.θκ

include I in
theorem θ_half : 1 / 2 ≤ P.θ := I.params.θ_half

include I in
theorem β_cfg : 13 / 16 ≤ P.β := I.params.β_cfg

include I in
/-- Section 7.5 (iii): "`max{1/2, 1-δ, 1-ηδ, η} < β`". -/
theorem β_half : 1 / 2 ≤ P.β := le_trans (by norm_num) I.β_cfg

include I in
/-- `q > q₀ ≥ 4κ + 2 ≥ 22`. -/
theorem q_ten : 10 ≤ L.q := by
  have := I.params.q₀_cert; have := I.params.κ_five; have := I.q_large; omega

include I in
/-- **Lemma A.12 applies to the labels**: `q > q₀ ≥ 2064` (Section 7.5 (i): "Enlarge it as needed
for the coherent-configuration cap bounds"). -/
theorem q_cfg : GI.Paper.a12Threshold ≤ L.q := I.params.q₀_cfg.trans I.q_large.le

include I in
/-- `κ < q`: `q > q₀ ≥ 4κ + 2`. -/
theorem κ_lt_q : P.κ < L.q := by
  have := I.params.q₀_cert; have := I.q_large; omega

include I in
/-- The support classification at the phase size (Corollary A.25 above the base size). -/
theorem cases : SupportCases P.α S.N := I.params.cases S.N I.N_large

/-- The kernel-orbit quotient of the domain action when `q > λ` (Corollary A.25). -/
theorem kq_cases (hlam : (S.N : ℝ) ^ P.α < L.q) :
    Nonempty (GI.StabilizerQuotient.KernelQuotient I.πd S.dom (Fin L.q)) ∨
    Nonempty (GI.StabilizerQuotient.KernelQuotient I.πd S.dom (GI.Pairs.OrderedPair (Fin L.q))) ∨
    Nonempty (GI.StabilizerQuotient.KernelQuotient I.πd S.dom
      (GI.Johnson.SubsetVertex (Fin L.q) 2)) := by
  classical
  haveI := I.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  haveI := domGroup_pretransitive I.htr
  have hcard : Fintype.card S.dom ≤ S.N := by
    rw [← Nat.card_eq_fintype_card]; exact I.size_le
  have hlam' : (S.N : ℝ) ^ P.α < Fintype.card (Fin L.q) := by rw [Fintype.card_fin]; exact hlam
  exact I.cases S.domGroup I.πd (πd_surjective I.πd_spec) hcard hlam'

include I in
/-- With natural labels on `q > λ` points, the state retains rows of degree at least `q`: it is
not in the row case. -/
theorem rows_fit (hlam : (S.N : ℝ) ^ P.α < L.q) (hnat : ∃ label, NaturalRows S L label) :
    ∃ R, S.rows = some R ∧ L.q ≤ R.m := by
  by_contra h
  push Not at h
  exact I.hnot ⟨hlam, hnat, h⟩

/-- **The data of Lemma A.30 for natural labels** when `q > λ` (Section 5.3: "Suppose a later
column action has `q` natural blocks and `q ≤ m`. Couple its even permutations diagonally to the
same permutations of `q` selected rows"): built from the carrier invariant of the state and the
labels above the retained columns (`CarrierData.ofState`). -/
noncomputable def carrierData (hlam : (S.N : ℝ) ^ P.α < L.q)
    (hnat : ∃ label, NaturalRows S L label) : CarrierData S L :=
  haveI := I.fin
  CarrierData.ofState I.htr I.con.kills hnat (I.rows_fit hlam hnat).choose_spec.1
    (I.rows_fit hlam hnat).choose_spec.2

end AggregationData

/-- **An aggregation round with its choices.** Besides the data of `AggregationData`, a round
fixes the things that the paper leaves to the algorithm.

* The numbers of the comparison classes `num` (Section A.3: "Its classes provide the tuple
  colors needed for the Design Lemma … Use the same palette for both inputs"). The paper names
  the colors by the classes; any numbering that gives different classes of the common palette
  different numbers works (`num_ok`). The refined colors, hence the canonical structures and
  the items, depend on it, so a program meets the model with its own numbering.
* The bounded source tuple `src` (Section 4.1: "We fix a bounded source tuple, branch over its
  target images"). Any tuple works if it makes the object of the source string good in Cases 2b
  and 3 (`src_good`): Case 2b: "`C` is a nontrivial homogeneous coherent configuration with
  `|C| ≥ δq`"; Case 3: the classes of outcome (a) have fewer than `3q/4` points, and the vertex
  class of outcome (b) has at least `3q/4` points. Such a tuple exists (`src_exists`).
* The rectangle representations `rep` (Algorithm `alg:auxiliary`, Lemmas A.27 and A.30): for
  every rectangle that the auxiliary items ask about, a subgroup of the parent action with an
  equivariant matrix above the rectangle. Any such representation works; the ones of the
  support classification exist (`defaultRep`).
* The order of the calls and the representatives of the certificate and comparison phases: the
  order of the test sets (`sets`), of the ordered test tuples (`tests`) and of the branch tuples
  (`tups`), each an enumeration without repeats; the coset representatives of `CheckNewWindow`
  (`reps`, one per coset); and the representative kept of each lockstep comparison coset
  (`pick`); the alignment and the parity twist of the halving items (`halv`); the rectangle
  certificate, the even alignment and the imprimitive pair of the first-rectangle items
  (`soj`). The paper fixes none of them.

`AggregationData.toAgg` makes a round from the default choices. -/
structure Aggregation (P : Params) {Ω C : Type} (S : State Ω C) (L : GiantLabels S) : Type 1
    extends AggregationData P S L where
  /-- The numbers of the comparison classes (the tuple colors before refinement). -/
  num : ClassNum S P.κ L.q
  /-- Different classes of the source string get different numbers. -/
  num_ok : ClassNum.OK fin S L (L.domMap con.onDomain) P.κ num
  /-- The bounded source tuple of `ℓ = κ + 1` labels. -/
  src : Fin (P.κ + 1) → Fin L.q
  /-- In Cases 2b and 3 the object of the source string is good. -/
  src_good : (aggCase (structX fin S L (L.domMap con.onDomain) hK P.κ num src).grp = .twoB ∨
      aggCase (structX fin S L (L.domMap con.onDomain) hK P.κ num src).grp = .three) →
    ∀ Y, (outPair hK (structX fin S L (L.domMap con.onDomain) hK P.κ num src) Y).1.Good P.β
  /-- The rectangle representations. -/
  rep : ∀ W R : Finset (Fin L.q), RectConds P S L W R → RectRep P S L W R
  /-- The order of the test sets in the certificate phase. -/
  sets : TestSetOrder L.q P.κ
  /-- The coset representatives of `CheckNewWindow`. -/
  reps : CosetRepFn S.dom
  /-- The order of the ordered test tuples in the comparison phase. -/
  tests : TestTupleOrder L.q P.κ
  /-- The representatives of the comparison cosets. -/
  pick : PickFn S.dom
  /-- The branch tuples, in the order of the items: every tuple exactly once. -/
  tups : List (Fin (P.κ + 1) → Fin L.q)
  tups_nodup : tups.Nodup
  mem_tups : ∀ b, b ∈ tups
  /-- The alignment and the parity twist of the halving items (Lemma A.11). -/
  halv : HalvingChoice S L
  /-- The certificate, the alignment and the imprimitive pair of the first-rectangle items
  (Lemma 5.1). -/
  soj : SojChoice

namespace AggregationData

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : AggregationData P S L)

/-- **The default rectangle representations** (Lemmas A.27 and A.30): the representation
chosen by the support classification (`rectRepOf`), with the carrier data of the state for
natural labels. -/
noncomputable def defaultRep (W R : Finset (Fin L.q)) (h : RectConds P S L W R) :
    RectRep P S L W R :=
  haveI := I.fin
  rectRepOf I.πd_spec I.θ_half
    (fun hlam hnat _ _ hc => RectRep.ofCarrier (I.carrierData hlam hnat)
      (le_trans (by norm_num) I.θ_half) hc.2.2.2.2) I.kq_cases W R h

/-- **The default round**: a source tuple given by `src_exists` and the default rectangle
representations. Any other good source tuple and any other rectangle representations give a
round as well. -/
noncomputable def toAgg : Aggregation P S L where
  toAggregationData := I
  num := ClassNum.default I.fin S L I.πd P.κ
  num_ok := ClassNum.default_ok I.fin S L I.πd P.κ
  src := (I.src_exists _ (ClassNum.default_ok I.fin S L I.πd P.κ)).choose
  src_good := (I.src_exists _ (ClassNum.default_ok I.fin S L I.πd P.κ)).choose_spec
  rep := I.defaultRep
  sets := TestSetOrder.default L.q P.κ
  reps := haveI := I.fin; letI : Fintype S.dom := Fintype.ofFinite _; CosetRepFn.default S.dom
  tests := TestTupleOrder.default L.q P.κ
  pick := PickFn.default S.dom
  tups := Finset.univ.toList
  tups_nodup := Finset.nodup_toList _
  mem_tups _ := Finset.mem_toList.2 (Finset.mem_univ _)
  halv := HalvingChoice.default S L
  soj := SojChoice.default

end AggregationData

namespace Aggregation

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (I : Aggregation P S L)

/-- **In Cases 2b and 3 the source object is good** (the choice of `src`): Case 2b: "`C` is a
nontrivial homogeneous coherent configuration with `|C| ≥ δq`"; Case 3: the classes of outcome
(a) have fewer than `3q/4` points, and the vertex class of outcome (b) has at least
`3q/4 ≥ δq` points. -/
theorem out_good (hc : aggCase (structX I.fin S L I.πd I.hK P.κ I.num I.src).grp = .twoB ∨
    aggCase (structX I.fin S L I.πd I.hK P.κ I.num I.src).grp = .three) :
    ∀ Y, (I.out (structX I.fin S L I.πd I.hK P.κ I.num I.src) Y).1.Good P.β :=
  I.src_good hc

/-- **The rectangle oracle** (Algorithm `alg:auxiliary`, Lemmas A.27 and A.30): the queries of the
rectangle representations of the round. -/
noncomputable def rect : RectOracle P S L :=
  haveI := I.fin
  RectOracle.ofReps I.rep

/-- The canonical structure of the source string with an individualized tuple. -/
noncomputable def strX (t : Fin I.ℓ → Fin L.q) : Canon L.q P.κ I.ℓ :=
  structX I.fin S L I.πd I.hK P.κ I.num t

/-- The canonical structure of the target string with an individualized tuple. -/
noncomputable def strY (t : Fin I.ℓ → Fin L.q) : Canon L.q P.κ I.ℓ :=
  structY I.fin S L I.πd I.hK P.κ I.num t

/-- The parent isomorphisms of the branch of the target tuple `b`. -/
def isoSet (b : Fin I.ℓ → Fin L.q) : Set (Perm Ω) := isoSetOf I.fin S L I.πd I.hK P.κ I.num I.src b

/-- **The Johnson block map of the selected constituent** (Lemma A.11: "the supplied map of a
selected Cameron constituent"), carried by the labels. -/
def blocks : JohnsonBlocks S L := I.con.blocks

/-- **The item of the configuration branch** (Algorithm `alg:auxiliary`) from the objects of
the two strings. -/
noncomputable def cfg (X Y : Canon L.q P.κ I.ℓ) : AuxItem P S L :=
  cfgOutItem I.rect I.soj (I.out X Y).1 (I.out X Y).2

/-- **The item of the configuration branch is valid** in Cases 2b and 3: the source object is
good (`out_good`), every parent isomorphism of the branch maps the source structure to the target
structure and hence the source object to the target object (`out_equivariant`), and the labels
are many (`q > q₀ ≥ 2064`, the explicit threshold of Lemma A.12, `q_cfg`). -/
theorem cfg_valid (b : Fin I.ℓ → Fin L.q)
    (hc : aggCase (I.strX I.src).grp = .twoB ∨ aggCase (I.strX I.src).grp = .three) :
    (I.cfg (I.strX I.src) (I.strY b)).Valid (I.isoSet b) :=
  cfgOutItem_valid_explicit I.β_cfg L I.rect I.soj _ _ (I.out_good hc _) I.q_cfg fun g hg =>
    ⟨hg.2.1, (I.out_equivariant _ hg.2.2).symm⟩

/-- The item of the branch of the target tuple `b`: the paper's case analysis `plan`. -/
noncomputable def items (b : Fin I.ℓ → Fin L.q) : AuxItem P S L :=
  plan I.fin I.πd I.halv I.cfg (I.strX I.src) (I.strY b)

/-- **The item of every branch is valid** (`plan_valid`). -/
theorem items_valid (b : Fin I.ℓ → Fin L.q) : (I.items b).Valid (I.isoSet b) :=
  plan_valid I.fin I.πd I.πd_spec I.hK I.num I.β_half I.θ_half I.q_ten I.blocks I.halv I.cfg I.src b
    (I.cfg_valid b)

/-- **The branches cover every parent isomorphism** (Section A.3: "Consequently the branches
cover every parent isomorphism"): a parent isomorphism `g` lies in the branch of the target
tuple `π(g) ∘ src`. This was an assumption of the interface; it is now a theorem, from the
equivariance of the certificates, of the comparison classes and of the coherent refinement
(`mem_isoSetOf`). -/
theorem cover : S.answer ⊆ ⋃ b, S.answer ∩ I.isoSet b := fun _ hg =>
  Set.mem_iUnion.2 ⟨_, hg, mem_isoSetOf I.fin S L I.πd I.hK P.κ I.num I.πd_spec I.src hg⟩

/-- The branch tuples, in the order of the round. -/
def tuples : List (Fin I.ℓ → Fin L.q) := I.tups

theorem mem_tuples (b : Fin I.ℓ → Fin L.q) : b ∈ I.tuples := I.mem_tups b

theorem length_tuples : I.tuples.length = L.q ^ I.ℓ := by
  have h : I.tuples.toFinset = Finset.univ :=
    Finset.eq_univ_iff_forall.2 fun b => List.mem_toFinset.2 (I.mem_tuples b)
  have := List.toFinset_card_of_nodup (show I.tuples.Nodup from I.tups_nodup)
  rw [h, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at this
  exact this.symm

/-- **The certificate phase** of the round: the local certificates of all test sets, for both
strings (`certPhase`, `Workspace/Algorithm/CertificatePhase.lean`). -/
noncomputable def certScript : Script (List (StagePair S)) :=
  haveI := I.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  certPhase S I.πd P.κ I.sets I.reps (dstr S S.x) (dstr S S.y)

/-- **The comparison phase** of the round: the lockstep comparisons of all pairs of ordered test
tuples of the two strings (`comparePhase`, `Workspace/Algorithm/ComparisonPhase.lean`). With
exact answers it computes the relation `CompareRel` from which the tuple colors of the canonical
structures are built (`compScript_evalExact`). -/
noncomputable def compScript : Script (List Bool) :=
  haveI := I.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  comparePhase S I.πd P.κ I.tests I.pick (dstr S S.x) (dstr S S.y)

/-- **The comparison phase computes the comparison relation**: the entry of a pair of ordered
test tuples is `true` exactly when their ordered comparison set is nonempty. -/
theorem compScript_evalExact :
    haveI := I.fin
    letI : Fintype S.dom := Fintype.ofFinite _
    letI : DecidableEq Ω := Classical.decEq _
    I.compScript.evalExact = (I.tests.tuples.flatMap fun a =>
      I.tests.tuples.map fun b =>
        (compareScript S I.πd I.pick (strOf S (dstr S S.x) (dstr S S.y) a.1)
          (strOf S (dstr S S.x) (dstr S S.y) b.1) a.2 b.2).evalExact) ∧
    ∀ a b : TestTuple L.q P.κ,
      (compareScript S I.πd I.pick (strOf S (dstr S S.x) (dstr S S.y) a.1)
          (strOf S (dstr S S.x) (dstr S S.y) b.1) a.2 b.2).evalExact = true ↔
        GI.LocalCertificates.CompareRel S.domGroup I.πd P.κ
          (strOf S (dstr S S.x) (dstr S S.y) a.1, a.2) (strOf S (dstr S S.x) (dstr S S.y) b.1, b.2) :=
  haveI := I.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  comparePhase_evalExact _ _ _ _ _ _ _

/-- The auxiliary part of the round: the items' scripts in order, their outputs concatenated. -/
noncomputable def itemsScript : Script (Branches Ω) :=
  (Script.seqList (I.tuples.map fun b => (I.items b).script)).bind fun l =>
    Script.done (Branches.concat l)

/-- **The script of the aggregation round**: the certificate phase and the ordered comparisons
(Lemma 4.1), then the items of all branches (Algorithm `alg:auxiliary`). -/
noncomputable def script : Script (Branches Ω) :=
  I.certScript.bind fun _ => I.compScript.bind fun _ => I.itemsScript

theorem script_evalExact :
    I.script.evalExact = Branches.concat (I.tuples.map fun b => (I.items b).script.evalExact) := by
  simp only [script, itemsScript, Script.evalExact_bind, Script.evalExact_seqList, List.map_map]
  rfl

theorem mem_pieces {p : Set (Perm Ω)} :
    p ∈ I.script.evalExact.pieces ↔ ∃ b, p ∈ (I.items b).script.evalExact.pieces := by
  rw [script_evalExact]
  simp [Branches.concat, mem_tuples]

theorem mem_overs {o : Perm Ω × Subgroup (Perm Ω)} :
    o ∈ I.script.evalExact.overs ↔ ∃ b, o ∈ (I.items b).script.evalExact.overs := by
  rw [script_evalExact]
  simp [Branches.concat, mem_tuples]

/-- Every overcoset is a lift `(τ, π⁻¹(E₀))` with `π(τ) ∈ ...` and `aw(E₀) ≤ βq`. -/
theorem overs_cap : ∀ o ∈ I.script.evalExact.overs, ∃ (σ : alternatingGroup (Fin L.q))
    (E₀ : Subgroup (alternatingGroup (Fin L.q))), GI.SectionCaps.Cap E₀ ⌊P.β * L.q⌋₊ ∧ o = (L.rep σ, L.lift E₀) := by
  intro o ho
  obtain ⟨b, hb⟩ := (I.mem_overs).1 ho
  exact (I.items b).overs_spec (I.items_valid b) o hb

/-- **Covering** (proof of Lemma 6.1: "every parent isomorphism is covered by an aggregation
branch"). -/
theorem covers : Branches.Covers S I.script.evalExact where
  pieces_sub p hp := by
    obtain ⟨b, hb⟩ := (I.mem_pieces).1 hp
    exact (I.items b).pieces_sub (I.items_valid b) p hb
  overs_mem j := by
    obtain ⟨σ, E₀, -, he⟩ := I.overs_cap _ (List.get_mem _ j)
    rw [he]; exact L.rep_mem σ
  overs_le j := by
    obtain ⟨σ, E₀, -, he⟩ := I.overs_cap _ (List.get_mem _ j)
    rw [he]; exact L.lift_le E₀
  cover g hg := by
    obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (I.cover hg)
    rcases (I.items b).cover (I.items_valid b) hb with h | h
    · left
      simp only [Set.mem_iUnion, exists_prop] at h ⊢
      obtain ⟨p, hp, hgp⟩ := h
      exact ⟨p, (I.mem_pieces).2 ⟨b, hp⟩, hgp⟩
    · right
      simp only [Set.mem_iUnion, exists_prop] at h ⊢
      obtain ⟨o, ho, hgo⟩ := h
      obtain ⟨j, hj⟩ := List.mem_iff_get.1 ((I.mem_overs).2 ⟨b, ho⟩)
      exact ⟨j, by rw [hj]; exact hgo⟩

/-- The calls of the certificate phase are charged calls (Lemma 4.1, clause 2). -/
theorem certScript_calls : I.certScript.CallsExact (AggCall P S) := by
  haveI := I.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  exact certPhase_calls S I.πd P.κ I.sets I.reps I.htr rfl I.κ_five I.θκ _ _

/-- The calls of the comparison phase are charged calls (Lemma 4.1, clause 2). -/
theorem compScript_calls : I.compScript.CallsExact (AggCall P S) := by
  haveI := I.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  exact comparePhase_calls S I.πd P.κ I.tests I.pick I.htr rfl I.κ_five I.θκ _ _

/-- Every call is an inherited charged call or a fresh configuration call. -/
theorem calls : I.script.CallsExact (AggCall P S) :=
  Script.callsExact_bind _ _ I.certScript_calls
    (Script.callsExact_bind _ _ I.compScript_calls
      (Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hs
        exact (I.items b).calls (I.items_valid b)) trivial))



theorem itemsScript_numCont_le : I.itemsScript.numCont ≤ 3 * L.q ^ I.ℓ := by
  simp only [itemsScript, Script.numCont_bind, Script.numCont_seqList, List.map_map]
  simp only [Script.numCont, add_zero]
  have h := List.sum_le_card_nsmul (I.tuples.map (Script.numCont ∘ fun b => (I.items b).script)) 3
    (fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
      exact (I.items b).numCont_le (I.items_valid b))
  rw [List.length_map, length_tuples, smul_eq_mul] at h
  linarith

/-- The certificate phase makes at most `2 binom(q, κ) s κ!` `Continue` calls. -/
theorem certScript_numCont_le :
    I.certScript.numCont ≤ 2 * L.q.choose P.κ * S.size * P.κ.factorial := by
  haveI := I.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  have h := certPhase_numCont_le S I.πd P.κ I.sets I.reps (dstr S S.x) (dstr S S.y)
  have hs : Fintype.card S.dom = S.size := by
    rw [State.size, Nat.card_eq_fintype_card]
  rw [hs] at h
  exact h

/-- The comparison phase makes at most `4 q^{2κ} s` `Continue` calls. -/
theorem compScript_numCont_le : I.compScript.numCont ≤ 4 * L.q ^ (2 * P.κ) * S.size := by
  haveI := I.fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq Ω := Classical.decEq _
  have h := comparePhase_numCont_le S I.πd P.κ I.tests I.pick (dstr S S.x) (dstr S S.y)
  have hs : Fintype.card S.dom = S.size := by
    rw [State.size, Nat.card_eq_fintype_card]
  rw [hs] at h
  exact h

theorem numCont_le :
    I.script.numCont ≤ 2 * L.q.choose P.κ * S.size * P.κ.factorial +
      (4 * L.q ^ (2 * P.κ) * S.size + 3 * L.q ^ I.ℓ) := by
  rw [script, Script.numCont_bind, Script.numCont_bind]
  exact Nat.add_le_add I.certScript_numCont_le
    (Nat.add_le_add I.compScript_numCont_le I.itemsScript_numCont_le)

theorem overs_length_le : I.script.evalExact.overs.length ≤ 2 * L.q ^ I.ℓ := by
  rw [script_evalExact]
  simp only [Branches.concat, List.length_flatMap, List.map_map]
  have h := List.sum_le_card_nsmul
    (I.tuples.map ((fun b : Branches Ω => b.overs.length) ∘ fun b => (I.items b).script.evalExact)) 2
    (fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
      exact (I.items b).overs_length_le (I.items_valid b))
  rw [List.length_map, length_tuples, smul_eq_mul] at h
  linarith

/-- **At most `N^a` inherited calls** (Section 7.2, rows "Affected test or rectangle" and
"Visible unaffected test": multiplicity `N^a`). The certificate phase makes at most
`2 binom(q, κ) s κ! ≤ N^{2κ+2}` calls (`q, s ≤ N`, `κ! ≤ κ^κ ≤ N^κ` since `κ < q`), the
comparison phase at most
`4 q^{2κ} s ≤ N^{2κ+3}`, and the auxiliary calls number at most `3 q^ℓ ≤ N^{ℓ+2}`; together at
most `3 N^{2κ+ℓ+3} ≤ N^{2κ+ℓ+4} ≤ N^a`. -/
theorem count_bound :
    (((2 * L.q.choose P.κ * S.size * P.κ.factorial +
      (4 * L.q ^ (2 * P.κ) * S.size + 3 * L.q ^ I.ℓ) : ℕ) : ℝ)) ≤ (S.N : ℝ) ^ P.a := by
  have hq2 : (2 : ℝ) ≤ L.q := by exact_mod_cast I.q_two
  have hqN : (L.q : ℝ) ≤ S.N := by exact_mod_cast I.q_le
  have hN2 : (2 : ℝ) ≤ S.N := by linarith
  have hN1 : (1 : ℝ) ≤ S.N := by linarith
  have hsN : (S.size : ℝ) ≤ S.N := by exact_mod_cast I.size_le
  have hN3 : (3 : ℝ) ≤ S.N := by
    have h10 : (10 : ℝ) ≤ L.q := by exact_mod_cast I.q_ten
    linarith
  -- `κ! ≤ κ^κ ≤ N^κ`, since `κ < q ≤ N`
  have hfN : (P.κ.factorial : ℝ) ≤ (S.N : ℝ) ^ P.κ := by
    have h1 : P.κ.factorial ≤ P.κ ^ P.κ := Nat.factorial_le_pow _
    have h2 : (P.κ : ℝ) ≤ S.N := by exact_mod_cast (I.κ_lt_q.le.trans I.q_le)
    calc (P.κ.factorial : ℝ) ≤ ((P.κ ^ P.κ : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (P.κ : ℝ) ^ P.κ := by push_cast; ring
      _ ≤ (S.N : ℝ) ^ P.κ := pow_le_pow_left₀ (by positivity) h2 _
  have hch : (L.q.choose P.κ : ℝ) ≤ (S.N : ℝ) ^ P.κ := by
    calc (L.q.choose P.κ : ℝ) ≤ ((L.q ^ P.κ : ℕ) : ℝ) := by
          exact_mod_cast Nat.choose_le_pow L.q P.κ
      _ = (L.q : ℝ) ^ P.κ := by push_cast; ring
      _ ≤ (S.N : ℝ) ^ P.κ := pow_le_pow_left₀ (by linarith) hqN _
  -- the certificate phase
  have hcert : ((2 * L.q.choose P.κ * S.size * P.κ.factorial : ℕ) : ℝ) ≤
      (S.N : ℝ) ^ (2 * P.κ + 2) := by
    push_cast
    calc 2 * (L.q.choose P.κ : ℝ) * S.size * P.κ.factorial
        = 2 * ((L.q.choose P.κ : ℝ) * S.size * P.κ.factorial) := by ring
      _ ≤ S.N * ((S.N : ℝ) ^ P.κ * S.N * (S.N : ℝ) ^ P.κ) := by
          apply mul_le_mul hN2 (mul_le_mul (mul_le_mul hch hsN (by positivity) (by positivity))
            hfN (by positivity) (by positivity)) (by positivity) (by positivity)
      _ = (S.N : ℝ) ^ (2 * P.κ + 2) := by ring
  -- the comparison phase
  have hcomp : ((4 * L.q ^ (2 * P.κ) * S.size : ℕ) : ℝ) ≤ (S.N : ℝ) ^ (2 * P.κ + 3) := by
    push_cast
    calc 4 * (L.q : ℝ) ^ (2 * P.κ) * S.size ≤ (S.N : ℝ) ^ 2 * (S.N : ℝ) ^ (2 * P.κ) * S.N := by
          apply mul_le_mul (mul_le_mul (by nlinarith) (pow_le_pow_left₀ (by linarith) hqN _)
            (by positivity) (by positivity)) hsN (by positivity) (by positivity)
      _ = (S.N : ℝ) ^ (2 * P.κ + 3) := by ring
  -- the auxiliary calls
  have haux : ((3 * L.q ^ I.ℓ : ℕ) : ℝ) ≤ (S.N : ℝ) ^ (I.ℓ + 2) := by
    push_cast
    calc 3 * (L.q : ℝ) ^ I.ℓ ≤ (S.N : ℝ) ^ 2 * (S.N : ℝ) ^ I.ℓ := by
          apply mul_le_mul (by nlinarith) (pow_le_pow_left₀ (by linarith) hqN _)
            (by positivity) (by positivity)
      _ = (S.N : ℝ) ^ (I.ℓ + 2) := by ring
  set M := 2 * P.κ + I.ℓ + 3
  have hpow : ∀ m : ℕ, m ≤ M → (S.N : ℝ) ^ m ≤ (S.N : ℝ) ^ M :=
    fun m hm => pow_le_pow_right₀ hN1 hm
  have hM0 : (0 : ℝ) ≤ (S.N : ℝ) ^ M := by positivity
  calc ((2 * L.q.choose P.κ * S.size * P.κ.factorial +
          (4 * L.q ^ (2 * P.κ) * S.size + 3 * L.q ^ I.ℓ) : ℕ) : ℝ)
      = ((2 * L.q.choose P.κ * S.size * P.κ.factorial : ℕ) : ℝ) +
          (((4 * L.q ^ (2 * P.κ) * S.size : ℕ) : ℝ) + ((3 * L.q ^ I.ℓ : ℕ) : ℝ)) := by
        push_cast; ring
    _ ≤ (S.N : ℝ) ^ M + ((S.N : ℝ) ^ M + (S.N : ℝ) ^ M) :=
        add_le_add (hcert.trans (hpow _ (by omega)))
          (add_le_add (hcomp.trans (hpow _ (by omega))) (haux.trans (hpow _ (by omega))))
    _ ≤ (S.N : ℝ) * (S.N : ℝ) ^ M := by nlinarith
    _ = (S.N : ℝ) ^ (M + 1) := by ring
    _ = (S.N : ℝ) ^ (((M + 1 : ℕ) : ℝ)) := by rw [Real.rpow_natCast]
    _ ≤ (S.N : ℝ) ^ P.a :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by simp only [M]; push_cast; linarith [I.a_cert])

/-- **At most `N^a` inherited calls**: `numCont_le` and `count_bound`. -/
theorem calls_count : (I.script.numCont : ℝ) ≤ (S.N : ℝ) ^ P.a :=
  le_trans (by exact_mod_cast I.numCont_le) I.count_bound

/-- **At most `q^a` overcosets** (Section 7.2: "a same-domain configuration or rectangle
continuation has at most `q^a` choices … They come from bounded tuples, anchors, and orbital
choices on the `q` labels"): `2 q^ℓ ≤ q^{ℓ+1} ≤ q^a`. -/
theorem overs_count : (I.script.evalExact.overs.length : ℝ) ≤ (L.q : ℝ) ^ P.a := by
  have hq2 : (2 : ℝ) ≤ L.q := by exact_mod_cast I.q_two
  calc (I.script.evalExact.overs.length : ℝ) ≤ 2 * (L.q : ℝ) ^ I.ℓ := by
        exact_mod_cast I.overs_length_le
    _ ≤ (L.q : ℝ) * (L.q : ℝ) ^ I.ℓ := by
        apply mul_le_mul_of_nonneg_right hq2 (by positivity)
    _ = (L.q : ℝ) ^ (I.ℓ + 1) := by ring
    _ = (L.q : ℝ) ^ ((I.ℓ : ℝ) + 1) := by rw [← Real.rpow_natCast]; push_cast; rfl
    _ ≤ (L.q : ℝ) ^ P.a :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [I.ℓ_le])

/-- The hierarchy of the continuation on an overcoset: the selected interval bound becomes
`min{c, ⌊βq⌋}`, all other bounds are unchanged (`LiftAndContinue`: "It replaces the selected
interval bound by the minimum of its old value and `βq` … All other parent bounds remain
unchanged"). -/
noncomputable def newHier (_ : Perm Ω × Subgroup (Perm Ω)) : List (Interval Ω) :=
  S.hier.set I.sel { S.hier[I.sel] with cap := min S.hier[I.sel].cap ⌊P.β * L.q⌋₊ }

/-- **The continuations keep the carrier** of the retained rows: the group of a continuation is
`π⁻¹(E₀)`, which contains every element that fixes every retained column, since such an element
has trivial label image (`Constituent.kills`); and the cap update keeps the partitions of the
hierarchy (Section A.4: "use full preimages of all quotient restrictions. This keeps the entire
kernel `J`"). -/
theorem overs_keep (o : Perm Ω × Subgroup (Perm Ω)) (ho : o ∈ I.script.evalExact.overs) :
    CarrierOK o.2 S.dom S.rows (I.newHier o) := by
  obtain ⟨σ, E₀, -, rfl⟩ := I.overs_cap o ho
  refine S.carrier.mono (L.lift_le E₀) (fun R c hR hc g hg hf => ?_) fun c h => h.of_parts ?_
  · refine L.mem_lift.2 ⟨hg, ?_⟩
    rw [I.con.kills R c hR hc ⟨g, hg⟩ hf]
    exact E₀.one_mem
  · exact map_part_set_cap _ _ _ _

/-- **The cap update** of every continuation. The new bound is valid: the group of the
continuation is `π⁻¹(E₀)` with `aw(E₀) ≤ βq` (`overs_cap`). -/
theorem capUpdate : ∀ o ∈ I.script.evalExact.overs, CapUpdate P S.hier L.q (I.newHier o) :=
  fun _ _ => ⟨I.sel, I.sel_cap, I.sel_clamped, rfl⟩

end Aggregation

end GI.Algorithm
