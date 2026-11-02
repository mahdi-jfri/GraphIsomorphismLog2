import Workspace.Algorithm.AggregationParams
import Workspace.Algorithm.HierInv

/-!
# The data that the supplied labels carry

`GiantLabels S` is only a surjection `π : G ↠ Alt(q)`. The labels that the recursion actually
supplies to `GiantStep` come from the normalization of a single alternating factor of a primitive
quotient of the domain action (Algorithm 5: "Normalize the single alternating factor"). The paper
attaches more to them:

* the labels are read on the domain (Section 3: "Every fresh call uses the faithful permutation
  image on its own active domain"; the primitive quotient is a quotient of the domain action), so
  `π` kills every element that fixes the domain pointwise (`GiantLabels.OnDomain`);
* the labels lie above the retained columns (Algorithm 5: "Expose the next primitive quotient
  above any retained column partition"), so every element of `G` that fixes every retained
  column has trivial label image (`GiantLabels.Constituent.kills`);
* the block map of the selected Cameron constituent, `p : dom → binom(Γ, h)` with
  `1 ≤ h ≤ q/2` (Lemma A.11: "Assume its actual equivariant block map is `p : Ω → binom(Γ, h)`";
  Section A.5, "Constructive recognition": the Cameron constituent acts on the `k`-subsets of
  `[m]`; the Johnson scheme `J(m,k)` is `J(m,m-k)`, so `h = min(k, m-k)`).

`GiantLabels.Constituent L` holds these two facts, and `SuppliedLabels S` is a label set with
them. `NormAbove P S` is the single-factor normalization with its degree above `q₀` and the
constituent data of its labels on every child state; it is built in
`Workspace/Algorithm/NormLabels.lean`.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

variable {Ω C : Type}

/-- **The data of the selected Cameron constituent** that the supplied labels carry: the labels
are read on the domain, and the Johnson block map of the constituent (Lemma A.11; Section A.5,
"Constructive recognition"). -/
structure GiantLabels.Constituent {S : State Ω C} (L : GiantLabels S) : Type where
  /-- The labels are read on the domain: an element that fixes every point of the domain has
  trivial label image. -/
  onDomain : L.OnDomain
  /-- The Johnson block map `p : dom → binom(Γ, h)`, `1 ≤ h ≤ q/2`, of the constituent. -/
  blocks : JohnsonBlocks S L
  /-- The labels lie above the retained columns (Algorithm 5: "Expose the next primitive
  quotient above any retained column partition"): an element that fixes every retained column
  has trivial label image. -/
  kills : ∀ R c, S.rows = some R → R.cols = some c → ∀ g : S.G, FixesCols c S.dom g → L.π g = 1

/-- Without a row record, the condition `Constituent.kills` is empty. -/
theorem GiantLabels.kills_of_none {S : State Ω C} (L : GiantLabels S) (h : S.rows = none) :
    ∀ R c, S.rows = some R → R.cols = some c → ∀ g : S.G, FixesCols c S.dom g → L.π g = 1 :=
  fun _ _ hR => absurd (h.symm.trans hR) (by simp)

/-- **The supplied alternating labels of a giant step** (Algorithm 5, `GiantStep(S, Γ)`, with
`Γ` from the single-factor normalization): a label map with the data of its Cameron
constituent. -/
structure SuppliedLabels (S : State Ω C) extends GiantLabels S where
  con : toGiantLabels.Constituent
  /-- **The interval of the selected constituent** (Section 7.2: "the selected alternating
  section belongs to that whole constituent"): its coarse end holds the domain, and the labels
  are the action on its fine classes, so an element has trivial label image exactly when it
  fixes every fine class. -/
  sel : Fin S.hier.length
  sel_univ : ∀ v ∈ S.dom, ∀ w ∈ S.dom, (S.hier[sel]).part.r v w
  sel_ker : ∀ g : S.G, toGiantLabels.π g = 1 ↔
    ∀ w ∈ S.dom, (fineEnd ⊥ (S.hier.take sel)).r ((g : Perm Ω) w) w

instance {S : State Ω C} : CoeOut (SuppliedLabels S) (GiantLabels S) :=
  ⟨SuppliedLabels.toGiantLabels⟩

/-- The labels of the normalized group on a child state with group `G'` and the parent domain:
`π : G' ↠ Alt(q)`. -/
def Normalization.labels {S : State Ω C} (I : Normalization S) (x y : Ω → C)
    (hier : List (Interval Ω)) : GiantLabels (S.restrict I.G' I.le x y hier) :=
  ⟨I.q, I.π, I.π_surj⟩

/-- **The single-factor normalization as the recursion uses it** (Algorithm 5: "Normalize the
single alternating factor, with at most two cosets"): its degree is above `q₀` (Section A.3:
"When `m ≤ q₀`, enumerate the alternating quotient"), and on every child state (the group `G'`
on the parent domain) its labels carry the data of the Cameron constituent. -/
structure NormAbove (P : Params) (S : State Ω C) : Type 1 where
  I : Normalization S
  q_large : P.q₀ < I.q
  con : ∀ (x y : Ω → C) (hier : List (Interval Ω)), (I.labels x y hier).Constituent
  /-- The hierarchy of the children satisfies the invariant for the normalized group. -/
  tower : HierInv I.G' S.dom I.hier'
  /-- The exposed interval: its coarse end holds the domain, and the labels are the action on
  its fine classes (Section A.5: "Expose the next primitive quotient"). -/
  sel : Fin I.hier'.length
  sel_univ : ∀ v ∈ S.dom, ∀ w ∈ S.dom, (I.hier'[sel]).part.r v w
  sel_ker : ∀ g : I.G', I.π g = 1 ↔
    ∀ w ∈ S.dom, (fineEnd ⊥ (I.hier'.take sel)).r ((g : Perm Ω) w) w
  /-- The normalized group keeps the carrier of the retained rows: it contains every element
  that fixes every retained column (Section A.4: "use full preimages of all quotient
  restrictions. This keeps the entire kernel `J`"). -/
  keeps : CarrierOK I.G' S.dom S.rows I.hier'

/-- The supplied labels of a child state of a normalization. -/
def NormAbove.labels {P : Params} {S : State Ω C} (N : NormAbove P S) (x y : Ω → C) :
    SuppliedLabels (S.restrict N.I.G' N.I.le x y N.I.hier') :=
  ⟨N.I.labels x y N.I.hier', N.con x y N.I.hier', N.sel, N.sel_univ, N.sel_ker⟩

end GI.Algorithm
