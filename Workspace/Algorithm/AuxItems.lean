module

public import Workspace.Algorithm.AggregationCanon
public import Workspace.Algorithm.CertificatePhase
public import Workspace.Algorithm.ComparisonPhase
public import Workspace.Paper.Caps
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Data.List.ReduceOption

@[expose] public section

/-!
# The aggregation round as a procedure on its structural data

This file defines the interface `Aggregation` of the aggregation path of `GiantStep`
(Algorithm 5, after "Freeze `S_0 ← S`"), and the query script that the recursion runs for
it. The script is not a field. It is computed from the structural data of the paper's
aggregation step by the paper's procedure, and the facts that the recursion needs
(`covers`, `calls`, `calls_count`, `overs_count`, `capUpdate`) are theorems.

## What the paper does

Section 4.1 ("From the tests to an auxiliary graph") aggregates the local certificates
by the case analysis of [H, Section 6.2], re-proved in Section A.3 for constant-size
certificates (Cases 1, 2a, 2b, 3). Each case branches over a bounded tuple of labels: the
anchors of Case 2b and the image of its source orbital, the individualized points of the
Design Lemma in Case 3, and the source vertex of the first rectangle (Lemma 5.1). For each
choice of target images, Algorithm `alg:auxiliary` (`AuxiliaryReduction`) appends to the
list `ℰ` one overcoset on the label set `Γ`:

* a balanced colored partition (Case 1; Design outcome (a); the balanced outcomes of
  Lemma 5.1): its full allowed coset on `Γ`, with no recursive call;
* a configuration on `q ≤ λ` labels (Lemma A.12): one fresh `Solve` call on the pair
  structure, extended to `Γ`;
* a rectangle (Lemma 5.1, A.27, A.30): at most two `Continue` calls on an inherited orbit
  `Δ`, whose answer is projected to the left side and extended over `Γ \ W`.

Case 2a (Lemma A.11) instead returns exact pieces of the parent answer: three `Continue`
calls under the kernel `K` of the dominant alternating factor give `Aut_K(x)` and the two
parity twists, and the lifts of the large alternating factor recover the answer.

`LiftAndContinue` lifts each overcoset `σ E₀` to `τ π⁻¹(E₀)` with `π(τ) = σ`, and the
selected interval bound becomes `min{c, βq}`. This last step is the `aggregate`
constructor of `GI.Algorithm.Run`.

## The data

An `Aggregation` consists of
* the selected interval `sel` of the Cameron constituent of the labels, with `q ≤ c ≤ d`
  there (Section 7.2: "The old cap is at least `q` because the selected alternating section
  belongs to that whole constituent"; Section 3.3: "every stored bound is at most its
  current interval ratio");
* the length `ℓ` of the branch tuples and one `AuxItem` for each tuple `b : [ℓ] → Γ`
  of target images;
* the facts that each item satisfies (`AuxItem.Valid`): the cap `aw(E₀) ≤ βq` of every
  overcoset group (Lemma 5.1, Lemma A.12, Section A.3 "Case 1 and balanced colored
  partitions"), the call types of the queries, and for Case 2a the groups of Lemma A.11;
* the covering of the parent answer by the branches of the items (`cover`), the
  equivariance claim of Section A.3 and [H, Section 6.2]: "Every genuine parent isomorphism
  conjugates the two anchored subgroups and carries the chosen source orbital to one of the
  enumerated target orbitals. Consequently the branches cover every parent isomorphism".

The adapters from the proved lemmas to the items are in
`Workspace/Algorithm/AggregationItems.lean`.

## Why there is no trivial instance

The script is `Aggregation.script`, a function of the items. Its exact pieces are only the
large-symmetry pieces `ρ b · Aut_K(x) · A`, built from `Continue` answers under the
kernel `K = π⁻¹(Alt(Φ) × Alt(C)) ∩ π⁻¹(1_Φ)` whose orbits have at most `θ s` points. Its
overcosets are only lifts `τ π⁻¹(E₀)` with `aw(E₀) ≤ βq` (`overs_cap`). So no instance
returns `S.answer` itself, or an overcoset of the whole group, without recursive work.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Rectangle
open scoped Pointwise

variable {Ω C : Type}

-- The lemmas `Script.numCont_bind`, `callsExact_seqList`, `numCont_seqList` are in
-- `Workspace/Algorithm/Interfaces.lean`.

/-- The concatenation of the outputs of several branches. -/
def Branches.concat (l : List (Branches Ω)) : Branches Ω :=
  ⟨l.flatMap Branches.pieces, l.flatMap Branches.overs⟩

/-! ### Lifting overcosets from the labels to the positions -/

namespace GiantLabels

variable {S : State Ω C} (L : GiantLabels S)

/-- `π⁻¹(E₀)` as a subgroup of `Sym(Ω)`: the group of the lifted overcoset
(`LiftAndContinue`: "lifts `E` to a coset `Hτ` in the original parent action"). -/
def lift (E₀ : Subgroup (alternatingGroup (Fin L.q))) : Subgroup (Perm Ω) :=
  (E₀.comap L.π).map S.G.subtype

theorem mem_lift {E₀ : Subgroup (alternatingGroup (Fin L.q))} {g : Perm Ω} :
    g ∈ L.lift E₀ ↔ ∃ hg : g ∈ S.G, L.π ⟨g, hg⟩ ∈ E₀ := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, hh⟩
  · rintro ⟨hg, hE⟩
    exact ⟨⟨g, hg⟩, hE, rfl⟩

theorem lift_le (E₀ : Subgroup (alternatingGroup (Fin L.q))) : L.lift E₀ ≤ S.G :=
  fun _ hg => ((L.mem_lift).1 hg).1

/-- A lift `τ ∈ G` of a label permutation `σ`: `π(τ) = σ`. -/
noncomputable def rep (σ : alternatingGroup (Fin L.q)) : Perm Ω :=
  ((L.π_surj σ).choose : Perm Ω)

theorem rep_mem (σ : alternatingGroup (Fin L.q)) : L.rep σ ∈ S.G :=
  (L.π_surj σ).choose.2

theorem π_rep (σ : alternatingGroup (Fin L.q)) : L.π ⟨L.rep σ, L.rep_mem σ⟩ = σ :=
  (L.π_surj σ).choose_spec

/-- The elements of `G` whose label image lies in the overcoset `σ E₀`. -/
def overSet (σ : alternatingGroup (Fin L.q)) (E₀ : Subgroup (alternatingGroup (Fin L.q))) :
    Set (Perm Ω) :=
  {g | ∃ hg : g ∈ S.G, σ⁻¹ * L.π ⟨g, hg⟩ ∈ E₀}

/-- `LiftAndContinue`, first claim of `GI.Paper.alg_auxiliary_lift_and_continue`: the lift of
the overcoset `σ E₀` lies in `τ π⁻¹(E₀)`. -/
theorem overSet_subset (σ : alternatingGroup (Fin L.q))
    (E₀ : Subgroup (alternatingGroup (Fin L.q))) :
    L.overSet σ E₀ ⊆ L.rep σ • (L.lift E₀ : Set (Perm Ω)) := by
  rintro g ⟨hg, hE⟩
  have hm : (L.rep σ)⁻¹ * g ∈ S.G := S.G.mul_mem (S.G.inv_mem (L.rep_mem σ)) hg
  refine ⟨(L.rep σ)⁻¹ * g, (L.mem_lift).2 ⟨hm, ?_⟩, by simp⟩
  have e : L.π ⟨(L.rep σ)⁻¹ * g, hm⟩ = (L.π ⟨L.rep σ, L.rep_mem σ⟩)⁻¹ * L.π ⟨g, hg⟩ := by
    rw [← map_inv, ← map_mul]; rfl
  rw [e, L.π_rep]
  exact hE

end GiantLabels

/-! ### The items of the auxiliary reduction -/

/-- A recursive query of `AuxiliaryReduction`: a call `mode` on the state `T`, and the
overcoset representative `read A` that the procedure reads off the answer `A` of the call
(Algorithm `alg:auxiliary`: "Project the entire returned coset, including its representative
and generators, and retain the source--target alignment"; "Extend `I` using the outer color
classes, fixed anchors, and parity"). `read A = none` means that no overcoset is appended ("**if**
this answer is empty **then continue**"; an empty parity coset is rejected). -/
structure AuxQuery (P : Params) {Ω C : Type} (S : State Ω C) (L : GiantLabels S) : Type 1 where
  mode : Mode
  Ω' : Type
  C' : Type
  T : State Ω' C'
  read : Set (Perm Ω') → Option (alternatingGroup (Fin L.q))
  /-- A fresh `Solve` query is asked on a finite set of positions. -/
  solve_fin : mode = .solve → Finite Ω'

namespace AuxQuery

variable {P : Params} {S : State Ω C} {L : GiantLabels S}

/-- Ask the query and read its representative. -/
noncomputable def script (Q : AuxQuery P S L) : Script (Option (alternatingGroup (Fin L.q))) :=
  Script.ask Q.mode Q.T fun A => Script.done (Q.read A)

theorem script_evalExact (Q : AuxQuery P S L) : Q.script.evalExact = Q.read Q.T.answer := rfl

end AuxQuery

/-- **The large-symmetry branch** (Case 2a, Lemma A.11). `Φ` is the dominant orbit of the
ideal image of `F_x` (after aligning the target, `τ₀`). The groups are the paper's:
* `H = π⁻¹((Sym(Φ) × Sym(C)) ∩ Alt(Γ))` (`big`), `C = Γ \ Φ`;
* `H₀ = π⁻¹(Alt(Φ) × Alt(C))` (`even`);
* `K = π⁻¹(1_Φ × Alt(C))` (`ker`).
`t` is the parity twist ("an even paired transposition … supplies its representative"),
and `A` is generated by the lifts `a₁, a₂ ∈ F_x ∩ H₀` of two generators of `Alt(Φ) × 1`. -/
structure Halving {Ω C : Type} (S : State Ω C) (L : GiantLabels S) where
  Φ : Finset (Fin L.q)
  τ₀ : Perm Ω
  t : Perm Ω
  A : Subgroup (Perm Ω)

namespace Halving

variable {P : Params} {S : State Ω C} {L : GiantLabels S} (H : Halving S L)

/-- `H = π⁻¹((Sym(Φ) × Sym(C)) ∩ Alt(Γ))`. -/
def big : Subgroup (Perm Ω) := L.lift (permitted H.Φ H.Φᶜ)

/-- `H₀ = π⁻¹(Alt(Φ) × Alt(C))`. -/
def even : Subgroup (Perm Ω) := L.lift (evenSides H.Φ H.Φᶜ)

/-- `K = π⁻¹(1_Φ × Alt(C))`: the elements of `H₀` whose label image fixes `Φ` pointwise. -/
def ker : Subgroup (Perm Ω) :=
  L.lift (evenSides H.Φ H.Φᶜ ⊓
    fixingSubgroup (alternatingGroup (Fin L.q)) (H.Φ : Set (Fin L.q)))

theorem ker_le_even : H.ker ≤ H.even := fun g hg => by
  obtain ⟨hgG, hE⟩ := (L.mem_lift).1 hg
  exact (L.mem_lift).2 ⟨hgG, hE.1⟩

theorem ker_le : H.ker ≤ S.G := L.lift_le _

/-- The inherited `Continue` state under `K` on the parent domain with target `z`. It clears the
bookkeeping (`State.queryChild`). -/
noncomputable def kerState (z : Ω → C) : State Ω C :=
  S.queryChild H.ker S.dom (S.dom_inv.mono H.ker_le) S.x z

@[simp] theorem kerState_G (z : Ω → C) : (H.kerState z).G = H.ker := S.queryChild_G ..
@[simp] theorem kerState_dom (z : Ω → C) : (H.kerState z).dom = S.dom := S.queryChild_dom ..
@[simp] theorem kerState_x (z : Ω → C) : (H.kerState z).x = S.x := S.queryChild_x ..
@[simp] theorem kerState_y (z : Ω → C) : (H.kerState z).y = z := S.queryChild_y ..
@[simp] theorem kerState_N (z : Ω → C) : (H.kerState z).N = S.N := S.queryChild_N ..
@[simp] theorem kerState_hier (z : Ω → C) : (H.kerState z).hier = S.hier := S.queryChild_hier ..
theorem kerState_answer (z : Ω → C) :
    (H.kerState z).answer = GI.Algorithm.answer H.ker S.dom S.x z := S.queryChild_answer ..

open Classical in
/-- The exact piece of one parity class: if `b` is a `K`-transporter to the twisted target
`y ∘ ρ`, the piece is `ρ b · Aut_K(x) · A` (Lemma A.11: "If `t ∈ Iso_K(x,z)` is found, the
full answer is `Aut_{H₀}(x) t`", and `Aut_{H₀}(x) = ⟨Aut_K(x), a₁, a₂⟩`). -/
noncomputable def piece (ρ : Perm Ω) (AK B : Set (Perm Ω)) : Set (Perm Ω) :=
  if h : B.Nonempty then (ρ * h.some) • (AK * (H.A : Set (Perm Ω))) else ∅

/-- The script of Lemma A.11: `Aut_K(x)`, and the `K`-transporters for the two parity
classes ("Compute `Aut_K(x)` and the `K`-transporters for the at-most-two parity twists by
these orbit chains. Combine the successful full cosets and undo the initial alignment"). -/
noncomputable def script : Script (Branches Ω) :=
  Script.ask .cont (H.kerState S.x) fun AK =>
  Script.ask .cont (H.kerState (S.y ∘ H.τ₀)) fun B₁ =>
  Script.ask .cont (H.kerState (S.y ∘ (H.τ₀ * H.t))) fun B₂ =>
  Script.done ⟨[H.piece H.τ₀ AK B₁, H.piece (H.τ₀ * H.t) AK B₂], []⟩

/-- The facts of Lemma A.11 that the branch uses. -/
structure Valid (P : Params) : Prop where
  τ₀_mem : H.τ₀ ∈ S.G
  /-- "The index `[H:H₀]` is at most two"; the twist `t` represents the second coset. -/
  t_mem : H.t ∈ H.big
  split : ∀ g ∈ H.big, g ∈ H.even ∨ H.t⁻¹ * g ∈ H.even
  /-- `a₁, a₂ ∈ F_x ∩ H₀`, so both lifts preserve `x`. -/
  A_le : H.A ≤ H.even
  A_aut : ∀ a ∈ H.A, ∀ v ∈ S.dom, S.x (a v) = S.x v
  /-- "They map onto generators of `H₀/K`." -/
  onto : ∀ h ∈ H.even, ∃ a ∈ H.A, h * a⁻¹ ∈ H.ker
  /-- "Every physical `K`-orbit has size at most `n/2`" (with `θ ≥ 1/2`). -/
  orb_small : ∀ v ∈ S.dom, (Nat.card (orb H.ker v) : ℝ) ≤ P.θ * S.size
  /-- The dominant orbit: `|Φ| > q/2`. -/
  dominant : L.q < 2 * H.Φ.card

end Halving

/-- **One item of the aggregation**: what `AuxiliaryReduction` produces for one choice of
target images.
* `none`: the choice is inconsistent ("**if** `|C_X| ≠ |C_Y|` **then return** the empty
  list"; "**skip** this choice if side sizes differ");
* `overcoset σ E₀`: a full-`Γ` overcoset with no recursive call (a balanced colored partition);
* `query Qs E₀`: at most two recursive queries (the configuration call, or the rectangle
  call with its parity twist), whose nonempty answers give overcosets `rep h · E₀`;
* `halving H`: the large-symmetry branch of Lemma A.11.

The parent isomorphisms an item is responsible for are not part of the item: they are the
isomorphisms between the two canonical structures of its branch (`Aggregation.isoSet`), and
`AuxItem.Valid B` states what the item does for a given such set `B`. -/
inductive AuxItem (P : Params) {Ω C : Type} (S : State Ω C) (L : GiantLabels S) : Type 1
  | none
  | overcoset (σ : alternatingGroup (Fin L.q)) (E₀ : Subgroup (alternatingGroup (Fin L.q)))
  | query (Qs : List (AuxQuery P S L)) (E₀ : Subgroup (alternatingGroup (Fin L.q)))
  | halving (H : Halving S L)

namespace AuxItem

variable {P : Params} {S : State Ω C} {L : GiantLabels S}

/-- The lifted overcoset `(τ, π⁻¹(E₀))` with `π(τ) = σ`. -/
noncomputable def liftOver (L : GiantLabels S) (E₀ : Subgroup (alternatingGroup (Fin L.q)))
    (σ : alternatingGroup (Fin L.q)) : Perm Ω × Subgroup (Perm Ω) :=
  (L.rep σ, L.lift E₀)

/-- The script of one item, by the paper's procedure. -/
noncomputable def script : AuxItem P S L → Script (Branches Ω)
  | none => Script.done ⟨[], []⟩
  | overcoset σ E₀ => Script.done ⟨[], [liftOver L E₀ σ]⟩
  | query Qs E₀ => (Script.seqList (Qs.map AuxQuery.script)).bind fun l =>
      Script.done ⟨[], l.reduceOption.map (liftOver L E₀)⟩
  | halving H => H.script

/-- **The facts each item satisfies**, for the set `B` of parent isomorphisms of its branch.
* `none`: no parent isomorphism lies in the branch;
* `overcoset σ E₀`: the cap `aw(E₀) ≤ βq`, and every parent isomorphism of the branch has its
  label image in `σ E₀`;
* `query Qs E₀`: the cap, at most two calls of the charged types, soundness (every
  representative `σ` read off an answer gives a coset `σ E₀` containing the label image of every
  parent isomorphism of the branch) and completeness (if the branch has a parent isomorphism,
  some query yields a representative);
* `halving H`: the facts of Lemma A.11, and every parent isomorphism of the branch lies in
  `τ₀ H`. -/
def Valid (B : Set (Perm Ω)) : AuxItem P S L → Prop
  | none => S.answer ∩ B = ∅
  | overcoset σ E₀ => GI.SectionCaps.Cap E₀ ⌊P.β * L.q⌋₊ ∧
      ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G, σ⁻¹ * L.π ⟨g, hg⟩ ∈ E₀
  | query Qs E₀ => GI.SectionCaps.Cap E₀ ⌊P.β * L.q⌋₊ ∧ Qs.length ≤ 2 ∧
      (∀ Q ∈ Qs, AggCall P S Q.mode Q.T) ∧
      (∀ Q ∈ Qs, ∀ σ, Q.read Q.T.answer = some σ → ∀ g ∈ S.answer ∩ B,
        ∃ hg : g ∈ S.G, σ⁻¹ * L.π ⟨g, hg⟩ ∈ E₀) ∧
      ((S.answer ∩ B).Nonempty → ∃ Q ∈ Qs, ∃ σ, Q.read Q.T.answer = some σ)
  | halving H => H.Valid P ∧ ∀ g ∈ S.answer ∩ B, g ∈ H.τ₀ • (H.big : Set (Perm Ω))

/-! #### The facts of one item -/

theorem evalExact_query (Qs : List (AuxQuery P S L)) (E₀ : Subgroup (alternatingGroup (Fin L.q))) :
    (query Qs E₀).script.evalExact =
      ⟨[], (Qs.map fun Q => Q.read Q.T.answer).reduceOption.map (liftOver L E₀)⟩ := by
  simp only [script, Script.evalExact_bind, Script.evalExact_seqList, List.map_map]
  rfl

theorem evalExact_halving (H : Halving S L) : (halving H : AuxItem P S L).script.evalExact =
    ⟨[H.piece H.τ₀ (H.kerState S.x).answer (H.kerState (S.y ∘ H.τ₀)).answer,
      H.piece (H.τ₀ * H.t) (H.kerState S.x).answer
        (H.kerState (S.y ∘ (H.τ₀ * H.t))).answer], []⟩ := rfl

variable {B : Set (Perm Ω)}

/-- Every fresh `Solve` call of an item is asked on a finite set of positions. -/
theorem solve_finite (I : AuxItem P S L) :
    I.script.CallsExact fun {Ω' _} m _ => m = .solve → Finite Ω' := by
  cases I with
  | none => trivial
  | overcoset => trivial
  | query Qs E₀ =>
    refine Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => ?_) trivial
    obtain ⟨Q, -, rfl⟩ := List.mem_map.1 hs
    exact ⟨Q.solve_fin, trivial⟩
  | halving H =>
    show H.script.CallsExact _
    simp [Halving.script, Script.CallsExact]

/-- Every call of an item is an aggregation call. -/
theorem calls (I : AuxItem P S L) (hI : I.Valid B) : I.script.CallsExact (AggCall P S) := by
  cases I with
  | none => trivial
  | overcoset => trivial
  | query Qs E₀ =>
    obtain ⟨-, -, hc, -, -⟩ := hI
    refine Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => ?_) trivial
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hs
    exact ⟨hc Q hQ, trivial⟩
  | halving H =>
    have hch : ∀ z : Ω → C, AggCall P S .cont (H.kerState z) := fun z =>
      Or.inr ⟨rfl, rfl, show ChargedCall P S (H.kerState z) from
        ⟨by simp, by simpa using H.ker_le, by simp, by simp, fun v hv => Or.inl (by
          simp only [Halving.kerState_G]; exact hI.1.orb_small v (by simpa using hv))⟩⟩
    exact ⟨hch _, hch _, hch _, trivial⟩

/-- An item makes at most three `Continue` calls. -/
theorem numCont_le (I : AuxItem P S L) (hI : I.Valid B) : I.script.numCont ≤ 3 := by
  cases I with
  | none => simp [script, Script.numCont]
  | overcoset => simp [script, Script.numCont]
  | query Qs E₀ =>
    obtain ⟨-, hlen, -, -, -⟩ := hI
    simp only [script, Script.numCont_bind, Script.numCont_seqList, List.map_map]
    have : ((Qs.map (Script.numCont ∘ AuxQuery.script)).sum) ≤ Qs.length := by
      have h := List.sum_le_card_nsmul (Qs.map (Script.numCont ∘ AuxQuery.script)) 1
        (fun x hx => by
          obtain ⟨Q, -, rfl⟩ := List.mem_map.1 hx
          simp only [Function.comp, AuxQuery.script, Script.numCont]
          split_ifs <;> simp)
      simpa using h
    simp only [Script.numCont]
    omega
  | halving H =>
    simp only [script, Halving.script, Script.numCont]
    simp

/-- An item returns at most two overcosets. -/
theorem overs_length_le (I : AuxItem P S L) (hI : I.Valid B) :
    I.script.evalExact.overs.length ≤ 2 := by
  cases I with
  | none => simp [script, Script.evalExact]
  | overcoset => simp [script, Script.evalExact]
  | query Qs E₀ =>
    obtain ⟨-, hlen, -, -, -⟩ := hI
    rw [evalExact_query]
    simp only [List.length_map]
    exact (List.reduceOption_length_le _).trans (by simpa using hlen)
  | halving H => simp [evalExact_halving]

/-- Every overcoset of an item is a lift `(τ, π⁻¹(E₀))` with `aw(E₀) ≤ βq`. -/
theorem overs_spec (I : AuxItem P S L) (hI : I.Valid B) :
    ∀ o ∈ I.script.evalExact.overs, ∃ (σ : alternatingGroup (Fin L.q))
      (E₀ : Subgroup (alternatingGroup (Fin L.q))), GI.SectionCaps.Cap E₀ ⌊P.β * L.q⌋₊ ∧
      o = liftOver L E₀ σ := by
  cases I with
  | none => simp [script, Script.evalExact]
  | overcoset σ E₀ =>
    intro o ho
    simp only [script, Script.evalExact, List.mem_singleton] at ho
    exact ⟨σ, E₀, hI.1, ho⟩
  | query Qs E₀ =>
    intro o ho
    rw [evalExact_query] at ho
    obtain ⟨σ, -, rfl⟩ := List.mem_map.1 ho
    exact ⟨σ, E₀, hI.1, rfl⟩
  | halving H => simp [evalExact_halving]

/-- Every exact piece consists of parent isomorphisms. -/
theorem pieces_sub (I : AuxItem P S L) (hI : I.Valid B) :
    ∀ p ∈ I.script.evalExact.pieces, p ⊆ S.answer := by
  cases I with
  | none => simp [script, Script.evalExact]
  | overcoset => simp [script, Script.evalExact]
  | query Qs E₀ => rw [evalExact_query]; simp
  | halving H =>
    replace hI := hI.1
    rw [evalExact_halving]
    simp only [Halving.kerState_answer]
    -- A piece is `ρ b · Aut_K(x) · A` with `b ∈ Iso_K(x, y ∘ ρ)`.
    have key : ∀ ρ : Perm Ω, ρ ∈ S.G → ∀ z : Ω → C, z = S.y ∘ ρ →
        H.piece ρ (GI.Algorithm.answer H.ker S.dom S.x S.x)
          (GI.Algorithm.answer H.ker S.dom S.x z) ⊆ S.answer := by
      intro ρ hρ z hz g hg
      unfold Halving.piece at hg
      split_ifs at hg with hB
      · obtain ⟨_, ⟨k, hk, a, ha, rfl⟩, rfl⟩ := hg
        have hb := hB.some_mem
        set b := hB.some
        obtain ⟨hbK, hbx⟩ := hb
        obtain ⟨hkK, hkx⟩ := hk
        have hbG := H.ker_le hbK
        have hkG := H.ker_le hkK
        have haG : a ∈ S.G := (L.lift_le _) (hI.A_le ha)
        refine ⟨?_, fun v hv => ?_⟩
        · exact S.G.mul_mem (S.G.mul_mem hρ hbG) (S.G.mul_mem hkG haG)
        · have hav : a v ∈ S.dom := (S.dom_inv a haG v).2 hv
          have hkav : k (a v) ∈ S.dom := (S.dom_inv k hkG _).2 hav
          have h1 := hbx (k (a v)) hkav
          have h2 := hkx (a v) hav
          have h3 := hI.A_aut a ha v hv
          change S.y ((ρ * b * (k * a)) v) = S.x v
          simp only [Perm.mul_apply]
          change z (b (k (a v))) = S.x (k (a v)) at h1
          rw [hz] at h1
          change S.x (k (a v)) = S.x (a v) at h2
          simp only [Function.comp_apply] at h1
          rw [h1, h2, h3]
      · exact absurd hg (Set.notMem_empty g)
    have hτ₀ := hI.τ₀_mem
    have hρ₂ : H.τ₀ * H.t ∈ S.G := S.G.mul_mem hτ₀ ((L.lift_le _) hI.t_mem)
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact key _ hτ₀ _ rfl
    · exact key _ hρ₂ _ rfl

/-- **The item covers its branch**: every parent isomorphism of the branch lies in an exact
piece or in a lifted overcoset of the item. -/
theorem cover (I : AuxItem P S L) (hI : I.Valid B) :
    S.answer ∩ B ⊆ (⋃ p ∈ I.script.evalExact.pieces, p) ∪
      ⋃ o ∈ I.script.evalExact.overs, o.1 • (o.2 : Set (Perm Ω)) := by
  intro g ⟨hg, hgb⟩
  cases I with
  | none =>
    have : g ∈ S.answer ∩ B := ⟨hg, hgb⟩
    rw [show S.answer ∩ B = ∅ from hI] at this
    exact absurd this (Set.notMem_empty g)
  | overcoset σ E₀ =>
    right
    simp only [script, Script.evalExact, List.mem_singleton, Set.mem_iUnion, exists_prop,
      exists_eq_left]
    exact L.overSet_subset σ E₀ (hI.2 g ⟨hg, hgb⟩)
  | query Qs E₀ =>
    obtain ⟨-, -, -, hsound, hcomp⟩ := hI
    right
    rw [evalExact_query]
    obtain ⟨Q, hQ, σ, hσ⟩ := hcomp ⟨g, hg, hgb⟩
    have hmem : σ ∈ (Qs.map fun Q => Q.read Q.T.answer).reduceOption := by
      rw [List.reduceOption_mem_iff]
      exact List.mem_map.2 ⟨Q, hQ, hσ⟩
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨_, List.mem_map.2 ⟨_, hmem, rfl⟩, ?_⟩
    obtain ⟨hgG, hE⟩ := hsound Q hQ σ hσ g ⟨hg, hgb⟩
    exact L.overSet_subset _ E₀ ⟨hgG, hE⟩
  | halving H =>
    have hgb' := hI.2 g ⟨hg, hgb⟩
    replace hI := hI.1
    left
    rw [evalExact_halving]
    simp only [Halving.kerState_answer]
    obtain ⟨h, hhH, rfl⟩ := hgb'
    -- the part `h ∈ H₀`, or `t⁻¹ h ∈ H₀`
    have key : ∀ ρ : Perm Ω, ρ ∈ S.G → ∀ h' ∈ H.even, ρ * h' ∈ S.answer →
        ρ * h' ∈ H.piece ρ (GI.Algorithm.answer H.ker S.dom S.x S.x)
          (GI.Algorithm.answer H.ker S.dom S.x (S.y ∘ ρ)) := by
      intro ρ hρ h' hh' hans
      obtain ⟨a, ha, hka⟩ := hI.onto h' hh'
      have haG : a ∈ S.G := (L.lift_le _) (hI.A_le ha)
      have hdom : ∀ v ∈ S.dom, a⁻¹ v ∈ S.dom := fun v hv => S.dom_inv.inv_mem haG hv
      -- `k = h' a⁻¹ ∈ K` is a `K`-transporter from `x` to `y ∘ ρ`.
      have hk : h' * a⁻¹ ∈ GI.Algorithm.answer H.ker S.dom S.x (S.y ∘ ρ) := by
        refine ⟨hka, fun v hv => ?_⟩
        have h1 := hans.2 (a⁻¹ v) (hdom v hv)
        have h2 := hI.A_aut a ha (a⁻¹ v) (hdom v hv)
        rw [Perm.apply_inv_self] at h2
        change S.y (ρ (h' (a⁻¹ v))) = S.x v
        change S.y ((ρ * h') (a⁻¹ v)) = S.x (a⁻¹ v) at h1
        rw [h2]
        exact h1
      have hB : (GI.Algorithm.answer H.ker S.dom S.x (S.y ∘ ρ)).Nonempty := ⟨_, hk⟩
      unfold Halving.piece
      rw [dif_pos hB]
      set b := hB.some
      obtain ⟨hbK, hbx⟩ := hB.some_mem
      -- `b⁻¹ k ∈ Aut_K(x)`.
      have hbk : b⁻¹ * (h' * a⁻¹) ∈ GI.Algorithm.answer H.ker S.dom S.x S.x := by
        refine ⟨H.ker.mul_mem (H.ker.inv_mem hbK) hka, fun v hv => ?_⟩
        have hbG := H.ker_le hbK
        have hkG : h' * a⁻¹ ∈ S.G := H.ker_le hka
        have hkv : (h' * a⁻¹) v ∈ S.dom := (S.dom_inv _ hkG v).2 hv
        have hw : b⁻¹ ((h' * a⁻¹) v) ∈ S.dom := S.dom_inv.inv_mem hbG hkv
        have e1 := hbx _ hw
        rw [Perm.apply_inv_self] at e1
        have e2 := hk.2 v hv
        change S.x (b⁻¹ ((h' * a⁻¹) v)) = S.x v
        change S.y (ρ ((h' * a⁻¹) v)) = S.x (b⁻¹ ((h' * a⁻¹) v)) at e1
        change S.y (ρ ((h' * a⁻¹) v)) = S.x v at e2
        rw [← e1, e2]
      refine ⟨b⁻¹ * (h' * a⁻¹) * a, ⟨_, hbk, a, ha, rfl⟩, ?_⟩
      simp only [smul_eq_mul]
      group
    have hτ₀ := hI.τ₀_mem
    have htG : H.t ∈ S.G := (L.lift_le _) hI.t_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_iUnion, exists_prop]
    rcases hI.split h hhH with he | he
    · exact ⟨_, Or.inl rfl, key _ hτ₀ h he hg⟩
    · refine ⟨_, Or.inr rfl, ?_⟩
      have e : H.τ₀ • h = (H.τ₀ * H.t) * (H.t⁻¹ * h) := by
        rw [smul_eq_mul]; group
      change H.τ₀ • h ∈ S.answer at hg
      change H.τ₀ • h ∈ _
      rw [e] at hg ⊢
      exact key _ (S.G.mul_mem hτ₀ htG) _ he hg

end AuxItem

/-! ### The canonical structures of a round and their isomorphisms -/

section Structures

variable (fin : Finite Ω) (S : State Ω C) (L : GiantLabels S)
  (πd : S.domGroup →* alternatingGroup (Fin L.q)) (hK : JointFn)
  (κ : ℕ) (nm : ClassNum S κ L.q)

/-- **The numbering of the comparison classes separates the classes** of the source string
`S.x` (`NumOK`, with the instances of `structX`). -/
def ClassNum.OK : Prop :=
  haveI := fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  NumOK S πd κ nm (dstr S S.x) (dstr S S.y)

/-- **The default numbering of the comparison classes**: the index in the common palette. -/
noncomputable def ClassNum.default : ClassNum S κ L.q :=
  haveI := fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  palNum S πd κ (dstr S S.x) (dstr S S.y)

theorem ClassNum.default_ok : ClassNum.OK fin S L πd κ (ClassNum.default fin S L πd κ) :=
  haveI := fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  palNum_ok S πd κ _ _

/-- **The canonical structure of `S.x`** with the individualized tuple `t`
(`GI.Algorithm.canon`, `Workspace/Algorithm/AggregationCanon.lean`): the ideal image of the
certificate group, the refined comparison colors of `κ`-tuples under the class numbering `nm`
(refined jointly with those of `S.y`), and `t`. -/
noncomputable def structX {ℓ : ℕ} (t : Fin ℓ → Fin L.q) : Canon L.q κ ℓ :=
  haveI := fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  canon S πd κ hK nm (dstr S S.x) (dstr S S.y) t

/-- **The canonical structure of `S.y`** with the individualized tuple `t`: the second side of
the joint refinement (`GI.Algorithm.canon'`). -/
noncomputable def structY {ℓ : ℕ} (t : Fin ℓ → Fin L.q) : Canon L.q κ ℓ :=
  haveI := fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  canon' S πd κ hK nm (dstr S S.x) (dstr S S.y) t

/-- The parent isomorphisms of a branch: the elements of `G` whose label permutation maps the
structure of `(x, src)` to the structure of `(y, b)`. -/
def isoSetOf {ℓ : ℕ} (src b : Fin ℓ → Fin L.q) : Set (Perm Ω) :=
  {g | ∃ hg : g ∈ S.G, (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • structX fin S L πd hK κ nm src =
    structY fin S L πd hK κ nm b}

/-- **Every parent isomorphism lies in the branch of its own target tuple** (Section A.3: "Every
genuine parent isomorphism … carries the chosen source orbital to one of the enumerated target
orbitals"), from the equivariance of the canonical structure (`canon_equivariant`), when `π_d`
agrees with `π`. -/
theorem mem_isoSetOf (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) {ℓ : ℕ}
    (src : Fin ℓ → Fin L.q) {g : Perm Ω} (hg : g ∈ S.answer) :
    g ∈ isoSetOf fin S L πd hK κ nm src ((L.π ⟨g, hg.1⟩ : Perm (Fin L.q)) ∘ src) := by
  haveI := fin
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : DecidableEq S.dom := Classical.decEq _
  exact ⟨hg.1, canon_equivariant L πd hπ hK nm src hg⟩

end Structures

end GI.Algorithm
