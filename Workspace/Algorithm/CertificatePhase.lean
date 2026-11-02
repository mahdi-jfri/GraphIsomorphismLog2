import Workspace.Algorithm.Certificates

/-!
# The certificate phase of an aggregation round

Section 4.1: "Aggregate the full certificates, and use the comparison classes of the nonfull
certificates as tuple colors." Before it aggregates, the round computes the local certificate of
every test set `T` of size `κ`, for both strings (Algorithm 2, `LocalCertificate`). Lemma 4.1:
"all test certificates … can be computed with polynomial structural work and polynomially many
inherited recursive calls" of the two charged types.

`certPhase` is this phase as a query script: for every `κ`-subset `T` of the labels it runs the
lifted endpoint script of Algorithm 2 (`endpointScriptLift`, `Workspace/Algorithm/Certificates.lean`)
to its final stage `n = |dom|` for `x` and then for `y`.

* `certPhase_evalExact`: with exact answers it returns the final stages of the endpoint
  procedure, which are what the canonical structure of the round is built from
  (`Workspace/Algorithm/AggregationCanon.lean`).
* `certPhase_calls`: every call is a charged call of the round (Lemma 4.1, clause 2, through
  `endpointScriptLift_bind_calls`).
* `certPhase_numCont_le`: it makes at most `2 binom(q, κ) n κ!` `Continue` calls: each of the at
  most `n` updates enumerates the cosets of `ker(φ_T|_A)` in `A`, at most `|Alt(T)| ≤ κ!` of them
  (Section 4: "It enumerates the constantly many cosets of `ker(φ_T|_A)` in `A`"; eq.
  `constant-recurrence`: "The multiplicity absorbs the at most `n` updates, orbit calls, `k!`
  cosets, and all test tuples").

The ordered comparisons (lockstep scripts) are not part of this script; the comparison classes
enter the round through their mathematical definition (`GI.LocalCertificates.CompareRel`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Endpoint GI.LocalGroups
open scoped Pointwise

/-! ### Counting the calls of one endpoint script -/

section Count

variable {V : Type} {Q : Type} [Group Q]

omit [Group Q] in
theorem cosetReps_length [Fintype V] (A N : Subgroup (Perm V)) :
    (cosetReps A N).length = Nat.card (A ⧸ N.subgroupOf A) := by
  classical
  unfold cosetReps
  simp only [List.length_map, Finset.length_toList, Finset.card_univ]
  exact (@Nat.card_eq_fintype_card _ (Fintype.ofFinite _)).symm

/-- The number of cosets of `ker(φ|_A)` in `A` is at most `|Q|`. -/
theorem kernelIn_index_le [Finite Q] {P : Subgroup (Perm V)} (phi : P →* Q)
    {A : Subgroup (Perm V)} (hA : A ≤ P) :
    Nat.card (A ⧸ (kernelIn phi A).subgroupOf A) ≤ Nat.card Q := by
  let f : A →* Q := phi.comp (Subgroup.inclusion hA)
  have hker : f.ker = (kernelIn phi A).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_kernelIn]
    exact ⟨fun h => ⟨a.2, hA a.2, h⟩, fun ⟨_, _, h⟩ => h⟩
  rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  exact Subgroup.card_le_card_group _

/-- **The default coset representatives**: `Quotient.out` of every coset, in the order of
`Finset.univ.toList`. -/
noncomputable def CosetRepFn.default (V : Type) [Fintype V] : CosetRepFn V where
  reps := cosetReps
  mem := cosetReps_mem
  cover := cosetReps_cover
  length_le A N := (cosetReps_length A N).le

variable [DecidableEq V]

/-- `CheckNewWindow` makes one `Continue` call per coset representative. -/
theorem numCont_checkNewWindowLift {Ω C C₀ : Type} [DecidableEq Ω] (S : State Ω C)
    [Fintype S.dom] (R : CosetRepFn S.dom) (A N : Subgroup (Perm S.dom)) (W : Finset S.dom)
    (x : S.dom → C₀) :
    (checkNewWindowLift S R A N W x).numCont ≤ (R.reps A N).length := by
  classical
  unfold checkNewWindowLift
  split_ifs with hW
  · rw [Script.numCont_bind, Script.numCont_seqList]
    simp only [Script.numCont, add_zero, List.map_map]
    have : ∀ s ∈ (R.reps A N).map ((Script.numCont ∘ fun τ : Perm S.dom =>
        (Script.call .cont (windowCall S N W hW x τ)).bind
          fun B => Script.done (τ • restrictAns S B))), s ≤ 1 := by
      intro s hs
      obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hs
      simp [Script.call, Script.bind, Script.numCont]
    have h := List.sum_le_card_nsmul _ 1 this
    simpa using h
  · simp [Script.numCont]

/-- **The calls of one endpoint script**: at most `t |Q|` `Continue` calls in `t` rounds. -/
theorem numCont_endpointScriptLift {Ω C C₀ : Type} [DecidableEq Ω] (S : State Ω C)
    [Fintype S.dom] [Finite Q] (R : CosetRepFn S.dom) {P' : Subgroup (Perm S.dom)}
    (phi : P' →* Q) (hP : P' ≤ S.domGroup) (x : S.dom → C₀) (t : ℕ) :
    (endpointScriptLift S R phi x t).numCont ≤ t * Nat.card Q := by
  classical
  induction t with
  | zero => simp [endpointScriptLift, Script.numCont]
  | succ t ih =>
    rw [endpointScriptLift, Script.numCont_bind, endpointScriptLift_evalExact S R phi hP]
    have hstep : (if increment phi (stage phi x t).1 (stage phi x t).2 = ∅ then
        Script.done (stage phi x t) else
        (checkNewWindowLift S R (stage phi x t).1 (kernelIn phi (stage phi x t).1)
          (increment phi (stage phi x t).1 (stage phi x t).2) x).bind
          fun B => Script.done (Subgroup.closure B, (stage phi x t).2 ∪
            increment phi (stage phi x t).1 (stage phi x t).2)).numCont ≤ Nat.card Q := by
      split_ifs
      · simp [Script.numCont]
      · rw [Script.numCont_bind]
        simp only [Script.numCont, add_zero]
        refine (numCont_checkNewWindowLift S R _ _ _ x).trans ?_
        exact (R.length_le _ _).trans (kernelIn_index_le phi (grp_le phi x t))
    have := Nat.add_le_add ih hstep
    rw [Nat.succ_mul]
    convert this using 2

end Count

/-! ### The certificate phase -/

section Phase

variable {Ω C : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom] {q : ℕ}
  (πd : S.domGroup →* alternatingGroup (Fin q)) (κ : ℕ)

/-- **An order of the test sets**: every `κ`-subset of the labels exactly once. The paper takes
all test sets and fixes no order, so the order of the calls is a parameter of the round
(`TestSetOrder.default` is `Finset.toList`). -/
structure TestSetOrder (q κ : ℕ) where
  sets : List (Finset (Fin q))
  nodup : sets.Nodup
  mem : ∀ T, T ∈ sets ↔ T.card = κ

/-- The test sets in the order of `Finset.toList`. -/
noncomputable def testSets : List (Finset (Fin q)) :=
  (Finset.univ.filter fun T : Finset (Fin q) => T.card = κ).toList

theorem mem_testSets {T : Finset (Fin q)} : T ∈ testSets (q := q) κ ↔ T.card = κ := by
  simp [testSets]

/-- The default order of the test sets. -/
noncomputable def TestSetOrder.default (q κ : ℕ) : TestSetOrder q κ :=
  ⟨testSets (q := q) κ, Finset.nodup_toList _, fun _ => mem_testSets κ⟩

/-- Every order lists `binom(q, κ)` test sets. -/
theorem TestSetOrder.length_eq (O : TestSetOrder q κ) : O.sets.length = q.choose κ := by
  have h1 : O.sets.toFinset = Finset.powersetCard κ Finset.univ := by
    ext T; simp [O.mem, Finset.mem_powersetCard]
  rw [← List.toFinset_card_of_nodup O.nodup, h1, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin]

/-- The final stages of the endpoint procedures of `x` and `y` for one test set. -/
abbrev StagePair (S : State Ω C) : Type :=
  (Subgroup (Perm S.dom) × Finset S.dom) × (Subgroup (Perm S.dom) × Finset S.dom)

variable (O : TestSetOrder q κ) (R : CosetRepFn S.dom)

/-- **The certificate phase**: for each test set `T`, in the order `O`, the local certificate of
`x` and then of `y` (Algorithm 2 with lifted calls and the coset representatives `R`, run to the
final stage `n = |dom|`). -/
noncomputable def certPhase (x y : S.dom → C) : Script (List (StagePair S)) :=
  Script.seqList (O.sets.map fun T =>
    (endpointScriptLift S R (phiT S.domGroup πd T) x (Fintype.card S.dom)).bind fun a =>
      (endpointScriptLift S R (phiT S.domGroup πd T) y (Fintype.card S.dom)).bind fun b =>
        Script.done (a, b))

/-- **With exact answers, the phase computes the final stages** of the endpoint procedure
(`finalGrp`, `finalWin`) for every test set and both strings. -/
theorem certPhase_evalExact (x y : S.dom → C) :
    (certPhase S πd κ O R x y).evalExact = O.sets.map fun T =>
      (stage (phiT S.domGroup πd T) x (Fintype.card S.dom),
        stage (phiT S.domGroup πd T) y (Fintype.card S.dom)) := by
  unfold certPhase
  rw [Script.evalExact_seqList, List.map_map]
  refine List.map_congr_left fun T _ => ?_
  simp only [Function.comp, Script.evalExact_bind, Script.evalExact,
    endpointScriptLift_evalExact S R _ Pgrp_le]

/-- **Every call of the certificate phase is a charged call** of the aggregation round (Lemma 4.1,
clause 2, `endpointScriptLift_bind_calls`). -/
theorem certPhase_calls [Finite Ω] {P : Params} (htr : S.Transitive) (hκ : P.κ = κ)
    (hk5 : 5 ≤ κ) (hθ : 1 ≤ P.θ * κ) (x y : S.dom → C) :
    (certPhase S πd κ O R x y).CallsExact (AggCall P S) := by
  unfold certPhase
  refine Script.callsExact_seqList _ fun s hs => ?_
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hs
  have hTc : T.card = κ := (O.mem T).1 hT
  refine endpointScriptLift_bind_calls htr πd T (hTc ▸ hk5) (hTc ▸ hκ) (hTc ▸ hθ) R x _ _ ?_
  exact endpointScriptLift_bind_calls htr πd T (hTc ▸ hk5) (hTc ▸ hκ) (hTc ▸ hθ) R y _ _ trivial

/-- **The number of calls of the certificate phase**: at most `2 binom(q, κ) n κ!`. -/
theorem certPhase_numCont_le (x y : S.dom → C) :
    (certPhase S πd κ O R x y).numCont ≤
      2 * q.choose κ * Fintype.card S.dom * κ.factorial := by
  unfold certPhase
  rw [Script.numCont_seqList, List.map_map]
  have hone : ∀ T : Finset (Fin q), T.card = κ →
      (Script.numCont ∘ fun T : Finset (Fin q) =>
        (endpointScriptLift S R (phiT S.domGroup πd T) x (Fintype.card S.dom)).bind fun a =>
          (endpointScriptLift S R (phiT S.domGroup πd T) y (Fintype.card S.dom)).bind fun b =>
            Script.done (a, b)) T ≤ 2 * Fintype.card S.dom * κ.factorial := by
    intro T hT
    have hQ : Nat.card (alternatingGroup T) ≤ κ.factorial := by
      calc Nat.card (alternatingGroup T) ≤ Nat.card (Perm T) :=
            Nat.card_le_card_of_injective _ Subtype.val_injective
        _ = κ.factorial := by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe, hT]
    simp only [Function.comp, Script.numCont_bind, Script.numCont, add_zero]
    have h1 := numCont_endpointScriptLift S R (phiT S.domGroup πd T) Pgrp_le x
      (Fintype.card S.dom)
    have h2 := numCont_endpointScriptLift S R (phiT S.domGroup πd T) Pgrp_le y
      (Fintype.card S.dom)
    have h3 := Nat.mul_le_mul_left (Fintype.card S.dom) hQ
    nlinarith
  have h := List.sum_le_card_nsmul _ (2 * Fintype.card S.dom * κ.factorial) (by
    intro s hs
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hs
    exact hone T ((O.mem T).1 hT))
  rw [List.length_map, O.length_eq, smul_eq_mul] at h
  calc _ ≤ _ := h
    _ = _ := by ring

end Phase

end GI.Algorithm
