import Workspace.Algorithm.CertificatePhase

/-!
# The comparison phase of an aggregation round

Section 4.1: "use the comparison classes of the nonfull certificates as tuple colors". The
comparison classes are the classes of the relation `GI.LocalCertificates.CompareRel`: two
ordered test tuples `(z, t)` and `(z', t')` are related when the ordered comparison set of
eq. `comparison` is nonempty. Section 4 says how this set is computed: "For ordered
comparisons, run two copies in lockstep under the full ordered-tuple transporter, maintaining
the complete comparison coset after each new window. Each update uses the same inherited
kernel-orbit queries. A mismatch or empty coset ends that comparison."

This file writes these lockstep runs as query scripts and adds them to the round.

* `compareCall`, `lockstepStepLift`: one lockstep update, with the call lifted to the positions
  of the state (the way `windowCall` lifts the calls of `CheckNewWindow`). It is the lifted form
  of `lockstepStep` (`Workspace/Algorithm/Certificates.lean`).
* `lockstepStepLift_evalExact`: with an exact answer, one update maps a member of the stage-`j`
  coset to the stage-`j+1` coset (`GI.Paper.lockstep_comparison`).
* `compareLoop`, `compareLoop_evalExact`: `n = |dom|` updates, keeping one representative of
  the current coset, or none once the coset is empty. The run ends with a representative of the
  final comparison set if and only if that set is nonempty; an empty coset stays empty, since
  every later coset lies in it (`GI.Paper.comparison_cannot_revive`).
* `compareScript_evalExact`: the comparison script returns `true` exactly when `CompareRel`
  holds.
* `comparePhase`: the comparisons of all pairs of injective `κ`-tuples of the two strings;
  `comparePhase_evalExact`, `comparePhase_calls` (every call is a charged call, Lemma 4.1,
  clause 2), `comparePhase_numCont_le` (at most `(2 q^κ)^2 n` calls: polynomially many, as
  Lemma 4.1 says).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Endpoint GI.LocalGroups GI.LocalCertificates
open scoped Pointwise

/-! ### One lifted lockstep update -/

section Lifted

variable {Ω C C₀ : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom]

/-- **The lifted call of a lockstep update**: `Continue` under the lift of `N` on the lifted
window `V`, for the colorings `(x, y ∘ g₀)` of the domain, extended off the domain by one extra
color (no lift of `g₀` to `G` is chosen). It clears the bookkeeping (`State.queryChild`), as a
certificate child. -/
noncomputable def compareCall (N : Subgroup (Perm S.dom)) (V : Finset S.dom)
    (hV : GI.Algorithm.Invariant N (V : Set S.dom)) (x y : S.dom → C₀) (g₀ : Perm S.dom) :
    State Ω (Option C₀) :=
  S.queryChild (S.liftGroup N) (Subtype.val '' (V : Set S.dom)) (lifted_invariant S hV)
    (liftColor S x) (liftColor S (y ∘ g₀))

/-- The restricted answer of the lifted call is the answer of the call on the domain. -/
theorem compareCall_answer {N : Subgroup (Perm S.dom)} (hN : N ≤ S.domGroup)
    {V : Finset S.dom} (hV : GI.Algorithm.Invariant N (V : Set S.dom)) (x y : S.dom → C₀)
    {g₀ : Perm S.dom} (hg₀ : g₀ ∈ S.domGroup) :
    restrictAns S (compareCall S N V hV x y g₀).answer =
      GI.Algorithm.answer N (V : Set S.dom) x (y ∘ g₀) := by
  have key : ∀ (g : Perm Ω) (hg : g ∈ S.G) (v : S.dom),
      liftColor S (y ∘ g₀) (g v) = some (y (g₀ (S.domHom ⟨g, hg⟩ v))) := by
    intro g hg v
    have h1 : g v = (S.domHom ⟨g, hg⟩ v : Ω) := rfl
    rw [h1, liftColor_mem]
    rfl
  ext p
  simp only [restrictAns, compareCall, State.queryChild_answer, GI.Algorithm.answer,
    Set.mem_setOf_eq, Function.comp_apply]
  constructor
  · rintro ⟨g, hg, ⟨hgL, hcol⟩, rfl⟩
    obtain ⟨_, hgN⟩ := State.mem_liftGroup.1 hgL
    refine ⟨hgN, fun v hv => ?_⟩
    have := hcol v ⟨v, hv, rfl⟩
    rw [key g hg v, liftColor_mem] at this
    exact Option.some_injective _ this
  · rintro ⟨hpN, hcol⟩
    obtain ⟨⟨g, hg⟩, rfl⟩ := hN hpN
    refine ⟨g, hg, ⟨State.mem_liftGroup.2 ⟨hg, hpN⟩, ?_⟩, rfl⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [key g hg v, liftColor_mem]
    exact congrArg some (hcol v hv)

variable {q k : ℕ} (πd : S.domGroup →* alternatingGroup (Fin q))

/-- The stage kernel `N_j = ker(φ_T|_{A_j})` of the endpoint procedure of `(x, T)`,
`T = tset t`. -/
noncomputable abbrev stageKer (x : S.dom → C₀) (t : Fin k → Fin q) (j : ℕ) :
    Subgroup (Perm S.dom) :=
  kernelIn (phiT S.domGroup πd (tset t)) (grp (phiT S.domGroup πd (tset t)) x j)

theorem stageKer_le (x : S.dom → C₀) (t : Fin k → Fin q) (j : ℕ) :
    stageKer S πd x t j ≤ S.domGroup :=
  inf_le_left.trans ((grp_le _ x j).trans Pgrp_le)

theorem stageKer_invariant (x : S.dom → C₀) (t : Fin k → Fin q) (j : ℕ) :
    GI.Algorithm.Invariant (stageKer S πd x t j)
      (inc (phiT S.domGroup πd (tset t)) x j : Set S.dom) :=
  (invariant_coe (inc_invariant (phiT S.domGroup πd (tset t)) x j)).mono inf_le_left

/-- **One lockstep update with a lifted call** (Section 4: "For ordered comparisons, run two
copies in lockstep under the full ordered-tuple transporter, maintaining the complete
comparison coset after each new window"). The current coset is `g₀ N_j`; the update asks
`Continue` under `N_j` on the new window `V_j` of `(x, T)` with the colorings `(x, y ∘ g₀)`,
restricts the answer to the domain and translates it by `g₀`. -/
noncomputable def lockstepStepLift (j : ℕ) (x y : S.dom → C₀) (t : Fin k → Fin q)
    (g₀ : Perm S.dom) : Script (Set (Perm S.dom)) :=
  (Script.call .cont (compareCall S (stageKer S πd x t j)
      (inc (phiT S.domGroup πd (tset t)) x j) (stageKer_invariant S πd x t j) x y g₀)).bind
    fun B => Script.done (g₀ • restrictAns S B)

/-- **The lifted lockstep update is exact** (`GI.Paper.lockstep_comparison`): if `g₀` lies in
the stage-`j` comparison coset and the call is exact, the update returns the stage-`j+1`
coset. -/
theorem lockstepStepLift_evalExact (j : ℕ) (x y : S.dom → C₀) (t t' : Fin k → Fin q)
    {g₀ : Perm S.dom} (hg₀ : g₀ ∈ lockstep S.domGroup πd j x t y t') :
    (lockstepStepLift S πd j x y t g₀).evalExact = lockstep S.domGroup πd (j + 1) x t y t' := by
  classical
  have hg₀G : g₀ ∈ S.domGroup := hg₀.1
  simp only [lockstepStepLift, Script.evalExact_bind, Script.call, Script.evalExact]
  rw [compareCall_answer S (stageKer_le S πd x t j) _ x y hg₀G]
  rw [(GI.Paper.lockstep_comparison S.domGroup πd j x y t t').2]
  have hcoset := lockstep_eq_coset hg₀
  rw [(automorphisms_J_eq (G := S.domGroup) (π := πd) x (tset t) j).1,
    (automorphisms_J_eq (G := S.domGroup) (π := πd) x (tset t) j).2] at hcoset
  ext g
  simp only [Set.mem_smul_set, smul_eq_mul, Set.mem_setOf_eq, GI.Algorithm.answer,
    Function.comp_apply]
  rw [hcoset]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, ⟨hn, hnV⟩, rfl⟩
    exact ⟨⟨n, hn, rfl⟩, fun v hv => by rw [Perm.mul_apply]; exact hnV v hv⟩
  · rintro ⟨⟨n, hn, rfl⟩, hV'⟩
    exact ⟨n, ⟨hn, fun v hv => by have := hV' v hv; rwa [Perm.mul_apply] at this⟩, rfl⟩

/-! ### The lockstep run of one comparison -/

open Classical in
/-- A representative of a set of permutations, if it is nonempty. -/
noncomputable def pickRep {V : Type} (A : Set (Perm V)) : Option (Perm V) :=
  if h : A.Nonempty then some h.some else none

theorem pickRep_mem {V : Type} {A : Set (Perm V)} {g : Perm V} (h : pickRep A = some g) :
    g ∈ A := by
  classical
  unfold pickRep at h
  split_ifs at h with hA
  · cases h; exact hA.some_mem

theorem pickRep_eq_none {V : Type} {A : Set (Perm V)} : pickRep A = none ↔ A = ∅ := by
  classical
  unfold pickRep
  split_ifs with hA
  · simp only [false_iff]
    exact hA.ne_empty
  · simpa [Set.not_nonempty_iff_eq_empty] using hA

/-- **A choice of representatives** of sets of permutations: an element of a nonempty set, and
`none` for the empty set. The lockstep run keeps one representative of each comparison coset;
the paper fixes none, so it is a parameter (`PickFn.default` is `pickRep`). -/
structure PickFn (V : Type) where
  pick : Set (Perm V) → Option (Perm V)
  mem : ∀ {A : Set (Perm V)} {g : Perm V}, pick A = some g → g ∈ A
  eq_none : ∀ {A : Set (Perm V)}, pick A = none ↔ A = ∅

/-- The default representatives, by `Set.Nonempty.some`. -/
noncomputable def PickFn.default (V : Type) : PickFn V :=
  ⟨pickRep, pickRep_mem, pickRep_eq_none⟩

variable (Pk : PickFn S.dom)

/-- **The lockstep run** of the comparison of `(x, t)` and `(y, t')`: `j` updates, keeping one
representative of the current comparison coset, chosen by `Pk` ("A mismatch or empty coset ends
that comparison"). The initial coset, the full ordered-tuple transporter of the empty windows, is
structural work. -/
noncomputable def compareLoop (x y : S.dom → C₀) (t t' : Fin k → Fin q) :
    ℕ → Script (Option (Perm S.dom))
  | 0 => Script.done (Pk.pick (lockstep S.domGroup πd 0 x t y t'))
  | j + 1 => (compareLoop x y t t' j).bind fun o =>
      match o with
      | none => Script.done none
      | some g₀ => (lockstepStepLift S πd j x y t g₀).bind fun B => Script.done (Pk.pick B)

/-- **The lockstep run computes the comparison cosets**: after `j` exact updates it holds a
representative of the stage-`j` coset, or none when that coset is empty. An empty coset stays
empty, because each coset lies in the one before (`GI.Paper.lockstep_comparison`). -/
theorem compareLoop_evalExact (x y : S.dom → C₀) (t t' : Fin k → Fin q) (j : ℕ) :
    (compareLoop S πd Pk x y t t' j).evalExact = Pk.pick (lockstep S.domGroup πd j x t y t') := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [compareLoop, Script.evalExact_bind, ih]
    rcases ho : Pk.pick (lockstep S.domGroup πd j x t y t') with _ | g₀
    · -- the stage-`j` coset is empty, so the stage-`j+1` coset is empty
      have he := Pk.eq_none.1 ho
      show (none : Option (Perm S.dom)) = Pk.pick _
      symm
      rw [Pk.eq_none, (GI.Paper.lockstep_comparison S.domGroup πd j x y t t').2, he]
      ext g
      simp
    · simp only [Script.evalExact_bind, Script.evalExact]
      rw [lockstepStepLift_evalExact S πd j x y t t' (Pk.mem ho)]

/-- **The comparison script** of `(x, t)` and `(y, t')`: the lockstep run to the final windows
`j = n`, returning whether the final comparison set is nonempty. -/
noncomputable def compareScript (x y : S.dom → C₀) (t t' : Fin k → Fin q) : Script Bool :=
  (compareLoop S πd Pk x y t t' (Fintype.card S.dom)).bind fun o => Script.done o.isSome

/-- **The comparison script computes `CompareRel`** (eq. `comparison`; "the comparison relation
is exact", Lemma 4.1). -/
theorem compareScript_evalExact (x y : S.dom → C₀) (t t' : Fin k → Fin q) :
    (compareScript S πd Pk x y t t').evalExact = true ↔
      CompareRel S.domGroup πd k (x, t) (y, t') := by
  rw [compareScript, Script.evalExact_bind, compareLoop_evalExact]
  simp only [Script.evalExact, Option.isSome_iff_ne_none, ne_eq, Pk.eq_none]
  exact Set.nonempty_iff_ne_empty.symm

/-- At most one `Continue` call per update. -/
theorem compareLoop_numCont_le (x y : S.dom → C₀) (t t' : Fin k → Fin q) (j : ℕ) :
    (compareLoop S πd Pk x y t t' j).numCont ≤ j := by
  induction j with
  | zero => simp [compareLoop, Script.numCont]
  | succ j ih =>
    rw [compareLoop, Script.numCont_bind]
    have : ((match (compareLoop S πd Pk x y t t' j).evalExact with
        | none => Script.done none
        | some g₀ => (lockstepStepLift S πd j x y t g₀).bind fun B =>
            Script.done (Pk.pick B)) : Script (Option (Perm S.dom))).numCont ≤ 1 := by
      split
      · simp [Script.numCont]
      · simp [lockstepStepLift, Script.call, Script.bind, Script.numCont]
    omega

theorem compareScript_numCont_le (x y : S.dom → C₀) (t t' : Fin k → Fin q) :
    (compareScript S πd Pk x y t t').numCont ≤ Fintype.card S.dom := by
  rw [compareScript, Script.numCont_bind]
  simp only [Script.numCont, add_zero]
  exact compareLoop_numCont_le S πd Pk x y t t' _

end Lifted

/-! ### The calls are charged calls -/

section Calls

variable {P : Params} {Ω C C₀ : Type} [Finite Ω] [DecidableEq Ω] {S : State Ω C}
  [Fintype S.dom] {q k : ℕ}

/-- **Every call of a lockstep run is a charged call** (Lemma 4.1, clause 2, through
`ChargedCall.of_local_test`): the call of stage `j` runs under the lift of the stage kernel
`N_j` of the endpoint procedure of `(x, T)` on its lifted increment `V_j`, which are the calls
of that endpoint procedure. The test tuple is injective, so `|T| = κ`. -/
theorem compareScript_calls (htr : S.Transitive) (πd : S.domGroup →* alternatingGroup (Fin q))
    (Pk : PickFn S.dom) (hκ : P.κ = k) (hk5 : 5 ≤ k) (hθ : 1 ≤ P.θ * k) (x y : S.dom → C₀)
    (t : Fin k ↪ Fin q) (t' : Fin k → Fin q) :
    (compareScript S πd Pk x y t t').CallsExact (AggCall P S) := by
  have hT : (tset (t : Fin k → Fin q)).card = k := by
    rw [tset, Finset.card_image_of_injective _ t.injective, Finset.card_univ, Fintype.card_fin]
  have loop : ∀ j, (compareLoop S πd Pk x y t t' j).CallsExact (AggCall P S) := by
    intro j
    induction j with
    | zero => trivial
    | succ j ih =>
      refine Script.callsExact_bind _ _ ih ?_
      split
      · trivial
      · refine Script.callsExact_bind _ _ ⟨Or.inr ⟨rfl, rfl, ?_⟩, trivial⟩ trivial
        exact ChargedCall.of_local_test htr πd x (tset (t : Fin k → Fin q)) (by rw [hT]; exact hk5)
          (by rw [hT]; exact hκ) (by rw [hT]; exact hθ) j (State.queryChild_N _ _ _ _ _ _) (State.queryChild_hier _ _ _ _ _ _)
          (by rw [compareCall, State.queryChild_G]) (by rw [compareCall, State.queryChild_dom])
  exact Script.callsExact_bind _ _ (loop _) trivial

end Calls

/-! ### The comparison phase -/

section Phase

variable {Ω C : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom]
  {q : ℕ} (πd : S.domGroup →* alternatingGroup (Fin q)) (κ : ℕ)

/-- The ordered test tuples of one string: a string (`false` for `x`, `true` for `y`) and an
injective `κ`-tuple of labels. -/
abbrev TestTuple (q κ : ℕ) : Type := Bool × (Fin κ ↪ Fin q)

/-- All ordered test tuples of the two strings, in the order of `Finset.toList`. -/
noncomputable def testTuples : List (TestTuple q κ) := Finset.univ.toList

/-- **An order of the ordered test tuples**: every test tuple of the two strings exactly once.
The order of the comparisons is a parameter of the round (`TestTupleOrder.default` is
`testTuples`). -/
structure TestTupleOrder (q κ : ℕ) where
  tuples : List (TestTuple q κ)
  nodup : tuples.Nodup
  mem : ∀ a, a ∈ tuples

/-- The default order of the test tuples. -/
noncomputable def TestTupleOrder.default (q κ : ℕ) : TestTupleOrder q κ :=
  ⟨testTuples (q := q) κ, Finset.nodup_toList _, fun _ => Finset.mem_toList.2 (Finset.mem_univ _)⟩

/-- The string of a test tuple. -/
def strOf (x y : S.dom → C) (b : Bool) : S.dom → C := if b then y else x

variable (O : TestTupleOrder q κ) (Pk : PickFn S.dom)

/-- **The comparison phase**: the lockstep comparison of every pair of ordered test tuples of the
two strings, in the order `O` (Section 4.1: "use the comparison classes of the nonfull
certificates as tuple colors"; Lemma 4.1: "all test certificates and ordered comparisons can be
computed with … polynomially many inherited recursive calls"). -/
noncomputable def comparePhase (x y : S.dom → C) : Script (List Bool) :=
  Script.seqList (O.tuples.flatMap fun a => O.tuples.map fun b =>
    compareScript S πd Pk (strOf S x y a.1) (strOf S x y b.1) a.2 b.2)

/-- **The comparison phase computes the comparison relation**: with exact answers, the entry of
the pair `(a, b)` is `true` exactly when `CompareRel` relates them. -/
theorem comparePhase_evalExact (x y : S.dom → C) :
    (comparePhase S πd κ O Pk x y).evalExact = (O.tuples.flatMap fun a =>
      O.tuples.map fun b =>
        (compareScript S πd Pk (strOf S x y a.1) (strOf S x y b.1) a.2 b.2).evalExact) ∧
    ∀ a b : TestTuple q κ,
      (compareScript S πd Pk (strOf S x y a.1) (strOf S x y b.1) a.2 b.2).evalExact = true ↔
        CompareRel S.domGroup πd κ (strOf S x y a.1, a.2) (strOf S x y b.1, b.2) := by
  refine ⟨?_, fun a b => compareScript_evalExact S πd Pk _ _ _ _⟩
  rw [comparePhase, Script.evalExact_seqList, List.map_flatMap]
  simp only [List.map_map]
  rfl

theorem TestTupleOrder.length_eq : O.tuples.length = 2 * Fintype.card (Fin κ ↪ Fin q) := by
  have h : O.tuples.toFinset = Finset.univ := Finset.eq_univ_iff_forall.2 fun a =>
    List.mem_toFinset.2 (O.mem a)
  rw [← List.toFinset_card_of_nodup O.nodup, h, Finset.card_univ, Fintype.card_prod,
    Fintype.card_bool]

theorem card_embedding_le : Fintype.card (Fin κ ↪ Fin q) ≤ q ^ κ := by
  calc Fintype.card (Fin κ ↪ Fin q) ≤ Fintype.card (Fin κ → Fin q) :=
        Fintype.card_le_of_injective (fun f : Fin κ ↪ Fin q => (f : Fin κ → Fin q)) DFunLike.coe_injective
    _ = q ^ κ := by simp

/-- **The number of calls of the comparison phase**: at most `(2 q^κ)^2 n`, one call per update
of each of the `(2 q^κ)^2` lockstep runs. -/
theorem comparePhase_numCont_le (x y : S.dom → C) :
    (comparePhase S πd κ O Pk x y).numCont ≤ 4 * q ^ (2 * κ) * Fintype.card S.dom := by
  rw [comparePhase, Script.numCont_seqList]
  set L := O.tuples
  have h1 : ∀ s ∈ (L.flatMap fun a => L.map fun b =>
      compareScript S πd Pk (strOf S x y a.1) (strOf S x y b.1) a.2 b.2).map Script.numCont,
      s ≤ Fintype.card S.dom := by
    intro s hs
    obtain ⟨sc, hsc, rfl⟩ := List.mem_map.1 hs
    obtain ⟨a, -, hb⟩ := List.mem_flatMap.1 hsc
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hb
    exact compareScript_numCont_le S πd Pk _ _ _ _
  have h := List.sum_le_card_nsmul _ _ h1
  rw [List.length_map, List.length_flatMap] at h
  simp only [List.length_map, List.map_const', List.sum_replicate, smul_eq_mul] at h
  have hL : L.length ≤ 2 * q ^ κ := by
    rw [O.length_eq]; have := card_embedding_le (q := q) κ; omega
  have hLL : L.length * L.length ≤ 4 * q ^ (2 * κ) := by
    calc L.length * L.length ≤ (2 * q ^ κ) * (2 * q ^ κ) := Nat.mul_le_mul hL hL
      _ = 4 * q ^ (2 * κ) := by ring
  calc _ ≤ L.length * L.length * Fintype.card S.dom := h
    _ ≤ 4 * q ^ (2 * κ) * Fintype.card S.dom := Nat.mul_le_mul_right _ hLL

/-- **Every call of the comparison phase is a charged call** of the aggregation round (Lemma 4.1,
clause 2). -/
theorem comparePhase_calls [Finite Ω] {P : Params} (htr : S.Transitive) (hκ : P.κ = κ)
    (hk5 : 5 ≤ κ) (hθ : 1 ≤ P.θ * κ) (x y : S.dom → C) :
    (comparePhase S πd κ O Pk x y).CallsExact (AggCall P S) := by
  refine Script.callsExact_seqList _ fun s hs => ?_
  obtain ⟨a, -, hb⟩ := List.mem_flatMap.1 hs
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hb
  exact compareScript_calls htr πd Pk hκ hk5 hθ _ _ a.2 b.2

/-- Every call of a lockstep comparison is a `Continue` call. -/
theorem compareScript_cont (x y : S.dom → C) {k : ℕ} (t t' : Fin k → Fin q) :
    (compareScript S πd Pk x y t t').CallsExact (fun m _ => m = .cont) := by
  have loop : ∀ j, (compareLoop S πd Pk x y t t' j).CallsExact (fun m _ => m = .cont) := by
    intro j
    induction j with
    | zero => trivial
    | succ j ih =>
      refine Script.callsExact_bind _ _ ih ?_
      split
      · trivial
      · exact Script.callsExact_bind _ _ ⟨rfl, trivial⟩ trivial
  exact Script.callsExact_bind _ _ (loop _) trivial

/-- Every call of the comparison phase is a `Continue` call. -/
theorem comparePhase_cont (x y : S.dom → C) :
    (comparePhase S πd κ O Pk x y).CallsExact (fun m _ => m = .cont) := by
  refine Script.callsExact_seqList _ fun s hs => ?_
  obtain ⟨a, -, hb⟩ := List.mem_flatMap.1 hs
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hb
  exact compareScript_cont S πd Pk _ _ a.2 b.2

end Phase

end GI.Algorithm
