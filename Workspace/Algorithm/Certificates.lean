module

public import Workspace.Algorithm.LocalTestCalls
public import Workspace.Algorithm.QueryChild
public import Workspace.CertificateEndpoint
public import Workspace.CertificateComparison

@[expose] public section

/-!
# `CheckNewWindow` and the endpoint procedure as query scripts (Algorithm 2)

Section 4: "The operation `CheckNewWindow` returns the full subgroup of `A`
preserving `x` on `V`. It enumerates the constantly many cosets of `ker(φ_T|_A)` in
`A` and uses `Continue` on the kernel orbits in `V`, with the inherited state and the
orbit chain rule."

`checkNewWindow S₀ phi A V x` is that script: for one representative `τ` of each
coset of `N = ker(φ|_A)` in `A`, it asks `Continue` under `N` on the window `V` with
the colorings `(x, x ∘ τ)` (an inherited call: the bookkeeping is that of the frozen
parent `S₀`), and returns the union of the translates `τ · A_τ`. The `Continue` call
on the intransitive `N` splits into kernel-orbit calls by the orbit chain.

`endpointScript` runs the loop of Algorithm 2 with these calls; when the calls are
exact it computes the stages `GI.Endpoint.stage` of the endpoint procedure
(`endpointScript_evalExact`), which Lemma 4.1 (`GI.Paper.lem_main_local_test`) is
about. The lockstep comparisons are computed the same way
(`lockstepStep_evalExact`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Endpoint
open scoped Pointwise

variable {Ω C Q : Type} [Fintype Ω] [DecidableEq Ω] [Group Q]

/-- Representatives of the left cosets of `N ⊓ A` in `A`, one per coset. -/
noncomputable def cosetReps (A N : Subgroup (Perm Ω)) : List (Perm Ω) := by
  classical
  haveI : Fintype (A ⧸ N.subgroupOf A) := Fintype.ofFinite _
  exact (Finset.univ : Finset (A ⧸ N.subgroupOf A)).toList.map fun c => ((Quotient.out c : A) : Perm Ω)

omit [DecidableEq Ω] in
theorem cosetReps_mem {A N : Subgroup (Perm Ω)} {τ : Perm Ω} (h : τ ∈ cosetReps A N) : τ ∈ A := by
  classical
  unfold cosetReps at h
  simp only [List.mem_map] at h
  obtain ⟨c, -, rfl⟩ := h
  exact (Quotient.out c : A).2

omit [DecidableEq Ω] in
theorem cosetReps_cover (A N : Subgroup (Perm Ω)) :
    (A : Set (Perm Ω)) ⊆ ⋃ τ ∈ cosetReps A N, τ • (N : Set (Perm Ω)) := by
  classical
  intro a ha
  haveI : Fintype (A ⧸ N.subgroupOf A) := Fintype.ofFinite _
  let c : A ⧸ N.subgroupOf A := QuotientGroup.mk ⟨a, ha⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (N.subgroupOf A) (⟨a, ha⟩ : A)
  simp only [Set.mem_iUnion]
  refine ⟨((Quotient.out c : A) : Perm Ω), ?_, ?_⟩
  · unfold cosetReps
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    exact ⟨c, rfl⟩
  · rw [Set.mem_smul_set]
    refine ⟨((h : A) : Perm Ω)⁻¹, N.inv_mem (Subgroup.mem_subgroupOf.1 h.2), ?_⟩
    have : ((Quotient.out c : A) : Perm Ω) = a * ((h : A) : Perm Ω) := by
      have := congrArg (fun z : A => (z : Perm Ω)) hh
      simpa using this
    rw [smul_eq_mul, this, mul_inv_cancel_right]

/-- **A choice of coset representatives** (Section 4: "It enumerates the constantly many cosets
of `ker(φ_T|_A)` in `A`"): for all subgroups `A, N`, a list of elements of `A`, at most one for
each left coset of `N ⊓ A` in `A`, whose cosets cover `A`. The paper fixes no particular
representatives, so `CheckNewWindow` takes them as a parameter. The list also fixes the order of
the calls. `CosetRepFn.default` takes `Quotient.out` of every coset. -/
structure CosetRepFn (V : Type) where
  reps : Subgroup (Perm V) → Subgroup (Perm V) → List (Perm V)
  mem : ∀ {A N : Subgroup (Perm V)} {τ : Perm V}, τ ∈ reps A N → τ ∈ A
  cover : ∀ A N : Subgroup (Perm V), (A : Set (Perm V)) ⊆ ⋃ τ ∈ reps A N, τ • (N : Set (Perm V))
  length_le : ∀ A N : Subgroup (Perm V), (reps A N).length ≤ Nat.card (A ⧸ N.subgroupOf A)

/-- **`CheckNewWindow`** (Section 4). Ask `Continue` under `N` on `V` for the colorings
`(x, x ∘ τ)`, one call per coset representative `τ` of `N` in `A`, and return the
union of `τ · A_τ`. If `V` is not `N`-invariant (which does not happen when the
earlier calls were exact) no call is made. -/
noncomputable def checkNewWindow (S₀ : State Ω C) (A N : Subgroup (Perm Ω)) (V : Finset Ω)
    (x : Ω → C) : Script (Set (Perm Ω)) := by
  classical
  exact if hV : GI.Algorithm.Invariant N (V : Set Ω) then
    (Script.seqList ((cosetReps A N).map fun τ : Perm Ω =>
        (Script.call .cont (S₀.inherit N (V : Set Ω) hV x (x ∘ τ))).bind
          fun B => Script.done (τ • B))).bind
      fun l => Script.done (⋃ s ∈ l, s)
  else Script.done ∅

omit [DecidableEq Ω] in
/-- `CheckNewWindow` is exact: with exact recursive answers it returns the set of
elements of `A` that preserve the colors of `x` on the `A`-invariant window `V`. -/
theorem checkNewWindow_evalExact (S₀ : State Ω C) {A N : Subgroup (Perm Ω)} (hNA : N ≤ A)
    {V : Finset Ω} (hV : GI.Algorithm.Invariant A (V : Set Ω)) (x : Ω → C) :
    (checkNewWindow S₀ A N V x).evalExact = GI.Algorithm.answer A V x x := by
  classical
  have hVN : GI.Algorithm.Invariant N (V : Set Ω) := hV.mono hNA
  unfold checkNewWindow
  rw [dif_pos hVN, Script.evalExact_bind, Script.evalExact_seqList, List.map_map]
  simp only [Function.comp_def, Script.evalExact_bind, Script.call, Script.evalExact,
    State.inherit_answer]
  rw [← answer_cover (ι := {τ // τ ∈ cosetReps A N}) (fun τ => τ.1) (fun _ => N)
    (fun τ => cosetReps_mem τ.2) (fun _ => hNA) ?_]
  · ext g
    simp only [Set.mem_iUnion, List.mem_map, exists_prop]
    constructor
    · rintro ⟨s, ⟨τ, hτ, rfl⟩, hg⟩
      exact ⟨⟨τ, hτ⟩, hg⟩
    · rintro ⟨⟨τ, hτ⟩, hg⟩
      exact ⟨_, ⟨τ, hτ, rfl⟩, hg⟩
  · intro g hg
    have := cosetReps_cover A N hg.1
    simp only [Set.mem_iUnion] at this ⊢
    obtain ⟨τ, hτ, h⟩ := this
    exact ⟨⟨τ, hτ⟩, h⟩

section Endpoint

variable {P : Subgroup (Perm Ω)} (phi : P →* Q)

/-- The loop of **Algorithm 2** (`LocalCertificate`), `t` rounds, with `CheckNewWindow`
for the window updates: `A ← CheckNewWindow(S, A, V, x)`, `W ← W ∪ V`. A round with
empty increment (a stop) makes no call. -/
noncomputable def endpointScript (S₀ : State Ω C) (x : Ω → C) :
    ℕ → Script (Subgroup (Perm Ω) × Finset Ω)
  | 0 => Script.done (P, ∅)
  | t + 1 => (endpointScript S₀ x t).bind fun AW => by
      classical
      exact if increment phi AW.1 AW.2 = ∅ then Script.done AW
      else (checkNewWindow S₀ AW.1 (kernelIn phi AW.1) (increment phi AW.1 AW.2) x).bind
        fun B => Script.done (Subgroup.closure B, AW.2 ∪ increment phi AW.1 AW.2)

omit [Fintype Ω] [DecidableEq Ω] in
theorem invariant_coe {A : Subgroup (Perm Ω)} {W : Finset Ω} (h : GI.Endpoint.Invariant A W) :
    GI.Algorithm.Invariant A (W : Set Ω) := fun a ha v => by
  simpa using h a ha v

/-- **Algorithm 2 computes the endpoint stages.** If every `Continue` call made by
`CheckNewWindow` returns its exact answer, round `t` of the loop holds the stage
`(A_t, W_t)` of `GI.Endpoint.stage` (`GI.Paper.alg_local_certificate`). -/
theorem endpointScript_evalExact (S₀ : State Ω C) (x : Ω → C) (t : ℕ) :
    (endpointScript phi S₀ x t).evalExact = stage phi x t := by
  classical
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [endpointScript, Script.evalExact_bind, ih]
    have hinv := invariant_coe (inc_invariant phi x t)
    by_cases hV : increment phi (stage phi x t).1 (stage phi x t).2 = ∅
    · simp only [hV, if_true, Script.evalExact]
      change stage phi x t = (automorphisms (grp phi x t) (mask x (inc phi x t)),
        win phi x t ∪ inc phi x t)
      have hV' : inc phi x t = ∅ := hV
      rw [hV', automorphisms_mask_empty, Finset.union_empty]
    · simp only [hV, if_false, Script.evalExact_bind, Script.evalExact]
      rw [checkNewWindow_evalExact S₀
        (show kernelIn phi (grp phi x t) ≤ grp phi x t from inf_le_left) hinv x]
      change (Subgroup.closure _, _) = (automorphisms (grp phi x t) (mask x (inc phi x t)), _)
      congr 1
      have hset : GI.Algorithm.answer (grp phi x t) (inc phi x t : Set Ω) x x =
          (automorphisms (grp phi x t) (mask x (inc phi x t)) : Set (Perm Ω)) := by
        ext g
        rw [SetLike.mem_coe, mem_autWindow_iff _ x _ (inc_invariant phi x t)]
        simp [GI.Algorithm.answer]
      rw [hset, Subgroup.closure_eq]

end Endpoint

section Lockstep

open GI.LocalGroups GI.LocalCertificates

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ] (G : Subgroup (Perm Ω))
  (π : G →* alternatingGroup Γ) {k : ℕ}

/-- **One lockstep update** of an ordered comparison (Section 4: "For ordered
comparisons, run two copies in lockstep under the full ordered-tuple transporter,
maintaining the complete comparison coset after each new window. Each update uses
the same inherited kernel-orbit queries."). The current comparison coset is
`g₀ N_j`, with `N_j` the kernel group of the `x`-endpoint at stage `j`; the update
asks `Continue` under `N_j` on the new window `V_j` with the colorings `(x, y ∘ g₀)`
and translates the answer by `g₀`. -/
noncomputable def lockstepStep (S₀ : State Ω C) (j : ℕ) (x y : Ω → C) (t : Fin k → Γ)
    (g₀ : Perm Ω) : Script (Set (Perm Ω)) := by
  classical
  exact if hV : GI.Algorithm.Invariant (kernelIn (phiT G π (tset t)) (grp (phiT G π (tset t)) x j))
      (inc (phiT G π (tset t)) x j : Set Ω) then
    (Script.call .cont (S₀.inherit (kernelIn (phiT G π (tset t)) (grp (phiT G π (tset t)) x j))
      (inc (phiT G π (tset t)) x j : Set Ω) hV x (y ∘ g₀))).bind fun B => Script.done (g₀ • B)
  else Script.done ∅

/-- **The lockstep update is exact.** If `g₀` lies in the stage-`j` comparison coset
and the `Continue` call is exact, the update returns the stage-`(j+1)` comparison
coset `GI.LocalCertificates.lockstep` (the comparison of eq. `comparison` at the
final stage). -/
theorem lockstepStep_evalExact (S₀ : State Ω C) (j : ℕ) (x y : Ω → C) (t t' : Fin k → Γ)
    {g₀ : Perm Ω} (hg₀ : g₀ ∈ lockstep G π j x t y t') :
    (lockstepStep G π S₀ j x y t g₀).evalExact = lockstep G π (j + 1) x t y t' := by
  classical
  set T := tset t
  set N := kernelIn (phiT G π T) (grp (phiT G π T) x j)
  have hNA : N ≤ grp (phiT G π T) x j := inf_le_left
  have hV : GI.Algorithm.Invariant N (inc (phiT G π T) x j : Set Ω) :=
    (invariant_coe (inc_invariant (phiT G π T) x j)).mono hNA
  unfold lockstepStep
  rw [dif_pos hV]
  simp only [Script.evalExact_bind, Script.call, Script.evalExact, State.inherit_answer]
  rw [lockstep_succ (G := G) (π := π)]
  have hcoset := lockstep_eq_coset hg₀
  rw [(automorphisms_J_eq (G := G) (π := π) x T j).1, (automorphisms_J_eq (G := G) (π := π) x T j).2] at hcoset
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

end Lockstep


/-! ### The recursion's form: lifted calls on the domain of a state

In the recursion the local test runs on the faithful image `G|_dom` of a transitive state `S`
on its domain (Lemma 4.1 is stated for a group on a whole finite type; Section 3: "Every fresh
call uses the faithful permutation image on its own active domain"). Its `Continue` calls are
inherited calls of `S` on the positions `Ω`: under the lift of the stage kernel `N_t` (the
elements of `G` whose restriction lies in `N_t`), on the lifted window, with the colors of the
domain extended by one extra color off the domain. These are exactly the calls of
`ChargedCall.of_local_test` (`Workspace/Algorithm/LocalTestCalls.lean`).

* `checkNewWindowLift`, `endpointScriptLift`: the scripts, with these lifted calls;
* `endpointScriptLift_evalExact`: with exact answers they compute the stages of the endpoint
  procedure on `G|_dom`;
* `endpointScriptLift_calls`: every call is a charged call of the aggregation round of `S`
  (`AggCall`), by Lemma 4.1, clause 2. This is what the field `Aggregation.calls` of the
  constructor `Run.aggregate` asks of the calls of the local certificates
  (`endpointScriptLift_bind_calls`). -/

section Lifted

variable {Ω C C₀ : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom]

/-- The coloring of `Ω` given by a coloring of the domain, with one extra color off it. -/
noncomputable def liftColor (x : S.dom → C₀) : Ω → Option C₀ := fun v => by
  classical
  exact if h : v ∈ S.dom then some (x ⟨v, h⟩) else none

theorem liftColor_mem (x : S.dom → C₀) (v : S.dom) : liftColor S x v = some (x v) := by
  classical
  simp [liftColor, v.2]

open Classical in
/-- A lift to `G` of an element of the faithful image `G|_dom`. -/
noncomputable def liftPerm (τ : Perm S.dom) : Perm Ω :=
  if h : τ ∈ S.domGroup then ((Classical.choose h : S.G) : Perm Ω) else 1

theorem liftPerm_spec {τ : Perm S.dom} (h : τ ∈ S.domGroup) :
    ∃ hm : liftPerm S τ ∈ S.G, S.domHom ⟨liftPerm S τ, hm⟩ = τ := by
  classical
  unfold liftPerm
  rw [dif_pos h]
  exact ⟨(Classical.choose h).2, Classical.choose_spec h⟩

/-- The restriction to the domain of a set of elements of `G`. -/
def restrictAns (B : Set (Perm Ω)) : Set (Perm S.dom) :=
  {p | ∃ g, ∃ hg : g ∈ S.G, g ∈ B ∧ S.domHom ⟨g, hg⟩ = p}

theorem lifted_invariant {N : Subgroup (Perm S.dom)} {V : Finset S.dom}
    (hV : GI.Algorithm.Invariant N (V : Set S.dom)) :
    GI.Algorithm.Invariant (S.liftGroup N) (Subtype.val '' (V : Set S.dom)) := by
  intro g hg v
  obtain ⟨hgG, hgN⟩ := State.mem_liftGroup.1 hg
  constructor
  · rintro ⟨w, hw, hwv⟩
    have hv : v ∈ S.dom := (S.dom_inv g hgG v).1 (hwv ▸ w.2)
    refine ⟨⟨v, hv⟩, ?_, rfl⟩
    have h1 : S.domHom ⟨g, hgG⟩ ⟨v, hv⟩ = w := Subtype.ext (by rw [State.domHom_apply]; exact hwv.symm)
    rw [← (hV _ hgN ⟨v, hv⟩), h1]
    exact hw
  · rintro ⟨w, hw, rfl⟩
    refine ⟨S.domHom ⟨g, hgG⟩ w, (hV _ hgN w).2 hw, rfl⟩

/-- **The lifted window call** of `CheckNewWindow`: `Continue` under the lift of `N` on the
lifted window `V`, for the colorings `(x, x ∘ τ)` of the domain, extended off the domain by one
extra color (no lift of `τ` to `G` is chosen). A certificate child clears the bookkeeping
(`State.queryChild`; Section 6: "An independent certificate or rectangle child that may lose the
carrier clears its row record and floor mode, and sets `h=2`"). -/
noncomputable def windowCall (N : Subgroup (Perm S.dom)) (V : Finset S.dom)
    (hV : GI.Algorithm.Invariant N (V : Set S.dom)) (x : S.dom → C₀) (τ : Perm S.dom) :
    State Ω (Option C₀) :=
  S.queryChild (S.liftGroup N) (Subtype.val '' (V : Set S.dom)) (lifted_invariant S hV)
    (liftColor S x) (liftColor S (x ∘ τ))

/-- The restricted answer of the lifted call is the answer of the call on the domain. -/
theorem windowCall_answer {N : Subgroup (Perm S.dom)} (hN : N ≤ S.domGroup) {V : Finset S.dom}
    (hV : GI.Algorithm.Invariant N (V : Set S.dom)) (x : S.dom → C₀) {τ : Perm S.dom}
    (hτ : τ ∈ S.domGroup) :
    restrictAns S (windowCall S N V hV x τ).answer = GI.Algorithm.answer N (V : Set S.dom) x (x ∘ τ) := by
  have key : ∀ (g : Perm Ω) (hg : g ∈ S.G) (v : S.dom),
      liftColor S (x ∘ τ) (g v) = some (x (τ (S.domHom ⟨g, hg⟩ v))) := by
    intro g hg v
    have h1 : g v = (S.domHom ⟨g, hg⟩ v : Ω) := rfl
    rw [h1, liftColor_mem]
    rfl
  ext p
  simp only [restrictAns, windowCall, State.queryChild_answer, GI.Algorithm.answer,
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

/-- **`CheckNewWindow` with lifted calls** (Section 4). For one representative `τ` of each
coset of `N` in `A`, ask `Continue` on the lifted window call, restrict its answer to the
domain and translate by `τ`; return the union. -/
noncomputable def checkNewWindowLift (R : CosetRepFn S.dom) (A N : Subgroup (Perm S.dom))
    (V : Finset S.dom) (x : S.dom → C₀) : Script (Set (Perm S.dom)) := by
  classical
  exact if hV : GI.Algorithm.Invariant N (V : Set S.dom) then
    (Script.seqList ((R.reps A N).map fun τ : Perm S.dom =>
        (Script.call .cont (windowCall S N V hV x τ)).bind
          fun B => Script.done (τ • restrictAns S B))).bind
      fun l => Script.done (⋃ s ∈ l, s)
  else Script.done ∅

/-- `CheckNewWindow` with lifted calls is exact. -/
theorem checkNewWindowLift_evalExact (R : CosetRepFn S.dom) {A N : Subgroup (Perm S.dom)}
    (hA : A ≤ S.domGroup)
    (hNA : N ≤ A) {V : Finset S.dom} (hV : GI.Algorithm.Invariant A (V : Set S.dom))
    (x : S.dom → C₀) :
    (checkNewWindowLift S R A N V x).evalExact = GI.Algorithm.answer A V x x := by
  classical
  have hVN : GI.Algorithm.Invariant N (V : Set S.dom) := hV.mono hNA
  unfold checkNewWindowLift
  rw [dif_pos hVN, Script.evalExact_bind, Script.evalExact_seqList, List.map_map]
  simp only [Function.comp_def, Script.evalExact_bind, Script.call, Script.evalExact]
  rw [← answer_cover (ι := {τ // τ ∈ R.reps A N}) (fun τ => τ.1) (fun _ => N)
    (fun τ => R.mem τ.2) (fun _ => hNA) ?_]
  · ext g
    simp only [Set.mem_iUnion, List.mem_map, exists_prop]
    constructor
    · rintro ⟨s, ⟨τ, hτ, rfl⟩, hg⟩
      rw [windowCall_answer S (hNA.trans hA) hVN x (hA (R.mem hτ))] at hg
      exact ⟨⟨τ, hτ⟩, hg⟩
    · rintro ⟨⟨τ, hτ⟩, hg⟩
      refine ⟨_, ⟨τ, hτ, rfl⟩, ?_⟩
      rw [windowCall_answer S (hNA.trans hA) hVN x (hA (R.mem hτ))]
      exact hg
  · intro g hg
    have := R.cover A N hg.1
    simp only [Set.mem_iUnion] at this ⊢
    obtain ⟨τ, hτ, h⟩ := this
    exact ⟨⟨τ, hτ⟩, h⟩

variable {Q : Type} [Group Q] {P' : Subgroup (Perm S.dom)} (R : CosetRepFn S.dom) (phi : P' →* Q)

/-- **Algorithm 2 with lifted calls**: the loop of `endpointScript` on the faithful image
`G|_dom`, with `checkNewWindowLift` for the window updates and the coset representatives `R`. -/
noncomputable def endpointScriptLift (x : S.dom → C₀) :
    ℕ → Script (Subgroup (Perm S.dom) × Finset S.dom)
  | 0 => Script.done (P', ∅)
  | t + 1 => (endpointScriptLift x t).bind fun AW => by
      classical
      exact if increment phi AW.1 AW.2 = ∅ then Script.done AW
      else (checkNewWindowLift S R AW.1 (kernelIn phi AW.1) (increment phi AW.1 AW.2) x).bind
        fun B => Script.done (Subgroup.closure B, AW.2 ∪ increment phi AW.1 AW.2)

/-- **Algorithm 2 with lifted calls computes the endpoint stages** on `G|_dom`. -/
theorem endpointScriptLift_evalExact (hP : P' ≤ S.domGroup) (x : S.dom → C₀) (t : ℕ) :
    (endpointScriptLift S R phi x t).evalExact = stage phi x t := by
  classical
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [endpointScriptLift, Script.evalExact_bind, ih]
    have hinv := invariant_coe (inc_invariant phi x t)
    by_cases hV : increment phi (stage phi x t).1 (stage phi x t).2 = ∅
    · simp only [hV, if_true, Script.evalExact]
      change stage phi x t = (automorphisms (grp phi x t) (mask x (inc phi x t)),
        win phi x t ∪ inc phi x t)
      have hV' : inc phi x t = ∅ := hV
      rw [hV', automorphisms_mask_empty, Finset.union_empty]
    · simp only [hV, if_false, Script.evalExact_bind, Script.evalExact]
      rw [checkNewWindowLift_evalExact S R ((grp_le phi x t).trans hP)
        (show kernelIn phi (grp phi x t) ≤ grp phi x t from inf_le_left) hinv x]
      change (Subgroup.closure _, _) = (automorphisms (grp phi x t) (mask x (inc phi x t)), _)
      congr 1
      have hset : GI.Algorithm.answer (grp phi x t) (inc phi x t : Set S.dom) x x =
          (automorphisms (grp phi x t) (mask x (inc phi x t)) : Set (Perm S.dom)) := by
        ext g
        rw [SetLike.mem_coe, mem_autWindow_iff _ x _ (inc_invariant phi x t)]
        simp [GI.Algorithm.answer]
      rw [hset, Subgroup.closure_eq]

end Lifted

-- `Script.callsExact_seqList` is in `Workspace/Algorithm/Interfaces.lean`.

section LiftedCalls

open GI.LocalGroups

variable {P : Params} {Ω C C₀ Γ : Type} [Finite Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {S : State Ω C} [Fintype S.dom]

/-- **The calls of the local certificate are charged calls** (Lemma 4.1, clause 2, through
`ChargedCall.of_local_test`). For a transitive state, a label map `π : G|_dom → Alt(Γ)` and a
test set `T` with `|T| = κ ≥ 5` and `θ κ ≥ 1`, every call that the lifted endpoint script
makes along the exact answers is an inherited `Continue` call of the type `AggCall` of an
aggregation round of `S`. -/
theorem endpointScriptLift_calls (htr : S.Transitive) (π : S.domGroup →* alternatingGroup Γ)
    (T : Finset Γ) (hk5 : 5 ≤ T.card) (hκ : P.κ = T.card) (hθ : 1 ≤ P.θ * T.card)
    (R : CosetRepFn S.dom) (x : S.dom → C₀) (t : ℕ) :
    (endpointScriptLift S R (phiT S.domGroup π T) x t).CallsExact (AggCall P S) := by
  classical
  induction t with
  | zero => trivial
  | succ t ih =>
    refine Script.callsExact_bind _ _ ih ?_
    rw [endpointScriptLift_evalExact _ _ _ Pgrp_le]
    by_cases hV : increment (phiT S.domGroup π T) (stage (phiT S.domGroup π T) x t).1
        (stage (phiT S.domGroup π T) x t).2 = ∅
    · simp only [hV, if_true]; trivial
    · simp only [hV, if_false]
      refine Script.callsExact_bind _ _ ?_ trivial
      unfold checkNewWindowLift
      split_ifs with hW
      · refine Script.callsExact_bind _ _ (Script.callsExact_seqList _ fun s hs => ?_) trivial
        obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hs
        refine ⟨Or.inr ⟨rfl, rfl, ?_⟩, trivial⟩
        exact ChargedCall.of_local_test htr π x T hk5 hκ hθ t (State.queryChild_N _ _ _ _ _ _)
          (State.queryChild_hier _ _ _ _ _ _) (State.queryChild_G _ _ _ _ _ _)
          (by rw [windowCall, State.queryChild_dom])
      · trivial

/-- **The connection to `Run.aggregate`.** An aggregation script that first runs the local
certificate (the lifted endpoint script) and then continues with `f` satisfies the field
`Aggregation.calls` as soon as its continuation does. -/
theorem endpointScriptLift_bind_calls {β : Type} (htr : S.Transitive)
    (π : S.domGroup →* alternatingGroup Γ) (T : Finset Γ) (hk5 : 5 ≤ T.card)
    (hκ : P.κ = T.card) (hθ : 1 ≤ P.θ * T.card) (R : CosetRepFn S.dom) (x : S.dom → C₀) (t : ℕ)
    (f : Subgroup (Perm S.dom) × Finset S.dom → Script β)
    (hf : (f (stage (phiT S.domGroup π T) x t)).CallsExact (AggCall P S)) :
    ((endpointScriptLift S R (phiT S.domGroup π T) x t).bind f).CallsExact (AggCall P S) :=
  Script.callsExact_bind _ _ (endpointScriptLift_calls htr π T hk5 hκ hθ R x t)
    (by rw [endpointScriptLift_evalExact _ _ _ Pgrp_le]; exact hf)

end LiftedCalls

end GI.Algorithm
