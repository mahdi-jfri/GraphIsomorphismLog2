module

public import Workspace.Impl.AggCertStep

@[expose] public section

/-!
# The positions of one endpoint loop, along the exact answers

The step function of the certificate phase walks the endpoint loop of one string of one test
set (`epFrom`, `winCont`, `Workspace/Impl/ScriptCont.lean`). Every reply of a run is the exact
answer (`Run.exact`), so after `t` rounds the stage that the program holds is the stage
`stage φ z t` of the endpoint procedure. This file names the remaining script at the two kinds of
program positions, for a candidate `R` of the coset representatives, and proves how one moves to
the next:

* `cpRound R t`: at the start of round `t` (the remaining `n - t` rounds, then `K R`);
* `cpWin R t τs acc`: inside round `t`, with the window calls of `τs` still to come and the
  translated answers `acc` collected so far.

Moves:

* `cpRound_empty`: a round with an empty increment changes nothing (`stage (t+1) = stage t`);
* `cpRound_end`: after the last round, the continuation of the final stage;
* `cpRound_start`: a round with a nonempty increment starts with the window calls of the
  recorded representatives (for every candidate of the record);
* `cpWin_cons`: the next window call;
* `cpWin_close`: after the window calls of all representatives, with the exact answers, the
  next round starts at `stage (t+1)` (`cpUnion_eq`, the computation of
  `endpointScriptLift_evalExact`).
* `cp_window_step`: `StepPostC` for one window call of all candidates of a record, with the
  canonical window value (`canon_window`);
* `stepPostC_mono_set`, `cpRound_narrow`: narrowing the candidates when new representatives are
  recorded;
* `cpWin_good`: the window call is a charged call of the round, so `Good` and below the round's
  measure (`chargedCall_good_mlt`, `ChargedCall.of_local_test`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open scoped Pointwise

section Loop

variable {Ω C C₀ : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom]
  {Q : Type} [Group Q] {P' : Subgroup (Perm S.dom)} (phi : P' →* Q) (z : S.dom → C₀) (n : ℕ)
  {β : Type} (K : CosetRepFn S.dom → Subgroup (Perm S.dom) × Finset S.dom → Script β)

/-- The window increment of round `t` is invariant under the kernel. -/
theorem cpInv (t : ℕ) :
    GI.Algorithm.Invariant (kernelIn phi (grp phi z t)) (inc phi z t : Set S.dom) :=
  (invariant_coe (inc_invariant phi z t)).mono inf_le_left

/-- The remaining script at the start of round `t`. -/
noncomputable def cpRound (R : CosetRepFn S.dom) (t : ℕ) : Script β :=
  (epFrom S R phi z (stage phi z t) (n - t)).bind (K R)

/-- The remaining script inside round `t`. -/
noncomputable def cpWin (R : CosetRepFn S.dom) (t : ℕ) (τs : List (Perm S.dom))
    (acc : List (Set (Perm S.dom))) : Script β :=
  winCont S R phi z (grp phi z t) (win phi z t) (inc phi z t) (cpInv S phi z t) τs acc
    (n - t - 1) (K R)

/-- **A round with an empty increment** changes nothing. -/
theorem cpRound_empty (R : CosetRepFn S.dom) {t : ℕ} (ht : t < n) (h : inc phi z t = ∅) :
    cpRound S phi z n K R t = cpRound S phi z n K R (t + 1) := by
  unfold cpRound
  have e : n - t = n - (t + 1) + 1 := by omega
  rw [e, epFrom_succ_bind_empty S R phi z _ _ _ h]
  have hs : stage phi z (t + 1) = stage phi z t := by
    apply Prod.ext
    · change grp phi z (t + 1) = grp phi z t
      rw [grp_succ, h, automorphisms_mask_empty]
    · change win phi z (t + 1) = win phi z t
      rw [win_succ, h, Finset.union_empty]
  rw [hs]

/-- **After the last round**: the continuation of the final stage. -/
theorem cpRound_end (R : CosetRepFn S.dom) :
    cpRound S phi z n K R n = K R (stage phi z n) := by
  unfold cpRound
  rw [Nat.sub_self, epFrom_zero, scr_done_bind]

/-- **The start of a round with a nonempty increment**, for a candidate of a record that holds
the representatives `l` of `(A_t, ker)`. -/
theorem cpRound_start {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) ×
    List (Perm S.dom))} {R : CosetRepFn S.dom} (hR : R ∈ Cands rec) {t : ℕ} (ht : t < n)
    (h : inc phi z t ≠ ∅) {l : List (Perm S.dom)}
    (hl : ((grp phi z t, kernelIn phi (grp phi z t)), l) ∈ rec) :
    cpRound S phi z n K R t = cpWin S phi z n K R t l [] := by
  unfold cpRound cpWin
  have e : n - t = (n - t - 1) + 1 := by omega
  rw [e]
  exact cert_roundStart S phi z hR (stage phi z t) (n - t - 1) (K R) h (cpInv S phi z t) hl

/-- **The next window call.** -/
theorem cpWin_cons (R : CosetRepFn S.dom) (t : ℕ) (τ : Perm S.dom) (τs : List (Perm S.dom))
    (acc : List (Set (Perm S.dom))) :
    cpWin S phi z n K R t (τ :: τs) acc =
      Script.ask .cont (windowCall S (kernelIn phi (grp phi z t)) (inc phi z t)
          (cpInv S phi z t) z τ) fun B =>
        cpWin S phi z n K R t τs (acc ++ [winVal S τ B]) := by
  unfold cpWin
  exact winCont_cons S R phi z _ _ _ _ τ τs acc _ _

/-- The translated exact answers of the window calls of the representatives. -/
noncomputable def cpAcc (t : ℕ) (l : List (Perm S.dom)) :
    List (Set (Perm S.dom)) :=
  l.map fun τ => winVal S τ (windowCall S (kernelIn phi (grp phi z t)) (inc phi z t)
    (cpInv S phi z t) z τ).answer

theorem cpAcc_append (t : ℕ) (l : List (Perm S.dom)) (τ : Perm S.dom) :
    cpAcc S phi z t l ++ [winVal S τ (windowCall S (kernelIn phi (grp phi z t)) (inc phi z t)
      (cpInv S phi z t) z τ).answer] = cpAcc S phi z t (l ++ [τ]) := by
  simp [cpAcc]

/-- **The union of the translated exact answers** of all representatives is the answer of the
round on the domain (the computation of `checkNewWindowLift_evalExact`). -/
theorem cpUnion_eq (hP : P' ≤ S.domGroup) (R : CosetRepFn S.dom) (t : ℕ) :
    (⋃ s ∈ cpAcc S phi z t (R.reps (grp phi z t) (kernelIn phi (grp phi z t))), s) =
      GI.Algorithm.answer (grp phi z t) (inc phi z t : Set S.dom) z z := by
  classical
  have h := checkNewWindowLift_evalExact S R ((grp_le phi z t).trans hP)
    (show kernelIn phi (grp phi z t) ≤ grp phi z t from inf_le_left)
    (invariant_coe (inc_invariant phi z t)) z
  unfold checkNewWindowLift at h
  rw [dif_pos (cpInv S phi z t), Script.evalExact_bind, Script.evalExact_seqList,
    List.map_map] at h
  simp only [Function.comp_def, Script.evalExact_bind, Script.call, Script.evalExact] at h
  rw [← h]
  rfl

/-- **The end of a round, with the exact answers**: the next round starts at `stage (t+1)`. -/
theorem cpWin_close (hP : P' ≤ S.domGroup) (R : CosetRepFn S.dom) (t : ℕ) :
    cpWin S phi z n K R t []
        (cpAcc S phi z t (R.reps (grp phi z t) (kernelIn phi (grp phi z t)))) =
      cpRound S phi z n K R (t + 1) := by
  classical
  unfold cpWin cpRound
  rw [winCont_nil, cpUnion_eq S phi z hP R t]
  have e : n - t - 1 = n - (t + 1) := by omega
  rw [e]
  have hset : GI.Algorithm.answer (grp phi z t) (inc phi z t : Set S.dom) z z =
      (automorphisms (grp phi z t) (mask z (inc phi z t)) : Set (Perm S.dom)) := by
    ext g
    rw [SetLike.mem_coe, mem_autWindow_iff _ z _ (inc_invariant phi z t)]
    simp [GI.Algorithm.answer]
  have hs : stage phi z (t + 1) =
      (Subgroup.closure (GI.Algorithm.answer (grp phi z t) (inc phi z t : Set S.dom) z z),
        win phi z t ∪ inc phi z t) := by
    rw [hset, Subgroup.closure_eq]
    rfl
  rw [hs]

end Loop

/-! ### The window call is an allowed call -/

section Good

variable {P : Params} {Ω C C₀ : Type} [Finite Ω] [DecidableEq Ω] {S : State Ω C}
  [Fintype S.dom] {Γ : Type} [Fintype Γ] [DecidableEq Γ]

/-- **The window call is a charged call** of the aggregation round (Lemma 4.1, clause 2). -/
theorem cpWin_charged (htr : S.Transitive) (π : S.domGroup →* alternatingGroup Γ)
    (T : Finset Γ) (hk5 : 5 ≤ T.card) (hκ : P.κ = T.card) (hθ : 1 ≤ P.θ * T.card)
    (z : S.dom → C₀) (t : ℕ) (τ : Perm S.dom) :
    ChargedCall P S (windowCall S (kernelIn (phiT S.domGroup π T) (grp (phiT S.domGroup π T) z t))
      (inc (phiT S.domGroup π T) z t) (cpInv S (phiT S.domGroup π T) z t) z τ) :=
  ChargedCall.of_local_test htr π z T hk5 hκ hθ t (State.queryChild_N _ _ _ _ _ _)
    (State.queryChild_hier _ _ _ _ _ _) (State.queryChild_G _ _ _ _ _ _)
    (by rw [windowCall, State.queryChild_dom])

end Good

/-- **The window call may be made** from a giant node `S` of the round's parameters `P₀`. -/
theorem cpWin_good {Ω C C₀ : Type} [Finite Ω] [DecidableEq Ω] {S : State Ω C} [Fintype S.dom]
    {Γ : Type} [Fintype Γ] [DecidableEq Γ] (hgood : Good P₀ .giant S) (htr : S.Transitive)
    (π : S.domGroup →* alternatingGroup Γ) (T : Finset Γ) (hk5 : 5 ≤ T.card)
    (hκ : P₀.κ = T.card) (hθ : 1 ≤ P₀.θ * T.card) (z : S.dom → C₀) (t : ℕ) (τ : Perm S.dom) :
    let W := windowCall S (kernelIn (phiT S.domGroup π T) (grp (phiT S.domGroup π T) z t))
      (inc (phiT S.domGroup π T) z t) (cpInv S (phiT S.domGroup π T) z t) z τ
    Good P₀ .cont W ∧ MLt (measure P₀ .cont W) (measure P₀ .giant S) :=
  chargedCall_good_mlt hgood (cpWin_charged htr π T hk5 hκ hθ z t τ)

/-! ### One window call of the step function -/

/-- **One window call, for the candidates of a record.** At a program position inside round `t`
of the loop of the string `z`, with the representatives `τ :: τs` still to come (the same for
every candidate of the record), the step function may return `[1, 1, arg, kst]` with the window
value `arg` of `canon_window` (group value `gv` of the lift of the kernel, the window indicator
`dv`, the codes of `wp_spec`), provided every canonical answer leads to a program state of the
continuations. -/
theorem cp_window_step {k : ℕ} {Ω C : Type} [Finite Ω] [DecidableEq Ω] {e : Ω ≃ Fin k}
    {c : C → ℕ} (hc : Function.Injective c) {S : State Ω C} [Fintype S.dom] {sv : GI.Cited.Val}
    (hS : Canon e c sv S) {hv : GI.Cited.Val} (hh : HierValC e hv S.hier) (hgood : Good P₀ .giant S)
    (htr : S.Transitive) {q : ℕ} (π : S.domGroup →* alternatingGroup (Fin q)) (T : Finset (Fin q))
    (hk5 : 5 ≤ T.card) (hκ : P₀.κ = T.card) (hθ : 1 ≤ P₀.θ * T.card) (z : Ω → C) (n : ℕ)
    {β : Type} (K : CosetRepFn S.dom → Subgroup (Perm S.dom) × Finset S.dom → Script β)
    {Out : β → GI.Cited.Val → Prop} {Rep : GI.Cited.Val → Set (Script β) → ℕ → Prop}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (hC : (Cands rec).Nonempty) (t : ℕ) {g : Perm Ω} (hg : g ∈ S.G) (τs : List (Perm S.dom))
    (acc : List (Set (Perm S.dom))) {gv dv : GI.Cited.Val}
    (hgv : GroupValC k gv (groupFin e (S.liftGroup
      (kernelIn (phiT S.domGroup π T) (grp (phiT S.domGroup π T) (dstr S z) t)))))
    (hdv : DomVal e dv (Subtype.val '' (inc (phiT S.domGroup π T) (dstr S z) t : Set S.dom)))
    {f : ℕ} (hf : 0 < f) {kst : GI.Cited.Val}
    (hrep : ∀ u, AnsC e u (windowCall S (kernelIn (phiT S.domGroup π T)
        (grp (phiT S.domGroup π T) (dstr S z) t)) (inc (phiT S.domGroup π T) (dstr S z) t)
        (cpInv S (phiT S.domGroup π T) (dstr S z) t) (dstr S z) (S.domHom ⟨g, hg⟩)).answer →
      Rep (.list [kst, u]) ((fun R => cpWin S (phiT S.domGroup π T) (dstr S z) n K R t τs
        (acc ++ [winVal S (S.domHom ⟨g, hg⟩) (windowCall S (kernelIn (phiT S.domGroup π T)
          (grp (phiT S.domGroup π T) (dstr S z) t)) (inc (phiT S.domGroup π T) (dstr S z) t)
          (cpInv S (phiT S.domGroup π T) (dstr S z) t) (dstr S z)
          (S.domHom ⟨g, hg⟩)).answer])) '' Cands rec) (f - 1)) :
    Iface.StepPostC (measure P₀ .giant S) Out Rep
      ((fun R => cpWin S (phiT S.domGroup π T) (dstr S z) n K R t (S.domHom ⟨g, hg⟩ :: τs) acc) ''
        Cands rec) f
      (.list [.nat 1, .nat (modeCode .cont), winVal' k gv dv
        (GI.Lang.natList (winCodesX e c S z (toFin e g))) (GI.Lang.natList (winCodesY e c S z (toFin e g))) hv S.N,
        kst]) := by
  obtain ⟨hG, hlt⟩ := cpWin_good hgood htr π T hk5 hκ hθ (dstr S z) t (S.domHom ⟨g, hg⟩)
  refine stepPostC_ask hC _ _ (fun R B => cpWin S (phiT S.domGroup π T) (dstr S z) n K R t τs
      (acc ++ [winVal S (S.domHom ⟨g, hg⟩) B])) (fun R _ => cpWin_cons S _ _ n K R t _ τs acc) hf e
    (winCode e c S z (toFin e g)) (winCode_injective e c S z (toFin e g) hc) ?_ hG hlt hrep
  exact canon_window hS hh (cpInv S (phiT S.domGroup π T) (dstr S z) t) z hg rfl hgv hdv

/-- **A larger candidate set.** What a step returns for a set of candidates is also right for
any larger set: the finished candidate or the candidates asking the call stay in it. This is how
the step narrows the candidates when it records new representatives (`CacheOK.miss`). -/
theorem stepPostC_mono_set {μ : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} {β : Type}
    {Out : β → GI.Cited.Val → Prop} {Rep : GI.Cited.Val → Set (Script β) → ℕ → Prop}
    {Ss Ss' : Set (Script β)} (hS : Ss ⊆ Ss') {f : ℕ} {w : GI.Cited.Val}
    (h : Iface.StepPostC μ Out Rep Ss f w) : Iface.StepPostC μ Out Rep Ss' f w := by
  rcases h with ⟨a, out, hw, ho, hm⟩ | ⟨hf, m, Ω', C', T, k', e', c', arg, kst, Ks, hc', hm, hw,
    hcan, hg, hlt, hKs, hKS, hrep⟩
  · exact Or.inl ⟨a, out, hw, ho, hS hm⟩
  · exact Or.inr ⟨hf, m, Ω', C', T, k', e', c', arg, kst, Ks, hc', hm, hw, hcan, hg, hlt, hKs,
      fun k hk => hS (hKS k hk), hrep⟩

/-- **Narrowing at the start of a round.** If the record `rec'` extends `rec` (for example by the
new representatives of a cache miss), the candidates of `rec'` at the start of round `t` are among
those of `rec`, and all of them continue with the window calls of the recorded `l`. -/
theorem cpRound_narrow {Ω C C₀ : Type} [DecidableEq Ω] (S : State Ω C) [Fintype S.dom]
    {Q : Type} [Group Q] {P' : Subgroup (Perm S.dom)} (phi : P' →* Q) (z : S.dom → C₀) (n : ℕ)
    {β : Type} (K : CosetRepFn S.dom → Subgroup (Perm S.dom) × Finset S.dom → Script β)
    {rec rec' : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    (hsub : Cands rec' ⊆ Cands rec) {t : ℕ} (ht : t < n) (h : inc phi z t ≠ ∅)
    {l : List (Perm S.dom)} (hl : ((grp phi z t, kernelIn phi (grp phi z t)), l) ∈ rec') :
    (fun R => cpWin S phi z n K R t l []) '' Cands rec' ⊆
      (fun R => cpRound S phi z n K R t) '' Cands rec := by
  rintro _ ⟨R, hR, rfl⟩
  exact ⟨R, hsub hR, cpRound_start S phi z n K hR ht h hl⟩

end GI.Impl
