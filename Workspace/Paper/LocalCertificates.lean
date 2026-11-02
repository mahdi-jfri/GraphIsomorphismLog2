import Workspace.CertificateCalls
import Workspace.CertificateComparison

/-!
# Paper statements: local certificates (Section 4, Sections A.1 and A.3)

Faithful statements for

* Section A, "The local permutation families" (`sec:local-groups`): the claim
  about `φ_T` before Proposition A.1, and Proposition A.1;
* Section A, "Constant-size certificates and exact comparisons"
  (`sec:certificates`): the endpoint construction, the two recursive call types,
  the counting content of eq. `constant-recurrence`, and the ordered comparisons;
* Section 4: Algorithm `alg:local-certificate` and Lemma 4.1
  (`lem:main-local-test`).

## Conventions

`G ≤ Sym(Ω)` is a subgroup of `Equiv.Perm Ω` and `π : G → Alt(Γ)` a surjection.
For a test set `T ⊆ Γ`, the groups `Q_T`, `P_T`, `J_T` and the restriction
`φ_T : P_T → Alt(T)` are `GI.LocalGroups.Qgrp`, `Pgrp`, `Jgrp`, `phiT`; `π(g)` is
`GI.LocalGroups.lab G π g`.

The endpoint procedure (Algorithm `alg:local-certificate`, rules 1 to 5 of
"Endpoint construction") is the sequence of stages
`GI.Endpoint.stage (phiT G π T) x t = (A_t, W_t)` (`GI.Paper.alg_local_certificate`),
defined by recursion on `t`:

* `A_0 = P_T`, `W_0 = ∅`;
* `A_{t+1} = Aut_{A_t}(x^{V_t})`, `W_{t+1} = W_t ∪ V_t`, where the increment
  `V_t = GI.Endpoint.increment (phiT G π T) A_t W_t` is
  `∅` if `φ_T(A_t) ≠ Alt(T)` (rule 1, nonfull stop);
  else `E_t` (the affected points outside `W_t`) if `E_t ≠ ∅` (rule 2);
  else `∅` if `φ_T((A_t)_{(Ω \ W_t)}) = Alt(T)` (rule 3, full stop);
  else the union of the `A_t`-orbits `Δ` outside `W_t` with
  `φ_T((A_t)_{(Δ)}) = 1` (rule 4).

After a stop the sequence is constant, and the stage with index `n = |Ω|` is the
final one (`GI.Paper.endpoint_at_most_n_updates`). Its group and window are
`finalGrp` and `finalWin = W(x, T)`, and the full certificate is
`K(T) = fullCert = (A_final)_{(Ω \ W_final)}`.

## Deferred algorithmic clauses

The paper's polynomial-time clauses ("Generators ... can be obtained in
polynomial time" in Proposition A.1; "can be computed with polynomial
structural work and polynomially many inherited recursive calls" in Lemma 4.1;
the coset enumeration inside `CheckNewWindow`; the `n^{O(1)}` factor of eq.
`constant-recurrence`) are statements about algorithms on the machine model.
They are left to the machine-level programs of `Workspace/Impl/`. Here we prove the mathematical
content those clauses rely on: the definitions of the windows and groups as
functions of the data, the identities and invariances, equivariance under
parent isomorphisms, the bound on the number of updates, the number of kernel
cosets, and the size and budget facts that make the two call types
`(s, σ) ↦ (s/κ, σ)` and `(s, σ) ↦ (s, σ - κ)`.
-/

namespace GI.Paper

open Equiv Equiv.Perm GI.Endpoint GI.LocalGroups GI.LocalCertificates

variable {Ω Γ C : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]

/-! ### Section A.1: the local permutation families -/

omit [Fintype Ω] [DecidableEq Ω] in
/-- **Section A.1** (`sec:local-groups`), the claim before Proposition A.1: "If
`k ≥ 3` and `m - k ≥ 2`, restriction gives a surjection `φ_T : P_T → Alt(T)`, with
kernel `J_T`, and `[Q_T : P_T] = 2`." -/
theorem sec_local_groups_phiT (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    (hπ : Function.Surjective π) (T : Finset Γ) (hk : 3 ≤ T.card)
    (hmk : 2 ≤ Fintype.card Γ - T.card) :
    Function.Surjective (phiT G π T) ∧
    (phiT G π T).ker.map (Pgrp G π T).subtype = Jgrp G π T ∧
    (Pgrp G π T).relIndex (Qgrp G π T) = 2 :=
  ⟨phiT_surjective hπ, phiT_ker,
    index_P_in_Q hπ (by omega) (by rw [Finset.card_univ_diff]; exact hmk)⟩

omit [Fintype Ω] [DecidableEq Ω] in
/-- **Proposition A.1**, mathematical content. The proof computes `ker π`, lifts
generators of `Alt(T) × Alt(Γ \ T)` to get `P_T`, lifts only the complementary
alternating group to get `J_T`, and adds one paired transposition for `Q_T`.
This rests on: `ker π ≤ J_T ≤ P_T ≤ Q_T ≤ G`; `P_T` is the full preimage of
`Alt(T) × Alt(Γ \ T)`; and every element of `Q_T` lies in `P_T` or in `P_T τ` for
any `τ ∈ Q_T \ P_T`. The polynomial-time clause is left to the machine level (see the
module docstring). -/
theorem prop_local_groups (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    (T : Finset Γ) :
    π.ker.map G.subtype ≤ Jgrp G π T ∧ Jgrp G π T ≤ Pgrp G π T ∧
    Pgrp G π T ≤ Qgrp G π T ∧ Qgrp G π T ≤ G ∧
    (∀ g : Perm Ω, g ∈ Pgrp G π T ↔ g ∈ G ∧ ∃ h : (∀ c, lab G π g c ∈ T ↔ c ∈ T),
      sign ((lab G π g).subtypePerm h) = 1 ∧
      sign ((lab G π g).subtypePerm (p := fun c => c ∉ T) (fun c => not_congr (h c))) = 1) ∧
    (∀ τ g : Perm Ω, τ ∈ Qgrp G π T → τ ∉ Pgrp G π T → g ∈ Qgrp G π T →
      g ∈ Pgrp G π T ∨ g * τ⁻¹ ∈ Pgrp G π T) :=
  ⟨ker_le_Jgrp, Jgrp_le_Pgrp, Pgrp_le_Qgrp, Qgrp_le, fun _ => mem_Pgrp_iff_preimage,
    fun _ _ hτ hτP hg => Qgrp_eq_union hτ hτP hg⟩

/-! ### Algorithm `alg:local-certificate`: the endpoint construction -/

/-- **Algorithm `alg:local-certificate`** (`LocalCertificate(S, x, T)`) as a
mathematical object: its stages `(A_t, W_t)`. -/
noncomputable def alg_local_certificate (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    (x : Ω → C) (T : Finset Γ) (t : ℕ) : Subgroup (Perm Ω) × Finset Ω :=
  stage (phiT G π T) x t

theorem alg_local_certificate_zero (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    (x : Ω → C) (T : Finset Γ) : alg_local_certificate G π x T 0 = (Pgrp G π T, ∅) := rfl

/-- The update rule 5: `W_{t+1} = W_t ∪ V_t` and `A_{t+1} = Aut^{V_t}_{A_t}(x)`, the
elements of `A_t` that preserve the colors of `x` on the `A_t`-invariant set `V_t`. -/
theorem alg_local_certificate_succ (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    (x : Ω → C) (T : Finset Γ) (t : ℕ) :
    win (phiT G π T) x (t + 1) = win (phiT G π T) x t ∪ inc (phiT G π T) x t ∧
    Invariant (grp (phiT G π T) x t) (inc (phiT G π T) x t) ∧
    ∀ g : Perm Ω, g ∈ grp (phiT G π T) x (t + 1) ↔
      g ∈ grp (phiT G π T) x t ∧ ∀ v ∈ inc (phiT G π T) x t, x (g v) = x v :=
  ⟨rfl, inc_invariant _ x t, fun g => by
    rw [grp_succ]; exact mem_autWindow_iff _ x _ (inc_invariant _ x t) g⟩

/-- "The extra union in step 4 is ... nonempty": at a stage where `φ_T(A_t) = Alt(T)`
but `φ_T((A_t)_{(U_t)}) ≠ Alt(T)`, some `A_t`-orbit `Δ` outside `W_t` has
`φ_T((A_t)_{(Δ)}) = 1`. -/
theorem endpoint_extra_union_nonempty (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    (x : Ω → C) (T : Finset Γ) (hk : 5 ≤ T.card) (t : ℕ)
    (hA : Full (phiT G π T) (grp (phiT G π T) x t))
    (hK : ¬ Full (phiT G π T) (fix (grp (phiT G π T) x t) (outside (win (phiT G π T) x t)))) :
    (extraSet (phiT G π T) (grp (phiT G π T) x t) (win (phiT G π T) x t)).Nonempty := by
  have h5 : 5 ≤ Fintype.card T := by rwa [Fintype.card_coe]
  haveI := GI.AlternatingSimple.isSimple h5
  exact extraSet_nonempty _ (GI.AlternatingSimple.nonabelian h5) (grp_le _ x t)
    (win_invariant _ x t) hA hK

/-- **Prefix recovery** ("For every finite prefix `j`, they satisfy the exact
identity `A_j = Aut_{P_T}(x^{W_j})`"), together with the invariant "`W_i` is
`A_i`-invariant". -/
theorem endpoint_prefix_recovery (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    (x : Ω → C) (T : Finset Γ) (j : ℕ) :
    grp (phiT G π T) x j = automorphisms (Pgrp G π T) (mask x (win (phiT G π T) x j)) ∧
    Invariant (grp (phiT G π T) x j) (win (phiT G π T) x j) :=
  ⟨grp_eq_automorphisms_mask _ x j, win_invariant _ x j⟩

/-- **At most `n` updates.** "Every update adds a nonempty `A_i`-invariant set, so
there are at most `n` updates." Some stage `s ≤ n = |Ω|` is stopped and all
earlier ones are not; every unstopped stage strictly enlarges the window; and
after a stop the stages are constant. -/
theorem endpoint_at_most_n_updates (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    (x : Ω → C) (T : Finset Γ) (hk : 5 ≤ T.card) :
    (∃ s ≤ Fintype.card Ω,
      Stopped (phiT G π T) (grp (phiT G π T) x s) (win (phiT G π T) x s) ∧
      ∀ t < s, ¬ Stopped (phiT G π T) (grp (phiT G π T) x t) (win (phiT G π T) x t)) ∧
    (∀ t, ¬ Stopped (phiT G π T) (grp (phiT G π T) x t) (win (phiT G π T) x t) →
      (inc (phiT G π T) x t).Nonempty ∧
      (win (phiT G π T) x t).card < (win (phiT G π T) x (t + 1)).card) ∧
    (∀ t, Stopped (phiT G π T) (grp (phiT G π T) x t) (win (phiT G π T) x t) →
      ∀ u, t ≤ u → stage (phiT G π T) x u = stage (phiT G π T) x t) := by
  have h5 : 5 ≤ Fintype.card T := by rwa [Fintype.card_coe]
  haveI := GI.AlternatingSimple.isSimple h5
  have hna := GI.AlternatingSimple.nonabelian h5
  refine ⟨⟨stopTime _ hna x, stopTime_le _ hna x, stopTime_stopped _ hna x,
      fun t ht => not_stopped_of_lt_stopTime _ hna x ht⟩,
    fun t ht => ⟨increment_nonempty _ hna (grp_le _ x t) (win_invariant _ x t) ht,
      win_card_lt _ hna x ht⟩,
    fun t ht u hu => stage_eq_of_stopped _ x ht u hu⟩

/-- **Full termination.** "At full termination, `K(T)` preserves `x` on `W_i` and
fixes its complement, so `K(T) ≤ Aut_G(x)` and its image contains the required
alternating group." -/
theorem endpoint_full_certificate (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    (x : Ω → C) (T : Finset Γ) (hk : 5 ≤ T.card) (hfull : IsFull (phiT G π T) x) :
    fullCert (phiT G π T) x ≤ automorphisms G x ∧
    img (phiT G π T) (fullCert (phiT G π T) x) = ⊤ := by
  have h5 : 5 ≤ Fintype.card T := by rwa [Fintype.card_coe]
  haveI := GI.AlternatingSimple.isSimple h5
  obtain ⟨hle, hK⟩ := full_certificate _ (GI.AlternatingSimple.nonabelian h5) x hfull
  exact ⟨fun g hg => ⟨Pgrp_le (hle hg).1, (hle hg).2⟩, hK⟩

/-- **Nonfull termination.** "At nonfull termination, `Aut_{P_T}(x) ≤ A_i` has
proper image. The full setwise group `Aut_{Q_T}(x)` therefore cannot contain
`Alt(T)` in its induced action either." -/
theorem endpoint_nonfull_certificate (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    (x : Ω → C) (T : Finset Γ) (hnf : ¬ IsFull (phiT G π T) x) :
    automorphisms (Pgrp G π T) x ≤ finalGrp (phiT G π T) x ∧
    img (phiT G π T) (automorphisms (Pgrp G π T) x) ≠ ⊤ ∧
    ¬ ∀ σ ∈ alternatingGroup T, ∃ (g : Perm Ω) (hg : g ∈ automorphisms (Qgrp G π T) x),
      restrictQ G π T ⟨g, hg.1⟩ = σ :=
  ⟨(nonfull_certificate _ x hnf).1, (nonfull_certificate _ x hnf).2, nonfull_Q hnf⟩

/-! ### The two recursive call types -/

/-- **Affected orbits** ("For an affected `A_i`-orbit `Δ`, the minimum-index
property of `Alt(k)` gives `|a^{N_i}| = |Δ|/[Alt(k) : φ_T((A_i)_a)] ≤ |Δ|/k`").
At a stage with `φ_T(A) = Alt(T)`, for an affected point `a`:
`|a^{N}| · [Alt(T) : φ_T(A_a)] = |a^{A}|` and `k · |a^{N}| ≤ |a^{A}|`. -/
theorem affected_orbit_call (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    (x : Ω → C) (T : Finset Γ) (hk : 5 ≤ T.card) (t : ℕ) (a : Ω)
    (hA : Full (phiT G π T) (grp (phiT G π T) x t))
    (ha : Affected (phiT G π T) (grp (phiT G π T) x t) a) :
    Nat.card (orb (kernelIn (phiT G π T) (grp (phiT G π T) x t)) a) *
        (img (phiT G π T) (stab (grp (phiT G π T) x t) a)).index =
      Nat.card (orb (grp (phiT G π T) x t) a) ∧
    T.card * Nat.card (orb (kernelIn (phiT G π T) (grp (phiT G π T) x t)) a) ≤
      Nat.card (orb (grp (phiT G π T) x t) a) := by
  have h5 : 5 ≤ Fintype.card T := by rwa [Fintype.card_coe]
  refine ⟨kernel_orbit_card_mul_index _ (grp_le _ x t) hA a, ?_⟩
  have h := affected_kernel_orbit_le _ (k := Fintype.card T)
    (fun H hH => alternating_min_index h5 H hH) (grp_le _ x t) hA ha
  rwa [Fintype.card_coe] at h

/-- **Extra orbits** ("For an extra orbit `Δ` added in step 4, every point is
unaffected, so `N_i` is transitive on `Δ`. The test `φ_T((A_i)_{(Δ)}) = 1`
implies `(A_i|_Δ)/(N_i|_Δ) ≅ Alt(k)`. This is a visible marked step ...
`σ(N_i|_Δ, Δ) ≤ σ(A_i|_Δ, Δ) - κ ≤ σ(G, Ω) - κ`"). Here `k = |T| = κ`, `G` is
transitive, and `v` is an unaffected point with a visible orbit at a full stage. -/
theorem extra_orbit_call (G : Subgroup (Perm Ω)) [MulAction.IsPretransitive G Ω] (α : Ω)
    (π : G →* alternatingGroup Γ) (x : Ω → C) (T : Finset Γ) (hk : 5 ≤ T.card) (t : ℕ)
    (v : Ω) (hA : Full (phiT G π T) (grp (phiT G π T) x t))
    (hv : ¬ Affected (phiT G π T) (grp (phiT G π T) x t) v)
    (hvis : VisibleOrbit (phiT G π T) (grp (phiT G π T) x t) v) :
    orb (kernelIn (phiT G π T) (grp (phiT G π T) x t)) v = orb (grp (phiT G π T) x t) v ∧
    Nonempty (GI.VisibleStep v (grp (phiT G π T) x t)
      (kernelIn (phiT G π T) (grp (phiT G π T) x t)) T.card) ∧
    GI.sigma T.card (GI.activeOrbitBase (kernelIn (phiT G π T) (grp (phiT G π T) x t)) v)
        (GI.faithfulOrbitImage (kernelIn (phiT G π T) (grp (phiT G π T) x t)) v) + T.card ≤
      GI.sigma T.card (GI.activeOrbitBase (grp (phiT G π T) x t) v)
        (GI.faithfulOrbitImage (grp (phiT G π T) x t) v) ∧
    GI.sigma T.card (GI.activeOrbitBase (grp (phiT G π T) x t) v)
        (GI.faithfulOrbitImage (grp (phiT G π T) x t) v) ≤ GI.sigma T.card α G := by
  classical
  have hAP := grp_le (phiT G π T) x t
  let e : alternatingGroup T ≃* alternatingGroup (Fin T.card) :=
    GI.AlternatingSimple.relabel (T.equivFin)
  have hd := extra_sigma_decrease_parent (phiT G π T) hk le_rfl e G α
    (hAP.trans Pgrp_le) hAP hA hv hvis
  exact ⟨orb_kernel_eq_of_unaffected _ hAP hv, ⟨extraVisibleStep _ e hAP hA hv hvis⟩, hd⟩

/-- **Every update has only the two call types**, with the parameters of
Lemma 4.1: for each point `v` of the increment `V_t`, either its kernel orbit has
at most `s/κ` points and the budget of the child is at most `σ(G, Ω)` (type
`(s, σ) ↦ (s/κ, σ)`), or the child has at most `s` points and budget at most
`σ(G, Ω) - κ` (type `(s, σ) ↦ (s, σ - κ)`). Here `s = |Ω|`, `κ = |T|`, and the
child is `N_t` acting on the orbit `v^{N_t}`. -/
theorem certificate_call_types (G : Subgroup (Perm Ω)) [MulAction.IsPretransitive G Ω]
    (α : Ω) (π : G →* alternatingGroup Γ) (x : Ω → C) (T : Finset Γ) (hk : 5 ≤ T.card)
    (t : ℕ) (v : Ω) (hv : v ∈ inc (phiT G π T) x t) :
    (T.card * Nat.card (orb (kernelIn (phiT G π T) (grp (phiT G π T) x t)) v) ≤
        Fintype.card Ω ∧
      GI.sigma T.card (GI.activeOrbitBase (kernelIn (phiT G π T) (grp (phiT G π T) x t)) v)
        (GI.faithfulOrbitImage (kernelIn (phiT G π T) (grp (phiT G π T) x t)) v) ≤
        GI.sigma T.card α G) ∨
    (Nat.card (orb (kernelIn (phiT G π T) (grp (phiT G π T) x t)) v) ≤ Fintype.card Ω ∧
      GI.sigma T.card (GI.activeOrbitBase (kernelIn (phiT G π T) (grp (phiT G π T) x t)) v)
        (GI.faithfulOrbitImage (kernelIn (phiT G π T) (grp (phiT G π T) x t)) v) + T.card ≤
        GI.sigma T.card α G) := by
  classical
  set A := grp (phiT G π T) x t
  set N := kernelIn (phiT G π T) A
  have hAP : A ≤ Pgrp G π T := grp_le _ x t
  have hAG : A ≤ G := hAP.trans Pgrp_le
  have hNG : N ≤ G := inf_le_left.trans hAG
  have horb : ∀ B : Subgroup (Perm Ω), Nat.card (orb B v) ≤ Fintype.card Ω := fun B => by
    rw [← Nat.card_eq_fintype_card]; exact Finite.card_subtype_le _
  have h5 : 5 ≤ Fintype.card T := by rwa [Fintype.card_coe]
  rcases inc_child_types (phiT G π T) (k := T.card)
      (fun H hH => by have := alternating_min_index h5 H hH; rwa [Fintype.card_coe] at this)
      (GI.AlternatingSimple.relabel T.equivFin) x t hv with ⟨_, hle⟩ | ⟨_, ⟨step⟩⟩
  · left
    exact ⟨hle.trans (horb A), GI.Paper.lem_budget_inheritance hk G α hNG v⟩
  · right
    refine ⟨horb N, ?_⟩
    have h1 := GI.sigma_faithfulOrbit_marked_decrease hk le_rfl step
    have h2 := GI.Paper.lem_budget_inheritance hk G α hAG v
    rw [← GI.sigma_faithfulOrbit] at h2
    exact h1.trans h2

/-- **Eq. `constant-recurrence`, counting content.** "The multiplicity absorbs the
at most `n` updates, orbit calls, `k!` cosets, and all test tuples and pairwise
comparisons." For each test set `T` with `|T| = k ≥ 5`: at most `n = |Ω|` updates;
at each update, `N_t` has exactly `|Alt(k)| = k!/2` cosets in `A_t`; the orbit
calls at an update are at most `n` (one per point of `V_t`); and there are `m^k`
test tuples. -/
theorem eq_constant_recurrence_counts (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    (x : Ω → C) (T : Finset Γ) (hk : 5 ≤ T.card) :
    (∃ s ≤ Fintype.card Ω,
      Stopped (phiT G π T) (grp (phiT G π T) x s) (win (phiT G π T) x s)) ∧
    (∀ t, ¬ Stopped (phiT G π T) (grp (phiT G π T) x t) (win (phiT G π T) x t) →
      ((kernelIn (phiT G π T) (grp (phiT G π T) x t)).subgroupOf
          (grp (phiT G π T) x t)).index = T.card.factorial / 2 ∧
      (inc (phiT G π T) x t).card ≤ Fintype.card Ω) ∧
    Fintype.card (Fin T.card → Γ) = Fintype.card Γ ^ T.card := by
  obtain ⟨⟨s, hs, hst, _⟩, _, _⟩ := endpoint_at_most_n_updates G π x T hk
  refine ⟨⟨s, hs, hst⟩, fun t ht => ⟨?_, Finset.card_le_univ _⟩, by simp⟩
  have hA : Full (phiT G π T) (grp (phiT G π T) x t) := by
    by_contra hn; exact ht (Or.inl hn)
  rw [kernel_index_eq_card _ (grp_le _ x t) hA, Nat.card_eq_fintype_card]
  haveI : Nontrivial T := Fintype.one_lt_card_iff_nontrivial.mp
    (by rw [Fintype.card_coe]; omega)
  rw [card_alternatingGroup, Fintype.card_coe]

/-! ### Ordered comparisons and equivariance -/

/-- **Eq. `comparison` and lockstep cosets.** "If nonempty, it is a coset of
`Aut_{J_T}(x^{W_i}) = A_i ∩ J_T = N_i`." Every lockstep comparison set at stage
`j` (in particular the final comparison set, `j = n`) that contains `g₀` equals
`g₀ · Aut_{J_T}(x^{W_j})`. -/
theorem eq_comparison_coset (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ) {k : ℕ}
    (j : ℕ) (x y : Ω → C) (t t' : Fin k → Γ) (g₀ : Perm Ω)
    (hg₀ : g₀ ∈ lockstep G π j x t y t') :
    lockstep G π j x t y t' =
      {g | ∃ a ∈ automorphisms (Jgrp G π (tset t)) (mask x (win (phiT G π (tset t)) x j)),
        g = g₀ * a} ∧
    automorphisms (Jgrp G π (tset t)) (mask x (win (phiT G π (tset t)) x j)) =
      grp (phiT G π (tset t)) x j ⊓ Jgrp G π (tset t) ∧
    grp (phiT G π (tset t)) x j ⊓ Jgrp G π (tset t) =
      kernelIn (phiT G π (tset t)) (grp (phiT G π (tset t)) x j) :=
  ⟨lockstep_eq_coset hg₀, automorphisms_J_eq x (tset t) j⟩

/-- **Lockstep comparison.** "Every representative conjugates `A_i` to the other
endpoint group ... Therefore it maps affected sets, the extra orbit union, and
stopping tests to the corresponding objects at the other endpoint. The next
comparison is string isomorphism on the new window under `N_i`." A member of the
lockstep coset at stage `j` conjugates the earlier groups, maps the earlier
windows and the increment `V_j`, and the stopping tests agree; the stage-`j+1`
coset is cut out of the stage-`j` coset by agreement on `V_j`. -/
theorem lockstep_comparison (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ) {k : ℕ}
    (j : ℕ) (x y : Ω → C) (t t' : Fin k → Γ) :
    (∀ g ∈ lockstep G π j x t y t',
      (∀ i ≤ j, grp (phiT G π (tset t')) y i = cmap g (grp (phiT G π (tset t)) x i) ∧
        win (phiT G π (tset t')) y i = wmap g (win (phiT G π (tset t)) x i)) ∧
      inc (phiT G π (tset t')) y j = wmap g (inc (phiT G π (tset t)) x j) ∧
      (Stopped (phiT G π (tset t')) (grp (phiT G π (tset t')) y j)
          (win (phiT G π (tset t')) y j) ↔
        Stopped (phiT G π (tset t)) (grp (phiT G π (tset t)) x j)
          (win (phiT G π (tset t)) x j))) ∧
    lockstep G π (j + 1) x t y t' =
      {g | g ∈ lockstep G π j x t y t' ∧ ∀ v ∈ inc (phiT G π (tset t)) x j, y (g v) = x v} :=
  ⟨fun _ hg => lockstep_conj hg, lockstep_succ j x y t t'⟩

/-- **"An empty partial comparison cannot revive at the final windows."** Any `g`
in the final comparison set lies in every earlier lockstep comparison coset and
conjugates the endpoint groups and windows; the full tests and the stopping
tests at every stage agree ("incompatible stopping stages give an empty
comparison"). -/
theorem comparison_cannot_revive (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    {k : ℕ} (x y : Ω → C) (t t' : Fin k → Γ) (g : Perm Ω)
    (hg : g ∈ comparison G π x t y t') :
    (∀ j ≤ Fintype.card Ω, g ∈ lockstep G π j x t y t' ∧
      grp (phiT G π (tset t')) y j = cmap g (grp (phiT G π (tset t)) x j) ∧
      win (phiT G π (tset t')) y j = wmap g (win (phiT G π (tset t)) x j)) ∧
    (IsFull (phiT G π (tset t')) y ↔ IsFull (phiT G π (tset t)) x) ∧
    ∀ j ≤ Fintype.card Ω,
      (Stopped (phiT G π (tset t')) (grp (phiT G π (tset t')) y j)
          (win (phiT G π (tset t')) y j) ↔
        Stopped (phiT G π (tset t)) (grp (phiT G π (tset t)) x j)
          (win (phiT G π (tset t)) x j)) :=
  ⟨comparison_lockstep hg, comparison_isFull_iff hg⟩

/-- **The endpoint identity** `Aut_{P_T}(x^{W(x,T)}) = A_final`. -/
theorem comparison_endpoint_identity (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    (x : Ω → C) (T : Finset Γ) :
    automorphisms (Pgrp G π T) (mask x (finalWin (phiT G π T) x)) = finalGrp (phiT G π T) x :=
  (grp_eq_automorphisms_mask _ x _).symm

/-- **Comparison is an equivalence relation** ("Full transporter composition and
inversion make nonemptiness in (comparison) a genuine equivalence relation"). -/
theorem comparison_equivalence (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ) (k : ℕ) :
    Equivalence (CompareRel (C := C) G π k) :=
  compareRel_equivalence

/-- **Equivariance under parent isomorphisms.** A parent isomorphism `g ∈ G` with
`x^g = y` maps the endpoint procedure of `(x, T)` to that of `(y, T^{π(g)})`
(groups conjugated, windows mapped, the full test and the full certificate
preserved), and lies in the comparison set of `(x, t)` and `(y, π(g) t)`. -/
theorem comparison_equivariance (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    {x y : Ω → C} {g : Perm Ω} (hgG : g ∈ G) (hxy : Transports x y g) :
    (∀ (T : Finset Γ) (j : ℕ),
      grp (phiT G π (wmap (lab G π g) T)) y j = cmap g (grp (phiT G π T) x j) ∧
      win (phiT G π (wmap (lab G π g) T)) y j = wmap g (win (phiT G π T) x j)) ∧
    (∀ T : Finset Γ, (IsFull (phiT G π (wmap (lab G π g) T)) y ↔ IsFull (phiT G π T) x) ∧
      fullCert (phiT G π (wmap (lab G π g) T)) y = cmap g (fullCert (phiT G π T) x)) ∧
    ∀ {k : ℕ} (t : Fin k → Γ), g ∈ comparison G π x t y (fun i => lab G π g (t i)) :=
  ⟨fun T j => ⟨(certificate_of_iso hgG hxy T j).1, (certificate_of_iso hgG hxy T j).2.1⟩,
    fun T => ⟨(certificate_of_iso hgG hxy T _).2.2, fullCert_of_iso hgG hxy T⟩,
    fun t => comparison_of_iso hgG hxy t⟩

/-- **The extension to noninjective tuples.** "Extend this coloring from injective
tuples to all of `Γ^k` by giving each noninjective tuple its equality-pattern
color, in a palette disjoint from the injective colors. ... This extension is
equivariant." The relation is an equivalence relation, agrees with the
comparison relation on injective tuples, never relates an injective tuple to a
noninjective one, and is preserved by parent isomorphisms. -/
theorem noninjective_extension (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ) (k : ℕ) :
    Equivalence (tupleRel (C := C) G π k) ∧
    (∀ a b : (Ω → C) × (Fin k → Γ), Function.Injective a.2 → Function.Injective b.2 →
      (tupleRel G π k a b ↔ CompareRel G π k a b)) ∧
    (∀ a b : (Ω → C) × (Fin k → Γ), Function.Injective a.2 → ¬ Function.Injective b.2 →
      ¬ tupleRel G π k a b) ∧
    (∀ {x y : Ω → C} {g : Perm Ω}, g ∈ G → Transports x y g → ∀ t : Fin k → Γ,
      tupleRel G π k (x, t) (y, fun i => lab G π g (t i))) := by
  refine ⟨tupleRel_equivalence, fun a b ha hb => ?_, fun a b ha hb => ?_,
    fun hgG hxy t => tupleRel_of_iso hgG hxy t⟩
  · constructor
    · rintro (⟨_, _, h⟩ | ⟨h, _, _⟩)
      · exact h
      · exact absurd ha h
    · intro h; exact Or.inl ⟨ha, hb, h⟩
  · rintro (⟨_, h, _⟩ | ⟨h, _, _⟩)
    · exact hb h
    · exact h ha

/-- **No large twins** ("If all orderings of a nonfull `T` had the same color,
their transporters would realize all of `Sym(T)` on the final marked window. Its
even part would force `φ_T(A_i) = Alt(T)`, a contradiction."). -/
theorem no_large_twin (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ) {k : ℕ}
    (x : Ω → C) (t₀ : Fin k → Γ) (ht₀ : Function.Injective t₀)
    (hnf : ¬ IsFull (phiT G π (tset t₀)) x) :
    ∃ t₁ : Fin k → Γ, Function.Injective t₁ ∧ tset t₁ = tset t₀ ∧
      ¬ CompareRel G π k (x, t₀) (x, t₁) :=
  GI.LocalCertificates.no_large_twin ht₀ hnf

/-! ### Lemma 4.1 -/

/-- **Lemma 4.1** (`lem:main-local-test`, Local-test interface), mathematical
content. Let `G ≤ Sym(Ω)` be transitive, `s = |Ω|`, `π : G ↠ Alt(Γ)`, and let
`κ = k ≥ 5` be the test size.

1. For every string `x` and every `k`-set `T`, the endpoint procedure stops after
   at most `s` updates, with a full certificate (`K(T) ≤ Aut_G(x)` with image
   `Alt(T)`) or a nonfull one (`φ_T(Aut_{P_T}(x)) ≠ Alt(T)`).
2. Every recursive call made at an update has one of the two types
   `(s, σ) ↦ (s/κ, σ)` and `(s, σ) ↦ (s, σ - κ)` (`σ = σ(G, Ω)`, the child being
   `N_t` on a kernel orbit).
3. "Every comparison returns the complete isomorphism coset": a nonempty
   comparison set is a full coset `g₀ · Aut_{J_T}(x^{W(x,T)})`.
4. "The certificates and the equality classes of ordered comparisons are
   preserved by all parent isomorphisms": comparison is an equivalence relation,
   and a parent isomorphism `g` relates `(x, t)` to `(y, π(g) t)` and carries the
   certificate of `(x, T)` to that of `(y, T^{π(g)})`.

The polynomial bounds on the structural work and on the number of calls are
algorithmic and left to the machine level (see the module docstring); their counting content is
`eq_constant_recurrence_counts`. -/
theorem lem_main_local_test (G : Subgroup (Perm Ω)) [MulAction.IsPretransitive G Ω] (α : Ω)
    (π : G →* alternatingGroup Γ) (k : ℕ) (hk : 5 ≤ k) :
    -- 1. Certificates.
    (∀ (x : Ω → C) (T : Finset Γ), T.card = k →
      (∃ s ≤ Fintype.card Ω,
        Stopped (phiT G π T) (grp (phiT G π T) x s) (win (phiT G π T) x s)) ∧
      (IsFull (phiT G π T) x → fullCert (phiT G π T) x ≤ automorphisms G x ∧
        img (phiT G π T) (fullCert (phiT G π T) x) = ⊤) ∧
      (¬ IsFull (phiT G π T) x → img (phiT G π T) (automorphisms (Pgrp G π T) x) ≠ ⊤)) ∧
    -- 2. The two recursive call types.
    (∀ (x : Ω → C) (T : Finset Γ), T.card = k → ∀ (t : ℕ), ∀ v ∈ inc (phiT G π T) x t,
      (k * Nat.card (orb (kernelIn (phiT G π T) (grp (phiT G π T) x t)) v) ≤
          Fintype.card Ω ∧
        GI.sigma k (GI.activeOrbitBase (kernelIn (phiT G π T) (grp (phiT G π T) x t)) v)
          (GI.faithfulOrbitImage (kernelIn (phiT G π T) (grp (phiT G π T) x t)) v) ≤
          GI.sigma k α G) ∨
      (Nat.card (orb (kernelIn (phiT G π T) (grp (phiT G π T) x t)) v) ≤ Fintype.card Ω ∧
        GI.sigma k (GI.activeOrbitBase (kernelIn (phiT G π T) (grp (phiT G π T) x t)) v)
          (GI.faithfulOrbitImage (kernelIn (phiT G π T) (grp (phiT G π T) x t)) v) + k ≤
          GI.sigma k α G)) ∧
    -- 3. Complete comparison cosets.
    (∀ (x y : Ω → C) (t t' : Fin k → Γ) (g₀ : Perm Ω), g₀ ∈ comparison G π x t y t' →
      comparison G π x t y t' =
        {g | ∃ a ∈ automorphisms (Jgrp G π (tset t)) (mask x (finalWin (phiT G π (tset t)) x)),
          g = g₀ * a}) ∧
    -- 4. Equivariance.
    Equivalence (CompareRel (C := C) G π k) ∧
    (∀ (x y : Ω → C) (g : Perm Ω), g ∈ G → Transports x y g →
      (∀ t : Fin k → Γ, CompareRel G π k (x, t) (y, fun i => lab G π g (t i))) ∧
      ∀ T : Finset Γ,
        finalGrp (phiT G π (wmap (lab G π g) T)) y = cmap g (finalGrp (phiT G π T) x) ∧
        finalWin (phiT G π (wmap (lab G π g) T)) y = wmap g (finalWin (phiT G π T) x) ∧
        (IsFull (phiT G π (wmap (lab G π g) T)) y ↔ IsFull (phiT G π T) x)) := by
  refine ⟨fun x T hT => ?_, fun x T hT t v hv => ?_, fun x y t t' g₀ hg₀ => ?_,
    compareRel_equivalence, fun x y g hgG hxy => ?_⟩
  · subst hT
    obtain ⟨⟨s, hs, hst, _⟩, _, _⟩ := endpoint_at_most_n_updates G π x T hk
    exact ⟨⟨s, hs, hst⟩, endpoint_full_certificate G π x T hk,
      fun hnf => (endpoint_nonfull_certificate G π x T hnf).2.1⟩
  · subst hT
    exact certificate_call_types G α π x T hk t v hv
  · exact lockstep_eq_coset hg₀
  · obtain ⟨h1, h2, h3⟩ := comparison_equivariance G π hgG hxy
    exact ⟨fun t => ⟨g, h3 t⟩, fun T => ⟨(h1 T _).1, (h1 T _).2, (h2 T).1⟩⟩

end GI.Paper
