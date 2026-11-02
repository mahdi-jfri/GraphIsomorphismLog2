import Workspace.CertificateTermination
import Workspace.SupportIndexGap
import Workspace.Paper.HereditaryBudgetBasic

/-!
# The two recursive call types of the endpoint procedure

Paper, Appendix A, `sec:certificates`, "The two recursive call types".

At an update let `N_i = ker(φ_T|_{A_i})` (`kernelIn phi A`).

* **Affected orbits.** "For an affected `A_i`-orbit `Δ`, the minimum-index
  property of `Alt(k)` gives `|a^{N_i}| = |Δ| / [Alt(k) : φ_T((A_i)_a)] ≤ |Δ|/k`."
  (`kernel_orbit_card_mul_index`, `affected_kernel_orbit_le`).
* **Extra orbits.** "For an extra orbit `Δ` added in step 4, every point is
  unaffected, so `N_i` is transitive on `Δ`. The test `φ_T((A_i)_{(Δ)}) = 1`
  implies `(A_i|_Δ)/(N_i|_Δ) ≅ Alt(k)`. This is a visible marked step ...
  `σ(N_i|_Δ, Δ) ≤ σ(A_i|_Δ, Δ) - κ ≤ σ(G, Ω) - κ`."
  (`kernel_transitive_of_unaffected`, `extraVisibleStep`, `extra_sigma_decrease`).

Only the unaffectedness of the chosen base point is used for transitivity.
The minimum-index property of `Alt(k)`, `k ≥ 5`, is proved
(`alternating_min_index`): a proper subgroup gives a faithful coset action of
the simple group.
-/

namespace GI.Endpoint

open Equiv Equiv.Perm

/-! ### The minimum-index property of `Alt(k)` -/

/-- **Minimum index of `Alt(k)`**: for `|α| = k ≥ 5`, every proper subgroup of
`Alt(α)` has index at least `k`. -/
theorem alternating_min_index {α : Type*} [Fintype α] [DecidableEq α]
    (hk : 5 ≤ Fintype.card α) (H : Subgroup (alternatingGroup α)) (hH : H ≠ ⊤) :
    Fintype.card α ≤ H.index := by
  haveI : IsSimpleGroup (alternatingGroup α) := GI.AlternatingSimple.isSimple hk
  haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hle := GI.SupportThresholds.card_le_factorial_index H hH
  have h2 := two_mul_card_alternatingGroup (α := α)
  rw [Fintype.card_perm, ← Nat.card_eq_fintype_card] at h2
  by_contra hlt
  push Not at hlt
  set k := Fintype.card α
  have hf : H.index.factorial ≤ (k - 1).factorial := Nat.factorial_le (by omega)
  have hk1 : k.factorial = k * (k - 1).factorial := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [Nat.factorial_succ, show k - 1 + 1 = k by omega]
  have hpos := Nat.factorial_pos (k - 1)
  nlinarith

/-! ### Orbit sizes of the kernel -/

section Index

variable {G Q : Type*} [Group G] [Group Q]

theorem relIndex_mul_index_sup [Finite G] (H N : Subgroup G) [N.Normal] :
    H.relIndex N * (H ⊔ N).index = H.index := by
  have hpos : 0 < N.relIndex H :=
    Nat.pos_of_ne_zero (N.subgroupOf H).index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc
    (H.relIndex N * (H ⊔ N).index) * N.relIndex H =
        H.relIndex N * (N.relIndex (H ⊔ N) * (H ⊔ N).index) := by
      rw [Subgroup.relIndex_sup_right]
      ac_rfl
    _ = H.relIndex N * N.index := by rw [Subgroup.relIndex_mul_index le_sup_right]
    _ = (H ⊓ N).index := by
      rw [← Subgroup.inf_relIndex_right H N]
      exact Subgroup.relIndex_mul_index inf_le_right
    _ = N.relIndex H * H.index := by
      rw [← Subgroup.inf_relIndex_left H N]
      exact (Subgroup.relIndex_mul_index inf_le_left).symm
    _ = H.index * N.relIndex H := Nat.mul_comm _ _

/-- For a surjection `q : G ↠ Q`, the orbit of the kernel has size
`|a^G| / [Q : q(G_a)]`. -/
theorem kernel_orbit_card_factorization {X : Type*} [Finite G] [MulAction G X]
    (q : G →* Q) (hq : Function.Surjective q) (a : X) :
    Nat.card (MulAction.orbit q.ker a) * ((MulAction.stabilizer G a).map q).index =
      Nat.card (MulAction.orbit G a) := by
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer q.ker a),
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G a),
    ← Subgroup.index_eq_card, ← Subgroup.index_eq_card]
  have hst : MulAction.stabilizer q.ker a = (MulAction.stabilizer G a).subgroupOf q.ker := by
    ext g; rfl
  rw [hst, Subgroup.index_map, MonoidHom.range_eq_top.mpr hq, Subgroup.index_top, mul_one]
  exact relIndex_mul_index_sup _ _

end Index

variable {V Q : Type*} [Group Q] [DecidableEq V] [Fintype V]
  {P : Subgroup (Perm V)} (phi : P →* Q)

omit [DecidableEq V] [Fintype V] in
theorem orbit_ker_eq_orb {A : Subgroup (Perm V)} (hAP : A ≤ P) (v : V) :
    (MulAction.orbit (restrictTo phi hAP).ker v : Set V) = orb (kernelIn phi A) v := by
  ext w
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨((k : A) : Perm V), (mem_kernelIn phi).2 ⟨(k : A).2, hAP (k : A).2, k.2⟩, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨hnA, hnP, hn1⟩ := (mem_kernelIn phi).1 hn
    exact ⟨⟨⟨n, hnA⟩, hn1⟩, rfl⟩

omit [DecidableEq V] [Fintype V] in
theorem orbit_eq_orb (A : Subgroup (Perm V)) (v : V) :
    (MulAction.orbit A v : Set V) = orb A v := (orb_eq_orbit A v).symm

omit [DecidableEq V] [Fintype V] in
theorem stabilizer_map_eq_img {A : Subgroup (Perm V)} (hAP : A ≤ P) (v : V) :
    (MulAction.stabilizer A v).map (restrictTo phi hAP) = img phi (stab A v) := by
  ext q
  rw [mem_img, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, hAP a.2⟩, mem_stab.2 ⟨a.2, ha⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨haA, hav⟩ := mem_stab.1 ha
    exact ⟨⟨a, haA⟩, hav, rfl⟩

omit [DecidableEq V] in
/-- The exact orbit identity `|a^{N}| · [Q : φ(A_a)] = |a^{A}|` at a full stage. -/
theorem kernel_orbit_card_mul_index {A : Subgroup (Perm V)} (hAP : A ≤ P) (hA : Full phi A)
    (v : V) :
    Nat.card (orb (kernelIn phi A) v) * (img phi (stab A v)).index = Nat.card (orb A v) := by
  have h := kernel_orbit_card_factorization (restrictTo phi hAP)
    (restrictTo_surjective phi hAP hA) v
  rw [stabilizer_map_eq_img] at h
  have e1 := orbit_ker_eq_orb phi hAP v
  have e2 := orbit_eq_orb A v
  rw [← e1, ← e2]
  exact h

omit [DecidableEq V] in
/-- **Affected orbits.** If every proper subgroup of `Q` has index at least `k`
(the minimum-index property of `Alt(k)`), the kernel orbit of an affected point
has size at most `|Δ|/k`, where `Δ = v^{A}`. -/
theorem affected_kernel_orbit_le {k : ℕ} (hmin : ∀ H : Subgroup Q, H ≠ ⊤ → k ≤ H.index)
    {A : Subgroup (Perm V)} (hAP : A ≤ P) (hA : Full phi A) {v : V} (hv : Affected phi A v) :
    k * Nat.card (orb (kernelIn phi A) v) ≤ Nat.card (orb A v) := by
  rw [← kernel_orbit_card_mul_index phi hAP hA v, mul_comm]
  exact Nat.mul_le_mul_left _ (hmin _ hv)

omit [DecidableEq V] [Fintype V] in
/-- At a full stage, `N` has `|Q|` cosets in `A` ("Enumerate its `|Alt(k)|`
cosets in `A_i`"). -/
theorem kernel_index_eq_card {A : Subgroup (Perm V)} (hAP : A ≤ P) (hA : Full phi A) :
    ((kernelIn phi A).subgroupOf A).index = Nat.card Q := by
  have hk : (kernelIn phi A).subgroupOf A = (restrictTo phi hAP).ker := by
    ext a
    rw [Subgroup.mem_subgroupOf, mem_kernelIn, MonoidHom.mem_ker, restrictTo_apply]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨a.2, hAP a.2, h⟩⟩
  rw [hk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (restrictTo_surjective phi hAP hA)]
  exact Subgroup.card_top

/-! ### Extra orbits -/

omit [DecidableEq V] [Fintype V] in
/-- **The kernel is transitive on an unaffected orbit.** If the base point `v` is
unaffected, `N` is transitive on `Δ = v^{A}`. -/
theorem kernel_transitive_of_unaffected {A : Subgroup (Perm V)} (hAP : A ≤ P) {v : V}
    (hv : ¬ Affected phi A v) (h : A) :
    ∃ n ∈ kernelIn phi A, n v = (h : Perm V) v := by
  rw [Affected, not_not] at hv
  have hq : phi ⟨h, hAP h.2⟩ ∈ img phi (stab A v) := by rw [hv]; trivial
  obtain ⟨s, hs, hse⟩ := (mem_img phi).1 hq
  obtain ⟨hsA, hsv⟩ := mem_stab.1 hs
  refine ⟨(h : Perm V) * (s : Perm V)⁻¹, (mem_kernelIn phi).2
    ⟨A.mul_mem h.2 (A.inv_mem hsA), P.mul_mem (hAP h.2) (P.inv_mem s.2), ?_⟩, ?_⟩
  · have : (⟨(h : Perm V) * (s : Perm V)⁻¹, P.mul_mem (hAP h.2) (P.inv_mem s.2)⟩ : P) =
        ⟨h, hAP h.2⟩ * s⁻¹ := rfl
    rw [this, map_mul, map_inv, hse, mul_inv_cancel]
  · have : (s : Perm V)⁻¹ v = v := by
      conv_lhs => rw [← hsv]
      simp
    simp [Perm.mul_apply, this]

omit [DecidableEq V] [Fintype V] in
theorem orb_kernel_eq_of_unaffected {A : Subgroup (Perm V)} (hAP : A ≤ P) {v : V}
    (hv : ¬ Affected phi A v) : orb (kernelIn phi A) v = orb A v := by
  ext w
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, ((mem_kernelIn phi).1 hn).1, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨n, hn, hnv⟩ := kernel_transitive_of_unaffected phi hAP hv ⟨a, ha⟩
    exact ⟨n, hn, hnv⟩

omit [DecidableEq V] in
/-- **The visible marked step on an extra orbit.** At a full stage, if `v` is
unaffected and `φ(A_{(Δ)}) = 1` for `Δ = v^A`, then `A ≥ N` is a marked step of
eq. `visible-mark` at the active point `v`, with weight `k` (given `Q ≅ Alt(k)`). -/
def extraVisibleStep {k : ℕ} (e : Q ≃* alternatingGroup (Fin k)) {A : Subgroup (Perm V)}
    (hAP : A ≤ P) (hA : Full phi A) {v : V} (hv : ¬ Affected phi A v)
    (hvis : VisibleOrbit phi A v) : GI.VisibleStep v A (kernelIn phi A) k where
  lower := inf_le_left
  quotient := e.toMonoidHom.comp (restrictTo phi hAP)
  onto := e.surjective.comp (restrictTo_surjective phi hAP hA)
  kernel h := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      restrictTo_apply, mem_kernelIn]
    exact ⟨fun h1 => ⟨h.2, hAP h.2, h1⟩, fun ⟨_, _, h1⟩ => h1⟩
  transitiveKernel h := by
    obtain ⟨n, hn, hnv⟩ := kernel_transitive_of_unaffected phi hAP hv h
    exact ⟨⟨n, hn⟩, hnv⟩
  visible h hfix := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      restrictTo_apply]
    have hmem : phi ⟨h, hAP h.2⟩ ∈ img phi (fix A (orb A v)) := by
      refine (mem_img phi).2 ⟨⟨h, hAP h.2⟩, mem_fix.2 ⟨h.2, ?_⟩, rfl⟩
      rintro _ ⟨g, hg, rfl⟩
      exact hfix ⟨g, hg⟩
    rw [hvis] at hmem
    exact hmem

omit [DecidableEq V] in
/-- **The budget decrease on an extra orbit**:
`σ(N|_Δ, Δ) + k ≤ σ(A|_Δ, Δ)` for the faithful images on the active orbits. -/
theorem extra_sigma_decrease {kcert k : ℕ} (hk5 : 5 ≤ kcert) (hk : kcert ≤ k)
    (e : Q ≃* alternatingGroup (Fin k)) {A : Subgroup (Perm V)} (hAP : A ≤ P)
    (hA : Full phi A) {v : V} (hv : ¬ Affected phi A v) (hvis : VisibleOrbit phi A v)
    [Fintype (GI.ActiveOrbit (kernelIn phi A) v)] [Fintype (GI.ActiveOrbit A v)] :
    GI.sigma kcert (GI.activeOrbitBase (kernelIn phi A) v)
        (GI.faithfulOrbitImage (kernelIn phi A) v) + k ≤
      GI.sigma kcert (GI.activeOrbitBase A v) (GI.faithfulOrbitImage A v) := by
  have h := GI.sigma_faithfulOrbit_marked_decrease hk5 hk (extraVisibleStep phi e hAP hA hv hvis)
  rwa [GI.sigma_faithfulOrbit kcert A v] at h

omit [DecidableEq V] in
/-- `σ(N|_Δ, Δ) + k ≤ σ(A|_Δ, Δ) ≤ σ(G, Ω)` when `A ≤ G` and `G` is transitive
("The second inequality uses the transitivity of the physical parent and
inherited passage to the `A_i`-orbit `Δ`", Lemma A.3). -/
theorem extra_sigma_decrease_parent {kcert k : ℕ} (hk5 : 5 ≤ kcert) (hk : kcert ≤ k)
    (e : Q ≃* alternatingGroup (Fin k)) (G : Subgroup (Perm V))
    [MulAction.IsPretransitive G V] (α : V) {A : Subgroup (Perm V)} (hAG : A ≤ G)
    (hAP : A ≤ P) (hA : Full phi A) {v : V} (hv : ¬ Affected phi A v)
    (hvis : VisibleOrbit phi A v)
    [Fintype (GI.ActiveOrbit (kernelIn phi A) v)] [Fintype (GI.ActiveOrbit A v)] :
    GI.sigma kcert (GI.activeOrbitBase (kernelIn phi A) v)
        (GI.faithfulOrbitImage (kernelIn phi A) v) + k ≤
      GI.sigma kcert (GI.activeOrbitBase A v) (GI.faithfulOrbitImage A v) ∧
    GI.sigma kcert (GI.activeOrbitBase A v) (GI.faithfulOrbitImage A v) ≤
      GI.sigma kcert α G :=
  ⟨extra_sigma_decrease phi hk5 hk e hAP hA hv hvis,
    GI.Paper.lem_budget_inheritance hk5 G α hAG v⟩

/-! ### Every child of an update has one of the two types -/

variable {C : Type*}

/-- At every stage, every point `v` of the increment `V_t` is of one of the two
types: an affected point, whose kernel orbit has at most `|v^{A_t}|/k` points; or
a point of an extra orbit, on which `N_t` is transitive and the step `A_t ≥ N_t`
is a visible marked step. -/
theorem inc_child_types {k : ℕ} (hmin : ∀ H : Subgroup Q, H ≠ ⊤ → k ≤ H.index)
    (e : Q ≃* alternatingGroup (Fin k)) (x : V → C) (t : ℕ) {v : V}
    (hv : v ∈ inc phi x t) :
    (Affected phi (grp phi x t) v ∧
      k * Nat.card (orb (kernelIn phi (grp phi x t)) v) ≤ Nat.card (orb (grp phi x t) v)) ∨
    (orb (kernelIn phi (grp phi x t)) v = orb (grp phi x t) v ∧
      Nonempty (GI.VisibleStep v (grp phi x t) (kernelIn phi (grp phi x t)) k)) := by
  classical
  have hAP := grp_le phi x t
  set A := grp phi x t
  set W := win phi x t
  change v ∈ increment phi A W at hv
  by_cases hA : Full phi A
  swap
  · simp [increment, hA] at hv
  by_cases hE : (affectedSet phi A W).Nonempty
  · simp only [increment, hA, not_true_eq_false, ↓reduceIte, hE] at hv
    have ha := ((mem_affectedSet phi).1 hv).2
    exact Or.inl ⟨ha, affected_kernel_orbit_le phi hmin hAP hA ha⟩
  by_cases hK : Full phi (fix A (outside W))
  · simp [increment, hA, hE, hK] at hv
  simp only [increment, hA, not_true_eq_false, ↓reduceIte, hE, hK] at hv
  obtain ⟨hvW, hvis⟩ := (mem_extraSet phi).1 hv
  have hun : ¬ Affected phi A v := by
    intro ha
    exact hE ⟨v, (mem_affectedSet phi).2 ⟨hvW, ha⟩⟩
  exact Or.inr ⟨orb_kernel_eq_of_unaffected phi hAP hun,
    ⟨extraVisibleStep phi e hAP hA hun hvis⟩⟩

end GI.Endpoint
