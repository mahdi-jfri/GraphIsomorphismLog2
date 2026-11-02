import Workspace.MulticosetRadical
import Workspace.MulticosetTerminal

/-!
# Paper statements: Section A, "Exact quotient algorithms and a transitive-kernel terminal"

Faithful statements for `sec:quotient-algorithms`:

* the implicit object model: coset objects `GI.Multicoset.cobj L c h = (c, L_c h)` with the
  right action, transporters `GI.Multicoset.Iso H X Y = {h ∈ H : X^h = Y}`;
* Lemma A.19 (`lem:solvable-supplement`) and the two paragraphs after it (restriction to
  the supplement, rebasing into the orbits of a normal subgroup `R`);
* Theorem A.20 (`thm:solvable-multicoset`): the procedure `GI.Multicoset.solvableTransport`,
  its correctness, its recursion count, and the bound `exp(O(log(b+M+2) log(b+2)))`;
* Corollary A.22 (`cor:transitive-kernel-multicoset`): the procedure
  `GI.Multicoset.radicalTransport`, its correctness and its bound;
* Theorem A.23 (`thm:transitive-gat-terminal`): the procedure
  `GI.Multicoset.terminalTransport`, its correctness, the zero-sum and parity test, and the
  bounds.

Corollaries A.22 and A.23 here take the radical index bound as a hypothesis `hidx`.
Lemma A.21 and the discharge of `hidx` (with `N` transitive) are in
`Workspace/Paper/RadicalFreeOrder.lean`.

## Conventions

Right actions, as in the paper: `x ↼ g` is `x^g` and `x ↼ (g * h) = (x ↼ g) ↼ h`. A kernel
`N ◁ H` of subgroups of an ambient group `G` is written `N ≤ H` and `Normalizes H N`. The
orbit colors are a type `κ` with subgroups `L c`; the tag `c` keeps colors distinct even when
two subgroups agree (`GI.Multicoset.cobj_ne_of_tag_ne`).

## Stage 1 and the clauses left to stage 2

The procedures are Lean functions on subgroups, cosets and multisets, following the paper's
recursion (`GI.Multicoset.proc`). Each returns its set and the number of procedure calls in
its recursion tree. The steps that the paper performs with cited algorithms appear as their
mathematical results:

* point stabilizers and point transporters of solvable groups ([LM, Proposition 3.9]);
* normalized-product factorization and normalized intersections ([LM, Theorem 3.1(viii)]);
* Sylow construction and conjugacy in Lemma A.19 ([LM, Theorem 3.1(viii),(xi)]);
* the integer Hermite and Smith normal forms ([Kannan-Bachem]) and the vector stabilizer
  and vector transporter of [LM, Theorem 1.4 and Section 5.2] in the affine step: the
  procedure chooses an element `g` of the target profile stabilizer that solves the affine
  condition, when one exists (`GI.Multicoset.glue`);
* constructing the radical preimage (chief series, quotient centralizers [LM, Lemma 3.2]) and
  enumerating its cosets in Corollary A.22.

Deferred to stage 2 (machine): "can be found deterministically in polynomial time in `b`"
(A.19); "computable deterministically in `exp(O(log(b+M+2) log(b+2)))` time" (A.20: the
per-call polynomial work `P(b, M)` and the bit bounds of the abelian coordinates); "has
deterministic running time ..." (A.22: the per-coset overhead).
-/

namespace GI.Paper

open GI.Multicoset

universe u

/-! ### The implicit object model -/

/-- **The implicit object model** ("Since `N` fixes every object, this action factors
through `H/N`"; "the stabilizer of `Lh` is `R ∩ L^h` ... It still contains `N`"; "two objects
`Lh, Lk` of the same original color lie in one `R`-orbit exactly when `hk⁻¹ ∈ LR`"). Here
`L^h = h⁻¹ L h` (`conjR`), as for right actions. -/
theorem sec_quotient_object_model {G : Type*} [Group G] {κ : Type*} (L : κ → Subgroup G)
    {H N R : Subgroup G} (hn : Normalizes H N) (hR : Normalizes H R) (hNR : N ≤ R) (c : κ)
    (hNL : N ≤ L c) {h k : G} (hh : h ∈ H) (hk : k ∈ H) :
    (∀ n ∈ N, cobj L c h ↼ n = cobj L c h) ∧
    Aut R (cobj L c h) = R ⊓ conjR (L c) h ∧ N ≤ Aut R (cobj L c h) ∧
    ((∃ r ∈ R, cobj L c h ↼ r = cobj L c k) ↔ ∃ l ∈ L c, ∃ r ∈ R, h * k⁻¹ = l * r) :=
  ⟨fun _ hN => cobj_act_kernel hNL hn hh hN, aut_cobj R L c h,
    kernel_le_aut_cobj hNR hNL hn hh, cobj_same_orbit_iff hR hk⟩

/-- In the coset model, `N` fixes every listed object. -/
theorem fixes_of_cobj {G : Type*} [Group G] {κ : Type*} {L : κ → Subgroup G}
    {H N : Subgroup G} (hn : Normalizes H N) (hNL : ∀ c, N ≤ L c) {X : Multiset (CObj κ G)}
    (hX : ∀ o ∈ X, ∃ c, ∃ h ∈ H, o = cobj L c h) : Fixes N X := by
  intro n hN o ho
  obtain ⟨c, h, hh, rfl⟩ := hX o ho
  exact cobj_act_kernel (hNL c) hn hh hN

/-! ### Lemma A.19 -/

/-- **Lemma A.19** (`lem:solvable-supplement`), mathematical content: if `H/N` is solvable,
there is a solvable `S ≤ H` with `SN = H`. The proof is the paper's Frattini descent
(`GI.Multicoset.frattini_descent`). Stated for any finite ambient group; the paper's
`H ≤ Sym(B)` is a special case. Deferred: "can be found deterministically in polynomial
time in `b`". -/
theorem lem_solvable_supplement {G : Type*} [Group G] [Finite G] {H N : Subgroup G}
    (hNH : N ≤ H) [(N.subgroupOf H).Normal] [IsSolvable (H ⧸ N.subgroupOf H)] :
    ∃ S : Subgroup G, S ≤ H ∧ IsSolvable S ∧ S ⊔ N = H :=
  exists_solvable_supplement_descent hNH (normalizes_of_normal hNH)

/-- The paragraph after Lemma A.19, "Restriction to `S` loses no object permutation":
with `NS = H` and `N ≤ L`,
* each generator `l = n_l s_l` of `L` gives `L ∩ S = ⟨S ∩ N, s_l⟩`;
* `Lh = Ls` when `h = ns`, and every object `Lh`, `h ∈ H`, is some `Ls`, `s ∈ S`;
* `(L ∩ S)s ↦ Ls` is injective on `S` and respects the `S`-action;
* "adjoining `N` recovers the full transporter": `Iso_H(X, Y) = N · Iso_S(X, Y)`. -/
theorem par_restriction_to_supplement {G : Type*} [Group G] {κ : Type*}
    {H N S : Subgroup G} (hNH : N ≤ H) (hSH : S ≤ H) (hSn : Normalizes S N)
    (hSN : S ⊔ N = H) (L : κ → Subgroup G) (c : κ) (hNL : N ≤ L c) :
    (∀ {Γ : Set G}, Subgroup.closure Γ = L c → ∀ (fac : Γ → G × G),
      (∀ γ : Γ, (fac γ).1 ∈ N ∧ (fac γ).2 ∈ S ∧ (γ : G) = (fac γ).1 * (fac γ).2) →
        L c ⊓ S = Subgroup.closure (Set.range (fun γ : Γ => (fac γ).2)) ⊔ (S ⊓ N)) ∧
    (∀ h ∈ H, ∃ s ∈ S, cobj L c h = cobj L c s) ∧
    (∀ s ∈ S, ∀ s' ∈ S, (cobj (fun c => L c ⊓ S) c s = cobj (fun c => L c ⊓ S) c s' ↔
      cobj L c s = cobj L c s')) ∧
    (∀ {Ω : Type*} [RAct G Ω] (X Y : Multiset Ω), Fixes N X →
      Iso H X Y = {h | ∃ n ∈ N, ∃ s ∈ Iso S X Y, h = n * s}) := by
  have hcover := exists_kernel_mul_of_sup_eq hSn hSN
  refine ⟨fun hΓ fac hfac => inf_supplement_eq_closure hNL hSn hΓ fac hfac,
    fun h hh => cobj_supplement_surj hNL hcover hh,
    fun s hs s' hs' => cobj_supplement_eq_iff hs hs', ?_⟩
  intro Ω _ X Y hX
  exact iso_eq_kernel_mul_supplement hNH hSH hcover hX

/-! ### Theorem A.20 -/

/-- **Theorem A.20** (`thm:solvable-multicoset`), the recursion bound "`T_ℓ ≤ C(M+1)³
T_{ℓ-1} + P(b, M)`" as a count: the recursion tree of the procedure with fuel `ℓ` has at
most `(4M³ + 2)^ℓ` calls. Each call makes at most `4M²` pairwise comparisons with at most
`M` candidate images each, and one profile call, all with at most `M` objects. -/
theorem thm_solvable_multicoset_recursion {G : Type u} [Group G] (ℓ : ℕ) {Ω : Type u}
    [RAct G Ω] (H N : Subgroup G) (X Y : Multiset Ω) (M : ℕ) (hX : Multiset.card X ≤ M)
    (hY : Multiset.card Y ≤ M) : (proc ℓ H N X Y).calls ≤ (4 * M ^ 3 + 2) ^ ℓ :=
  proc_calls_le ℓ H N X Y M hX hY

/-- **Theorem A.20** (`thm:solvable-multicoset`), stage 1. In the coset-object model with
`N ◁ H ≤ Sym(B)`, `H/N` solvable, orbit colors `N ≤ L_c ≤ H`, and two multisets of at most
`M` objects each, the procedure `solvableTransport` returns the full transporter
`Iso_H(X, Y)`. Its recursion tree has at most `exp(42 log(b+M+2) log(b+2))` calls, and
with a polynomial `(b+M+2)^k` of work per call the total is
`exp((42 + 2k) log(b+M+2) log(b+2))`. No string-isomorphism oracle occurs in the procedure.
Dixon's bound is a cited input (`GI.Cited.DixonDerivedLength`). -/
theorem thm_solvable_multicoset (dixon : GI.Cited.DixonDerivedLength) {B : Type u}
    [Fintype B] [DecidableEq B] {H N : Subgroup (Equiv.Perm B)} (hNH : N ≤ H)
    [(N.subgroupOf H).Normal] [IsSolvable (H ⧸ N.subgroupOf H)] {κ : Type u}
    (L : κ → Subgroup (Equiv.Perm B)) (hL : ∀ c, N ≤ L c ∧ L c ≤ H)
    (X Y : Multiset (CObj κ (Equiv.Perm B)))
    (hXo : ∀ o ∈ X, ∃ c, ∃ h ∈ H, o = cobj L c h) (hYo : ∀ o ∈ Y, ∃ c, ∃ h ∈ H, o = cobj L c h)
    (M : ℕ) (hX : Multiset.card X ≤ M) (hY : Multiset.card Y ≤ M) :
    (solvableTransport H N X Y).set = Iso H X Y ∧
    ((solvableTransport H N X Y).calls : ℝ) ≤
      Real.exp (42 * Real.log ((Fintype.card B : ℝ) + M + 2) *
        Real.log ((Fintype.card B : ℝ) + 2)) ∧
    ∀ k : ℕ, ((solvableTransport H N X Y).calls : ℝ) * (((Fintype.card B + M + 2) ^ k : ℕ) : ℝ) ≤
      Real.exp ((42 + 2 * k) * Real.log ((Fintype.card B : ℝ) + M + 2) *
        Real.log ((Fintype.card B : ℝ) + 2)) := by
  have hn := normalizes_of_normal hNH
  have hsolv := exists_relDerived_of_isSolvable hNH
  have hcount : ((solvableTransport H N X Y).calls : ℝ) ≤
      Real.exp (42 * Real.log ((Fintype.card B : ℝ) + M + 2) *
        Real.log ((Fintype.card B : ℝ) + 2)) := by
    have h1 := proc_calls_le (quotLength (supplement H N) (supplement H N ⊓ N))
      (supplement H N) (supplement H N ⊓ N) X Y M hX hY
    have h2 := count_le_exp (Fintype.card B) M _ (solvableTransport_depth dixon hNH hn hsolv)
    exact (Nat.cast_le.mpr h1).trans h2
  refine ⟨solvableTransport_set hNH hn hsolv (fixes_of_cobj hn (fun c => (hL c).1) hXo)
    (fixes_of_cobj hn (fun c => (hL c).1) hYo), hcount, fun k => ?_⟩
  have hp := poly_le_exp (Fintype.card B) M k
  refine (mul_le_mul hcount hp (by positivity) (by positivity)).trans ?_
  rw [← Real.exp_add]
  apply le_of_eq
  congr 1
  ring

/-! ### Corollary A.22 -/

/-- **Corollary A.22** (`cor:transitive-kernel-multicoset`), stage 1. With `N ◁ H ≤ Sym(B)`
in the coset-object model, the procedure `radicalTransport` (enumerate the cosets of the
radical preimage `R`, apply Theorem A.20 in each, take the union) returns the full
transporter. Its number of procedure calls is at most
`exp(45 (log²(b+2) + log(M+2) log(b+2)))`.

The radical index bound `[H : R] ≤ b(H/N)² ≤ b^{2 log₂ b}` is the hypothesis `hidx`. In the
paper it follows from [GMP, Theorem 1.4] (here `N` transitive is used) and Lemma A.21,
which are not formalized here. The transitivity of `N` is used only through `hidx`. -/
theorem cor_transitive_kernel_multicoset (dixon : GI.Cited.DixonDerivedLength) {B : Type u}
    [Fintype B] [DecidableEq B] {H N : Subgroup (Equiv.Perm B)} (hNH : N ≤ H)
    [(N.subgroupOf H).Normal]
    (hidx : (((radicalPreimage H N).subgroupOf H).index : ℝ) ≤
      (Fintype.card B : ℝ) ^ (2 * Real.logb 2 (Fintype.card B)))
    {κ : Type u} (L : κ → Subgroup (Equiv.Perm B)) (hL : ∀ c, N ≤ L c ∧ L c ≤ H)
    (X Y : Multiset (CObj κ (Equiv.Perm B)))
    (hXo : ∀ o ∈ X, ∃ c, ∃ h ∈ H, o = cobj L c h) (hYo : ∀ o ∈ Y, ∃ c, ∃ h ∈ H, o = cobj L c h)
    (M : ℕ) (hX : Multiset.card X ≤ M) (hY : Multiset.card Y ≤ M) :
    (radicalTransport H N X Y).set = Iso H X Y ∧
    ((radicalTransport H N X Y).calls : ℝ) ≤
      Real.exp (45 * (Real.log ((Fintype.card B : ℝ) + 2) ^ 2 +
        Real.log ((M : ℝ) + 2) * Real.log ((Fintype.card B : ℝ) + 2))) := by
  have hn := normalizes_of_normal hNH
  exact ⟨radicalTransport_set hNH hn (fixes_of_cobj hn (fun c => (hL c).1) hXo)
      (fixes_of_cobj hn (fun c => (hL c).1) hYo),
    radicalTransport_calls_exp dixon hNH hn X Y M hX hY hidx⟩

/-! ### Theorem A.23 -/

/-- **Theorem A.23** (`thm:transitive-gat-terminal`), stage 1.

Setting (the subsubsection before the theorem): strings on `B × [m]` are row tuples
`x : Fin m → Ω`; `N ◁ H ≤ Sym(B)`; `φ : N → A` is the map to the abelian `A = N/N*`; `J` is
modeled by `InJ` and `G = K R₀` by `InG`, with the lifts `k(h)` of Theorem A.18 satisfying
`h⁻¹ k_i(h) ∈ N`. The structural data of Theorem A.18 are hypotheses here.

Claims:
1. the procedure returns the full transporter `Iso_G(x, y)`;
2. every element of it carries the type multiset of `x` to that of `y` under the residual
   element (`types_lift`, `types_rowAct_J`), and passes the zero-sum test: for an even matching
   with local transporters `x_i^{n_i} = y_{π i}`, a `J`-element with that matching exists
   exactly when `∏ φ(n_i) ∈ B(x)`;
3. when two rows share a type, parity is free;
4. the residual step makes at most `exp(45 (log²(b+2) + log(m+2) log(b+2)))` procedure calls,
   and the degree-`b` string calls number `2m² + m ≤ 3(m+1)²`.

The radical index bound `hidx` stands for [GMP, Theorem 1.4] and Lemma A.21; it is where the
transitivity of `N` is used. Deferred to stage 2: the polynomial-time affine label transport
inside each radical coset (Theorem A.20's affine step over `D/N` with the offsets
`∑_a m_a [t_a(h)] + ∑_i [d_i(h)]`), the lifts and corrections from stored tables, and the
final running-time total `poly(n) F(b) + exp(O(log²(n+2)))`. Here the label step is
represented by its result, the test of claim 2. -/
theorem thm_transitive_gat_terminal (dixon : GI.Cited.DixonDerivedLength) {B : Type u}
    [Fintype B] [DecidableEq B] {Ω : Type u} [RAct (Equiv.Perm B) Ω]
    {H N : Subgroup (Equiv.Perm B)} (hNH : N ≤ H) [(N.subgroupOf H).Normal]
    {A : Type*} [CommGroup A] (φ : N →* A) {m : ℕ} (k : Equiv.Perm B → Fin m → Equiv.Perm B)
    (hk : ∀ h ∈ H, ∀ i, h⁻¹ * k h i ∈ N)
    (hidx : (((radicalPreimage H N).subgroupOf H).index : ℝ) ≤
      (Fintype.card B : ℝ) ^ (2 * Real.logb 2 (Fintype.card B)))
    (x y : Fin m → Ω) :
    terminalTransport H N φ k x y = isoG H N φ k x y ∧
    (∀ p ∈ isoG H N φ k x y, ∃ h ∈ H, types N x ↼ h = types N y ∧
      ∃ μ, InJ N φ μ p.2 ∧ p.1 = k h * μ) ∧
    (∀ (z : Fin m → Ω) (π : Equiv.Perm (Fin m)), π ∈ alternatingGroup (Fin m) →
      ∀ n : Fin m → Equiv.Perm B, (∀ i, n i ∈ N) → (∀ i, x i ↼ n i = z (π i)) →
        ((∃ μ, InJ N φ μ π ∧ rowAct μ π x = z) ↔ ∏ i, phiT N φ (n i) ∈ labelGroup N φ x)) ∧
    (∀ (z : Fin m → Ω) (i j : Fin m), i ≠ j → ∀ c ∈ N, x i ↼ c = x j →
      ((∃ π ∈ alternatingGroup (Fin m), LabelOK N φ x z π) ↔ ∃ π, LabelOK N φ x z π)) ∧
    ((radicalTransport H N (types N x) (types N y)).calls : ℝ) ≤
      Real.exp (45 * (Real.log ((Fintype.card B : ℝ) + 2) ^ 2 +
        Real.log ((m : ℝ) + 2) * Real.log ((Fintype.card B : ℝ) + 2))) ∧
    terminalStringCalls m ≤ 3 * (m + 1) ^ 2 := by
  have hn := normalizes_of_normal hNH
  refine ⟨terminalTransport_eq hNH hn hk x y, ?_, fun z π hπ n hnN hxz =>
    exists_jIso_iff_label hπ hnN hxz, fun z i j hij c hc hcij =>
    exists_even_iff_exists_of_repeat hij hc hcij,
    terminalTransport_calls_exp dixon hNH hn hidx x y, ?_⟩
  · rintro ⟨d, π⟩ ⟨⟨h, hh, μ, hJ, rfl⟩, hxy⟩
    refine ⟨h, hh, ?_, μ, hJ, rfl⟩
    rw [rowAct_mul] at hxy
    rw [← types_lift hn hk hh, ← hxy, types_rowAct_J hJ.1]
  · simp only [terminalStringCalls]
    nlinarith

end GI.Paper
