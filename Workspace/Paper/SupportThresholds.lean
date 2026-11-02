import Workspace.SupportClassification
import Workspace.SupportTwoQuotient
import Workspace.KernelOrbitEquiv
import Workspace.Cited.TransitiveAffected

/-!
# Paper statements: Lemma A.15, Lemma A.24, Corollary A.25, Lemma A.26

Faithful statements of `lem:transitive-kernel-giant-threshold` (A.15),
`lem:low-index-alt-support` (A.24), `cor:physical-support-thresholds` (A.25),
`lem:support-two-orbit-quotient` (A.26) and the paragraph "When the
hypothesis occurs" after A.26.

Groups `G ≤ Sym(Ω)` are subgroups of `Equiv.Perm Ω` with their natural
(faithful) action. The claims "computable in polynomial time" in A.24, A.25
and A.26 are algorithmic clauses about the machine model; they are left
to the machine-level programs of `Workspace/Impl/`. Here we prove the mathematical content: the
classification, the equivariant quotient map (`KernelQuotient.map`), its
fibers being exactly the kernel orbits (`KernelQuotient.kernel_fibers`), and
their equal sizes (`KernelQuotient.equal_fibers`). The induced bijection
between the `K`-orbits and the target set is `KernelQuotient.orbitEquiv`,
which is equivariant by `KernelQuotient.orbitEquiv_equivariant`.
-/

namespace GI.Paper

open Equiv Equiv.Perm GI.SupportThresholds GI.StabilizerQuotient
open scoped Pointwise

/-! ### Lemma A.15 -/

/-- **Lemma A.15** (No large giant above a transitive kernel).
Suppose `N ◁ E ≤ Sym(B)`, `N` is transitive, `|B| = f`, and
`E/N ≅ Alt(k)`. Then `k ≤ max {8, 2 + log₂ f}`.

"Transitive" refers to `N`, as the title and the proof ("transitivity gives
`E = N E_v`") show. Transitivity of `E` alone would not do: `E = Alt(k)` on
`k ≥ 9` points with `N = 1` violates the bound.

The proof is the paper's: transitivity of `N` gives `E = N E_v`, so `E_v`
maps onto `E/N`, every point is unaffected, and this contradicts
`[H, Lemma 4.3(a)]` (`GI.Cited.TransitiveAffected`). -/
theorem lem_transitive_kernel_giant_threshold (hcite : GI.Cited.TransitiveAffected)
    {B : Type} [Fintype B] [DecidableEq B] (E N : Subgroup (Perm B)) (hNE : N ≤ E)
    [(N.subgroupOf E).Normal] [MulAction.IsPretransitive N B] {k : ℕ}
    (e : E ⧸ N.subgroupOf E ≃* alternatingGroup (Fin k)) :
    (k : ℝ) ≤ max 8 (2 + Real.logb 2 (Fintype.card B)) := by
  by_contra hlt
  push Not at hlt
  have hk : 9 ≤ k := by
    have : (8 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hlt
    exact_mod_cast this
  let q : E →* alternatingGroup (Fin k) := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hq : Function.Surjective q :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqN : ∀ n : N, q ⟨n, hNE n.2⟩ = 1 := by
    intro n
    have : (⟨n, hNE n.2⟩ : E) ∈ N.subgroupOf E := n.2
    simp only [q, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff _).mpr this, map_one]
  -- `B` is nonempty: otherwise `E` is trivial and cannot map onto `Alt(k)`.
  obtain ⟨v⟩ : Nonempty B := by
    by_contra hB
    rw [not_nonempty_iff] at hB
    haveI : Subsingleton E := ⟨fun g h => Subtype.ext (Subsingleton.elim _ _)⟩
    haveI : Nontrivial (alternatingGroup (Fin k)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
    obtain ⟨a, b, hab⟩ := exists_pair_ne (alternatingGroup (Fin k))
    obtain ⟨g, rfl⟩ := hq a
    obtain ⟨h, rfl⟩ := hq b
    exact hab (congrArg q (Subsingleton.elim g h))
  -- `E` is transitive, since it contains the transitive `N`.
  haveI : MulAction.IsPretransitive E B := ⟨fun x y => by
    obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N x y
    exact ⟨⟨n, hNE n.2⟩, hn⟩⟩
  -- `E = N E_v`, so `E_v` maps onto `E/N ≅ Alt(k)`: the point `v` is unaffected.
  have hunaff : (MulAction.stabilizer E v).map q = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨g, rfl⟩ := hq a
    obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N v (g • v)
    refine ⟨⟨n, hNE n.2⟩⁻¹ * g, ?_, ?_⟩
    · rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
      exact hn.symm
    · rw [map_mul, map_inv, hqN, inv_one, one_mul]
  exact hcite B E k q hq hlt v hunaff

/-! ### Lemma A.24 -/

/-- **Lemma A.24** (Alternating subgroups of index below `C(m,3)`).
There is an absolute `m₀` such that for `m ≥ m₀`, `|Γ| = m`, every subgroup
`P ≤ Alt(Γ)` with `[Alt(Γ) : P] < C(m,3)` is one of
1. `Alt(Γ)`;
2. `Alt(Γ ∖ {a})`, the stabilizer of one point `a`;
3. `Alt(Γ ∖ {a, b})`, the pointwise stabilizer of two distinct points
   (`GI.Pairs.pointwise`, the stabilizer of the ordered pair `(a, b)`);
4. the setwise stabilizer of `{a, b}` in `Alt(Γ)` (`GI.Pairs.setwise`).

The coset actions are identified in
`lem_low_index_alt_support_coset_action`. The polynomial-time clause is
left to the machine level. A concrete `m₀` is
`GI.SupportThresholds.lowIndexThreshold = 201`
(`GI.SupportThresholds.low_index_classification`). -/
theorem lem_low_index_alt_support :
    ∃ m₀ : ℕ, ∀ (Γ : Type) [Fintype Γ] [DecidableEq Γ], m₀ ≤ Fintype.card Γ →
      ∀ P : Subgroup (alternatingGroup Γ),
        P.index < (Fintype.card Γ).choose 3 →
        P = ⊤ ∨ (∃ a : Γ, P = MulAction.stabilizer (alternatingGroup Γ) a) ∨
          (∃ (a b : Γ) (hab : a ≠ b), P = GI.Pairs.pointwise a b hab) ∨
          (∃ (a b : Γ) (hab : a ≠ b), P = GI.Pairs.setwise a b hab) :=
  ⟨lowIndexThreshold, fun _ _ _ hm P hI => low_index_classification hm P hI⟩

/-- The coset action of `Alt(Γ)` on `Alt(Γ) ⧸ Stab(w)` is isomorphic to its
action on a transitive set `W`, by `g Stab(w) ↦ g • w`. -/
theorem coset_action_equiv {Q W : Type*} [Group Q] [MulAction Q W]
    [MulAction.IsPretransitive Q W] (w : W) :
    ∃ f : Q ⧸ MulAction.stabilizer Q w ≃ W,
      (∀ g : Q, f (QuotientGroup.mk g) = g • w) ∧
      ∀ (g : Q) (y : Q ⧸ MulAction.stabilizer Q w), f (g • y) = g • f y := by
  let f := (MulAction.orbitEquivQuotientStabilizer Q w).symm.trans
    ((Equiv.setCongr (MulAction.orbit_eq_univ Q w)).trans (Equiv.Set.univ W))
  have hf : ∀ g : Q, f (QuotientGroup.mk g) = g • w := fun g => by
    simp [f, MulAction.orbitEquivQuotientStabilizer_symm_apply]
  refine ⟨f, hf, ?_⟩
  intro g y
  induction y using QuotientGroup.induction_on with
  | H h =>
    rw [MulAction.Quotient.smul_mk, hf, hf, smul_eq_mul, mul_smul]

/-- **Lemma A.24, coset actions.** The four groups of
`lem_low_index_alt_support` have the trivial, natural, ordered-pair and
unordered-pair coset actions: for `m ≥ 4` there is an `Alt(Γ)`-equivariant
bijection from `Alt(Γ) ⧸ P` onto a point, `Γ`, the ordered pairs of distinct
elements, and the two-element subsets, respectively. -/
theorem lem_low_index_alt_support_coset_action {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (h4 : 4 ≤ Fintype.card Γ) :
    (∀ y : alternatingGroup Γ ⧸ (⊤ : Subgroup (alternatingGroup Γ)), y = QuotientGroup.mk 1) ∧
    (∀ a : Γ, ∃ f : alternatingGroup Γ ⧸ MulAction.stabilizer (alternatingGroup Γ) a ≃ Γ,
      ∀ (g : alternatingGroup Γ) y, f (g • y) = g • f y) ∧
    (∀ (a b : Γ) (hab : a ≠ b),
      ∃ f : alternatingGroup Γ ⧸ GI.Pairs.pointwise a b hab ≃ GI.Pairs.OrderedPair Γ,
        ∀ (g : alternatingGroup Γ) y, f (g • y) = g • f y) ∧
    (∀ (a b : Γ) (hab : a ≠ b),
      ∃ f : alternatingGroup Γ ⧸ GI.Pairs.setwise a b hab ≃ GI.Johnson.SubsetVertex Γ 2,
        ∀ (g : alternatingGroup Γ) y, f (g • y) = g • f y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    induction y using QuotientGroup.induction_on with
    | H g => exact (QuotientGroup.eq.mpr (Subgroup.mem_top _))
  · intro a
    haveI : MulAction.IsPretransitive (alternatingGroup Γ) Γ := ⟨fun x y => by
      obtain ⟨p, hp⟩ := GI.AlternatingActions.exists_alternating_finset_eq (by omega)
        ({x} : Finset Γ) {y} rfl
      refine ⟨p, ?_⟩
      rw [Finset.smul_finset_singleton, Finset.singleton_inj] at hp
      exact hp⟩
    obtain ⟨f, -, hf⟩ := coset_action_equiv (Q := alternatingGroup Γ) a
    exact ⟨f, hf⟩
  · intro a b hab
    haveI : MulAction.IsPretransitive (alternatingGroup Γ) (GI.Pairs.OrderedPair Γ) :=
      ⟨GI.Pairs.ordered_transitive h4⟩
    obtain ⟨f, -, hf⟩ := coset_action_equiv (Q := alternatingGroup Γ)
      (⟨(a, b), hab⟩ : GI.Pairs.OrderedPair Γ)
    exact ⟨f, hf⟩
  · intro a b hab
    haveI : MulAction.IsPretransitive (alternatingGroup Γ) (GI.Johnson.SubsetVertex Γ 2) :=
      ⟨GI.Pairs.unordered_transitive h4⟩
    obtain ⟨f, -, hf⟩ := coset_action_equiv (Q := alternatingGroup Γ)
      (GI.Pairs.unorderedOfOrdered ⟨(a, b), hab⟩)
    exact ⟨f, hf⟩

/-! ### Corollary A.25 -/

section Physical

variable {Ω Γ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]

/-- The alternating group is transitive on points in degree at least three. -/
theorem alternating_point_transitive (h3 : 3 ≤ Fintype.card Γ) (a y : Γ) :
    ∃ q : alternatingGroup Γ, q • a = y := by
  obtain ⟨p, hp⟩ := GI.AlternatingActions.exists_alternating_finset_eq h3
    ({a} : Finset Γ) {y} rfl
  refine ⟨p, ?_⟩
  rw [Finset.smul_finset_singleton, Finset.singleton_inj] at hp
  exact hp

omit [DecidableEq Ω] in
/-- `|Ω/K| ≤ n`: the index of the point-stabilizer image is at most the degree. -/
theorem index_stabilizer_map_le (G : Subgroup (Perm Ω)) [MulAction.IsPretransitive G Ω]
    (φ : G →* alternatingGroup Γ) (hφ : Function.Surjective φ) (x : Ω) :
    ((MulAction.stabilizer G x).map φ).index ≤ Fintype.card Ω := by
  have hd := Subgroup.index_map_dvd (MulAction.stabilizer G x) hφ
  rw [MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card] at hd
  exact Nat.le_of_dvd (Fintype.card_pos_iff.mpr ⟨x⟩) hd

/-- The trivial-action case is excluded at the unaffected-stabilizer threshold:
no point stabilizer maps onto `Alt(Γ)`, by `[H, Lemma 4.3(a)]`. -/
theorem stabilizer_map_ne_top (hcite : GI.Cited.TransitiveAffected)
    (G : Subgroup (Perm Ω)) [MulAction.IsPretransitive G Ω]
    (φ : G →* alternatingGroup Γ) (hφ : Function.Surjective φ)
    (hlog : max 8 (2 + Real.logb 2 (Fintype.card Ω)) < (Fintype.card Γ : ℝ)) (x : Ω) :
    (MulAction.stabilizer G x).map φ ≠ ⊤ := by
  intro htop
  let r := GI.AlternatingSimple.relabel (Fintype.equivFin Γ)
  let ψ : G →* alternatingGroup (Fin (Fintype.card Γ)) := r.toMonoidHom.comp φ
  have hψ : Function.Surjective ψ := r.surjective.comp hφ
  apply hcite Ω G (Fintype.card Γ) ψ hψ hlog x
  rw [← Subgroup.map_map, htop]
  exact Subgroup.map_top_of_surjective _ r.surjective

/-- The three proper cases of Corollary A.25, each with its quotient map. -/
theorem physical_support_cases (hcite : GI.Cited.TransitiveAffected)
    (G : Subgroup (Perm Ω)) [MulAction.IsPretransitive G Ω]
    (φ : G →* alternatingGroup Γ) (hφ : Function.Surjective φ)
    (hm : lowIndexThreshold ≤ Fintype.card Γ)
    (hn : Fintype.card Ω < (Fintype.card Γ).choose 3)
    (hlog : max 8 (2 + Real.logb 2 (Fintype.card Ω)) < (Fintype.card Γ : ℝ)) :
    Nonempty (KernelQuotient φ Ω Γ) ∨
      Nonempty (KernelQuotient φ Ω (GI.Pairs.OrderedPair Γ)) ∨
      Nonempty (KernelQuotient φ Ω (GI.Johnson.SubsetVertex Γ 2)) := by
  have hm' : 201 ≤ Fintype.card Γ := hm
  -- `Ω` is nonempty: otherwise `G` is trivial and cannot map onto `Alt(Γ)`.
  obtain ⟨x⟩ : Nonempty Ω := by
    by_contra hΩ
    rw [not_nonempty_iff] at hΩ
    haveI : Subsingleton G := ⟨fun g h => Subtype.ext (Subsingleton.elim _ _)⟩
    haveI : Nontrivial (alternatingGroup Γ) :=
      alternatingGroup.nontrivial_of_three_le_card (by omega)
    obtain ⟨a, b, hab⟩ := exists_pair_ne (alternatingGroup Γ)
    obtain ⟨g, rfl⟩ := hφ a
    obtain ⟨h, rfl⟩ := hφ b
    exact hab (congrArg φ (Subsingleton.elim g h))
  have hsource : ∀ y : Ω, ∃ g : G, g • x = y := MulAction.exists_smul_eq G x
  -- `P = φ(G_x)` has index `|Ω/K| ≤ n < C(m,3)`, so Lemma A.24 applies.
  have hI := (index_stabilizer_map_le G φ hφ x).trans_lt hn
  rcases low_index_classification hm _ hI with htop | ⟨a, ha⟩ | ⟨a, b, hab, hp⟩ |
      ⟨a, b, hab, hs⟩
  · exact absurd htop (stabilizer_map_ne_top hcite G φ hφ hlog x)
  · exact Or.inl ⟨kernelQuotientOfImage φ x a hφ hsource
      (alternating_point_transitive (by omega) a) ha⟩
  · exact Or.inr (Or.inl ⟨kernelQuotientOfImage φ x (⟨(a, b), hab⟩ : GI.Pairs.OrderedPair Γ)
      hφ hsource (GI.Pairs.ordered_transitive (by omega) _) hp⟩)
  · exact Or.inr (Or.inr ⟨kernelQuotientOfImage φ x
      (GI.Pairs.unorderedOfOrdered ⟨(a, b), hab⟩) hφ hsource
      (GI.Pairs.unordered_transitive (by omega) _) hs⟩)

/-- **Corollary A.25** (Constructive physical support thresholds).
Let `G ≤ Sym(Ω)` be transitive, `|Ω| = n`, and `φ : G ↠ Alt(Γ)` with
`m = |Γ| ≥ m₀` (`m₀ = lowIndexThreshold`, the constant of Lemma A.24),
`K = ker φ`. Suppose `n < C(m,3)` and `m > max {8, 2 + log₂ n}`. Then the
action of `G` on its `K`-orbits is isomorphic to the natural, ordered-pair, or
unordered-pair action on `Γ`: there is an equivariant surjective quotient map
from `Ω` whose fibers are exactly the `K`-orbits, all of equal size
(a `KernelQuotient`; `KernelQuotient.orbitEquiv` is the induced equivariant
bijection from the `K`-orbits). If in addition `n < C(m,2)`, only the natural
action is possible, so `K` is transitive inside each of its `m` natural
blocks (the fibers).

Deferred: "the equivariant quotient map is polynomial-time computable". -/
theorem cor_physical_support_thresholds (hcite : GI.Cited.TransitiveAffected)
    (G : Subgroup (Perm Ω)) [MulAction.IsPretransitive G Ω]
    (φ : G →* alternatingGroup Γ) (hφ : Function.Surjective φ)
    (hm : lowIndexThreshold ≤ Fintype.card Γ)
    (hn : Fintype.card Ω < (Fintype.card Γ).choose 3)
    (hlog : max 8 (2 + Real.logb 2 (Fintype.card Ω)) < (Fintype.card Γ : ℝ)) :
    (Nonempty (KernelQuotient φ Ω Γ) ∨
      Nonempty (KernelQuotient φ Ω (GI.Pairs.OrderedPair Γ)) ∨
      Nonempty (KernelQuotient φ Ω (GI.Johnson.SubsetVertex Γ 2))) ∧
    (Fintype.card Ω < (Fintype.card Γ).choose 2 → Nonempty (KernelQuotient φ Ω Γ)) := by
  have hcases := physical_support_cases hcite G φ hφ hm hn hlog
  refine ⟨hcases, fun hn2 => ?_⟩
  have hm' : 201 ≤ Fintype.card Γ := hm
  -- The ordered and unordered pair actions have degrees `m(m-1)` and `C(m,2)`.
  rcases hcases with h | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact h
  · have hle := Fintype.card_le_of_surjective f.map f.onto
    rw [card_orderedPair] at hle
    have h2 := two_mul_choose_two (Fintype.card Γ)
    have : Fintype.card Γ * (Fintype.card Γ - 1) =
        Fintype.card Γ * Fintype.card Γ - Fintype.card Γ := Nat.mul_sub_one _ _
    omega
  · have hle := Fintype.card_le_of_surjective f.map f.onto
    rw [Fintype.card_finset_len] at hle
    omega

/-! ### Lemma A.26 -/

omit [Fintype Ω] [DecidableEq Ω] in
/-- **Lemma A.26** (The support-two orbit quotient).
Let `G ≤ Sym(Ω)` be transitive, `φ : G ↠ Alt(Γ)`, `m = |Γ| ≥ 9`,
`K = ker φ`. Suppose for some `x ∈ Ω` and some two-element `D ⊆ Γ`,
`Alt(Γ ∖ D) ≤ φ(G_x) ≤ Alt(Γ)_{D}` (IR1). Then the action of `G` on its
`K`-orbits is equivariantly isomorphic to the action on unordered pairs or on
ordered pairs of distinct elements of `Γ`: there is an equivariant surjective
map `f : Ω → Ξ`, built from `φ`, `x` and `D`, whose fibers are precisely the
`K`-orbits and all have equal size.

Here `Alt(Γ ∖ D)` is the image of `Alt(Γ ∖ D)` under extension by the
identity (`GI.AlternatingSimple.extend`), and `Alt(Γ)_{D}` is the setwise
stabilizer of `D`. Deferred: the polynomial-time construction. -/
theorem lem_support_two_orbit_quotient
    (G : Subgroup (Perm Ω)) [MulAction.IsPretransitive G Ω]
    (φ : G →* alternatingGroup Γ) (hφ : Function.Surjective φ)
    (hm : 9 ≤ Fintype.card Γ) (x : Ω) (D : Finset Γ) (hD : D.card = 2)
    (lower : (GI.AlternatingSimple.extend (Finset.univ \ D)).range ≤
      (MulAction.stabilizer G x).map φ)
    (upper : (MulAction.stabilizer G x).map φ ≤ MulAction.stabilizer (alternatingGroup Γ) D) :
    Nonempty (KernelQuotient φ Ω (GI.Johnson.SubsetVertex Γ 2)) ∨
      Nonempty (KernelQuotient φ Ω (GI.Pairs.OrderedPair Γ)) := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hD
  rw [setStabilizer_pair a b hab] at upper
  -- The upper group of (IR1) over the lower group has order two, so `φ(G_x)`
  -- is the two-set stabilizer or the pointwise stabilizer `Alt(m-2)`.
  rcases GI.Pairs.support_two_quotient (by omega) φ hφ x (MulAction.exists_smul_eq G x)
      a b hab lower upper with h | h
  · exact Or.inr h
  · exact Or.inl h

/-! ### When the hypothesis occurs -/

/-- **"When the hypothesis occurs"** (paragraph after Lemma A.26). Under the
hypotheses of Corollary A.25, at every point `x` either `φ(G_x)` is a point
stabilizer (the support-one alternative), or there is a two-element
`D ⊆ Γ` for which `φ(G_x)` satisfies (IR1), so Lemma A.26 applies. -/
theorem par_when_the_hypothesis_occurs (hcite : GI.Cited.TransitiveAffected)
    (G : Subgroup (Perm Ω)) [MulAction.IsPretransitive G Ω]
    (φ : G →* alternatingGroup Γ) (hφ : Function.Surjective φ)
    (hm : lowIndexThreshold ≤ Fintype.card Γ)
    (hn : Fintype.card Ω < (Fintype.card Γ).choose 3)
    (hlog : max 8 (2 + Real.logb 2 (Fintype.card Ω)) < (Fintype.card Γ : ℝ)) (x : Ω) :
    (∃ a : Γ, (MulAction.stabilizer G x).map φ = MulAction.stabilizer (alternatingGroup Γ) a) ∨
      ∃ D : Finset Γ, D.card = 2 ∧
        (GI.AlternatingSimple.extend (Finset.univ \ D)).range ≤
          (MulAction.stabilizer G x).map φ ∧
        (MulAction.stabilizer G x).map φ ≤ MulAction.stabilizer (alternatingGroup Γ) D := by
  have hI := (index_stabilizer_map_le G φ hφ x).trans_lt hn
  rcases low_index_classification hm _ hI with htop | ha | ⟨a, b, hab, hp⟩ | ⟨a, b, hab, hs⟩
  · exact absurd htop (stabilizer_map_ne_top hcite G φ hφ hlog x)
  · exact Or.inl ha
  · refine Or.inr ⟨{a, b}, Finset.card_pair hab, ?_, ?_⟩
    · rw [hp, ← GI.Pairs.complement_alternating_range a b hab]
      exact le_rfl
    · rw [hp, setStabilizer_pair a b hab]
      exact GI.Pairs.pointwise_le_setwise a b hab
  · refine Or.inr ⟨{a, b}, Finset.card_pair hab, ?_, ?_⟩
    · rw [hs]
      exact (GI.Pairs.complement_alternating_range a b hab).le.trans
        (GI.Pairs.pointwise_le_setwise a b hab)
    · rw [hs, setStabilizer_pair a b hab]

end Physical

end GI.Paper
