module

public import Workspace.RectangleCaps
public import Workspace.RectangleOutput
public import Workspace.Paper.SupportThresholds
public import Workspace.CoherentRectangleCertificate
public import Workspace.CoherentComponentPartition
public import Workspace.Parameters
public import Workspace.RectangleLeftCap
public import Workspace.SideParity

@[expose] public section

/-!
# Paper statements: Lemma A.27 (`lem:inherited-support-two-rectangle`)

Faithful statement of the mathematical content of Lemma A.27, in both the ordered
and the unordered pair case. Lemma A.26 is assumed in the form of its output: a
`KernelQuotient` `f` from the physical points onto the ordered or unordered pairs of
`Γ`, whose fibers are the kernel orbits (`GI.Paper.lem_support_two_orbit_quotient`).

* `P = (Sym W × Sym R × Sym Y) ∩ Alt Γ` is `GI.Rectangle.permitted W R`: the even
  permutations that fix `W` and `R` setwise (they then fix `Y = Γ \ (W ∪ R)` too).
* `H = φ⁻¹(P)` is `(permitted W R).comap φ`.
* `Ξ_{W,R}` is `orderedRectangle hd` (pairs `(w, r)`) or `unorderedRectangle hd`.
* `Δ = f⁻¹(Ξ_{W,R})` is the subtype `OrderedPhysical f hd`, and `H^Δ` is the range of
  `orderedPhysicalAction f hd`.
* The image of `P` acting on `W × R` is the range of `rectangleAction`; it embeds in
  `Sym W × Sym R` by `extractSides` (`GI.Rectangle.extractSides_transports`).

Stage 2 (machine level, not stated here): "computable by one exact string-isomorphism call", "lift its
generators to `H` and apply `φ`", and "polynomial-time membership and lifting
operations" are machine-level clauses. Stage 1 here: the call's answer, as a
mathematical object, is the transporter of the pulled-back strings in `H^Δ`, and its
projection is the complete permitted matrix transporter.

The paragraph "Parity and source--target alignment" after Lemma A.27:
`par_parity_alignment`, `par_parity_permitted_image`, `par_parity_full_transporter`.
Algorithm `alg:auxiliary` (Section 5.4), mathematical content: `liftAndContinue`
with `alg_auxiliary_lift_and_continue`, the rectangle branch
`alg_auxiliary_rectangle_branch`, and the covering list `alg_auxiliary_cover`.
-/

namespace GI.Paper

open Equiv Equiv.Perm GI.StabilizerQuotient GI.Rectangle

section A27

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] [DecidableEq Γ]

/-- **Lemma A.27** (An exact inherited rectangle query), ordered-pair case.

Given the ordered-pair quotient `f` of Lemma A.26 and disjoint `W, R ⊆ Γ` with
`|W| ≥ 3` and `R` nonempty:
1. `Δ = f⁻¹(Ξ_{W,R})` is nonempty and is one `H`-orbit;
2. (IR2) `|Δ| · m(m-1) = |W||R| n`;
3. the input strings `x ∘ f`, `y ∘ f` are constant on the fibers of `f`;
4. projecting the complete transporter of the pulled-back strings in `H^Δ` gives
   exactly the complete permitted matrix transporter, and the projection
   `H^Δ → P^{W×R}` is onto (every permitted pair permutation has a lift);
5. the call inherits the budget: `σ(H^Δ) ≤ σ(G)` at every base point;
6. the call inherits every alternating-section cap of `G`. -/
theorem lem_inherited_support_two_rectangle_ordered
    (G : Subgroup (Perm Ω)) (φ : G →* alternatingGroup Γ) (hφ : Function.Surjective φ)
    (f : KernelQuotient φ Ω (GI.Pairs.OrderedPair Γ))
    (W R : Finset Γ) (hd : Disjoint W R) (hW : 3 ≤ W.card) (hR : R.Nonempty)
    [Fintype (OrderedPhysical f hd)] :
    (∃ x : Ω, f.map x ∈ orderedRectangle hd) ∧
    (∀ x : Ω, f.map x ∈ orderedRectangle hd →
      {y : Ω | f.map y ∈ orderedRectangle hd} = MulAction.orbit ((permitted W R).comap φ) x) ∧
    Nat.card {x : Ω // f.map x ∈ orderedRectangle hd} *
        (Fintype.card Γ * (Fintype.card Γ - 1)) = W.card * R.card * Fintype.card Ω ∧
    (∀ {C : Type*} (x : W × R → C) (u v : OrderedPhysical f hd),
      f.map u.val = f.map v.val → (x ∘ orderedMap f hd) u = (x ∘ orderedMap f hd) v) ∧
    (∀ {C : Type*} (x y : W × R → C),
      orderedProjection f hd ''
        {p : (orderedPhysicalAction f hd).range |
          Transports (x ∘ orderedMap f hd) (y ∘ orderedMap f hd) p.val} =
        {q : (rectangleAction (W := W) (R := R)).range | Transports x y q.val}) ∧
    Function.Surjective (orderedProjection f hd) ∧
    (∀ kcert : ℕ, 5 ≤ kcert → ∀ x : OrderedPhysical f hd,
      sigma kcert x (orderedPhysicalAction f hd).range ≤ sigma kcert x.val G) ∧
    (∀ b : ℕ, SectionCaps.Cap G b → SectionCaps.Cap (orderedPhysicalAction f hd).range b) := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < W.card)
  obtain ⟨b, hb⟩ := hR
  -- `Δ` is nonempty: `f` is onto the pairs, and `(a, b) ∈ Ξ_{W,R}`.
  have hne : ∃ x : Ω, f.map x ∈ orderedRectangle hd := by
    obtain ⟨x, hx⟩ := f.onto (orderedEmbedding hd (⟨a, ha⟩, ⟨b, hb⟩))
    exact ⟨x, hx ▸ ⟨_, rfl⟩⟩
  refine ⟨hne, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- "The group `P` is transitive on `W × R` ... The kernel `K ≤ H` is transitive on
    -- each fiber of `f`, proving transitivity on `Δ`."
    exact fun x hx => ordered_preimage_is_orbit f hφ hd hW x hx
  · -- "Equal fiber sizes give (IR2)."
    have h := ordered_physical_fraction f hd (orderedEmbedding hd (⟨a, ha⟩, ⟨b, hb⟩))
    rwa [Nat.card_eq_fintype_card (α := Ω)] at h
  · -- "The input strings are constant on the fibers of `f`."
    intro C x u v huv
    exact ordered_strings_constant_on_fibers f hd x u v huv
  · -- "An element of `H` preserves or transports these pulled-back strings exactly when
    -- its induced pair permutation preserves or transports the matrices. Every
    -- permitted pair permutation has a lift in `H`."
    intro C x y
    exact ordered_exact_query f hφ hd x y
  · exact EmbeddedQuotient.permittedProjection_onto f (orderedEmbedding hd) (permitted W R)
      rectangleAction (orderedEmbedding_move hd) hφ
  · -- "The queried action is literally the action of a subgroup of `G` on one of its
    -- orbits ... the visibility and inherited-state conditions of the marked-chain
    -- budget apply."
    intro kcert hk x
    exact ordered_query_budget f hd hk x
  · -- Caps pass to subgroups (`H ≤ G`) and to images (`H → H^Δ`).
    intro b hb
    exact SectionCaps.of_surjective _ (QuotientImage.range_surjective _)
      (SectionCaps.subgroup hb _)

/-- **Lemma A.27**, unordered-pair case. The same six assertions as
`lem_inherited_support_two_rectangle_ordered`, with (IR2) in the form
`|Δ| · m(m-1) = 2 |W||R| n`. -/
theorem lem_inherited_support_two_rectangle_unordered
    (G : Subgroup (Perm Ω)) (φ : G →* alternatingGroup Γ) (hφ : Function.Surjective φ)
    (f : KernelQuotient φ Ω (GI.Johnson.SubsetVertex Γ 2))
    (W R : Finset Γ) (hd : Disjoint W R) (hW : 3 ≤ W.card) (hR : R.Nonempty)
    [Fintype (UnorderedPhysical f hd)] :
    (∃ x : Ω, f.map x ∈ unorderedRectangle hd) ∧
    (∀ x : Ω, f.map x ∈ unorderedRectangle hd →
      {y : Ω | f.map y ∈ unorderedRectangle hd} = MulAction.orbit ((permitted W R).comap φ) x) ∧
    Nat.card {x : Ω // f.map x ∈ unorderedRectangle hd} *
        (Fintype.card Γ * (Fintype.card Γ - 1)) = 2 * (W.card * R.card * Fintype.card Ω) ∧
    (∀ {C : Type*} (x : W × R → C) (u v : UnorderedPhysical f hd),
      f.map u.val = f.map v.val → (x ∘ unorderedMap f hd) u = (x ∘ unorderedMap f hd) v) ∧
    (∀ {C : Type*} (x y : W × R → C),
      unorderedProjection f hd ''
        {p : (unorderedPhysicalAction f hd).range |
          Transports (x ∘ unorderedMap f hd) (y ∘ unorderedMap f hd) p.val} =
        {q : (rectangleAction (W := W) (R := R)).range | Transports x y q.val}) ∧
    Function.Surjective (unorderedProjection f hd) ∧
    (∀ kcert : ℕ, 5 ≤ kcert → ∀ x : UnorderedPhysical f hd,
      sigma kcert x (unorderedPhysicalAction f hd).range ≤ sigma kcert x.val G) ∧
    (∀ b : ℕ, SectionCaps.Cap G b → SectionCaps.Cap (unorderedPhysicalAction f hd).range b) := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < W.card)
  obtain ⟨b, hb⟩ := hR
  have hne : ∃ x : Ω, f.map x ∈ unorderedRectangle hd := by
    obtain ⟨x, hx⟩ := f.onto (unorderedEmbedding hd (⟨a, ha⟩, ⟨b, hb⟩))
    exact ⟨x, hx ▸ ⟨_, rfl⟩⟩
  refine ⟨hne, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x hx => unordered_preimage_is_orbit f hφ hd hW x hx
  · have h := unordered_physical_fraction f hd (unorderedEmbedding hd (⟨a, ha⟩, ⟨b, hb⟩))
    rwa [Nat.card_eq_fintype_card (α := Ω)] at h
  · intro C x u v huv
    exact unordered_strings_constant_on_fibers f hd x u v huv
  · intro C x y
    exact unordered_exact_query f hφ hd x y
  · exact EmbeddedQuotient.permittedProjection_onto f (unorderedEmbedding hd) (permitted W R)
      rectangleAction (unorderedEmbedding_move hd) hφ
  · intro kcert hk x
    exact unordered_query_budget f hd hk x
  · intro b hb
    exact SectionCaps.of_surjective _ (QuotientImage.range_surjective _)
      (SectionCaps.subgroup hb _)

end A27

section A28

open GI.PairRefinement GI.CoherentEntrance

variable {n : ℕ}

/-- **Lemma A.28** (The first certified Split-or-Johnson entrance).

The configuration is `c` on `C = Fin n` (`n = |C|`), with the two instances
indexed by `side`; "nontrivial" is `NontrivialOffDiagonal` (at least two
off-diagonal colors). The ideal degree is `m ≥ n`. The hypothesis `|C| ≥ δ m` of
the paper is not needed for these conclusions. The paper fixes `2/3 < η < 1`; the
proof only uses `1/2 ≤ η < 1`.

Either the configuration is imprimitive and gives the canonical partition into
equal blocks of sizes between `2` and `n/2` (first paragraph of [H, Section 5.2]),
or it is primitive and, for every source vertex `x` (one branch for each target
image), either every color class at `x` has size at most `η n` (the colored
partition), or there is an actual rectangle `W, R ⊆ C` with a nontrivial
semiregular binary matrix (the fields `rows`, `columns`, `mixed` of the
certificate) satisfying (IR3), with every left twin class of size at most `|W|/2`,
and with `x` on neither side. The proof of [H, Theorem 5.3] that the paper quotes
is proved in the library (`GI.CoherentEntrance.primitive_entrance_alternative`), so
no cited input is needed.

Stage 2 (machine level, not stated here): "polynomially many branches and polynomial structural work".
The branches are the `n` target images of `x`; the covering of every parent
isomorphism by its branch is `lem_first_soj_rectangle_covers`. -/
theorem lem_first_soj_rectangle (c : Coloring n) (hc : Coherent c) (side : Bool)
    (hh : Homogeneous c side) (hn : NontrivialOffDiagonal c side)
    {m : ℕ} (hnm : n ≤ m) {η : ℝ} (hη : 1 / 2 ≤ η) (hη1 : η < 1) :
    (¬ PrimitiveColorCuts c side ∧ ∃ a b : Fin n, a ≠ b ∧
      (∀ x y, (colorComponent c side (c (side, a, b)) x).card =
        (colorComponent c side (c (side, a, b)) y).card) ∧
      (∀ x, 2 ≤ (colorComponent c side (c (side, a, b)) x).card ∧
        2 * (colorComponent c side (c (side, a, b)) x).card ≤ n)) ∨
    (PrimitiveColorCuts c side ∧ ∀ x : Fin n,
      (∀ i, ((colorClass c side x i).card : ℝ) ≤ η * n) ∨
      ∃ cert : RectangleCertificate c side x η,
        η * n < ((colorClass c side x cert.leftColor).card : ℝ) ∧
        (colorClass c side x cert.rightColor).card ≤
          n - (colorClass c side x cert.leftColor).card ∧
        ((colorClass c side x cert.leftColor).card : ℝ) *
            (colorClass c side x cert.rightColor).card ≤ η * (1 - η) * (m : ℝ) ^ 2 ∧
        Disjoint (colorClass c side x cert.leftColor) (colorClass c side x cert.rightColor) ∧
        x ∉ colorClass c side x cert.leftColor ∧ x ∉ colorClass c side x cert.rightColor ∧
        ∀ u, 2 * (Semiregular.twins
          (fiberMatrix c side x cert.leftColor cert.rightColor cert.edgeColor) u).card ≤
            (colorClass c side x cert.leftColor).card) := by
  by_cases hp : PrimitiveColorCuts c side
  swap
  · -- "An imprimitive coherent configuration gives the canonical equal-block partition."
    exact Or.inl ⟨hp, nonprimitive_balanced_components c hc side hh hp⟩
  refine Or.inr ⟨hp, fun x => ?_⟩
  -- "Otherwise choose a source vertex `x` and branch over its target image. If none of
  -- their classes exceeds `η|C|`, they give the required colored partition."
  rcases primitive_entrance_alternative c hc side hh hn hp x η hη with hbal | hcert
  · exact Or.inl hbal
  obtain ⟨cert⟩ := hcert
  refine Or.inr ⟨cert, cert.dominant, ?_, ?_, cert.disjoint, ?_, ?_, cert.twinBound⟩
  · -- `r ≤ c - w`
    have := cert.sideSum
    rw [colorClass_card, colorClass_card]
    omega
  · -- "the decreasing quadratic `w(c-w)` on `[ηc, c]` gives `wr ≤ η(1-η)c²`", and `c ≤ m`.
    have harea := cert.area
    rw [colorClass_card, colorClass_card]
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hsq : (n : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hnm' 2
    have hcoef : 0 ≤ η * (1 - η) := mul_nonneg (by linarith) (by linarith)
    exact harea.trans (mul_le_mul_of_nonneg_left hsq hcoef)
  · -- "`x` belongs to neither side"
    rw [mem_colorClass]
    exact fun h => cert.leftOffDiagonal h.symm
  · rw [mem_colorClass]
    exact fun h => cert.rightOffDiagonal h.symm

/-- Lemma A.28, "They cover every parent isomorphism": a parent isomorphism `p`
(a transporter of the two configurations) maps the color classes at `x` onto the
color classes of the same colors at `p x`, and transports the matrix of every
color triple. So the branch `x ↦ p x` contains `p`, and both instances produce
rectangles of the same colors and sizes. -/
theorem lem_first_soj_rectangle_covers (c : Coloring n) (source target : Bool)
    (p : Equiv.Perm (Fin n)) (h : GI.PairRefinement.Transports c source target p)
    (x : Fin n) (i j k : Color n) :
    (colorClass c target (p x) i).card = (colorClass c source x i).card ∧
    ∀ (w : ColorFiber c source x i) (r : ColorFiber c source x j),
      fiberMatrix c target (p x) i j k (fiberTransport c source target p h x i w)
        (fiberTransport c source target p h x j r) = fiberMatrix c source x i j k w r := by
  refine ⟨?_, fun w r => fiberMatrix_transport c source target p h x i j k w r⟩
  have e := Fintype.card_congr (fiberTransport c source target p h x i)
  simp only [Fintype.card_subtype] at e
  exact e.symm

end A28

section ReturnedCap

/-- Paragraph "The returned parent cap" after Lemma A.28, inequality (IR4), and the
same display in the proof of Lemma 5.1:
`max {w/2, r, m - w} ≤ max {1/2, 1 - ηδ} m`, for `w > η c`, `r ≤ c - w`, `c ≥ δ m`,
`0 ≤ c ≤ m`, `η ≥ 0`. -/
theorem par_returned_parent_cap_bound {m c w r η δ : ℝ} (hc0 : 0 ≤ c) (hcm : c ≤ m)
    (hδm : δ * m ≤ c)
    (hw : η * c < w) (hr0 : 0 ≤ r) (hr : r ≤ c - w) (hη : 0 ≤ η) :
    max (w / 2) (max r (m - w)) ≤ max (1 / 2) (1 - η * δ) * m := by
  have hwm : w ≤ m := by linarith
  have hw0 : 0 ≤ w := by nlinarith
  have hm0 : 0 ≤ m := by linarith
  have hηc : η * (δ * m) ≤ η * c := mul_le_mul_of_nonneg_left hδm hη
  have h1 : w / 2 ≤ 1 / 2 * m := by linarith
  have h2 : m - w ≤ (1 - η * δ) * m := by nlinarith
  have h3 : r ≤ (1 - η * δ) * m := by linarith
  have e1 : 1 / 2 * m ≤ max (1 / 2) (1 - η * δ) * m :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hm0
  have e2 : (1 - η * δ) * m ≤ max (1 / 2) (1 - η * δ) * m :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hm0
  exact max_le (h1.trans e1) (max_le (h3.trans e2) (h2.trans e2))

/-- Paragraph "The returned parent cap" after Lemma A.28, first sentence, and the
end of Section 5.2: "(IR2)--(IR3) give `|Δ| ≤ θ n`; the unordered case is the larger
one, with ratio at most `2η(1-η)m/(m-1)`". The hypothesis `hIR2` holds in both pair
cases (with equality and factor `2` in the unordered case, by Lemma A.27). -/
theorem par_returned_parent_cap_fraction {Δ n w r m : ℕ} {η θ : ℝ} (hm : 2 ≤ m)
    (hIR2 : Δ * (m * (m - 1)) ≤ 2 * (w * r * n))
    (hIR3 : (w : ℝ) * r ≤ η * (1 - η) * (m : ℝ) ^ 2)
    (hθ : 2 * η * (1 - η) * m ≤ θ * (m - 1)) : (Δ : ℝ) ≤ θ * n := by
  have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hpos : (0 : ℝ) < m * ((m : ℝ) - 1) := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have h2 : (Δ : ℝ) * (m * ((m : ℝ) - 1)) ≤ 2 * (w * r * n) := by
    rw [← hm1]; exact_mod_cast hIR2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h3 : 2 * ((w : ℝ) * r * n) ≤ 2 * (η * (1 - η) * (m : ℝ) ^ 2 * n) := by
    have := mul_le_mul_of_nonneg_right hIR3 hn0
    linarith
  have h4 : 2 * (η * (1 - η) * (m : ℝ) ^ 2 * n) ≤ θ * n * (m * ((m : ℝ) - 1)) := by
    have := mul_le_mul_of_nonneg_right hθ (mul_nonneg hm0 hn0)
    nlinarith
  by_contra hlt
  push Not at hlt
  have := mul_lt_mul_of_pos_right hlt hpos
  linarith

/-- Section 7.5, item (iii): for `θ > 2η(1-η)` the condition
`2η(1-η) m/(m-1) ≤ θ` holds for all sufficiently large `m`. -/
theorem rectangle_fraction_eventually {η θ : ℝ} (hθ : 2 * η * (1 - η) < θ) :
    ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → 2 * η * (1 - η) * m ≤ θ * (m - 1) := by
  set a := 2 * η * (1 - η)
  refine ⟨⌈θ / (θ - a)⌉₊ + 2, by omega, fun m hm => ?_⟩
  have hpos : 0 < θ - a := by linarith
  have hceil : θ / (θ - a) ≤ (m : ℝ) := by
    have h1 := Nat.le_ceil (θ / (θ - a))
    have h2 : ((⌈θ / (θ - a)⌉₊ + 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    push_cast at h2
    linarith
  rw [div_le_iff₀ hpos] at hceil
  nlinarith

open GI.Rectangle

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- Paragraph "The returned parent cap" after Lemma A.28 (and the last sentence of
Lemma 5.1). Let `M, N` be the source and the aligned target matrix on `W × R`,
`W, R ⊆ C ⊆ Γ`, with every left twin class of `M` of size at most `|W|/2`, (IR3)'s
side conditions `|W| > η|C|`, `|R| ≤ |C| - |W|`, and `|C| ≥ δ q`, `q = |Γ|`.
The overcoset `leftOvercoset M N` (left projection of the permitted matrix
transporter, extended over `Γ \ W`, even) contains the ideal image of every
permitted matrix transporter, is a left coset of `leftGroup M` when nonempty, and
`aw(leftGroup M) ≤ ⌊β q⌋` for every `β ≥ max {1/2, 1 - ηδ}`. -/
theorem par_returned_parent_cap {W R C : Finset Γ} (hWC : W ⊆ C)
    {η δ β : ℝ} (hη : 0 ≤ η)
    (hC : δ * Fintype.card Γ ≤ C.card) (hW : η * C.card < W.card)
    (hR : R.card ≤ C.card - W.card) (hβ : max (1 / 2) (1 - η * δ) ≤ β)
    (M : W → R → Bool) (twins : ∀ u, 2 * (Semiregular.twins M u).card ≤ W.card) :
    (∀ (N : W → R → Bool) (h : permitted W R), MatrixTransports M N h →
      (h : alternatingGroup Γ) ∈ leftOvercoset M N) ∧
    (∀ (N : W → R → Bool) (g₀ : alternatingGroup Γ), g₀ ∈ leftOvercoset M N →
      ∀ g, g ∈ leftOvercoset M N ↔ g₀⁻¹ * g ∈ leftGroup M) ∧
    SectionCaps.Cap (leftGroup M) ⌊β * Fintype.card Γ⌋₊ := by
  refine ⟨fun N h hh => mem_leftOvercoset hh, fun N g₀ hg₀ g => leftOvercoset_coset hg₀ g, ?_⟩
  -- "The kernel of the right action ... permutes only left twin classes; the quotient
  -- acts on `R`. Hence the left projection has alternating width at most
  -- `max {w/2, r}`. Extend its full coset by arbitrary permutations of `Γ \ W`."
  have hcap := leftGroup_cap M (W.card / 2) (fun u => by have := twins u; omega)
  apply SectionCaps.mono hcap
  apply Nat.le_floor
  have hCq : (C.card : ℝ) ≤ Fintype.card Γ := by exact_mod_cast Finset.card_le_univ C
  have hWC' : W.card ≤ C.card := Finset.card_le_card hWC
  have hRC : (R.card : ℝ) ≤ C.card - W.card := by
    rw [← Nat.cast_sub hWC']; exact_mod_cast hR
  have hb := par_returned_parent_cap_bound (Nat.cast_nonneg _) hCq hC hW (Nat.cast_nonneg _) hRC hη
  have hq0 : (0 : ℝ) ≤ Fintype.card Γ := Nat.cast_nonneg _
  have hβq := mul_le_mul_of_nonneg_right hβ hq0
  have hsub : ((Fintype.card Γ - W.card : ℕ) : ℝ) = (Fintype.card Γ : ℝ) - W.card := by
    rw [Nat.cast_sub (hWC'.trans (Finset.card_le_univ C))]
  have hhalf : ((W.card / 2 : ℕ) : ℝ) ≤ (W.card : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have : W.card / 2 * 2 ≤ W.card := Nat.div_mul_le_self _ _
    exact_mod_cast this
  push_cast [hsub]
  refine le_trans ?_ (hb.trans hβq)
  exact max_le (le_max_of_le_right (le_max_right _ _))
    (max_le (le_max_of_le_left hhalf) (le_max_of_le_right (le_max_left _ _)))

end ReturnedCap

section Main51

open GI.PairRefinement GI.CoherentEntrance GI.Rectangle

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {n : ℕ}

/-- A side of the rectangle as a subset of the ideal set `Γ`: the color class at `x`,
moved into `Γ` by the embedding `ι : C ↪ Γ` (`C = Fin n`). -/
def idealSide (ι : Fin n ↪ Γ) (c : Coloring n) (side : Bool) (x : Fin n) (i : Color n) :
    Finset Γ :=
  (colorClass c side x i).map ι

/-- The color fiber and its ideal side are in bijection by `ι`. -/
noncomputable def idealSideEquiv (ι : Fin n ↪ Γ) (c : Coloring n) (side : Bool) (x : Fin n)
    (i : Color n) : ColorFiber c side x i ≃ idealSide ι c side x i :=
  Equiv.ofBijective
    (fun y => ⟨ι y.val, Finset.mem_map_of_mem ι ((mem_colorClass c side x y.val i).mpr y.property)⟩)
    ⟨fun y z h => Subtype.ext (ι.injective (congrArg Subtype.val h)), by
      rintro ⟨a, ha⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp ha
      exact ⟨⟨y, (mem_colorClass c side x y i).mp hy⟩, rfl⟩⟩

/-- The fiber matrix, carried to the ideal sides. -/
noncomputable def idealMatrix (ι : Fin n ↪ Γ) (c : Coloring n) (side : Bool) (x : Fin n)
    (i j k : Color n) : idealSide ι c side x i → idealSide ι c side x j → Bool :=
  fun a b => fiberMatrix c side x i j k ((idealSideEquiv ι c side x i).symm a)
    ((idealSideEquiv ι c side x j).symm b)

theorem twins_card_transfer {L L' S S' : Type*} [Fintype L] [Fintype L'] [Fintype S]
    [Fintype S'] [DecidableEq L'] (eL : L ≃ L') (eS : S ≃ S') (M : L → S → Bool) (a : L') :
    (Semiregular.twins (fun u v => M (eL.symm u) (eS.symm v)) a).card =
      (Semiregular.twins M (eL.symm a)).card := by
  have h : Semiregular.twins (fun u v => M (eL.symm u) (eS.symm v)) a =
      (Semiregular.twins M (eL.symm a)).map eL.toEmbedding := by
    ext z
    simp only [Semiregular.twins, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map_equiv]
    constructor
    · intro hz
      funext v
      simpa using congrFun hz (eS v)
    · intro hz
      funext v
      exact congrFun hz (eS.symm v)
  rw [h, Finset.card_map]

omit [Fintype Γ] [DecidableEq Γ] in
theorem card_idealSide (ι : Fin n ↪ Γ) (c : Coloring n) (side : Bool) (x : Fin n)
    (i : Color n) : (idealSide ι c side x i).card = (colorClass c side x i).card :=
  Finset.card_map ι

/-- **Lemma 5.1** (First-rectangle interface).

The coherent configuration `c` lives on `C = Fin n`, embedded in the ideal set `Γ`
(`q = |Γ|`) by `ι`, with `|C| ≥ δ q` (outcome 3 of the interface in Section 4).
The parameters satisfy `2/3 < η < 1` and `β ≥ max {1/2, 1 - ηδ}`
(Section 7.5, item (iii)).

Either the configuration gives a fixed-fraction restriction (the imprimitive
equal-block partition, or, at a source vertex `x`, a colored partition with all
classes of size at most `η|C|`), or the first entrance gives disjoint `W, R ⊆ C`
with a nontrivial semiregular matrix `M` (the certificate) such that
`|W| > η|C|`, `|R| ≤ |C| - |W|`, `|W||R| ≤ η(1-η) q²`, every left twin class has size
at most `|W|/2`, and the overcoset `leftOvercoset M N` built from the complete
permitted matrix transporter contains every parent isomorphism of the branch
(every permitted matrix transporter to the aligned target `N`), is a coset of
`leftGroup M`, and `aw(leftGroup M) ≤ βq`.

Stage 2 (machine level, not stated here): "with polynomially many choices" (the `n` branches for the
target of `x`, `lem_first_soj_rectangle_covers`). -/
theorem lem_main_rectangle (c : Coloring n) (hc : Coherent c) (side : Bool)
    (hh : Homogeneous c side) (hn : NontrivialOffDiagonal c side) (ι : Fin n ↪ Γ)
    {η δ β : ℝ} (hη : 2 / 3 < η) (hη1 : η < 1) (hC : δ * Fintype.card Γ ≤ n)
    (hβ : max (1 / 2) (1 - η * δ) ≤ β) :
    (¬ PrimitiveColorCuts c side ∧ ∃ a b : Fin n, a ≠ b ∧
      (∀ x y, (colorComponent c side (c (side, a, b)) x).card =
        (colorComponent c side (c (side, a, b)) y).card) ∧
      (∀ x, 2 ≤ (colorComponent c side (c (side, a, b)) x).card ∧
        2 * (colorComponent c side (c (side, a, b)) x).card ≤ n)) ∨
    (PrimitiveColorCuts c side ∧ ∀ x : Fin n,
      (∀ i, ((colorClass c side x i).card : ℝ) ≤ η * n) ∨
      ∃ cert : RectangleCertificate c side x η,
        Disjoint (idealSide ι c side x cert.leftColor) (idealSide ι c side x cert.rightColor) ∧
        η * n < ((idealSide ι c side x cert.leftColor).card : ℝ) ∧
        (idealSide ι c side x cert.rightColor).card ≤
          n - (idealSide ι c side x cert.leftColor).card ∧
        ((idealSide ι c side x cert.leftColor).card : ℝ) *
            (idealSide ι c side x cert.rightColor).card ≤
          η * (1 - η) * (Fintype.card Γ : ℝ) ^ 2 ∧
        (∀ u, 2 * (Semiregular.twins (idealMatrix ι c side x cert.leftColor cert.rightColor
          cert.edgeColor) u).card ≤ (idealSide ι c side x cert.leftColor).card) ∧
        (∀ (N : idealSide ι c side x cert.leftColor → idealSide ι c side x cert.rightColor →
            Bool) (h : permitted (idealSide ι c side x cert.leftColor)
              (idealSide ι c side x cert.rightColor)),
          MatrixTransports (idealMatrix ι c side x cert.leftColor cert.rightColor
            cert.edgeColor) N h →
          (h : alternatingGroup Γ) ∈ leftOvercoset (idealMatrix ι c side x cert.leftColor
            cert.rightColor cert.edgeColor) N) ∧
        (∀ (N : idealSide ι c side x cert.leftColor → idealSide ι c side x cert.rightColor →
            Bool) (g₀ : alternatingGroup Γ),
          g₀ ∈ leftOvercoset (idealMatrix ι c side x cert.leftColor cert.rightColor
            cert.edgeColor) N →
          ∀ g, g ∈ leftOvercoset (idealMatrix ι c side x cert.leftColor cert.rightColor
            cert.edgeColor) N ↔
            g₀⁻¹ * g ∈ leftGroup (idealMatrix ι c side x cert.leftColor cert.rightColor
              cert.edgeColor)) ∧
        SectionCaps.Cap (leftGroup (idealMatrix ι c side x cert.leftColor cert.rightColor
          cert.edgeColor)) ⌊β * Fintype.card Γ⌋₊) := by
  have hnq : n ≤ Fintype.card Γ := by
    simpa using Fintype.card_le_of_injective ι ι.injective
  -- "The construction is the first entrance described in Lemma A.28."
  rcases lem_first_soj_rectangle c hc side hh hn hnq (by linarith : (1 / 2 : ℝ) ≤ η) hη1 with
    himp | ⟨hp, hx⟩
  · exact Or.inl himp
  refine Or.inr ⟨hp, fun x => ?_⟩
  rcases hx x with hbal | ⟨cert, hdom, hR, harea, hdis, -, -, htw⟩
  · exact Or.inl hbal
  refine Or.inr ⟨cert, ?_⟩
  simp only [card_idealSide]
  have htw' : ∀ u, 2 * (Semiregular.twins (idealMatrix ι c side x cert.leftColor
      cert.rightColor cert.edgeColor) u).card ≤ (colorClass c side x cert.leftColor).card := by
    intro u
    have e := twins_card_transfer (idealSideEquiv ι c side x cert.leftColor)
      (idealSideEquiv ι c side x cert.rightColor)
      (fiberMatrix c side x cert.leftColor cert.rightColor cert.edgeColor) u
    exact (congrArg (2 * ·) e).trans_le (htw _)
  -- The ideal sides lie in the ideal image `C = ι(Fin n)` of the configuration.
  have hWC : idealSide ι c side x cert.leftColor ⊆ Finset.univ.map ι :=
    Finset.map_subset_map.mpr (Finset.subset_univ _)
  have hCcard : (Finset.univ.map ι).card = n := by simp
  have hcap := par_returned_parent_cap hWC (by linarith : (0 : ℝ) ≤ η)
    (C := Finset.univ.map ι) (δ := δ) (β := β) (by rw [hCcard]; exact hC)
    (by rw [hCcard, card_idealSide]; exact hdom)
    (by rw [hCcard, card_idealSide, card_idealSide]; exact hR) hβ
    (idealMatrix ι c side x cert.leftColor cert.rightColor cert.edgeColor)
    (by intro u; rw [card_idealSide]; exact htw' u)
  refine ⟨Finset.disjoint_map ι |>.mpr hdis, hdom, hR, harea, htw', hcap.1, hcap.2.1, hcap.2.2⟩

end Main51

/-! ### Parity and source--target alignment (paragraph after Lemma A.27) -/

section Alignment

open GI.Rectangle

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- Paragraph **"Parity and source--target alignment"**, first part. Let the source
and target rectangles have sides `W, R` and `W', R'`.
1. If corresponding sizes differ, the branch is empty: no permutation of `Γ` maps the
   source parts onto the target parts.
2. If the sizes agree and `|W| ≥ 3`, there is an even bijection of `Γ` taking the
   source parts to the target parts ("the sign of any alignment can be corrected
   inside its `W_Y` part"); it then takes `Y_X` to `Y_Y` as well.
3. "This fixes one alignment coset; the subgroup in Lemma A.27 then supplies all
   remaining possibilities": the even aligning permutations are exactly `g₀ P`, with
   `P = permitted W R`. -/
theorem par_parity_alignment {W R W' R' : Finset Γ} (hd : Disjoint W R) (hd' : Disjoint W' R') :
    ((∃ p : Perm Γ, p '' (W : Set Γ) = W' ∧ p '' (R : Set Γ) = R') →
      W.card = W'.card ∧ R.card = R'.card) ∧
    (W.card = W'.card → R.card = R'.card → 3 ≤ W.card →
      ∃ g₀ : alternatingGroup Γ, (g₀ : Perm Γ) '' (W : Set Γ) = W' ∧
        (g₀ : Perm Γ) '' (R : Set Γ) = R' ∧
        (g₀ : Perm Γ) '' (((W ∪ R)ᶜ : Finset Γ) : Set Γ) = (((W' ∪ R')ᶜ : Finset Γ) : Set Γ) ∧
        ∀ g : alternatingGroup Γ,
          ((g : Perm Γ) '' (W : Set Γ) = W' ∧ (g : Perm Γ) '' (R : Set Γ) = R') ↔
            g₀⁻¹ * g ∈ permitted W R) := by
  refine ⟨?_, fun hW hR h3 => ?_⟩
  · rintro ⟨p, hpW, hpR⟩
    have card_eq : ∀ S S' : Finset Γ, p '' (S : Set Γ) = S' → S.card = S'.card := by
      intro S S' h
      have e : S.map p.toEmbedding = S' := by
        apply Finset.coe_injective
        rw [Finset.coe_map]
        exact h
      rw [← e, Finset.card_map]
    exact ⟨card_eq W W' hpW, card_eq R R' hpR⟩
  · obtain ⟨g₀, hgW, hgR⟩ := exists_even_alignment hd hd' hW hR (by omega)
    refine ⟨g₀, hgW, hgR, ?_, fun g => alignment_coset g₀ hgW hgR g⟩
    rw [Finset.coe_compl, Finset.coe_compl, Set.image_compl_eq (g₀ : Perm Γ).bijective,
      Finset.coe_union, Finset.coe_union, Set.image_union, hgW, hgR]

/-- Paragraph **"Parity and source--target alignment"**, second part: "When
`|Y| ≥ 2`, the permitted group on `W × R` is the full `Sym(W) × Sym(R)`: a sign can
be corrected on `Y`. When `|Y| ≤ 1`, it is the index-two subgroup with even product
sign." Here `Y = Γ \ (W ∪ R)` and the image is `sideAction`. -/
theorem par_parity_permitted_image {W R : Finset Γ} (hd : Disjoint W R) :
    (2 ≤ (W ∪ R)ᶜ.card → (sideAction (W := W) (R := R)).range = ⊤) ∧
    ((W ∪ R)ᶜ.card ≤ 1 → ∀ p : Perm W × Perm R,
      p ∈ (sideAction (W := W) (R := R)).range ↔ sign p.1 * sign p.2 = 1) :=
  ⟨sideAction_range_eq_top hd, sideAction_mem_range_iff hd⟩

/-- Paragraph **"Parity and source--target alignment"**, last part: "The full ideal
transporter ... is obtained from the projected lifts by adjoining the pointwise
`(W ∪ R)`-stabilizer in the alternating group." Two permitted permutations have the
same projection to `Sym(W) × Sym(R)` exactly when they differ by an element fixing
`W ∪ R` pointwise. -/
theorem par_parity_full_transporter {W R : Finset Γ} (g h : permitted W R) :
    sideAction g = sideAction h ↔
      ∀ a, a ∈ W ∨ a ∈ R → (((g⁻¹ * h : permitted W R) : alternatingGroup Γ) : Perm Γ) a = a :=
  sideAction_eq_iff g h

end Alignment

/-! ### Algorithm `alg:auxiliary`: lifting an overcoset and continuing

The parent group `G` acts on the strings `X` and on the `q` labels `Γ` through
`π : G → Alt(Γ)`. An overcoset `E` on `Γ` with group `E₀` (`E = σ E₀` for every
`σ ∈ E`) is lifted to `π⁻¹(E) = τ H`, `H = π⁻¹(E₀)`, `π(τ) ∈ E`.
`LiftAndContinue(S₀, E)` "invokes `Continue` under `H` on `(x, y^{τ⁻¹})`, and
right-multiplies the returned answer by `τ`". Our actions are on the left, so the
answer of `Continue` under `H` on `(x, τ⁻¹ y)` is multiplied by `τ` on the left.

Stage 2 (machine level, not stated here): computing the lift `τ` and generators of `H` by constructive
membership, and the call to `Continue` itself; here `Continue` returns its exact
answer, the full `H`-transporter. -/

section Auxiliary

open GI.Rectangle

variable {Γ G X : Type*} [Fintype Γ] [DecidableEq Γ] [Group G] [MulAction G X]

/-- The exact answer of `Continue` under a subgroup `H`: its full transporter. -/
def continueAnswer (H : Subgroup G) (x y : X) : Set G := {h | h ∈ H ∧ h • x = y}

/-- `LiftAndContinue(S₀, E)`, for the overcoset with group `E₀` and a lift `τ` of one
of its points: the answer of `Continue` under `H = π⁻¹(E₀)` on `(x, τ⁻¹ y)`, multiplied
by `τ`. -/
def liftAndContinue (π : G →* alternatingGroup Γ) (E₀ : Subgroup (alternatingGroup Γ)) (τ : G)
    (x y : X) : Set G :=
  (fun h => τ * h) '' continueAnswer (E₀.comap π) x (τ⁻¹ • y)

/-- **`LiftAndContinue`, mathematical content.** If `E = σ E₀` for `σ = π(τ)`, then
1. the lift `π⁻¹(E)` is the coset `τ H`, `H = π⁻¹(E₀)`;
2. `LiftAndContinue` returns exactly the parent isomorphisms whose ideal image lies
   in `E` ("it checks the original coloring constraints while retaining the full
   lifted coset");
3. the new cap: the ideal image of `H` lies in `E₀`, so every cap of `E₀` holds for it
   ("It replaces the selected interval bound by the minimum of its old value and
   `βq`"). -/
theorem alg_auxiliary_lift_and_continue (π : G →* alternatingGroup Γ)
    (E : Set (alternatingGroup Γ)) (E₀ : Subgroup (alternatingGroup Γ)) (τ : G)
    (hE : ∀ σ, σ ∈ E ↔ (π τ)⁻¹ * σ ∈ E₀) (x y : X) :
    π ⁻¹' E = {g | τ⁻¹ * g ∈ E₀.comap π} ∧
    liftAndContinue π E₀ τ x y = {g | π g ∈ E ∧ g • x = y} ∧
    ∀ b : ℕ, SectionCaps.Cap E₀ b → SectionCaps.Cap ((E₀.comap π).map π) b := by
  have hlift : ∀ g : G, π g ∈ E ↔ τ⁻¹ * g ∈ E₀.comap π := by
    intro g
    rw [hE, Subgroup.mem_comap, map_mul, map_inv]
  refine ⟨Set.ext hlift, ?_, fun b hb => ?_⟩
  · ext g
    simp only [liftAndContinue, continueAnswer, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h, ⟨hH, hx⟩, rfl⟩
      refine ⟨(hlift _).mpr (by simpa using hH), ?_⟩
      rw [mul_smul, hx, smul_inv_smul]
    · rintro ⟨hg, hx⟩
      refine ⟨τ⁻¹ * g, ⟨(hlift g).mp hg, ?_⟩, by simp⟩
      rw [mul_smul, hx]
  · have hle : (E₀.comap π).map π ≤ E₀ := Subgroup.map_comap_le _ _
    exact SectionCaps.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle) hb

/-- **Algorithm `alg:auxiliary`, the rectangle branch.** The source rectangle has sides
`W, R` and matrix `M`; the target has sides `W', R'` and matrix `N'`. The even
alignment `a₀` maps `W` into `W'` and `R` into `R'` (`par_parity_alignment`), and
`N` is the aligned target matrix, `N(w, r) = N'(a₀ w, a₀ r)`. The rectangle answer
gives the overcoset `a₀ · leftOvercoset M N` on `Γ`, with group
`a₀ leftGroup(M) a₀⁻¹`; in left-coset form its points are `a₀ g₀ h`, `h ∈ leftGroup M`.
Let `τ` lift the point `a₀ g₀`, `g₀ ∈ leftOvercoset M N`. Then:
1. every parent isomorphism `g` of the branch (`g x = y`, and `π(g)` maps `W` to `W'`,
   `R` to `R'` and `M` to `N'`) lies in the returned continuation coset;
2. the continuation coset is exactly the set of parent isomorphisms in the lifted
   overcoset;
3. its group `H = π⁻¹(leftGroup M)` keeps every cap of `leftGroup M` (Lemma 5.1 gives
   `aw(leftGroup M) ≤ βq`). -/
theorem alg_auxiliary_rectangle_branch (π : G →* alternatingGroup Γ)
    {W R W' R' : Finset Γ} (a₀ : alternatingGroup Γ)
    (haW : (a₀ : Perm Γ) '' (W : Set Γ) = W') (haR : (a₀ : Perm Γ) '' (R : Set Γ) = R')
    (M : W → R → Bool) (N' : W' → R' → Bool)
    (hW : ∀ w : W, (a₀ : Perm Γ) w ∈ W') (hR : ∀ r : R, (a₀ : Perm Γ) r ∈ R')
    (g₀ : alternatingGroup Γ)
    (hg₀ : g₀ ∈ leftOvercoset M (fun w r => N' ⟨_, hW w⟩ ⟨_, hR r⟩))
    (τ : G) (hτ : π τ = a₀ * g₀) (x y : X) :
    (∀ g : G, g • x = y →
      ∀ (hgW : ∀ w : W, (π g : Perm Γ) w ∈ W') (hgR : ∀ r : R, (π g : Perm Γ) r ∈ R'),
        (∀ w r, N' ⟨_, hgW w⟩ ⟨_, hgR r⟩ = M w r) →
        g ∈ liftAndContinue π (leftGroup M) τ x y) ∧
    liftAndContinue π (leftGroup M) τ x y =
      {g | a₀⁻¹ * π g ∈ leftOvercoset M (fun w r => N' ⟨_, hW w⟩ ⟨_, hR r⟩) ∧ g • x = y} ∧
    ∀ b : ℕ, SectionCaps.Cap (leftGroup M) b →
      SectionCaps.Cap (((leftGroup M).comap π).map π) b := by
  set N : W → R → Bool := fun w r => N' ⟨_, hW w⟩ ⟨_, hR r⟩
  have hE : ∀ σ, σ ∈ {σ : alternatingGroup Γ | a₀⁻¹ * σ ∈ leftOvercoset M N} ↔
      (π τ)⁻¹ * σ ∈ leftGroup M := by
    intro σ
    rw [Set.mem_setOf_eq, leftOvercoset_coset hg₀, hτ, mul_inv_rev, mul_assoc]
  obtain ⟨-, heq, hcap⟩ := alg_auxiliary_lift_and_continue π _ (leftGroup M) τ hE x y
  refine ⟨fun g hgx hgW hgR hmat => ?_, heq, hcap⟩
  rw [heq]
  refine ⟨?_, hgx⟩
  -- After alignment, `a₀⁻¹ π(g)` is a permitted permutation that transports `M` to `N`.
  have hmaps : ∀ (S S' : Finset Γ), (a₀ : Perm Γ) '' (S : Set Γ) = S' →
      (∀ s : S, (π g : Perm Γ) s ∈ S') → ∀ s ∈ S, ((a₀⁻¹ * π g : alternatingGroup Γ) : Perm Γ) s ∈ S := by
    intro S S' ha hs s hsS
    have h1 : (π g : Perm Γ) s ∈ (S' : Set Γ) := hs ⟨s, hsS⟩
    rw [← ha] at h1
    obtain ⟨t, ht, hts⟩ := h1
    change ((a₀ : Perm Γ))⁻¹ ((π g : Perm Γ) s) ∈ S
    rw [← hts, Perm.inv_apply_self]
    exact ht
  have hP : a₀⁻¹ * π g ∈ permitted W R :=
    mem_sides_of_maps _ (hmaps W W' haW hgW) (hmaps R R' haR hgR)
  have htrans : MatrixTransports M N ⟨_, hP⟩ := by
    intro w r
    change N' ⟨(a₀ : Perm Γ) (((a₀ : Perm Γ))⁻¹ ((π g : Perm Γ) w)), _⟩
      ⟨(a₀ : Perm Γ) (((a₀ : Perm Γ))⁻¹ ((π g : Perm Γ) r)), _⟩ = M w r
    simp only [Perm.apply_inv_self]
    exact hmat w r
  exact mem_leftOvercoset htrans

/-- Algorithm `alg:auxiliary`: "The resulting continuation cosets are kept as a list
... covering this aggregation branch." Given overcosets `Es` on `Γ` such that every
parent isomorphism of the branch has its ideal image in one of them, the exact
continuation answers `{g ∈ π⁻¹(E) | g x = y}` cover the branch, and each consists of
parent isomorphisms only. -/
theorem alg_auxiliary_cover (π : G →* alternatingGroup Γ) (Es : List (Set (alternatingGroup Γ)))
    (branch : G → Prop) (x y : X)
    (hcover : ∀ g : G, g • x = y → branch g → ∃ E ∈ Es, π g ∈ E) :
    (∀ g : G, g • x = y → branch g →
      ∃ A ∈ Es.map (fun E => {g : G | π g ∈ E ∧ g • x = y}), g ∈ A) ∧
    (∀ A ∈ Es.map (fun E => {g : G | π g ∈ E ∧ g • x = y}), ∀ g ∈ A, g • x = y) := by
  refine ⟨fun g hg hb => ?_, fun A hA g hgA => ?_⟩
  · obtain ⟨E, hE, hgE⟩ := hcover g hg hb
    exact ⟨_, List.mem_map_of_mem hE, hgE, hg⟩
  · obtain ⟨E, -, rfl⟩ := List.mem_map.mp hA
    exact hgA.2

end Auxiliary

end GI.Paper
