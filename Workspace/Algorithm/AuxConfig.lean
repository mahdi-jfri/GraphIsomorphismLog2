import Workspace.Algorithm.AggregationPlan

/-!
# Pair configurations on the labels and the configuration query

Section 4.1 ("From the tests to an auxiliary graph") lists three outcomes of the aggregation.
The third is "a nontrivial homogeneous coherent configuration on `C ⊆ Γ`, with `|C| ≥ δq`".
Cases 2b and 3 of Section A.3 end there. This file gives that outcome a concrete form and
builds the query of Algorithm `alg:auxiliary` for small `q`.

## The configuration

A `PairCfg q` is a coloring `col` of the ordered pairs of labels together with a diagonal color
`j`. Its fiber is `C = {a | col(a, a) = j}`. `Perm(Γ)` acts on it by relabeling. Both
constructions of the paper produce such an object canonically from the structure of a string:
in Case 2b the refined orbital graph, in Case 3 the pair skeleton of the Design Lemma. A parent
isomorphism `g` of a branch therefore maps the configuration `P_X` of the source to the
configuration `P_Y` of the target: `π(g) • P_X = P_Y`.

`PairCfg.Good P δ` says that `col` restricted to the fiber is a coherent configuration (equal
colors have equal equality pattern, equal converse colors and equal intersection numbers inside
`C`), that it has two different off-diagonal colors, and that `|C| ≥ δq`. It is homogeneous by
the choice of `C`.

`PairCfg.coloring` turns the restriction to `C` into a `GI.PairRefinement.Coloring` on
`Fin |C|`, so that Lemma A.12 (`GI.Paper.lem_exact_configuration`) applies: every group of even
label permutations that maps `C` onto itself and keeps the colors has `aw ≤ βq`. In particular
the group `K` of its proof (`PairCfg.autE`: such permutations that also keep the outer color
classes) has this cap (`PairCfg.autE_cap`).

## The configuration query

Algorithm `alg:auxiliary`, the branch `q ≤ λ`: "`I ← Solve` on the full colored-pair structures
`C_X², C_Y²`. Extend `I` using the outer color classes, fixed anchors, and parity. Append the
resulting nonempty overcoset to `ℰ`." And after the algorithm: "The small-configuration call
uses the action induced by all permutations of `C_X` on ordered pairs; it has at most `q²`
positions."

`pairState` is that call: the positions are the ordered pairs of `[n]`, `n = |C_X| = |C_Y|`,
the group is the diagonal action of `Sym(n)`, and the two colorings are the pair colors of `C_X`
and `C_Y`, numbered by fixed enumerations. `cfgQuery` reads off its answer an even label
permutation that agrees on `C_X` with an element of the answer ("Extend `I` … and parity").
`cfgItem` is the item: the query, with the group `autE P_X`. `cfgItem_valid` proves its facts:
the cap from Lemma A.12, the call type (a fresh `Solve` call on `n² ≤ q² ≤ N^{2α}` positions,
Section 6: "An auxiliary configuration on `q ≤ λ` labels is an allowed exception: it starts a
fresh call on at most `q² ≤ N^{2α}` positions"), soundness from the coset statement, and
completeness from the exactness of the call (`cfgQuery_covers`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.PairRefinement GI.ExactConfiguration

/-! ### Pair configurations on the labels -/

/-- **A pair configuration on the labels** `[q]`: a coloring of the ordered pairs and the color
`j` of the diagonal of its fiber `C = {a | col(a, a) = j}`. -/
@[ext] structure PairCfg (q : ℕ) where
  col : Fin q → Fin q → ℕ
  j : ℕ

namespace PairCfg

variable {q : ℕ}

/-- Relabeling of a pair configuration. -/
instance : MulAction (Perm (Fin q)) (PairCfg q) where
  smul σ P := ⟨fun a b => P.col (σ⁻¹ a) (σ⁻¹ b), P.j⟩
  one_smul P := by
    ext
    · rfl
    · rfl
  mul_smul σ τ P := by
    ext a b
    · change P.col ((σ * τ)⁻¹ a) ((σ * τ)⁻¹ b) = P.col (τ⁻¹ (σ⁻¹ a)) (τ⁻¹ (σ⁻¹ b))
      rw [mul_inv_rev]; rfl
    · rfl

@[simp] theorem smul_col (σ : Perm (Fin q)) (P : PairCfg q) (a b : Fin q) :
    (σ • P).col a b = P.col (σ⁻¹ a) (σ⁻¹ b) := rfl

@[simp] theorem smul_j (σ : Perm (Fin q)) (P : PairCfg q) : (σ • P).j = P.j := rfl

/-- The fiber `C = {a | col(a, a) = j}`. -/
def fiber (P : PairCfg q) : Finset (Fin q) := Finset.univ.filter fun a => P.col a a = P.j

theorem mem_fiber {P : PairCfg q} {a : Fin q} : a ∈ P.fiber ↔ P.col a a = P.j := by
  simp [fiber]

theorem mem_fiber_smul {σ : Perm (Fin q)} {P : PairCfg q} {a : Fin q} :
    a ∈ (σ • P).fiber ↔ σ⁻¹ a ∈ P.fiber := by
  rw [mem_fiber, mem_fiber, smul_col, smul_j]

/-- `σ` maps `P` to `P'` on the fiber of `P` and on the outer color classes: it maps the fiber
of `P` onto the fiber of `P'`, keeps the pair colors there, and maps every point outside the
fiber to a point of the same diagonal color (the outer color classes of Lemma A.12). -/
def Maps (P P' : PairCfg q) (σ : Perm (Fin q)) : Prop :=
  (∀ a, σ a ∈ P'.fiber ↔ a ∈ P.fiber) ∧
    (∀ a ∈ P.fiber, ∀ b ∈ P.fiber, P'.col (σ a) (σ b) = P.col a b) ∧
    ∀ a, a ∉ P.fiber → P'.col (σ a) (σ a) = P.col a a

theorem maps_of_smul {σ : Perm (Fin q)} {P P' : PairCfg q} (h : σ • P = P') : Maps P P' σ := by
  subst h
  refine ⟨fun a => ?_, fun a _ b _ => ?_, fun a _ => ?_⟩
  · rw [mem_fiber_smul, Perm.inv_apply_self]
  · rw [smul_col, Perm.inv_apply_self, Perm.inv_apply_self]
  · rw [smul_col, Perm.inv_apply_self]

theorem Maps.one (P : PairCfg q) : Maps P P 1 :=
  ⟨fun _ => Iff.rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩

theorem Maps.comp {P P' P'' : PairCfg q} {σ τ : Perm (Fin q)} (hσ : Maps P P' σ)
    (hτ : Maps P' P'' τ) : Maps P P'' (τ * σ) := by
  refine ⟨fun a => (hτ.1 (σ a)).trans (hσ.1 a), fun a ha b hb => ?_, fun a ha => ?_⟩
  · change P''.col (τ (σ a)) (τ (σ b)) = _
    rw [hτ.2.1 _ ((hσ.1 a).2 ha) _ ((hσ.1 b).2 hb), hσ.2.1 a ha b hb]
  · change P''.col (τ (σ a)) (τ (σ a)) = _
    rw [hτ.2.2 _ (fun h => ha ((hσ.1 a).1 h)), hσ.2.2 a ha]

theorem Maps.inv {P P' : PairCfg q} {σ : Perm (Fin q)} (hσ : Maps P P' σ) : Maps P' P σ⁻¹ := by
  have hm : ∀ a, σ⁻¹ a ∈ P.fiber ↔ a ∈ P'.fiber := fun a => by
    have := hσ.1 (σ⁻¹ a); rw [Perm.apply_inv_self] at this; exact this.symm
  refine ⟨hm, fun a ha b hb => ?_, fun a ha => ?_⟩
  · have := hσ.2.1 _ ((hm a).2 ha) _ ((hm b).2 hb)
    rw [Perm.apply_inv_self, Perm.apply_inv_self] at this
    exact this.symm
  · have := hσ.2.2 _ (fun h => ha ((hm a).1 h))
    rw [Perm.apply_inv_self] at this
    exact this.symm

/-- Two maps from `P` to `P'` differ by an automorphism of `P`. -/
theorem Maps.coset {P P' : PairCfg q} {σ₀ σ : Perm (Fin q)} (h₀ : Maps P P' σ₀)
    (h : Maps P P' σ) : Maps P P (σ₀⁻¹ * σ) :=
  h.comp h₀.inv

/-- **The group `K` of Lemma A.12**, in `Alt(Γ)`. The proof of Lemma A.12 says: "The oracle
returns its entire isomorphism coset and the full group `K_C = Aut(C)`. Combine it with the Young
groups on the outer color classes, align those classes, fix all previously individualized ideal
points, and impose alternating parity by the sign homomorphism." Here `K` is the even
permutations that map the fiber onto itself and keep its pair colors (`Aut(C)`), and keep every
outer color class, the points outside the fiber with one diagonal color (the Young groups). An
individualized point that is a singleton outer color class is fixed by this condition. -/
def autE (P : PairCfg q) : Subgroup (alternatingGroup (Fin q)) where
  carrier := {e | Maps P P (e : Perm (Fin q))}
  one_mem' := Maps.one P
  mul_mem' {e f} he hf := by
    change Maps P P ((e : Perm (Fin q)) * f)
    exact Maps.comp hf he
  inv_mem' {e} he := by
    change Maps P P ((e : Perm (Fin q)))⁻¹
    exact Maps.inv he

theorem mem_autE {P : PairCfg q} {e : alternatingGroup (Fin q)} :
    e ∈ P.autE ↔ Maps P P (e : Perm (Fin q)) := Iff.rfl

/-! #### The configuration facts -/

/-- The intersection numbers inside the fiber. -/
def inter (P : PairCfg q) (a b : Fin q) (i k : ℕ) : ℕ :=
  (P.fiber.filter fun z => P.col a z = i ∧ P.col z b = k).card

/-- **A nontrivial homogeneous coherent configuration on at least `δq` labels** (outcome 3 of
Section 4.1). On its fiber the coloring is a coherent configuration: equal colors have the same
equality pattern, the same converse color, and the same intersection numbers inside the fiber.
It has two different off-diagonal colors, and the fiber has at least `δq` points. -/
structure Good (P : PairCfg q) (δ : ℝ) : Prop where
  coherent : ∀ a ∈ P.fiber, ∀ b ∈ P.fiber, ∀ a' ∈ P.fiber, ∀ b' ∈ P.fiber,
    P.col a b = P.col a' b' →
      (a = b ↔ a' = b') ∧ P.col b a = P.col b' a' ∧ ∀ i k, P.inter a b i k = P.inter a' b' i k
  nontrivial : ∃ a ∈ P.fiber, ∃ b ∈ P.fiber, ∃ a' ∈ P.fiber, ∃ b' ∈ P.fiber,
    a ≠ b ∧ a' ≠ b' ∧ P.col a b ≠ P.col a' b'
  large : δ * q ≤ P.fiber.card

/-! #### Numbering the fiber -/

/-- The fiber numbered by `Fin n`, for `n = |C|`, in increasing order (`Finset.orderIsoOfFin`).
The numbering is fixed by the order of the labels, so a program computes it by sorting; no
choice is involved. -/
def emb (P : PairCfg q) {n : ℕ} (h : P.fiber.card = n) : Fin n ↪ Fin q :=
  ⟨fun i => (P.fiber.orderIsoOfFin h i).1, fun i i' hii' =>
    (P.fiber.orderIsoOfFin h).injective (Subtype.ext hii')⟩

theorem emb_mem (P : PairCfg q) {n : ℕ} (h : P.fiber.card = n) (i : Fin n) :
    P.emb h i ∈ P.fiber :=
  (P.fiber.orderIsoOfFin h i).2

/-- The index of a point of the fiber: the inverse of `emb`. -/
def idx (P : PairCfg q) {a : Fin q} (ha : a ∈ P.fiber) : Fin P.fiber.card :=
  (P.fiber.orderIsoOfFin rfl).symm ⟨a, ha⟩

theorem emb_idx (P : PairCfg q) {a : Fin q} (ha : a ∈ P.fiber) : P.emb rfl (P.idx ha) = a := by
  change ((P.fiber.orderIsoOfFin rfl) ((P.fiber.orderIsoOfFin rfl).symm ⟨a, ha⟩)).1 = a
  rw [OrderIso.apply_symm_apply]

theorem exists_emb (P : PairCfg q) {n : ℕ} (h : P.fiber.card = n) {a : Fin q}
    (ha : a ∈ P.fiber) : ∃ i, P.emb h i = a := by
  subst h
  exact ⟨P.idx ha, P.emb_idx ha⟩

theorem mem_range_emb (P : PairCfg q) {n : ℕ} (h : P.fiber.card = n) (a : Fin q) :
    a ∈ Set.range (P.emb h) ↔ a ∈ P.fiber := by
  constructor
  · rintro ⟨i, rfl⟩; exact P.emb_mem h i
  · intro ha; exact P.exists_emb h ha

/-! #### The pair-refinement coloring of the fiber -/

/-- The pair colors that occur on the fiber. -/
noncomputable def vals (P : PairCfg q) : Finset ℕ :=
  (Finset.univ : Finset (Fin P.fiber.card × Fin P.fiber.card)).image
    fun d => P.col (P.emb rfl d.1) (P.emb rfl d.2)

theorem col_mem_vals (P : PairCfg q) (i k : Fin P.fiber.card) :
    P.col (P.emb rfl i) (P.emb rfl k) ∈ P.vals :=
  Finset.mem_image.2 ⟨(i, k), Finset.mem_univ _, rfl⟩

theorem card_vals_lt (P : PairCfg q) :
    P.vals.card < Fintype.card (Domain P.fiber.card) + 1 := by
  have h1 : P.vals.card ≤ P.fiber.card * P.fiber.card :=
    Finset.card_image_le.trans (by simp)
  have h2 : Fintype.card (Domain P.fiber.card) = 2 * (P.fiber.card * P.fiber.card) := by
    simp [Domain, Fintype.card_prod, Fintype.card_bool]
  omega

/-- The code of a pair color in `Color n`: its rank among the colors that occur, in increasing
order (`Finset.orderIsoOfFin`, no choice). -/
noncomputable def enc (P : PairCfg q) (v : ℕ) : Color P.fiber.card :=
  if h : v ∈ P.vals then
    ⟨((P.vals.orderIsoOfFin rfl).symm ⟨v, h⟩ : ℕ),
      lt_trans ((P.vals.orderIsoOfFin rfl).symm ⟨v, h⟩).2 P.card_vals_lt⟩
  else 0

theorem enc_inj (P : PairCfg q) {v w : ℕ} (hv : v ∈ P.vals) (hw : w ∈ P.vals)
    (h : P.enc v = P.enc w) : v = w := by
  unfold enc at h
  rw [dif_pos hv, dif_pos hw] at h
  have h' : (P.vals.orderIsoOfFin rfl).symm ⟨v, hv⟩ = (P.vals.orderIsoOfFin rfl).symm ⟨w, hw⟩ := by
    have := congrArg Fin.val h
    exact Fin.ext this
  exact congrArg Subtype.val ((P.vals.orderIsoOfFin rfl).symm.injective h')

/-- **The pair-refinement coloring of the fiber**: the codes of the pair colors of `C`,
numbered by `Fin |C|`, the same on both sides. -/
noncomputable def coloring (P : PairCfg q) : Coloring P.fiber.card :=
  fun d => P.enc (P.col (P.emb rfl d.2.1) (P.emb rfl d.2.2))

theorem coloring_eq_iff (P : PairCfg q) (s s' : Bool) (i k i' k' : Fin P.fiber.card) :
    P.coloring (s, i, k) = P.coloring (s', i', k') ↔
      P.col (P.emb rfl i) (P.emb rfl k) = P.col (P.emb rfl i') (P.emb rfl k') := by
  constructor
  · exact P.enc_inj (P.col_mem_vals _ _) (P.col_mem_vals _ _)
  · intro h
    change P.enc _ = P.enc _
    rw [h]

/-- The color class of a code: either empty, or the color class of one pair color. -/
theorem coloring_eq_code (P : PairCfg q) (I : Color P.fiber.card) :
    (∀ s i k, P.coloring (s, i, k) ≠ I) ∨
      ∃ v, ∀ s i k, P.coloring (s, i, k) = I ↔ P.col (P.emb rfl i) (P.emb rfl k) = v := by
  by_cases h : ∃ s i k, P.coloring (s, i, k) = I
  · obtain ⟨s, i, k, hI⟩ := h
    refine Or.inr ⟨P.col (P.emb rfl i) (P.emb rfl k), fun s' i' k' => ?_⟩
    rw [← hI, P.coloring_eq_iff]
  · push Not at h
    exact Or.inl h

/-- The intersection numbers of the coloring are those of the fiber. -/
theorem intersection_coloring (P : PairCfg q) (i k : Fin P.fiber.card) (v w : ℕ) :
    (Finset.univ.filter fun z : Fin P.fiber.card =>
        P.col (P.emb rfl i) (P.emb rfl z) = v ∧ P.col (P.emb rfl z) (P.emb rfl k) = w).card =
      P.inter (P.emb rfl i) (P.emb rfl k) v w := by
  unfold inter
  apply Finset.card_bij (fun z _ => P.emb rfl z)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact Finset.mem_filter.2 ⟨P.emb_mem rfl z, hz⟩
  · intro z _ z' _ h
    exact (P.emb rfl).injective h
  · intro a ha
    obtain ⟨haC, hav⟩ := Finset.mem_filter.1 ha
    obtain ⟨z, rfl⟩ := P.exists_emb rfl haC
    exact ⟨z, Finset.mem_filter.2 ⟨Finset.mem_univ _, hav⟩, rfl⟩

/-- **The coloring is coherent**, from the coherence of the configuration on its fiber. -/
theorem coloring_coherent {P : PairCfg q} {δ : ℝ} (hP : P.Good δ) : Coherent P.coloring := by
  rintro ⟨s, i, k⟩ ⟨s', i', k'⟩ hab
  have hcol := (P.coloring_eq_iff s s' i k i' k').1 hab
  obtain ⟨hdiag, hconv, hint⟩ := hP.coherent _ (P.emb_mem rfl i) _ (P.emb_mem rfl k) _
    (P.emb_mem rfl i') _ (P.emb_mem rfl k') hcol
  refine ⟨?_, ?_, fun I J => ?_⟩
  · show decide (i = k) = decide (i' = k')
    have e1 : (i = k) ↔ (i' = k') := by
      rw [← (P.emb rfl).injective.eq_iff, ← (P.emb rfl).injective.eq_iff (a := i')]
      exact hdiag
    by_cases h : i = k
    · rw [decide_eq_true h, decide_eq_true (e1.1 h)]
    · rw [decide_eq_false h, decide_eq_false (fun h' => h (e1.2 h'))]
  · simp only [transpose]
    exact (P.coloring_eq_iff s s' k i k' i').2 hconv
  · simp only [intersection]
    rcases P.coloring_eq_code I with hI | ⟨v, hv⟩
    · have e : ∀ s₀ i₀ k₀, (Finset.univ.filter fun z : Fin P.fiber.card =>
          P.coloring (s₀, i₀, z) = I ∧ P.coloring (s₀, z, k₀) = J) = ∅ := by
        intro s₀ i₀ k₀
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and]
        exact fun h => absurd h (hI _ _ _)
      rw [e, e]
    rcases P.coloring_eq_code J with hJ | ⟨w, hw⟩
    · have e : ∀ s₀ i₀ k₀, (Finset.univ.filter fun z : Fin P.fiber.card =>
          P.coloring (s₀, i₀, z) = I ∧ P.coloring (s₀, z, k₀) = J) = ∅ := by
        intro s₀ i₀ k₀
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and]
        exact fun _ h => absurd h (hJ _ _ _)
      rw [e, e]
    have e : ∀ s₀ i₀ k₀, (Finset.univ.filter fun z : Fin P.fiber.card =>
        P.coloring (s₀, i₀, z) = I ∧ P.coloring (s₀, z, k₀) = J) =
        Finset.univ.filter fun z : Fin P.fiber.card =>
          P.col (P.emb rfl i₀) (P.emb rfl z) = v ∧ P.col (P.emb rfl z) (P.emb rfl k₀) = w := by
      intro s₀ i₀ k₀
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hv, hw]
    rw [e, e, P.intersection_coloring, P.intersection_coloring, hint]

theorem coloring_homogeneous (P : PairCfg q) (side : Bool) : Homogeneous P.coloring side := by
  intro i k
  change P.enc _ = P.enc _
  rw [mem_fiber.1 (P.emb_mem rfl i), mem_fiber.1 (P.emb_mem rfl k)]

theorem coloring_nontrivial {P : PairCfg q} {δ : ℝ} (hP : P.Good δ) (side : Bool) :
    NontrivialOffDiagonal P.coloring side := by
  obtain ⟨a, ha, b, hb, a', ha', b', hb', hab, hab', hne⟩ := hP.nontrivial
  obtain ⟨i, rfl⟩ := P.exists_emb rfl ha
  obtain ⟨k, rfl⟩ := P.exists_emb rfl hb
  obtain ⟨i', rfl⟩ := P.exists_emb rfl ha'
  obtain ⟨k', rfl⟩ := P.exists_emb rfl hb'
  refine ⟨i, k, i', k', fun h => hab (by rw [h]), fun h => hab' (by rw [h]), fun h => hne ?_⟩
  exact (P.coloring_eq_iff side side i k i' k').1 h

/-- The automorphisms of the configuration preserve the coloring of the fiber. -/
theorem autE_le_configGroup (P : PairCfg q) (side : Bool) :
    P.autE.map (alternatingGroup (Fin q)).subtype ≤ configGroup (P.emb rfl) P.coloring side := by
  rintro _ ⟨e, he, rfl⟩
  refine ⟨fun a => ?_, fun a b a' b' ha hb => ?_⟩
  · rw [P.mem_range_emb, P.mem_range_emb]
    exact he.1 a
  · change P.enc _ = P.enc _
    have := he.2.1 _ (P.emb_mem rfl a) _ (P.emb_mem rfl b)
    change P.col ((e : Perm (Fin q)) (P.emb rfl a)) ((e : Perm (Fin q)) (P.emb rfl b)) = _ at this
    rw [show (e : Perm (Fin q)) (P.emb rfl a) = P.emb rfl a' from ha,
      show (e : Perm (Fin q)) (P.emb rfl b) = P.emb rfl b' from hb] at this
    rw [this]

end PairCfg

/-! ### The cap of the configuration (Lemma A.12) -/

namespace PairCfg

/-- **The cap of a configuration branch** (Lemma A.12, `GI.Paper.lem_exact_configuration`, via
`AuxItem.config_cap`): for `β > max {1 - δ, 1/2}` there is `q₀` such that for `q ≥ q₀` the
automorphism group `autE P` of a good configuration has `aw ≤ βq`. -/
theorem autE_cap {P : Params} {δ : ℝ} (hβ : max (1 - δ) (1 / 2) < P.β) :
    ∃ q₀ : ℕ, ∀ {Ω C : Type} {S : State Ω C} (L : GiantLabels S) (X : PairCfg L.q),
      X.Good δ → q₀ ≤ L.q → GI.SectionCaps.Cap X.autE ⌊P.β * L.q⌋₊ := by
  obtain ⟨q₀, hq₀⟩ := AuxItem.config_cap (P := P) hβ
  refine ⟨q₀, fun L X hX hq => ?_⟩
  exact hq₀ L X.fiber.card X.coloring false (X.emb rfl) (coloring_coherent hX)
    (X.coloring_homogeneous false) (coloring_nontrivial hX false) hX.large hq X.autE
    (X.autE_le_configGroup false)

end PairCfg

/-! ### The pair structure call -/

/-- The diagonal action of `Sym(n)` on ordered pairs. -/
def diagHom (n : ℕ) : Perm (Fin n) →* Perm (Fin n × Fin n) where
  toFun p := Equiv.prodCongr p p
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem diagHom_apply (n : ℕ) (p : Perm (Fin n)) (d : Fin n × Fin n) :
    diagHom n p d = (p d.1, p d.2) := rfl

/-- **The pair structure state** of a configuration call (Algorithm `alg:auxiliary`: "`Solve` on
the full colored-pair structures `C_X², C_Y²`"; "the action induced by all permutations of
`C_X` on ordered pairs"): positions are the ordered pairs of `[n]`, the group is the diagonal
action of `Sym(n)`, the domain is everything, and the colorings are `x` and `y`. It is a fresh
call: empty hierarchy, no rows, `h = 2`, and its phase size is its number of positions. -/
def pairState {C' : Type} (n : ℕ) (x y : Fin n × Fin n → C') : State (Fin n × Fin n) C' :=
  ⟨(diagHom n).range, Set.univ, fun _ _ _ => Iff.rfl, x, y, [], none, false, 2, le_rfl, n * n,
    CounterInv.reset _ _ _ _,
    CarrierOK.none _ _ _⟩

theorem pairState_size {C' : Type} (n : ℕ) (x y : Fin n × Fin n → C') :
    (pairState n x y).size = n * n := by
  simp [State.size, pairState]

theorem mem_pairState_answer {C' : Type} {n : ℕ} {x y : Fin n × Fin n → C'} (p : Perm (Fin n)) :
    diagHom n p ∈ (pairState n x y).answer ↔ ∀ i k, y (p i, p k) = x (i, k) := by
  constructor
  · rintro ⟨-, h⟩ i k
    exact h (i, k) trivial
  · intro h
    exact ⟨⟨p, rfl⟩, fun d _ => h d.1 d.2⟩

theorem pairState_answer_diag {C' : Type} {n : ℕ} {x y : Fin n × Fin n → C'} {h : Perm (Fin n × Fin n)}
    (hh : h ∈ (pairState n x y).answer) : ∃ p, h = diagHom n p := by
  obtain ⟨⟨p, rfl⟩, -⟩ := hh
  exact ⟨p, rfl⟩

/-! ### The configuration query and its item -/

section Query

variable {P : Params} {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-- The pair colors of the fiber of `X`, numbered by `Fin n`. -/
noncomputable def pairCols (X : PairCfg L.q) {n : ℕ} (h : X.fiber.card = n) :
    Fin n × Fin n → ℕ :=
  fun d => X.col (X.emb h d.1) (X.emb h d.2)

open Classical in
/-- **The configuration query** (Algorithm `alg:auxiliary`, branch `q ≤ λ`): a `Solve` call on
the pair structures of the fibers of `X` and `Y`, both with `n` points. From the answer it reads
an even label permutation `σ` that agrees on `C_X` with an element `p` of the answer and maps
every outer color class of `X` onto the class of `Y` with the same color ("Extend `I` using the
outer color classes, fixed anchors, and parity"; Lemma A.12: "align those classes"); none if
there is no such element ("rejecting an empty parity coset"). When the outer classes of `X` and
`Y` have different sizes, no such `σ` exists. -/
noncomputable def cfgQuery (X Y : PairCfg L.q) (hc : X.fiber.card = Y.fiber.card) :
    AuxQuery P S L where
  mode := .solve
  Ω' := Fin X.fiber.card × Fin X.fiber.card
  C' := ℕ
  T := pairState X.fiber.card (pairCols X rfl) (pairCols Y hc.symm)
  read A :=
    if h : ∃ p : Perm (Fin X.fiber.card), diagHom _ p ∈ A ∧ ∃ σ : alternatingGroup (Fin L.q),
        (∀ i, (σ : Perm (Fin L.q)) (X.emb rfl i) = Y.emb hc.symm (p i)) ∧
          ∀ a, a ∉ X.fiber → Y.col ((σ : Perm (Fin L.q)) a) ((σ : Perm (Fin L.q)) a) = X.col a a then
      some h.choose_spec.2.choose
    else none
  solve_fin _ := inferInstance

/-- The representative read off the configuration answer maps `X` to `Y` on the fiber. -/
theorem cfgQuery_read_maps {X Y : PairCfg L.q} (hc : X.fiber.card = Y.fiber.card)
    {σ : alternatingGroup (Fin L.q)}
    (h : (cfgQuery (P := P) X Y hc).read (cfgQuery (P := P) X Y hc).T.answer = some σ) :
    PairCfg.Maps X Y (σ : Perm (Fin L.q)) := by
  classical
  simp only [cfgQuery] at h
  split_ifs at h with hex
  obtain ⟨hpA, -⟩ := hex.choose_spec
  have hσ := hex.choose_spec.2.choose_spec.1
  have hσo := hex.choose_spec.2.choose_spec.2
  rw [Option.some.injEq] at h
  subst h
  set p := hex.choose
  set σ := hex.choose_spec.2.choose
  have hp := (mem_pairState_answer p).1 hpA
  -- `σ` maps the fiber of `X` into the fiber of `Y`
  have hin : ∀ i, (σ : Perm (Fin L.q)) (X.emb rfl i) ∈ Y.fiber := fun i => by
    rw [hσ i]; exact Y.emb_mem _ _
  refine ⟨fun a => ⟨fun ha => ?_, fun ha => ?_⟩, fun a ha b hb => ?_, hσo⟩
  · -- the fibers have the same size, so `σ` maps `C_X` onto `C_Y`
    by_contra hna
    have himg : (X.fiber.map (σ : Perm (Fin L.q)).toEmbedding) ⊆ Y.fiber := by
      intro b hb
      obtain ⟨a', ha', rfl⟩ := Finset.mem_map.1 hb
      obtain ⟨i, rfl⟩ := X.exists_emb rfl ha'
      exact hin i
    have heq : X.fiber.map (σ : Perm (Fin L.q)).toEmbedding = Y.fiber :=
      Finset.eq_of_subset_of_card_le himg (by rw [Finset.card_map, hc])
    rw [← heq] at ha
    obtain ⟨a', ha', he⟩ := Finset.mem_map.1 ha
    have : a' = a := (σ : Perm (Fin L.q)).injective he
    exact hna (this ▸ ha')
  · obtain ⟨i, rfl⟩ := X.exists_emb rfl ha
    exact hin i
  · obtain ⟨i, rfl⟩ := X.exists_emb rfl ha
    obtain ⟨k, rfl⟩ := X.exists_emb rfl hb
    rw [hσ i, hσ k]
    exact hp i k

/-- **The configuration query is exact** (`AuxQuery.Covers`): every even label permutation that
maps `X` to `Y` on the fiber yields a representative. Its restriction to the fiber is an element
`p` of the answer of the pair-structure call, and the permutation itself is an even extension of
`p`. -/
theorem cfgQuery_covers {X Y : PairCfg L.q} (hc : X.fiber.card = Y.fiber.card) :
    (cfgQuery (P := P) X Y hc).Covers
      {σ | ∃ e : alternatingGroup (Fin L.q), (e : Perm (Fin L.q)) = σ ∧ PairCfg.Maps X Y σ} := by
  classical
  rintro _ ⟨e, rfl, hm⟩
  -- the restriction of `e` to the fiber, numbered by `Fin n`
  have hY : ∀ i, ∃ k, Y.emb hc.symm k = (e : Perm (Fin L.q)) (X.emb rfl i) := fun i =>
    Y.exists_emb hc.symm ((hm.1 _).2 (X.emb_mem rfl i))
  choose f hf using hY
  have hfi : Function.Injective f := fun i i' h => by
    have := congrArg (Y.emb hc.symm) h
    rw [hf, hf] at this
    exact (X.emb rfl).injective ((e : Perm (Fin L.q)).injective this)
  let p : Perm (Fin X.fiber.card) := Equiv.ofBijective f hfi.bijective_of_finite
  have hp : ∀ i, Y.emb hc.symm (p i) = (e : Perm (Fin L.q)) (X.emb rfl i) := hf
  have hpA : diagHom _ p ∈ (cfgQuery (P := P) X Y hc).T.answer := by
    change diagHom _ p ∈ (pairState _ _ _).answer
    rw [mem_pairState_answer]
    intro i k
    simp only [pairCols]
    rw [hp, hp]
    exact hm.2.1 _ (X.emb_mem rfl i) _ (X.emb_mem rfl k)
  have hex : ∃ p : Perm (Fin X.fiber.card), diagHom _ p ∈ (cfgQuery (P := P) X Y hc).T.answer ∧
      ∃ σ : alternatingGroup (Fin L.q),
        (∀ i, (σ : Perm (Fin L.q)) (X.emb rfl i) = Y.emb hc.symm (p i)) ∧
          ∀ a, a ∉ X.fiber → Y.col ((σ : Perm (Fin L.q)) a) ((σ : Perm (Fin L.q)) a) = X.col a a :=
    ⟨p, hpA, e, fun i => (hp i).symm, hm.2.2⟩
  simp only [cfgQuery]
  exact ⟨_, dif_pos hex⟩

open Classical in
/-- **The item of a configuration branch for `q ≤ λ`** (Algorithm `alg:auxiliary`): if the two
fibers have different sizes the branch is empty ("**if** `|C_X| ≠ |C_Y|` **then return** the
empty list"); otherwise the configuration query, with the group `autE X`. This follows the
proof of Lemma A.12: "Encode the configuration as its color string on `C²`, with the diagonal
action of `Sym(C)`" (`pairState`); "The oracle returns its entire isomorphism coset and the full
group `K_C = Aut(C)`" (the answer of the call); "Combine it with the Young groups on the outer
color classes, align those classes, … and impose alternating parity by the sign homomorphism"
(the representative of `cfgQuery`, which maps each outer class of `X` onto the class of `Y` with
the same color and is even, and the group `autE X`). If the outer classes cannot be aligned, or
no aligned map is even, the query reads nothing and the branch has no overcoset. -/
noncomputable def cfgItem (X Y : PairCfg L.q) : AuxItem P S L :=
  if hc : X.fiber.card = Y.fiber.card then .query [cfgQuery X Y hc] X.autE else .none

/-- `n² ≤ q² ≤ (N^α)² = N^{2α}`. -/
theorem sq_le_rpow {n q N : ℕ} {α : ℝ} (hn : n ≤ q) (hq : (q : ℝ) ≤ (N : ℝ) ^ α) :
    ((n * n : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 * α) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h1 : (n : ℝ) ≤ (N : ℝ) ^ α := le_trans (by exact_mod_cast hn) hq
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  rw [show 2 * α = α * 2 by ring, Real.rpow_mul hN, Real.rpow_two]
  push_cast
  nlinarith

/-- **The configuration item is valid** (Algorithm `alg:auxiliary` with Lemma A.12). Let
`β > max {1 - δ, 1/2}`. For `q ≥ q₀`, `q ≤ λ = N^α`, a good configuration `X` on at least `δq`
labels, and a branch whose parent isomorphisms map `X` to `Y`, the item `cfgItem X Y` satisfies
`AuxItem.Valid`. The cap is Lemma A.12 (`PairCfg.autE_cap`); the call is a fresh `Solve` call on
`n² ≤ N^{2α}` positions; soundness is the coset statement (`PairCfg.Maps.coset`); completeness is
the exactness of the call (`cfgQuery_covers`). -/
theorem cfgItem_valid {δ : ℝ} (hβ : max (1 - δ) (1 / 2) < P.β) :
    ∃ q₀ : ℕ, ∀ {Ω C : Type} {S : State Ω C} (L : GiantLabels S) {B : Set (Perm Ω)}
      (X Y : PairCfg L.q), X.Good δ → q₀ ≤ L.q → (L.q : ℝ) ≤ (S.N : ℝ) ^ P.α →
      (∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G, (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • X = Y) →
      (cfgItem (P := P) X Y : AuxItem P S L).Valid B := by
  obtain ⟨q₀, hq₀⟩ := PairCfg.autE_cap (P := P) hβ
  refine ⟨q₀, fun {Ω C S} L B X Y hX hq hlam hB => ?_⟩
  classical
  unfold cfgItem
  split_ifs with hc
  swap
  · -- different fiber sizes: the branch is empty
    show S.answer ∩ B = ∅
    refine Set.eq_empty_iff_forall_notMem.2 fun g hg => hc ?_
    obtain ⟨hgG, he⟩ := hB g hg
    rw [← he]
    refine Finset.card_bij (fun a _ => (L.π ⟨g, hgG⟩ : Perm (Fin L.q)) a) (fun a ha => ?_)
      (fun a _ b _ h => (L.π ⟨g, hgG⟩ : Perm (Fin L.q)).injective h) (fun b hb => ?_)
    · rw [PairCfg.mem_fiber_smul, Perm.inv_apply_self]; exact ha
    · rw [PairCfg.mem_fiber_smul] at hb
      exact ⟨_, hb, Perm.apply_inv_self _ _⟩
  refine ⟨hq₀ L X hX hq, by simp, fun Q hQ => ?_, fun Q hQ σ hσ g hg => ?_, fun hne => ?_⟩
  · -- a fresh `Solve` call on `n² ≤ N^{2α}` positions
    rw [List.mem_singleton] at hQ
    subst hQ
    left
    refine ⟨rfl, ?_⟩
    change ((pairState _ _ _).size : ℝ) ≤ _
    rw [pairState_size]
    exact sq_le_rpow (by simpa using Finset.card_le_univ X.fiber) hlam
  · -- soundness: two maps from `X` to `Y` differ by an automorphism of `X`
    rw [List.mem_singleton] at hQ
    subst hQ
    obtain ⟨hgG, he⟩ := hB g hg
    refine ⟨hgG, ?_⟩
    have h1 := cfgQuery_read_maps hc hσ
    have h2 := PairCfg.maps_of_smul he
    exact PairCfg.Maps.coset h1 h2
  · -- completeness: the call is exact
    refine AuxQuery.comp_of_covers (List.mem_singleton_self _) (cfgQuery_covers hc)
      (fun g hg => ?_) hne
    obtain ⟨hgG, he⟩ := hB g hg
    exact ⟨hgG, _, rfl, PairCfg.maps_of_smul he⟩

end Query

end GI.Algorithm
