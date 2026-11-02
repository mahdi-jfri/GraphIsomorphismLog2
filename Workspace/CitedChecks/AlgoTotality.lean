import Workspace.CitedChecks.AlgoChecks
import Workspace.Cited.AlgoCameron
import Workspace.Cited.AlgoLinear
import Workspace.Cited.AlgoDesign
import Workspace.Cited.AlgoRefinement

/-!
# Totality of the algorithm tasks

For each task of `Workspace/Cited/Algo*.lean`, a correct output within the task's output
bounds exists. This is the requirement "every instance has a correct output" of
`GI.Cited.Task`. The simplest cases (`exists_gensOf`, `preimage_total`, `orbits_total`) are in
`Workspace/CitedChecks/AlgoChecks.lean`. Two tasks rest on cited results: the joint refinement on
`KaryCoherentRefinement`, and Cameron recognition on `MarotiPrimitive`
(`cameronRecognition_total` in `AlgoCameron.lean`; `cameron_params_le` here bounds its output).
The Smith normal form task is not covered: the bit bound on its transformation matrices is the
content of the cited source. Nothing here is trusted.
-/

namespace GI.CitedChecks

open GI.Cited Equiv
open scoped Pointwise

/-! ### Tasks with a short totality proof -/

/-- **Totality of `MembershipTask`**: the answer is `1` or `0`. -/
theorem membership_total (I : MemberInst) : ∃ v : Val,
    (v = .nat 1 ∧ I.x ∈ gens I.gs) ∨ (v = .nat 0 ∧ I.x ∉ gens I.gs) := by
  by_cases h : I.x ∈ gens I.gs
  · exact ⟨_, Or.inl ⟨rfl, h⟩⟩
  · exact ⟨_, Or.inr ⟨rfl, h⟩⟩

/-- **Totality of `GroupOrderTask`**; the order has at most `n² + 1` bits (`card_lt_two_pow`). -/
theorem groupOrder_total (I : GroupInst) : ∃ v : Val, v = .nat (Nat.card (gens I.gs)) :=
  ⟨_, rfl⟩

/-- **Totality of the tasks whose output is one subgroup** (`PointwiseStabTask`,
`NormalClosureTask`, `DerivedSubgroupTask`, `NormalizedIntersectionTask`,
`QuotientCentralizerTask`, `VectorStabilizerTask`): each asks for `GensOf H` of a subgroup `H`,
which exists by `exists_gensOf`. -/
theorem pointwiseStab_total (I : PointsInst) : ∃ v, GensOf (pointwiseStab (gens I.gs) I.S) v :=
  exists_gensOf _

theorem normalClosure_total (I : TwoListInst) : ∃ v, GensOf (Subgroup.closure
    {x | ∃ g ∈ gens (I.gs ++ I.hs), ∃ h ∈ I.hs, x = g * h * g⁻¹}) v :=
  exists_gensOf _

theorem derivedSubgroup_total (I : GroupInst) : ∃ v, GensOf ⁅gens I.gs, gens I.gs⁆ v :=
  exists_gensOf _

theorem normalizedIntersection_total (I : NormalizedInst) :
    ∃ v, GensOf (gens I.gs ⊓ gens I.ns) v :=
  exists_gensOf _

theorem quotientCentralizer_total (I : QuotCentInst) : ∃ v, GensOf (quotCentralizer I) v :=
  exists_gensOf _

theorem vectorStabilizer_total (I : VecStabInst) :
    ∃ v, GensOf ((vecStab I).map (gens I.gs).subtype) v :=
  exists_gensOf _

/-- **Totality of `NormalizedFactorTask`**: the factorization is the field `mem` of the
instance. -/
theorem normalizedFactor_total (I : FactorInst) : ∃ v : Val, ∃ g ∈ gens I.gs, ∃ m ∈ gens I.ns,
    I.x = g * m ∧ v = .list [encPerm g, encPerm m] := by
  obtain ⟨g, hg, m, hm, hx⟩ := I.mem
  exact ⟨_, g, hg, m, hm, hx, rfl⟩

/-- **Totality of `SolvableCosetIntersectionTask`**: either `Gx ∩ H` is empty, or it has an
element `y`, and `G ∩ H` has a generating list of at most `n²` permutations. -/
theorem solvableCosetIntersection_total (I : SolvCosetInst) : ∃ v : Val,
    (v = .nat 0 ∧ ∀ g ∈ gens I.gs, g * I.x ∉ gens I.hs) ∨
    ∃ y : Perm (Fin I.n), (∃ g ∈ gens I.gs, y = g * I.x) ∧ y ∈ gens I.hs ∧
      ∃ L : Val, v = .list [encPerm y, L] ∧ GensOf (gens I.gs ⊓ gens I.hs) L := by
  by_cases h : ∃ g ∈ gens I.gs, g * I.x ∈ gens I.hs
  · obtain ⟨g, hg, hy⟩ := h
    obtain ⟨L, hL⟩ := exists_gensOf (gens I.gs ⊓ gens I.hs)
    exact ⟨_, Or.inr ⟨_, ⟨g, hg, rfl⟩, hy, L, rfl, hL⟩⟩
  · push Not at h
    exact ⟨_, Or.inl ⟨rfl, h⟩⟩


/-! ### Series -/

section Chains

variable {G : Type*} [Group G] [Finite G]

/-- A step of a series: `B` is a proper subgroup of `A` allowed by `Q`, and no subgroup allowed
by `Q` lies strictly between them. -/
def SeriesStep (Q : Subgroup G → Subgroup G → Prop) (A B : Subgroup G) : Prop :=
  B < A ∧ Q A B ∧ ∀ M, B ≤ M → M ≤ A → Q A M → M = B ∨ M = A

/-- **Existence of a series.** If `Q A ⊥` for every `A`, then every `K` starts a chain of
`SeriesStep Q` steps that ends at `⊥`. The next term below `K` is an allowed proper subgroup of
largest order; it exists since `⊥` is allowed, and it leaves no allowed subgroup strictly in
between, since such a subgroup would have a larger order. The induction is on `|K|`. -/
theorem exists_series (Q : Subgroup G → Subgroup G → Prop) (hQ : ∀ A, Q A ⊥) (K : Subgroup G) :
    ∃ rest : List (Subgroup G), (K :: rest).IsChain (SeriesStep Q) ∧
      (K :: rest).getLast? = some ⊥ := by
  classical
  induction hK : Nat.card K using Nat.strong_induction_on generalizing K with
  | _ c ih =>
  by_cases hbot : K = ⊥
  · exact ⟨[], by simp, by simp [hbot]⟩
  have hex : ∃ d, ∃ M, M < K ∧ Q K M ∧ Nat.card M + d = Nat.card K :=
    ⟨Nat.card K - 1, ⊥, bot_lt_iff_ne_bot.mpr hbot, hQ K, by
      have : 0 < Nat.card K := Nat.card_pos
      simp; omega⟩
  obtain ⟨N, hNK, hQN, hd⟩ := Nat.find_spec hex
  have hmax : ∀ M, M < K → Q K M → Nat.card M ≤ Nat.card N := by
    intro M hM hQM
    have hle := Subgroup.card_le_of_le hM.le
    have := Nat.find_min' hex ⟨M, hM, hQM, Nat.add_sub_of_le hle⟩
    omega
  have hstep : SeriesStep Q K N := by
    refine ⟨hNK, hQN, fun M hNM hMK hQM => ?_⟩
    by_cases hMK' : M = K
    · exact Or.inr hMK'
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge hNM
        (hmax M (lt_of_le_of_ne hMK hMK') hQM)).symm
  have hlt : Nat.card N < c := by
    have := two_mul_card_le_of_lt hNK
    have : 0 < Nat.card N := Nat.card_pos
    omega
  obtain ⟨rest, hch, hlast⟩ := ih _ hlt N rfl
  refine ⟨N :: rest, List.IsChain.cons_cons hstep hch, ?_⟩
  rw [List.getLast?_cons_cons]
  exact hlast

/-- A chain of proper subgroups starting at `A` with `m` further terms has `2^m ≤ |A|`, since
each step at least halves the order (`two_mul_card_le_of_lt`). -/
theorem two_pow_le_card_of_chain : ∀ (A : Subgroup G) (rest : List (Subgroup G)),
    (A :: rest).IsChain (fun A B => B < A) → 2 ^ rest.length ≤ Nat.card A
  | A, [], _ => by have : 0 < Nat.card A := Nat.card_pos; simp only [List.length_nil, pow_zero]; omega
  | A, B :: rest, h => by
    rw [List.isChain_cons_cons] at h
    have := two_pow_le_card_of_chain B rest h.2
    have := two_mul_card_le_of_lt h.1
    rw [List.length_cons, pow_succ]
    omega

end Chains

/-! ### Composition and chief series -/

section Series

variable {n : ℕ}

/-- Every list of at most `n² + 1` subgroups of `Sym(n)` has a `SeriesOf` value: give each term a
generating list of at most `n²` permutations (`exists_gensOf`). -/
theorem seriesOf_of_list {P : List (Subgroup (Perm (Fin n))) → Prop}
    (Hs : List (Subgroup (Perm (Fin n)))) (hlen : Hs.length ≤ n ^ 2 + 1) (hP : P Hs) :
    ∃ v, SeriesOf P v := by
  have hg : ∀ H : Subgroup (Perm (Fin n)), ∃ hs : List (Perm (Fin n)),
      hs.length ≤ n ^ 2 ∧ gens hs = H := fun H => by
    obtain ⟨v, hs, -, hl, hg⟩ := exists_gensOf H
    exact ⟨hs, hl, hg⟩
  choose f hf1 hf2 using hg
  refine ⟨_, Hs.map f, rfl, by simpa using hlen, ?_, ?_⟩
  · intro hs hm
    obtain ⟨H, -, rfl⟩ := List.mem_map.mp hm
    exact hf1 H
  · rw [List.map_map]
    have : (gens ∘ f) = id := funext hf2
    rw [this, List.map_id]
    exact hP

/-- A series of `SeriesStep` steps that starts at a subgroup of `Sym(n)` has at most `n² + 1`
terms: `2^(terms - 1) ≤ |G| < 2^(n² + 1)` (`two_pow_le_card_of_chain`, `card_lt_two_pow`). -/
theorem series_length_le {Q : Subgroup (Perm (Fin n)) → Subgroup (Perm (Fin n)) → Prop}
    {G : Subgroup (Perm (Fin n))} {rest : List (Subgroup (Perm (Fin n)))}
    (h : (G :: rest).IsChain (SeriesStep Q)) : (G :: rest).length ≤ n ^ 2 + 1 := by
  have h1 := two_pow_le_card_of_chain G rest (h.imp fun _ _ hs => hs.1)
  have h2 := card_lt_two_pow G
  have h3 : 2 ^ rest.length < 2 ^ (n ^ 2 + 1) := lt_of_le_of_lt h1 h2
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h3
  simp only [List.length_cons]
  omega

/-- **Totality of `CompositionSeriesTask`.** Series of `SeriesStep` steps where each term is
normalized by the one before are composition series. -/
theorem compositionSeries_total (G : Subgroup (Perm (Fin n))) :
    ∃ v, SeriesOf (IsCompositionSeries G) v := by
  obtain ⟨rest, hch, hlast⟩ := exists_series
    (fun A M => ∀ x ∈ A, ∀ y ∈ M, x * y * x⁻¹ ∈ M)
    (fun A x _ y hy => by rw [Subgroup.mem_bot] at hy ⊢; simp [hy]) G
  refine seriesOf_of_list _ (series_length_le hch) ⟨rfl, hlast, fun i hi => ?_⟩
  exact List.isChain_iff_getElem.mp hch i hi

/-- **Totality of `ChiefSeriesTask`.** Series of `SeriesStep` steps where each term is
normalized by `G` are chief series; the first term `G` is normalized by itself. -/
theorem chiefSeries_total (G : Subgroup (Perm (Fin n))) :
    ∃ v, SeriesOf (IsChiefSeries G) v := by
  obtain ⟨rest, hch, hlast⟩ := exists_series
    (fun _ M => ∀ x ∈ G, ∀ y ∈ M, x * y * x⁻¹ ∈ M)
    (fun A x _ y hy => by rw [Subgroup.mem_bot] at hy ⊢; simp [hy]) G
  have hstep := List.isChain_iff_getElem.mp hch
  refine seriesOf_of_list _ (series_length_le hch) ⟨rfl, hlast, ?_, fun i hi => ?_⟩
  · intro H hH
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hH
    rcases j with _ | i
    · intro x hx y hy
      exact G.mul_mem (G.mul_mem hx hy) (G.inv_mem hx)
    · exact (hstep i hj).2.1
  · exact ⟨(hstep i hi).1, fun N h1 h2 h3 => (hstep i hi).2.2 N h1 h2 h3⟩

end Series

/-! ### Minimal block systems -/


section Blocks

variable {n : ℕ}

/-- The number of classes of a labeling. -/
def numClasses (lab : Fin n → ℕ) : ℕ := (Finset.univ.image lab).card

/-- A coarser labeling has at most as many classes, and fewer if it merges two classes. The
classes of `lab'` are the images of those of `lab` under a map `g` with `g (lab i) = lab' i`. -/
theorem numClasses_lt_of_coarser {lab lab' : Fin n → ℕ}
    (hc : ∀ i j, lab i = lab j → lab' i = lab' j) :
    numClasses lab' ≤ numClasses lab ∧
      ((∃ i j, lab i ≠ lab j ∧ lab' i = lab' j) → numClasses lab' < numClasses lab) := by
  classical
  let g : ℕ → ℕ := fun a => if h : ∃ i, lab i = a then lab' h.choose else 0
  have hg : ∀ i, g (lab i) = lab' i := by
    intro i
    have h : ∃ j, lab j = lab i := ⟨i, rfl⟩
    simp only [g, dif_pos h]
    exact hc _ _ h.choose_spec
  have himg : Finset.univ.image lab' = (Finset.univ.image lab).image g := by
    rw [Finset.image_image]
    congr 1
    funext i
    exact (hg i).symm
  unfold numClasses
  rw [himg]
  refine ⟨Finset.card_image_le, fun ⟨i, j, hne, heq⟩ => ?_⟩
  refine lt_of_le_of_ne Finset.card_image_le fun he => ?_
  have hinj := Finset.card_image_iff.mp he
  exact hne (hinj (by simp) (by simp) (by rw [hg, hg, heq]))

/-- `IsMinimalBlocks` depends only on which points share a label. -/
theorem isMinimalBlocks_congr {G : Subgroup (Perm (Fin n))} {lab lab' : Fin n → ℕ}
    (he : ∀ i j, lab i = lab j ↔ lab' i = lab' j) (h : IsMinimalBlocks G lab) :
    IsMinimalBlocks G lab' := by
  obtain ⟨hinv, ⟨i, j, hij⟩, hmin⟩ := h
  refine ⟨fun g hg a b => ?_, ⟨i, j, fun e => hij ((he i j).mpr e)⟩, fun l hl hc => ?_⟩
  · rw [← he, ← he]; exact hinv g hg a b
  · rcases hmin l hl (fun a b e => hc a b ((he a b).mp e)) with h1 | h1
    · exact Or.inl fun a b => (h1 a b).trans (he a b)
    · exact Or.inr h1

/-- **Totality of `MinimalBlocksTask`.** Among the invariant labelings with at least two
classes (the labeling of each point by itself is one, as `n ≥ 2`) take one with the fewest
classes. A coarser invariant labeling with at least two classes has at least as many classes, so
it has the same classes (`numClasses_lt_of_coarser`). Then rename each label to the least point
of its class, so the labels are below `n` (`isMinimalBlocks_congr`). -/
theorem minimalBlocks_total (I : TransitiveInst) : ∃ v, LabelsOf (IsMinimalBlocks (gens I.gs)) v := by
  classical
  set G := gens I.gs
  let Good : (Fin I.n → ℕ) → Prop := fun lab => InvariantLabeling G lab ∧ ∃ i j, lab i ≠ lab j
  have hex : ∃ k, ∃ lab, Good lab ∧ numClasses lab = k := by
    refine ⟨_, fun i => (i : ℕ), ⟨fun g _ a b => ?_, ⟨0, by have := I.two_le; omega⟩,
      ⟨1, by have := I.two_le; omega⟩,
      by simp⟩, rfl⟩
    simp only [Fin.val_inj]
    exact g.injective.eq_iff
  obtain ⟨lab, ⟨hinv, hne⟩, hk⟩ := Nat.find_spec hex
  have hmin : IsMinimalBlocks G lab := by
    refine ⟨hinv, hne, fun l hl hc => ?_⟩
    by_cases hall : ∀ i j, l i = l j
    · exact Or.inr hall
    left
    push Not at hall
    have hge := Nat.find_min' hex ⟨l, ⟨hl, hall⟩, rfl⟩
    obtain ⟨-, hlt⟩ := numClasses_lt_of_coarser hc
    intro i j
    refine ⟨fun e => ?_, hc i j⟩
    by_contra hij
    have := hlt ⟨i, j, hij, e⟩
    omega
  -- rename the labels
  let rep : Fin I.n → Fin I.n := fun i => (Finset.univ.filter fun j => lab j = lab i).min' ⟨i, by simp⟩
  have hrep : ∀ i, lab (rep i) = lab i := fun i => by
    have := Finset.min'_mem (Finset.univ.filter fun j => lab j = lab i) ⟨i, by simp⟩
    simpa using this
  have he : ∀ i j, lab i = lab j ↔ (rep i : ℕ) = rep j := by
    intro i j
    constructor
    · intro e
      simp only [rep, e]
    · intro e
      rw [← hrep i, ← hrep j, Fin.val_inj.mp e]
  exact ⟨_, fun i => rep i, rfl, fun i => (rep i).isLt, isMinimalBlocks_congr he hmin⟩

end Blocks

/-! ### Sylow subgroups -/

/-- **Totality of `SylowTask`.** A Sylow `p`-subgroup of `G` exists (`Sylow.nonempty`), and its
image in `Sym(n)` has index prime to `p` (`Sylow.not_dvd_index`). -/
theorem sylow_total (I : SylowInst) : ∃ v, ∃ S, GensOf S v ∧ IsSylowOf I.p (gens I.gs) S := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  obtain ⟨P⟩ : Nonempty (Sylow I.p (gens I.gs)) := inferInstance
  set S := (P : Subgroup (gens I.gs)).map (gens I.gs).subtype
  have hS : S.subgroupOf (gens I.gs) = P :=
    Subgroup.comap_map_eq_self_of_injective (gens I.gs).subtype_injective _
  obtain ⟨v, hv⟩ := exists_gensOf S
  refine ⟨v, S, hv, Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_⟩
  rw [hS]
  exact Sylow.not_dvd_index P


/-- A subgroup `P ≤ G` with `IsSylowOf p G P`, as a Sylow subgroup of `G`. -/
noncomputable def toSylowOf {n p : ℕ} [Fact p.Prime] {G P : Subgroup (Perm (Fin n))}
    (h : IsSylowOf p G P) : Sylow p G :=
  IsPGroup.toSylow (h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe h.1).symm) h.2.2

/-- **Totality of `SylowConjugateTask`**, by Sylow's conjugacy theorem: `G` acts transitively
by conjugation on its Sylow `p`-subgroups (`MulAction.exists_smul_eq`). -/
theorem sylowConjugate_total (I : SylowConjInst) : ∃ v, ∃ g ∈ gens I.gs, v = encPerm g ∧
      ∀ x, x ∈ gens I.P₂ ↔ g * x * g⁻¹ ∈ gens I.P₁ := by
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (gens I.gs) (toSylowOf I.syl₁) (toSylowOf I.syl₂)
  refine ⟨_, (h : Perm (Fin I.n))⁻¹, (gens I.gs).inv_mem h.2, rfl, fun x => ?_⟩
  have key : ∀ z : gens I.gs, z ∈ (toSylowOf I.syl₂ : Subgroup (gens I.gs)) ↔
      h⁻¹ * z * h ∈ (toSylowOf I.syl₁ : Subgroup (gens I.gs)) := by
    intro z
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp
  constructor
  · intro hx
    have hxG : x ∈ gens I.gs := I.syl₂.1 hx
    have := (key ⟨x, hxG⟩).mp hx
    simpa [toSylowOf, Subgroup.mem_subgroupOf] using this
  · intro hx
    have hy : (h : Perm (Fin I.n))⁻¹ * x * (h : Perm (Fin I.n))⁻¹⁻¹ ∈ gens I.gs := I.syl₁.1 hx
    have hxG : x ∈ gens I.gs := by
      have := (gens I.gs).mul_mem ((gens I.gs).mul_mem h.2 hy) ((gens I.gs).inv_mem h.2)
      simpa [mul_assoc] using this
    have := (key ⟨x, hxG⟩).mpr (by simpa [toSylowOf, Subgroup.mem_subgroupOf] using hx)
    simpa [toSylowOf, Subgroup.mem_subgroupOf] using this

/-! ### Design Lemma witnesses -/

/-- **Totality of `DesignWitnessTask`.** List each finite set of witnesses once: the tuples of
outcome (a), and the pairs `(x, j)` of outcome (b), where `j` ranges over the colors of the
vertex colorings `skel₁ c x` (outcome (b) asks that `j` be such a color). -/
theorem designWitness_total {k : ℕ} (α : ℚ) (I : KColoringInst k) :
    ∃ v, DesignWitnessLists α I.c v := by
  classical
  let A : (ℓ : Fin k) → List (Fin ℓ → Fin I.n) := fun ℓ =>
    (Finset.univ.filter fun x => DesignWitnessA α I.c x).toList
  let S : (ℓ : Fin k) → Finset ℕ := fun ℓ =>
    Finset.univ.image fun p : (Fin ℓ → Fin I.n) × Fin I.n => skel₁ I.c p.1 p.2
  let B : (ℓ : Fin k) → List ((Fin ℓ → Fin I.n) × ℕ) := fun ℓ =>
    ((Finset.univ ×ˢ S ℓ).filter fun p => DesignWitnessB α I.c p.1 p.2).toList
  refine ⟨_, A, B, rfl, fun ℓ => ⟨Finset.nodup_toList _, Finset.nodup_toList _⟩,
    fun ℓ x => by simp [A], fun ℓ x j => ?_⟩
  simp only [B, Finset.mem_toList, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    true_and, and_iff_right_iff_imp]
  intro h
  obtain ⟨-, -, u, -, -, -, hu, -⟩ := h
  exact Finset.mem_image.mpr ⟨(x, u), Finset.mem_univ _, hu⟩


/-! ### Joint `k`-ary refinement -/


section Refinement

variable {n k : ℕ}

/-- The rank of `a` in a finite set `T`: the number of elements of `T` below `a`. It is
injective on `T` and takes values below `|T|`. -/
def rankIn (T : Finset ℕ) (a : ℕ) : ℕ := (T.filter (· < a)).card

theorem rankIn_lt {T : Finset ℕ} {a : ℕ} (ha : a ∈ T) : rankIn T a < T.card :=
  Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨a, ha, lt_irrefl a⟩)

theorem rankIn_injOn {T : Finset ℕ} {a b : ℕ} (ha : a ∈ T) (hb : b ∈ T)
    (h : rankIn T a = rankIn T b) : a = b := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hab | hab
  · have : rankIn T a < rankIn T b := Finset.card_lt_card
      ⟨Finset.monotone_filter_right _ fun x _ hx => lt_trans hx hab,
       fun hs => by simpa using (hs (Finset.mem_filter.mpr ⟨ha, hab⟩))⟩
    omega
  · have : rankIn T b < rankIn T a := Finset.card_lt_card
      ⟨Finset.monotone_filter_right _ fun x _ hx => lt_trans hx hab,
       fun hs => by simpa using (hs (Finset.mem_filter.mpr ⟨hb, hab⟩))⟩
    omega

/-- Renaming the colors injectively keeps a configuration a configuration: the definition uses
only equalities of colors. -/
theorem isConfiguration_comp {g : (Fin k → Fin n) → ℕ} {r : ℕ → ℕ}
    (hr : ∀ x y, r (g x) = r (g y) → g x = g y) (h : IsConfiguration g) :
    IsConfiguration (r ∘ g) :=
  ⟨fun x y e => h.1 x y (hr x y e), fun x y e τ => congrArg r (h.2 x y (hr x y e) τ)⟩

/-- Renaming the colors injectively keeps coherence. A color vector `κ` that is not made of
renamed colors is met by no point; otherwise it is the renaming of one color vector `κ₀`, and
the counts are those of `κ₀`. -/
theorem isCoherent_comp {g : (Fin k → Fin n) → ℕ} {T : Finset ℕ} (hT : ∀ x, g x ∈ T)
    (h : IsCoherent g) : IsCoherent (rankIn T ∘ g) := by
  classical
  intro x y e κ
  have e' : g x = g y := rankIn_injOn (hT x) (hT y) e
  by_cases hκ : ∀ i, ∃ a ∈ T, rankIn T a = κ i
  · choose κ₀ hκ₀ hκr using hκ
    have hiff : ∀ w : Fin k → Fin n, ∀ i, rankIn T (g w) = κ i ↔ g w = κ₀ i := fun w i =>
      ⟨fun hw => rankIn_injOn (hT w) (hκ₀ i) (hw.trans (hκr i).symm),
       fun hw => hw ▸ hκr i⟩
    simp only [Function.comp, hiff]
    exact h x y e' κ₀
  · push Not at hκ
    obtain ⟨i, hi⟩ := hκ
    have hempty : ∀ w : Fin k → Fin n,
        (Finset.univ.filter fun z : Fin n => ∀ i, (rankIn T ∘ g) (Function.update w i z) = κ i) =
          ∅ := fun w => by
      rw [Finset.filter_eq_empty_iff]
      intro z _ hz
      exact hi _ (hT _) (hz i)
    rw [hempty x, hempty y]

/-- An equivariant refinement `F` carries relabelings: if `σ` carries `a` to `b`, then it
carries `F a` to `F b`, since `b` is `a` relabeled by `σ`. -/
theorem carries_of_equivariant {F : ((Fin k → Fin n) → ℕ) → ((Fin k → Fin n) → ℕ)}
    (hF : ∀ c (σ : Perm (Fin n)), F (fun x => c (σ.symm ∘ x)) = fun x => F c (σ.symm ∘ x))
    {σ : Perm (Fin n)} {a b : (Fin k → Fin n) → ℕ} (h : Carries σ a b) :
    Carries σ (F a) (F b) := by
  have hb : b = fun x => a (σ.symm ∘ x) := by
    funext x
    have := h (σ.symm ∘ x)
    rwa [← Function.comp_assoc, Equiv.self_comp_symm, Function.id_comp] at this
  intro x
  rw [hb, hF]
  simp only [← Function.comp_assoc, Equiv.symm_comp_self, Function.id_comp]

/-- **Totality of `KaryRefinementTask`**, given `KaryCoherentRefinement`. Take `F c` and `F c'`
and rename the joint palette `T` (at most `2 n^k` colors) by rank in `T`. All clauses of
`JointRefinement` use only equalities of colors and counts, so they survive the renaming. -/
theorem karyRefinement_total (hK : KaryCoherentRefinement) (I : TwoColoringsInst k) :
    ∃ v : Val, ∃ d d' : (Fin k → Fin I.n) → ℕ,
      v = .list [encKColoring d, encKColoring d'] ∧
      (∀ x, d x < 2 * I.n ^ k) ∧ (∀ x, d' x < 2 * I.n ^ k) ∧ JointRefinement I.c I.c' d d' := by
  classical
  obtain ⟨F, hcoh, hcol, heq⟩ := hK I.n k
  set T : Finset ℕ := Finset.univ.image (F I.c) ∪ Finset.univ.image (F I.c')
  have hT : ∀ x, F I.c x ∈ T := fun x => Finset.mem_union_left _ (by simp)
  have hT' : ∀ x, F I.c' x ∈ T := fun x => Finset.mem_union_right _ (by simp)
  have hcard : T.card ≤ 2 * I.n ^ k := by
    have h1 : T.card ≤ (Finset.univ.image (F I.c)).card + (Finset.univ.image (F I.c')).card :=
      Finset.card_union_le _ _
    have h2 := Finset.card_image_le (s := Finset.univ) (f := F I.c)
    have h3 := Finset.card_image_le (s := Finset.univ) (f := F I.c')
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h2 h3
    omega
  have inj : ∀ {a b : (Fin k → Fin I.n) → ℕ} {x y}, F a x ∈ T → F b y ∈ T →
      rankIn T (F a x) = rankIn T (F b y) → F a x = F b y :=
    fun ha hb h => rankIn_injOn ha hb h
  have hcar : ∀ {σ : Perm (Fin I.n)} {a b : (Fin k → Fin I.n) → ℕ}, Carries σ a b →
      Carries σ (rankIn T ∘ F a) (rankIn T ∘ F b) := fun h x => by
    simp only [Function.comp_apply, carries_of_equivariant heq h x]
  refine ⟨_, rankIn T ∘ F I.c, rankIn T ∘ F I.c', rfl,
    fun x => lt_of_lt_of_le (rankIn_lt (hT x)) hcard,
    fun x => lt_of_lt_of_le (rankIn_lt (hT' x)) hcard,
    isConfiguration_comp (fun x y h => inj (hT x) (hT y) h) (hcoh I.c).1,
    isCoherent_comp hT (hcoh I.c).2,
    isConfiguration_comp (fun x y h => inj (hT' x) (hT' y) h) (hcoh I.c').1,
    isCoherent_comp hT' (hcoh I.c').2,
    fun x y h => hcol _ _ x y (inj (hT x) (hT y) h),
    fun x y h => hcol _ _ x y (inj (hT' x) (hT' y) h),
    fun x y h => hcol _ _ x y (inj (hT x) (hT' y) h),
    fun σ => ⟨hcar, hcar, hcar⟩⟩

end Refinement

/-! ### Cameron recognition -/

/-- `m ≤ binom(m, k)` for `1 ≤ k < m`, by Pascal's rule and induction on `m`. -/
theorem le_choose_of_lt {k : ℕ} (hk : 1 ≤ k) : ∀ {m : ℕ}, k < m → m ≤ m.choose k
  | 0, h => by omega
  | m + 1, h => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Nat.choose_succ_succ']
    rcases Nat.lt_or_ge (k' + 1) m with hlt | hge
    · have := le_choose_of_lt hk hlt
      have := Nat.choose_pos (show k' ≤ m by omega)
      omega
    · obtain rfl : m = k' + 1 := by omega
      rw [Nat.choose_succ_self_right]
      simp

/-- **Output size of `CameronRecognitionTask`.** The identification `e` forces
`n = binom(m, k)^r`. With `n ≥ 25`, `binom(m, k) ≥ 2`, so `1 ≤ k < m`; then
`m ≤ binom(m, k) ≤ n`, and `2^r ≤ binom(m, k)^r = n`. -/
theorem cameron_params_le {n m k r : ℕ} (hn : 25 ≤ n)
    (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})) :
    1 ≤ k ∧ k < m ∧ m ≤ n ∧ 2 ^ r ≤ n := by
  have hc := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_finset_len, Fintype.card_fin,
    Fintype.card_fin] at hc
  -- `hc : n = m.choose k ^ r`
  have hr : r ≠ 0 := by rintro rfl; simp at hc; omega
  have hB : 2 ≤ m.choose k := by
    by_contra hlt
    have : m.choose k ^ r ≤ 1 := by
      interval_cases h : m.choose k <;> simp [hr]
    omega
  have hkm : k < m := by
    by_contra h
    rcases Nat.eq_or_lt_of_le (not_lt.mp h) with h | h
    · subst h; simp at hB
    · rw [Nat.choose_eq_zero_of_lt h] at hB; omega
  have hk : 1 ≤ k := by
    by_contra h
    obtain rfl : k = 0 := by omega
    simp at hB
  have hle : m.choose k ≤ m.choose k ^ r := Nat.le_self_pow hr _
  refine ⟨hk, hkm, ?_, ?_⟩
  · have := le_choose_of_lt hk hkm
    omega
  · rw [hc]; exact Nat.pow_le_pow_left hB r


end GI.CitedChecks
