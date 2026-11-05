module

public import Workspace.Algorithm.Interfaces
public import Workspace.Paper.Caps
public import Workspace.Cited.MarotiPrimitive
public import Workspace.Proved.WielTheorem
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# The cited inputs of the dispatcher and of the aggregation round

This file instantiates as much of the interfaces `Reduction` (`Workspace/Algorithm/Interfaces.lean`)
and `Aggregation` (`Workspace/Algorithm/Aggregation.lean`) as the cited statements allow. The cited statements
enter as hypotheses.

## Which cited results instantiate `Reduction`

The dispatcher (Section 3.3; Algorithm 5, "if enumeration or a product refinement applies";
Section A.5, "Constructive recognition" and "Selection of the quotient and its cap") cites
"the constructive reduction stated in [H, Theorem 3.1 and Section 2.8]". Mathematically this is
the Cameron–Maróti theorem, `GI.Cited.MarotiPrimitive`, applied to the primitive action of the
current group on the blocks of its coarsest primitive quotient. It gives:

* (Maróti (iii)) `|H| < d^{1 + ⌊log₂ d⌋}` for the degree-`d` primitive quotient `H`. Then the
  enumeration reduction applies, with index `≤ exp(3 (log d)²)`
  (`GI.Algorithm.CitedInstances.maroti_order_le_exp`, `maroti_dichotomy`). Its children run under
  the kernel `K` of the block action; their orbits lie in single blocks, which gives the orbit
  fact `d · |v^K| ≤ s` of `DispatchFacts.enumeration`.
* (Maróti (i)) a product action of `Sym(m) wr Sym(r)` on `r`-tuples of `k`-subsets. For `r ≥ 2`
  this is the product refinement: the children run under the subgroup fixing every coordinate,
  the old interval of ratio `d = e^r` (`e = binom(m,k)`) splits into `r` coordinate intervals,
  and `ρ` drops by `r - 1` (`hierRho_split`). For `r = 1` it is the single-factor normalization.

The constructive part ([H, Section 2.8], [BLS]: finding the normal subgroup and the Johnson
coordinates) is an algorithm, stated as `GI.Cited.CameronRecognitionTask`
(`Workspace/Cited/AlgoCameron.lean`).

This file proves:
* `Reduction.ofEnumeration`: a `Reduction` of kind `enumeration d` from a block system,
  a subgroup `K ≤ G` (the block kernel) with the orbit fact, and an index bound; the coset
  representatives are built here (`exists_coset_cover`).
* `Reduction.ofProduct`: a `Reduction` of kind `product r` from the coordinate subgroup,
  an index bound `2^r r!`, and the split of one interval of ratio `e^r` into `r` intervals of
  ratio `e`; the facts `ρ' + (r-1) ≤ ρ` and `Q' ≤ Q` are proved (`hierRho_split`,
  `hierQ_split`), and `r ≤ log₂ s` follows from `e^r ≤ s`.
* `maroti_dichotomy`: the dichotomy of `GI.Cited.MarotiPrimitive`, with the order bound in the
  form `exp(3 (log d)²)` that `DispatchFacts.enumeration` uses.

The orbit fact of the block kernel, the index bound for the coordinate subgroup, the
dispatcher itself and the order bound in the Cameron range are proved in
`Workspace/Algorithm/Dispatch.lean` (`block_kernel_orbit`, `index_coordinate_le`,
`PrimitiveQuotient.dispatch`, `dispatch_cases`) and `Workspace/CameronRange.lean`.

## Which cited results instantiate `Aggregation`

`Aggregation` is the paper's Section 4.1 interface, with Lemma 5.1, Lemmas A.11, A.12,
A.27–A.30 and the certificate tables of Lemma 4.1. The paper cites for it:
* [H, Section 6.2], the aggregation of certificates (Cases 1, 2a, 2b, 3). This is a case
  analysis that the paper re-proves for its constant-size certificates (Section A.3,
  "Aggregation and orbital colors", "The remaining aggregation branches at constant certificate
  size", "Case 1 and balanced colored partitions"). It contains two cited mathematical facts:
  - Case 2b: `d ≤ 7` — `GI.Proved.eightTransitiveContainsAlt`. This file proves the
    form (`exists_transitivity_degree_le_seven`): a transitive group of degree `≥ 8` not
    containing the alternating group has a maximal transitivity degree `1 ≤ d ≤ 7`.
  - Case 3: the Design Lemma ([H, Proposition 5.1]) — `GI.Cited.DesignLemma`, applied to the
    canonical `k`-ary coherent refinement — `GI.Cited.KaryCoherentRefinement` ([H, Sections
    2.3, 2.5]).
* The no-large-twin argument ([H, Section 6.2]) and [H, Exercise 2.15] are proved in the
  library (`GI.Paper.no_large_twin`, `GI.PairRefinement.coherent_clique_half`); the binary
  canonical coherent refinement is proved (`GI.PairRefinement.run_coherent`,
  `run_transports_iff`); [H, Theorem 5.3, Proposition 5.7, Section 5.2, Exercise 5.4] are not
  needed, since Lemma A.28 is proved without them (`GI.Paper.lem_first_soj_rectangle`).

The script of an aggregation round (the local certificates as `Continue` calls, the case
analysis, and the auxiliary rectangle and configuration calls) is not built here; it is paper
content (Section A.3), not a cited result.
-/

namespace GI.Algorithm

namespace CitedInstances

open Equiv Equiv.Perm
open scoped Pointwise

variable {Ω C : Type}

/-! ### Coset representatives -/

/-- For subgroups `K, G` with `G` finite there are `[G : K]` elements `τ_j ∈ G` whose cosets
`τ_j K` cover `G`. -/
theorem exists_coset_cover [Finite Ω] (G K : Subgroup (Perm Ω)) :
    ∃ τ : Fin (K.subgroupOf G).index → Perm Ω, (∀ j, τ j ∈ G) ∧
      (G : Set (Perm Ω)) ⊆ ⋃ j, τ j • (K : Set (Perm Ω)) := by
  classical
  have e : G ⧸ K.subgroupOf G ≃ Fin (K.subgroupOf G).index := by
    rw [Subgroup.index]
    exact Finite.equivFin _
  refine ⟨fun j => ((Quotient.out (e.symm j) : G) : Perm Ω),
    fun j => (Quotient.out (e.symm j) : G).2, ?_⟩
  intro g hg
  refine Set.mem_iUnion.2 ⟨e (QuotientGroup.mk (⟨g, hg⟩ : G)), ?_⟩
  set q : G ⧸ K.subgroupOf G := QuotientGroup.mk (⟨g, hg⟩ : G)
  have hq : (QuotientGroup.mk (Quotient.out q) : G ⧸ K.subgroupOf G) = q := Quotient.out_eq q
  have hmem : (Quotient.out q)⁻¹ * (⟨g, hg⟩ : G) ∈ K.subgroupOf G := by
    rw [← QuotientGroup.eq]
    exact hq
  show g ∈ ((Quotient.out (e.symm (e q)) : G) : Perm Ω) • (K : Set (Perm Ω))
  rw [Equiv.symm_apply_apply]
  refine ⟨(((Quotient.out q)⁻¹ * (⟨g, hg⟩ : G) : G) : Perm Ω), ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.1 hmem
  · simp

/-! ### The order bound of Maróti's case (iii) -/

/-- `d^{1 + ⌊log₂ d⌋} ≤ exp(3 (log d)²)` for `d ≥ 2`. -/
theorem pow_one_add_log_le_exp {d : ℕ} (hd : 2 ≤ d) :
    ((d : ℝ) ^ (1 + Nat.log 2 d) : ℝ) ≤ Real.exp (3 * Real.log d ^ 2) := by
  have hd0 : (0 : ℝ) < d := by positivity
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogd : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) (by exact_mod_cast hd)
  have hL : (Nat.log 2 d : ℝ) * Real.log 2 ≤ Real.log d := by
    have h := Nat.pow_log_le_self 2 (show d ≠ 0 by omega)
    have h' : ((2 : ℝ) ^ Nat.log 2 d) ≤ d := by exact_mod_cast h
    have := Real.log_le_log (by positivity) h'
    rwa [Real.log_pow] at this
  rw [← Real.exp_log (by positivity : (0 : ℝ) < (d : ℝ) ^ (1 + Nat.log 2 d)), Real.log_pow]
  apply Real.exp_le_exp.2
  push_cast
  -- `(1 + L) log d ≤ 3 (log d)²`, from `log 2 ≤ log d` and `L log 2 ≤ log d`.
  have hpos : 0 < Real.log 2 := by linarith
  have h1 : (1 + (Nat.log 2 d : ℝ)) * Real.log 2 ≤ 2 * Real.log d := by nlinarith
  have h2 : (1 + (Nat.log 2 d : ℝ)) * Real.log d * Real.log 2 ≤ 2 * Real.log d ^ 2 := by
    have hld : 0 ≤ Real.log d := by linarith
    nlinarith
  have h3 : 2 * Real.log d ^ 2 ≤ 3 * Real.log d ^ 2 * Real.log 2 := by
    have : 0 ≤ Real.log d ^ 2 := sq_nonneg _
    nlinarith
  have := h2.trans h3
  exact le_of_mul_le_mul_right (by linarith) hpos

/-- **The dichotomy of the dispatcher** ([H, Theorem 3.1], `GI.Cited.MarotiPrimitive`): a
primitive group of degree `d ≥ 25` has order at most `exp(3 (log d)²)` (enumeration applies),
or it has the product structure of Maróti's case (i). -/
theorem maroti_dichotomy (hM : GI.Cited.MarotiPrimitive) {d : ℕ} (hd : 25 ≤ d)
    (G : Subgroup (Perm (Fin d))) (hG : MulAction.IsPreprimitive G (Fin d)) :
    (Nat.card G : ℝ) ≤ Real.exp (3 * Real.log d ^ 2) ∨
    ∃ (m k r : ℕ) (e : Fin d ≃ (Fin r → {A : Finset (Fin m) // A.card = k})),
      (∀ g ∈ G, ∃ (σ : Perm (Fin r)) (h : Fin r → Perm (Fin m)),
        ∀ x : Fin d, e (g x) = fun i => GI.Cited.kSetPerm (h i) (e x (σ i))) ∧
      (∀ h : Fin r → Perm (Fin m), (∀ i, h i ∈ alternatingGroup (Fin m)) →
        (e.trans ((Equiv.piCongrRight fun i => GI.Cited.kSetPerm (h i)).trans e.symm) :
          Perm (Fin d)) ∈ G) := by
  rcases hM d hd G hG with h | h
  · left
    have h' : (Nat.card G : ℝ) ≤ ((d ^ (1 + Nat.log 2 d) : ℕ) : ℝ) := by exact_mod_cast h.le
    push_cast at h'
    exact h'.trans (pow_one_add_log_le_exp (by omega))
  · exact Or.inr h

/-! ### The enumeration reduction -/

/-- **A `Reduction` of kind `enumeration d`** (Section 7.2, row "Primitive enumeration"):
the children run under `K ≤ G` on the `[G : K]` cosets; the hypotheses are the facts of
`DispatchFacts.enumeration`, with the index bound in place of the coset count. -/
noncomputable def Reduction.ofEnumeration [Finite Ω] (P : Params) (S : State Ω C)
    (blocks : Setoid Ω) (blocks_inv : ∀ g ∈ S.G, ∀ v w, blocks.r (g v) (g w) ↔ blocks.r v w)
    (K : Subgroup (Perm Ω)) (hK : K ≤ S.G) (d : ℕ) (hd : 2 ≤ d) (hds : d ≤ S.size)
    (hidx : ((K.subgroupOf S.G).index : ℝ) ≤ Real.exp (P.a * Real.log d ^ 2))
    (horb : ∀ v ∈ S.dom, d * Nat.card (orb K v) ≤ S.size)
    (hier' : List (Interval Ω)) (hrho : State.hierRho hier' ≤ State.hierRho S.hier)
    (hQ : State.hierQ hier' ≤ State.hierQ S.hier) : Reduction P S where
  kind := .enumeration d
  blocks := blocks
  blocks_inv := blocks_inv
  K := K
  K_le := hK
  n := (K.subgroupOf S.G).index
  τ := (exists_coset_cover S.G K).choose
  τ_mem := (exists_coset_cover S.G K).choose_spec.1
  cover := (exists_coset_cover S.G K).choose_spec.2
  hier' := hier'
  Q_le := hQ
  facts := ⟨hd, hds, hidx, hrho, horb⟩

/-- The enumeration reduction with the order bound of Maróti's case (iii): if the block
action `f : G → Sym(d)` has kernel `K` and image of order at most `exp(3 (log d)²)`, and
`P.a ≥ 3`, the index condition of `DispatchFacts.enumeration` holds. -/
theorem index_le_of_image_card {G K : Subgroup (Perm Ω)} {d : ℕ}
    {Q : Type} [Group Q] (f : G →* Q) (hker : f.ker = K.subgroupOf G)
    (hcard : (Nat.card f.range : ℝ) ≤ Real.exp (3 * Real.log d ^ 2)) {a : ℝ} (ha : 3 ≤ a) :
    ((K.subgroupOf G).index : ℝ) ≤ Real.exp (a * Real.log d ^ 2) := by
  have hidx : (K.subgroupOf G).index = Nat.card f.range := by
    rw [← hker, Subgroup.index_ker]
  rw [hidx]
  refine hcard.trans (Real.exp_le_exp.2 ?_)
  exact mul_le_mul_of_nonneg_right ha (sq_nonneg _)

/-! ### The product refinement -/

/-- `ρ` of a hierarchy is the sum of the tower ranks of its ratios. -/
theorem hierRho_append (l l' : List (Interval Ω)) :
    State.hierRho (l ++ l') = State.hierRho l + State.hierRho l' := by
  simp [State.hierRho, List.map_append, List.sum_append]

theorem hierQ_append (l l' : List (Interval Ω)) :
    State.hierQ (l ++ l') = State.hierQ l + State.hierQ l' := by
  simp [State.hierQ, List.map_append, List.sum_append]

/-- `towerRank (e^r) ≥ r · towerRank e + (r - 1)` for `e ≥ 2`, `r ≥ 1` (eq. `rho`: "Splitting
one ratio into `t` nontrivial factors decreases `ρ` by at least `t - 1`"). -/
theorem towerRank_pow {e : ℕ} (he : 2 ≤ e) : ∀ r : ℕ, 1 ≤ r →
    (r : ℤ) * GI.towerRank e + ((r : ℤ) - 1) ≤ GI.towerRank (e ^ r)
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simp
  | r + 2, _ => by
    have ih := towerRank_pow he (r + 1) (by omega)
    have hpow : 2 ≤ e ^ (r + 1) :=
      le_trans he (Nat.le_self_pow (by omega) e)
    have hsplit := GI.tower_rank_split hpow he
    rw [← pow_succ] at hsplit
    push_cast at ih ⊢
    linarith

/-- The hierarchy after a product refinement: the interval `I` of ratio `e^r` is replaced by
`r` coordinate intervals `js` of ratio `e`. Then `ρ` drops by at least `r - 1`. -/
theorem hierRho_split (pre post js : List (Interval Ω)) (I : Interval Ω) {e r : ℕ}
    (he : 2 ≤ e) (hr : 1 ≤ r) (hI : I.ratio = e ^ r) (hjs : js.length = r)
    (hjr : ∀ J ∈ js, J.ratio = e) :
    State.hierRho (pre ++ js ++ post) + ((r : ℝ) - 1) ≤ State.hierRho (pre ++ I :: post) := by
  rw [hierRho_append, hierRho_append, show pre ++ I :: post = pre ++ [I] ++ post by simp,
    hierRho_append, hierRho_append]
  have hjs' : State.hierRho js = (r : ℝ) * ((GI.towerRank e : ℤ) : ℝ) := by
    unfold State.hierRho
    rw [List.map_congr_left (g := fun _ => ((GI.towerRank e : ℤ) : ℝ))
      (fun J hJ => by rw [hjr J hJ]), List.map_const', List.sum_replicate, hjs, nsmul_eq_mul]
  have hI' : State.hierRho [I] = ((GI.towerRank (e ^ r) : ℤ) : ℝ) := by
    simp [State.hierRho, hI]
  rw [hjs', hI']
  have := towerRank_pow he r hr
  have h' : ((r : ℤ) : ℝ) * ((GI.towerRank e : ℤ) : ℝ) + (((r : ℤ) : ℝ) - 1) ≤
      ((GI.towerRank (e ^ r) : ℤ) : ℝ) := by exact_mod_cast this
  push_cast at h'
  linarith

/-- After a product refinement `Q` does not increase, when every coordinate interval keeps a
cap at most the old cap ("Refining its product coordinates gives each resulting interval cap
`q`, clamped by any already smaller valid cap"; Corollary A.13, "the additivity of `log d`
makes `Q` nonincreasing"). -/
theorem hierQ_split (pre post js : List (Interval Ω)) (I : Interval Ω) {e r : ℕ}
    (hI : I.ratio = e ^ r) (hjs : js.length = r) (hjr : ∀ J ∈ js, J.ratio = e)
    (hjc : ∀ J ∈ js, J.cap ≤ I.cap) :
    State.hierQ (pre ++ js ++ post) ≤ State.hierQ (pre ++ I :: post) := by
  rw [hierQ_append, hierQ_append, show pre ++ I :: post = pre ++ [I] ++ post by simp,
    hierQ_append, hierQ_append]
  have hle : State.hierQ js ≤ State.hierQ [I] := by
    have hI' : State.hierQ [I] = (r : ℝ) * (Real.log e * Real.log (max I.cap 2 : ℕ)) := by
      simp only [State.hierQ, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, hI]
      push_cast
      rw [Real.log_pow]
      ring
    rw [hI']
    unfold State.hierQ
    have hbound : ∀ x ∈ js.map (fun J => Real.log J.ratio * Real.log (max J.cap 2 : ℕ)),
        x ≤ Real.log e * Real.log (max I.cap 2 : ℕ) := by
      intro x hx
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hx
      rw [hjr J hJ]
      apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg _)
      apply Real.log_le_log (by positivity)
      exact_mod_cast max_le_max (hjc J hJ) le_rfl
    have := List.sum_le_card_nsmul _ _ hbound
    rw [List.length_map, hjs, nsmul_eq_mul] at this
    exact this
  linarith

/-- **A `Reduction` of kind `product r`** (Section 7.2, row "Product refinement"): the
children run under the coordinate subgroup `K ≤ G` on its cosets, and the hierarchy splits the
interval `I` of ratio `e^r` of a hierarchy `pre ++ I :: post` into `r` coordinate intervals of
ratio `e`. The hierarchy `pre ++ I :: post` is the stored one, or a refinement of it with no
larger `ρ` and `Q` (the exposed quotient, Algorithm 5: "Expose the next primitive quotient"). The facts of
`DispatchFacts.product` are proved from the split; `r ≤ log₂ s` follows from `e^r ≤ s`. The
index bound `[G : K] ≤ 2^r r!` is a hypothesis (from Maróti's case (i)). -/
noncomputable def Reduction.ofProduct [Finite Ω] (P : Params) (S : State Ω C)
    (blocks : Setoid Ω) (blocks_inv : ∀ g ∈ S.G, ∀ v w, blocks.r (g v) (g w) ↔ blocks.r v w)
    (K : Subgroup (Perm Ω)) (hK : K ≤ S.G) {e r : ℕ} (he : 2 ≤ e) (hr : 2 ≤ r)
    (hidx : (K.subgroupOf S.G).index ≤ 2 ^ r * r.factorial) (hds : e ^ r ≤ S.size)
    (pre post js : List (Interval Ω)) (I : Interval Ω)
    (hρ : State.hierRho (pre ++ I :: post) ≤ State.hierRho S.hier)
    (hQ : State.hierQ (pre ++ I :: post) ≤ State.hierQ S.hier) (hI : I.ratio = e ^ r) (hjs : js.length = r) (hjr : ∀ J ∈ js, J.ratio = e)
    (hjc : ∀ J ∈ js, J.cap ≤ I.cap) : Reduction P S where
  kind := .product r
  blocks := blocks
  blocks_inv := blocks_inv
  K := K
  K_le := hK
  n := (K.subgroupOf S.G).index
  τ := (exists_coset_cover S.G K).choose
  τ_mem := (exists_coset_cover S.G K).choose_spec.1
  cover := (exists_coset_cover S.G K).choose_spec.2
  hier' := pre ++ js ++ post
  Q_le := (hierQ_split pre post js I hI hjs hjr hjc).trans hQ
  facts := by
    refine ⟨hr, ?_, hidx, ?_⟩
    · -- `2^r ≤ e^r ≤ s`, so `r ≤ log₂ s`.
      have h2 : 2 ^ r ≤ S.size := le_trans (Nat.pow_le_pow_left he r) hds
      have h2' : ((2 : ℝ) ^ (r : ℝ)) ≤ S.size := by
        rw [Real.rpow_natCast]; exact_mod_cast h2
      have hs : (0 : ℝ) < S.size := by
        have : 0 < 2 ^ r := by positivity
        exact_mod_cast lt_of_lt_of_le this h2
      rw [Real.le_logb_iff_rpow_le (by norm_num) hs]
      exact h2'
    · exact (hierRho_split pre post js I he (by omega) hI hjs hjr).trans hρ

/-! ### Case 2b of the aggregation: the transitivity degree is at most seven -/

/-- `G ≤ Sym(n)` is `d`-transitive: transitive on injective `d`-tuples. -/
def MultTransitive {n : ℕ} (G : Subgroup (Perm (Fin n))) (d : ℕ) : Prop :=
  ∀ a b : Fin d ↪ Fin n, ∃ g ∈ G, ∀ i, g (a i) = b i

/-- **`d ≤ 7`** (paper, Section A.3, "Aggregation and orbital colors": "let `d ≤ 7` be its maximal
degree of transitivity"). For a transitive `G ≤ Sym(n)`, `n ≥ 8`, that does not contain `Alt(n)`,
there is a `d` with `1 ≤ d ≤ 7` such that `G` is `d`-transitive but not `(d+1)`-transitive. -/
theorem exists_transitivity_degree_le_seven {n : ℕ}
    (hn : 8 ≤ n) (G : Subgroup (Perm (Fin n))) (h1 : MultTransitive G 1)
    (hAlt : ¬ alternatingGroup (Fin n) ≤ G) :
    ∃ d, 1 ≤ d ∧ d ≤ 7 ∧ MultTransitive G d ∧ ¬ MultTransitive G (d + 1) := by
  classical
  -- the largest `d ≤ 7` with `G` `d`-transitive
  have hex : ∃ d, d ≤ 6 ∧ MultTransitive G (7 - d) := by
    by_contra hno
    push Not at hno
    -- then not 1-transitive: `7 - 6 = 1`
    exact hno 6 le_rfl h1
  let d₀ := Nat.find hex
  have hd₀ : d₀ ≤ 6 ∧ MultTransitive G (7 - d₀) := Nat.find_spec hex
  refine ⟨7 - d₀, by omega, by omega, hd₀.2, ?_⟩
  intro hnext
  by_cases hz : d₀ = 0
  · -- `G` would be 8-transitive
    apply hAlt
    apply GI.Proved.eightTransitiveContainsAlt n hn G
    have : 7 - d₀ + 1 = 8 := by omega
    rw [this] at hnext
    exact hnext
  · have hmin := Nat.find_min hex (show d₀ - 1 < d₀ by omega)
    apply hmin
    refine ⟨by omega, ?_⟩
    have : 7 - (d₀ - 1) = 7 - d₀ + 1 := by omega
    rw [this]
    exact hnext

end CitedInstances

end GI.Algorithm
