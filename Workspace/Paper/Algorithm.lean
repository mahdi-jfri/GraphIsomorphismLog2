module

public import Workspace.Algorithm.Correctness
public import Workspace.Algorithm.Certificates
public import Workspace.Algorithm.Cases
public import Workspace.Algorithm.Tree
public import Workspace.Paper.LocalCertificates
public import Workspace.GraphReduction
public import Workspace.GraphOutput
public import Workspace.Statement.Main

@[expose] public section

/-!
# Paper statements: the algorithm of Sections 3 and 6

* Lemma 6.1 (`lem:main-correctness`): `GI.Paper.lem_main_correctness`.
* Algorithm 1 (`alg:graph-wrapper`) and the reduction of Theorem 1.1 to string
  isomorphism on ordered vertex pairs (Section 1.1, "For a graph, the positions are
  ordered vertex pairs, the colors record adjacency, and the allowed permutations
  apply the same vertex permutation to both coordinates"; Section 3: "Thus the
  reduction preserves exactly the graph isomorphisms"):
  `GI.Paper.alg_graph_wrapper`, `GI.Paper.graph_reduction_answer`,
  `GI.Paper.graph_reduction_automorphisms`.
* Section 3.2, the orbit chain rule and the coset rule:
  `GI.Paper.sec_model_orbit_chain_rule`, `GI.Paper.sec_model_coset_rule`; Section 3,
  faithful images and joint compression: `GI.Paper.sec_model_faithful_image`,
  `GI.Paper.sec_model_joint_compression`.
* Section 4, `CheckNewWindow` and the lockstep updates compute the endpoint stages and
  the comparison cosets: `GI.Paper.alg_local_certificate_by_calls`,
  `GI.Paper.lockstep_update_by_call`.
* Section 6.2, "Why the cases cover every large action":
  `GI.Paper.cases_support_classification`, `GI.Paper.cases_natural_level`,
  `GI.Paper.cases_row_size`, `GI.Paper.cases_column_giant_natural`,
  `GI.Paper.cases_giant_step`.

The procedure itself is `GI.Algorithm.Run` (`Workspace/Algorithm/Procedure.lean`),
with the state of Section 6.1 in `Workspace/Algorithm/State.lean` and the
interfaces in `Workspace/Algorithm/Interfaces.lean`.

## Deferred to stage 2

The polynomial bounds on structural work, the generator representation of
answers, and the running time of `GraphIso` (Theorem 1.1 itself).
-/

namespace GI.Paper

open Equiv Equiv.Perm GI.Algorithm
open scoped Pointwise

/-! ### Lemma 6.1 -/

/-- **Lemma 6.1** (`lem:main-correctness`, Exact recursive output). "Assuming exact
answers to the recursive calls, every invocation of `Continue` returns exactly the
allowed relabelings taking its first coloring to its second."

A run `r` of `Continue` on a state `S` is a finite tree of recursive runs; the
recursive calls are its subtrees. By induction over the tree (the induction
hypothesis is "exact answers to the recursive calls"; one step per case is
`GI.Algorithm.step_orbitChain`, `step_cosets`, `step_aggregate`, …), the returned
set `A` is the set of `g ∈ G` with `y (g v) = x v` for every `v` of the active
domain. Consequently `A` is empty or a full coset `t · Aut_G(x on dom)` with `t ∈ G`:
the complete isomorphism coset. The interfaces of the subroutines that are not yet
proved (`GI.Algorithm.RowTerminal`, `GI.Algorithm.Aggregation`) enter as data of
the run. -/
theorem lem_main_correctness {P : Params} {Ω C : Type} {S : State Ω C} {A : Set (Perm Ω)}
    (r : Run P .cont S none A) :
    A = {g | g ∈ S.G ∧ ∀ v ∈ S.dom, S.y (g v) = S.x v} ∧
    (A = ∅ ∨ ∃ t ∈ S.G, A = t • (autGroup S.G S.dom S.dom_inv S.x : Set (Perm Ω))) := by
  have h := r.exact
  refine ⟨h, ?_⟩
  rw [h]
  exact answer_empty_or_coset S.dom_inv S.x S.y

/-- Lemma 6.1 holds for `Solve` and `GiantStep` as well: every run of any of the three
procedures returns the exact answer of its state. -/
theorem lem_main_correctness_all {P : Params} {m : Mode} {Ω C : Type} {S : State Ω C}
    {L : Option (SuppliedLabels S)}
    {A : Set (Perm Ω)} (r : Run P m S L A) : A = S.answer :=
  r.exact

/-! ### Algorithm 1: from graphs to colored positions -/

section Graph

variable {V : Type} [DecidableEq V]

/-- The action of vertex permutations on ordered pairs: `p ↦ ((u, v) ↦ (p u, p v))`
(Algorithm 1: "Let `G` be the action of all vertex permutations on `Ω`"). -/
def diagonalHom (V : Type) : Perm V →* Perm (V × V) where
  toFun := GI.diagonal
  map_one' := by ext ⟨u, v⟩ <;> rfl
  map_mul' p q := by ext ⟨u, v⟩ <;> rfl

omit [DecidableEq V] in
theorem diagonalHom_apply (p : Perm V) (u v : V) : diagonalHom V p (u, v) = (p u, p v) := rfl

omit [DecidableEq V] in
theorem diagonalHom_injective : Function.Injective (diagonalHom V) :=
  GI.diagonal_injective

/-- The color of an ordered pair: its diagonal status and its adjacency (Algorithm 1:
"Let `x, y` color each pair by its diagonal status and adjacency in `X, Y`"). -/
def pairColor (X : SimpleGraph V) [DecidableRel X.Adj] : V × V → Bool × Bool :=
  fun uv => (decide (uv.1 = uv.2), decide (X.Adj uv.1 uv.2))

/-- The initial state of Algorithm 1: positions `Ω = V²`, the diagonal action of all
vertex permutations, the two pair colorings, an empty hierarchy, `h = 2` and phase
size `|Ω|`. -/
def graphState [Fintype V] (X Y : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel Y.Adj] :
    State (V × V) (Bool × Bool) where
  G := (diagonalHom V).range
  dom := Set.univ
  dom_inv := fun _ _ _ => Iff.rfl
  x := pairColor X
  y := pairColor Y
  hier := []
  rows := none
  floor := false
  h := 2
  h_le := le_rfl
  N := Fintype.card (V × V)
  counter := CounterInv.reset _ _ _ _
  carrier := CarrierOK.none _ _ _

/-- **The reduction is exact.** The relabelings of the pair positions that take the
colors of `X` to those of `Y` are exactly the diagonal images of the graph
isomorphisms `p` (`X.Adj u v ↔ Y.Adj (p u) (p v)`). -/
theorem graph_reduction_answer [Fintype V] (X Y : SimpleGraph V) [DecidableRel X.Adj]
    [DecidableRel Y.Adj] :
    (graphState X Y).answer =
      diagonalHom V '' {p | ∀ u v, X.Adj u v ↔ Y.Adj (p u) (p v)} := by
  ext g
  simp only [State.answer, GI.Algorithm.answer, graphState, Set.mem_setOf_eq, Set.mem_univ,
    true_implies, Set.mem_image]
  constructor
  · rintro ⟨⟨p, rfl⟩, hp⟩
    refine ⟨p, fun u v => ?_, rfl⟩
    have h := congrArg Prod.snd (hp (u, v))
    dsimp only [pairColor, diagonalHom_apply] at h
    exact decide_eq_decide.mp h.symm
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p, rfl⟩, fun ⟨u, v⟩ => ?_⟩
    simp only [pairColor, diagonalHom_apply, Prod.mk.injEq]
    exact ⟨decide_eq_decide.mpr p.injective.eq_iff, decide_eq_decide.mpr (hp u v).symm⟩

/-- **Algorithm 1** (`alg:graph-wrapper`, `GraphIso`), correctness. Let `A` be the
output of a run of `Solve` on the pair state of `X` and `Y`. The vertex permutations
induced by `A` ("return the vertex permutations induced by the full answer") are
exactly the graph isomorphisms from `X` to `Y`. In particular the output is empty
exactly when the graphs are not isomorphic, and for `Y = X` the induced
permutations form the automorphism group of `X`. -/
theorem alg_graph_wrapper [Fintype V] {P : Params} (X Y : SimpleGraph V) [DecidableRel X.Adj]
    [DecidableRel Y.Adj] {A : Set (Perm (V × V))} (r : Run P .solve (graphState X Y) none A) :
    diagonalHom V ⁻¹' A = {p | ∀ u v, X.Adj u v ↔ Y.Adj (p u) (p v)} ∧
    (A = ∅ ↔ IsEmpty (X ≃g Y)) := by
  have hA : A = diagonalHom V '' {p | ∀ u v, X.Adj u v ↔ Y.Adj (p u) (p v)} :=
    r.exact.trans (graph_reduction_answer X Y)
  refine ⟨?_, ?_⟩
  · rw [hA, Set.preimage_image_eq _ diagonalHom_injective]
  · rw [hA, Set.image_eq_empty]
    constructor
    · intro h
      refine ⟨fun e => ?_⟩
      have : (e.toEquiv : Perm V) ∈ ({p | ∀ u v, X.Adj u v ↔ Y.Adj (p u) (p v)} :
          Set (Perm V)) := fun u v => e.map_rel_iff.symm
      rw [h] at this
      exact this
    · intro h
      apply Set.eq_empty_of_forall_notMem
      intro p hp
      exact h.false ⟨p, fun {u v} => (hp u v).symm⟩

/-- For `Y = X`, the induced vertex permutations of the output of Algorithm 1 form the
automorphism group of `X` in the sense of the trusted statement
(`GI.Statement.autGroup`): "returns … generators for the full automorphism group of
the first graph". -/
theorem graph_reduction_automorphisms {n : ℕ} {P : Params} (X : SimpleGraph (Fin n))
    [DecidableRel X.Adj] {A : Set (Perm (Fin n × Fin n))}
    (r : Run P .solve (graphState X X) none A) :
    diagonalHom (Fin n) ⁻¹' A = (GI.Statement.autGroup X : Set (Perm (Fin n))) := by
  rw [(alg_graph_wrapper X X r).1]
  ext p
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, GI.Statement.autGroup, Subgroup.mem_mk,
    Submonoid.mem_mk, Subsemigroup.mem_mk]
  exact forall₂_congr fun u v => iff_comm

end Graph

/-! ### Section 3.2: the orbit chain rule and the coset rule -/

section Model

variable {Ω C : Type}

/-- **The orbit chain rule** (Section 3.2): "If the answer on the first orbit is `Hπ`,
absorb `π` into the target coloring and continue under `H`." For a `G`-invariant
`D₁ ⊆ D`: if the first orbit has no isomorphism, neither does `D`; and if `t` is one
isomorphism on `D₁`, the answer on `D` is `t` times the answer on `D \ D₁` under
`H = Aut_G(x on D₁)` for the colorings `(x, y ∘ t)`. -/
theorem sec_model_orbit_chain_rule {G : Subgroup (Perm Ω)} {D D₁ : Set Ω}
    (hD₁ : GI.Algorithm.Invariant G D₁) (hsub : D₁ ⊆ D) (x y : Ω → C) :
    (answer G D₁ x y = ∅ → answer G D x y = ∅) ∧
    ∀ t ∈ answer G D₁ x y,
      answer G D x y = t • answer (autGroup G D₁ hD₁ x) (D \ D₁) x (y ∘ t) :=
  ⟨answer_orbit_chain_empty hsub, fun _ ht => answer_orbit_chain hD₁ hsub ht⟩

/-- **The coset rule** (Section 3.2): for an exhaustive family of successful answers
`t_i H_i` with union the exact answer, the automorphism group is generated by the
`H_i` and the ratios `t₀⁻¹ t_i` of the successful representatives. -/
theorem sec_model_coset_rule {ι : Type} {G : Subgroup (Perm Ω)} {D : Set Ω}
    (hD : GI.Algorithm.Invariant G D) {x y : Ω → C} (t : ι → Perm Ω)
    (H : ι → Subgroup (Perm Ω))
    (hunion : (⋃ i, t i • (H i : Set (Perm Ω))) = answer G D x y) (i₀ : ι) :
    autGroup G D hD x =
      Subgroup.closure ((⋃ i, (H i : Set (Perm Ω))) ∪ Set.range fun i => (t i₀)⁻¹ * t i) :=
  combine_generators hD t H hunion i₀

/-- **Faithful images** (Section 3: "Every fresh call uses the faithful permutation
image on its own active domain"): the answer on `D` is the preimage of the answer of
the image group `G|_D` under the restriction map. -/
theorem sec_model_faithful_image (G : Subgroup (Perm Ω)) (D : Set Ω)
    (hD : GI.Algorithm.Invariant G D) (x y : Ω → C) :
    answer G D x y = {g | ∃ hg : g ∈ G, restrictHom G D hD ⟨g, hg⟩ ∈
      answer (restrictHom G D hD).range Set.univ (x ∘ Subtype.val) (y ∘ Subtype.val)} :=
  answer_restrict_image G D hD x y

/-- **Joint compression** (Section 3: "compress the two input colorings jointly: equal
color records receive the same integer name, distinct records receive distinct
names"): one renaming, injective on the colors used, does not change the answer. -/
theorem sec_model_joint_compression {C' : Type} (G : Subgroup (Perm Ω)) (D : Set Ω)
    (x y : Ω → C) (c : C → C') (hc : Set.InjOn c (Set.range x ∪ Set.range y)) :
    answer G D (c ∘ x) (c ∘ y) = answer G D x y :=
  answer_recolor G D x y c hc

end Model

/-! ### Section 4: the local certificates by inherited calls -/

section Certificates

open GI.Endpoint GI.LocalGroups GI.LocalCertificates

variable {Ω Γ C : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]

/-- **Algorithm 2 with `CheckNewWindow`** (Section 4: "The operation `CheckNewWindow`
returns the full subgroup of `A` preserving `x` on `V`. It enumerates the constantly
many cosets of `ker(φ_T|_A)` in `A` and uses `Continue` on the kernel orbits in `V`").
When those `Continue` calls are exact, round `t` of the loop holds the stage
`(A_t, W_t)` of `GI.Paper.alg_local_certificate`. -/
theorem alg_local_certificate_by_calls (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    (S₀ : State Ω C) (x : Ω → C) (T : Finset Γ) (t : ℕ) :
    (endpointScript (phiT G π T) S₀ x t).evalExact = alg_local_certificate G π x T t :=
  endpointScript_evalExact _ S₀ x t

/-- **The lockstep update** (Section 4: "run two copies in lockstep under the full
ordered-tuple transporter, maintaining the complete comparison coset after each new
window. Each update uses the same inherited kernel-orbit queries."). From a member
`g₀` of the stage-`j` comparison coset, one `Continue` call under `N_j` on the new
window gives the stage-`(j+1)` comparison coset, when it is exact. -/
theorem lockstep_update_by_call (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)
    (S₀ : State Ω C) {k : ℕ} (j : ℕ) (x y : Ω → C) (t t' : Fin k → Γ) {g₀ : Perm Ω}
    (hg₀ : g₀ ∈ lockstep G π j x t y t') :
    (lockstepStep G π S₀ j x y t g₀).evalExact = lockstep G π (j + 1) x t y t' :=
  lockstepStep_evalExact G π S₀ j x y t t' hg₀

end Certificates

/-! ### Section 6.2: why the cases cover every large action -/

/-- **Section 6.2**, first paragraph: "For `q > λ` and sufficiently large `N`, we have
`C(q,3) > N`. Also `q` exceeds the logarithmic transitive-kernel threshold. The
support classification therefore gives precisely the one-label and two-label
cases." -/
theorem cases_support_classification {α : ℝ}
    (hα : 1 / 3 < α) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ∀ {Ω Γ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
        (G : Subgroup (Equiv.Perm Ω)) [MulAction.IsPretransitive G Ω]
        (φ : G →* alternatingGroup Γ), Function.Surjective φ →
        Fintype.card Ω ≤ N → (N : ℝ) ^ α < Fintype.card Γ →
        (Nonempty (GI.StabilizerQuotient.KernelQuotient φ Ω Γ) ∨
          Nonempty (GI.StabilizerQuotient.KernelQuotient φ Ω (GI.Pairs.OrderedPair Γ)) ∨
          Nonempty (GI.StabilizerQuotient.KernelQuotient φ Ω (GI.Johnson.SubsetVertex Γ 2))) :=
  large_giant_support_cases hα

/-- **Section 6.2**, second paragraph: "a selected Johnson constituent has
`C(q,a) ≥ q` physical blocks … there are exactly `q` physical blocks and `a = 1`." -/
theorem cases_natural_level {q a : ℕ} (hq : 4 ≤ q) (ha : 1 ≤ a) (haq : 2 * a ≤ q)
    (hc : q.choose a = q) : a = 1 :=
  johnson_level_eq_one hq ha haq hc

/-- **Section 6.2**, third paragraph: "The row size is at most `N^{1-α}`. Since
`1-α < 2α < γ`, the row terminal makes only fresh calls below the phase
threshold." -/
theorem cases_row_size {α γ : ℝ} (hα : 1 / 3 < α) (hγ : 2 * α < γ) {N q f : ℕ} (hN : 0 < N)
    (hs : f * q ≤ N) (hq : (N : ℝ) ^ α < q) :
    (f : ℝ) < (N : ℝ) ^ (1 - α) ∧ 1 - α < 2 * α ∧ 2 * α < γ :=
  ⟨row_size_lt hN hs hq, exponent_order hα hγ⟩

/-- **Section 6.2**, third paragraph: "Any later column giant of degree `q > λ` must be
natural, since even its unordered-pair action would require `C(q,2) > N^{1-α}`
columns." -/
theorem cases_column_giant_natural {α : ℝ} (hα : 1 / 3 < α) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ q : ℕ, (N : ℝ) ^ α < q →
      (N : ℝ) ^ (1 - α) < (q.choose 2 : ℕ) :=
  column_giant_natural hα

/-- **The giant-step dispatch is exhaustive** (Algorithm 5 with Sections 5.2, 5.3 and
6.2). A large action (`q > λ`) that `GiantStep` does not send to `RowStep` has a
non-natural (two-label) kernel-orbit map, or a retained row action of degree
`m ≥ q`: the pair rectangle of Section 5.2 or the diagonal rectangle of Section 5.3
applies. -/
theorem cases_giant_step {α : ℝ} {Ω C : Type} (S : State Ω C) (L : GiantLabels S)
    (hq : (S.N : ℝ) ^ α < L.q) (hnot : ¬ RowCase α S L) :
    (¬ ∃ label, NaturalRows S L label) ∨ ∃ R, S.rows = some R ∧ L.q ≤ R.m :=
  giantStep_cases S L hq hnot

end GI.Paper
