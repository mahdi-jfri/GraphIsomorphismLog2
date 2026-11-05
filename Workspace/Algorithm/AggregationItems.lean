module

public import Workspace.Algorithm.AuxItems

@[expose] public section

/-!
# The items of an aggregation round from the proved lemmas

`Workspace/Algorithm/Aggregation.lean` defines the items of an aggregation round and the
facts each one must satisfy (`AuxItem.Valid`). This file derives these facts from the
proved lemmas of the paper.

* Overcoset items (Case 1, Design outcome (a), the balanced outcomes of Lemma 5.1): the cap
  `aw(E₀) ≤ βq` gives `Valid` (`AuxItem.valid_overcoset`).
* Configuration items (Lemma A.12): every group inside the configuration group has
  `aw ≤ βq` (`GI.Paper.lem_exact_configuration`), so the cap of a configuration item holds
  (`AuxItem.config_cap`).
* The halving branch of Case 2a (Lemma A.11): the parity twist and the split
  `H = H₀ ∪ t H₀` (`Halving.twist_facts`, from
  `GI.Paper.lem_large_symmetry_constant_cert_twist`, and `Halving.no_twist_facts`, from
  `GI.Paper.lem_large_symmetry_constant_cert_no_twist`), and the fact that `A` meets every
  coset of the kernel (`Halving.onto_of_agree`), and the small kernel orbits `orb_small`
  from the Johnson blocks (`Halving.orb_small_of_blocks`, from
  `GI.Paper.lem_large_symmetry_constant_cert_half`).
* Items from equivariant invariants of the canonical structures of a branch
  (`AuxItem.valid_none_of_invariant`, `AuxItem.valid_overcoset_of_invariant`,
  `AuxItem.valid_query_of_invariant`): the isomorphisms of a branch map `F X` to `F Y` for
  every invariant `F` that commutes with relabeling, so they lie in one coset of its stabilizer.
* Configuration query items (Lemma A.12: cap and coset statement, `AuxItem.valid_query_config`)
  and rectangle query items (Lemma 5.1 / `alg_auxiliary_rectangle_branch`: the left transporters
  form a coset of `leftGroup M`, `AuxItem.valid_query_rectangle`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm GI.Rectangle GI.Paper GI.ExactConfiguration GI.PairRefinement
open scoped Pointwise

variable {Ω C : Type} {P : Params} {S : State Ω C} {L : GiantLabels S}

namespace AuxItem

/-- The cap of an overcoset group from `aw(E₀) ≤ βq`. -/
theorem cap_of_aw {E₀ : Subgroup (alternatingGroup (Fin L.q))}
    (h : (aw E₀ : ℝ) ≤ P.β * L.q) : GI.SectionCaps.Cap E₀ ⌊P.β * L.q⌋₊ :=
  (aw_le_iff _).1 (Nat.le_floor h)

/-- **An overcoset item is valid** when its group has `aw(E₀) ≤ βq` (Section A.3, "Case 1 and
balanced colored partitions"; Lemma 5.1) and the label image of every parent isomorphism of the
branch `B` lies in `σ E₀`. -/
theorem valid_overcoset {B : Set (Perm Ω)} (σ : alternatingGroup (Fin L.q))
    {E₀ : Subgroup (alternatingGroup (Fin L.q))} (h : (aw E₀ : ℝ) ≤ P.β * L.q)
    (hB : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G, σ⁻¹ * L.π ⟨g, hg⟩ ∈ E₀) :
    (overcoset σ E₀ : AuxItem P S L).Valid B :=
  ⟨cap_of_aw h, hB⟩

/-- **The cap of a configuration item** (Lemma A.12, `GI.Paper.lem_exact_configuration`):
there is `q₀` such that, for a nontrivial homogeneous coherent configuration on at least
`δq` of the `q ≥ q₀` labels, every group `E₀` whose permutations preserve the
configuration has `aw(E₀) ≤ βq`. -/
theorem config_cap {δ : ℝ} (hβ : max (1 - δ) (1 / 2) < P.β) :
    ∃ q₀ : ℕ, ∀ {Ω C : Type} {S : State Ω C} (L : GiantLabels S) (n : ℕ) (c : Coloring n)
      (side : Bool) (ι : Fin n ↪ Fin L.q), Coherent c → Homogeneous c side →
      NontrivialOffDiagonal c side → δ * L.q ≤ n → q₀ ≤ L.q →
      ∀ E₀ : Subgroup (alternatingGroup (Fin L.q)),
        E₀.map (alternatingGroup (Fin L.q)).subtype ≤ configGroup ι c side →
        GI.SectionCaps.Cap E₀ ⌊P.β * L.q⌋₊ := by
  obtain ⟨q₀, hq₀⟩ := lem_exact_configuration hβ
  refine ⟨q₀, fun L n c side ι hc hh hn hδ hq E₀ hE => ?_⟩
  have hδ' : δ * Fintype.card (Fin L.q) ≤ n := by simpa using hδ
  have hq' : q₀ ≤ Fintype.card (Fin L.q) := by simpa using hq
  have h := (hq₀ (Fin L.q) n c side ι hc hh hn hδ' hq').2.2 _ hE
  rw [Fintype.card_fin] at h
  have hK : GI.SectionCaps.Cap (E₀.map (alternatingGroup (Fin L.q)).subtype)
      ⌊P.β * L.q⌋₊ := (aw_le_iff _).1 (Nat.le_floor h)
  let e := E₀.equivMapOfInjective (alternatingGroup (Fin L.q)).subtype
    (alternatingGroup (Fin L.q)).subtype_injective
  exact GI.SectionCaps.of_injective e.toMonoidHom e.injective hK


/-! ### Items from equivariant invariants of the canonical structures

The branch of a target tuple `b` is responsible for the parent isomorphisms `g` with
`π(g) X = Y`, where `X, Y` are the two canonical structures of the branch (`isoSetOf`). Every
item the paper builds from `X` and `Y` (a canonical colored partition in Case 1, a canonical
object of the Design Lemma, a canonical configuration) is an *equivariant invariant* `F` of the
structure. The isomorphisms of the branch then map `F X` to `F Y`, so they lie in a coset of
the stabilizer of `F X`. The three adapters below turn this into the facts `AuxItem.Valid`. -/

section Invariant

variable {q κ ℓ : ℕ} {Z : Type*} [MulAction (Perm (Fin q)) Z]

/-- An invariant of the canonical structures that commutes with relabeling. -/
def Equivariant (F : Canon q κ ℓ → Z) : Prop :=
  ∀ (σ : Perm (Fin q)) X, F (σ • X) = σ • F X

end Invariant

section Branch

variable {Z : Type*} [MulAction (Perm (Fin L.q)) Z] {ℓ : ℕ}
  {X Y : Canon L.q P.κ ℓ} {B : Set (Perm Ω)}

/-- A branch whose isomorphisms all map `X` to `Y` maps `F X` to `F Y`. -/
theorem invariant_of_branch {F : Canon L.q P.κ ℓ → Z} (hF : Equivariant F)
    (hB : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G, (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • X = Y) :
    ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G, (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • F X = F Y := by
  intro g hg
  obtain ⟨hgG, h⟩ := hB g hg
  exact ⟨hgG, by rw [← hF, h]⟩

/-- **An inconsistent branch is empty** ("**skip** this choice if side sizes differ"): if no
even label permutation maps `F X` to `F Y`, the branch has no parent isomorphism. -/
theorem valid_none_of_invariant {F : Canon L.q P.κ ℓ → Z} (hF : Equivariant F)
    (hB : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G, (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • X = Y)
    (hne : ∀ σ : alternatingGroup (Fin L.q), (σ : Perm (Fin L.q)) • F X ≠ F Y) :
    (none : AuxItem P S L).Valid B := by
  show S.answer ∩ B = ∅
  refine Set.eq_empty_iff_forall_notMem.2 fun g hg => ?_
  obtain ⟨hgG, h⟩ := invariant_of_branch hF hB g hg
  exact hne _ h

/-- **An overcoset of the stabilizer of an invariant** (Case 1: the stabilizer of a canonical
balanced colored partition; Design Lemma, outcome (a): the stabilizer of a canonical object).
If `σ` maps `F X` to `F Y`, every isomorphism of the branch lies in `σ E₀` as soon as `E₀`
contains the even stabilizer of `F X`. -/
theorem valid_overcoset_of_invariant {F : Canon L.q P.κ ℓ → Z} (hF : Equivariant F)
    (hB : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G, (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • X = Y)
    (σ : alternatingGroup (Fin L.q)) (hσ : (σ : Perm (Fin L.q)) • F X = F Y)
    {E₀ : Subgroup (alternatingGroup (Fin L.q))} (hcap : (aw E₀ : ℝ) ≤ P.β * L.q)
    (hstab : ∀ e : alternatingGroup (Fin L.q), (e : Perm (Fin L.q)) • F X = F X → e ∈ E₀) :
    (overcoset σ E₀ : AuxItem P S L).Valid B := by
  refine valid_overcoset σ hcap fun g hg => ?_
  obtain ⟨hgG, h⟩ := invariant_of_branch hF hB g hg
  refine ⟨hgG, hstab _ ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, h, ← hσ, inv_smul_smul]

/-- **A query item whose answers are transporters of an invariant** (the configuration call and
the rectangle call: a representative `σ` read off an answer has `σ (F X) = F Y`). Soundness
holds when `E₀` contains the even stabilizer of `F X`; completeness is the hypothesis `hcomp`
that some query has a nonempty answer when the branch has a parent isomorphism. -/
theorem valid_query_of_invariant {F : Canon L.q P.κ ℓ → Z} (hF : Equivariant F)
    (hB : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G, (L.π ⟨g, hg⟩ : Perm (Fin L.q)) • X = Y)
    (Qs : List (AuxQuery P S L)) {E₀ : Subgroup (alternatingGroup (Fin L.q))}
    (hcap : (aw E₀ : ℝ) ≤ P.β * L.q)
    (hstab : ∀ e : alternatingGroup (Fin L.q), (e : Perm (Fin L.q)) • F X = F X → e ∈ E₀)
    (hlen : Qs.length ≤ 2) (hcalls : ∀ Q ∈ Qs, AggCall P S Q.mode Q.T)
    (hrep : ∀ Q ∈ Qs, ∀ σ, Q.read Q.T.answer = some σ →
      ((σ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) • F X = F Y)
    (hcomp : (S.answer ∩ B).Nonempty → ∃ Q ∈ Qs, ∃ σ, Q.read Q.T.answer = some σ) :
    (query Qs E₀ : AuxItem P S L).Valid B := by
  refine ⟨cap_of_aw hcap, hlen, hcalls, fun Q hQ σ hσ g hg => ?_, hcomp⟩
  obtain ⟨hgG, hgF⟩ := invariant_of_branch hF hB g hg
  refine ⟨hgG, hstab _ ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, hgF, ← hrep Q hQ σ hσ, inv_smul_smul]

end Branch

/-! ### Configuration and rectangle queries -/

/-- **A configuration query item** (Lemma A.12, `GI.Paper.lem_exact_configuration`). The
branch carries a nontrivial homogeneous coherent configuration `c` on at least `δq` labels
(through `ι`). If every answer represents a configuration transporter, and the label image of
every isomorphism of the branch is one too, then the item with group
`E₀ = Alt(Γ) ∩ configGroup` is sound and has the cap `aw(E₀) ≤ βq`: two transporters differ by
an element of the configuration group (the coset statement of Lemma A.12). -/
theorem valid_query_config {δ : ℝ} (hβ : max (1 - δ) (1 / 2) < P.β) :
    ∃ q₀ : ℕ, ∀ {Ω C : Type} {S : State Ω C} (L : GiantLabels S) {B : Set (Perm Ω)} (n : ℕ)
      (c : Coloring n) (side target : Bool) (ι : Fin n ↪ Fin L.q), Coherent c →
      Homogeneous c side → NontrivialOffDiagonal c side → δ * L.q ≤ n → q₀ ≤ L.q →
      ∀ Qs : List (AuxQuery P S L), Qs.length ≤ 2 → (∀ Q ∈ Qs, AggCall P S Q.mode Q.T) →
      (∀ Q ∈ Qs, ∀ σ, Q.read Q.T.answer = some σ →
        ((σ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) ∈
          configTransporter ι c side target) →
      (∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G,
        ((L.π ⟨g, hg⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) ∈
          configTransporter ι c side target) →
      ((S.answer ∩ B).Nonempty → ∃ Q ∈ Qs, ∃ σ, Q.read Q.T.answer = some σ) →
      (query Qs ((configGroup ι c side).comap (alternatingGroup (Fin L.q)).subtype) :
        AuxItem P S L).Valid B := by
  obtain ⟨q₀, hq₀⟩ := lem_exact_configuration hβ
  refine ⟨q₀, fun L B n c side target ι hc hh hn hδ hq Qs hlen hcalls hrep hB hcomp => ?_⟩
  have hδ' : δ * Fintype.card (Fin L.q) ≤ n := by simpa using hδ
  have hq' : q₀ ≤ Fintype.card (Fin L.q) := by simpa using hq
  obtain ⟨-, hcoset, hcap⟩ := hq₀ (Fin L.q) n c side ι hc hh hn hδ' hq'
  set E₀ := (configGroup ι c side).comap (alternatingGroup (Fin L.q)).subtype
  have hE : E₀.map (alternatingGroup (Fin L.q)).subtype ≤ configGroup ι c side :=
    Subgroup.map_comap_le _ _
  have hK := hcap _ hE
  rw [Fintype.card_fin] at hK
  let e := E₀.equivMapOfInjective (alternatingGroup (Fin L.q)).subtype
    (alternatingGroup (Fin L.q)).subtype_injective
  have hcapE : GI.SectionCaps.Cap E₀ ⌊P.β * L.q⌋₊ :=
    GI.SectionCaps.of_injective e.toMonoidHom e.injective ((aw_le_iff _).1 (Nat.le_floor hK))
  refine ⟨hcapE, hlen, hcalls, fun Q hQ σ hσ g hg => ?_, hcomp⟩
  obtain ⟨hgG, hgT⟩ := hB g hg
  refine ⟨hgG, ?_⟩
  show ((σ⁻¹ * L.π ⟨g, hgG⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)) ∈
    configGroup ι c side
  rw [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (hcoset target _ (hrep Q hQ σ hσ) _).1 hgT

/-- **A rectangle query item** (Lemma 5.1 and the rectangle branch of Algorithm
`alg:auxiliary`, `GI.Paper.alg_auxiliary_rectangle_branch`). The left side `W` of the
rectangle with matrix `M` is mapped by the aligning permutation `a₀` onto the left side of the
target rectangle with matrix `N`. If every answer represents `a₀ σ` with `σ` a left
transporter (`leftOvercoset M N`), and the label image of every isomorphism of the branch is
`a₀ σ` with `σ` a left transporter too, then the item with group `leftGroup M` is sound: two
left transporters differ by an element of `leftGroup M` (`leftOvercoset_coset`). The cap of
`leftGroup M` is the cap of Lemma 5.1 (`hcap`). -/
theorem valid_query_rectangle {B : Set (Perm Ω)} {W R : Finset (Fin L.q)}
    (M N : W → R → Bool) (a₀ : alternatingGroup (Fin L.q))
    (Qs : List (AuxQuery P S L)) (hcap : (aw (leftGroup M) : ℝ) ≤ P.β * L.q)
    (hlen : Qs.length ≤ 2) (hcalls : ∀ Q ∈ Qs, AggCall P S Q.mode Q.T)
    (hrep : ∀ Q ∈ Qs, ∀ σ, Q.read Q.T.answer = some σ → a₀⁻¹ * σ ∈ leftOvercoset M N)
    (hB : ∀ g ∈ S.answer ∩ B, ∃ hg : g ∈ S.G, a₀⁻¹ * L.π ⟨g, hg⟩ ∈ leftOvercoset M N)
    (hcomp : (S.answer ∩ B).Nonempty → ∃ Q ∈ Qs, ∃ σ, Q.read Q.T.answer = some σ) :
    (query Qs (leftGroup M) : AuxItem P S L).Valid B := by
  refine ⟨cap_of_aw hcap, hlen, hcalls, fun Q hQ σ hσ g hg => ?_, hcomp⟩
  obtain ⟨hgG, hgM⟩ := hB g hg
  refine ⟨hgG, ?_⟩
  have := (leftOvercoset_coset (hrep Q hQ σ hσ) _).1 hgM
  rwa [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at this

end AuxItem

namespace Halving

variable (H : Halving S L)

/-- **The parity twist** (Lemma A.11, `GI.Paper.lem_large_symmetry_constant_cert_twist`):
if the label image of `t` is `(a b)(c d)` with `a ≠ b` in `Φ` and `c ≠ d` outside `Φ`, then
`t ∈ H` and `H = H₀ ∪ t H₀`. -/
theorem twist_facts {a b c d : Fin L.q} (ha : a ∈ H.Φ) (hb : b ∈ H.Φ) (hab : a ≠ b)
    (hc : c ∉ H.Φ) (hd : d ∉ H.Φ) (hcd : c ≠ d) (htG : H.t ∈ S.G)
    (ht : (L.π ⟨H.t, htG⟩ : Perm (Fin L.q)) = swap a b * swap c d) :
    H.t ∈ H.big ∧ ∀ g ∈ H.big, g ∈ H.even ∨ H.t⁻¹ * g ∈ H.even := by
  obtain ⟨htP, -, hsplit⟩ :=
    lem_large_symmetry_constant_cert_twist L.π ha hb hab hc hd hcd ⟨H.t, htG⟩ ht
  refine ⟨(L.mem_lift).2 ⟨htG, htP⟩, fun g hg => ?_⟩
  obtain ⟨hgG, hgP⟩ := (L.mem_lift).1 hg
  rcases hsplit ⟨g, hgG⟩ hgP with h | h
  · exact Or.inl ((L.mem_lift).2 ⟨hgG, h⟩)
  · exact Or.inr ((L.mem_lift).2 ⟨S.G.mul_mem (S.G.inv_mem htG) hgG, h⟩)

/-- **No twist** (Lemma A.11, `GI.Paper.lem_large_symmetry_constant_cert_no_twist`): if at
most one label lies outside `Φ`, then `H = H₀`, so `t = 1` represents both parity classes. -/
theorem no_twist_facts (hC : H.Φᶜ.card ≤ 1) (ht : H.t = 1) :
    H.t ∈ H.big ∧ ∀ g ∈ H.big, g ∈ H.even ∨ H.t⁻¹ * g ∈ H.even := by
  have heq := lem_large_symmetry_constant_cert_no_twist L.π H.Φ hC
  refine ⟨ht ▸ H.big.one_mem, fun g hg => Or.inl ?_⟩
  obtain ⟨hgG, hgP⟩ := (L.mem_lift).1 hg
  have : (⟨g, hgG⟩ : S.G) ∈ (permitted H.Φ H.Φᶜ).comap L.π := hgP
  rw [heq] at this
  exact (L.mem_lift).2 ⟨hgG, this⟩

/-- **The lifts of the generators meet every coset of the kernel** (Lemma A.11: "They map
onto generators of `H₀/K`"): if for each `h ∈ H₀` some `a ∈ A` has the same label action on
`Φ`, then `h a⁻¹ ∈ K`. -/
theorem onto_of_agree (hA : H.A ≤ H.even)
    (hagree : ∀ h ∈ H.even, ∃ a ∈ H.A, ∃ (hh : h ∈ S.G) (ha : a ∈ S.G),
      ∀ x ∈ H.Φ, (L.π ⟨h, hh⟩ : Perm (Fin L.q)) x = (L.π ⟨a, ha⟩ : Perm (Fin L.q)) x) :
    ∀ h ∈ H.even, ∃ a ∈ H.A, h * a⁻¹ ∈ H.ker := by
  intro h hh
  obtain ⟨a, haA, hhG, haG, hx⟩ := hagree h hh
  refine ⟨a, haA, ?_⟩
  have hm : h * a⁻¹ ∈ S.G := S.G.mul_mem hhG (S.G.inv_mem haG)
  obtain ⟨hh', hhE⟩ := (L.mem_lift).1 hh
  obtain ⟨ha', haE⟩ := (L.mem_lift).1 (hA haA)
  refine (L.mem_lift).2 ⟨hm, ?_, ?_⟩
  · have : L.π ⟨h * a⁻¹, hm⟩ = L.π ⟨h, hhG⟩ * (L.π ⟨a, haG⟩)⁻¹ := by
      rw [← map_inv, ← map_mul]; rfl
    rw [this]
    exact (evenSides H.Φ H.Φᶜ).mul_mem hhE ((evenSides H.Φ H.Φᶜ).inv_mem haE)
  · -- `π(a)` maps `Φ` onto itself, so `π(a)⁻¹ x ∈ Φ` for `x ∈ Φ`.
    rintro ⟨x, hxΦ⟩
    have hP : (L.π ⟨a, haG⟩ : Perm (Fin L.q)) ∈ sides H.Φ H.Φᶜ := evenSides_le haE
    have hstab : (L.π ⟨a, haG⟩ : Perm (Fin L.q))⁻¹ ∈
        MulAction.stabilizer (Perm (Fin L.q)) ((H.Φ : Finset (Fin L.q)) : Set (Fin L.q)) :=
      Subgroup.inv_mem _ hP.1
    have hy : (L.π ⟨a, haG⟩ : Perm (Fin L.q))⁻¹ x ∈ H.Φ := by
      have h1 : (L.π ⟨a, haG⟩ : Perm (Fin L.q))⁻¹ • x ∈
          (L.π ⟨a, haG⟩ : Perm (Fin L.q))⁻¹ • ((H.Φ : Finset (Fin L.q)) : Set (Fin L.q)) :=
        Set.smul_mem_smul_set hxΦ
      rw [MulAction.mem_stabilizer_iff.1 hstab] at h1
      exact h1
    have : L.π ⟨h * a⁻¹, hm⟩ = L.π ⟨h, hhG⟩ * (L.π ⟨a, haG⟩)⁻¹ := by
      rw [← map_inv, ← map_mul]; rfl
    change (L.π ⟨h * a⁻¹, hm⟩ : Perm (Fin L.q)) x = x
    rw [this]
    change (L.π ⟨h, hhG⟩ : Perm (Fin L.q)) ((L.π ⟨a, haG⟩ : Perm (Fin L.q))⁻¹ x) = x
    rw [hx _ hy]
    simp

/-! ### Small kernel orbits from the Johnson blocks -/

/-- **The kernel orbits of the halving branch are small** (Lemma A.11,
`GI.Paper.lem_large_symmetry_constant_cert_half`: "Every physical `K`-orbit has size at most
`n/2`"). The hypotheses are those of the lemma for the action of `G` on the domain: an
equivariant block map `p` onto the `h`-subsets of the labels with fibers of equal size `f`,
`1 ≤ h ≤ q/2`. With `θ ≥ 1/2` this is the fact `orb_small` of `Halving.Valid`. -/
theorem orb_small_of_blocks [Finite Ω]
    (p : S.dom → Finset (Fin L.q)) {h f : ℕ}
    (hp : ∀ (g : S.G) v, p (S.domHom g v) =
      (p v).map ((L.π g : alternatingGroup (Fin L.q)) : Perm (Fin L.q)).toEmbedding)
    (hcard : ∀ v, (p v).card = h)
    (hfib : ∀ Bl : Finset (Fin L.q), Bl.card = h →
      (@Finset.univ S.dom (Fintype.ofFinite _) |>.filter fun v => p v = Bl).card = f)
    (h1 : 1 ≤ h) (h2 : 2 * h ≤ L.q) (hdom : L.q < 2 * H.Φ.card) (hθ : 1 / 2 ≤ P.θ) :
    ∀ v ∈ S.dom, (Nat.card (orb H.ker v) : ℝ) ≤ P.θ * S.size := by
  classical
  letI : Fintype S.dom := Fintype.ofFinite _
  letI : MulAction S.G S.dom := MulAction.compHom S.dom S.domHom
  intro v hv
  let π' : S.G →* Perm (Fin L.q) := (alternatingGroup (Fin L.q)).subtype.comp L.π
  let K : Subgroup S.G := H.ker.subgroupOf S.G
  have hK : ∀ k ∈ K, ∀ a ∈ H.Φ, π' k a = a := by
    intro k hk a ha
    obtain ⟨hkG, hkE⟩ := (L.mem_lift).1 (Subgroup.mem_subgroupOf.1 hk)
    exact (mem_fixingSubgroup_iff _).1 hkE.2 a ha
  have hcardΓ : Fintype.card (Fin L.q) = L.q := Fintype.card_fin _
  have hhalf := lem_large_symmetry_constant_cert_half π' p (fun g w => hp g w) hcard
    (by convert hfib using 4) h1 (by rw [hcardΓ]; exact h2) H.Φ (by rw [hcardΓ]; exact hdom)
    K hK ⟨v, hv⟩
  -- the orbit of `v` under `K` in `Ω` is the image of its orbit in the domain
  have horb : orb H.ker v = Subtype.val '' MulAction.orbit K (⟨v, hv⟩ : S.dom) := by
    ext w
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨k v, (S.dom_inv k (H.ker_le hk) v).2 hv⟩,
        ⟨⟨⟨k, H.ker_le hk⟩, Subgroup.mem_subgroupOf.2 hk⟩, ?_⟩, rfl⟩
      rfl
    · rintro ⟨u, ⟨k, rfl⟩, rfl⟩
      exact ⟨((k : S.G) : Perm Ω), Subgroup.mem_subgroupOf.1 k.2, rfl⟩
  have hc : Nat.card (orb H.ker v) = Fintype.card (MulAction.orbit K (⟨v, hv⟩ : S.dom)) := by
    rw [horb, Nat.card_image_of_injective Subtype.val_injective, Nat.card_eq_fintype_card]
  have hs : S.size = Fintype.card S.dom := by rw [State.size, Nat.card_eq_fintype_card]
  rw [hc, hs]
  have : (2 * Fintype.card (MulAction.orbit K (⟨v, hv⟩ : S.dom)) : ℝ) ≤ Fintype.card S.dom := by
    exact_mod_cast hhalf
  have h0 : (0 : ℝ) ≤ Fintype.card S.dom := by positivity
  nlinarith

end Halving

end GI.Algorithm
