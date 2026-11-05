module

public import Workspace.Transport
public import Workspace.Compat
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

/-!
# Exact answers and the rules that combine them (Section 3.2, Section 6)

An *instance* of the recursion is a group `G ≤ Sym(Ω)`, an active domain `D ⊆ Ω`
and two colorings `x, y : Ω → C`. Its *exact answer* is the set of allowed
relabelings that take `x` to `y` on the active domain:
`answer G D x y = {g ∈ G | y (g v) = x v for all v ∈ D}`.

We keep the convention of `Workspace/Transport.lean`: permutations compose as
functions, `(p * q) v = p (q v)`, and `g` takes `x` to `y` when `y ∘ g = x`. The
paper's right action `x^g = y` is this relation. The paper's "absorb `π` into the
target coloring and continue under `H` on `(x, y^{π⁻¹})`" is, in this convention,
"continue on `(x, y ∘ π)` and left-multiply the returned answer by `π`".

An answer on an orbit `Δ` of a subgroup `K` is kept in *lifted* form: the set of
elements of `K` (permutations of the whole `Ω`) whose action on `Δ` takes `x` to
`y`. The paper solves the faithful image of `K` on `Δ` and lifts the result with
the restriction map (Section 3: "Its caller retains the homomorphism used to lift
the returned generators and representative"). The lifted form is the full
preimage, so the two describe the same answer
(`answer_restrict_image`). Which form is stored is a question of representation,
left for the machine stage.

The lemmas here are the exact-combination rules used in the proof of Lemma 6.1:

* `answer_eq_smul_aut`, `answer_empty_or_coset`: a nonempty exact answer is a full
  coset `t · Aut`;
* `answer_orbit_chain`, `answer_orbit_chain_empty`: the orbit chain rule of
  Section 3.2;
* `answer_cover`: an exhaustive family of overcosets `τ_j H_j`, each continued
  under `H_j` on `(x, y ∘ τ_j)`, gives the exact answer (`LiftAndContinue` and
  `CombineExact` of Algorithms 3 and 5, and every coset enumeration);
* `answer_combine`: the same with some branches supplying exact pieces directly;
* `answer_recolor`: joint color compression does not change the answer.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm
open scoped Pointwise

variable {Ω C : Type*}

/-- The exact answer of an instance: the allowed relabelings `g ∈ G` taking `x` to
`y` on the active domain `D`. -/
def answer (G : Subgroup (Perm Ω)) (D : Set Ω) (x y : Ω → C) : Set (Perm Ω) :=
  {g | g ∈ G ∧ ∀ v ∈ D, y (g v) = x v}

theorem mem_answer {G : Subgroup (Perm Ω)} {D : Set Ω} {x y : Ω → C} {g : Perm Ω} :
    g ∈ answer G D x y ↔ g ∈ G ∧ ∀ v ∈ D, y (g v) = x v := Iff.rfl

theorem answer_subset_group (G : Subgroup (Perm Ω)) (D : Set Ω) (x y : Ω → C) :
    answer G D x y ⊆ G := fun _ hg => hg.1

/-- On the whole domain, the exact answer is the string transporter of
`Workspace/Transport.lean`. -/
theorem answer_univ (G : Subgroup (Perm Ω)) (x y : Ω → C) :
    answer G Set.univ x y = transporter G x y := by
  ext g
  simp [answer, transporter, Transports]

/-- A shrinking of the domain can only enlarge the answer. -/
theorem answer_anti {G : Subgroup (Perm Ω)} {D D' : Set Ω} (h : D' ⊆ D) (x y : Ω → C) :
    answer G D x y ⊆ answer G D' x y :=
  fun _ hg => ⟨hg.1, fun v hv => hg.2 v (h hv)⟩

theorem answer_mono_group {G H : Subgroup (Perm Ω)} (h : H ≤ G) (D : Set Ω) (x y : Ω → C) :
    answer H D x y ⊆ answer G D x y :=
  fun _ hg => ⟨h hg.1, hg.2⟩

/-- `G` leaves the set `D` invariant. -/
def Invariant (G : Subgroup (Perm Ω)) (D : Set Ω) : Prop :=
  ∀ g ∈ G, ∀ v, g v ∈ D ↔ v ∈ D

theorem Invariant.mono {G H : Subgroup (Perm Ω)} {D : Set Ω} (hD : Invariant G D)
    (h : H ≤ G) : Invariant H D := fun g hg => hD g (h hg)

theorem Invariant.compl {G : Subgroup (Perm Ω)} {D : Set Ω} (hD : Invariant G D) :
    Invariant G Dᶜ := fun g hg v => not_congr (hD g hg v)

theorem Invariant.diff {G : Subgroup (Perm Ω)} {D D₁ : Set Ω} (hD : Invariant G D)
    (hD₁ : Invariant G D₁) : Invariant G (D \ D₁) := fun g hg v =>
  and_congr (hD g hg v) (not_congr (hD₁ g hg v))

theorem Invariant.inv_mem {G : Subgroup (Perm Ω)} {D : Set Ω} (hD : Invariant G D)
    {g : Perm Ω} (hg : g ∈ G) {v : Ω} (hv : v ∈ D) : g⁻¹ v ∈ D := by
  have := hD g⁻¹ (G.inv_mem hg) v
  exact this.2 hv

/-- The automorphism group `Aut_G(x on D)` of an invariant domain, as a subgroup. -/
def autGroup (G : Subgroup (Perm Ω)) (D : Set Ω) (hD : Invariant G D) (x : Ω → C) :
    Subgroup (Perm Ω) where
  carrier := answer G D x x
  one_mem' := ⟨G.one_mem, fun _ _ => rfl⟩
  mul_mem' {a b} ha hb := ⟨G.mul_mem ha.1 hb.1, fun v hv => by
    rw [Perm.mul_apply, ha.2 (b v) ((hD b hb.1 v).2 hv), hb.2 v hv]⟩
  inv_mem' {a} ha := ⟨G.inv_mem ha.1, fun v hv => by
    have h := ha.2 (a⁻¹ v) (hD.inv_mem ha.1 hv)
    rw [Perm.apply_inv_self] at h
    exact h.symm⟩

theorem mem_autGroup {G : Subgroup (Perm Ω)} {D : Set Ω} {hD : Invariant G D} {x : Ω → C}
    {g : Perm Ω} : g ∈ autGroup G D hD x ↔ g ∈ answer G D x x := Iff.rfl

theorem autGroup_le (G : Subgroup (Perm Ω)) (D : Set Ω) (hD : Invariant G D) (x : Ω → C) :
    autGroup G D hD x ≤ G := fun _ hg => hg.1

theorem autGroup_invariant {G : Subgroup (Perm Ω)} {D : Set Ω} (hD : Invariant G D)
    (x : Ω → C) {E : Set Ω} (hE : Invariant G E) : Invariant (autGroup G D hD x) E :=
  hE.mono (autGroup_le G D hD x)

/-- **A nonempty exact answer is a full coset.** If `t` takes `x` to `y` on an
invariant domain, the answer is `t · Aut_G(x on D)`. -/
theorem answer_eq_smul_aut {G : Subgroup (Perm Ω)} {D : Set Ω} (hD : Invariant G D)
    {x y : Ω → C} {t : Perm Ω} (ht : t ∈ answer G D x y) :
    answer G D x y = t • (autGroup G D hD x : Set (Perm Ω)) := by
  ext g
  rw [Set.mem_smul_set]
  constructor
  · intro hg
    refine ⟨t⁻¹ * g, ⟨G.mul_mem (G.inv_mem ht.1) hg.1, fun v hv => ?_⟩, by simp⟩
    have hgv : g v ∈ D := (hD g hg.1 v).2 hv
    have hw : t⁻¹ (g v) ∈ D := hD.inv_mem ht.1 hgv
    have h1 := ht.2 _ hw
    rw [Perm.apply_inv_self] at h1
    rw [Perm.mul_apply, ← h1, hg.2 v hv]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨G.mul_mem ht.1 ha.1, fun v hv => ?_⟩
    rw [smul_eq_mul, Perm.mul_apply, ht.2 _ ((hD a ha.1 v).2 hv), ha.2 v hv]

/-- "Every recursive call returns the complete set of compatible relabelings": an
exact answer is empty or a coset `t · Aut_G(x on D)` with `t ∈ G`. -/
theorem answer_empty_or_coset {G : Subgroup (Perm Ω)} {D : Set Ω} (hD : Invariant G D)
    (x y : Ω → C) :
    answer G D x y = ∅ ∨
      ∃ t ∈ G, answer G D x y = t • (autGroup G D hD x : Set (Perm Ω)) := by
  rcases (answer G D x y).eq_empty_or_nonempty with h | ⟨t, ht⟩
  · exact Or.inl h
  · exact Or.inr ⟨t, ht.1, answer_eq_smul_aut hD ht⟩

/-- **Orbit chain rule** (Section 3.2). Let `D₁ ⊆ D` be `G`-invariant, and let `t`
take `x` to `y` on `D₁`. Then the answer on `D` is `t` times the answer on `D \ D₁`
under `H = Aut_G(x on D₁)`, for the colorings `(x, y ∘ t)`: "absorb `π` into the
target coloring and continue under `H`". -/
theorem answer_orbit_chain {G : Subgroup (Perm Ω)} {D D₁ : Set Ω} (hD₁ : Invariant G D₁)
    (hsub : D₁ ⊆ D) {x y : Ω → C} {t : Perm Ω} (ht : t ∈ answer G D₁ x y) :
    answer G D x y = t • answer (autGroup G D₁ hD₁ x) (D \ D₁) x (y ∘ t) := by
  ext g
  rw [Set.mem_smul_set]
  constructor
  · intro hg
    refine ⟨t⁻¹ * g, ⟨?_, fun v hv => ?_⟩, by simp⟩
    · have hg₁ := answer_anti hsub x y hg
      rw [answer_eq_smul_aut hD₁ ht] at hg₁
      obtain ⟨a, ha, rfl⟩ := Set.mem_smul_set.1 hg₁
      simpa [smul_eq_mul] using ha
    · simp only [Function.comp_apply, Perm.mul_apply, Perm.apply_inv_self]
      exact hg.2 v hv.1
  · rintro ⟨a, ⟨ha, hrest⟩, rfl⟩
    refine ⟨G.mul_mem ht.1 (autGroup_le G D₁ hD₁ x ha), fun v hv => ?_⟩
    rw [smul_eq_mul, Perm.mul_apply]
    by_cases h₁ : v ∈ D₁
    · rw [ht.2 _ ((hD₁ a (autGroup_le G D₁ hD₁ x ha) v).2 h₁), ha.2 v h₁]
    · exact hrest v ⟨hv, h₁⟩

/-- The orbit chain stops with the empty answer when the first orbit has none. -/
theorem answer_orbit_chain_empty {G : Subgroup (Perm Ω)} {D D₁ : Set Ω} (hsub : D₁ ⊆ D)
    {x y : Ω → C} (h : answer G D₁ x y = ∅) : answer G D x y = ∅ :=
  Set.eq_empty_of_subset_empty (h ▸ answer_anti hsub x y)

/-- One lifted continuation: if `τ ∈ G` and `H ≤ G`, then `τ` times the answer of
`H` on `(x, y ∘ τ)` is the part of the answer of `G` inside the overcoset `τ H`.
This is `LiftAndContinue` (Section 5.4). -/
theorem smul_answer_eq_inter {G H : Subgroup (Perm Ω)} {D : Set Ω} {x y : Ω → C}
    {τ : Perm Ω} (hτ : τ ∈ G) (hH : H ≤ G) :
    τ • answer H D x (y ∘ τ) = answer G D x y ∩ τ • (H : Set (Perm Ω)) := by
  ext g
  simp only [Set.mem_inter_iff, Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨h, ⟨hH', hh⟩, rfl⟩
    exact ⟨⟨G.mul_mem hτ (hH hH'), fun v hv => hh v hv⟩, h, hH', rfl⟩
  · rintro ⟨⟨_, hg⟩, h, hH', rfl⟩
    exact ⟨h, ⟨hH', fun v hv => hg v hv⟩, rfl⟩

/-- **Exhaustive overcosets** (`CombineExact` over `LiftAndContinue`, and every
coset enumeration). If every element of the answer lies in one of the overcosets
`τ_j H_j` with `τ_j ∈ G` and `H_j ≤ G`, then the union over `j` of
`τ_j · answer(H_j, D, x, y ∘ τ_j)` is the exact answer. -/
theorem answer_cover {ι : Type*} {G : Subgroup (Perm Ω)} {D : Set Ω} {x y : Ω → C}
    (τ : ι → Perm Ω) (H : ι → Subgroup (Perm Ω)) (hτ : ∀ j, τ j ∈ G) (hH : ∀ j, H j ≤ G)
    (hcov : answer G D x y ⊆ ⋃ j, τ j • (H j : Set (Perm Ω))) :
    (⋃ j, τ j • answer (H j) D x (y ∘ τ j)) = answer G D x y := by
  simp_rw [smul_answer_eq_inter (hτ _) (hH _), ← Set.inter_iUnion]
  exact Set.inter_eq_left.2 hcov

/-- **Exact combination with exact pieces.** Some branches return an exact piece
`P_i ⊆ answer` directly (the large-symmetry branch, a terminal), the others an
overcoset `τ_j H_j` that is continued. If pieces and overcosets together cover
the answer, the union is the exact answer. -/
theorem answer_combine {ι κ : Type*} {G : Subgroup (Perm Ω)} {D : Set Ω} {x y : Ω → C}
    (P : κ → Set (Perm Ω)) (hP : ∀ i, P i ⊆ answer G D x y)
    (τ : ι → Perm Ω) (H : ι → Subgroup (Perm Ω)) (hτ : ∀ j, τ j ∈ G) (hH : ∀ j, H j ≤ G)
    (hcov : answer G D x y ⊆ (⋃ i, P i) ∪ ⋃ j, τ j • (H j : Set (Perm Ω))) :
    (⋃ i, P i) ∪ (⋃ j, τ j • answer (H j) D x (y ∘ τ j)) = answer G D x y := by
  simp_rw [smul_answer_eq_inter (hτ _) (hH _), ← Set.inter_iUnion]
  apply Set.Subset.antisymm
  · exact Set.union_subset (Set.iUnion_subset hP) Set.inter_subset_left
  · intro g hg
    rcases hcov hg with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hg, h⟩

/-- **Coset enumeration.** If `G` is covered by the cosets `τ_j K` of a subgroup
`K ≤ G` with `τ_j ∈ G`, the answer is the union of `τ_j · answer(K, D, x, y ∘ τ_j)`.
This is the enumeration of an actual quotient, the product refinement, and the
single-factor normalization of Algorithm 5. -/
theorem answer_cosets {ι : Type*} {G K : Subgroup (Perm Ω)} {D : Set Ω} {x y : Ω → C}
    (τ : ι → Perm Ω) (hτ : ∀ j, τ j ∈ G) (hK : K ≤ G)
    (hcov : (G : Set (Perm Ω)) ⊆ ⋃ j, τ j • (K : Set (Perm Ω))) :
    (⋃ j, τ j • answer K D x (y ∘ τ j)) = answer G D x y :=
  answer_cover τ (fun _ => K) hτ (fun _ => hK)
    ((answer_subset_group G D x y).trans hcov)

/-- **Joint color compression** (Section 3): renaming colors by one map that is
injective on the colors used by `x` and `y` does not change the answer. -/
theorem answer_recolor {C' : Type*} (G : Subgroup (Perm Ω)) (D : Set Ω) (x y : Ω → C)
    (c : C → C') (hc : Set.InjOn c (Set.range x ∪ Set.range y)) :
    answer G D (c ∘ x) (c ∘ y) = answer G D x y := by
  ext g
  simp only [mem_answer, Function.comp_apply]
  refine and_congr_right fun _ => forall₂_congr fun v _ => ?_
  exact ⟨fun h => hc (Or.inr ⟨_, rfl⟩) (Or.inl ⟨_, rfl⟩) h, fun h => by rw [h]⟩

/-- A change of coordinates or a retained column partition leaves the group, the
domain and the colorings unchanged, so it changes no answer. (The paper: "Changing
coordinates or retaining a column partition loses no relabeling.") -/
theorem answer_congr {G G' : Subgroup (Perm Ω)} {D D' : Set Ω} {x x' y y' : Ω → C}
    (hG : G = G') (hD : D = D') (hx : x = x') (hy : y = y') :
    answer G D x y = answer G' D' x' y' := by
  subst hG hD hx hy; rfl

/-! ### The faithful image on the active domain -/

/-- The restriction of `G` to an invariant domain `D`: the action on `D` itself. -/
def restrictHom (G : Subgroup (Perm Ω)) (D : Set Ω) (hD : Invariant G D) : G →* Perm D where
  toFun g := (g : Perm Ω).subtypePerm fun v => hD g g.2 v
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

theorem restrictHom_apply (G : Subgroup (Perm Ω)) (D : Set Ω) (hD : Invariant G D) (g : G)
    (v : D) : (restrictHom G D hD g v : Ω) = (g : Perm Ω) v := rfl

/-- **The faithful image represents the same answer** (Section 3: "Every fresh call
uses the faithful permutation image on its own active domain … Its caller retains
the homomorphism used to lift the returned generators and representative"). The
answer on `D` in lifted form is the full preimage, under the restriction to `D`, of
the answer of the image group `G|_D` on all of `D`. -/
theorem answer_restrict_image (G : Subgroup (Perm Ω)) (D : Set Ω) (hD : Invariant G D)
    (x y : Ω → C) :
    answer G D x y = {g | ∃ hg : g ∈ G, restrictHom G D hD ⟨g, hg⟩ ∈
      answer (restrictHom G D hD).range Set.univ (x ∘ Subtype.val) (y ∘ Subtype.val)} := by
  ext g
  constructor
  · rintro ⟨hg, hxy⟩
    exact ⟨hg, ⟨⟨_, rfl⟩, fun v _ => hxy v v.2⟩⟩
  · rintro ⟨hg, -, hxy⟩
    exact ⟨hg, fun v hv => hxy ⟨v, hv⟩ trivial⟩

/-! ### The coset rule for an exhaustive family -/

/-- **The coset rule** (Section 3.2: "For an exhaustive family of branches, the
successful answers can again be represented by one coset: take one successful
representative, adjoin the stabilizer generators in each successful answer, and
adjoin the ratios of successful representatives. This is valid because the
exhaustive union is the full isomorphism coset."). Let the successful answers be
cosets `t_i H_i` whose union is the exact answer, and let `t₀` be one successful
representative. Then the automorphism group is generated by the groups `H_i` and the
ratios `t₀⁻¹ t_i`, so the answer is `t₀ ⟨H_i, t₀⁻¹ t_i⟩`. -/
theorem combine_generators {ι : Type*} {G : Subgroup (Perm Ω)} {D : Set Ω}
    (hD : Invariant G D) {x y : Ω → C} (t : ι → Perm Ω) (H : ι → Subgroup (Perm Ω))
    (hunion : (⋃ i, t i • (H i : Set (Perm Ω))) = answer G D x y) (i₀ : ι) :
    autGroup G D hD x =
      Subgroup.closure ((⋃ i, (H i : Set (Perm Ω))) ∪ Set.range fun i => (t i₀)⁻¹ * t i) := by
  have hmem : ∀ i, t i ∈ answer G D x y := fun i => by
    rw [← hunion]
    exact Set.mem_iUnion.2 ⟨i, Set.mem_smul_set.2 ⟨1, (H i).one_mem, by simp⟩⟩
  have hcoset := answer_eq_smul_aut hD (hmem i₀)
  -- `t₀⁻¹ g ∈ Aut` for every `g` in the answer.
  have hratio : ∀ g ∈ answer G D x y, (t i₀)⁻¹ * g ∈ autGroup G D hD x := by
    intro g hg
    rw [hcoset] at hg
    obtain ⟨a, ha, rfl⟩ := Set.mem_smul_set.1 hg
    simpa [smul_eq_mul] using ha
  apply le_antisymm
  · intro a ha
    -- `t₀ a` lies in some `t_i H_i`, so `a = (t₀⁻¹ t_i) h`.
    have hta : t i₀ * a ∈ answer G D x y := by
      rw [hcoset]; exact Set.mem_smul_set.2 ⟨a, ha, rfl⟩
    rw [← hunion] at hta
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hta
    obtain ⟨h, hh, hth⟩ := Set.mem_smul_set.1 hi
    have : a = ((t i₀)⁻¹ * t i) * h := by
      rw [smul_eq_mul] at hth
      rw [mul_assoc, hth, inv_mul_cancel_left]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr ⟨i, rfl⟩))
      (Subgroup.subset_closure (Or.inl (Set.mem_iUnion.2 ⟨i, hh⟩)))
  · rw [Subgroup.closure_le]
    rintro g (hg | ⟨i, rfl⟩)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hg
      -- `t_i h` and `t_i` are both in the answer, so `h = (t₀⁻¹ t_i)⁻¹ (t₀⁻¹ t_i h) ∈ Aut`.
      have h1 := hratio _ (hmem i)
      have h2 := hratio (t i * g) (by
        rw [← hunion]; exact Set.mem_iUnion.2 ⟨i, Set.mem_smul_set.2 ⟨g, hi, rfl⟩⟩)
      have := (autGroup G D hD x).mul_mem ((autGroup G D hD x).inv_mem h1) h2
      simpa [mul_assoc] using this
    · exact hratio _ (hmem i)

end GI.Algorithm
