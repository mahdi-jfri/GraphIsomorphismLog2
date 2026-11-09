module

public import Workspace.Degree.GraphRooted
public import Workspace.Algorithm.Exact
public import Workspace.Cited.AlgoPermGroups

/-!
# From slots to positions

The string queries of the graph program live on `Fin (m * m)` with `m = n * D`. This file moves the
step of Section 9.2 of the paper to these positions.

* `slotE`: slots to numbers, `(u, i) ↦ i + D * u`.
* `pairE`: pairs to numbers, `(s, s') ↦ s' + m * s`.
* `diag`: the action of a permutation of the slots on pairs of slots.
* `colorX`: the string.
* `mem_answer_iff`: the answer of the string query is the image under `diag` of the query.
* `answer_coset`: what a canonical answer says.
-/

@[expose] public section

namespace GI.Degree

open Equiv GI.Cited GI.Algorithm
open scoped Pointwise

variable {n D : ℕ}

/-- Slots to numbers. -/
def slotE (n D : ℕ) : Fin n × Fin D ≃ Fin (n * D) := finProdFinEquiv

/-- Pairs to numbers. -/
def pairE (m : ℕ) : Fin m × Fin m ≃ Fin (m * m) := finProdFinEquiv

theorem slotE_val (u : Fin n) (i : Fin D) : (slotE n D (u, i) : ℕ) = i + D * u := by
  simp [slotE, finProdFinEquiv]

theorem pairE_val {m : ℕ} (s s' : Fin m) : (pairE m (s, s') : ℕ) = s' + m * s := by
  simp [pairE, finProdFinEquiv]

/-- The action on pairs of slots. -/
def diag (n D : ℕ) : Perm (Fin n × Fin D) →* Perm (Fin (n * D * (n * D))) where
  toFun g := (pairE (n * D)).permCongrHom (Equiv.prodCongr ((slotE n D).permCongrHom g)
    ((slotE n D).permCongrHom g))
  map_one' := by
    have h : Equiv.prodCongr (1 : Perm (Fin (n * D))) (1 : Perm (Fin (n * D))) =
        (1 : Perm (Fin (n * D) × Fin (n * D))) := by ext x <;> rfl
    rw [map_one, h, map_one]
  map_mul' f g := by
    have h : ∀ a b : Perm (Fin (n * D)), Equiv.prodCongr (a * b) (a * b) =
        Equiv.prodCongr a a * Equiv.prodCongr b b := fun a b => by ext x <;> rfl
    rw [map_mul, h, map_mul]

theorem diag_apply (g : Perm (Fin n × Fin D)) (s s' : Fin n × Fin D) :
    diag n D g (pairE (n * D) (slotE n D s, slotE n D s')) =
      pairE (n * D) (slotE n D (g s), slotE n D (g s')) := by
  simp [diag, Equiv.permCongrHom, Equiv.permCongr]

/-- `diag` is injective, when there is a slot. -/
theorem diag_injective (z : Fin n × Fin D) : Function.Injective (diag n D) := by
  intro f g h
  ext1 s
  have h1 := congrArg (fun t : Perm _ => t (pairE (n * D) (slotE n D s, slotE n D z))) h
  simp only [diag_apply] at h1
  have h2 := (pairE (n * D)).injective h1
  exact (slotE n D).injective (congrArg Prod.fst h2)

/-- The string of a graph. -/
noncomputable def colorX (D : ℕ) (ℓ : Fin n → ℕ) (r : ℕ) (X : SimpleGraph (Fin n))
    (f : Fin n → List (Fin n)) (p : Fin (n * D * (n * D))) : ℕ :=
  slotColor ℓ r X f ((slotE n D).symm ((pairE (n * D)).symm p).1)
    ((slotE n D).symm ((pairE (n * D)).symm p).2)

theorem colorX_pair (ℓ : Fin n → ℕ) (r : ℕ) (X : SimpleGraph (Fin n)) (f : Fin n → List (Fin n))
    (s s' : Fin n × Fin D) :
    colorX D ℓ r X f (pairE (n * D) (slotE n D s, slotE n D s')) = slotColor ℓ r X f s s' := by
  simp [colorX]

variable {ℓ : Fin n → ℕ} {r : ℕ} {X Y : SimpleGraph (Fin n)} {fX fY : Fin n → List (Fin n)}

/-- A position is a pair. -/
theorem exists_pair (p : Fin (n * D * (n * D))) :
    ∃ s s', p = pairE (n * D) (slotE n D s, slotE n D s') :=
  ⟨(slotE n D).symm ((pairE (n * D)).symm p).1, (slotE n D).symm ((pairE (n * D)).symm p).2,
    by simp⟩

/-- **The answer of the string query is the image of the query.** -/
theorem mem_answer_iff {t : Perm (Fin (n * D * (n * D)))} :
    t ∈ answer ((slotGroup D (ballGroup ℓ r X)).map (diag n D)) Set.univ
        (colorX D ℓ r X fX) (colorX D ℓ r Y fY) ↔
      ∃ g ∈ Query D ℓ r X Y fX fY, diag n D g = t := by
  constructor
  · rintro ⟨⟨g, hg, rfl⟩, h⟩
    refine ⟨g, ⟨hg, fun s s' => ?_⟩, rfl⟩
    have := h _ (Set.mem_univ (pairE (n * D) (slotE n D s, slotE n D s')))
    rwa [diag_apply, colorX_pair, colorX_pair] at this
  · rintro ⟨g, ⟨hg, h⟩, rfl⟩
    refine ⟨⟨g, hg, rfl⟩, fun p _ => ?_⟩
    obtain ⟨s, s', rfl⟩ := exists_pair p
    rw [diag_apply, colorX_pair, colorX_pair]
    exact h s s'

/-- Two elements of the query differ by an element of the group of `X`. -/
theorem query_inv_mul {g h : Perm (Fin n × Fin D)} (hg : g ∈ Query D ℓ r X Y fX fY)
    (hh : h ∈ Query D ℓ r X Y fX fY) : g⁻¹ * h ∈ querySub D ℓ r X fX := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hg.1) hh.1, fun s s' => ?_⟩
  have h1 := hg.2 (g⁻¹ (h s)) (g⁻¹ (h s'))
  simp only [Perm.apply_inv_self] at h1
  rw [Perm.mul_apply, Perm.mul_apply, ← h1]
  exact hh.2 s s'

theorem query_mul {g f : Perm (Fin n × Fin D)} (hg : g ∈ Query D ℓ r X Y fX fY)
    (hf : f ∈ querySub D ℓ r X fX) : g * f ∈ Query D ℓ r X Y fX fY := by
  refine ⟨Subgroup.mul_mem _ hg.1 hf.1, fun s s' => ?_⟩
  rw [Perm.mul_apply, Perm.mul_apply, hg.2]
  exact hf.2 s s'

/-- A list in the image lifts. -/
theorem exists_lift_list {α β : Type} (φ : α → β) (S : Set α) (l : List β)
    (h : ∀ b ∈ l, ∃ a ∈ S, φ a = b) : ∃ l' : List α, l'.map φ = l ∧ ∀ a ∈ l', a ∈ S := by
  induction l with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons b l ih =>
    obtain ⟨a, ha, rfl⟩ := h b (by simp)
    obtain ⟨l', h1, h2⟩ := ih fun c hc => h c (by simp [hc])
    refine ⟨a :: l', by simp [h1], ?_⟩
    simpa using ⟨ha, h2⟩

/-- **What a canonical answer says.** If the answer is the coset `t ⟨hs⟩`, then `t` is the image of
an element of the query, and `hs` is the image of a list of generators of the group of `X`. -/
theorem answer_coset (z : Fin n × Fin D) {t : Perm (Fin (n * D * (n * D)))}
    {hs : List (Perm (Fin (n * D * (n * D))))}
    (hA : t • (gens hs : Set (Perm (Fin (n * D * (n * D))))) =
      answer ((slotGroup D (ballGroup ℓ r X)).map (diag n D)) Set.univ
        (colorX D ℓ r X fX) (colorX D ℓ r Y fY)) :
    ∃ g₀ ∈ Query D ℓ r X Y fX fY, diag n D g₀ = t ∧
      ∃ hs' : List (Perm (Fin n × Fin D)), hs'.map (diag n D) = hs ∧
        Subgroup.closure {f | f ∈ hs'} = querySub D ℓ r X fX := by
  have ht : t ∈ answer ((slotGroup D (ballGroup ℓ r X)).map (diag n D)) Set.univ
      (colorX D ℓ r X fX) (colorX D ℓ r Y fY) := by
    rw [← hA]
    exact ⟨1, Subgroup.one_mem _, by simp⟩
  obtain ⟨g₀, hg₀, rfl⟩ := mem_answer_iff.1 ht
  refine ⟨g₀, hg₀, rfl, ?_⟩
  have hin : ∀ c ∈ gens hs, ∃ f ∈ querySub D ℓ r X fX, diag n D f = c := by
    intro c hc
    have h1 : diag n D g₀ * c ∈ answer ((slotGroup D (ballGroup ℓ r X)).map (diag n D)) Set.univ
        (colorX D ℓ r X fX) (colorX D ℓ r Y fY) := by
      rw [← hA]
      exact ⟨c, hc, rfl⟩
    obtain ⟨g, hg, he⟩ := mem_answer_iff.1 h1
    refine ⟨g₀⁻¹ * g, query_inv_mul hg₀ hg, ?_⟩
    rw [map_mul, map_inv, he]
    group
  obtain ⟨hs', h1, h2⟩ := exists_lift_list (diag n D) (querySub D ℓ r X fX : Set _) hs
    fun b hb => hin b (Subgroup.subset_closure hb)
  refine ⟨hs', h1, le_antisymm ?_ fun f hf => ?_⟩
  · rw [Subgroup.closure_le]
    exact h2
  · have h3 : diag n D (g₀ * f) ∈ answer ((slotGroup D (ballGroup ℓ r X)).map (diag n D)) Set.univ
        (colorX D ℓ r X fX) (colorX D ℓ r Y fY) :=
      mem_answer_iff.2 ⟨_, query_mul hg₀ hf, rfl⟩
    rw [← hA] at h3
    obtain ⟨c, hc, he⟩ := h3
    have h4 : c = diag n D f := by
      rw [map_mul] at he
      exact mul_left_cancel he
    rw [h4] at hc
    have h5 : gens hs = (Subgroup.closure {f | f ∈ hs'}).map (diag n D) := by
      rw [MonoidHom.map_closure, gens, ← h1]
      congr 1
      ext x
      simp
    change diag n D f ∈ gens hs at hc
    rw [h5] at hc
    obtain ⟨f', hf', he'⟩ := hc
    rwa [← diag_injective z he']

end GI.Degree
