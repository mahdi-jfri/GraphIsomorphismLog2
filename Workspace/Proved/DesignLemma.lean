import Workspace.Proved.DesignClique
import Mathlib.Data.Fintype.EquivFin

/-!
# The Design Lemma ([H, Proposition 5.1])

We prove `GI.Cited.DesignLemma`, Babai's Design Lemma for `1/2 < α < 1`, following [H,
Section 5.1] (Helfgott, Bajpai, Dona, arXiv:1710.04574v1) and the outline in the docstring of
`GI.Cited.DesignLemma`.

Suppose both outcomes fail (`DesignCtx`). Write `C(x)` for `designDom c α x`, the dominant class
of `z ↦ c(x, z, …, z)`. The plan has three steps.

1. `designStep`: if `ℓ + 1 < k`, `u ∈ C(x)` and `u ≠ z`, then `u ∈ C(x z)`. This uses the large
   clique lemma `designTwin` (`Workspace/Proved/DesignClique.lean`).
2. `designMem`: by induction, every point of `C(∅)` that does not occur in `x` lies in `C(x)`.
3. `designTwins`: any two points `u, v ∈ C(∅)` are twins. A tuple that contains `u` is a
   reordering of `(x, u, v, …, v)`, where `x` lists the other entries. The transposition
   `(u v)` turns this tuple into `(x, v, u, …, u)`, which has the same color by step 2 and the
   clique property. Axiom (b) of configurations carries this to the reordered tuple.

So `C(∅)` is a set of pairwise twins with at least `α n` points, which contradicts the
hypothesis. Only `designLemma` is used outside this file.
-/

namespace GI.Proved

open Finset GI.Cited

variable {n k ℓ : ℕ} {c : (Fin k → Fin n) → ℕ} {α : ℝ}

/-- The empty tuple. -/
def designRoot : Fin 0 → Fin n := Fin.elim0

section

variable (H : DesignCtx n k c α)
include H

/-- **Step.** If `ℓ + 1 < k`, `u ∈ C(x)` and `u ≠ z`, then `u ∈ C(x z)`.

By the clique property (if `z ∈ C(x)`) or the large clique lemma (if `z ∉ C(x)`), the coloring
`w ↦ c(x, z, w, …, w)` is constant on `C(x) \ {z}`. The dominant class `E` of this coloring
meets `C(x)`, since both have more than `n/2` points. A common point is not `z`: the class of
`z` is `{z}`, by axiom (a) of configurations, and `E` has more than one point. So `E` contains
a point of `C(x) \ {z}`, hence all of `C(x) \ {z}`. -/
theorem designStep (hℓ : ℓ + 1 < k) (x : Fin ℓ → Fin n) {z u : Fin n}
    (hu : u ∈ designDom c α x) (huz : u ≠ z) :
    u ∈ designDom c α (Fin.snoc (α := fun _ => Fin n) x z) := by
  have hsk : ∀ w, skel₁ c (Fin.snoc (α := fun _ => Fin n) x z) w = skel₂ c x z w := by
    intro w
    simp only [skel₁, skel₂, designPad_snoc]
  obtain ⟨e, he⟩ := designDom_nonempty H (x := Fin.snoc (α := fun _ => Fin n) x z) hℓ
  obtain ⟨m, hm⟩ := designMeet H.hα (designDom_card x hu) (designDom_card _ he) ⟨u, hu⟩
  rw [mem_inter] at hm
  -- The common point `m` is not `z`.
  have hmz : m ≠ z := by
    intro hmz
    rw [hmz] at hm
    have hsub : designDom c α (Fin.snoc (α := fun _ => Fin n) x z) ⊆ {z} := by
      intro w hw
      have e1 : skel₂ c x z w = skel₂ c x z z := by
        rw [← hsk, ← hsk]
        exact designDom_eq H _ hw hm.2
      have := H.conf.1 _ _ e1 ⟨ℓ, by omega⟩ ⟨ℓ + 1, hℓ⟩
      simp [padTuple₂] at this
      simp [this]
    have h1 := card_le_card hsub
    have h2 := designDom_card _ hm.2
    have h3 : ((designDom c α (Fin.snoc (α := fun _ => Fin n) x z)).card : ℝ) ≤ 1 := by
      exact_mod_cast h1.trans (by simp)
    have h4 : (4 : ℝ) ≤ n := by exact_mod_cast (by have := H.hk; have := H.hkn; omega : 4 ≤ n)
    have := H.hα
    nlinarith
  -- The coloring `w ↦ c(x, z, w, …, w)` agrees at `u` and `m`.
  have huv : skel₂ c x z u = skel₂ c x z m := by
    by_cases hz : z ∈ designDom c α x
    · exact designClique H hℓ hz hu hz hm.1 (Ne.symm huz) (Ne.symm hmz)
    · exact designTwin H hℓ x hz hu hm.1
  exact designDom_of _ hm.2 (by rw [hsk, hsk, huv])

/-- Every point of `C(∅)` that does not occur in `x` lies in `C(x)`, for `ℓ < k`. -/
theorem designMem : ∀ ℓ, ℓ < k → ∀ (x : Fin ℓ → Fin n) (u : Fin n),
    u ∈ designDom c α (designRoot : Fin 0 → Fin n) → (∀ i, x i ≠ u) →
    u ∈ designDom c α x := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro _ x u hu _
    have : x = designRoot := funext fun i => i.elim0
    rw [this]
    exact hu
  | succ m ih =>
    intro hm x u hu hx
    rw [← Fin.snoc_init_self x]
    exact designStep H (by omega) (Fin.init x)
      (ih (by omega) (Fin.init x) u hu (fun i => hx _)) (fun e => hx (Fin.last m) e.symm)

/-- `(x, u, v, …, v)` and `(x, v, u, …, u)` have the same color when `u, v ∈ C(x)`. -/
theorem designSwapEq (hℓ : ℓ < k) (x : Fin ℓ → Fin n) {u v : Fin n}
    (hu : u ∈ designDom c α x) (hv : v ∈ designDom c α x) :
    c (padTuple₂ x u v) = c (padTuple₂ x v u) := by
  by_cases huv : u = v
  · rw [huv]
  by_cases h : ℓ + 1 < k
  · exact designClique H h hu hv hv hu huv (Ne.symm huv)
  · rw [designPad₂_full x u v (by omega), designPad₂_full x v u (by omega)]
    exact designDom_eq H x hu hv

/-- The transposition `(u v)`, for `u, v ∈ C(∅)`, keeps the color of every tuple that
contains `u`. -/
theorem designTwinsAux {u v : Fin n} (hu : u ∈ designDom c α (designRoot : Fin 0 → Fin n))
    (hv : v ∈ designDom c α (designRoot : Fin 0 → Fin n)) (t : Fin k → Fin n)
    (htu : ∃ i, t i = u) : c (Equiv.swap u v ∘ t) = c t := by
  classical
  by_cases huv : u = v
  · rw [huv, Equiv.swap_self]
    rfl
  -- List the entries of `t` other than `u` and `v` as `x`.
  set W := (univ.image t).filter fun y => y ≠ u ∧ y ≠ v with hW
  set e := W.equivFin
  set x : Fin W.card → Fin n := fun i => (e.symm i).1 with hxdef
  have hx : ∀ i, x i ≠ u ∧ x i ≠ v := fun i => (mem_filter.mp (e.symm i).2).2
  have himage : (univ.image t).card ≤ k := by
    simpa using card_image_le (s := (univ : Finset (Fin k))) (f := t)
  obtain ⟨i₀, hi₀⟩ := htu
  have huW : u ∉ W := fun h => (mem_filter.mp h).2.1 rfl
  have hvW : v ∉ W := fun h => (mem_filter.mp h).2.2 rfl
  have hWk : W.card < k := by
    have : insert u W ⊆ univ.image t := by
      intro y hy
      rcases mem_insert.mp hy with rfl | hy
      · exact mem_image.mpr ⟨i₀, mem_univ _, hi₀⟩
      · exact (mem_filter.mp hy).1
    have := card_le_card this
    rw [card_insert_of_notMem huW] at this
    omega
  have hWv : ∀ i, t i = v → W.card + 1 < k := by
    intro i hi
    have : insert u (insert v W) ⊆ univ.image t := by
      intro y hy
      rcases mem_insert.mp hy with rfl | hy
      · exact mem_image.mpr ⟨i₀, mem_univ _, hi₀⟩
      rcases mem_insert.mp hy with rfl | hy
      · exact mem_image.mpr ⟨i, mem_univ _, hi⟩
      · exact (mem_filter.mp hy).1
    have := card_le_card this
    rw [card_insert_of_notMem (by simp [huv, huW]), card_insert_of_notMem hvW] at this
    omega
  have hmem : ∀ i, t i ≠ u → t i ≠ v → t i ∈ W := fun i h1 h2 =>
    mem_filter.mpr ⟨mem_image.mpr ⟨i, mem_univ _, rfl⟩, h1, h2⟩
  -- `t` is a reordering of `(x, u, v, …, v)`.
  let τ : Fin k → Fin k := fun i =>
    if h1 : t i = u then ⟨W.card, hWk⟩
    else if h2 : t i = v then ⟨W.card + 1, hWv i h2⟩
    else ⟨(e ⟨t i, hmem i h1 h2⟩).1, lt_trans (e ⟨t i, hmem i h1 h2⟩).isLt hWk⟩
  have hτ : padTuple₂ x u v ∘ τ = t := by
    funext i
    simp only [Function.comp_apply, τ]
    by_cases h1 : t i = u
    · simp [h1, padTuple₂]
    · by_cases h2 : t i = v
      · simp [h2, show v ≠ u from Ne.symm huv, padTuple₂]
      · simp only [h1, h2, dite_false, padTuple₂, Fin.is_lt, dif_pos, Fin.eta, hxdef,
          Equiv.symm_apply_apply]
  have hux : ∀ i, x i ≠ u := fun i => (hx i).1
  have hvx : ∀ i, x i ≠ v := fun i => (hx i).2
  have hu' := designMem H W.card hWk x u hu hux
  have hv' := designMem H W.card hWk x v hv hvx
  calc c (Equiv.swap u v ∘ t) = c (padTuple₂ x v u ∘ τ) := by
        rw [← hτ, ← Function.comp_assoc, designSwap_pad₂ x u v hx]
    _ = c (padTuple₂ x u v ∘ τ) := H.conf.2 _ _ (designSwapEq H hWk x hu' hv').symm τ
    _ = c t := by rw [hτ]

/-- **Twins.** Any two points of `C(∅)` are twins. -/
theorem designTwins {u v : Fin n} (hu : u ∈ designDom c α (designRoot : Fin 0 → Fin n))
    (hv : v ∈ designDom c α (designRoot : Fin 0 → Fin n)) : Twins c u v := by
  intro t
  by_cases htu : ∃ i, t i = u
  · exact designTwinsAux H hu hv t htu
  by_cases htv : ∃ i, t i = v
  · rw [Equiv.swap_comm]
    exact designTwinsAux H hv hu t htv
  have : Equiv.swap u v ∘ t = t := by
    funext i
    exact Equiv.swap_apply_of_ne_of_ne (fun e => htu ⟨i, e⟩) (fun e => htv ⟨i, e⟩)
  rw [this]

end

/-- **The Design Lemma** ([H, Proposition 5.1]) for `1/2 < α < 1`. -/
theorem designLemma : GI.Cited.DesignLemma := by
  intro n k hk hkn α hα _ c hconf hcoh htwin
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  have H : DesignCtx n k c α :=
    { hk := hk, hkn := hkn, hα := hα, conf := hconf, coh := hcoh
      notA := fun ℓ hℓ x => by
        by_contra hj
        exact hA ⟨ℓ, hℓ, x, fun j => lt_of_not_ge fun h => hj ⟨j, h⟩⟩
      notB := fun ℓ hℓ x j hj u v w y hu hv hw hy huv hwy => by
        by_contra hne
        exact hB ⟨ℓ, hℓ, x, j, hj, u, v, w, y, hu, hv, hw, hy, huv, hwy, hne⟩ }
  obtain ⟨z, hz⟩ := designDom_nonempty H (x := (designRoot : Fin 0 → Fin n)) (by omega)
  have h1 := htwin (designDom c α (designRoot : Fin 0 → Fin n))
    (fun u hu v hv => designTwins H hu hv)
  have h2 := designDom_card (designRoot : Fin 0 → Fin n) hz
  linarith

end GI.Proved
