module

public import Workspace.Impl.CamTransport

@[expose] public section

/-!
# Primitivity excludes `m = 2k`

Step 4 of the reduction of `camProg` (`CamProg.lean`). If `m = 2k`, the complement of a `k`-set is
again a `k`-set. Taking complements in every coordinate gives a fixed-point-free involution `c` of
the points that commutes with `G`, so the pairs `{x, c x}` form a block system. A primitive group on
at least three points has no such blocks.
-/

namespace GI.Impl

open Equiv GI.Cited
open scoped Pointwise

variable {n m k r : ℕ}

/-- The complement of a `k`-set, when `m = 2k`. -/
def camHalfCompl (hm : m = 2 * k) (A : {A : Finset (Fin m) // A.card = k}) :
    {A : Finset (Fin m) // A.card = k} :=
  ⟨A.1ᶜ, by rw [Finset.card_compl, Fintype.card_fin, A.2]; omega⟩

theorem cam_halfCompl_kSetPerm (hm : m = 2 * k) (h : Perm (Fin m))
    (A : {A : Finset (Fin m) // A.card = k}) :
    camHalfCompl hm (kSetPerm h A) = kSetPerm h (camHalfCompl hm A) := by
  apply Subtype.ext
  ext y
  show y ∈ (A.1.map h.toEmbedding)ᶜ ↔ y ∈ A.1ᶜ.map h.toEmbedding
  rw [Finset.mem_compl, Finset.mem_map_equiv, Finset.mem_map_equiv, Finset.mem_compl]

theorem cam_halfCompl_halfCompl (hm : m = 2 * k) (A : {A : Finset (Fin m) // A.card = k}) :
    camHalfCompl hm (camHalfCompl hm A) = A :=
  Subtype.ext (compl_compl A.1)

theorem cam_halfCompl_ne [Nonempty (Fin m)] (hm : m = 2 * k)
    (A : {A : Finset (Fin m) // A.card = k}) : camHalfCompl hm A ≠ A := by
  intro h
  obtain ⟨a⟩ := ‹Nonempty (Fin m)›
  have := congrArg (fun B : {A : Finset (Fin m) // A.card = k} => a ∈ B.1) h
  simp only [camHalfCompl, Finset.mem_compl, eq_iff_iff] at this
  exact iff_not_self this.symm

/-- **No Maróti structure of a primitive group on at least three points has `m = 2k`.** -/
theorem cam_two_mul_ne {G : Subgroup (Perm (Fin n))} (hprim : MulAction.IsPreprimitive G (Fin n))
    (hn : 3 ≤ n) {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})}
    (hM : MarotiStructure G e) : m ≠ 2 * k := by
  intro hm
  -- two points with different images give a coordinate and two different `k`-sets
  have hne : e ⟨0, by omega⟩ ≠ e ⟨1, by omega⟩ := fun h => by
    have := congrArg Fin.val (e.injective h)
    simp at this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have : Nonempty (Fin m) := by
    by_contra h0
    rw [not_nonempty_iff] at h0
    exact hi (Subtype.ext (Subsingleton.elim (α := Finset (Fin m)) _ _))
  let c : Fin n → Fin n := fun x => e.symm fun j => camHalfCompl hm (e x j)
  have hc : ∀ g ∈ G, ∀ x, c (g x) = g (c x) := by
    intro g hg x
    obtain ⟨σ, h, hgh⟩ := hM.1 g hg
    apply e.injective
    simp only [c, Equiv.apply_symm_apply, hgh]
    funext j
    rw [cam_halfCompl_kSetPerm]
  have hcc : ∀ x, c (c x) = x := fun x => by
    apply e.injective
    simp only [c, Equiv.apply_symm_apply]
    funext j
    exact cam_halfCompl_halfCompl hm _
  have hcx : ∀ x, c x ≠ x := fun x h => by
    have := congrArg (fun y => e y i) h
    simp only [c, Equiv.apply_symm_apply] at this
    exact cam_halfCompl_ne hm _ this
  let x₀ : Fin n := ⟨0, by omega⟩
  set B : Set (Fin n) := {x₀, c x₀}
  have hB : MulAction.IsBlock G B := by
    rw [MulAction.isBlock_iff_smul_eq_of_mem]
    rintro ⟨g, hg⟩ a ha hga
    have hgB : (⟨g, hg⟩ : G) • B = {g x₀, g (c x₀)} := by
      rw [Set.smul_set_insert, Set.smul_set_singleton]
      rfl
    rw [hgB]
    change g a ∈ B at hga
    have key : g x₀ = x₀ ∨ g x₀ = c x₀ := by
      rcases ha with rfl | rfl
      · exact hga
      · rcases hga with h | h
        · right
          rw [← hcc (g x₀), hc g hg, h]
        · left
          rw [← hc g hg] at h
          have := congrArg c h
          rwa [hcc, hcc] at this
    rcases key with h | h
    · rw [← hc g hg, h]
    · rw [← hc g hg, h, hcc, Set.pair_comm]
  rcases hB.subsingleton_or_eq_univ with h | h
  · exact hcx x₀ (h (Set.mem_insert_of_mem _ rfl) (Set.mem_insert _ _))
  · have hcard : (Finset.univ : Finset (Fin n)) ⊆ {x₀, c x₀} := fun y _ => by
      have : y ∈ B := h ▸ Set.mem_univ y
      simpa [B] using this
    have := (Finset.card_le_card hcard).trans (Finset.card_le_two)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega

end GI.Impl
