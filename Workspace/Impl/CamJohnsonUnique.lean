import Workspace.Impl.CamNormalizer
import Workspace.Cited.AlgoJohnson

/-!
# Two Johnson identifications of one group differ by a permutation of `Fin m`

If `ι₀` and `ι` both carry `H` onto the action of `Alt(m)` on `k`-sets, then `ι₀⁻¹ ι` normalizes
that action, so by `cam_normalizer` it is the action of some `σ`. For `m = 6` the normalizer fact
is not available, but the reduction only needs `m = 6` with `k = 1`, where every permutation of the
one-element sets comes from a permutation of `Fin m` (`cam_kset_one`).
-/

namespace GI.Impl

open Equiv GI.Cited

variable {m : ℕ}

/-- Every permutation of the one-element subsets comes from a permutation of `Fin m`. -/
theorem cam_kset_one (β : Perm {A : Finset (Fin m) // A.card = 1}) :
    ∃ σ : Perm (Fin m), β = kSetPerm σ := by
  choose f hf using fun x : Fin m => Finset.card_eq_one.mp (β ⟨{x}, Finset.card_singleton x⟩).2
  have hinj : Function.Injective f := fun x y h => by
    have := β.injective (Subtype.ext (by rw [hf, hf, h]) :
      β ⟨{x}, Finset.card_singleton x⟩ = β ⟨{y}, Finset.card_singleton y⟩)
    simpa using congrArg Subtype.val this
  refine ⟨.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩, ?_⟩
  ext s : 1
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp s.2
  obtain rfl : s = ⟨{x}, Finset.card_singleton x⟩ := Subtype.ext hx
  apply Subtype.ext
  rw [hf, cam_kSetPerm_apply, Finset.map_singleton]
  rfl

/-- **Uniqueness of Johnson identifications up to `Sym(m)`.** -/
theorem cam_johnson_unique {n k : ℕ} (hm : 5 ≤ m) (hk1 : 1 ≤ k) (hk : 2 * k < m)
    (h6 : m = 6 → k = 1) {H : Subgroup (Perm (Fin n))}
    {ι₀ ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}}
    (h0 : IsJohnsonId H ι₀) (h1 : IsJohnsonId H ι) :
    ∃ σ : Perm (Fin m), ∀ w, ι w = kSetPerm σ (ι₀ w) := by
  set β : Perm {A : Finset (Fin m) // A.card = k} := ι₀.symm.trans ι
  suffices hσ : ∃ σ : Perm (Fin m), β = kSetPerm σ by
    obtain ⟨σ, hσ⟩ := hσ
    refine ⟨σ, fun w => ?_⟩
    rw [← hσ]
    simp [β]
  by_cases hm6 : m = 6
  · obtain rfl := h6 hm6
    exact cam_kset_one β
  refine cam_normalizer (by omega) hk1 hk β fun h hh => ?_
  -- the element of `H` that acts as `h` through `ι₀`
  let g : Perm (Fin n) := ι₀.trans ((kSetPerm h).trans ι₀.symm)
  have hg : g ∈ H := (h0 g).mpr ⟨h, hh, fun x => by simp [g]⟩
  obtain ⟨h', hh', hgh'⟩ := (h1 g).mp hg
  refine ⟨h', hh', ?_⟩
  ext A : 1
  -- `β (h A) = h' (β A)`, applied to `A = β⁻¹ A'`
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  set A' := β⁻¹ A
  have hA : A = β A' := by simp [A']
  rw [hA]
  have := hgh' (ι₀.symm A')
  simp only [g, Equiv.trans_apply, Equiv.apply_symm_apply] at this
  simpa [β] using this

end GI.Impl
