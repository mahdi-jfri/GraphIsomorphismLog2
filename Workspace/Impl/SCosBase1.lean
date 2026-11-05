module

public import Workspace.Impl.SCosSpec
public import Workspace.Impl.Lift

@[expose] public section

/-!
# The base case `Φ = {α}`, the mathematics

`N = n + n` and `X = nintSum x = x₁ ⊕ x₂`. The base function computes `τ = X⁻¹ (n + x₁ α)`,
which is the point `n + x₂⁻¹ (x₁ α)` of the second copy (`scosBase_tau`). An element
`g ⊕ h` of `𝒢.map nintSum` maps `n + α` to `n + h α` (`scosBase_natAdd`). So it maps `n + α`
to `τ` exactly when `h α = x₂⁻¹ (x₁ α)`, which is the test of `scosC_single`
(`scosBase_mem_scosC`, `scosBase_scosC_empty`). The stabilizer of `n + α` in `𝒢.map nintSum`
is `L(𝒢, {α})` (`scosBase_pstab`).
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

variable {n : ℕ}

theorem scosBase_natAdd_inj {a b : Fin n} (h : Fin.natAdd n a = Fin.natAdd n b) : a = b := by
  have e := congrArg Fin.val h
  simp only [Fin.val_natAdd] at e
  exact Fin.ext (by omega)

/-- `g ⊕ h` maps `n + α` to `n + h α`. -/
theorem scosBase_natAdd (g : ScosPair n) (a : Fin n) :
    nintSum g (Fin.natAdd n a) = Fin.natAdd n (g.2 a) := by
  apply Fin.ext
  rw [nintSum_apply, sumToFin_sumCongr_natAdd]
  simp only [Fin.val_natAdd]

/-- `g ⊕ h` maps `α` to `g α`. -/
theorem scosBase_castAdd (g : ScosPair n) (a : Fin n) :
    nintSum g (Fin.castAdd n a) = Fin.castAdd n (g.1 a) := by
  apply Fin.ext
  rw [nintSum_apply, sumToFin_sumCongr_castAdd]
  simp

/-- The point `τ`: `X⁻¹ (n + x₁ α) = n + x₂⁻¹ (x₁ α)`. -/
theorem scosBase_tau (x : ScosPair n) (a : Fin n) :
    (nintSum x)⁻¹ (Fin.natAdd n (x.1 a)) = Fin.natAdd n (x.2⁻¹ (x.1 a)) := by
  rw [← map_inv, scosBase_natAdd]
  rfl

/-- The stabilizer of `n + α` in `𝒢.map nintSum` is `L(𝒢, {α})`. -/
theorem scosBase_pstab {𝒢 : Subgroup (ScosPair n)} {a : Fin n} (h : ScosInv 𝒢 {a}) :
    pointwiseStab (𝒢.map nintSum) [Fin.natAdd n a] = (scosL 𝒢 {a}).map nintSum := by
  ext σ
  constructor
  · rintro ⟨⟨g, hg, rfl⟩, hfix⟩
    have e := hfix _ (List.mem_singleton_self _)
    rw [scosBase_natAdd] at e
    have e2 : g.2 a = a := scosBase_natAdd_inj e
    exact ⟨g, (mem_scosL_single h).mpr ⟨hg, e2⟩, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨hu1, hu2⟩ := (mem_scosL_single h).mp hu
    refine ⟨⟨u, hu1, rfl⟩, fun i hi => ?_⟩
    rw [List.mem_singleton.mp hi, scosBase_natAdd, hu2]

/-- An element of `𝒢` whose sum maps `n + α` to `τ` gives a point of the subcoset. -/
theorem scosBase_mem_scosC {x : ScosPair n} {𝒢 : Subgroup (ScosPair n)} {a : Fin n}
    (h : ScosInv 𝒢 {a}) {g : ScosPair n} (hg : g ∈ 𝒢)
    (ht : nintSum g (Fin.natAdd n a) = Fin.natAdd n (x.2⁻¹ (x.1 a))) :
    x * g ∈ scosC x 𝒢 {a} := by
  rw [scosBase_natAdd] at ht
  exact (scosC_single h).mpr ⟨g, hg, rfl, scosBase_natAdd_inj ht⟩

/-- If the subcoset is not empty, then `τ` is in the orbit of `n + α`. -/
theorem scosBase_of_mem {x : ScosPair n} {𝒢 : Subgroup (ScosPair n)} {a : Fin n}
    (h : ScosInv 𝒢 {a}) {y : ScosPair n} (hy : y ∈ scosC x 𝒢 {a}) :
    ∃ σ ∈ 𝒢.map nintSum, σ (Fin.natAdd n a) = Fin.natAdd n (x.2⁻¹ (x.1 a)) := by
  obtain ⟨g, hg, -, e⟩ := (scosC_single h).mp hy
  exact ⟨nintSum g, ⟨g, hg, rfl⟩, by rw [scosBase_natAdd, e]⟩

/-- Entry `i` of the list of a permutation. -/
theorem scosBase_get_perm {m : ℕ} (σ : Perm (Fin m)) (i : Fin m) :
    ((List.finRange m).map fun j => Val.nat (σ j))[(i : ℕ)]? = some (.nat (σ i)) := by
  simp

end GI.Impl
