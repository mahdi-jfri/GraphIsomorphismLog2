module

public import Workspace.Impl.LinIntPresentation
public import Mathlib.Algebra.Group.TypeTags.Hom

@[expose] public section

/-! The actual coordinate map for the complete abelian presentation.
It sends the i-th integer basis vector to the i-th quotient generator. -/
namespace GI.Impl

/-- Evaluate integer coordinates in an abelian group, written additively. -/
noncomputable def linCoordMap {t : ℕ} {Q : Type*} [CommGroup Q] (v : Fin t → Q) :
    (Fin t → ℤ) →ₗ[ℤ] Additive Q :=
  ∑ i, (LinearMap.proj i).smulRight (Additive.ofMul (v i))

@[simp] theorem linCoordMap_single {t : ℕ} {Q : Type*} [CommGroup Q]
    (v : Fin t → Q) (i : Fin t) (z : ℤ) :
    linCoordMap v (Pi.single i z) = z • Additive.ofMul (v i) := by
  classical
  simp [linCoordMap, LinearMap.sum_apply, Pi.single_apply]

/-- The same map with multiplicative type tags, for SLP evaluation. -/
noncomputable def linCoordHom {t : ℕ} {Q : Type*} [CommGroup Q] (v : Fin t → Q) :
    Multiplicative (Fin t → ℤ) →* Q :=
  AddMonoidHom.toMultiplicativeLeft (linCoordMap v).toAddMonoidHom

@[simp] theorem linCoordHom_single {t : ℕ} {Q : Type*} [CommGroup Q]
    (v : Fin t → Q) (i : Fin t) (z : ℤ) :
    linCoordHom v (Multiplicative.ofAdd (Pi.single i z)) = v i ^ z := by
  change Additive.toMul (linCoordMap v (Pi.single i z)) = _
  rw [linCoordMap_single]
  rfl

/-- Quotient generators generate the whole coordinate image. -/
theorem linCoordHom_surjective {t : ℕ} {G Q : Type*} [Group G] [CommGroup Q]
    (π : G →* Q) (hπ : Function.Surjective π) (N : Subgroup G) (hN : N ≤ π.ker)
    (as : Fin t → G) (hgen : N ⊔ Subgroup.closure (Set.range as) = ⊤) :
    Function.Surjective (linCoordHom (fun i => π (as i))) := by
  let q := linCoordHom (fun i => π (as i))
  let K := q.range.comap π
  have hn : N ≤ K := by
    intro x hx
    change π x ∈ q.range
    rw [hN hx]
    exact q.range.one_mem
  have ha : Subgroup.closure (Set.range as) ≤ K := by
    apply (Subgroup.closure_le K).mpr
    rintro _ ⟨i, rfl⟩
    change π (as i) ∈ q.range
    exact ⟨Multiplicative.ofAdd (Pi.single i (1 : ℤ)), by simp [q]⟩
  have hall : (⊤ : Subgroup G) ≤ K := by rw [← hgen]; exact sup_le hn ha
  intro y
  obtain ⟨x, rfl⟩ := hπ y
  exact hall (Subgroup.mem_top x)

theorem linCoordMap_surjective {t : ℕ} {G Q : Type*} [Group G] [CommGroup Q]
    (π : G →* Q) (hπ : Function.Surjective π) (N : Subgroup G) (hN : N ≤ π.ker)
    (as : Fin t → G) (hgen : N ⊔ Subgroup.closure (Set.range as) = ⊤) :
    Function.Surjective (linCoordMap (fun i => π (as i))) := by
  intro y
  obtain ⟨z, hz⟩ := linCoordHom_surjective π hπ N hN as hgen (Additive.toMul y)
  exact ⟨Multiplicative.toAdd z, congrArg Additive.ofMul hz⟩

end GI.Impl
