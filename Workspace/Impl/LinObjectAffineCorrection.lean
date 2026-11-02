import Workspace.Impl.LinObjectDiagonalCriterion
import Workspace.Impl.LinObjectFrameActions

namespace GI.Impl
open GI.Cited GI.Multicoset

theorem linObjectAffineInverseZero {G V : Type*} [Group G] [AddCommGroup V]
    (ρ : G →* (V ≃+ V)) (c : G → V) (hc : ∀ g h, c (g*h) = ρ g (c h)+c g)
    (g : G) (v : V) : ρ g⁻¹ v + c g⁻¹ = 0 ↔ v = c g := by
  have h1 := hc 1 1
  simp only [one_mul,map_one] at h1
  change c 1 = c 1 + c 1 at h1
  have h0 : c 1 = 0 := add_left_cancel (show c 1 + c 1 = c 1 + 0 by simpa using h1.symm)
  have hbase : ρ g⁻¹ (c g)+c g⁻¹ = 0 := by
    rw [← hc,inv_mul_cancel,h0]
  constructor
  · intro hv
    exact (ρ g⁻¹).injective (add_right_cancel (hv.trans hbase.symm))
  · rintro rfl
    exact hbase

/-- The affine transporter from zero to the source coordinate has the
orientation needed by right object actions: g, followed by a common A
correction, carries the source configuration to the reference. -/
theorem linObjectAffineCorrection_iff {n : ℕ} {Q : Type*} [CommGroup Q]
    (H A : Subgroup (Equiv.Perm (Fin n))) (hn : Normalizes H A)
    (Y : Multiset (CObj ℕ (Equiv.Perm (Fin n))))
    (hy : ∀ g ∈ H, Conf A Y (Y ↼ g)) (π : A →* Q) (hπ : Function.Surjective π)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A)
    (g : H) (Z : Multiset (CObj ℕ (Equiv.Perm (Fin n)))) (hZ : Conf A Y Z) :
    (linObjectDiagonalModule A π Y).mkQ (linObjectConfigCoord A π Y Z) =
      (linObjectDiagonalModule A π Y).mkQ (linObjectFiniteConfigAction H A hn Y hy π hπ hker g 0) ↔
      ∃ a ∈ A, (Z ↼ g.val) ↼ a = Y := by
  let ρ := linObjectAffineQuotientLinear H A hn Y hy π hπ hker
  let c := fun k : H => (linObjectDiagonalModule A π Y).mkQ
    (linObjectFiniteConfigAction H A hn Y hy π hπ hker k 0)
  let v := (linObjectDiagonalModule A π Y).mkQ (linObjectConfigCoord A π Y Z)
  have hc := linObjectAffineQuotient_cocycle H A hn Y hy π hπ hker
  have he := linObjectAffineQuotient_eval H A hn Y hy π hπ hker g⁻¹ Z hZ
  have hzg : Conf A Y (Z ↼ g.val) :=
    (affine_law hn g.property (hy _ g.property) hZ).2.2
  have hi := linObjectAffineInverseZero ρ c hc g v
  change v = c g ↔ _
  rw [← hi]
  change ρ g⁻¹ v+c g⁻¹ = 0 ↔ _
  change ρ g⁻¹ v+c g⁻¹ = (linObjectDiagonalModule A π Y).mkQ
    (linObjectConfigCoord A π Y (Z ↼ (g⁻¹).val⁻¹)) at he
  simp only [Subgroup.coe_inv,inv_inv] at he
  rw [he]
  exact linObjectDiagonal_transport_iff A π hπ Y (Z ↼ g.val) hzg hker

end GI.Impl
