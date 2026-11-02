import Workspace.Impl.LinObjectAffineDiagonal

namespace GI.Impl
open GI.Cited GI.Multicoset
variable {n : ℕ} {Q Ω : Type*} [CommGroup Q] [RAct (Equiv.Perm (Fin n)) Ω]

theorem linObject_groupImage_add_iff
    (A : Subgroup (Equiv.Perm (Fin n))) (π : A →* Q)
    (C : Subgroup (Equiv.Perm (Fin n))) (hker : π.ker ≤ C.subgroupOf A) (a b : A) :
    Additive.ofMul (π a) + Additive.ofMul (π b) ∈ linObjectGroupImage A π C ↔
      a.val * b.val ∈ C := by
  change Additive.ofMul (π a * π b) ∈ _ ↔ _
  rw [← map_mul]
  exact linObject_groupImage_mem_iff A π C hker (a * b)

noncomputable def linObjectDiagonalModule (A : Subgroup (Equiv.Perm (Fin n))) (π : A →* Q) (Y : Multiset Ω) :=
  LinearMap.range (linObjectDiagonal
    (fun T : {T // T ∈ pieces A Y} => linObjectGroupImage A π (Aut A T.val)))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linObjectDiagonalCriterion (A : Subgroup (Equiv.Perm (Fin n)))
    (π : A →* Q) (hπ : Function.Surjective π) (Y Z : Multiset Ω) (hZ : Conf A Y Z)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A) :
    (linObjectDiagonalModule A π Y).mkQ (linObjectConfigCoord A π Y Z) = 0 ↔
      DCond A Y (coord A Z) := by
  unfold linObjectDiagonalModule
  rw [linObjectCommonCorrection]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨a, ha⟩ := hπ q.toMul
    have heq : Additive.ofMul (π a) = q := congrArg Additive.ofMul ha
    refine ⟨a.val, a.property, ?_⟩
    intro T hT
    have he := hq ⟨T, hT⟩
    rw [← heq] at he
    change (linObjectGroupImage A π (Aut A T)).mkQ
      (Additive.ofMul (π (linIntoSubgroup A (coord A Z T)))) +
        (linObjectGroupImage A π (Aut A T)).mkQ (Additive.ofMul (π a)) = 0 at he
    rw [← map_add, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at he
    have hm := (linObject_groupImage_add_iff A π (Aut A T) (hker T hT)
      (linIntoSubgroup A (coord A Z T)) a).mp he
    have hh := linIntoSubgroup_val A _ (coord_spec hZ hT).1
    change (linIntoSubgroup A (coord A Z T)).val = coord A Z T at hh
    rwa [hh] at hm
  · rintro ⟨a, ha, h⟩
    refine ⟨Additive.ofMul (π ⟨a, ha⟩), ?_⟩
    intro T
    have hc := (coord_spec hZ T.property).1
    have hh := linIntoSubgroup_val A _ hc
    change (linIntoSubgroup A (coord A Z T.val)).val = coord A Z T.val at hh
    have hm : (linIntoSubgroup A (coord A Z T.val)).val * a ∈ Aut A T.val := by
      rw [hh]
      exact h T.val T.property
    have he := (linObject_groupImage_add_iff A π (Aut A T.val) (hker T.val T.property)
      (linIntoSubgroup A (coord A Z T.val)) ⟨a, ha⟩).mpr hm
    change (linObjectGroupImage A π (Aut A T.val)).mkQ
      (Additive.ofMul (π (linIntoSubgroup A (coord A Z T.val)))) +
        (linObjectGroupImage A π (Aut A T.val)).mkQ (Additive.ofMul (π ⟨a, ha⟩)) = 0
    rw [← map_add, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact he

theorem linObjectDiagonal_transport_iff (A : Subgroup (Equiv.Perm (Fin n)))
    (π : A →* Q) (hπ : Function.Surjective π) (Y Z : Multiset Ω) (hZ : Conf A Y Z)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A) :
    (linObjectDiagonalModule A π Y).mkQ (linObjectConfigCoord A π Y Z) = 0 ↔
      ∃ a ∈ A, Z ↼ a = Y :=
  (linObjectDiagonalCriterion A π hπ Y Z hZ hker).trans (dcond_iff hZ)

noncomputable def linObjectAffineQuotientLinear (B A : Subgroup (Equiv.Perm (Fin n)))
    (hn : Normalizes B A) (Y : Multiset Ω) (hy : ∀ g ∈ B, Conf A Y (Y ↼ g))
    (π : A →* Q) (hπ : Function.Surjective π)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A) :
    B →* (((∀ T : {T // T ∈ pieces A Y}, Additive Q ⧸ linObjectGroupImage A π (Aut A T.val)) ⧸
      linObjectDiagonalModule A π Y) ≃+
      ((∀ T : {T // T ∈ pieces A Y}, Additive Q ⧸ linObjectGroupImage A π (Aut A T.val)) ⧸
      linObjectDiagonalModule A π Y)) :=
  linDescendRep (linObjectDiagonalModule A π Y).mkQ.toAddMonoidHom
    (Submodule.mkQ_surjective _) (linObjectAffineLinear B A hn Y hy π hπ hker)
    (linObjectAffineLinear_preserves_diagonal B A hn Y hy π hπ hker)

theorem linObjectAffineQuotient_cocycle (B A : Subgroup (Equiv.Perm (Fin n)))
    (hn : Normalizes B A) (Y : Multiset Ω) (hy : ∀ g ∈ B, Conf A Y (Y ↼ g))
    (π : A →* Q) (hπ : Function.Surjective π)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A) (g h : B) :
    (linObjectDiagonalModule A π Y).mkQ (linObjectFiniteConfigAction B A hn Y hy π hπ hker (g * h) 0) =
      linObjectAffineQuotientLinear B A hn Y hy π hπ hker g
        ((linObjectDiagonalModule A π Y).mkQ (linObjectFiniteConfigAction B A hn Y hy π hπ hker h 0)) +
          (linObjectDiagonalModule A π Y).mkQ (linObjectFiniteConfigAction B A hn Y hy π hπ hker g 0) :=
  linDescendRep_cocycle (linObjectDiagonalModule A π Y).mkQ.toAddMonoidHom
    (Submodule.mkQ_surjective _) (linObjectAffineLinear B A hn Y hy π hπ hker)
    (linObjectAffineLinear_preserves_diagonal B A hn Y hy π hπ hker)
    (fun g => linObjectFiniteConfigAction B A hn Y hy π hπ hker g 0)
    (linObjectAffine_cocycle B A hn Y hy π hπ hker) g h

theorem linObjectAffineQuotient_eval (B A : Subgroup (Equiv.Perm (Fin n)))
    (hn : Normalizes B A) (Y : Multiset Ω) (hy : ∀ g ∈ B, Conf A Y (Y ↼ g))
    (π : A →* Q) (hπ : Function.Surjective π)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A)
    (g : B) (Z : Multiset Ω) (hZ : Conf A Y Z) :
    linObjectAffineQuotientLinear B A hn Y hy π hπ hker g
        ((linObjectDiagonalModule A π Y).mkQ (linObjectConfigCoord A π Y Z)) +
      (linObjectDiagonalModule A π Y).mkQ (linObjectFiniteConfigAction B A hn Y hy π hπ hker g 0) =
        (linObjectDiagonalModule A π Y).mkQ (linObjectConfigCoord A π Y (Z ↼ g.val⁻¹)) := by
  have hi : linObjectAffineQuotientLinear B A hn Y hy π hπ hker g
      ((linObjectDiagonalModule A π Y).mkQ (linObjectConfigCoord A π Y Z)) =
        (linObjectDiagonalModule A π Y).mkQ
          (linObjectAffineLinear B A hn Y hy π hπ hker g (linObjectConfigCoord A π Y Z)) :=
    linDescendRep_image (linObjectDiagonalModule A π Y).mkQ.toAddMonoidHom
      (Submodule.mkQ_surjective _) (linObjectAffineLinear B A hn Y hy π hπ hker)
      (linObjectAffineLinear_preserves_diagonal B A hn Y hy π hπ hker) g
      (linObjectConfigCoord A π Y Z)
  rw [hi]
  rw [← map_add]
  have he := linActionLinearEquiv_eval (linObjectFiniteConfigAction B A hn Y hy π hπ hker)
    (linObjectFiniteConfigAction_affine B A hn Y hy π hπ hker) g (linObjectConfigCoord A π Y Z)
  change (linObjectDiagonalModule A π Y).mkQ
    (linObjectAffineLinear B A hn Y hy π hπ hker g (linObjectConfigCoord A π Y Z) +
      linObjectFiniteConfigAction B A hn Y hy π hπ hker g 0) = _
  change linObjectAffineLinear B A hn Y hy π hπ hker g (linObjectConfigCoord A π Y Z) +
    linObjectFiniteConfigAction B A hn Y hy π hπ hker g 0 =
      linObjectFiniteConfigAction B A hn Y hy π hπ hker g (linObjectConfigCoord A π Y Z) at he
  rw [he, linObjectFiniteConfigAction_eval B A hn Y hy π hπ hker g Z hZ]

theorem linObjectAffineQuotient_transport_iff (B A : Subgroup (Equiv.Perm (Fin n)))
    (hn : Normalizes B A) (Y : Multiset Ω) (hy : ∀ g ∈ B, Conf A Y (Y ↼ g))
    (π : A →* Q) (hπ : Function.Surjective π)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A)
    (g : B) (Z : Multiset Ω) (hZ : Conf A Y Z) :
    linObjectAffineQuotientLinear B A hn Y hy π hπ hker g
        ((linObjectDiagonalModule A π Y).mkQ (linObjectConfigCoord A π Y Z)) +
      (linObjectDiagonalModule A π Y).mkQ (linObjectFiniteConfigAction B A hn Y hy π hπ hker g 0) = 0 ↔
        ∃ a ∈ A, (Z ↼ g.val⁻¹) ↼ a = Y := by
  rw [linObjectAffineQuotient_eval B A hn Y hy π hπ hker g Z hZ]
  exact linObjectDiagonal_transport_iff A π hπ Y _
    (affine_law hn (B.inv_mem g.property) (hy _ (B.inv_mem g.property)) hZ).2.2 hker

end GI.Impl
