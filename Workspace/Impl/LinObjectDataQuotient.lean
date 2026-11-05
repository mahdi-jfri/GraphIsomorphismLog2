module

public import Workspace.Impl.LinObjectDataMath

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Multicoset
open scoped IsMulCommutative

theorem linObjectAbelian_normal {n : ℕ} (as ns : List (Equiv.Perm (Fin n)))
    (hc : ∀ a ∈ gens as, ∀ b ∈ gens as, a * b * a⁻¹ * b⁻¹ ∈ gens ns) :
    ((gens ns).subgroupOf (gens as)).Normal := by
  let N := (gens ns).subgroupOf (gens as)
  have hcomm : ∀ x y : gens as, x * y * x⁻¹ * y⁻¹ ∈ N :=
    fun x y => hc x.val x.property y.val y.property
  have hh := linChain_normal N ([] : List (gens as)) hcomm 0
  simpa only [linChain_zero] using hh

theorem linObjectAbelian_comm {n : ℕ} (as ns : List (Equiv.Perm (Fin n)))
    [((gens ns).subgroupOf (gens as)).Normal]
    (hc : ∀ a ∈ gens as, ∀ b ∈ gens as, a * b * a⁻¹ * b⁻¹ ∈ gens ns) :
    IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as)) :=
  linQuotient_comm ((gens ns).subgroupOf (gens as))
    (fun x y => hc x.val x.property y.val y.property)

theorem linPermPresentation_certificate {n : ℕ} (as ns : List (Equiv.Perm (Fin n)))
    [((gens ns).subgroupOf (gens as)).Normal]
    [IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as))]
    (M : Matrix (Fin as.length) (Fin as.length) ℤ) (hM : linPermPresentation ns as M) :
    linPresentationCertificate M (linObjectLiftCoord as (QuotientGroup.mk' ((gens ns).subgroupOf (gens as)))) := by
  obtain ⟨hN, hQ, hCert⟩ := hM
  exact hCert

theorem linObjectDataLocal_kernel {n p r : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (M : Matrix (Fin as.length) (Fin as.length) ℤ)
    (hM : linPresentationCertificate M (linObjectLiftCoord as π))
    (B : Fin p → Submodule ℤ (Additive Q))
    (L : Fin p → Matrix (Fin (as.length + r)) (Fin as.length) ℤ)
    (hL : ∀ i, ∃ C : Matrix (Fin r) (Fin as.length) ℤ,
      L i = linRowStack M C ∧ (linRelations C).map (linObjectLiftCoord as π) = B i) :
    ∀ i, LinearMap.ker ((B i).mkQ.comp (linObjectLiftCoord as π)) = linRelations (L i) := by
  intro i
  obtain ⟨C, he, hC⟩ := hL i
  rw [he]
  exact linObjectLocalRelation_ker M hM.1 (linObjectLiftCoord as π) hM.2.1 hM.2.2.1 hM.2.2.2
    C (B i) hC.symm

end GI.Impl
