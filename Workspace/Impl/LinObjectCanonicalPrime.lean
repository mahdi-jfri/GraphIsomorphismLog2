import Workspace.Impl.LinObjectDataFrames
import Workspace.Impl.LinObjectPrimeBound
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fintype.Perm

namespace GI.Impl
open GI.Cited GI.Multicoset
open scoped IsMulCommutative

theorem linObjectProduct_annihilated {ι Q : Type*} [AddCommGroup Q]
    (B : ι → Submodule ℤ Q) (q : ℕ) (hq : ∀ a : Q, q • a = 0) (w : ∀ i, Q ⧸ B i) : q • w = 0 := by
  funext i
  obtain ⟨a,ha⟩ := Submodule.mkQ_surjective (B i) (w i)
  change q • w i = 0
  rw [← ha,← map_nsmul,hq,map_zero]

variable {n : ℕ} (as ns : List (Equiv.Perm (Fin n)))
variable [((gens ns).subgroupOf (gens as)).Normal]
variable [IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as))]

theorem linObjectCanonicalOrder_dvd_factorial :
    Nat.card ((gens as) ⧸ (gens ns).subgroupOf (gens as)) ∣ n.factorial := by
  have hA : Nat.card (gens as) ∣ n.factorial := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] using
      (gens as).card_subgroup_dvd_card
  exact ((gens ns).subgroupOf (gens as)).card_quotient_dvd_card.trans hA

theorem linObjectCanonical_annihilated
    (a : Additive ((gens as) ⧸ (gens ns).subgroupOf (gens as))) :
    Nat.card ((gens as) ⧸ (gens ns).subgroupOf (gens as)) • a = 0 := by
  apply Additive.toMul.injective
  rw [toMul_nsmul]
  exact pow_card_eq_one'

theorem linObjectCanonicalFrame_product_prime {d : ℕ} (Y : List (TmRiO n)) (m : Fin d → ℕ)
    (E : linObjectOriginalProduct as (linObjectCanonicalProjection as ns) Y ≃+ linFiniteVec m)
    (i : Fin d) (p : ℕ) (hp : p.Prime) (hpi : p ∣ m i) : p ≤ n := by
  have hmi := linObjectModulus_dvd_annihilator m E
    (Nat.card ((gens as) ⧸ (gens ns).subgroupOf (gens as)))
    (linObjectProduct_annihilated _ _ (linObjectCanonical_annihilated as ns)) i
  exact hp.dvd_factorial.mp (hpi.trans (hmi.trans (linObjectCanonicalOrder_dvd_factorial as ns)))

theorem linObjectCanonicalFrame_quotient_prime {d : ℕ} (Y : List (TmRiO n)) (m : Fin d → ℕ)
    (E : linObjectOriginalQuotient as (linObjectCanonicalProjection as ns) Y ≃+ linFiniteVec m)
    (i : Fin d) (p : ℕ) (hp : p.Prime) (hpi : p ∣ m i) : p ≤ n :=
  linObjectQuotient_prime_bound _ m E (linObjectCanonical_annihilated as ns)
    (linObjectCanonicalOrder_dvd_factorial as ns) i p hp hpi

end GI.Impl
