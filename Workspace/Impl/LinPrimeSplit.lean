module

public import Workspace.Impl.LinFiniteProjection
public import Workspace.Impl.LinPrimaryMatrixAlgebra
public import Mathlib.Data.Nat.GCD.BigOperators

@[expose] public section

/-! The kernel of a primary coordinate projection consists exactly of the
elements killed by an integer coprime to p. It is therefore preserved by
every additive map, which is the characteristic property needed for descent. -/
namespace GI.Impl
open scoped BigOperators

structure linPrimeSplitData {d : ℕ} (m : Fin d → ℕ) (p : ℕ) where
  exponent : Fin d → ℕ
  cofactor : Fin d → ℕ
  factor : ∀ i, m i = p ^ exponent i * cofactor i
  coprime : ∀ i, p.Coprime (cofactor i)

theorem linPrimeSplit_dvd {d p : ℕ} {m : Fin d → ℕ} (D : linPrimeSplitData m p) (i : Fin d) :
    linPrimaryOrders p D.exponent i ∣ m i := ⟨D.cofactor i, D.factor i⟩

noncomputable def linPrimeProjection {d p : ℕ} {m : Fin d → ℕ} (D : linPrimeSplitData m p) :
    linFiniteVec m →+ linFiniteVec (linPrimaryOrders p D.exponent) :=
  linFiniteProjection m (linPrimaryOrders p D.exponent) (linPrimeSplit_dvd D)

theorem linPrimeProjection_surjective {d p : ℕ} {m : Fin d → ℕ} (D : linPrimeSplitData m p) :
    Function.Surjective (linPrimeProjection D) := linFiniteProjection_surjective _ _ _

set_option maxHeartbeats 1000000 in
theorem linPrimeProjection_kernel {d p : ℕ} {m : Fin d → ℕ} (D : linPrimeSplitData m p)
    (hm : ∀ i, 0 < m i) (x : linFiniteVec m) :
    linPrimeProjection D x = 0 ↔ ∃ t : ℕ, p.Coprime t ∧ t • x = 0 := by
  constructor
  · intro hx
    have hq := (linFiniteProjection_kernel m (linPrimaryOrders p D.exponent) (linPrimeSplit_dvd D) hm x).mp hx
    let t := ∏ i, D.cofactor i
    have ht : p.Coprime t := Nat.coprime_prod_right_iff.mpr (fun i _ => D.coprime i)
    refine ⟨t, ht, (linFiniteNsmul_zero_iff m hm t x).mpr ?_⟩
    intro i
    have hti : D.cofactor i ∣ t := Finset.dvd_prod_of_mem D.cofactor (Finset.mem_univ i)
    have hh := Nat.mul_dvd_mul hti (hq i)
    change D.cofactor i * p ^ D.exponent i ∣ t * (x i).val at hh
    rw [Nat.mul_comm (D.cofactor i), ← D.factor i] at hh
    exact hh
  · rintro ⟨t, ht, hx⟩
    apply (linFiniteProjection_kernel m (linPrimaryOrders p D.exponent) (linPrimeSplit_dvd D) hm x).mpr
    have hmul := (linFiniteNsmul_zero_iff m hm t x).mp hx
    intro i
    have hq : p ^ D.exponent i ∣ t * (x i).val := (linPrimeSplit_dvd D i).trans (hmul i)
    exact (ht.pow_left (D.exponent i)).dvd_of_dvd_mul_left hq

theorem linPrimeProjection_preserved {d p : ℕ} {m : Fin d → ℕ} (D : linPrimeSplitData m p)
    (hm : ∀ i, 0 < m i) (f : linFiniteVec m →+ linFiniteVec m) (x : linFiniteVec m)
    (hx : linPrimeProjection D x = 0) : linPrimeProjection D (f x) = 0 := by
  obtain ⟨t, ht, he⟩ := (linPrimeProjection_kernel D hm x).mp hx
  apply (linPrimeProjection_kernel D hm (f x)).mpr
  refine ⟨t, ht, ?_⟩
  simpa only [map_nsmul, map_zero] using congrArg f he

end GI.Impl
