module

public import Workspace.Impl.LinFiniteCoordinates

@[expose] public section

/-! Reducing full finite-abelian matrices on a primary layer. The inactive
coordinates will be given a trivial action, so the ambient dimension stays fixed. -/
namespace GI.Impl
open scoped BigOperators

/-- Reduction by a multiple of p does not change the residue modulo p. -/
theorem linNatModCast {p m : ℕ} (hpm : p ∣ m) (a : ℕ) :
    ((a % m : ℕ) : ZMod p) = (a : ZMod p) := by
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_mod_of_dvd a hpm

/-- The full reduced product descends to every prime dividing its target row's
modulus. -/
theorem linFiniteMatrix_comp_mod {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (p : ℕ) (f g : linFiniteVec m →+ linFiniteVec m) (i k : Fin d) (hpi : p ∣ m i) :
    (linFiniteMatrix m (f.comp g) i k : ZMod p) =
      ∑ l, (linFiniteMatrix m f i l : ZMod p) * (linFiniteMatrix m g l k : ZMod p) := by
  rw [linFiniteMatrix_comp m hm, linNatModCast hpi]
  simp only [Nat.cast_sum, Nat.cast_mul]

/-- The identity on a retained cyclic coordinate reduces to the identity row. -/
theorem linFiniteMatrix_id_mod {d : ℕ} (m : Fin d → ℕ) (p : ℕ) (i k : Fin d)
    (hpi : p ∣ m i) :
    (linFiniteMatrix m (AddMonoidHom.id (linFiniteVec m)) i k : ZMod p) =
      if i = k then 1 else 0 := by
  classical
  by_cases hik : i = k
  · subst k
    simp only [linFiniteMatrix, AddMonoidHom.id_apply, linFiniteBasis, Pi.single_eq_same,
      if_pos rfl, ZMod.val_one_eq_one_mod]
    simpa only [Nat.cast_one, if_true] using linNatModCast hpi 1
  · simp [linFiniteMatrix, linFiniteBasis, Pi.single_apply, hik, Ne.symm hik]

def linPrimaryOrders {d : ℕ} (p : ℕ) (ν : Fin d → ℕ) : Fin d → ℕ := fun i => p ^ ν i

/-- A map from a smaller-exponent coordinate to a larger-exponent coordinate
has coefficient divisible by p. Such columns disappear on the retained layer. -/
theorem linPrimaryCoefficientDrop {d : ℕ} (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ)
    (f : linFiniteVec (linPrimaryOrders p ν) →+ linFiniteVec (linPrimaryOrders p ν))
    (i k : Fin d) (hik : ν k < ν i) :
    p ∣ linFiniteMatrix (linPrimaryOrders p ν) f i k := by
  have hpos : ∀ j, 0 < linPrimaryOrders p ν j := fun j => Nat.pow_pos hp
  have hc := linFiniteMatrix_compatible (linPrimaryOrders p ν) hpos f i k
  have hpow : p ^ (ν k + 1) ∣ p ^ ν i := Nat.pow_dvd_pow p (by omega)
  have hh : p ^ (ν k + 1) ∣
      linFiniteMatrix (linPrimaryOrders p ν) f i k * p ^ ν k := hpow.trans hc
  obtain ⟨a, ha⟩ := hh
  refine ⟨a, ?_⟩
  apply Nat.mul_left_cancel (Nat.pow_pos hp (n := ν k))
  calc p ^ ν k * linFiniteMatrix (linPrimaryOrders p ν) f i k =
      linFiniteMatrix (linPrimaryOrders p ν) f i k * p ^ ν k := by ring
    _ = p ^ (ν k + 1) * a := ha
    _ = p ^ ν k * (p * a) := by rw [pow_succ]; ring

end GI.Impl
