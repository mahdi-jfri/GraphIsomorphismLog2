module

public import Workspace.Impl.LinObjectQuotient
public import Workspace.Impl.LinFiniteCoordinates
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Prime.Factorial

@[expose] public section

/-! The size of `W` may exceed the size of `A/N`, but its exponent does
not. Thus the primary loop still only needs primes at most the cover degree. -/
namespace GI.Impl

theorem linObjectQuotient_annihilated {ι Q : Type*} [AddCommGroup Q]
    (B : ι → Submodule ℤ Q) (q : ℕ) (hq : ∀ a : Q, q • a = 0)
    (x : (∀ i, Q ⧸ B i) ⧸ LinearMap.range (linObjectDiagonal B)) : q • x = 0 := by
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ x
  have hw : q • w = 0 := by
    ext i
    obtain ⟨a, ha⟩ := Submodule.mkQ_surjective (B i) (w i)
    change q • w i = 0
    rw [← ha, ← map_nsmul, hq a, map_zero]
  rw [← map_nsmul, hw, map_zero]

theorem linObjectModulus_dvd_annihilator {V : Type*} [AddCommGroup V]
    {d : ℕ} (m : Fin d → ℕ) (e : V ≃+ linFiniteVec m) (q : ℕ)
    (hq : ∀ x : V, q • x = 0) (i : Fin d) : m i ∣ q := by
  classical
  have hh := congrArg e (hq (e.symm (linFiniteBasis m i)))
  rw [map_nsmul, e.apply_symm_apply, map_zero] at hh
  have hi := congrFun hh i
  have hz : (q : ZMod (m i)) = 0 := by
    simpa [linFiniteBasis, nsmul_eq_mul] using hi
  exact (ZMod.natCast_eq_zero_iff _ _).mp hz

theorem linObjectQuotient_prime_bound {ι Q : Type*} [AddCommGroup Q]
    (B : ι → Submodule ℤ Q) {d n q : ℕ} (m : Fin d → ℕ)
    (e : ((∀ i, Q ⧸ B i) ⧸ LinearMap.range (linObjectDiagonal B)) ≃+ linFiniteVec m)
    (hq : ∀ a : Q, q • a = 0) (hqn : q ∣ n.factorial)
    (i : Fin d) (p : ℕ) (hp : p.Prime) (hpi : p ∣ m i) : p ≤ n := by
  have hmi := linObjectModulus_dvd_annihilator m e q
    (linObjectQuotient_annihilated B q hq) i
  exact hp.dvd_factorial.mp (hpi.trans (hmi.trans hqn))

end GI.Impl
