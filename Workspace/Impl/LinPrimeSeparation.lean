module

public import Workspace.Impl.LinTrialPrimary

@[expose] public section

/-! Bounded primary projections jointly detect zero. The bound on the
prime divisors is precisely the one available for the paper's quotients. -/
namespace GI.Impl

theorem linPrimeSplit_exponent {d p : ℕ} {m : Fin d → ℕ}
    (D : linPrimeSplitData m p) (hp : p.Prime) (hm : ∀ i, 0 < m i) (i : Fin d) :
    D.exponent i = (m i).factorization p := by
  have hco : D.cofactor i ≠ 0 := by
    have hh := D.factor i
    intro he
    rw [he, Nat.mul_zero] at hh
    exact (Nat.ne_of_gt (hm i)) hh
  have hnd := hp.coprime_iff_not_dvd.mp (D.coprime i)
  have he := congrArg (fun n => n.factorization p) (D.factor i)
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hco] at he
  simpa [Nat.factorization_pow_self hp, hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd hnd] using he.symm

theorem linPrimeProjection_all_zero {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (bound : ℕ) (hbound : ∀ i p, p.Prime → p ∣ m i → p ≤ bound)
    (x : linFiniteVec m)
    (hx : ∀ p (hp : p.Prime), p ≤ bound →
      linPrimeProjection (linTrialPrimaryData m p hp hm) x = 0) : x = 0 := by
  apply funext
  intro i
  haveI : NeZero (m i) := ⟨Nat.ne_of_gt (hm i)⟩
  apply ZMod.val_injective
  have hd : m i ∣ (x i).val := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro p k hp hpk
    by_cases hk : k = 0
    · simp [hk]
    have hpm : p ∣ m i := (dvd_pow_self p hk).trans hpk
    have he := hx p hp (hbound i p hp hpm)
    have hd := (linFiniteProjection_kernel m _ _ hm x).mp he i
    have hν := linPrimeSplit_exponent (linTrialPrimaryData m p hp hm) hp hm i
    change p ^ (linTrialPrimaryData m p hp hm).exponent i ∣ (x i).val at hd
    rw [hν] at hd
    exact (Nat.pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt (hm i))).mp hpk)).trans hd
  have hz : (x i).val = 0 := by
    haveI : NeZero (m i) := ⟨Nat.ne_of_gt (hm i)⟩
    exact Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt (x i))
  simpa only [Pi.zero_apply, ZMod.val_zero] using hz

end GI.Impl
