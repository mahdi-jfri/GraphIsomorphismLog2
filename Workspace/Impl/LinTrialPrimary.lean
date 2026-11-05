module

public import Workspace.Impl.LinPrimeSplit
public import Workspace.Impl.LinNatPower
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

/-! Trial division needs only a number of divisions bounded by the bit length
of the cyclic order. No integer factorization primitive is used. -/
namespace GI.Impl
open GI.Machine

def linTrialPrimary (p n : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, n)
  | k + 1 =>
    let z := linTrialPrimary p n k
    if p ∣ z.2 then (z.1 + 1, z.2 / p) else z

theorem linTrialPrimary_invariant (p n : ℕ) (hp : 2 ≤ p) (hn : 0 < n) (k : ℕ) :
    let z := linTrialPrimary p n k
    n = p ^ z.1 * z.2 ∧ 0 < z.2 ∧ z.1 ≤ k ∧ (p ∣ z.2 → z.1 = k) := by
  induction k with
  | zero => simp [linTrialPrimary, hn]
  | succ k ih =>
    dsimp only at ih ⊢
    rcases ih with ⟨hfac, hpos, hle, hfull⟩
    simp only [linTrialPrimary]
    split_ifs with hd
    · have hprod : p * ((linTrialPrimary p n k).2 / p) = (linTrialPrimary p n k).2 :=
        Nat.mul_div_cancel' hd
      have hdivpos : 0 < (linTrialPrimary p n k).2 / p :=
        Nat.div_pos (Nat.le_of_dvd hpos hd) (by omega)
      refine ⟨?_, hdivpos, by omega, fun _ => by simp [hfull hd]⟩
      rw [pow_succ, Nat.mul_assoc, hprod]
      exact hfac
    · exact ⟨hfac, hpos, by omega, fun hd' => (hd hd').elim⟩

theorem linTrialPrimary_terminal (p n : ℕ) (hp : p.Prime) (hn : 0 < n) :
    let z := linTrialPrimary p n (len n)
    n = p ^ z.1 * z.2 ∧ p.Coprime z.2 ∧ z.1 ≤ len n := by
  obtain ⟨hfac, hpos, hle, hfull⟩ := linTrialPrimary_invariant p n hp.two_le hn (len n)
  have hnd : ¬p ∣ (linTrialPrimary p n (len n)).2 := by
    intro hd
    have he := hfull hd
    have hpow := Nat.pow_le_pow_left hp.two_le (len n)
    have hnlt := (len_le_iff.mp (le_refl (len n)))
    have hmul : p ^ (len n) ≤ p ^ (len n) * (linTrialPrimary p n (len n)).2 :=
      Nat.le_mul_of_pos_right _ hpos
    rw [he] at hfac
    omega
  exact ⟨hfac, (hp.coprime_iff_not_dvd.mpr hnd), hle⟩

def linTrialPrimaryData {d : ℕ} (m : Fin d → ℕ) (p : ℕ) (hp : p.Prime)
    (hm : ∀ i, 0 < m i) : linPrimeSplitData m p where
  exponent i := (linTrialPrimary p (m i) (len (m i))).1
  cofactor i := (linTrialPrimary p (m i) (len (m i))).2
  factor i := (linTrialPrimary_terminal p (m i) hp (hm i)).1
  coprime i := (linTrialPrimary_terminal p (m i) hp (hm i)).2.1

end GI.Impl
