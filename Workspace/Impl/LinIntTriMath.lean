import Workspace.Impl.LinBackSub
import Workspace.Lang.Lib.LinIntTail

/-! Bit bounds for the recursive triangular algorithm. Each residual increases
its coordinate bit bound by at most B+1, with B a bound for the matrix entries.
This yields a uniform polynomial bound through all recursive language calls. -/
namespace GI.Impl
open GI.Cited GI.Lang

/-- The pivot test in the pure solver is exactly integer divisibility. -/
theorem linTriPivot_iff (x y : ℤ) : (x / y) * y = x ↔ y ∣ x := by
  constructor
  · intro h
    exact ⟨x / y, by rw [mul_comm]; exact h.symm⟩
  · exact Int.ediv_mul_cancel

/-- One substitution step increases the residual bit bound by at most B+1. -/
theorem linTriResidualBits {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (w : Fin (n + 1) → ℤ) (B C : ℕ) (hH : EntriesBits B H)
    (hw : ∀ i, (w i).natAbs < 2 ^ C) :
    ∀ j, (linResidual H w (w 0 / H 0 0) j).natAbs < 2 ^ (C + B + 1) := by
  intro j
  have hq : (w 0 / H 0 0).natAbs < 2 ^ C := (Int.natAbs_ediv_le_natAbs _ _).trans_lt (hw 0)
  have hm : ((w 0 / H 0 0) * H 0 j.succ).natAbs < 2 ^ C * 2 ^ B := by
    rw [Int.natAbs_mul]
    exact Nat.mul_lt_mul'' hq (hH 0 j.succ)
  have hws : (w j.succ).natAbs < 2 ^ C * 2 ^ B :=
    (hw j.succ).trans_le (Nat.le_mul_of_pos_right _ (by positivity))
  have hs := Int.natAbs_sub_le (w j.succ) ((w 0 / H 0 0) * H 0 j.succ)
  change (w j.succ - (w 0 / H 0 0) * H 0 j.succ).natAbs < _
  rw [pow_succ, pow_add]
  omega

/-- Every successful coefficient has polynomial bit length in the original dimensions
and input-entry bit bounds. No bound is obtained by iterating a running-time polynomial. -/
theorem linTriSolutionBits (n : ℕ) (H : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℤ)
    (B C : ℕ) (hH : EntriesBits B H) (hw : ∀ i, (w i).natAbs < 2 ^ C)
    (z : Fin n → ℤ) (hz : linUpperSolve n H w = some z) :
    ∀ i, (z i).natAbs < 2 ^ (C + n * (B + 1)) := by
  induction n generalizing B C with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    simp only [linUpperSolve] at hz
    split at hz
    next hp =>
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hz
      have htail := ih (linTail H) (linResidual H w (w 0 / H 0 0)) B (C + B + 1)
        (fun i j => hH i.succ j.succ) (linTriResidualBits H w B C hH hw) t ht
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change (w 0 / H 0 0).natAbs < _
        exact ((Int.natAbs_ediv_le_natAbs _ _).trans_lt (hw 0)).trans_le
          (Nat.pow_le_pow_right (by decide) (by omega))
      · change (t j).natAbs < _
        have he : C + B + 1 + n * (B + 1) = C + (n + 1) * (B + 1) := by ring
        simpa only [he] using htail j
    next hp => contradiction

/-- The encoded successful result has polynomial weight. -/
theorem linTriSolutionWt (n : ℕ) (H : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℤ)
    (B C : ℕ) (hH : EntriesBits B H) (hw : ∀ i, (w i).natAbs < 2 ^ C)
    (z : Fin n → ℤ) (hz : linUpperSolve n H w = some z) :
    (linVecVal z).wt ≤ linVectorAccWt n (20 * (C + n * (B + 1) + 1)) := by
  have hb := linTriSolutionBits n H w B C hH hw z hz
  have hwt := linWtList (vs := (List.finRange n).map fun i => encInt (z i))
    (B := 20 * (C + n * (B + 1) + 1)) (by
      intro v hv
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
      exact linWtInt (hb i))
  simpa [linVecVal, linVectorAccWt] using hwt

end GI.Impl
