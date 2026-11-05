module

public import Workspace.Impl.LinSolve

@[expose] public section

/-! Exact integer substitution for the upper triangular Hermite block.
A row equation is solved from the first column onward. A failed pivot division
means that no integer solution exists. This is a pure algorithm, not a cited task. -/
namespace GI.Impl
open Matrix

/-- The trailing square block. -/
def linTail {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) :
    Matrix (Fin n) (Fin n) ℤ := fun i j => M i.succ j.succ

/-- Remove the contribution of the first row. -/
def linResidual {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (w : Fin (n + 1) → ℤ) (a : ℤ) : Fin n → ℤ := fun j => w j.succ - a * M 0 j.succ

/-- The first equation fixes the first coefficient. The other equations form a smaller system. -/
theorem linUpperEquation {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (hz : ∀ i : Fin n, M i.succ 0 = 0) (w : Fin (n + 1) → ℤ)
    (a : ℤ) (z : Fin n → ℤ) :
    (Fin.cons a z) ᵥ* M = w ↔
      a * M 0 0 = w 0 ∧ z ᵥ* linTail M = linResidual M w a := by
  have hh : ((Fin.cons a z) ᵥ* M) 0 = a * M 0 0 := by
    simp [vecMul, dotProduct, Fin.sum_univ_succ, hz]
  have ht (j : Fin n) : ((Fin.cons a z) ᵥ* M) j.succ =
      a * M 0 j.succ + (z ᵥ* linTail M) j := by
    simp [vecMul, dotProduct, Fin.sum_univ_succ, linTail]
  constructor
  · intro h
    constructor
    · simpa only [hh] using congrFun h 0
    · funext j
      have hj := congrFun h j.succ
      rw [ht] at hj
      change _ = w j.succ - a * M 0 j.succ
      omega
  · rintro ⟨h0, hs⟩
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact hh.trans h0
    · rw [ht]
      have hi := congrFun hs i
      change (z ᵥ* linTail M) i = w i.succ - a * M 0 i.succ at hi
      omega

/-- Exact integer pivot division, followed by substitution in the trailing block. -/
def linUpperSolve : (n : ℕ) → Matrix (Fin n) (Fin n) ℤ → (Fin n → ℤ) → Option (Fin n → ℤ)
  | 0, _, _ => some Fin.elim0
  | n + 1, M, w =>
    let a := w 0 / M 0 0
    if a * M 0 0 = w 0 then
      (linUpperSolve n (linTail M) (linResidual M w a)).map (Fin.cons a)
    else none

/-- Every returned vector solves the original integer equation. -/
theorem linUpperSolve_sound (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ)
    (htri : ∀ i j, j < i → M i j = 0) (w z : Fin n → ℤ)
    (h : linUpperSolve n M w = some z) : z ᵥ* M = w := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [linUpperSolve] at h
    split at h
    next hp =>
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨t, ht, rfl⟩ := h
      apply (linUpperEquation M (fun i => htri i.succ 0 (by simp)) w _ t).mpr
      refine ⟨hp, ?_⟩
      exact ih (linTail M) (fun i j hj => htri i.succ j.succ (by simpa using hj)) _ t ht
    next hp => contradiction

/-- If an integer solution exists, pivot division succeeds at every step. -/
theorem linUpperSolve_complete (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ)
    (htri : ∀ i j, j < i → M i j = 0) (hdiag : ∀ i, M i i ≠ 0)
    (w z : Fin n → ℤ) (h : z ᵥ* M = w) : linUpperSolve n M w = some z := by
  induction n with
  | zero =>
    change some Fin.elim0 = some z
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    have hz : z = Fin.cons (z 0) (fun i : Fin n => z i.succ) := by
      ext i
      refine Fin.cases rfl (fun _ => rfl) i
    rw [hz] at h ⊢
    obtain ⟨h0, ht⟩ := (linUpperEquation M (fun i => htri i.succ 0 (by simp)) w _ _).mp h
    have ha : w 0 / M 0 0 = z 0 := by
      rw [← h0]
      exact Int.mul_ediv_cancel _ (hdiag 0)
    simp only [linUpperSolve, ha, h0, ↓reduceIte]
    rw [ih (linTail M) (fun i j hj => htri i.succ j.succ (by simpa using hj))
      (fun i => hdiag i.succ) _ _ ht]
    rfl

/-- Failure is equivalent to insolubility over the integers. -/
theorem linUpperSolve_none_iff (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ)
    (htri : ∀ i j, j < i → M i j = 0) (hdiag : ∀ i, M i i ≠ 0) (w : Fin n → ℤ) :
    linUpperSolve n M w = none ↔ ¬ ∃ z, z ᵥ* M = w := by
  constructor
  · rintro hn ⟨z, hz⟩
    rw [linUpperSolve_complete n M htri hdiag w z hz] at hn
    contradiction
  · intro hn
    cases he : linUpperSolve n M w with
    | none => rfl
    | some z => exact (hn ⟨z, linUpperSolve_sound n M htri w z he⟩).elim

end GI.Impl
