import Workspace.Proved.SNFSize
import Workspace.Proved.SNFMath

/-!
# One bit bound for every state of the Smith form algorithm

`snf_all_bits`: if `SnfE E A` holds and `B` is at least `1 + t₀ (β + E) + n² (β + 2E)`, with
`t₀ = snfCount A` and `β = snfBeta E`, then every entry of every state, in both loops, has fewer
than `B` bits. It joins `snfIt_bits` (first loop) and `snfFix_bits` (second loop).
-/

namespace GI.Proved

open GI.Cited

variable {n : ℕ}

/-- The state after `k` steps of the second loop. -/
def snfRes' (A : _root_.Matrix (Fin n) (Fin n) ℤ) (k : ℕ) : SnfSt n := snfFix (snfIt A (snfCount A)) k

theorem snfRes'_succ (A : _root_.Matrix (Fin n) (Fin n) ℤ) (k : ℕ) :
    snfRes' A (k + 1) = snfFixK (snfRes' A k) k := rfl

theorem snfRes_eq (A : _root_.Matrix (Fin n) (Fin n) ℤ) : snfRes A = snfRes' A (n * n) := rfl

/-- The diagonal of every state of the second loop is positive. -/
theorem snfRes'_pos (hn : 0 < n) {A : _root_.Matrix (Fin n) (Fin n) ℤ} (hA : A.det ≠ 0) {k : ℕ}
    (hk : k ≤ n * n) : ∀ l, 0 < (snfRes' A k).H l l := by
  obtain ⟨-, -, -, hHf⟩ := snfIt_inv hn hA (snfCount A)
  have ht1 : 1 ≤ snfCount A := by unfold snfCount; omega
  have hD := snfIt_diag hn hA ht1 (snf_det_big hn A)
  have hpos : ∀ l, 0 < (snfIt A (snfCount A)).H l l := fun l => (hHf ht1).2.1 l l rfl
  exact (snfFix_inv hD hpos k hk).2.1

theorem snf_all_bits (hn : 0 < n) {A : _root_.Matrix (Fin n) (Fin n) ℤ} (hA : A.det ≠ 0) {E : ℕ}
    (hE : SnfE E A) {B : ℕ}
    (hB : 1 + snfCount A * (snfBeta E + E) + n * n * (snfBeta E + 2 * E) ≤ B) :
    (∀ t ≤ snfCount A, SnfBits B (snfIt A t).H ∧ SnfBits B (snfIt A t).P ∧
      SnfBits B (snfIt A t).Q) ∧
    (∀ k ≤ n * n, SnfBits B (snfRes' A k).H ∧ SnfBits B (snfRes' A k).P ∧
      SnfBits B (snfRes' A k).Q) := by
  set t₀ := snfCount A with ht₀
  have ht1 : 2 ≤ t₀ := by rw [ht₀]; unfold snfCount; omega
  have hβ := snf_le_beta E
  have hEt : E ≤ t₀ * (snfBeta E + E) := by
    have : 1 * (snfBeta E + E) ≤ t₀ * (snfBeta E + E) := Nat.mul_le_mul_right _ (by omega)
    omega
  refine ⟨fun t ht => ?_, fun k hk => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := snfIt_bits hn hA hE t
    have : t * (snfBeta E + E) ≤ t₀ * (snfBeta E + E) := Nat.mul_le_mul_right _ ht
    have k1 : E ≤ B := by omega
    have k2 : 1 + t * (snfBeta E + E) ≤ B := by omega
    exact ⟨snfBits_mono k1 h1, snfBits_mono k2 h2, snfBits_mono k2 h3⟩
  · obtain ⟨e, hP, hQ, hHf⟩ := snfIt_inv hn hA t₀
    have hX : snfX A t₀ = A := by unfold snfX; rw [if_pos (by rw [ht₀]; unfold snfCount; omega)]
    rw [hX] at e
    have hD := snfIt_diag hn hA (by omega) (snf_det_big hn A)
    have hpos : ∀ l, 0 < (snfIt A t₀).H l l := fun l => (hHf (by omega)).2.1 l l rfl
    obtain ⟨-, hPB, hQB⟩ := snfIt_bits hn hA hE t₀
    obtain ⟨h1, h2, h3⟩ := snfFix_bits hE.two_le hE.n_le e hP hQ hD hpos hE.det hPB hQB k hk
    have : k * (snfBeta E + 2 * E) ≤ n * n * (snfBeta E + 2 * E) := Nat.mul_le_mul_right _ hk
    have k1 : E ≤ B := by omega
    have k2 : 1 + t₀ * (snfBeta E + E) + k * (snfBeta E + 2 * E) ≤ B := by omega
    exact ⟨snfBits_mono k1 h1, snfBits_mono k2 h2, snfBits_mono k2 h3⟩

end GI.Proved
