module

public import Workspace.Impl.SCosSolve1
public import Workspace.Impl.SCosTop5
public import Workspace.Impl.SCosPaste1

@[expose] public section

/-!
# From the transitive step to the task

`scos_reduction_of_big`: if the transitive step with at least two points meets
`ScosBigHyp` with an own cost `OG n` bounded by a polynomial, the program solves
`SolvableCosetIntersectionTask` in polynomial time. The node bound is
`Q n = scosOwnE n + scosOwnN n + scosOwnB hps n + OG n + scosOwnC n c`, every call costs at most
`scosBnd (Q n) c n` (`scos_solve_all`, `scosT_le_bnd`), and this is a polynomial in `n`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

/-- A monomial bound with a smaller exponent gives one with a larger exponent. -/
theorem scos_mono_pow {a A E D n : ℕ} (h : a ≤ A * (n + 1) ^ E) (hED : E ≤ D) :
    a ≤ A * (n + 1) ^ D :=
  h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hED))

theorem scosBnd_mono_k (Q c : ℕ) {k k' : ℕ} (h : k ≤ k') : scosBnd Q c k ≤ scosBnd Q c k' := by
  unfold scosBnd
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.pow_le_pow_left h _) 1)

theorem scosBnd_poly {Q c n A E : ℕ} (hQ : Q ≤ A * (n + 1) ^ E) :
    scosBnd Q c n ≤ (4 * A) * (n + 1) ^ (E + (2 * c + 4)) := by
  unfold scosBnd
  have h1 : n ^ (2 * c + 4) + 1 ≤ 2 * (n + 1) ^ (2 * c + 4) := by
    have := Nat.pow_le_pow_left (show n ≤ n + 1 by omega) (2 * c + 4)
    have : 1 ≤ (n + 1) ^ (2 * c + 4) := Nat.one_le_pow _ _ (by omega)
    omega
  calc 2 * Q * (n ^ (2 * c + 4) + 1) ≤ 2 * (A * (n + 1) ^ E) * (2 * (n + 1) ^ (2 * c + 4)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hQ) h1
    _ = (4 * A) * (n + 1) ^ (E + (2 * c + 4)) := by rw [pow_add]; ring

section Red

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

/-- **The reduction, given the transitive step.** -/
theorem scos_reduction_of_big (OG : ℕ → ℕ) (KG DG : ℕ) (hOG : ∀ n, OG n ≤ KG * (n + 1) ^ DG)
    (hG : ∀ n, ScosBigHyp c hps hpre hmb n (OG n) (scosOwnC n c)) :
    SolvableCosetIntersection := by
  let Q : ℕ → ℕ := fun n => scosOwnE n + scosOwnN n + scosOwnB hps n + OG n + scosOwnC n c
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = 35 + (72 + 6 * (pointwiseStabPrim hps).k) + DG + (2 * c + 12) + 21 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = 10 ^ 21 + 10 ^ 33 +
    (10 ^ 6 * (10 ^ 16 * (10 ^ 5) ^ 6) ^ 2 + (pointwiseStabPrim hps).c * 3000002 ^ (pointwiseStabPrim hps).k) +
    KG + 100000000 * 4 ^ (c + 7) := ⟨_, rfl⟩
  have hQ : ∀ n, Q n ≤ A * (n + 1) ^ D := by
    intro n
    have e1 := scos_mono_pow (D := D) (scosOwnE_le n) (by omega)
    have e2 := scos_mono_pow (D := D) (scosOwnN_le n) (by omega)
    have e3 := scos_mono_pow (D := D) (scosOwnB_le hps n) (by omega)
    have e4 := scos_mono_pow (D := D) (hOG n) (by omega)
    have e5 := scos_mono_pow (D := D) (scosOwnC_le n c) (by omega)
    have : A * (n + 1) ^ D = 10 ^ 21 * (n + 1) ^ D + 10 ^ 33 * (n + 1) ^ D +
        (10 ^ 6 * (10 ^ 16 * (10 ^ 5) ^ 6) ^ 2 + (pointwiseStabPrim hps).c * 3000002 ^ (pointwiseStabPrim hps).k) * (n + 1) ^ D +
        KG * (n + 1) ^ D + 100000000 * 4 ^ (c + 7) * (n + 1) ^ D := by
      rw [hA]; ring
    simp only [Q]
    generalize (n + 1) ^ D = Y at *
    generalize 10 ^ 6 * (10 ^ 16 * (10 ^ 5) ^ 6) ^ 2 + (pointwiseStabPrim hps).c * 3000002 ^ (pointwiseStabPrim hps).k = B3 at *
    generalize 100000000 * 4 ^ (c + 7) = B5 at *
    omega
  refine scos_solvableCosetIntersection_of (c := c) (hps := hps) (hpre := hpre) (hmb := hmb)
    (F := fun n => scosBnd (Q n) c n) (K := 4 * A) (D := D + (2 * c + 4))
    (fun n => scosBnd_poly (hQ n)) fun n v 𝒢 x Φ hv => ?_
  have hq : ScosQ hps n (Q n) (OG n) (scosOwnC n c) :=
    { e := by simp only [Q]; omega
      b := by simp only [Q]; omega
      g := by simp only [Q]; omega
      ch := by simp only [Q]; omega
      nn := by simp only [Q]; omega }
  refine (scos_solve_all hq (hG n) Φ.card v 𝒢 x Φ rfl hv).mono fun w cost h => ⟨h.1, ?_⟩
  have hcard : Φ.card ≤ n := by simpa using Finset.card_le_univ Φ
  exact (h.2.trans (scosT_le_bnd _ _ _ _)).trans (scosBnd_mono_k _ _ hcard)

end Red

end GI.Impl
