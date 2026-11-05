module

public import Workspace.Proved.HNFSquare
public import Workspace.Proved.HNFBlock

@[expose] public section

/-!
# The Hermite form with transform of a matrix of full column rank

This file puts the pieces together as one pure function of the input matrix `A` and a bound
`T ≥ 1` on its entries.

1. Bareiss elimination (`hnfBarIter A c`) gives rows `s` and `d = det A[s,:] ≠ 0`.
2. `A' = [A | E]` (`hnfAp`) is nonsingular with `d ℤ^r` in its row lattice.
3. With `K = 2 r (r T)^r + 1`, the Hermite form of `[[A', I], [0, K I]]` gives `H'` and the
   transform `U'` (`hnfSquare_spec`). Here `(rT)^r` bounds the adjugate of `A'`.
4. The output is `U = U'` and `H` = the first `c` columns of `H'`.

The result used later is `hnfRect_spec`.
-/

namespace GI.Proved

open Matrix GI.Cited

variable {r c : ℕ}

/-- The modulus multiplier `K = 2 r (r T)^r + 1`. -/
def hnfK (r : ℕ) (T : ℤ) : ℤ := 2 * r * (r * T) ^ r + 1

/-- The transform. -/
def hnfRectU (A : Matrix (Fin r) (Fin c) ℤ) (T : ℤ) : Matrix (Fin r) (Fin r) ℤ :=
  hnfUp (hnfAp A (hnfBarIter A c).s) (hnfBarIter A c).d (hnfK r T)

/-- The Hermite form. -/
def hnfRectH (A : Matrix (Fin r) (Fin c) ℤ) (hcr : c ≤ r) (T : ℤ) : Matrix (Fin r) (Fin c) ℤ :=
  fun i j => hnfHp (hnfAp A (hnfBarIter A c).s) (hnfBarIter A c).d (hnfK r T) i (Fin.castLE hcr j)

theorem hnfColSel_full (y : Fin c) : hnfColSel c y c = id := by
  funext b
  simp [hnfColSel, b.isLt]

/-- The output of Bareiss elimination satisfies the hypotheses on the chosen rows. -/
theorem hnfBar_rows (A : Matrix (Fin r) (Fin c) ℤ) (hA : Function.Injective A.mulVec)
    (x : Fin r) (y : Fin c) :
    HnfRows A (hnfBarIter A c).s x ∧ (hnfB A (hnfBarIter A c).s x).det = (hnfBarIter A c).d := by
  obtain ⟨hlen, hlead, hd, -⟩ := hnfBarIter_spec A hA c le_rfl
  have hdet : (hnfB A (hnfBarIter A c).s x).det = (hnfBarIter A c).d := by
    rw [hlead x y]
    unfold hnfLead hnfMin hnfB
    rw [hlen, hnfColSel_full]
  refine ⟨⟨hlen, ?_, hdet ▸ hd⟩, hdet⟩
  rw [List.nodup_iff_injective_get]
  intro a b hab
  by_contra hne
  apply hd
  rw [← hdet]
  apply Matrix.det_zero_of_row_eq (i := ⟨a, by have := a.isLt; omega⟩)
    (j := ⟨b, by have := b.isLt; omega⟩)
  · intro e; exact hne (Fin.ext (by simpa using congrArg Fin.val e))
  · funext l
    simp only [hnfB, submatrix_apply, hnfRowSel, id]
    rw [List.getD_eq_getElem _ _ a.isLt, List.getD_eq_getElem _ _ b.isLt]
    simpa using congrArg (fun i => A i l) hab

/-- The hypotheses of `hnfSquare_spec` hold for `A' = [A | E]`, `d` and `K`. -/
theorem hnfRect_sq (A : Matrix (Fin r) (Fin c) ℤ) (hA : Function.Injective A.mulVec)
    (hc : 0 < c) (hcr : c ≤ r) {T : ℤ} (hT1 : 1 ≤ T) :
    HnfSq (hnfAp A (hnfBarIter A c).s) (hnfBarIter A c).d (hnfK r T) := by
  obtain ⟨hrows, hdet⟩ := hnfBar_rows A hA ⟨0, by omega⟩ ⟨0, hc⟩
  refine ⟨hnfAp_det_ne hrows, hdet ▸ hrows.det_ne, fun j => hdet ▸ hnfAp_single_mem hrows j, ?_⟩
  unfold hnfK; positivity

/-- **The Hermite form with transform.** For `A` of full column rank and `T ≥ 1` bounding its
entries: `U` is unimodular, `U A = H`, `H` is in Hermite form, `|U| < K` and `0 ≤ H ≤ |d| K`, where
`|d| ≤ c! T^c`. -/
theorem hnfRect_spec (A : Matrix (Fin r) (Fin c) ℤ) (hA : Function.Injective A.mulVec)
    (hc : 0 < c) (hcr : c ≤ r) {T : ℤ} (hT1 : 1 ≤ T) (hT : ∀ i j, |A i j| ≤ T) :
    IsUnit (hnfRectU A T).det ∧ hnfRectU A T * A = hnfRectH A hcr T ∧
      IsHermiteForm (hnfRectH A hcr T) ∧ (∀ i j, |hnfRectU A T i j| < hnfK r T) ∧
      (∀ i j, 0 ≤ hnfRectH A hcr T i j ∧
        hnfRectH A hcr T i j ≤ |(hnfBarIter A c).d| * hnfK r T) ∧
      |(hnfBarIter A c).d| ≤ c.factorial * T ^ c := by
  set x : Fin r := ⟨0, by omega⟩
  set y : Fin c := ⟨0, hc⟩
  obtain ⟨hrows, hdet⟩ := hnfBar_rows A hA x y
  set s := (hnfBarIter A c).s
  set d := (hnfBarIter A c).d
  have hsq : HnfSq (hnfAp A s) d (hnfK r T) := by
    refine ⟨hnfAp_det_ne hrows, hdet ▸ hrows.det_ne, fun j => hdet ▸ hnfAp_single_mem hrows j, ?_⟩
    unfold hnfK; positivity
  have hT' : ∀ i j, |hnfAp A s i j| ≤ T := by
    intro i j
    simp only [hnfAp]
    split_ifs
    · exact hT _ _
    · simpa using hT1
    · simpa using (zero_le_one.trans hT1)
  have hQ : ∀ i j, |(hnfAp A s).adjugate i j| ≤ (r * T) ^ r := by
    intro i j
    refine (hnf_adjugate_le hT1 hT' i j).trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le_pow r)
      (pow_nonneg (zero_le_one.trans hT1) _)
  have hK : 2 * (r * (r * T) ^ r) < hnfK r T := by unfold hnfK; linarith
  obtain ⟨hmul, hunit, hherm, hU, hH⟩ := hnfSquare_spec hsq hQ hK
  refine ⟨hunit, ?_, ?_, hU, fun i j => hH i _, ?_⟩
  · ext i j
    have := congrFun (congrFun hmul i) (Fin.castLE hcr j)
    rw [Matrix.mul_apply] at this ⊢
    rw [hnfRectH, ← this]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hnfAp, Fin.coe_castLE, j.isLt, dite_true]
    rfl
  · refine ⟨fun i j hij => hherm.1 _ _ (by simpa using hij), fun i j hij => hherm.2.1 _ _
      (by simpa using hij), fun i j i' hij hi' => hherm.2.2 _ _ _ (by simpa using hij)
      (by simpa using hi')⟩
  · obtain ⟨hlen, hlead, -, -⟩ := hnfBarIter_spec A hA c le_rfl
    have := hnfMin_abs_le A hT (s.length) s x (s.length) y
    have h2 := hlead x y
    simp only [hnfLead] at h2
    rw [← h2, hlen] at this
    exact this

end GI.Proved
