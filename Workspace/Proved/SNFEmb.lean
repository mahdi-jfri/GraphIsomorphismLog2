module

public import Workspace.Proved.SNFAlt

@[expose] public section

/-!
# A `2 × 2` block inside the identity (Smith form)

`snfEmb p q α β γ δ` is the identity matrix with the block `[[α, β], [γ, δ]]` on rows and
columns `p, q`. Multiplying by it on the left combines rows `p, q` (`snfEmb_left`), on the right
it combines columns `p, q` (`snfEmb_right`). Products of two such matrices multiply the blocks,
so a block of determinant `1` gives a unimodular matrix (`snfEmb_isUnit`). With `p = q = n`
(outside the range) it is the identity (`snfEmb_out`).
-/

namespace GI.Proved

open _root_.Matrix

variable {n : ℕ}

/-- The identity with the block `[[α, β], [γ, δ]]` on rows and columns `p, q`. -/
def snfEmb (p q : ℕ) (α β γ δ : ℤ) : _root_.Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if (i : ℕ) = p then (if (j : ℕ) = p then α else if (j : ℕ) = q then β else 0)
  else if (i : ℕ) = q then (if (j : ℕ) = p then γ else if (j : ℕ) = q then δ else 0)
  else if i = j then 1 else 0

theorem snfEmb_out (α β γ δ : ℤ) : (snfEmb n n α β γ δ : _root_.Matrix (Fin n) (Fin n) ℤ) = 1 := by
  ext i j
  have hi : (i : ℕ) ≠ n := by omega
  simp [snfEmb, if_neg hi, one_apply]

theorem snf_val_ne {p c : Fin n} (h : c ≠ p) : (c : ℕ) ≠ p := fun e => h (Fin.ext e)

/-- **Row operations.** -/
theorem snfEmb_left {p q : Fin n} (hpq : p ≠ q) (α β γ δ : ℤ) (M : _root_.Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin n) :
    (snfEmb (n := n) p q α β γ δ * M) i j =
      if i = p then α * M p j + β * M q j
      else if i = q then γ * M p j + δ * M q j else M i j := by
  have hpq' : (p : ℕ) ≠ q := snf_val_ne hpq
  rw [mul_apply]
  by_cases hip : i = p
  · subst hip
    rw [if_pos rfl, Finset.sum_eq_add i q hpq]
    · simp [snfEmb, if_neg (Ne.symm hpq')]
    · intro c _ hc
      simp [snfEmb, if_neg (snf_val_ne hc.1), if_neg (snf_val_ne hc.2), zero_mul]
    · simp
    · simp
  by_cases hiq : i = q
  · subst hiq
    rw [if_neg hip, Finset.sum_eq_add p i hpq]
    · simp [snfEmb, if_neg (snf_val_ne hip), if_neg hpq']
    · intro c _ hc
      simp [snfEmb, if_neg (snf_val_ne hip), if_neg (snf_val_ne hc.1),
        if_neg (snf_val_ne hc.2), zero_mul]
    · simp
    · simp
  rw [if_neg hip, if_neg hiq, Finset.sum_eq_single i]
  · simp [snfEmb, if_neg (snf_val_ne hip), if_neg (snf_val_ne hiq), one_mul]
  · intro c _ hc
    simp [snfEmb, if_neg (snf_val_ne hip), if_neg (snf_val_ne hiq), if_neg (Ne.symm hc),
      zero_mul]
  · simp

/-- **Column operations.** -/
theorem snfEmb_right {p q : Fin n} (hpq : p ≠ q) (α β γ δ : ℤ) (M : _root_.Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin n) :
    (M * snfEmb (n := n) p q α β γ δ) i j =
      if j = p then M i p * α + M i q * γ
      else if j = q then M i p * β + M i q * δ else M i j := by
  have hpq' : (p : ℕ) ≠ q := snf_val_ne hpq
  rw [mul_apply]
  by_cases hjp : j = p
  · subst hjp
    rw [if_pos rfl, Finset.sum_eq_add j q hpq]
    · simp [snfEmb, if_neg (Ne.symm hpq')]
    · intro c _ hc
      simp [snfEmb, if_neg (snf_val_ne hc.1), if_neg (snf_val_ne hc.2), if_neg (Ne.symm hc.1),
        mul_zero, hc.1, hc.2]
    · simp
    · simp
  by_cases hjq : j = q
  · subst hjq
    rw [if_neg hjp, Finset.sum_eq_add p j hpq]
    · simp [snfEmb, if_neg hpq', if_neg (snf_val_ne hjp)]
    · intro c _ hc
      simp [snfEmb, if_neg (snf_val_ne hc.1), if_neg (snf_val_ne hc.2), if_neg (Ne.symm hc.2),
        mul_zero, hc.1, hc.2]
    · simp
    · simp
  rw [if_neg hjp, if_neg hjq, Finset.sum_eq_single j]
  · simp [snfEmb, if_neg (snf_val_ne hjp), if_neg (snf_val_ne hjq), mul_one]
  · intro c _ hc
    by_cases hcp : c = p
    · subst hcp; simp [snfEmb, if_neg (snf_val_ne hjp), if_neg (snf_val_ne hjq),
        mul_zero]
    by_cases hcq : c = q
    · subst hcq; simp [snfEmb, if_neg (snf_val_ne hcp), if_neg (snf_val_ne hjp),
        if_neg (snf_val_ne hjq), mul_zero]
    simp [snfEmb, if_neg (snf_val_ne hcp), if_neg (snf_val_ne hcq), if_neg hc, mul_zero]
  · simp

/-- **Products of blocks.** -/
theorem snfEmb_mul {p q : Fin n} (hpq : p ≠ q) (α β γ δ α' β' γ' δ' : ℤ) :
    (snfEmb p q α β γ δ * snfEmb p q α' β' γ' δ' : _root_.Matrix (Fin n) (Fin n) ℤ) =
      snfEmb p q (α * α' + β * γ') (α * β' + β * δ') (γ * α' + δ * γ') (γ * β' + δ * δ') := by
  have hpq' : (p : ℕ) ≠ q := snf_val_ne hpq
  ext i j
  rw [snfEmb_left hpq]
  by_cases hip : i = p
  · subst hip
    simp [snfEmb, if_neg (Ne.symm hpq')]
    split_ifs <;> ring
  by_cases hiq : i = q
  · subst hiq
    simp [if_neg hip, snfEmb, if_neg (Ne.symm hpq'), if_neg (snf_val_ne hip)]
    split_ifs <;> ring
  simp [if_neg hip, if_neg hiq, snfEmb, if_neg (snf_val_ne hip), if_neg (snf_val_ne hiq)]

/-- **A block of determinant one gives a unimodular matrix.** -/
theorem snfEmb_isUnit {p q : Fin n} (hpq : p ≠ q) {α β γ δ : ℤ} (h : α * δ - β * γ = 1) :
    IsUnit (snfEmb p q α β γ δ : _root_.Matrix (Fin n) (Fin n) ℤ).det := by
  have e := snfEmb_mul (n := n) hpq α β γ δ δ (-β) (-γ) α
  have e1 : α * δ + β * -γ = 1 := by linarith
  have e2 : α * -β + β * α = 0 := by ring
  have e3 : γ * δ + δ * -γ = 0 := by ring
  have e4 : γ * -β + δ * α = 1 := by linarith
  rw [e1, e2, e3, e4] at e
  have hone : (snfEmb p q 1 0 0 1 : _root_.Matrix (Fin n) (Fin n) ℤ) = 1 := by
    ext i j
    have h1 := snfEmb_left (n := n) hpq 1 0 0 1 1 i j
    rw [Matrix.mul_one] at h1
    rw [h1]
    split_ifs with h2 h3 <;> subst_vars <;> simp
  rw [hone] at e
  have hd := congrArg det e
  rw [det_mul, det_one] at hd
  exact IsUnit.of_mul_eq_one _ hd

end GI.Proved
