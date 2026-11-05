/-
Basic facts about the machine of `Workspace.Statement.Machine` and the input layout of
`Workspace.Statement.Main`, used by the proof.
-/
module

public import Workspace.Statement.Main
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace GI.Machine

theorem len_zero : len 0 = 0 := rfl

/-- `len v` is the number of binary digits of `v`. -/
theorem len_spec {v : ℕ} (hv : v ≠ 0) : 2 ^ (len v - 1) ≤ v ∧ v < 2 ^ len v := by
  simp only [len, hv, if_false, Nat.add_sub_cancel]
  exact ⟨Nat.log2_self_le hv, Nat.lt_log2_self⟩

/-- Extra fuel never changes the result of a run that finishes. -/
theorem exec_fuel_mono {p : Program} {fuel fuel' : ℕ} {s : Stmt} {st : State}
    {res : Outcome × State × ℕ} (h : exec p fuel s st = some res) (hle : fuel ≤ fuel') :
    exec p fuel' s st = some res := by
  induction fuel generalizing fuel' s st res with
  | zero => simp [exec] at h
  | succ f ih =>
    obtain ⟨f', rfl⟩ : ∃ f', fuel' = f' + 1 := ⟨fuel' - 1, by omega⟩
    have hf : f ≤ f' := by omega
    cases s with
    | nop => simpa [exec] using h
    | assign r e => simpa [exec] using h
    | store a e => simpa [exec] using h
    | ret e => simpa [exec] using h
    | seq s t =>
      simp only [exec] at h ⊢
      cases h1 : exec p f s st with
      | none => simp [h1] at h
      | some r1 =>
        rw [ih h1 hf]
        rw [h1] at h
        obtain ⟨o, st', c⟩ := r1
        cases o with
        | returned v => exact h
        | normal =>
          simp only at h ⊢
          cases h2 : exec p f t st' with
          | none => simp [h2] at h
          | some r2 => rw [ih h2 hf]; rw [h2] at h; exact h
    | cond e s t =>
      simp only [exec] at h ⊢
      cases h1 : exec p f (if (evalExpr st e).1 = 0 then t else s) st with
      | none => simp [h1] at h
      | some r1 => rw [ih h1 hf]; rw [h1] at h; exact h
    | loop e body =>
      simp only [exec] at h ⊢
      split_ifs at h ⊢ with hv
      · exact h
      · cases h1 : exec p f body st with
        | none => simp [h1] at h
        | some r1 =>
          rw [ih h1 hf]
          rw [h1] at h
          obtain ⟨o, st', c⟩ := r1
          cases o with
          | returned w => exact h
          | normal =>
            simp only at h ⊢
            cases h2 : exec p f (.loop e body) st' with
            | none => simp [h2] at h
            | some r2 => rw [ih h2 hf]; rw [h2] at h; exact h
    | call r g args =>
      simp only [exec] at h ⊢
      cases hb : p.procs[g]? with
      | none => simp [hb] at h
      | some body =>
        rw [hb] at h
        simp only at h ⊢
        cases h1 : exec p f body
            { mem := st.mem, regs := fun i => (evalArgs st args).1.getD i 0 } with
        | none => rw [h1] at h; simp at h
        | some r1 => rw [ih h1 hf]; rw [h1] at h; exact h


end GI.Machine

namespace GI.Statement

variable {n : ℕ}

/-- The cell `n * i + j` determines the pair `(i, j)`. -/
theorem cell_div {i j : ℕ} (hj : j < n) : (n * i + j) / n = i := by
  have hn : 0 < n := by omega
  rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hj, Nat.add_zero]

theorem cell_mod {i j : ℕ} (hj : j < n) : (n * i + j) % n = j := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

theorem cell_lt {i j : ℕ} (hi : i < n) (hj : j < n) : n * i + j < n * n := by
  have : n * i + n ≤ n * n := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left n hi
  omega

theorem cell_inj {i j i' j' : Fin n} (h : n * (i : ℕ) + j = n * i' + j') : i = i' ∧ j = j' := by
  have hdiv := congrArg (· / n) h
  have hmod := congrArg (· % n) h
  simp only [cell_div j.isLt, cell_div j'.isLt] at hdiv
  simp only [cell_mod j.isLt, cell_mod j'.isLt] at hmod
  exact ⟨Fin.ext hdiv, Fin.ext hmod⟩

open Classical in
/-- The value that a cell of an adjacency matrix should hold, if `a` is `n * i + j`. -/
noncomputable def adjCell (G : SimpleGraph (Fin n)) (a : ℕ) : ℕ :=
  if ∃ i j : Fin n, a = n * i + j ∧ G.Adj i j then 1 else 0

open Classical in
theorem adjCell_eq (G : SimpleGraph (Fin n)) (i j : Fin n) :
    adjCell G (n * i + j) = if G.Adj i j then 1 else 0 := by
  unfold adjCell
  by_cases hadj : G.Adj i j
  · rw [if_pos ⟨i, j, rfl, hadj⟩, if_pos hadj]
  · rw [if_neg hadj, if_neg]
    rintro ⟨i', j', heq, hadj'⟩
    obtain ⟨rfl, rfl⟩ := cell_inj heq
    exact hadj hadj'

/-- A memory with the input layout exists, so the main statement is not vacuous. -/
theorem inputLayout_exists (G H : SimpleGraph (Fin n)) : ∃ mem, InputLayout G H mem := by
  have h2 : 2 * n * n = n * n + n * n := by ring
  refine ⟨fun a => if a = 0 then n else if a ≤ n * n then adjCell G (a - 1)
    else if a ≤ 2 * n * n then adjCell H (a - 1 - n * n) else 0, ?_, ?_, ?_, ?_⟩
  · simp
  · intro i j
    have hlt := cell_lt i.isLt j.isLt
    simp only [show 1 + n * i + j ≠ 0 by omega, if_false,
      show 1 + n * i + j ≤ n * n by omega, if_true,
      show 1 + n * i + j - 1 = n * i + j by omega]
    exact adjCell_eq G i j
  · intro i j
    have hlt := cell_lt i.isLt j.isLt
    simp only [show 1 + n * n + n * i + j ≠ 0 by omega, if_false,
      show ¬ 1 + n * n + n * i + j ≤ n * n by omega,
      show 1 + n * n + n * i + j ≤ 2 * n * n by omega, if_true,
      show 1 + n * n + n * i + j - 1 - n * n = n * i + j by omega]
    exact adjCell_eq H i j
  · intro a ha
    simp only [show a ≠ 0 by omega, if_false, show ¬ a ≤ n * n by omega,
      show ¬ a ≤ 2 * n * n by omega]

/-- The input layout fixes every cell, so `∀ mem, InputLayout G H mem → …` speaks about exactly
one memory. -/
theorem inputLayout_unique {G H : SimpleGraph (Fin n)} {m₁ m₂ : ℕ → ℕ}
    (h₁ : InputLayout G H m₁) (h₂ : InputLayout G H m₂) : m₁ = m₂ := by
  have h2 : 2 * n * n = n * n + n * n := by ring
  funext a
  by_cases ha0 : a = 0
  · rw [ha0, h₁.size, h₂.size]
  by_cases hbig : 2 * n * n < a
  · rw [h₁.rest a hbig, h₂.rest a hbig]
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; omega
    · exact hn
  -- Write the position of `a` inside its matrix as `n * i + j`.
  have decompose : ∀ b, b < n * n → ∃ i j : Fin n, b = n * i + j := by
    intro b hb
    refine ⟨⟨b / n, (Nat.div_lt_iff_lt_mul hn).mpr (by rwa [Nat.mul_comm] at hb)⟩,
      ⟨b % n, Nat.mod_lt b hn⟩, ?_⟩
    exact (Nat.div_add_mod b n).symm
  by_cases hleft : a ≤ n * n
  · obtain ⟨i, j, hij⟩ := decompose (a - 1) (by omega)
    have ha : a = 1 + n * i + j := by omega
    rw [ha, h₁.left, h₂.left]
  · obtain ⟨i, j, hij⟩ := decompose (a - 1 - n * n) (by omega)
    have ha : a = 1 + n * n + n * i + j := by omega
    rw [ha, h₁.right, h₂.right]

end GI.Statement
