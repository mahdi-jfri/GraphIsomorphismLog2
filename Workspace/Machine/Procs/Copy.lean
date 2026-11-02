/-
Copying a block of memory.

`copyBody` takes the source address in register 0, the target address in register 1 and the
number of cells in register 2, and copies the cells forward, using register 3 as the counter.
`wp_copy` gives its effect and cost.
-/
import Workspace.Machine.Layout

namespace GI.Machine

/-- Copy `L` cells from `src` to `dst`: registers 0, 1, 2 hold `src`, `dst`, `L`. -/
def copyBody : Stmt :=
  Stmt.forUp 3 2 (.store (.reg 1 + .reg 3) (.load (.reg 0 + .reg 3)))

/-- Copying `L` cells from `src` to `dst` forward. The copy is correct when `dst ≤ src` or the
blocks do not overlap. All addresses and the copied values must be at most `M`. Only the target
block and register 3 change. -/
theorem wp_copy {p : Program} {st : State} {src dst L M : ℕ}
    (h0 : st.regs 0 = src) (h1 : st.regs 1 = dst) (h2 : st.regs 2 = L)
    (hdisj : dst ≤ src ∨ src + L ≤ dst)
    (hM : src + L ≤ M) (hM' : dst + L ≤ M) (hv : ∀ i < L, st.mem (src + i) ≤ M) :
    WP p copyBody st (fun o st' c => o = .normal ∧
      (∀ i < L, st'.mem (dst + i) = st.mem (src + i)) ∧
      (∀ x, x < dst ∨ dst + L ≤ x → st'.mem x = st.mem x) ∧
      (∀ r, r ≠ 3 → st'.regs r = st.regs r) ∧
      c ≤ 30 * (L + 1) * (len M + 1)) := by
  refine (WP.frame_regs (Q := fun o st' c => o = .normal ∧
      (∀ i < L, st'.mem (dst + i) = st.mem (src + i)) ∧
      (∀ x, x < dst ∨ dst + L ≤ x → st'.mem x = st.mem x) ∧
      c ≤ 30 * (L + 1) * (len M + 1)) ?_).mono ?_
  · let I : ℕ → State → Prop := fun k st' =>
      st'.regs 0 = src ∧ st'.regs 1 = dst ∧ st'.regs 2 = L ∧
      (∀ i < k, st'.mem (dst + i) = st.mem (src + i)) ∧
      (∀ x, x < dst ∨ dst + k ≤ x → st'.mem x = st.mem x)
    refine WP.forUp_const (by decide) (by decide) (by decide) I (8 * (2 * len M + 1)) ?_ ?_ ?_ ?_
    · rintro k st' v ⟨a0, a1, a2, a3, a4⟩
      exact ⟨by simpa using a0, by simpa using a1, by simpa using a2, a3, a4⟩
    · exact ⟨h0, h1, h2, fun i hi => absurd hi (Nat.not_lt_zero _), fun x _ => rfl⟩
    · rintro k st' hk ⟨a0, a1, a2, a3, a4⟩ hik _
      rw [h2] at hk
      have hread : st'.mem (src + k) = st.mem (src + k) := a4 _ (by omega)
      have hvk := hv k hk
      refine WP.store_le (M := M) ?_ ?_ ?_ ?_ ?_
      · simp only [machine_simps, a1, hik]; omega
      · simp only [machine_simps, a0, hik, hread]; omega
      · simp only [machine_simps, a1, hik]; omega
      · simp only [machine_simps, a0,
          hik, hread]; omega
      · intro c hc
        simp only [Expr.add_eq, Expr.size_bin, Expr.size_reg, Expr.size_load] at hc
        refine ⟨rfl, ⟨a0, a1, a2, ?_, ?_⟩, by omega⟩
        · intro i hi
          simp only [machine_simps, a0,
            a1, hik, hread, Function.update_apply]
          split_ifs with h
          · rw [show i = k by omega]
          · exact a3 i (by omega)
        · intro x hx
          simp only [machine_simps, a0,
            a1, hik, hread, Function.update_apply]
          rw [if_neg (by omega)]; exact a4 x (by omega)
    · rintro st' c ⟨a0, a1, a2, a3, a4⟩ _ _ hc
      rw [h2] at a3 a4 hc
      refine ⟨rfl, a3, a4, ?_⟩
      have hl : len L ≤ len M := len_mono (by omega)
      have hLM : L * len L ≤ L * len M := Nat.mul_le_mul_left _ hl
      nlinarith
  · rintro o st' c ⟨⟨rfl, a1, a2, a3⟩, hr⟩
    refine ⟨rfl, a1, a2, fun r hr3 => hr r ?_, a3⟩
    simp [copyBody, Stmt.Writes, hr3]

end GI.Machine
