import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Polynomial bounds in one variable

The own costs of the steps are sums and products of powers of the weights and of the cost
bounds of the cited algorithms. To compare them with the work allowed at a node, we bound each
of them by `C * X ^ D` for one variable `X ≥ 1` that dominates all the weights. `PB X a C D`
says `a ≤ C * X ^ D`; the lemmas below combine such bounds.
-/

namespace GI.Impl

/-- `a ≤ C * X ^ D`. -/
def PB (X a C D : ℕ) : Prop := a ≤ C * X ^ D

namespace PB

variable {X a b C D C' D' : ℕ}

theorem mono_le (h : PB X a C D) (hb : b ≤ a) : PB X b C D := hb.trans h

theorem const (c : ℕ) : PB X c c 0 := by simp [PB]

theorem var : PB X X 1 1 := by simp [PB]

/-- Raising the exponent, for `X ≥ 1`. -/
theorem lift (hX : 1 ≤ X) (h : PB X a C D) (hD : D ≤ D') : PB X a C D' :=
  h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX hD))

theorem add (hX : 1 ≤ X) (h : PB X a C D) (h' : PB X b C' D') :
    PB X (a + b) (C + C') (max D D') := by
  have h1 := lift hX h (le_max_left D D')
  have h2 := lift hX h' (le_max_right D D')
  unfold PB at *
  rw [Nat.add_mul]
  omega

theorem mul (h : PB X a C D) (h' : PB X b C' D') : PB X (a * b) (C * C') (D + D') := by
  unfold PB at *
  calc a * b ≤ (C * X ^ D) * (C' * X ^ D') := Nat.mul_le_mul h h'
    _ = C * C' * X ^ (D + D') := by ring

theorem pow (h : PB X a C D) (n : ℕ) : PB X (a ^ n) (C ^ n) (D * n) := by
  unfold PB at *
  calc a ^ n ≤ (C * X ^ D) ^ n := Nat.pow_le_pow_left h n
    _ = C ^ n * X ^ (D * n) := by rw [mul_pow, ← pow_mul]

theorem smul (c : ℕ) (h : PB X a C D) : PB X (c * a) (c * C) D := by
  unfold PB at *
  calc c * a ≤ c * (C * X ^ D) := Nat.mul_le_mul_left c h
    _ = c * C * X ^ D := by ring

theorem add_const (hX : 1 ≤ X) (h : PB X a C D) (c : ℕ) : PB X (a + c) (C + c) D := by
  have := add hX h (const (X := X) c)
  simpa using this

end PB

end GI.Impl


namespace GI.Impl

/-- **A uniform polynomial bound** of a function of `k, W, B`: there are `C` and `D` with
`f k W B ≤ C * (W + B + k + 2) ^ D` for all `k, W, B`. -/
def PBU (f : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∃ C D : ℕ, ∀ k W B, PB (W + B + k + 2) (f k W B) C D

namespace PBU

theorem one_le (k W B : ℕ) : 1 ≤ W + B + k + 2 := by omega

theorem const (c : ℕ) : PBU fun _ _ _ => c := ⟨c, 0, fun _ _ _ => PB.const c⟩

theorem k1 : PBU fun k _ _ => k + 1 :=
  ⟨1, 1, fun k W B => PB.mono_le PB.var (show k + 1 ≤ W + B + k + 2 by omega)⟩

theorem W : PBU fun _ W _ => W :=
  ⟨1, 1, fun k W B => PB.mono_le PB.var (show W ≤ W + B + k + 2 by omega)⟩

theorem B : PBU fun _ _ B => B :=
  ⟨1, 1, fun k W B => PB.mono_le PB.var (show B ≤ W + B + k + 2 by omega)⟩

theorem k : PBU fun k _ _ => k :=
  ⟨1, 1, fun k W B => PB.mono_le PB.var (show k ≤ W + B + k + 2 by omega)⟩

theorem add {f g : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) (hg : PBU g) :
    PBU fun k W B => f k W B + g k W B := by
  obtain ⟨C, D, h⟩ := hf
  obtain ⟨C', D', h'⟩ := hg
  exact ⟨_, _, fun k W B => PB.add (one_le k W B) (h k W B) (h' k W B)⟩

theorem mul {f g : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) (hg : PBU g) :
    PBU fun k W B => f k W B * g k W B := by
  obtain ⟨C, D, h⟩ := hf
  obtain ⟨C', D', h'⟩ := hg
  exact ⟨_, _, fun k W B => PB.mul (h k W B) (h' k W B)⟩

theorem pow {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) (n : ℕ) : PBU fun k W B => f k W B ^ n := by
  obtain ⟨C, D, h⟩ := hf
  exact ⟨_, _, fun k W B => PB.pow (h k W B) n⟩

theorem smul {f : ℕ → ℕ → ℕ → ℕ} (c : ℕ) (hf : PBU f) : PBU fun k W B => c * f k W B :=
  mul (const c) hf

theorem addc {f : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) (c : ℕ) : PBU fun k W B => f k W B + c :=
  add hf (const c)

theorem mono {f g : ℕ → ℕ → ℕ → ℕ} (hf : PBU f) (h : ∀ k W B, g k W B ≤ f k W B) : PBU g := by
  obtain ⟨C, D, h'⟩ := hf
  exact ⟨C, D, fun k W B => PB.mono_le (h' k W B) (h k W B)⟩

end PBU

end GI.Impl
