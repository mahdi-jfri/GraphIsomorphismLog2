module

public import Workspace.Impl.VsQTop

@[expose] public section

/-!
# Polynomial bounds

`VsPoly sz f`: the function `f a S` is at most `K (S + 1)^D` whenever the size `sz a` is at most
`S`, for some `K` and `D`. The bounds are closed under sums, products, powers and the substitution of
polynomials for `S`; the cost functions of the program are built from these.
-/

namespace GI.Impl

variable {α : Type} {sz : α → ℕ}

/-- `f a S ≤ K (S + 1)^D` for `sz a ≤ S`. -/
def VsPoly (sz : α → ℕ) (f : α → ℕ → ℕ) : Prop := ∃ K D : ℕ, ∀ n S, sz n ≤ S → f n S ≤ K * (S + 1) ^ D

theorem vsPoly_const (c : ℕ) : VsPoly sz fun _ _ => c := ⟨c, 0, fun _ _ _ => by simp⟩

theorem vsPoly_S : VsPoly sz fun _ S => S := ⟨1, 1, fun _ S _ => by simp⟩

theorem vsPoly_n : VsPoly sz fun n _ => sz n := ⟨1, 1, fun n S h => by simp; omega⟩

theorem vsPoly_mono {f g : α → ℕ → ℕ} (h : ∀ n S, sz n ≤ S → f n S ≤ g n S) (hg : VsPoly sz g) : VsPoly sz f := by
  obtain ⟨K, D, hK⟩ := hg
  exact ⟨K, D, fun n S hn => (h n S hn).trans (hK n S hn)⟩

theorem vsPoly_add {f g : α → ℕ → ℕ} (hf : VsPoly sz f) (hg : VsPoly sz g) : VsPoly sz fun n S => f n S + g n S := by
  obtain ⟨K₁, D₁, h₁⟩ := hf
  obtain ⟨K₂, D₂, h₂⟩ := hg
  refine ⟨K₁ + K₂, max D₁ D₂, fun n S hn => ?_⟩
  have e₁ : (S + 1) ^ D₁ ≤ (S + 1) ^ max D₁ D₂ := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have e₂ : (S + 1) ^ D₂ ≤ (S + 1) ^ max D₁ D₂ := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have := h₁ n S hn
  have := h₂ n S hn
  have := Nat.mul_le_mul_left K₁ e₁
  have := Nat.mul_le_mul_left K₂ e₂
  calc f n S + g n S ≤ K₁ * (S + 1) ^ max D₁ D₂ + K₂ * (S + 1) ^ max D₁ D₂ := by omega
    _ = (K₁ + K₂) * (S + 1) ^ max D₁ D₂ := by ring

theorem vsPoly_mul {f g : α → ℕ → ℕ} (hf : VsPoly sz f) (hg : VsPoly sz g) : VsPoly sz fun n S => f n S * g n S := by
  obtain ⟨K₁, D₁, h₁⟩ := hf
  obtain ⟨K₂, D₂, h₂⟩ := hg
  refine ⟨K₁ * K₂, D₁ + D₂, fun n S hn => ?_⟩
  calc f n S * g n S ≤ (K₁ * (S + 1) ^ D₁) * (K₂ * (S + 1) ^ D₂) := Nat.mul_le_mul (h₁ n S hn) (h₂ n S hn)
    _ = K₁ * K₂ * (S + 1) ^ (D₁ + D₂) := by ring

theorem vsPoly_pow {f : α → ℕ → ℕ} (hf : VsPoly sz f) (j : ℕ) : VsPoly sz fun n S => f n S ^ j := by
  obtain ⟨K, D, h⟩ := hf
  refine ⟨K ^ j, D * j, fun n S hn => ?_⟩
  calc f n S ^ j ≤ (K * (S + 1) ^ D) ^ j := Nat.pow_le_pow_left (h n S hn) j
    _ = K ^ j * (S + 1) ^ (D * j) := by rw [mul_pow, ← pow_mul]

theorem vsPoly_sub {f g : α → ℕ → ℕ} (hf : VsPoly sz f) : VsPoly sz fun n S => f n S - g n S :=
  vsPoly_mono (fun _ _ _ => Nat.sub_le _ _) hf

/-- Substitution of a polynomial `g n S ≥ S` for `S`. -/
theorem vsPoly_comp {f g : α → ℕ → ℕ} (hf : VsPoly sz f) (hg : VsPoly sz g) (hge : ∀ n S, sz n ≤ S → S ≤ g n S) :
    VsPoly sz fun n S => f n (g n S) := by
  obtain ⟨K, D, h⟩ := hf
  obtain ⟨K₂, D₂, h₂⟩ := hg
  refine ⟨K * (K₂ + 1) ^ D, D₂ * D, fun n S hn => ?_⟩
  have h1 := h n (g n S) (hn.trans (hge n S hn))
  have h2 : g n S + 1 ≤ (K₂ + 1) * (S + 1) ^ D₂ := by
    have := h₂ n S hn
    have : 1 ≤ (S + 1) ^ D₂ := Nat.one_le_pow _ _ (by omega)
    nlinarith
  calc f n (g n S) ≤ K * (g n S + 1) ^ D := h1
    _ ≤ K * ((K₂ + 1) * (S + 1) ^ D₂) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 D)
    _ = K * (K₂ + 1) ^ D * (S + 1) ^ (D₂ * D) := by rw [mul_pow, ← pow_mul]; ring

theorem vsPoly_of_le {f : α → ℕ → ℕ} {K D : ℕ} (h : ∀ n S, sz n ≤ S → f n S ≤ K * (S + 1) ^ D) : VsPoly sz f :=
  ⟨K, D, h⟩

/-- `S + 1`. -/
theorem vsPoly_S1 : VsPoly sz fun _ S => S + 1 := vsPoly_add vsPoly_S (vsPoly_const 1)

/-- Close `VsPoly (fun n S => e)` for `e` built from `n`, `S`, constants, `+`, `*`, `^`, `-`. -/
macro "vs_poly" : tactic => `(tactic| repeat' (first
  | with_reducible exact vsPoly_const _ | with_reducible apply vsPoly_add | with_reducible apply vsPoly_mul
  | with_reducible apply vsPoly_pow | with_reducible apply vsPoly_sub
  | with_reducible exact vsPoly_S | with_reducible exact vsPoly_n | with_reducible assumption))

example : VsPoly (fun n : ℕ => n) fun n S => vsQLCCost (S ^ 3 + n) S + 10 ^ 4 * (4 * S ^ 2 + 1) ^ 7 := by
  unfold vsQLCCost
  vs_poly

end GI.Impl
