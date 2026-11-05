module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic

@[expose] public section

/-! The p-power filtration used after the Smith decomposition of A.20.
The transition lemma is the reason each layer has characteristic p. -/
namespace GI.Impl

variable {V : Type*} [AddCommGroup V]

/-- The subgroup p^j V, represented as an integer submodule. -/
def linPowerLayer (p j : ℕ) : Submodule ℤ V :=
  LinearMap.range ((p ^ j : ℤ) • (LinearMap.id : V →ₗ[ℤ] V))

theorem linPowerLayer_mem (p j : ℕ) (x : V) :
    x ∈ linPowerLayer (V := V) p j ↔ ∃ y : V, (p ^ j : ℤ) • y = x := by
  rfl

@[simp] theorem linPowerLayer_zero (p : ℕ) : linPowerLayer (V := V) p 0 = ⊤ := by
  ext x
  simp [linPowerLayer_mem]

/-- Every next layer is contained in the preceding one. -/
theorem linPowerLayer_succ_le (p j : ℕ) :
    linPowerLayer (V := V) p (j + 1) ≤ linPowerLayer p j := by
  intro x hx
  obtain ⟨y, rfl⟩ := (linPowerLayer_mem p (j + 1) x).mp hx
  apply (linPowerLayer_mem p j _).mpr
  exact ⟨(p : ℤ) • y, by simp [pow_succ, mul_smul]⟩

/-- Multiplication by p sends a layer into its next layer. Thus it acts as zero
on the quotient of these two layers. -/
theorem linPowerLayer_mul_mem (p j : ℕ) {x : V} (hx : x ∈ linPowerLayer (V := V) p j) :
    (p : ℤ) • x ∈ linPowerLayer (V := V) p (j + 1) := by
  obtain ⟨y, rfl⟩ := (linPowerLayer_mem p j x).mp hx
  apply (linPowerLayer_mem p (j + 1) _).mpr
  exact ⟨y, by simp [pow_succ, smul_smul, mul_comm]⟩

/-- The filtration terminates when the primary exponent annihilates V. -/
theorem linPowerLayer_eq_bot (p j : ℕ) (h : ∀ x : V, (p ^ j : ℤ) • x = 0) :
    linPowerLayer (V := V) p j = ⊥ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := (linPowerLayer_mem p j x).mp hx
    simpa only [Submodule.mem_bot] using h y
  · exact bot_le

/-- Every linear transformation preserves every layer; no choice of generators
or elementary divisors is involved in this invariance. -/
theorem linPowerLayer_map (p j : ℕ) (f : V →ₗ[ℤ] V) {x : V}
    (hx : x ∈ linPowerLayer (V := V) p j) : f x ∈ linPowerLayer (V := V) p j := by
  obtain ⟨y, rfl⟩ := (linPowerLayer_mem p j x).mp hx
  exact (linPowerLayer_mem p j _).mpr ⟨f y, (f.map_smul _ _).symm⟩

end GI.Impl
