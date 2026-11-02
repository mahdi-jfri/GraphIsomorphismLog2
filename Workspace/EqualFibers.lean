import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

namespace GI

variable {G V W : Type*} [Group G] [MulAction G V] [MulAction G W]

/-- Actual fiber transport by a group element, rather than an equal-size assumption. -/
def equivariantFiberEquiv (f : V → W) (equivariant : ∀ (g : G) (v : V), f (g • v) = g • f v)
    (g : G) (w : W) : {v // f v = w} ≃ {v // f v = g • w} where
  toFun v := ⟨g • v.1, by rw [equivariant, v.2]⟩
  invFun v := ⟨g⁻¹ • v.1, by rw [equivariant, v.2, inv_smul_smul]⟩
  left_inv v := by apply Subtype.ext; exact inv_smul_smul g v.1
  right_inv v := by apply Subtype.ext; exact smul_inv_smul g v.1

theorem equivariant_fiber_card_eq (f : V → W)
    (equivariant : ∀ (g : G) (v : V), f (g • v) = g • f v)
    (transitive : ∀ w z : W, ∃ g : G, g • w = z) (w z : W) :
    Nat.card {v // f v = w} = Nat.card {v // f v = z} := by
  obtain ⟨g, rfl⟩ := transitive w z
  exact Nat.card_congr (equivariantFiberEquiv f equivariant g w)

theorem equivariant_quotient_transitive (f : V → W) (onto : Function.Surjective f)
    (equivariant : ∀ (g : G) (v : V), f (g • v) = g • f v)
    (transitive : ∀ u v : V, ∃ g : G, g • u = v) :
    ∀ w z : W, ∃ g : G, g • w = z := by
  intro w z
  obtain ⟨u, rfl⟩ := onto w
  obtain ⟨v, rfl⟩ := onto z
  obtain ⟨g, hg⟩ := transitive u v
  exact ⟨g, by rw [← equivariant, hg]⟩

variable [Fintype V] [Fintype W]

theorem equal_fiber_card_factorization (f : V → W)
    (equivariant : ∀ (g : G) (v : V), f (g • v) = g • f v)
    (transitive : ∀ w z : W, ∃ g : G, g • w = z) (w : W) :
    Nat.card W * Nat.card {v // f v = w} = Nat.card V := by
  classical
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Fintype.card_sigma] at h
  have hc : ∀ z, Fintype.card {v // f v = z} = Fintype.card {v // f v = w} := by
    intro z
    simpa only [← Nat.card_eq_fintype_card] using
      equivariant_fiber_card_eq f equivariant transitive z w
  simp_rw [hc] at h
  simpa using h

def fiberSubsetEquiv (f : V → W) (B : Set W) :
    {v // f v ∈ B} ≃ Σ w : B, {v // f v = w.1} where
  toFun v := ⟨⟨f v.1, v.2⟩, ⟨v.1, rfl⟩⟩
  invFun z := ⟨z.2.1, by rw [z.2.2]; exact z.1.2⟩
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨⟨w, hw⟩, ⟨v, hv⟩⟩
    cases hv
    rfl

/-- Every union of quotient fibers has its exact expected physical cardinality. -/
theorem equal_fiber_subset_count (f : V → W)
    (equivariant : ∀ (g : G) (v : V), f (g • v) = g • f v)
    (transitive : ∀ w z : W, ∃ g : G, g • w = z) (w : W) (B : Set W) :
    Nat.card {v // f v ∈ B} = Nat.card B * Nat.card {v // f v = w} := by
  classical
  have h := Fintype.card_congr (fiberSubsetEquiv f B)
  rw [Fintype.card_sigma] at h
  have hc : ∀ z : B, Fintype.card {v // f v = z.1} = Fintype.card {v // f v = w} := by
    intro z
    simpa only [← Nat.card_eq_fintype_card] using
      equivariant_fiber_card_eq f equivariant transitive z.1 w
  simp_rw [hc] at h
  simpa using h

end GI
