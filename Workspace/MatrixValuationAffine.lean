module

public import Workspace.MatrixValuationBounds
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.TypeTags.Finite

@[expose] public section

namespace GI.MatrixValuation

variable (F : Type*) [Field F] (d : ℕ)

/-- The actual linear transformation induced by an invertible matrix. -/
def matrixLinearEquiv : GL (Fin d) F ≃* ((Fin d → F) ≃ₗ[F] (Fin d → F)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin d → F))

/-- The natural action of invertible matrices on vector translations. -/
def translationAction : GL (Fin d) F →* MulAut (Multiplicative (Fin d → F)) where
  toFun g := AddEquiv.toMultiplicative (matrixLinearEquiv F d g).toAddEquiv
  map_one' := by
    ext v : 1
    change Multiplicative.ofAdd ((matrixLinearEquiv F d 1) v.toAdd) = v
    rw [map_one]
    rfl
  map_mul' g h := by
    ext v : 1
    change Multiplicative.ofAdd ((matrixLinearEquiv F d (g * h)) v.toAdd) =
      Multiplicative.ofAdd ((matrixLinearEquiv F d g) ((matrixLinearEquiv F d h) v.toAdd))
    rw [map_mul]
    rfl

/-- The concrete affine group of vector translations and invertible matrices. -/
abbrev AffineGroup := Multiplicative (Fin d → F) ⋊[translationAction F d] GL (Fin d) F

instance [Fintype F] : Finite (AffineGroup F d) :=
  Finite.of_equiv (Multiplicative (Fin d → F) × GL (Fin d) F)
    SemidirectProduct.equivProd.symm

theorem translationAction_apply (g : GL (Fin d) F) (v : Fin d → F) :
    (translationAction F d g (Multiplicative.ofAdd v)).toAdd =
      Matrix.mulVec (g : Matrix (Fin d) (Fin d) F) v := by
  rfl

theorem affineGroup_card [Fintype F] :
    Nat.card (AffineGroup F d) = (Fintype.card F) ^ d * Nat.card (GL (Fin d) F) := by
  rw [SemidirectProduct.card, Nat.card_congr Multiplicative.toAdd,
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]

theorem affineGroup_valuation [Fintype F] {p : ℕ} [hp : Fact p.Prime]
    (hpq : ¬p ∣ Fintype.card F) :
    padicValNat p (Nat.card (AffineGroup F d)) =
      padicValNat p (Nat.card (GL (Fin d) F)) := by
  rw [affineGroup_card, padicValNat.mul
    (pow_ne_zero _ (Nat.ne_of_gt Fintype.card_pos)) (Nat.ne_of_gt Nat.card_pos),
    padicValNat.pow,
    padicValNat.eq_zero_of_not_dvd hpq]
  simp

theorem exists_prime_nondividing_card [Fintype F] :
    ∃ p : ℕ, (p = 3 ∨ p = 5) ∧ ¬p ∣ Fintype.card F := by
  obtain ⟨r, _, n, hr, hcard⟩ := FiniteField.card' F
  by_cases h3 : 3 ∣ Fintype.card F
  · refine ⟨5, Or.inr rfl, ?_⟩
    rw [hcard] at h3 ⊢
    have hr3 : r = 3 := (hr.dvd_iff_eq (by decide : 3 ≠ 1)).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    rw [hr3]
    intro h5
    have hd : 5 ∣ 3 := (by decide : Nat.Prime 5).dvd_of_dvd_pow h5
    norm_num at hd
  · exact ⟨3, Or.inl rfl, h3⟩

/-- The affine case of the order-valuation estimate, for every actual
subgroup of the affine semidirect group. Classification into this case
is a separate theorem. -/
theorem affine_subgroup_uniform_bound [Fintype F]
    (H : Subgroup (AffineGroup F d)) :
    ∃ p : ℕ, (p = 3 ∨ p = 5) ∧
      6 * (padicValNat p (Nat.card H) : ℝ) ≤
        (12 / Real.log 2) * Real.log ((Fintype.card F : ℝ) ^ d) := by
  obtain ⟨p, hp, hpq⟩ := exists_prime_nondividing_card F
  haveI : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> decide⟩
  refine ⟨p, hp, ?_⟩
  have hm := GI.primeValuation_mono (p := p)
    (Nat.ne_of_gt (Nat.card_pos (α := AffineGroup F d))) (Subgroup.card_subgroup_dvd_card H)
  rw [affineGroup_valuation F d hpq] at hm
  have hmReal : (padicValNat p (Nat.card H) : ℝ) ≤
      padicValNat p (Nat.card (GL (Fin d) F)) := by exact_mod_cast hm
  have hb := generalLinearGroup_uniform_bound (F := F) hp hpq d
  linarith

end GI.MatrixValuation
