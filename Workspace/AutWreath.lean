import Workspace.WreathValuation
import Mathlib.GroupTheory.SemidirectProduct

/-!
# The wreath product `Aut(T) wr Sym(s)`

The abstract group in `eq:budget-diagonal-degree` of the paper. The symmetric
group permutes the `s` coordinates of `Aut(T)^s`.
-/

namespace GI

/-- `Sym(s)` acts on `Aut(T)^s` by permuting coordinates: `σ · x = x ∘ σ⁻¹`. -/
def wreathPermAction (T : Type*) [Group T] (s : ℕ) :
    Equiv.Perm (Fin s) →* MulAut (Fin s → MulAut T) where
  toFun σ := MulEquiv.arrowCongr σ (MulEquiv.refl _)
  map_one' := by ext x i; rfl
  map_mul' σ τ := by ext x i; rfl

/-- The wreath product `Aut(T) wr Sym(s)`, as the semidirect product
`Aut(T)^s ⋊ Sym(s)` with coordinate permutation. -/
abbrev AutWreath (T : Type*) [Group T] (s : ℕ) :=
  (Fin s → MulAut T) ⋊[wreathPermAction T s] Equiv.Perm (Fin s)

theorem card_autWreath (T : Type*) [Group T] [Finite T] (s : ℕ) :
    Nat.card (AutWreath T s) = Nat.card (MulAut T) ^ s * s.factorial := by
  rw [Nat.card_congr (SemidirectProduct.equivProd), Nat.card_prod, Nat.card_pi,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_perm,
    Nat.card_eq_fintype_card (α := Fin s), Fintype.card_fin]

end GI
