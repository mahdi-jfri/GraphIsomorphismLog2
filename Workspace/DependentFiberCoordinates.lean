import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic

namespace GI.CartesianCover

variable {I : Type*} [DecidableEq I] {F : I → Type*}

/-- Actual transport between possibly different coordinate types. A background
tuple supplies representatives; the bijection laws follow from the real inverse. -/
def betweenFibers (background : ∀ i, F i) (h : Equiv.Perm (∀ i, F i)) (i j : I)
    (forward : ∀ x y : ∀ k, F k, x i = y i → h x j = h y j)
    (backward : ∀ x y : ∀ k, F k, x j = y j → h.symm x i = h.symm y i) : F i ≃ F j where
  toFun d := h (Function.update background i d) j
  invFun d := h.symm (Function.update background j d) i
  left_inv d := by
    calc
      h.symm (Function.update background j (h (Function.update background i d) j)) i =
          h.symm (h (Function.update background i d)) i := backward _ _ (by simp)
      _ = d := by rw [h.symm_apply_apply]; simp
  right_inv d := by
    calc
      h (Function.update background i (h.symm (Function.update background j d) i)) j =
          h (h.symm (Function.update background j d)) j := forward _ _ (by simp)
      _ = d := by rw [h.apply_symm_apply]; simp

theorem betweenFibers_apply (background : ∀ i, F i) (h : Equiv.Perm (∀ i, F i)) (i j : I)
    (forward : ∀ x y : ∀ k, F k, x i = y i → h x j = h y j)
    (backward : ∀ x y : ∀ k, F k, x j = y j → h.symm x i = h.symm y i)
    (x : ∀ i, F i) : betweenFibers background h i j forward backward (x i) = h x j :=
  forward _ _ (by simp)

end GI.CartesianCover

#print axioms GI.CartesianCover.betweenFibers
#print axioms GI.CartesianCover.betweenFibers_apply
