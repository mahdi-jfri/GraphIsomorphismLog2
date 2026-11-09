module

public import Workspace.Degree.OrderBound
public import Workspace.RadicalFreeOrder

/-!
# The order of a radical-free group in the class

Let `Q` be a finite group with no solvable normal subgroup except `1`, and let `T_1, …, T_b` be the
simple factors of its socle. If `Q` is in `Γ̂_D` then `|Q| ≤ D^b ∏ |Aut T_i|`
(`GI.Degree.card_le_of_radicalFree`): `Q` acts faithfully on the socle, the image of `Q` in `Sym(b)`
is a quotient of `Q`, so `GI.Degree.card_le_pow` bounds it, and the kernel embeds in `∏ Aut T_i`.
-/

@[expose] public section

namespace GI.Degree

open GI.RadicalSocle GI.SocleOuter GI.RadicalFreeOrder

variable {Q : Type} [Group Q] [Finite Q]

/-- The number of factors. -/
abbrev Factors (Q : Type) [Group Q] := MinimalNormals (socle Q)

theorem card_ker_factorAction_le [Fintype (Factors Q)]
    (rf : ∀ N : Subgroup Q, N.Normal → IsSolvable N → N = ⊥) :
    Nat.card (factorAction (G := Q)).ker ≤ ∏ N : Factors Q, Nat.card (MulAut N.val) := by
  have rfE := normal_subgroup_radicalFree rf (socle Q)
  rw [← Nat.card_pi]
  refine Nat.card_le_card_of_injective
    (fun k => (factorKernelEquiv rfE socle_idempotent) (kernelToFactorKernel k)) fun a b hab => ?_
  have h1 := (factorKernelEquiv rfE socle_idempotent).injective hab
  have h2 := congrArg Subtype.val h1
  exact Subtype.ext (socleConjugation_injective rf h2)

/-- `|Q| ≤ D^b ∏ |Aut T_i|`. -/
theorem card_le_of_radicalFree [Fintype (Factors Q)]
    (rf : ∀ N : Subgroup Q, N.Normal → IsSolvable N → N = ⊥) {D : ℕ} (hD : 6 ≤ D)
    (hQ : GammaHat D Q) :
    Nat.card Q ≤ D ^ Nat.card (Factors Q) * ∏ N : Factors Q, Nat.card (MulAut N.val) := by
  set φ := factorAction (G := Q)
  have hrange : Nat.card φ.range ≤ D ^ Nat.card (Factors Q) := by
    by_cases he : IsEmpty (Factors Q)
    · have : Subsingleton (Equiv.Perm (Factors Q)) := inferInstance
      have : Subsingleton φ.range := inferInstance
      simp
    · have : Nonempty (Factors Q) := not_isEmpty_iff.mp he
      have h := card_le_pow hD φ.range (hQ.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)
      exact h.trans (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))
  have hcard : Nat.card Q = Nat.card φ.range * Nat.card φ.ker := by
    rw [← Subgroup.index_ker, mul_comm, Subgroup.card_mul_index]
  rw [hcard]
  exact Nat.mul_le_mul hrange (card_ker_factorAction_le rf)

end GI.Degree
