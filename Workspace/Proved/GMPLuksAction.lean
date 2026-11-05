module

public import Workspace.Proved.GMPCosetAction
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section

/-!
# The second kernel in Luks's normal-subgroup centralizer construction

An automorphism preserving a point stabilizer acts on its cosets. We
use every point as a base point, rather than one per orbit. The sum of
the resulting coset spaces has at most the square of the original
degree, which is still polynomial. If all these coset actions are
trivial, the automorphism fixes the original faithful action pointwise.
-/

namespace GI.Proved

variable {N K : Type*} [Group N] [Group K]

def gmpAutCosetMap (S : Subgroup N) (e : MulAut N)
    (he : S ≤ S.comap e.toMonoidHom) : N ⧸ S → N ⧸ S :=
  Quotient.map' e (by
    intro x y hxy
    apply QuotientGroup.leftRel_apply.mpr
    have h := he (QuotientGroup.leftRel_apply.mp hxy)
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv] using h)

/-- Automorphisms preserving a subgroup act on its coset space.
The subgroup need not be normal. -/
def gmpAutCosetAction (S : Subgroup N) (φ : K →* MulAut N)
    (hφ : ∀ k, S ≤ S.comap (φ k).toMonoidHom) : K →* Equiv.Perm (N ⧸ S) where
  toFun k :=
    { toFun := gmpAutCosetMap S (φ k) (hφ k)
      invFun := gmpAutCosetMap S (φ k⁻¹) (hφ k⁻¹)
      left_inv := by
        intro q
        refine Quotient.inductionOn q (fun x => ?_)
        change (Quotient.mk'' (φ k⁻¹ (φ k x)) : N ⧸ S) = Quotient.mk'' x
        simp only [map_inv, MulAut.inv_apply_self]
      right_inv := by
        intro q
        refine Quotient.inductionOn q (fun x => ?_)
        change (Quotient.mk'' (φ k (φ k⁻¹ x)) : N ⧸ S) = Quotient.mk'' x
        simp only [map_inv, MulAut.apply_inv_self] }
  map_one' := by
    apply Equiv.ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    change (Quotient.mk'' (φ 1 x) : N ⧸ S) = Quotient.mk'' x
    rw [map_one]
    rfl
  map_mul' k l := by
    apply Equiv.ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    change (Quotient.mk'' (φ (k * l) x) : N ⧸ S) = Quotient.mk'' (φ k (φ l x))
    rw [map_mul]
    rfl

variable {V : Type*} [MulAction N V]

/-- A trivial coset action fixes every orbit point of the base point. -/
theorem gmpAutCosetAction_mem_ker (φ : K →* MulAut N) (a : V)
    (hφ : ∀ k, MulAction.stabilizer N a ≤
      (MulAction.stabilizer N a).comap (φ k).toMonoidHom) (k : K) :
    k ∈ (gmpAutCosetAction (MulAction.stabilizer N a) φ hφ).ker ↔
      ∀ x : N, φ k x • a = x • a := by
  constructor
  · intro hk x
    have he := congrArg (fun p : Equiv.Perm (N ⧸ MulAction.stabilizer N a) =>
      p (Quotient.mk'' x)) hk
    change (Quotient.mk'' (φ k x) : N ⧸ MulAction.stabilizer N a) = Quotient.mk'' x at he
    have h := QuotientGroup.leftRel_apply.mp (Quotient.exact he)
    change ((φ k x)⁻¹ * x) • a = a at h
    rw [mul_smul] at h
    exact ((inv_smul_eq_iff).mp h).symm
  · intro hk
    apply Equiv.ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    change (Quotient.mk'' (φ k x) : N ⧸ MulAction.stabilizer N a) = Quotient.mk'' x
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    change ((φ k x)⁻¹ * x) • a = a
    rw [mul_smul, ← hk x, inv_smul_smul]

/-- Luks's second action, using all original points as base points. -/
def gmpLuksSecondAction (φ : K →* MulAut N)
    (hφ : ∀ k (a : V), MulAction.stabilizer N a ≤
      (MulAction.stabilizer N a).comap (φ k).toMonoidHom) :
    K →* Equiv.Perm (Σ a : V, N ⧸ MulAction.stabilizer N a) :=
  (Equiv.Perm.sigmaCongrRightHom (fun a : V => N ⧸ MulAction.stabilizer N a)).comp
    (MonoidHom.pi (fun a : V => gmpAutCosetAction (MulAction.stabilizer N a) φ (fun k => hφ k a)))

/-- Its kernel consists exactly of the trivial automorphisms. For
conjugation automorphisms, this is the required centralizer. -/
theorem gmpLuksSecondAction_ker [FaithfulSMul N V] (φ : K →* MulAut N)
    (hφ : ∀ k (a : V), MulAction.stabilizer N a ≤
      (MulAction.stabilizer N a).comap (φ k).toMonoidHom) :
    (gmpLuksSecondAction φ hφ).ker = φ.ker := by
  ext k
  constructor
  · intro hk
    apply MulEquiv.ext
    intro x
    apply eq_of_smul_eq_smul (α := V)
    intro a
    change φ k x • a = x • a
    have hka : k ∈ (gmpAutCosetAction (MulAction.stabilizer N a) φ (fun k => hφ k a)).ker := by
      apply Equiv.ext
      intro q
      have he := congrArg (fun p : Equiv.Perm (Σ a : V, N ⧸ MulAction.stabilizer N a) =>
        p ⟨a, q⟩) hk
      exact eq_of_heq (Sigma.mk.inj he).2
    exact (gmpAutCosetAction_mem_ker φ a (fun k => hφ k a) k).mp hka x
  · intro hk
    apply Equiv.ext
    rintro ⟨a, q⟩
    have hka : k ∈ (gmpAutCosetAction (MulAction.stabilizer N a) φ (fun k => hφ k a)).ker := by
      apply (gmpAutCosetAction_mem_ker φ a (fun k => hφ k a) k).mpr
      intro x
      change φ k = 1 at hk
      rw [hk]
      rfl
    exact congrArg (Sigma.mk a) (congrArg (fun p : Equiv.Perm (N ⧸ MulAction.stabilizer N a) => p q) hka)

/-- Each coset space has the size of one orbit, so all the base-point
copies together have degree at most the square of the original degree. -/
theorem gmpLuksSecondAction_degree [Finite V] :
    Nat.card (Σ a : V, N ⧸ MulAction.stabilizer N a) ≤ Nat.card V ^ 2 := by
  classical
  letI := Fintype.ofFinite V
  haveI (a : V) : Finite (N ⧸ MulAction.stabilizer N a) :=
    Finite.of_equiv (MulAction.orbit N a) (MulAction.orbitEquivQuotientStabilizer N a)
  rw [Nat.card_sigma]
  calc
    ∑ a : V, Nat.card (N ⧸ MulAction.stabilizer N a) ≤ ∑ _a : V, Nat.card V := by
      apply Finset.sum_le_sum
      intro a _
      rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer N a)]
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = Nat.card V ^ 2 := by simp [pow_two, Nat.card_eq_fintype_card]

end GI.Proved
