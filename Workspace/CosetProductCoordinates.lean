module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Basic

@[expose] public section

namespace GI.PrimitiveCartesian

variable {I : Type*} {S : I → Type*} [∀ i, Group (S i)]

/-- Coordinate cosets of an actual product-subgroup coset. No normality
of the coordinate subgroups is needed. -/
def cosetProductMap (Q : ∀ i, Subgroup (S i)) :
    ((∀ i, S i) ⧸ Subgroup.pi Set.univ Q) → (∀ i, S i ⧸ Q i) :=
  Quotient.lift (fun x i => QuotientGroup.mk (x i)) (by
    intro x y hxy
    funext i
    apply Quotient.sound
    exact QuotientGroup.leftRel_apply.mpr
      ((QuotientGroup.leftRel_apply.mp hxy) i (Set.mem_univ i)))

theorem cosetProductMap_bijective (Q : ∀ i, Subgroup (S i)) :
    Function.Bijective (cosetProductMap Q) := by
  constructor
  · intro q r
    induction q using Quotient.inductionOn with | _ x =>
      induction r using Quotient.inductionOn with | _ y =>
        intro h
        apply Quotient.sound
        apply QuotientGroup.leftRel_apply.mpr
        intro i _
        exact QuotientGroup.leftRel_apply.mp (Quotient.exact (congrFun h i))
  · intro q
    refine ⟨QuotientGroup.mk (fun i => (q i).out), ?_⟩
    funext i
    exact QuotientGroup.out_eq' (q i)

noncomputable def cosetProductEquiv (Q : ∀ i, Subgroup (S i)) :
    ((∀ i, S i) ⧸ Subgroup.pi Set.univ Q) ≃ (∀ i, S i ⧸ Q i) :=
  Equiv.ofBijective (cosetProductMap Q) (cosetProductMap_bijective Q)

variable {G V : Type*} [Group G] [MulAction G V] [MulAction.IsPretransitive G V]

/-- Coordinates in the coset space of the actual point stabilizer. -/
noncomputable def transitiveCosetCoordinates (a : V) : V ≃ G ⧸ MulAction.stabilizer G a :=
  (Equiv.ofBijective (MulAction.ofQuotientStabilizer G a)
    ⟨MulAction.injective_ofQuotientStabilizer G a, fun v => by
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a v
      exact ⟨QuotientGroup.mk g, hg⟩⟩).symm

theorem transitiveCosetCoordinates_smul (a : V) (g : G) :
    transitiveCosetCoordinates a (g • a) = QuotientGroup.mk g := by
  apply (transitiveCosetCoordinates (G := G) a).symm.injective
  exact (transitiveCosetCoordinates (G := G) a).symm_apply_apply (g • a)

variable [MulAction (∀ i, S i) V] [MulAction.IsPretransitive (∀ i, S i) V]

/-- A product point stabilizer yields actual Cartesian coordinates on the
physical domain of its transitive action. -/
noncomputable def productActionCoordinates (a : V) (Q : ∀ i, Subgroup (S i))
    (hstab : MulAction.stabilizer (∀ i, S i) a = Subgroup.pi Set.univ Q) :
    V ≃ (∀ i, S i ⧸ Q i) :=
  (transitiveCosetCoordinates (G := ∀ i, S i) a).trans
    ((Subgroup.quotientEquivOfEq hstab).trans (cosetProductEquiv Q))

theorem productActionCoordinates_smul (a : V) (Q : ∀ i, Subgroup (S i))
    (hstab : MulAction.stabilizer (∀ i, S i) a = Subgroup.pi Set.univ Q)
    (g : ∀ i, S i) (i : I) :
    productActionCoordinates a Q hstab (g • a) i = QuotientGroup.mk (g i) := by
  change cosetProductMap Q ((Subgroup.quotientEquivOfEq hstab)
    (transitiveCosetCoordinates a (g • a))) i = _
  rw [transitiveCosetCoordinates_smul]
  rfl

theorem product_action_degree [Fintype I] [∀ i, Finite (S i)]
    (a : V) (Q : ∀ i, Subgroup (S i))
    (hstab : MulAction.stabilizer (∀ i, S i) a = Subgroup.pi Set.univ Q) :
    Nat.card V = ∏ i, (Q i).index := by
  rw [Nat.card_congr (productActionCoordinates a Q hstab), Nat.card_pi]
  rfl

end GI.PrimitiveCartesian
