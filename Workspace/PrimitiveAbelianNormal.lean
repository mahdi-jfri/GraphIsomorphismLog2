module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Workspace.BudgetInductionRegular

@[expose] public section

namespace GI.PrimitiveStructure

variable {G V : Type*} [Group G] [MulAction G V] [FaithfulSMul G V]

/-- Every nontrivial normal subgroup in a faithful primitive action is
transitive. This is the elementary normal-subgroup part of the action analysis. -/
theorem normal_pretransitive [MulAction.IsPreprimitive G V]
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥) : MulAction.IsPretransitive N V := by
  apply MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
  intro hfixed
  apply hne
  apply (Subgroup.eq_bot_iff_forall N).mpr
  intro n hn
  apply eq_of_smul_eq_smul (α := V)
  intro v
  have hv : v ∈ MulAction.fixedPoints N V := by rw [hfixed]; trivial
  rw [one_smul]
  exact MulAction.mem_fixedPoints.mp hv ⟨n, hn⟩

/-- A faithful transitive abelian action is regular: agreement at any one
point forces agreement everywhere. -/
theorem abelian_transitive_free [MulAction.IsPretransitive G V]
    (comm : ∀ x y : G, x * y = y * x) (a : V) :
    Function.Injective (fun g : G => g • a) := by
  intro x y hxy
  change x • a = y • a at hxy
  apply eq_of_smul_eq_smul (α := V)
  intro v
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G a v
  calc
    x • (g • a) = g • (x • a) := by rw [← mul_smul, comm x g, mul_smul]
    _ = g • (y • a) := by rw [hxy]
    _ = y • (g • a) := by rw [← mul_smul, comm g y, mul_smul]

theorem abelian_transitive_bijective [MulAction.IsPretransitive G V]
    (comm : ∀ x y : G, x * y = y * x) (a : V) :
    Function.Bijective (fun g : G => g • a) :=
  ⟨abelian_transitive_free comm a, fun v => MulAction.exists_smul_eq G a v⟩

/-- A nontrivial abelian normal subgroup of a faithful primitive group has
an actual regular permutation representation on the given point set. -/
theorem abelian_normal_regular [MulAction.IsPreprimitive G V]
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥)
    (comm : ∀ x y : N, x * y = y * x) (a : V) :
    Function.Bijective (fun g : N => g • a) := by
  letI := normal_pretransitive (V := V) N hne
  exact abelian_transitive_bijective comm a

noncomputable def abelianNormalPointEquiv [MulAction.IsPreprimitive G V]
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥)
    (comm : ∀ x y : N, x * y = y * x) (a : V) : N ≃ V :=
  Equiv.ofBijective (fun g : N => g • a) (abelian_normal_regular N hne comm a)

theorem abelian_normal_card [MulAction.IsPreprimitive G V]
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥)
    (comm : ∀ x y : N, x * y = y * x) (a : V) : Nat.card N = Nat.card V :=
  Nat.card_congr (abelianNormalPointEquiv N hne comm a)

end GI.PrimitiveStructure
