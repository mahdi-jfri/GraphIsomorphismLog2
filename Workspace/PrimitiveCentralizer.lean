module

public import Workspace.PrimitiveAbelianExponent
public import Workspace.RadicalSocleStructure

@[expose] public section

namespace GI.PrimitiveStructure

variable {G V : Type*} [Group G] [MulAction G V] [FaithfulSMul G V]

/-- A subgroup commuting with a transitive subgroup acts semiregularly.
The conclusion concerns the given physical action, with no classification
or abstract representation supplied as input. -/
theorem commuting_transitive_free (M N : Subgroup G)
    [MulAction.IsPretransitive N V]
    (comm : ∀ m : M, ∀ n : N, (m : G) * (n : G) = (n : G) * (m : G))
    (a : V) : Function.Injective (fun m : M => m • a) := by
  intro x y hxy
  change (x : G) • a = (y : G) • a at hxy
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := V)
  intro v
  obtain ⟨n, rfl⟩ := MulAction.exists_smul_eq N a v
  change (x : G) • ((n : G) • a) = (y : G) • ((n : G) • a)
  rw [← mul_smul, comm x n, mul_smul, hxy,
    ← mul_smul, ← comm y n, mul_smul]

/-- In particular, the actual centralizer of a transitive subgroup has
an injective evaluation map at every point. Normality is unnecessary. -/
theorem centralizer_transitive_free (N : Subgroup G)
    [MulAction.IsPretransitive N V] (a : V) :
    Function.Injective (fun c : Subgroup.centralizer (N : Set G) => c • a) :=
  commuting_transitive_free _ N (fun c n => (c.property n n.property).symm) a

theorem commuting_transitive_regular (M N : Subgroup G)
    [MulAction.IsPretransitive M V] [MulAction.IsPretransitive N V]
    (comm : ∀ m : M, ∀ n : N, (m : G) * (n : G) = (n : G) * (m : G))
    (a : V) : Function.Bijective (fun m : M => m • a) :=
  ⟨commuting_transitive_free M N comm a, fun v => MulAction.exists_smul_eq M a v⟩

/-- A transitive subgroup commuting with a transitive subgroup is its
entire centralizer inside the faithful ambient group. -/
theorem centralizer_eq_of_commuting_transitive (M N : Subgroup G)
    [MulAction.IsPretransitive M V] [MulAction.IsPretransitive N V]
    (comm : ∀ m : M, ∀ n : N, (m : G) * (n : G) = (n : G) * (m : G))
    (a : V) : Subgroup.centralizer (N : Set G) = M := by
  have hMC : M ≤ Subgroup.centralizer (N : Set G) := by
    intro m hm n hn
    exact (comm ⟨m, hm⟩ ⟨n, hn⟩).symm
  exact (eq_of_transitive_le_regular _ M hMC a (centralizer_transitive_free N a)).symm

/-- The pointwise stabilizer obstruction is explicit: an element of the
centralizer fixing one point is the identity. -/
theorem centralizer_eq_one_of_fixing_point (N : Subgroup G)
    [MulAction.IsPretransitive N V] (a : V)
    (c : Subgroup.centralizer (N : Set G)) (hfix : c • a = a) : c = 1 :=
  centralizer_transitive_free N a (by simpa only [one_smul] using hfix)

theorem centralizer_card_le_degree [Finite V] (N : Subgroup G)
    [MulAction.IsPretransitive N V] (a : V) :
    Nat.card (Subgroup.centralizer (N : Set G)) ≤ Nat.card V :=
  Nat.card_le_card_of_injective _ (centralizer_transitive_free N a)

end GI.PrimitiveStructure
