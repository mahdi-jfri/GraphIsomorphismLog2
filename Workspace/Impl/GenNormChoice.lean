module

public import Workspace.Impl.GenNormChild
public import Workspace.Impl.Weights

@[expose] public section

/-!
# Choosing the one or two normalization cosets

If every generator acts evenly on the Cameron points, the normalized group is the whole
parent group. Otherwise identity and any odd generator cover the parent group. These lemmas
build `NormChoice` without the default choice of coset representatives.
-/

namespace GI.Impl

open GI.Algorithm Equiv Equiv.Perm
open scoped Pointwise

variable {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S)
variable {m k : ℕ} (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k))
variable (hS : Q.ProductStructure m k 1 e)

/-- The sign of the point permutation, on the parent group. -/
noncomputable def normSign : S.G →* ℤˣ :=
  Perm.sign.comp ((Q.permHom e hS).comp Q.ρ.rangeRestrict)

/-- The normalized subgroup is exactly the kernel of the computed point sign. -/
theorem normMem_iff (g : S.G) :
    (g : Perm Ω) ∈ Q.normGroup e hS ↔ normSign Q e hS g = 1 := by
  constructor
  · exact Q.sign_of_mem e hS
  · intro h
    exact ⟨g, h, rfl⟩

/-- Testing a generating list suffices to decide whether all point actions are even. -/
theorem normEven_of_gens {n : ℕ} (en : Ω ≃ Fin n)
    (gs : List (Perm (Fin n))) (hgen : GI.Cited.gens gs = GI.Assembly.groupFin en S.G)
    (heven : ∀ a ∈ gs, ∀ ha : (GI.Assembly.toFin en).symm a ∈ S.G,
      normSign Q e hS ⟨_, ha⟩ = 1) : ∀ g : S.G, normSign Q e hS g = 1 := by
  have hh := hom_eq_of_gens (e := en) (normSign Q e hS) (1 : S.G →* ℤˣ) gs hgen heven
  intro g
  rw [hh]
  rfl

/-- With only even point actions, normalization has one coset. -/
theorem normIndex_one (heven : ∀ g : S.G, normSign Q e hS g = 1) :
    ((Q.normGroup e hS).subgroupOf S.G).index = 1 := by
  apply Subgroup.index_eq_one.mpr
  apply top_unique
  intro g _
  exact (normMem_iff Q e hS g).mpr (heven g)

/-- An odd point action forces exactly two cosets. -/
theorem normIndex_two [Finite Ω] (t : S.G) (ht : normSign Q e hS t ≠ 1) :
    ((Q.normGroup e hS).subgroupOf S.G).index = 2 := by
  have hne : (Q.normGroup e hS).subgroupOf S.G ≠ ⊤ := by
    intro h
    have hm : t ∈ (Q.normGroup e hS).subgroupOf S.G := by rw [h]; trivial
    exact ht ((normMem_iff Q e hS t).mp hm)
  have hlo := Subgroup.one_lt_index_of_ne_top hne
  have hhi := Q.index_le_two e hS
  omega

/-- The explicit representatives when all parent elements act evenly. -/
def normChoiceEven (heven : ∀ g : S.G, normSign Q e hS g = 1) : Q.NormChoice where
  m := m
  k := k
  e := e
  hS := hS
  τ _ := 1
  τ_mem _ := S.G.one_mem
  cover := by
    intro g hg
    have hi := normIndex_one Q e hS heven
    refine Set.mem_iUnion.mpr ⟨⟨0, by omega⟩, ?_⟩
    exact Set.mem_smul_set.mpr ⟨g, (normMem_iff Q e hS ⟨g, hg⟩).mpr (heven ⟨g, hg⟩), by simp⟩

/-- Identity and the supplied odd element are valid coset representatives. The sign proves
coverage, so no quotient representative is chosen inside this definition. -/
noncomputable def normChoiceOdd [Finite Ω] (t : S.G) (ht : normSign Q e hS t ≠ 1) :
    Q.NormChoice where
  m := m
  k := k
  e := e
  hS := hS
  τ j := if j.val = 0 then 1 else t.1
  τ_mem j := by split_ifs; exacts [S.G.one_mem, t.2]
  cover := by
    intro g hg
    have hi := normIndex_two Q e hS t ht
    by_cases he : normSign Q e hS ⟨g, hg⟩ = 1
    · refine Set.mem_iUnion.mpr ⟨⟨0, by omega⟩, ?_⟩
      simp only [ite_true]
      exact Set.mem_smul_set.mpr ⟨g, (normMem_iff Q e hS ⟨g, hg⟩).mpr he, by simp⟩
    · have hs : normSign Q e hS ⟨g, hg⟩ = normSign Q e hS t := by
        obtain h | h := Int.units_eq_one_or (normSign Q e hS ⟨g, hg⟩)
        · exact (he h).elim
        obtain h' | h' := Int.units_eq_one_or (normSign Q e hS t)
        · exact (ht h').elim
        exact h.trans h'.symm
      have hm : ((t : Perm Ω)⁻¹ * g) ∈ Q.normGroup e hS := by
        apply (normMem_iff Q e hS (t⁻¹ * ⟨g, hg⟩)).mpr
        rw [map_mul, map_inv, hs, inv_mul_cancel]
      refine Set.mem_iUnion.mpr ⟨⟨1, by omega⟩, ?_⟩
      simp only [show ¬ (1 : ℕ) = 0 by omega, ite_false]
      exact Set.mem_smul_set.mpr ⟨(t : Perm Ω)⁻¹ * g, hm, by
        change (t : Perm Ω) * ((t : Perm Ω)⁻¹ * g) = g
        simp⟩

end GI.Impl
