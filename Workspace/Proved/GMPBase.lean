module

public import Workspace.Proved.GMPPrimitive

@[expose] public section

/-! # The GMP interface in degree one and in the primitive case -/

namespace GI.Proved

open GI.Cited GI.Composition

/-- The degree-one endpoint of the transitive bound is an equality. -/
theorem gmp_transitiveNonabelian_one
    (A G : Subgroup (Equiv.Perm (Fin 1))) [(G.subgroupOf A).Normal]
    (a b : ℕ) (h : CompositionProducts (A ⧸ G.subgroupOf A) a b) :
    (b : ℝ) ≤ (1 : ℝ) ^ Real.logb 2 1 := by
  have hb := b_eq_one_of_solvable h inferInstance
  simp only [hb, Nat.cast_one, Real.one_rpow, le_refl]

/-- The exact cited interface when the ambient action is primitive.
This includes degree one. -/
theorem gmp_transitiveNonabelian_of_preprimitive
    (n : ℕ) (hn : 1 ≤ n) (A G : Subgroup (Equiv.Perm (Fin n))) (hGA : G ≤ A)
    [(G.subgroupOf A).Normal] [MulAction.IsPreprimitive A (Fin n)]
    (htrans : MulAction.IsPretransitive G (Fin n))
    (a b : ℕ) (h : CompositionProducts (A ⧸ G.subgroupOf A) a b) :
    (b : ℝ) ≤ (n : ℝ) ^ Real.logb 2 n := by
  by_cases hn1 : n = 1
  · subst n
    simpa only [Nat.cast_one] using gmp_transitiveNonabelian_one A G a b h
  have hn2 : 2 ≤ n := by omega
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn2
  have := htrans
  have hR : G.subgroupOf A ≠ ⊥ := by
    intro hbot
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (Fin n)
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
    have hgA : (⟨g.val, hGA g.property⟩ : A) ∈ G.subgroupOf A := g.property
    rw [hbot, Subgroup.mem_bot] at hgA
    have hgv : (g : Equiv.Perm (Fin n)) = 1 := congrArg (fun z : A => z.val) hgA
    have hg1 : g = 1 := Subtype.ext hgv
    rw [hg1, one_smul] at hg
    exact hxy hg
  rw [← bFac_eq h]
  exact gmp_primitive_quotient_bound hn2 A (G.subgroupOf A) hR

end GI.Proved
