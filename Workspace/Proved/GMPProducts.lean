module

public import Workspace.CompositionFactors
public import Mathlib.GroupTheory.SemidirectProduct

@[expose] public section

/-!
# Bounds for nonabelian composition products

These are the subgroup and quotient bounds used in the proof of GMP,
Theorem 5.1. To bound a subgroup, intersect it with the penultimate term
of a composition series. The remaining image lies in a simple group.
-/

namespace GI.Proved

open GI.Cited GI.Composition

universe u v

private theorem gmp_bFac_injective_aux :
    ∀ (n : ℕ) (X : Type u) [Group X] [Finite X], Nat.card X = n →
    ∀ (Y : Type v) [Group Y] [Finite Y] (f : Y →* X), Function.Injective f →
      bFac Y ≤ bFac X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ hn Y _ _ f hf
    rcases cases' (spec X) with ⟨hsub, _, hb⟩ |
      ⟨K, hKn, a, b, hs, hK, _, hb⟩
    · have : Subsingleton X := hsub
      have : Subsingleton Y := Function.Injective.subsingleton hf
      rw [bFac_of_solvable, hb]
    · let q : Y →* X ⧸ K := (QuotientGroup.mk' K).comp f
      let g : q.ker →* K :=
        { toFun := fun y => ⟨f y.val, (QuotientGroup.eq_one_iff _).mp y.property⟩
          map_one' := Subtype.ext (map_one f)
          map_mul' := fun x y => Subtype.ext (map_mul f x.val y.val) }
      have hg : Function.Injective g := by
        intro x y h
        exact Subtype.ext (hf (congrArg Subtype.val h))
      have hker : bFac q.ker ≤ bFac K :=
        ih (Nat.card K) (hn ▸ card_lt_of_ne_top (ne_top_of_simple hs)) K rfl q.ker g hg
      have himage : bFac q.range ≤ wb (X ⧸ K) := by
        by_cases hc : ∀ x y : X ⧸ K, x * y = y * x
        · have := Group.isSolvable_of_comm hc
          rw [bFac_of_solvable, wb_of_comm hc]
        · rw [wb_of_not_comm hc]
          exact bFac_le_card.trans (Subgroup.card_le_card_group _)
      rw [bFac_ker_range q, hb, ← bFac_eq hK]
      exact Nat.mul_le_mul hker himage

/-- The nonabelian composition product cannot increase on passing to a subgroup. -/
theorem gmp_bFac_le_of_injective {X Y : Type*} [Group X] [Finite X]
    [Group Y] [Finite Y] (f : Y →* X) (hf : Function.Injective f) :
    bFac Y ≤ bFac X :=
  gmp_bFac_injective_aux (Nat.card X) X rfl Y f hf

/-- Subgroup form of monotonicity of the nonabelian composition product. -/
theorem gmp_bFac_subgroup_le {X : Type*} [Group X] [Finite X] (H : Subgroup X) :
    bFac H ≤ bFac X :=
  gmp_bFac_le_of_injective H.subtype H.subtype_injective

/-- The nonabelian composition product cannot increase on passing to a quotient. -/
theorem gmp_bFac_le_of_surjective {X Y : Type*} [Group X] [Finite X]
    [Group Y] [Finite Y] (f : X →* Y) (hf : Function.Surjective f) :
    bFac Y ≤ bFac X := by
  rw [bFac_mul f.ker,
    bFac_congr (QuotientGroup.quotientKerEquivOfSurjective f hf)]
  exact Nat.le_mul_of_pos_left _ bFac_pos

/-- Enlarging the normal subgroup can only decrease the product in the quotient. -/
theorem gmp_bFac_quotient_antitone {X : Type*} [Group X] [Finite X]
    (N M : Subgroup X) [N.Normal] [M.Normal] (hNM : N ≤ M) :
    bFac (X ⧸ M) ≤ bFac (X ⧸ N) := by
  let f := QuotientGroup.map N M (MonoidHom.id X) hNM
  have hf : Function.Surjective f :=
    QuotientGroup.map_surjective_of_surjective N M (MonoidHom.id X)
      (QuotientGroup.mk'_surjective M) hNM
  exact gmp_bFac_le_of_surjective f hf

/-- Multiplicativity along two nested normal subgroups. -/
theorem gmp_bFac_quotient_chain {X : Type*} [Group X] [Finite X]
    (N M : Subgroup X) [N.Normal] [M.Normal] (hNM : N ≤ M) :
    bFac (X ⧸ N) = bFac (M ⧸ N.subgroupOf M) * bFac (X ⧸ M) := by
  have h := bFac_mul M (X := X)
  rw [bFac_mul (N.subgroupOf M),
    bFac_congr (Subgroup.subgroupOfEquivOfLe hNM), mul_assoc] at h
  rw [bFac_mul N] at h
  exact Nat.eq_of_mul_eq_mul_left bFac_pos h

/-- A solvable normal factor in a semidirect product contributes no
nonabelian composition factors. -/
theorem gmp_bFac_semidirect {N H : Type*} [Group N] [Group H]
    [Finite N] [Finite H] [Group.IsSolvable N] (φ : H →* MulAut N)
    [Finite (N ⋊[φ] H)] :
    bFac (N ⋊[φ] H) = bFac H := by
  let f : N ⋊[φ] H →* H := SemidirectProduct.rightHom
  have hker : bFac f.ker = 1 := by
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom,
      ← bFac_congr (MonoidHom.ofInjective (f := SemidirectProduct.inl)
        SemidirectProduct.inl_injective), bFac_of_solvable]
  rw [bFac_mul f.ker, hker, one_mul,
    bFac_congr (QuotientGroup.quotientKerEquivOfSurjective f
      SemidirectProduct.rightHom_surjective)]

end GI.Proved
