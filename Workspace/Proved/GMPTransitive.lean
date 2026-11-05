module

public import Workspace.Proved.GMPBlocks
public import Workspace.Proved.GMPRelabel

@[expose] public section

/-!
# The transitive nonabelian composition-product bound

This is GMP, Theorem 5.1, with the degree-one endpoint included. Strong
induction applies Theorem 2.3 to a nontrivial block system. Both the block
count and the block size are smaller than the original degree. The
primitive case was proved in `GMPPrimitive.lean`.
-/

namespace GI.Proved

open GI.Composition GI.Cited GI.BudgetInduction

theorem gmp_degreeBound : ∀ n : ℕ, 1 ≤ n → GMPDegreeBound n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn A R _ _
    by_cases hn1 : n = 1
    · subst n
      rw [bFac_of_solvable]
      simp only [Nat.cast_one, Real.one_rpow, le_refl]
    have hn2 : 2 ≤ n := by omega
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn2
    have : MulAction.IsPretransitive A (Fin n) := by
      constructor
      intro x y
      obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R x y
      exact ⟨r.val, hr⟩
    have hR : R ≠ ⊥ := by
      intro hbot
      obtain ⟨x, y, hxy⟩ := exists_pair_ne (Fin n)
      obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R x y
      have hr1 : r.val = 1 := by simpa only [hbot, Subgroup.mem_bot] using r.property
      have he : r = 1 := Subtype.ext hr1
      rw [he, one_smul] at hr
      exact hxy hr
    by_cases hprim : MulAction.IsPreprimitive A (Fin n)
    · exact gmp_primitive_quotient_bound hn2 A R hR
    let a : Fin n := ⟨0, by omega⟩
    have hnot : ¬ ∀ (S : Set (Fin n)), a ∈ S → MulAction.IsBlock A S →
        MulAction.IsTrivialBlock S := by
      intro hh
      exact hprim (MulAction.IsPreprimitive.of_isTrivialBlock_base a
        (fun ha hS => hh _ ha hS))
    push Not at hnot
    obtain ⟨S, ha, hS, hnt⟩ := hnot
    let p := partitionOfBlock hS ⟨a, ha⟩
    let B := Quotient p.setoid
    let c := p.blockCover
    let F := {x : Fin n // c.label x = c.label a}
    letI : Fintype B := Fintype.ofFinite B
    letI : Fintype F := Fintype.ofFinite F
    have hc := partitionOfBlock_card_bounds hS ha hnt
    change 2 ≤ Nat.card B ∧ 2 ≤ Nat.card F at hc
    have hBc : 2 ≤ Fintype.card B := by simpa only [Nat.card_eq_fintype_card] using hc.1
    have hFc : 2 ≤ Fintype.card F := by simpa only [Nat.card_eq_fintype_card] using hc.2
    have hsmall := blockCover_smaller_degrees c p.label_surjective a hBc hFc
    have hBn : Nat.card B < n := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hsmall.1
    have hFn : Nat.card F < n := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hsmall.2
    have := gmp_block_top_transitive c R p.label_surjective
    have := gmp_block_local_transitive c R (c.label a)
    have htop := gmp_degreeBound_relabel
      (ih (Nat.card B) hBn (by omega)) c.project.range
      ((R.map c.project).subgroupOf c.project.range)
    have hlocal := gmp_degreeBound_relabel
      (ih (Nat.card F) hFn (by omega)) (gmpBlockProject c (c.label a)).range
      (gmpBlockNormalImage c R (c.label a))
    have hsplit := gmp_block_quotient_bound c R p.label_surjective (c.label a)
    have hsplitR : (bFac (A ⧸ R) : ℝ) ≤
        (bFac (c.project.range ⧸ (R.map c.project).subgroupOf c.project.range) : ℝ) *
        (bFac ((gmpBlockProject c (c.label a)).range ⧸
          gmpBlockNormalImage c R (c.label a)) : ℝ) := by exact_mod_cast hsplit
    have hprod : (Nat.card B : ℝ) * (Nat.card F : ℝ) = n := by
      have h := blockCover_card_factorization c p.label_surjective a
      simpa only [← Nat.cast_mul, Nat.card_eq_fintype_card, Fintype.card_fin] using
        congrArg (fun k : ℕ => (k : ℝ)) h
    have hB1 : (1 : ℝ) ≤ Nat.card B := by exact_mod_cast (show 1 ≤ Nat.card B by omega)
    have hF1 : (1 : ℝ) ≤ Nat.card F := by exact_mod_cast (show 1 ≤ Nat.card F by omega)
    calc
      (bFac (A ⧸ R) : ℝ) ≤ _ := hsplitR
      _ ≤ (Nat.card B : ℝ) ^ Real.logb 2 (Nat.card B) *
          (Nat.card F : ℝ) ^ Real.logb 2 (Nat.card F) :=
        mul_le_mul htop hlocal (Nat.cast_nonneg _)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ ((Nat.card B : ℝ) * (Nat.card F : ℝ)) ^
          Real.logb 2 ((Nat.card B : ℝ) * (Nat.card F : ℝ)) :=
        gmp_degree_bound_mul hB1 hF1
      _ = _ := by rw [hprod]

/-- GMP, Theorem 1.4 (transitive case), equivalently Theorem 5.1 with
the non-strict endpoint at degree one. -/
theorem gmpTransitiveNonabelian : GI.Cited.GMPTransitiveNonabelian := by
  intro n hn A G hGA _ htrans a b h
  have : MulAction.IsPretransitive (G.subgroupOf A) (Fin n) := by
    constructor
    intro x y
    obtain ⟨g, hg⟩ := htrans.exists_smul_eq x y
    exact ⟨⟨⟨g.val, hGA g.property⟩, g.property⟩, hg⟩
  rw [← bFac_eq h]
  exact gmp_degreeBound n hn A (G.subgroupOf A)

end GI.Proved
