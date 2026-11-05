module

public import Workspace.Proved.GMPProducts
public import Workspace.Proved.GMPNumeric
public import Workspace.AffineRecognition
public import Workspace.PrimitiveAbelianCoordinates

@[expose] public section

/-!
# The affine case of the GMP bound

A primitive group with a nontrivial abelian normal subgroup embeds in an
affine group of degree `p ^ d`. Translations are solvable, so only the
linear group contributes nonabelian composition factors. Counting all
matrices bounds that contribution by `(p ^ d) ^ d`.
-/

namespace GI.Proved

open GI.Composition GI.PrimitiveStructure GI.MatrixValuation

/-- Counting all matrices gives the elementary order bound needed here. -/
theorem gmp_card_GL_le (p d : ℕ) [Fact p.Prime] :
    Nat.card (GL (Fin d) (ZMod p)) ≤ (p ^ d) ^ d := by
  calc
    Nat.card (GL (Fin d) (ZMod p)) ≤
        Nat.card (Matrix (Fin d) (Fin d) (ZMod p)) :=
      Nat.card_le_card_of_injective Units.val Units.val_injective
    _ = (p ^ d) ^ d := by
      rw [Matrix.card_matrix, Nat.card_fin, Nat.card_zmod, pow_mul]

/-- Every quotient of an affine group in its primitive action satisfies
the desired bound. Transitivity of the quotient kernel is not needed
for this case. -/
theorem gmp_affine_quotient_bound {n : ℕ} (hn : 1 ≤ n)
    (A : Subgroup (Equiv.Perm (Fin n))) [MulAction.IsPreprimitive A (Fin n)]
    (V : Subgroup A) [V.Normal] (hV : V ≠ ⊥)
    (comm : ∀ x y : V, x * y = y * x) (N : Subgroup A) [N.Normal] :
    (bFac (A ⧸ N) : ℝ) ≤ (n : ℝ) ^ Real.logb 2 n := by
  let a : Fin n := ⟨0, hn⟩
  obtain ⟨p, hp, d, ⟨basis⟩⟩ := abelian_normal_coordinates V hV comm a
  have : Fact p.Prime := ⟨hp⟩
  have regular := abelian_normal_regular V hV comm a
  have hdegree : n = p ^ d := by
    simpa only [Fintype.card_fin, ZMod.card] using
      AffineRecognition.degree_eq V a regular basis
  have hA : bFac A ≤ bFac (AffineGroup (ZMod p) d) :=
    gmp_bFac_le_of_injective (AffineRecognition.affineEmbedding V a regular basis)
      (AffineRecognition.affineEmbedding_injective V a regular basis)
  have hQ : bFac (A ⧸ N) ≤ bFac A :=
    gmp_bFac_le_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hlinear : bFac (AffineGroup (ZMod p) d) = bFac (GL (Fin d) (ZMod p)) :=
    gmp_bFac_semidirect (translationAction (ZMod p) d)
  have hnat : bFac (A ⧸ N) ≤ n ^ d := by
    exact ((hQ.trans (hA.trans hlinear.le)).trans
      (bFac_le_card.trans (gmp_card_GL_le p d))).trans_eq
        (congrArg (fun k => k ^ d) hdegree.symm)
  have hpow : 2 ^ d ≤ n := by
    rw [hdegree]
    exact Nat.pow_le_pow_left hp.two_le d
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    (bFac (A ⧸ N) : ℝ) ≤ (n : ℝ) ^ d := by exact_mod_cast hnat
    _ ≤ (n : ℝ) ^ Real.logb 2 n := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hnR (gmp_exponent_le_logb hpow)

end GI.Proved
