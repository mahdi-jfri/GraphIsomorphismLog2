import Workspace.Proved.SolvAFac
import Workspace.Proved.SolvOrder
import Workspace.Cited.GMP

/-!
# [GMP, Proposition 6.1], abelian part

`GI.Proved.gmpAbelianFactors : GI.Cited.GMPAbelianFactors`. For `P ≤ Sym(n)`, `n ≥ 1`, the
product `a(P)` of the orders of the abelian composition factors is at most `24^{(n-1)/3}`.

*Proof.* As in [GMP, Section 6, before Proposition 6.1]: `a(P)` is at most the order of a
solvable subgroup `S` of `P` (`GI.Proved.solvAFac_le_solvable`, proved here without CFSG by the
Frattini argument), and Dixon's theorem bounds `|S| ≤ 24^{(n-1)/3}`
(`GI.Proved.solvOrder_bound`).
-/

namespace GI.Proved

open GI.Composition

/-- From `c^3 ≤ 24^{n-1}` to `c ≤ 24^{(n-1)/3}`. -/
theorem solv_cube_root {c n : ℕ} (hn : 1 ≤ n) (h : c ^ 3 ≤ 24 ^ (n - 1)) :
    (c : ℝ) ≤ (24 : ℝ) ^ (((n : ℝ) - 1) / 3) := by
  have h1 : ((c : ℝ) ^ (3 : ℕ)) ≤ (24 : ℝ) ^ (n - 1 : ℕ) := by exact_mod_cast h
  have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ ((3 : ℕ) : ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast (by positivity) (by norm_num), ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)] at h2
  convert h2 using 2
  rw [Nat.cast_sub hn]
  push_cast
  ring

/-- **[GMP, Proposition 6.1], abelian part**, proved. -/
theorem gmpAbelianFactors : GI.Cited.GMPAbelianFactors := by
  intro n hn P a b h
  rw [← aFac_eq h]
  obtain ⟨S, hS, hle⟩ := solvAFac_le_solvable P
  let S' : Subgroup (Equiv.Perm (Fin n)) := S.map P.subtype
  have hS' : IsSolvable S' :=
    solvable_of_surjective (f := (S.equivMapOfInjective P.subtype
      P.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have hcard : Nat.card S' = Nat.card S := Subgroup.card_map_of_injective P.subtype_injective
  have hb := solvOrder_bound (α := Fin n) (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)
    S' hS'
  rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, hcard] at hb
  exact (Nat.cast_le.mpr hle).trans (solv_cube_root hn hb)

end GI.Proved
