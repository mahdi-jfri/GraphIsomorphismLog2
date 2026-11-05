module

public import Workspace.Cited.CFSG
public import Workspace.Cited.MarotiPrimitive
import CFSG.Certified.Classification
import CFSG.Yardstones.Md42047359a2a.Reduction
import Maroti.Main

/-!
# The cited theorems that rest on the classification

The paper uses three results that rest on the classification of finite simple groups. This file
proves them from two formalizations.

* `GI.Cited.cfsg`: the classification itself, `TauCeti.ClassificationStatement`. The proof is
  `CFSG.Certified.classification_finite_simple_groups` from AxiomMath/CFSG
  (https://github.com/AxiomMath/CFSG).
* `GI.Cited.catalogueSchreier`: Schreier's conjecture for the groups on the classification list,
  `GI.Cited.CatalogueSchreier`. The proof is `catalogueSchreier_of_certificates` from
  AxiomMath/CFSG, whose statement has the same body.
* `GI.Cited.marotiPrimitive`: Maróti's theorem on the orders of primitive groups for degree at
  least 25, `GI.Cited.MarotiPrimitive`. It follows from `Maroti.theorem_1_1_of_classification`,
  Theorem 1.1 of A. Maróti, *On the orders of primitive groups*, J. Algebra 258 (2002), 631–640,
  from MarotiOrdersOfPrimitiveGroups (https://github.com/mahdi-jfri/MarotiOrdersOfPrimitiveGroups).

The two formalizations are imported privately. A file that imports this one sees only the three
statements, so it does not load the proof of the classification.
-/

@[expose] public section

namespace GI.Cited

open Equiv Maroti

/-- **The classification of finite simple groups**, from AxiomMath/CFSG's proof. -/
theorem cfsg : TauCeti.ClassificationStatement.{0} :=
  TauCeti.classificationStatement_iff.2 fun G _ _ _ =>
    CFSG.Certified.classification_finite_simple_groups G

/-- **Schreier's conjecture for the groups on the classification list**, from AxiomMath/CFSG's
proof. The two statements have the same body. -/
theorem catalogueSchreier : CatalogueSchreier :=
  CFSG.Yardstones.Md42047359a2a.catalogueSchreier_of_certificates

/-- **Maróti's theorem for degree at least 25**, from Theorem 1.1. In degree `n ≥ 25` the Mathieu
case does not occur, and the third case gives `|G| < n^(1+⌊log₂ n⌋)`. In the first case,
Maróti's statement moves coordinate `σ⁻¹ i` to coordinate `i`, so `GI.Cited.MarotiPrimitive`
holds with `σ⁻¹` in place of `σ`. -/
theorem marotiPrimitive : MarotiPrimitive := by
  intro n hn G hG
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  rcases theorem_1_1_of_classification cfsg G with
    ⟨m, k, r, e, -, -, -, -, hwr, halt⟩ | ⟨s, hs, hcard, -⟩ | ⟨hle, hlt⟩
  · refine Or.inr ⟨m, k, r, e, fun g hg => ?_, fun h hh => ?_⟩
    · obtain ⟨σ, h, hgh⟩ := hwr g hg
      refine ⟨σ⁻¹, h, fun x => ?_⟩
      have := congrArg (· (e x)) hgh
      simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply] at this
      rw [this]
      funext i
      rfl
    · convert halt fun i => ⟨h i, hh i⟩ using 1
      apply Equiv.ext
      intro x
      apply e.injective
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.permCongr_apply,
        Equiv.symm_symm]
      funext i
      rfl
  · simp only [fourTransitiveMathieu, List.mem_cons, List.not_mem_nil, or_false] at hs
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
    rcases hs with rfl | rfl | rfl | rfl <;> simp at hcard <;> omega
  · rw [Nat.card_fin] at hle hlt
    exact Or.inl (hle.trans_lt hlt)

end GI.Cited
