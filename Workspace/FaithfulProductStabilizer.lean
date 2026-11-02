import Workspace.CoordinateFactors
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

namespace GI.PrimitiveProducts

variable {G V : Type*} [Group G] [MulAction G V]

/-- In a faithful transitive action, a normal subgroup contained in a
point stabilizer is trivial. -/
theorem normal_le_stabilizer_eq_bot [FaithfulSMul G V] [MulAction.IsPretransitive G V]
    (N : Subgroup G) [N.Normal] (a : V) (hle : N ≤ MulAction.stabilizer G a) : N = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall N).mpr
  intro x hx
  apply eq_of_smul_eq_smul (α := V)
  intro v
  rw [one_smul]
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G a v
  have hc : g⁻¹ * x * g ∈ N := by
    simpa only [inv_inv] using (inferInstance : N.Normal).conj_mem x hx g⁻¹
  have hf := hle hc
  change (g⁻¹ * x * g) • a = a at hf
  have h := congrArg (fun w : V => g • w) hf
  simpa only [mul_smul, smul_inv_smul] using h

variable {S I : Type*} [Group S] [DecidableEq I]

theorem coordinateFactor_normal (i : I) :
    (MonoidHom.mulSingle (fun _ : I => S) i).range.Normal := by
  constructor
  intro x hx g
  obtain ⟨s, rfl⟩ := hx
  refine ⟨g i * s * (g i)⁻¹, ?_⟩
  funext j
  by_cases hj : j = i
  · subst j
    simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same, Pi.mul_apply, Pi.inv_apply]
  · simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj,
      Pi.mul_apply, Pi.inv_apply, mul_one, mul_inv_cancel]

theorem stabilizer_noFullFactors [Nontrivial S] [MulAction (I → S) V]
    [FaithfulSMul (I → S) V] [MulAction.IsPretransitive (I → S) V] (a : V) :
    NoFullFactors (MulAction.stabilizer (I → S) a) := by
  intro i hi
  let N := (MonoidHom.mulSingle (fun _ : I => S) i).range
  letI : N.Normal := coordinateFactor_normal i
  have hle : N ≤ MulAction.stabilizer (I → S) a := by
    rintro _ ⟨s, rfl⟩
    exact hi s
  have hb := normal_le_stabilizer_eq_bot N a hle
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  have hm : Pi.mulSingle i s ∈ N := ⟨s, rfl⟩
  rw [hb, Subgroup.mem_bot] at hm
  have he := congrFun hm i
  exact hs (by simpa only [Pi.mulSingle_eq_same, Pi.one_apply] using he)

end GI.PrimitiveProducts

#print axioms GI.PrimitiveProducts.normal_le_stabilizer_eq_bot
#print axioms GI.PrimitiveProducts.coordinateFactor_normal
#print axioms GI.PrimitiveProducts.stabilizer_noFullFactors
