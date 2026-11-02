import Workspace.BudgetInductionAffineAlternative
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace GI.AffineRecognition

open MatrixValuation BudgetInduction

variable {G V : Type*} [Group G] [MulAction G V]
variable (N : Subgroup G) [N.Normal] (a : V)
variable (regular : Function.Bijective (fun n : N => n • a))
variable {p d : ℕ} [Fact p.Prime]
variable (basis : N ≃* Multiplicative (Fin d → ZMod p))

/-- Coordinates are obtained by inverting the actual regular orbit map. -/
noncomputable def orbitEquiv : N ≃ V := Equiv.ofBijective _ regular

noncomputable def coordinates : V ≃ (Fin d → ZMod p) :=
  (orbitEquiv N a regular).symm.trans (basis.toEquiv.trans Multiplicative.toAdd)

omit [N.Normal] [Fact p.Prime] in
theorem coordinates_orbit (n : N) :
    coordinates N a regular basis (n • a) = (basis n).toAdd := by
  change (basis ((orbitEquiv N a regular).symm ((orbitEquiv N a regular) n))).toAdd = _
  rw [Equiv.symm_apply_apply]

omit [N.Normal] [Fact p.Prime] in
theorem coordinates_base : coordinates N a regular basis a = 0 := by
  simpa only [one_smul, map_one] using coordinates_orbit N a regular basis 1

/-- Ambient conjugation on the actual regular normal subgroup, transported
to the given additive coordinates. -/
def additiveConjugation (g : G) : (Fin d → ZMod p) ≃+ (Fin d → ZMod p) :=
  AddEquiv.toMultiplicative.symm
    (basis.symm.trans ((MulAut.conjNormal (H := N) g).trans basis))

/-- Additivity over the prime field is proved to imply linearity. -/
def linearConjugation (g : G) : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p) :=
  { additiveConjugation N basis g with
    map_smul' := ZMod.map_smul (additiveConjugation N basis g) }

theorem linearConjugation_basis (g : G) (n : N) :
    linearConjugation N basis g (basis n).toAdd =
      (basis (MulAut.conjNormal (H := N) g n)).toAdd := by
  change (basis (MulAut.conjNormal g (basis.symm (basis n)))).toAdd = _
  rw [basis.symm_apply_apply]

/-- The affine identity is derived from the original group action. -/
theorem coordinates_smul (g : G) (v : V) :
    coordinates N a regular basis (g • v) =
      coordinates N a regular basis (g • a) +
        linearConjugation N basis g (coordinates N a regular basis v) := by
  obtain ⟨n, rfl⟩ := regular.surjective v
  obtain ⟨m, hm⟩ := regular.surjective (g • a)
  change m • a = g • a at hm
  have hmG : (m : G) • a = g • a := hm
  have hh : g • (n • a) = (MulAut.conjNormal (H := N) g n * m) • a := by
    change g • ((n : G) • a) =
      ((g * (n : G) * g⁻¹) * (m : G)) • a
    rw [mul_smul, hmG, mul_smul, mul_smul, inv_smul_smul]
  rw [hh, coordinates_orbit, coordinates_orbit, linearConjugation_basis,
    ← hm, coordinates_orbit, map_mul]
  exact add_comm _ _

/-- Both the translation and matrix are constructed from regularity,
normality, and the elementary-abelian coordinates. -/
noncomputable def affineElement (g : G) : AffineGroup (ZMod p) d :=
  ⟨Multiplicative.ofAdd (coordinates N a regular basis (g • a)),
    (matrixLinearEquiv (ZMod p) d).symm (linearConjugation N basis g)⟩

theorem affineElement_action (g : G) :
    affineActionHom (ZMod p) d (affineElement N a regular basis g) =
      relabelPerm (coordinates N a regular basis) (MulAction.toPermHom G V g) := by
  apply Equiv.ext
  intro v
  change coordinates N a regular basis (g • a) +
    matrixLinearEquiv (ZMod p) d
      ((matrixLinearEquiv (ZMod p) d).symm (linearConjugation N basis g)) v =
    coordinates N a regular basis (g • (coordinates N a regular basis).symm v)
  rw [MulEquiv.apply_symm_apply]
  simpa only [Equiv.apply_symm_apply] using
    (coordinates_smul N a regular basis g ((coordinates N a regular basis).symm v)).symm

/-- The recognition map is a homomorphism because the proved physical
action identity identifies its products under a faithful affine action. -/
noncomputable def affineEmbedding : G →* AffineGroup (ZMod p) d where
  toFun := affineElement N a regular basis
  map_one' := by
    apply affineActionHom_injective
    rw [affineElement_action, map_one, map_one, map_one]
  map_mul' g h := by
    apply affineActionHom_injective
    rw [map_mul, affineElement_action, affineElement_action, affineElement_action,
      map_mul, map_mul]

theorem affineEmbedding_injective [FaithfulSMul G V] :
    Function.Injective (affineEmbedding N a regular basis) := by
  intro g h he
  apply MulAction.toPerm_injective (α := G) (β := V)
  apply (relabelPerm (coordinates N a regular basis)).injective
  change affineElement N a regular basis g = affineElement N a regular basis h at he
  have he' := congrArg (affineActionHom (ZMod p) d) he
  rw [affineElement_action, affineElement_action] at he'
  exact he'

/-- The entire affine group acts back on the original vertex type by the
constructed coordinates. -/
noncomputable def physicalAffineAction : AffineGroup (ZMod p) d →* Equiv.Perm V :=
  (relabelPerm (coordinates N a regular basis).symm).toMonoidHom.comp
    (affineActionHom (ZMod p) d)

theorem physicalAffineAction_embedding (g : G) :
    physicalAffineAction N a regular basis (affineEmbedding N a regular basis g) =
      MulAction.toPermHom G V g := by
  change relabelPerm (coordinates N a regular basis).symm
    (affineActionHom (ZMod p) d (affineElement N a regular basis g)) = _
  rw [affineElement_action]
  apply Equiv.ext
  intro v
  change (coordinates N a regular basis).symm
    (coordinates N a regular basis (g •
      (coordinates N a regular basis).symm (coordinates N a regular basis v))) = g • v
  simp only [Equiv.symm_apply_apply]

theorem originalAction_le_affine_range :
    (MulAction.toPermHom G V).range ≤ (physicalAffineAction N a regular basis).range := by
  rintro _ ⟨g, rfl⟩
  exact ⟨affineEmbedding N a regular basis g, physicalAffineAction_embedding N a regular basis g⟩

include N a regular basis in
omit [N.Normal] in
theorem degree_eq [Fintype V] : Fintype.card V = (Fintype.card (ZMod p)) ^ d := by
  rw [Fintype.card_congr (coordinates N a regular basis), Fintype.card_fun, Fintype.card_fin]

end GI.AffineRecognition
