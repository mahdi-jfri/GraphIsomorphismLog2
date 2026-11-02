import Workspace.RadicalSocleIdempotent
namespace GI.RadicalSocle

variable {G : Type*} [Group G]

/-- An automorphism permutes the actual minimal normal subgroups. -/
def minimalNormalPerm (e : MulAut G) : Equiv.Perm (MinimalNormals G) where
  toFun N := ⟨N.val.map e.toMonoidHom, N.property.map e⟩
  invFun N := ⟨N.val.map e.symm.toMonoidHom, N.property.map e.symm⟩
  left_inv N := by
    apply Subtype.ext
    change (N.val.map e.toMonoidHom).map e.symm.toMonoidHom = N.val
    have h : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext x
      exact e.symm_apply_apply x
    rw [Subgroup.map_map, h, Subgroup.map_id]
  right_inv N := by
    apply Subtype.ext
    change (N.val.map e.symm.toMonoidHom).map e.toMonoidHom = N.val
    have h : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by
      ext x
      exact e.apply_symm_apply x
    rw [Subgroup.map_map, h, Subgroup.map_id]

def minimalNormalAction : MulAut G →* Equiv.Perm (MinimalNormals G) where
  toFun := minimalNormalPerm
  map_one' := by
    apply Equiv.ext
    intro N
    apply Subtype.ext
    exact Subgroup.map_id N.val
  map_mul' e f := by
    apply Equiv.ext
    intro N
    apply Subtype.ext
    change N.val.map (e * f).toMonoidHom =
      (N.val.map f.toMonoidHom).map e.toMonoidHom
    rw [Subgroup.map_map]
    rfl

theorem minimalNormalAction_apply (e : MulAut G) (N : MinimalNormals G) :
    (minimalNormalAction e N).val = N.val.map e.toMonoidHom := rfl

abbrev FactorKernel (G : Type*) [Group G] := (minimalNormalAction (G := G)).ker

theorem factorKernel_map_eq (e : FactorKernel G) (N : MinimalNormals G) :
    N.val.map e.val.toMonoidHom = N.val :=
  congrArg (fun p : Equiv.Perm (MinimalNormals G) => (p N).val) e.property

/-- Restriction to a preserved factor is an actual automorphism of it. -/
def factorKernelRestriction (e : FactorKernel G) (N : MinimalNormals G) : MulAut N.val :=
  (e.val.subgroupMap N.val).trans (MulEquiv.subgroupCongr (factorKernel_map_eq e N))

theorem factorKernelRestriction_apply (e : FactorKernel G) (N : MinimalNormals G)
    (x : N.val) : (factorKernelRestriction e N x : G) = e.val x := rfl

def factorKernelHom : FactorKernel G →* (∀ N : MinimalNormals G, MulAut N.val) where
  toFun := factorKernelRestriction
  map_one' := by
    funext N
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  map_mul' e f := by
    funext N
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl

/-- Agreement on every factor implies agreement on their generated group. -/
theorem factorKernelHom_injective (hsoc : socle G = ⊤) :
    Function.Injective (factorKernelHom (G := G)) := by
  intro e f hef
  have hle : socle G ≤ e.val.toMonoidHom.eqLocus f.val.toMonoidHom := by
    rw [socle_eq_iSup]
    apply iSup_le
    intro N x hx
    have h := congrArg (fun z : ∀ M : MinimalNormals G, MulAut M.val =>
      (z N ⟨x, hx⟩ : G)) hef
    exact h
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  exact hle (by rw [hsoc]; exact Subgroup.mem_top x)

/-- In particular, the actual socle has no additional invisible automorphisms
in the kernel of its actual permutation action on simple factors. -/
theorem socle_factorKernelHom_injective [Finite G] :
    Function.Injective (factorKernelHom (G := socle G)) :=
  factorKernelHom_injective socle_idempotent

end GI.RadicalSocle
