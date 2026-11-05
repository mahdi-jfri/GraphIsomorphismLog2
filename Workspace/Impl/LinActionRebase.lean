module

public import Workspace.Impl.LinActionRestrict

@[expose] public section

/-! A dictionary computed in the old cover is exactly the dictionary for
the restricted subgroup action, with the same full affine coordinates. -/
namespace GI.Impl
open GI.Cited GI.Lang

theorem linFiniteAffineVal_comp {G H : Type*} [Group G] [Group H] {d : ℕ}
    (m : Fin d → ℕ) (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m)
    (F : H →* G) (h : H) :
    linFiniteAffineVal m (ρ.comp F) (c ∘ F) h = linFiniteAffineVal m ρ c (F h) := by
  simp only [linFiniteAffineVal, linFiniteActionMatrix, linFiniteActionLinear,
    MonoidHom.comp_apply, Function.comp_apply, map_inv]

theorem linActionRestricted_cocycle {G H : Type*} [Group G] [Group H] {d : ℕ}
    (m : Fin d → ℕ) (ρ : G →* (linFiniteVec m ≃+ linFiniteVec m)) (c : G → linFiniteVec m)
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (F : H →* G) (g h : H) :
    (c ∘ F) (g * h) = (ρ.comp F) g ((c ∘ F) h) + (c ∘ F) g := by
  simpa only [Function.comp_apply, MonoidHom.comp_apply, map_mul] using hc (F g) (F h)

private theorem linIntoSubgroup_inclusion {G : Type*} [Group G] (K A : Subgroup G)
    (hKA : K ≤ A) (x : G) (hx : x ∈ K) :
    Subgroup.inclusion hKA (linIntoSubgroup K x) = linIntoSubgroup A x := by
  apply Subtype.ext
  change K.subtype (linIntoSubgroup K x) = A.subtype (linIntoSubgroup A x)
  rw [linIntoSubgroup_val K x hx, linIntoSubgroup_val A x (hKA hx)]

theorem linActionRestrictedTable {n d : ℕ} (gs hs : List (Equiv.Perm (Fin n)))
    (hle : gens hs ≤ gens gs) (m : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m) :
    linGroupSlpTable (linFiniteAffineVal m ρ c) (hs.map (linIntoSubgroup (gens gs))) =
      linGroupSlpTable (linFiniteAffineVal m (ρ.comp (Subgroup.inclusion hle))
        (c ∘ Subgroup.inclusion hle)) (linActionGens hs) := by
  unfold linGroupSlpTable linActionGens
  simp only [List.map_map]
  apply congrArg Val.list
  apply List.map_congr_left
  intro x hx
  dsimp only [Function.comp_apply]
  rw [linFiniteAffineVal_comp, linIntoSubgroup_inclusion _ _ hle x (Subgroup.subset_closure hx)]

@[simp] theorem linActionRestrictedIdentity {n d : ℕ} (gs hs : List (Equiv.Perm (Fin n)))
    (hle : gens hs ≤ gens gs) (m : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m) :
    linFiniteAffineVal m (ρ.comp (Subgroup.inclusion hle)) (c ∘ Subgroup.inclusion hle) 1 =
      linFiniteAffineVal m ρ c 1 := by
  rw [linFiniteAffineVal_comp, map_one]

/-- The restriction program consumes the raw generating list returned by the
vector primitive and returns the full dictionary for its subgroup. -/
theorem linActionRestrict_new_spec (h : ConstructiveMembership) {P : Program} {b jm n d : ℕ}
    (hp : linActionRestrictAt P b jm h) (gs hs : List (Equiv.Perm (Fin n)))
    (hle : gens hs ≤ gens gs) (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g) :
    FunDet P b (.list [linActionContext gs m ρ c, .list (hs.map encPerm)])
      (linGroupSlpTable (linFiniteAffineVal m (ρ.comp (Subgroup.inclusion hle))
        (c ∘ Subgroup.inclusion hle)) (linActionGens hs))
      (linActionRestrictCost h (Val.list [linActionContext gs m ρ c, .list (hs.map encPerm)]).wt) := by
  have hmem : ∀ g ∈ hs, g ∈ gens gs := fun g hg => hle (Subgroup.subset_closure hg)
  have he := linIntoSubgroup_map (gens gs) hs hmem
  have he' : (hs.map (linIntoSubgroup (gens gs))).map (fun g => encPerm g.val) = hs.map encPerm := by
    simpa only [List.map_map, Function.comp_def, Subgroup.subtype_apply] using congrArg (List.map encPerm) he
  have hh := linActionRestrict_spec h hp gs m hm ρ c hc (hs.map (linIntoSubgroup (gens gs)))
  change FunDet P b (.list [linActionContext gs m ρ c,
    .list ((hs.map (linIntoSubgroup (gens gs))).map fun g => encPerm g.val)])
    (linGroupSlpTable (linFiniteAffineVal m ρ c) (hs.map (linIntoSubgroup (gens gs)))) _ at hh
  rw [he', linActionRestrictedTable gs hs hle m ρ c] at hh
  exact hh

end GI.Impl
