module

public import Workspace.Impl.LinObjectConfigAdd

@[expose] public section

/-! The action computed through local transporters is affine on W.
Its linear part and translation obey the full group laws. -/
namespace GI.Impl
open GI.Cited GI.Multicoset
variable {n : ℕ} {Q Ω : Type*} [CommGroup Q] [RAct (Equiv.Perm (Fin n)) Ω]

theorem linObjectFiniteConfigAction_eval (B A : Subgroup (Equiv.Perm (Fin n)))
    (hn : Normalizes B A) (Y : Multiset Ω) (hy : ∀ g ∈ B, Conf A Y (Y ↼ g))
    (π : A →* Q) (hπ : Function.Surjective π)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A)
    (g : B) (Z : Multiset Ω) (hZ : Conf A Y Z) :
    linObjectFiniteConfigAction B A hn Y hy π hπ hker g (linObjectConfigCoord A π Y Z) =
      linObjectConfigCoord A π Y (Z ↼ g.val⁻¹) := by
  let E := linObjectConfigEquiv A π hπ Y hker
  change E ((linObjectConfigAction B A hn Y hy g) (E.symm (E ⟨Z, hZ⟩))) = _
  rw [E.symm_apply_apply]
  rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linObjectFiniteConfigAction_affine (B A : Subgroup (Equiv.Perm (Fin n)))
    (hn : Normalizes B A) (Y : Multiset Ω) (hy : ∀ g ∈ B, Conf A Y (Y ↼ g))
    (π : A →* Q) (hπ : Function.Surjective π)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A) :
    ∀ g x y, linObjectFiniteConfigAction B A hn Y hy π hπ hker g (x + y) +
      linObjectFiniteConfigAction B A hn Y hy π hπ hker g 0 =
      linObjectFiniteConfigAction B A hn Y hy π hπ hker g x +
        linObjectFiniteConfigAction B A hn Y hy π hπ hker g y := by
  intro g x y
  let E := linObjectConfigEquiv A π hπ Y hker
  let Z := E.symm x
  let Z' := E.symm y
  let w := coord A Z.val
  let v := coord A Z'.val
  have hw : ∀ T ∈ pieces A Y, w T ∈ A := fun T hT => (coord_spec Z.property hT).1
  have hv : ∀ T ∈ pieces A Y, v T ∈ A := fun T hT => (coord_spec Z'.property hT).1
  have hp : ∀ T ∈ pieces A Y, w T * v T ∈ A := fun T hT => A.mul_mem (hw T hT) (hv T hT)
  have hz : linObjectConfigOf A Y w = Z.val := (conf_coord Z.property).symm
  have hz' : linObjectConfigOf A Y v = Z'.val := (conf_coord Z'.property).symm
  have hcx : linObjectConfigCoord A π Y (linObjectConfigOf A Y w) = x := by
    rw [hz]
    exact E.apply_symm_apply x
  have hcy : linObjectConfigCoord A π Y (linObjectConfigOf A Y v) = y := by
    rw [hz']
    exact E.apply_symm_apply y
  have hcp : linObjectConfigCoord A π Y (linObjectConfigOf A Y (fun T => w T * v T)) = x + y := by
    rw [linObjectConfigOf_mul_coord A π Y hker w v hw hv, hcx, hcy]
  have hzero : linObjectFiniteConfigAction B A hn Y hy π hπ hker g 0 =
      linObjectConfigCoord A π Y (Y ↼ g.val⁻¹) := by
    calc
      _ = linObjectFiniteConfigAction B A hn Y hy π hπ hker g (linObjectConfigCoord A π Y Y) :=
        congrArg (linObjectFiniteConfigAction B A hn Y hy π hπ hker g)
          (linObjectConfigCoord_self A π Y hker).symm
      _ = _ := linObjectFiniteConfigAction_eval B A hn Y hy π hπ hker g Y (conf_self A Y)
  calc
    _ = linObjectConfigCoord A π Y ((linObjectConfigOf A Y (fun T => w T * v T)) ↼ g.val⁻¹) +
        linObjectConfigCoord A π Y (Y ↼ g.val⁻¹) := by
      rw [← hcp, linObjectFiniteConfigAction_eval B A hn Y hy π hπ hker g _
        (linObjectConfigOf_conf A Y _ hp), hzero]
    _ = linObjectConfigCoord A π Y ((linObjectConfigOf A Y w) ↼ g.val⁻¹) +
        linObjectConfigCoord A π Y ((linObjectConfigOf A Y v) ↼ g.val⁻¹) :=
      linObjectConfig_act_add π hn Y (B.inv_mem g.property) (hy _ (B.inv_mem g.property)) hker w v hw hv
    _ = _ := by
      rw [← linObjectFiniteConfigAction_eval B A hn Y hy π hπ hker g _
        (linObjectConfigOf_conf A Y w hw),
        ← linObjectFiniteConfigAction_eval B A hn Y hy π hπ hker g _
        (linObjectConfigOf_conf A Y v hv), hcx, hcy]

noncomputable def linObjectAffineLinear (B A : Subgroup (Equiv.Perm (Fin n)))
    (hn : Normalizes B A) (Y : Multiset Ω) (hy : ∀ g ∈ B, Conf A Y (Y ↼ g))
    (π : A →* Q) (hπ : Function.Surjective π)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A) :
    B →* ((∀ T : {T // T ∈ pieces A Y}, Additive Q ⧸ linObjectGroupImage A π (Aut A T.val)) ≃+
      (∀ T : {T // T ∈ pieces A Y}, Additive Q ⧸ linObjectGroupImage A π (Aut A T.val))) :=
  linActionLinearRep (linObjectFiniteConfigAction B A hn Y hy π hπ hker)
    (linObjectFiniteConfigAction_affine B A hn Y hy π hπ hker)

theorem linObjectAffine_cocycle (B A : Subgroup (Equiv.Perm (Fin n)))
    (hn : Normalizes B A) (Y : Multiset Ω) (hy : ∀ g ∈ B, Conf A Y (Y ↼ g))
    (π : A →* Q) (hπ : Function.Surjective π)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A) (g h : B) :
    linObjectFiniteConfigAction B A hn Y hy π hπ hker (g * h) 0 =
      linObjectAffineLinear B A hn Y hy π hπ hker g
        (linObjectFiniteConfigAction B A hn Y hy π hπ hker h 0) +
          linObjectFiniteConfigAction B A hn Y hy π hπ hker g 0 :=
  linAction_offset_cocycle _ _ g h

end GI.Impl
