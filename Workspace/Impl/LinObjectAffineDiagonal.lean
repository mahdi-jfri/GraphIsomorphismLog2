import Workspace.Impl.LinObjectAffineAction
import Workspace.Impl.LinDescendAction

namespace GI.Impl
open GI.Cited GI.Multicoset
variable {n : ℕ} {Q Ω : Type*} [CommGroup Q] [RAct (Equiv.Perm (Fin n)) Ω]

theorem linObjectFiniteConfigAction_zero (B A : Subgroup (Equiv.Perm (Fin n)))
    (hn : Normalizes B A) (Y : Multiset Ω) (hy : ∀ g ∈ B, Conf A Y (Y ↼ g))
    (π : A →* Q) (hπ : Function.Surjective π)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A) (g : B) :
    linObjectFiniteConfigAction B A hn Y hy π hπ hker g 0 =
      linObjectConfigCoord A π Y (Y ↼ g.val⁻¹) := by
  calc
    _ = linObjectFiniteConfigAction B A hn Y hy π hπ hker g (linObjectConfigCoord A π Y Y) :=
      congrArg (linObjectFiniteConfigAction B A hn Y hy π hπ hker g)
        (linObjectConfigCoord_self A π Y hker).symm
    _ = _ := linObjectFiniteConfigAction_eval B A hn Y hy π hπ hker g Y (conf_self A Y)

theorem linObjectConfigCoord_constant (A : Subgroup (Equiv.Perm (Fin n))) (π : A →* Q)
    (Y : Multiset Ω) (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A) (a : A) :
    linObjectConfigCoord A π Y (linObjectConfigOf A Y (fun _ => a.val)) =
      linObjectDiagonal (fun T : {T // T ∈ pieces A Y} => linObjectGroupImage A π (Aut A T.val))
        (Additive.ofMul (π a)) := by
  funext T
  exact linObjectConfigOf_coord A π Y hker _ (fun _ _ => a.property) T

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem linObjectAffineLinear_diagonal (B A : Subgroup (Equiv.Perm (Fin n)))
    (hn : Normalizes B A) (Y : Multiset Ω) (hy : ∀ g ∈ B, Conf A Y (Y ↼ g))
    (π : A →* Q) (hπ : Function.Surjective π)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A) (g : B) (a : A) :
    ∃ hc : g.val * a.val * g.val⁻¹ ∈ A,
      linObjectAffineLinear B A hn Y hy π hπ hker g
        (linObjectDiagonal (fun T : {T // T ∈ pieces A Y} => linObjectGroupImage A π (Aut A T.val))
          (Additive.ofMul (π a))) =
        linObjectDiagonal (fun T : {T // T ∈ pieces A Y} => linObjectGroupImage A π (Aut A T.val))
          (Additive.ofMul (π ⟨g.val * a.val * g.val⁻¹, hc⟩)) := by
  have hc := hn g.val g.property a.val a.property
  refine ⟨hc, ?_⟩
  change linObjectFiniteConfigAction B A hn Y hy π hπ hker g _ -
    linObjectFiniteConfigAction B A hn Y hy π hπ hker g 0 = _
  rw [← linObjectConfigCoord_constant A π Y hker a,
    linObjectFiniteConfigAction_eval B A hn Y hy π hπ hker g _
      (linObjectConfigOf_conf A Y _ (fun _ _ => a.property)),
    linObjectFiniteConfigAction_zero B A hn Y hy π hπ hker g]
  funext T
  obtain ⟨hm, he⟩ := linObjectConfigCoord_act_repr π hn Y _ (B.inv_mem g.property)
    (hy _ (B.inv_mem g.property)) (linObjectConfigOf_conf A Y _ (fun _ _ => a.property)) hker
    (fun _ => a.val) (fun _ _ => a.property)
    (fun T hT => partAt_conf hT (fun _ _ => a.property)) T
  simp only [Pi.sub_apply, he, inv_inv]
  let u : A := ⟨coord A (Y ↼ g.val⁻¹) T.val, (coord_spec (hy _ (B.inv_mem g.property)) T.property).1⟩
  let c : A := ⟨g.val * a.val * g.val⁻¹, hc⟩
  have hu : linIntoSubgroup A (coord A (Y ↼ g.val⁻¹) T.val) = u :=
    Subtype.ext (linIntoSubgroup_val A _ (coord_spec (hy _ (B.inv_mem g.property)) T.property).1)
  change (linObjectGroupImage A π (Aut A T.val)).mkQ (Additive.ofMul (π (u * c))) -
    (linObjectGroupImage A π (Aut A T.val)).mkQ (Additive.ofMul (π (linIntoSubgroup A _))) = _
  rw [hu, map_mul]
  change (linObjectGroupImage A π (Aut A T.val)).mkQ (Additive.ofMul (π u) + Additive.ofMul (π c)) -
    (linObjectGroupImage A π (Aut A T.val)).mkQ (Additive.ofMul (π u)) =
      (linObjectGroupImage A π (Aut A T.val)).mkQ (Additive.ofMul (π c))
  rw [map_add]
  exact add_sub_cancel_left _ _

theorem linObjectAffineLinear_preserves_diagonal (B A : Subgroup (Equiv.Perm (Fin n)))
    (hn : Normalizes B A) (Y : Multiset Ω) (hy : ∀ g ∈ B, Conf A Y (Y ↼ g))
    (π : A →* Q) (hπ : Function.Surjective π)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A) (g : B)
    (w : ∀ T : {T // T ∈ pieces A Y}, Additive Q ⧸ linObjectGroupImage A π (Aut A T.val)) :
    let D := LinearMap.range (linObjectDiagonal
      (fun T : {T // T ∈ pieces A Y} => linObjectGroupImage A π (Aut A T.val)))
    D.mkQ w = 0 → D.mkQ (linObjectAffineLinear B A hn Y hy π hπ hker g w) = 0 := by
  intro D hw
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at hw ⊢
  obtain ⟨q, rfl⟩ := hw
  obtain ⟨a, ha⟩ := hπ q.toMul
  have hq : Additive.ofMul (π a) = q := congrArg Additive.ofMul ha
  rw [← hq]
  obtain ⟨hc, he⟩ := linObjectAffineLinear_diagonal B A hn Y hy π hπ hker g a
  exact ⟨Additive.ofMul (π ⟨_, hc⟩), he.symm⟩

end GI.Impl
