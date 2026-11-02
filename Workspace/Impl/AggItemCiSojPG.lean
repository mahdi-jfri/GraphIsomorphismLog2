import Workspace.Impl.AggItemCiSojAC

/-!
# Projecting the complete source generators

Lift each canonical generator through the inverse of the position equivalence.
Its membership in the physical source automorphism group proves that this lift
belongs to the representation subgroup. The stored label homomorphism then
projects exactly the full source subgroup, rather than only some sound elements.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Rectangle Equiv Equiv.Perm
open GI.Cited (gens)
open scoped Pointwise

/-- Closure commutes with the finite generator list's homomorphic image. -/
theorem itcs_closure_hom {G H : Type*} [Group G] [Group H] (f : G →* H) (gs : List G) :
    itcsClosure (gs.map f) = (itcsClosure gs).map f := by
  unfold itcsClosure
  rw [MonoidHom.map_closure]
  congr 1
  ext h
  simp

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- Each canonical source generator has its unique physical lift in `H`. -/
noncomputable def itcsLiftGens (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R)
    (M : W → R → Bool) (gs : List (Perm (Fin k)))
    (hgs : gens gs = groupFin e (itcsPhysicalAut rep M)) : List rep.H :=
  gs.attach.map fun a => ⟨(toFin e).symm a.val, by
    have ha : a.val ∈ groupFin e (itcsPhysicalAut rep M) := hgs ▸ Subgroup.subset_closure a.property
    exact ((mem_groupFin_iff e _ _).1 ha).1⟩

/-- Forgetting the subgroup witnesses gives the unique physical lifts. -/
theorem itcs_lift_gens_val (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R)
    (M : W → R → Bool) (gs : List (Perm (Fin k)))
    (hgs : gens gs = groupFin e (itcsPhysicalAut rep M)) :
    (itcsLiftGens e rep M gs hgs).map rep.H.subtype = gs.map (toFin e).symm := by
  simp only [itcsLiftGens, List.map_map]
  exact List.attach_map_val (l := gs) (f := fun a => (toFin e).symm a)

/-- The lifted generators generate the full source subgroup inside `H`. -/
theorem itcs_lift_gens (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R)
    (M : W → R → Bool) (gs : List (Perm (Fin k)))
    (hgs : gens gs = groupFin e (itcsPhysicalAut rep M)) :
    itcsClosure (itcsLiftGens e rep M gs hgs) = (itcsPhysicalAut rep M).subgroupOf rep.H := by
  have himage : (itcsClosure (itcsLiftGens e rep M gs hgs)).map rep.H.subtype =
      itcsPhysicalAut rep M := by
    rw [← itcs_closure_hom, itcs_lift_gens_val]
    change itcsClosure (gs.map (toFin e).symm.toMonoidHom) = _
    rw [itcs_closure_hom]
    change (gens gs).map (toFin e).symm.toMonoidHom = _
    rw [hgs]
    ext g
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, he⟩
      have he' : b = g := by
        simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using he
      exact he' ▸ hb
    · intro hg
      exact ⟨toFin e g, ⟨g, hg, rfl⟩, (toFin e).symm_apply_apply g⟩
  ext h
  constructor
  · intro hh
    have hv : h.val ∈ (itcsClosure (itcsLiftGens e rep M gs hgs)).map rep.H.subtype := ⟨h, hh, rfl⟩
    rwa [himage] at hv
  · intro hh
    have hv : h.val ∈ (itcsClosure (itcsLiftGens e rep M gs hgs)).map rep.H.subtype := himage ▸ hh
    obtain ⟨h', hh', he⟩ := hv
    exact (Subtype.ext he : h' = h) ▸ hh'

/-- Projected canonical generators generate exactly the label image of the full
physical source automorphism subgroup. -/
theorem itcs_projected_gens (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R)
    (M : W → R → Bool) (gs : List (Perm (Fin k)))
    (hgs : gens gs = groupFin e (itcsPhysicalAut rep M)) :
    itcsClosure ((itcsLiftGens e rep M gs hgs).map (itcsRepMap rep)) =
      ((itcsPhysicalAut rep M).subgroupOf rep.H).map (itcsRepMap rep) := by
  rw [itcs_closure_hom, itcs_lift_gens]

end GI.Impl
