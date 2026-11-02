import Workspace.Impl.LinFiniteActionCost
import Workspace.Impl.LinMembership
import Workspace.Impl.LinPermCertificate

/-! Lift the cited permutation SLP to the original cover subgroup before
evaluating its full affine action. -/
namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linActionGens {n : ℕ} (gs : List (Equiv.Perm (Fin n))) : List (gens gs) :=
  gs.map (linIntoSubgroup (gens gs))

theorem linActionGens_map {n : ℕ} (gs : List (Equiv.Perm (Fin n))) :
    (linActionGens gs).map (gens gs).subtype = gs :=
  linIntoSubgroup_map (gens gs) gs (fun g hg => Subgroup.subset_closure hg)

theorem linSlpSubgroup_spec {n : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (x : Equiv.Perm (Fin n)) (hx : x ∈ gens gs) (prog : List SlpInstr) (hp : SlpReaches gs prog x) :
    ∃ es : List (gens gs), linSlpEntries (linActionGens gs) prog [] = some es ∧
      es.getLast?.getD 1 = ⟨x, hx⟩ := by
  have hv : linSlpValue gs prog = some x := by
    obtain ⟨es, he, hlast⟩ := hp
    simp only [linSlpValue, linSlpEntries_perm, he, Option.map_some, hlast]
  have hh := linSlpValue_map (gens gs).subtype (linActionGens gs) prog
  rw [linActionGens_map, hv] at hh
  obtain ⟨y, hy, he⟩ := Option.map_eq_some_iff.mp hh.symm
  unfold linSlpValue at hy
  obtain ⟨es, hes, hlast⟩ := Option.map_eq_some_iff.mp hy
  exact ⟨es, hes, Subtype.ext ((congrArg Subtype.val hlast).trans he)⟩

end GI.Impl
