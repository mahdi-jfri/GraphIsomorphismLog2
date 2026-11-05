module

public import Workspace.Impl.LinElementCoordinates
public import Workspace.Impl.LinPermCertificate

@[expose] public section

/-! The integer vector returned by the element-coordinate program has the
right image in every abelian quotient of the supplied permutation group. -/
namespace GI.Impl
open GI.Cited

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linElementCoordinates_map {n : ℕ} (as : List (Equiv.Perm (Fin n)))
    {Q : Type*} [CommGroup Q] (π : gens as →* Q)
    (x : Equiv.Perm (Fin n)) (hx : x ∈ gens as)
    (prog : List SlpInstr) (z : Fin as.length → ℤ)
    (hp : SlpReaches as prog x)
    (hz : linExponentValue (linPrefixVectors as.length 0 as.length) prog = some z) :
    linCoordHom (fun i : Fin as.length => π (linIntoSubgroup (gens as) as[i.val]))
      (Multiplicative.ofAdd z) = π ⟨x, hx⟩ := by
  let A := gens as
  let bs := as.map (linIntoSubgroup A)
  let v (i : Fin as.length) := π (linIntoSubgroup A as[i.val])
  let q := linCoordHom v
  have hbs : bs.map A.subtype = as := linIntoSubgroup_map A as
    (fun a ha => Subgroup.subset_closure ha)
  have hp' : linSlpValue as prog = some x := by
    obtain ⟨es, he, hlast⟩ := hp
    simp only [linSlpValue, linSlpEntries_perm, he, Option.map_some, hlast]
  have hpb : linSlpValue bs prog = some (⟨x, hx⟩ : A) := by
    apply Option.map_injective A.subtype_injective
    rw [← linSlpValue_map, hbs, hp']
    rfl
  have hmatch : bs.map π =
      ((linPrefixVectors as.length 0 as.length).map Multiplicative.ofAdd).map q := by
    simp only [linPrefixVectors, List.replicate_zero, List.nil_append, List.length_finRange,
      List.take_length, List.map_map]
    rw [List.take_of_length_le (by simp)]
    apply List.ext_getElem (by simp [bs])
    intro k hk hk'
    simp only [bs, List.getElem_map, List.getElem_finRange, Function.comp_apply]
    simp only [q, linCoordHom_single, zpow_one, v]
    rfl
  exact linExponent_relation π q bs _ hmatch prog ⟨x, hx⟩ hpb z hz

end GI.Impl
