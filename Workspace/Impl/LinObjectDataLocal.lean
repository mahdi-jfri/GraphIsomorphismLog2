import Workspace.Impl.LinObjectDataMath

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

def linListGetCast {α : Type*} {p : ℕ} (xs : List α) (h : p = xs.length) (i : Fin p) : α :=
  xs.get (i.cast h)

theorem linListGetCast_encoding {α : Type*} {p : ℕ} (xs : List α) (h : p = xs.length) :
    (List.finRange p).map (linListGetCast xs h) = xs := by
  subst p
  exact linList_finRange_get xs

set_option maxHeartbeats 100000 in
set_option maxRecDepth 300 in
theorem linObjectData_local_collection (hc : ConstructiveMembership)
    {P : Program} {b jm n : ℕ} (h : linObjectLocalRelationsAt P b jm hc)
    {Q : Type*} [CommGroup Q] (as ns : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (refs : List (List (TmRiO n))) (bss : List (List (Equiv.Perm (Fin n))))
    (M : Matrix (Fin as.length) (Fin as.length) ℤ) (hM : linPermPresentation ns as M)
    (hB : List.Forall₂ (fun S bs => gens bs = Aut (gens as) (tmGlMs S) ∧ bs.length ≤ n ^ 2) refs bss) :
    let ctx := Val.list [encGroup as, encIntMatrix M, encFun (fun i : Fin (n ^ 2 + 1) => i.val),
      encFun (fun i : Fin as.length => i.val)]
    let a := Val.list [ctx, .list (bss.map encGroup)]
    FunAll P b a (fun out cost =>
      (∃ L : Fin refs.length → Matrix (Fin (as.length + (n ^ 2 + 1))) (Fin as.length) ℤ,
        out = .list ((List.finRange refs.length).map fun i => encIntMatrix (L i)) ∧
        (∀ i, ∃ C : Matrix (Fin (n ^ 2 + 1)) (Fin as.length) ℤ,
          L i = linRowStack M C ∧ (linRelations C).map (linObjectLiftCoord as π) =
            linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs (refs.get i)))) ∧
        (∀ i, Function.Injective (L i).mulVec)) ∧
      cost ≤ linObjectLocalRelationsCost hc a.wt) := by
  have hbs : ∀ bs ∈ bss, ∀ x ∈ bs, x ∈ gens as := by
    intro bs hbs x hx
    obtain ⟨S, _, hS⟩ := linForall₂_mem_right hB hbs
    have ha : gens bs ≤ gens as := by rw [hS.1]; exact aut_le _ _
    exact ha (Subgroup.subset_closure hx)
  have hN : ∀ bs ∈ bss, (1 :: bs).length ≤ n ^ 2 + 1 := by
    intro bs hbs
    obtain ⟨S, _, hS⟩ := linForall₂_mem_right hB hbs
    simpa only [List.length_cons] using Nat.add_le_add_right hS.2 1
  refine (linObjectLocalRelations_spec hc h as bss hbs hN M π).mono fun out cost ho => ?_
  obtain ⟨⟨Ms, rfl, hMs⟩, hcost⟩ := ho
  have hcert := linObjectData_local_cert as π refs bss M hB Ms hMs
  let L := linListGetCast Ms hcert.length_eq
  have henc : (List.finRange refs.length).map (fun i => encIntMatrix (L i)) = Ms.map encIntMatrix := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map encIntMatrix) (linListGetCast_encoding Ms hcert.length_eq)
  have hlocal (i : Fin refs.length) : ∃ C : Matrix (Fin (n ^ 2 + 1)) (Fin as.length) ℤ,
      L i = linRowStack M C ∧ (linRelations C).map (linObjectLiftCoord as π) =
        linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs (refs.get i))) :=
    hcert.get i.isLt (i.cast hcert.length_eq).isLt
  refine ⟨⟨L, congrArg Val.list henc.symm, hlocal, ?_⟩, hcost⟩
  intro i
  obtain ⟨C, he, _⟩ := hlocal i
  rw [he]
  exact linObjectRowStack_injective M C (linObjectPresentation_mulVec_injective M (linPermPresentation_det hM))

end GI.Impl
