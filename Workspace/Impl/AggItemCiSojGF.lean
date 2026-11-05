module

public import Workspace.Impl.AggItemCiSojGB
public import Workspace.Impl.AggItemCiSojFO

@[expose] public section

/-! # The generator constructor returns exactly the full model group -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (gens encPerm)

/-- The identity prepended by `encGroup` does not change the generated subgroup. -/
theorem itcs_closure_one_cons {G : Type*} [Group G] (ls : List G) :
    itcsClosure (1::ls) = itcsClosure ls := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact (itcsClosure ls).one_mem
    · exact Subgroup.subset_closure hg
  · exact Subgroup.closure_mono (fun _ h=>List.mem_cons_of_mem _ h)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- The actual inverse/map/append program generates the exact full-label group,
using the complete projected answer cosets and source generators. -/
theorem itcs_group_build_full {Pg : Program} {f inv mp cmp app : ℕ}
    (hf : Pg.funs[f]? = some (itcsGroupBuildF inv mp app))
    (hi : Pg.HasAt inv (invFuns inv)) (hm : Pg.HasAt mp (mapFuns mp cmp))
    (hc : Pg.HasAt cmp (composeFuns cmp)) (ha : Pg.HasAt app (appendFuns app))
    (rep : RectRep P₀ S L W R) (M N : W → R → Bool) (rr : permitted W R → Option rep.H)
    (hr : ∀ t ∈ itcsTwists rep,match rr t with
      | none => (rep.state M N t).answer=∅
      | some g => g.val∈(rep.state M N t).answer)
    (sg : List (permitted W R))
    (hsg : itcsClosure sg=((itcsPhysicalAut rep M).subgroupOf rep.H).map (itcsRepMap rep))
    (p₀ : permitted W R) (h₀ : (itcsCosetReps rep rr)[0]?=some p₀) :
    let rs := itcsCosetReps rep rr
    let fs := itciMs (itcsFixColor W) (itciOt (itcsFixColor W))
    let ms := itcsLeftGens W R (itcsDiffGens p₀ rs sg)
    gens ms=(leftGroup M).map (alternatingGroup (Fin L.q)).subtype ∧
    FunDet Pg f (.list [.list ((rs.map fun p=>p.val.val).map encPerm),
      .list ((sg.map fun p=>p.val.val).map encPerm),.list (fs.map encPerm)])
      (.list (ms.map encPerm))
      (itcsGroupBuildC (L.q+rs.length+sg.length+fs.length+2)) := by
  dsimp only
  have hg := itcs_coset_generators rep M N rr hr sg hsg (List.mem_of_getElem? h₀)
  refine ⟨itcs_left_gens M _ hg, ?_⟩
  have hp := itcs_group_build_prog hf hi hm hc ha
    ((itcsCosetReps rep rr).map fun p=>p.val.val) (sg.map fun p=>p.val.val)
    (itciMs (itcsFixColor W) (itciOt (itcsFixColor W))) p₀.val.val
    (by rw [List.getElem?_map,h₀]; rfl)
  have he : (((itcsCosetReps rep rr).map fun p=>p.val.val).map (p₀.val.val⁻¹ * ·)++
      sg.map (fun p=>p.val.val))++itciMs (itcsFixColor W) (itciOt (itcsFixColor W)) =
      itcsLeftGens W R (itcsDiffGens p₀ (itcsCosetReps rep rr) sg) := by
    simp only [itcsLeftGens,itcsDiffGens,List.map_append,List.map_map,Function.comp_def,
      Subgroup.coe_mul,Subgroup.coe_inv]
  rw [he] at hp
  simpa only [List.length_map] using hp

end GI.Impl
