import Workspace.Impl.AggItemCiSojModelRows
import Workspace.Impl.AggItemCiSojAnswers
import Workspace.Impl.AggItemCiSojGFRows

/-! # Full source generators from the first nonempty processed occurrence -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm gens)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- Every surviving row supplies generators of exactly the same source image. -/
theorem itcs_processed_source_gens (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (rows : List (permitted W R × itcsProcessRow rep))
    (hv : ∀ row ∈ rows, itcsProcessValid rep M N row.1 row.2)
    {p : permitted W R} {sg : List (permitted W R)}
    (hmem : (p,sg) ∈ itcsNonemptyRows rep rows) :
    itcsClosure sg = ((itcsPhysicalAut rep M).subgroupOf rep.H).map (itcsRepMap rep) := by
  obtain ⟨⟨t,r⟩,hr,he⟩ := List.mem_filterMap.1 hmem
  cases r with
  | none => simp only [Option.map_none,reduceCtorEq] at he
  | some r =>
    simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at he
    have hh := (hv (t,some r) hr).2
    exact he.2 ▸ hh

/-- The actual group constructor reads the leading identity and generators
from the first surviving encoded group and recovers the exact full model group. -/
theorem itcs_group_build_processed {Pg : Program} {f inv mp cmp app : ℕ}
    (hf : Pg.funs[f]? = some (itcsGroupBuildF inv mp app))
    (hi : Pg.HasAt inv (invFuns inv)) (hm : Pg.HasAt mp (mapFuns mp cmp))
    (hc : Pg.HasAt cmp (composeFuns cmp)) (ha : Pg.HasAt app (appendFuns app))
    (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (rows : List (permitted W R × itcsProcessRow rep))
    (horder : rows.map Prod.fst = itcsTwists rep)
    (hv : ∀ row ∈ rows, itcsProcessValid rep M N row.1 row.2)
    (p₀ : permitted W R) (sg₀ : List (permitted W R))
    (tail : List (permitted W R × List (permitted W R)))
    (hfirst : itcsNonemptyRows rep rows = (p₀,sg₀)::tail) :
    let rs := (itcsNonemptyRows rep rows).map Prod.fst
    let sg := 1::sg₀
    let fs := itciMs (itcsFixColor W) (itciOt (itcsFixColor W))
    let ms := itcsLeftGens W R (itcsDiffGens p₀ rs sg)
    gens ms = (leftGroup M).map (alternatingGroup (Fin L.q)).subtype ∧
    FunDet Pg f (.list [.list ((rs.map fun p => p.val.val).map encPerm),
      .list ((sg.map fun p => p.val.val).map encPerm),.list (fs.map encPerm)])
      (.list (ms.map encPerm))
      (itcsGroupBuildC (L.q+rs.length+sg.length+fs.length+2)) := by
  dsimp only
  let phys := rows.map fun r => (r.1,r.2.map Prod.fst)
  have hporder : phys.map Prod.fst = itcsTwists rep := by
    simpa only [phys,List.map_map,Function.comp_def] using horder
  have hpvalid : ∀ row ∈ phys, match row.2 with
      | none => (rep.state M N row.1).answer = ∅
      | some g => g.val ∈ (rep.state M N row.1).answer := by
    intro row hrow
    obtain ⟨⟨t,r⟩,hr,rfl⟩ := List.mem_map.1 hrow
    have hh := hv (t,r) hr
    cases r with
    | none => exact hh
    | some r => exact hh.1
  have hsg := itcs_processed_source_gens rep M N rows hv
    (show (p₀,sg₀) ∈ itcsNonemptyRows rep rows by rw [hfirst]; exact List.mem_cons_self ..)
  have hsg1 : itcsClosure (1::sg₀) = _ := (itcs_closure_one_cons sg₀).trans hsg
  have hrep := itcs_nonempty_rows_reps rep rows
  change (itcsNonemptyRows rep rows).map Prod.fst = itcsAnswerReps rep phys at hrep
  have hp0 : (itcsAnswerReps rep phys)[0]? = some p₀ := by rw [←hrep,hfirst]; rfl
  have hh := itcs_group_build_rows hf hi hm hc ha rep M N phys hporder hpvalid (1::sg₀) hsg1 p₀ hp0
  rw [←hrep] at hh
  exact hh

end GI.Impl
