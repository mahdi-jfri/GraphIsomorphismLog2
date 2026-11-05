module

public import Workspace.Impl.AggItemCiSojFinalStages
public import Workspace.Impl.AggItemCiSojProcessedG

@[expose] public section

/-! # The full finalizer on nonempty exact rectangle answers -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
/-- The actual nonempty finalizer reconstructs the full left group and all
model overcosets, within a polynomial of its actual encoded input weight. -/
theorem itcs_finalize_some {Pg : Program} {f rf flt ne fm fb gb inv mp cmp app ovs ov Cr : ℕ}
    (hf : Pg.funs[f]? = some (itcsFinishF rf flt fm gb ovs))
    (hflt : Pg.HasAt flt (filterFuns flt ne)) (hne : Pg.funs[ne]? = some itcsRowNE)
    (hfm : Pg.HasAt fm (mapFuns fm fb)) (hfb : Pg.funs[fb]? = some krFstF)
    (hgb : Pg.funs[gb]? = some (itcsGroupBuildF inv mp app))
    (hi : Pg.HasAt inv (invFuns inv)) (hm : Pg.HasAt mp (mapFuns mp cmp))
    (hc : Pg.HasAt cmp (composeFuns cmp)) (ha : Pg.HasAt app (appendFuns app))
    (ho : Pg.HasAt ovs (mapFuns ovs ov)) (hov : Pg.funs[ov]? = some (itcsOverF cmp))
    (pf : Prim) (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (a₀ : alternatingGroup (Fin L.q))
    (rows : List (permitted W R × itcsProcessRow rep))
    (horder : rows.map Prod.fst=itcsTwists rep)
    (hv : ∀ row∈rows, itcsProcessValid rep M N row.1 row.2)
    (p₀ : permitted W R) (sg₀ : List (permitted W R))
    (tail : List (permitted W R × List (permitted W R)))
    (hfirst : itcsNonemptyRows rep rows=(p₀,sg₀)::tail) (ctx twists answers : Val)
    (hr : FunDet Pg rf
      (.list [.list [.nat L.q,encPerm a₀.val,
        .list ((itciMs (itcsFixColor W) (itciOt (itcsFixColor W))).map encPerm),ctx,twists],answers])
      (.list (rows.map fun r => itcsProcessRowVal rep r.1 r.2)) Cr)
    (hCr : Cr≤ itcsRowsBound pf (Val.list [.list [.nat L.q,encPerm a₀.val,
      .list ((itciMs (itcsFixColor W) (itciOt (itcsFixColor W))).map encPerm),ctx,twists],answers]).wt) :
    let inp := Val.list [.list [.nat L.q,encPerm a₀.val,
      .list ((itciMs (itcsFixColor W) (itciOt (itcsFixColor W))).map encPerm),ctx,twists],answers]
    ∃ os, FunDet Pg f inp (itcsResV (itciOV os)) (itcsFinalC pf inp.wt) ∧
      ItSOut e L (itcsRowsModel rep M N a₀ rows) [] os := by
  dsimp only
  let fs := itciMs (itcsFixColor W) (itciOt (itcsFixColor W))
  let fix := Val.list (fs.map encPerm)
  let inp := Val.list [.list [.nat L.q,encPerm a₀.val,fix,ctx,twists],answers]
  let WI := inp.wt
  let surviving := itcsNonemptyRows rep rows
  let rs := surviving.map Prod.fst
  let rsP := rs.map fun p => p.val.val
  let sg := 1::sg₀
  let ms := itcsLeftGens W R (itcsDiffGens p₀ rs sg)
  let raw := rows.map fun r => itcsProcessRowVal rep r.1 r.2
  let filtered := Val.list (surviving.map fun p =>
    .list [encPerm p.1.val.val,encGroup (p.2.map fun g => g.val.val)])
  let reps := Val.list (rsP.map encPerm)
  let msV := Val.list (ms.map encPerm)
  let os := itcsRowsOut rep M a₀ rows ms
  let more : List Val := tail.map fun p => .list [encPerm p.1.val.val,encGroup (p.2.map fun g => g.val.val)]
  let source := Val.list ((sg.map fun p => p.val.val).map encPerm)
  have wInput := itcs_final_input_weights a₀.val (.nat L.q) fix ctx twists answers
  change L.q≤ WI ∧ fix.wt≤ WI ∧ ctx.wt≤ WI ∧ (encPerm a₀.val).wt≤ WI at wInput
  rcases itcs_final_envelopes pf WI with ⟨hW0,hR0,h01,hF1,h12,hP2,h23,hG3,h34,hO4⟩
  have hW2 := hW0.trans (h01.trans h12)
  have hW3 := hW2.trans h23
  have hW4 := hW3.trans h34
  have hR4 := hR0.trans (h01.trans (h12.trans (h23.trans h34)))
  have hF4 := hF1.trans (h12.trans (h23.trans h34))
  have hP4 := hP2.trans (h23.trans h34)
  have hG4 := hG3.trans h34
  have rowsDet : FunDet Pg rf inp (.list raw) (itcsRowsBound pf WI) := hr.mono hCr
  obtain ⟨filterDet,hn⟩ := itcs_final_filter_stage hflt hne pf rep rows inp hr hCr
  change FunDet Pg flt (.list [.nat 0,.list raw]) filtered (itcsFilterB (itcsFinalU0 pf WI)) at filterDet
  have wf : filtered.wt≤ itcsFilterB (itcsFinalU0 pf WI) := itcs_det_weight filterDet
  have firstDet := itcs_final_firsts_stage hfm hfb pf WI surviving hn wf
  have heReps : surviving.map (fun p => encPerm p.1.val.val) = rsP.map encPerm := by
    simp only [rsP,rs,List.map_map,Function.comp_def]
  rw [heReps] at firstDet
  change FunDet Pg fm (.list [.nat 0,filtered]) reps (itcsFirstB (itcsFinalU1 pf WI)) at firstDet
  have wp : reps.wt≤ itcsFirstB (itcsFinalU1 pf WI) := itcs_det_weight firstDet
  have hsLen : sg.length≤ itcsFilterB (itcsFinalU0 pf WI) :=
    (itcs_typed_source_length surviving p₀ sg₀ tail hfirst).trans wf
  have hfLen : fs.length≤ WI := by
    have hh := (length_lt_wt_list (fs.map encPerm)).le
    simp only [List.length_map] at hh
    exact hh.trans wInput.2.1
  have hrLen : rs.length≤ itcsFinalU0 pf WI := by simpa only [rs,List.length_map] using hn
  have hgSize := itcs_group_size_bound (wInput.1.trans hW2)
    (hrLen.trans (h01.trans h12)) (hsLen.trans (hF1.trans h12)) (hfLen.trans hW2)
  obtain ⟨hGen,groupDet⟩ := itcs_group_build_processed hgb hi hm hc ha rep M N rows horder hv p₀ sg₀ tail hfirst
  have groupB : FunDet Pg gb (.list [reps,source,fix]) msV
      (itcsGroupBuildC (10*itcsFinalU2 pf WI+10)) := groupDet.mono (itcs_group_build_mono hgSize)
  have wg : msV.wt≤ itcsGroupBuildC (10*itcsFinalU2 pf WI+10) := itcs_det_weight groupB
  have wover : (Val.list [.list [encPerm a₀.val,msV],reps]).wt≤ itcsFinalU3 pf WI :=
    itcs_over_input_pad _ _ _ (wInput.2.2.2.trans hW2) wg (wp.trans hP2)
  have hrpLen : rsP.length≤ itcsFinalU3 pf WI := by
    simpa only [rsP,List.length_map] using hrLen.trans (h01.trans (h12.trans h23))
  have overDet := itcs_over_table ho hov hc a₀.val rsP ms
  have overBound := itcs_over_bound a₀.val rsP ms (wInput.1.trans hW3) hrpLen (wg.trans hG3) wover
  have overB := overDet.mono overBound
  have heOver : (Val.list (rsP.map fun r => lcOv (a₀.val*r) ms)) = itciOV os := by
    simp only [itciOV,os,itcsRowsOut,rsP,rs,surviving,List.map_map,Function.comp_def,Subgroup.coe_mul]
  rw [heOver] at overB
  have heFiltered : filtered = .list (.list [encPerm p₀.val.val,.list [.nat L.q,source]]::more) := by
    change Val.list ((itcsNonemptyRows rep rows).map fun p =>
      .list [encPerm p.1.val.val,encGroup (p.2.map fun g => g.val.val)]) = _
    rw [hfirst]
    rfl
  rw [heFiltered] at filterDet firstDet
  have result := itcs_finish_nonempty hf (.nat L.q) (encPerm a₀.val) fix ctx twists answers
    (encPerm p₀.val.val) (.nat L.q) source reps msV (itciOV os) raw more
    rowsDet filterDet firstDet groupB overB
  refine ⟨os,result.mono (itcs_finish_bound hW4 hR4 hF4 hP4 hG4 hO4),?_⟩
  exact itcs_rows_out e rep M N a₀ rows (itcs_processed_physical_valid rep M N rows hv) ms (fun _ => hGen)

end GI.Impl
