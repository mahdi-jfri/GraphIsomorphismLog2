import Workspace.Impl.AggItemCiSojProcessA
import Workspace.Impl.AggItemCiSojRT

/-! # Processing all saved canonical answers in query order -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm NormalizedFactor)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- Exact semantic content of one processed occurrence. -/
def itcsProcessValid (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (t : permitted W R) : itcsProcessRow rep → Prop
  | none => (rep.state M N t).answer = ∅
  | some (g,sg) => g.val ∈ (rep.state M N t).answer ∧
      itcsClosure sg = ((itcsPhysicalAut rep M).subgroupOf rep.H).map (itcsRepMap rep)

set_option maxHeartbeats 200000 in
/-- The installed range/map programs process every saved canonical answer with
its own recorded twist. The cost is uniform over all canonical representatives. -/
theorem itcs_answers_prog (hfac : NormalizedFactor)
    {Pg : Program} {f rng rm cb pr pi gm mp cmp sb sp jfac : ℕ}
    (hf : Pg.funs[f]? = some (itcsRowsF rng rm)) (hr : Pg.HasAt rng (rangeFuns rng))
    (hrm : Pg.HasAt rm (mapFuns rm cb)) (hcb : Pg.funs[cb]? = some (itcsRowF pr))
    (hpr : Pg.funs[pr]? = some (itcsProjectF pi gm cmp))
    (hpi : Pg.funs[pi]? = some (liftLabF sb sp jfac)) (hsh : ShiftAt Pg sb)
    (hsp : Pg.HasAt sp (pSplitFuns sp)) (hj : Pg.prims[jfac]? = some (normalizedFactorPrim hfac))
    (hgm : Pg.funs[gm]? = some (itcsGroupMapF mp)) (hm : Pg.HasAt mp (mapFuns mp pi))
    (hc : Pg.HasAt cmp (composeFuns cmp))
    (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (hs : List (Perm (Fin k) × Perm (Fin L.q))) (hhs : PairGens e L rep.H hs)
    (qv av fv : Val) (ts : List (permitted W R)) (answers : List Val)
    (ht : ts.length = answers.length)
    (ha : ∀ i : Fin answers.length,
      AnsC e (answers[i.val]'(i.isLt)) (rep.state M N (ts[i.val]'(by simpa only [ht] using i.isLt))).answer) :
    let ctx := liftLabCtx L.q k (hs.map Prod.swap)
    let twists := ts.map fun t => encPerm t.val.val
    let inp := Val.list [.list [qv,av,fv,ctx,.list twists],.list answers]
    ∃ rows : Fin answers.length → itcsProcessRow rep,
      (∀ i, itcsProcessValid rep M N (ts[i.val]'(by simpa only [ht] using i.isLt)) (rows i)) ∧
      FunDet Pg f inp (.list ((List.finRange answers.length).map fun i =>
        itcsProcessRowVal rep (ts[i.val]'(by simpa only [ht] using i.isLt)) (rows i)))
        (itcsRowsC inp answers.length
          (itcsProcessC (normalizedFactorPrim hfac) (10*(inp.wt+10)))) := by
  classical
  dsimp only
  let ctx := liftLabCtx L.q k (hs.map Prod.swap)
  let twists := ts.map fun t => encPerm t.val.val
  let payload := Val.list [qv,av,fv,ctx,.list twists]
  let inp := Val.list [payload,.list answers]
  have hrow (i : Fin answers.length) := itcs_process_answer hfac hpr hpi hsh hsp hj hgm hm hc
    e rep M N hs hhs (ts[i.val]'(by simpa only [ht] using i.isLt)) (answers[i.val]'(i.isLt)) (ha i)
  choose rows hvalid hrows using hrow
  refine ⟨rows,hvalid,?_⟩
  have wpay : payload.wt ≤ inp.wt := st_wt_mem (List.mem_cons_self ..)
  have wctx : ctx.wt ≤ inp.wt := (st_wt_mem (by simp : ctx ∈ [qv,av,fv,ctx,.list twists])).trans wpay
  have wtwists : (Val.list twists).wt ≤ inp.wt :=
    (st_wt_mem (by simp : Val.list twists ∈ [qv,av,fv,ctx,.list twists])).trans wpay
  have wans : (Val.list answers).wt ≤ inp.wt := st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  apply itcs_rows_prog (Cr := itcsProcessC (normalizedFactorPrim hfac) (10*(inp.wt+10))) hf hr hrm hcb qv av fv ctx twists answers
    (by simpa only [twists,List.length_map] using ht)
    (fun i => itcsProcessRowVal rep (ts[i.val]'(by simpa only [ht] using i.isLt)) (rows i))
  intro i
  have hamem : ((answers[i.val]'(i.isLt))) ∈ answers := List.getElem_mem i.isLt
  have wa := (st_wt_mem hamem).trans wans
  have wt : (encPerm (ts[i.val]'(by simpa only [ht] using i.isLt)).val.val).wt ≤ inp.wt := by
    apply (st_wt_mem (vs:=twists) ?_).trans wtwists
    exact List.mem_map.2 ⟨ts[i.val]'(by simpa only [ht] using i.isLt),List.getElem_mem (by simpa only [ht] using i.isLt),rfl⟩
  have wi := wt_list3_le ctx (answers[i.val]'(i.isLt)) (encPerm (ts[i.val]'(by simpa only [ht] using i.isLt)).val.val)
  have hbound : (Val.list [ctx,(answers[i.val]'(i.isLt)),encPerm (ts[i.val]'(by simpa only [ht] using i.isLt)).val.val]).wt ≤ 10*(inp.wt+10) := by omega
  have hp := (hrows i).mono (itcs_process_mono _ hbound)
  simpa only [twists,List.getElem_map] using hp

end GI.Impl
