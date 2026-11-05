module

public import Workspace.Impl.AggItemCiSojIndexed
public import Workspace.Impl.AggItemCiSojAnswersB

@[expose] public section

/-! # The proved complete saved-answer builder contract -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm NormalizedFactor)

/-- All canonical saved answers produce occurrence-indexed exact physical rows,
full source-image generators, and a uniform cost in actual encoded input weight. -/
def itcsRowsSpec (Pg : Program) (rf : ℕ) (pf : Prim) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (S : State Ω C) (L : GiantLabels S)
    (W R : Finset (Fin L.q)) (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (hs : List (Perm (Fin k) × Perm (Fin L.q))), PairGens e L rep.H hs →
    ∀ (qv av fv : Val) (answers : List Val),
      List.Forall₂ (fun t u => AnsC e u (rep.state M N t).answer) (itcsTwists rep) answers →
      let inp := Val.list [.list [qv,av,fv,liftLabCtx L.q k (hs.map Prod.swap),
        .list ((itcsTwists rep).map fun t => encPerm t.val.val)],.list answers]
      ∃ rows : List (permitted W R × itcsProcessRow rep),
        rows.map Prod.fst=itcsTwists rep ∧
        (∀ row∈rows, itcsProcessValid rep M N row.1 row.2) ∧
        FunDet Pg rf inp (.list (rows.map fun r => itcsProcessRowVal rep r.1 r.2))
          (itcsRowsBound pf inp.wt)

/-- The complete answer-row contract follows from the installed actual range,
map, normalized-factor projection, generator projection, and twist programs.
All factor membership and data-size preconditions were discharged by the
single-answer proof and the actual-input map bound. -/
theorem itcs_rows_spec (hfac : NormalizedFactor)
    {Pg : Program} {f rng rm cb pr pi gm mp cmp sb sp jfac : ℕ}
    (hf : Pg.funs[f]? = some (itcsRowsF rng rm)) (hr : Pg.HasAt rng (rangeFuns rng))
    (hrm : Pg.HasAt rm (mapFuns rm cb)) (hcb : Pg.funs[cb]? = some (itcsRowF pr))
    (hpr : Pg.funs[pr]? = some (itcsProjectF pi gm cmp))
    (hpi : Pg.funs[pi]? = some (liftLabF sb sp jfac)) (hsh : ShiftAt Pg sb)
    (hsp : Pg.HasAt sp (pSplitFuns sp)) (hj : Pg.prims[jfac]? = some (normalizedFactorPrim hfac))
    (hgm : Pg.funs[gm]? = some (itcsGroupMapF mp)) (hm : Pg.HasAt mp (mapFuns mp pi))
    (hc : Pg.HasAt cmp (composeFuns cmp)) :
    itcsRowsSpec Pg f (normalizedFactorPrim hfac) := by
  intro Ω C k e S L W R rep M N hs hhs qv av fv answers ha
  let ts := itcsTwists rep
  have ht : ts.length=answers.length := ha.length_eq
  have hcanon (i : Fin answers.length) :
      AnsC e (answers[i.val]'(i.isLt)) (rep.state M N (ts[i.val]'(by simpa only [ht] using i.isLt))).answer := by
    simpa only [List.get_eq_getElem] using ha.get (i:=i.val)
      (show i.val < ts.length from by rw [ht]; exact i.isLt) i.isLt
  obtain ⟨rs,hvalid,hmap⟩ := itcs_answers_prog hfac hf hr hrm hcb hpr hpi hsh hsp hj hgm hm hc
    e rep M N hs hhs qv av fv ts answers ht hcanon
  let rows := itcsIndexedRows rep ts answers ht rs
  refine ⟨rows,itcs_indexed_order rep ts answers ht rs,itcs_indexed_valid rep M N ts answers ht rs hvalid,?_⟩
  rw [←itcs_indexed_code rep ts answers ht rs] at hmap
  have hn := itcs_answers_length (.list [qv,av,fv,liftLabCtx L.q k (hs.map Prod.swap),
    .list (ts.map fun t => encPerm t.val.val)]) answers
  exact hmap.mono (itcs_rows_bound _ _ hn)

end GI.Impl
