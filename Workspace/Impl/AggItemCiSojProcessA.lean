import Workspace.Impl.AggItemCiSojProcessL
import Workspace.Impl.AggItemCiSojRows

/-! # Processing either form of a canonical rectangle answer -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens NormalizedFactor)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- An answer row records its physical representative and full projected source
subgroup generators. Each query occurrence has its own row. -/
abbrev itcsProcessRow (rep : RectRep P₀ S L W R) :=
  Option (rep.H × List (permitted W R))

/-- Encoded row after applying this occurrence's target twist. -/
noncomputable def itcsProcessRowVal (rep : RectRep P₀ S L W R) (t : permitted W R)
    (row : itcsProcessRow rep) : Val :=
  itcsRowVal (row.map fun r => ((t * itcsRepMap rep r.1).val.val,
    r.2.map fun g => g.val.val))

/-- The empty branch fits the same polynomial bound. -/
theorem itcs_process_empty_bound (pf : Prim) (n : ℕ) :
    20*(n+10) ≤ itcsProcessC pf n := by
  have hu := itcs_proj_u_ge n
  unfold itcsProcessC itcsProjectB
  omega

/-- Processing a canonical answer gives either an empty row with an empty exact
answer, or a physical answer representative and generators of the full common
source image. All calls satisfy their membership and weight preconditions. -/
theorem itcs_process_answer (hfac : NormalizedFactor)
    {Pg : Program} {f pi gm mp cmp sb sp jfac : ℕ}
    (hf : Pg.funs[f]? = some (itcsProjectF pi gm cmp))
    (hpi : Pg.funs[pi]? = some (liftLabF sb sp jfac)) (hsh : ShiftAt Pg sb)
    (hsp : Pg.HasAt sp (pSplitFuns sp)) (hj : Pg.prims[jfac]? = some (normalizedFactorPrim hfac))
    (hgm : Pg.funs[gm]? = some (itcsGroupMapF mp)) (hm : Pg.HasAt mp (mapFuns mp pi))
    (hc : Pg.HasAt cmp (composeFuns cmp))
    (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R) (M N : W → R → Bool)
    (hs : List (Perm (Fin k) × Perm (Fin L.q))) (hhs : PairGens e L rep.H hs)
    (t : permitted W R) (u : Val) (hu : AnsC e u (rep.state M N t).answer) :
    ∃ row : itcsProcessRow rep,
      (match row with
       | none => (rep.state M N t).answer = ∅
       | some (g,sg) => g.val ∈ (rep.state M N t).answer ∧
           itcsClosure sg = ((itcsPhysicalAut rep M).subgroupOf rep.H).map (itcsRepMap rep)) ∧
      FunDet Pg f (.list [liftLabCtx L.q k (hs.map Prod.swap),u,encPerm t.val.val])
        (itcsProcessRowVal rep t row)
        (itcsProcessC (normalizedFactorPrim hfac)
          (Val.list [liftLabCtx L.q k (hs.map Prod.swap),u,encPerm t.val.val]).wt) := by
  rcases hu with ⟨rfl,hempty⟩ | ⟨x,gs,rfl,-,hcoset⟩
  · exact ⟨none,hempty,(itcs_project_empty _ _ hf).mono
      (itcs_process_empty_bound _ _)⟩
  · obtain ⟨g,hg,hgx,hgs⟩ := itcs_answer_coset e (rep.state M N t) hcoset
    have hH : g ∈ rep.H := hg.1
    let gh : rep.H := ⟨g,hH⟩
    change gens gs = groupFin e (itcsPhysicalAut rep M) at hgs
    let sg := (itcsLiftGens e rep M gs hgs).map (itcsRepMap rep)
    refine ⟨some (gh,sg),⟨hg,itcs_projected_gens e rep M gs hgs⟩,?_⟩
    have hp := itcs_process_local hfac hf hpi hsh hsp hj hgm hm hc e rep M hs hhs gh t gs hgs
    change toFin e gh.val = x at hgx
    rw [hgx] at hp
    simpa only [itcsProcessRowVal,itcsRowVal,Option.map_some,List.map_map,
      Function.comp_def,sg] using hp

end GI.Impl
