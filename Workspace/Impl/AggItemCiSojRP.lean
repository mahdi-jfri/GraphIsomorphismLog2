import Workspace.Impl.AggItemCiSojPi
import Workspace.Impl.AggItemCiSojAns

/-!
# Label projection using the rectangle's own stored graph

The representation value records graph generators for `H`. A canonical answer
representative and each of its generators belong to `H`. Swapping this graph
therefore computes their exact permitted label images, using the existing lift
program and its normalized-factor routine.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm NormalizedFactor)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- The representation's graph contains the physical element and its permitted image. -/
theorem itcs_rep_pi_precondition (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R)
    {hs : List (Perm (Fin k) × Perm (Fin L.q))} (hhs : PairGens e L rep.H hs)
    (g : rep.H) :
    ∃ a, (a, toFin e g.val) ∈ Subgroup.closure {p | p ∈ hs.map Prod.swap} := by
  rw [itcs_swapped_gens, hhs]
  refine ⟨(itcsRepMap rep g).val.val, ?_⟩
  exact ⟨(toFin e g.val, (itcsRepMap rep g).val.val),
    (mem_graphOf e L).2 ⟨g.val, rep.le g.property, g.property, rfl, rfl⟩, rfl⟩

/-- The stored homomorphism fixes the projected label uniquely. -/
theorem itcs_rep_pi_unique (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R)
    {hs : List (Perm (Fin k) × Perm (Fin L.q))} (hhs : PairGens e L rep.H hs)
    (g : rep.H) {a : Perm (Fin L.q)}
    (ha : (a, toFin e g.val) ∈ Subgroup.closure {p | p ∈ hs.map Prod.swap}) :
    a = (itcsRepMap rep g).val.val := by
  rw [itcs_swapped_gens, hhs] at ha
  obtain ⟨p, hp, he⟩ := ha
  obtain ⟨g', hg', hH, hf, hl⟩ := (mem_graphOf e L).1 hp
  have hp1 : p.1 = toFin e g.val := congrArg Prod.snd he
  have hp2 : p.2 = a := congrArg Prod.fst he
  have hg : g' = g.val := (toFin e).injective (hf.trans hp1)
  subst g'
  exact hp2.symm.trans hl.symm

/-- Exact projection of any answer element through the rectangle's stored graph. -/
theorem itcs_rep_pi_prog (hfac : NormalizedFactor) {Pg : Program} {f sb sp jfac : ℕ}
    (hf : Pg.funs[f]? = some (liftLabF sb sp jfac)) (hsh : ShiftAt Pg sb)
    (hsp : Pg.HasAt sp (pSplitFuns sp)) (hj : Pg.prims[jfac]? = some (normalizedFactorPrim hfac))
    (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R)
    (hs : List (Perm (Fin k) × Perm (Fin L.q))) (hhs : PairGens e L rep.H hs) (g : rep.H) :
    FunDet Pg f (.list [liftLabCtx L.q k (hs.map Prod.swap), encPerm (toFin e g.val)])
      (encPerm (itcsRepMap rep g).val.val)
      (liftLabCost (normalizedFactorPrim hfac) (hs.length + L.q + k + 2)) := by
  have hh := liftLab_spec hfac hf hsh hsp hj (hs.map Prod.swap)
    (itcs_rep_pi_precondition e rep hhs g)
  exact FunAll.mono hh fun w cost ⟨a, hw, ha, hc⟩ => by
    rw [itcs_rep_pi_unique e rep hhs g ha] at hw
    exact ⟨hw, by simpa only [List.length_map] using hc⟩

end GI.Impl
