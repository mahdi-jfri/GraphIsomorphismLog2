module

public import Workspace.Impl.AggItemCiSojImpBranch

@[expose] public section

/-! # The exact balanced branch of the first-rectangle item -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val gens)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-- The balanced branch computes its singleton-block coloring item using the
established overcoset program, then returns the exact finished-item encoding. -/
theorem itcs_soj_bal_item {Pg : Program} {Ii : ItciIdx} {f item rng mp fb fe B : ℕ}
    (hi : ItciOk Pg Ii)
    (hf : Pg.funs[f]? = some (itcsResE (.call item (.var 0))))
    (hitem : Pg.funs[item]? = some (itcsBalPartF rng mp Ii.f))
    (hr : Pg.HasAt rng (rangeFuns rng)) (hm : Pg.HasAt mp (mapFuns mp fe))
    (he : Pg.funs[fe]? = some (itcsBalB fb)) (hb : Pg.funs[fb]? = some itcqFbT)
    (O : RectOracle P₀ S L) (ch : SojChoice) (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q)
    (hx : x₀ ∈ X.fiber) (hprim : PrimitiveColorCuts X.coloring false)
    (hbal : ∀ i, ((colorClass X.coloring false (X.idx hx) i).card : ℝ) ≤ etaB*X.fiber.card)
    (hcolX : itCfColsLe (.pair X x₀) B) (hcolY : itCfColsLe (.pair Y y₀) B) :
    let inp := Val.list [rcCertIn X x₀,rcCertIn Y y₀]
    ∃ ovs os,
      (sojItem O ch X Y x₀ y₀).script = Script.done ⟨[],ovs⟩ ∧
      List.Forall₂ (asOvAt L) os ovs ∧
      (∀ o ∈ os, gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype) ∧
      FunDet Pg f inp (itcsResV (itciOV os))
        (30*(100*(inp.wt+itcsBalPartC L.q B+100)+1)+itcsBalPartC L.q B) := by
  classical
  dsimp only
  obtain ⟨ovs,hs,ho,hg⟩ := itcs_bal_item (P:=P₀) L X Y x₀ y₀
  have hp := itcs_bal_part_prog hi hitem hr hm he hb X Y x₀ y₀ hcolX hcolY
    (evenStab (q:=L.q) (X.balPart x₀))
  refine ⟨ovs,_,?_,ho,hg,itcs_res_prog hf hp⟩
  simpa only [sojItem,dif_pos hx,if_pos hprim,if_pos hbal] using hs

end GI.Impl
