import Workspace.Impl.AggItemCiSojBalBranch

/-! # Finished source branches before the start controller adds its result wrapper -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val gens)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-- The component item computes the exact imprimitive branch before the outer
start expression adds the finished-result wrapper. -/
theorem itcs_soj_imp_raw {Pg : Program} {Ii : itcsCompIdx} {item mn mt fb B : ℕ}
    (hi : itcsCompOk Pg Ii)
    (hitem : Pg.funs[item]? = some (itcsImpPartF Ii.c1.rng Ii.f mn Ii.c1.f))
    (hm : Pg.HasAt mn (allFuns mn mt)) (ht : Pg.funs[mt]? = some (itcsMinF fb Ii.c1.sz))
    (hb : Pg.funs[fb]? = some itcqFbT)
    (O : RectOracle P₀ S L) (cf : RcCertFn) (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q)
    (hX : X.Good deltaB) (hx : x₀ ∈ X.fiber)
    (hcolX : itCfColsLe (.pair X x₀) B) (hcolY : itCfColsLe (.pair Y y₀) B)
    (hprim : ¬ PrimitiveColorCuts X.coloring false) :
    let himp := (itcs_imp_cut_iff X hX hx).2 hprim
    let v := itcsImpValue X himp
    let inp := Val.list [rcCertIn X x₀,rcCertIn Y y₀,.nat v]
    ∃ ovs os,
      (sojItem O (itcsChoices cf) X Y x₀ y₀).script = Script.done ⟨[],ovs⟩ ∧
      List.Forall₂ (asOvAt L) os ovs ∧
      (∀ o ∈ os, gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype) ∧
      FunDet Pg item inp (itciOV os) (itcsImpPartC L.q B) := by
  classical
  dsimp only
  let himp := (itcs_imp_cut_iff X hX hx).2 hprim
  obtain ⟨ovs,os,hs,ho,hg,hp⟩ := itcs_imp_part_item hi hitem hm ht hb X Y x₀ y₀
    (itcsImpValue X himp) hx hcolX hcolY (itcs_imp_value_le X x₀ hcolX himp)
    (itcs_imp_value_components X himp)
  refine ⟨ovs,os,?_,ho,hg,hp⟩
  simpa only [sojItem,dif_pos hx,if_neg hprim,dif_pos himp,itcsChoices,itcsImpValue] using hs


/-- The singleton-block item computes the exact balanced branch before the
same outer finished-result wrapper. -/
theorem itcs_soj_bal_raw {Pg : Program} {Ii : ItciIdx} {item rng mp fb fe B : ℕ}
    (hi : ItciOk Pg Ii)
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
      FunDet Pg item inp (itciOV os) (itcsBalPartC L.q B) := by
  classical
  dsimp only
  obtain ⟨ovs,hs,ho,hg⟩ := itcs_bal_item (P:=P₀) L X Y x₀ y₀
  have hp := itcs_bal_part_prog hi hitem hr hm he hb X Y x₀ y₀ hcolX hcolY
    (evenStab (q:=L.q) (X.balPart x₀))
  refine ⟨ovs,_,?_,ho,hg,hp⟩
  simpa only [sojItem,dif_pos hx,if_pos hprim,if_pos hbal] using hs


end GI.Impl
