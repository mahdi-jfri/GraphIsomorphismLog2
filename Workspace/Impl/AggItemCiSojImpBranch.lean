module

public import Workspace.Impl.AggItemCiSojStart

@[expose] public section

/-! # The exact implication branch of the first-rectangle item -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val gens)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-- Reading the first passing pair's color computes exactly the globally fixed
implication choice used by the model. -/
theorem itcs_imp_color_prog {q : ℕ} {Pg : Program} {pc : ℕ}
    (hf : Pg.funs[pc]? = some itcqPcF) (X : PairCfg q) (h : ∃ a b, ImpPair X a b) :
    let inp := Val.list [.list [rcColVal X,itcqFV X,.nat X.fiber.card],.nat (itcsImpScan X)]
    FunDet Pg pc inp (.nat (itcsImpValue X h)) (50*(inp.wt+1)) := by
  have hs := itcs_imp_scan_first X h
  have hlt : itcsImpScan X < X.fiber.card*X.fiber.card := hs ▸
    (itciPE X.fiber.card (itcsImp X h).1).isLt
  let t : Fin (X.fiber.card*X.fiber.card) := ⟨itcsImpScan X,hlt⟩
  have ht : t = itciPE X.fiber.card (itcsImp X h).1 := Fin.ext hs
  have hc : itcqPC X rfl ((itciPE X.fiber.card).symm t) = itcsImpValue X h := by
    rw [ht,Equiv.symm_apply_apply]
    rfl
  have hp := itcq_pcF_spec hf X t (W:=(Val.list [.list [rcColVal X,itcqFV X,.nat X.fiber.card],
    .nat (itcsImpScan X)]).wt) (le_refl _)
  simpa only [hc] using hp

/-- The implication branch returns the exact model item and complete overcoset
encodings, with every source component-size and palette precondition proved. -/
theorem itcs_soj_imp_item {Pg : Program} {Ii : itcsCompIdx} {f item mn mt fb B : ℕ}
    (hi : itcsCompOk Pg Ii)
    (hf : Pg.funs[f]? = some (itcsResE (.call item (.var 0))))
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
      FunDet Pg f inp (itcsResV (itciOV os))
        (30*(100*(inp.wt+itcsImpPartC L.q B+100)+1)+itcsImpPartC L.q B) := by
  classical
  dsimp only
  let himp := (itcs_imp_cut_iff X hX hx).2 hprim
  obtain ⟨ovs,os,hs,ho,hg,hp⟩ := itcs_imp_part_item hi hitem hm ht hb X Y x₀ y₀
    (itcsImpValue X himp) hx hcolX hcolY (itcs_imp_value_le X x₀ hcolX himp)
    (itcs_imp_value_components X himp)
  refine ⟨ovs,os,?_,ho,hg,itcs_res_prog hf hp⟩
  simpa only [sojItem,dif_pos hx,if_neg hprim,dif_pos himp,itcsChoices,itcsImpValue] using hs

end GI.Impl
