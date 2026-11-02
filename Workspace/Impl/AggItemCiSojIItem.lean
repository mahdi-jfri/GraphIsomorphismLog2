import Workspace.Impl.AggItemCiSojIP

/-! # The computed component item agrees with the exact model script -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (gens)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-- The full imprimitive item program returns exactly its model overcosets,
including the empty result when the target check fails. -/
theorem itcs_imp_part_item {Pg : Program} {Ii : itcsCompIdx} {f mn mt fb B : ℕ}
    (hi : itcsCompOk Pg Ii)
    (hf : Pg.funs[f]? = some (itcsImpPartF Ii.c1.rng Ii.f mn Ii.c1.f))
    (hm : Pg.HasAt mn (allFuns mn mt)) (ht : Pg.funs[mt]? = some (itcsMinF fb Ii.c1.sz))
    (hb : Pg.funs[fb]? = some itcqFbT)
    (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q) (v : ℕ)
    (hx : x₀ ∈ X.fiber) (hX : itCfColsLe (.pair X x₀) B)
    (hY : itCfColsLe (.pair Y y₀) B) (hv : v ≤ B)
    (hmin : ∀ a ∈ X.fiber, 2 ≤ (X.comp v a).card) :
    ∃ ovs os,
      (objItem (P := P₀) (X.impPart v) (Y.impPart v) : AuxItem P₀ S L).script =
        Script.done ⟨[], ovs⟩ ∧
      List.Forall₂ (asOvAt L) os ovs ∧
      (∀ o ∈ os, gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype) ∧
      FunDet Pg f (.list [rcCertIn X x₀, rcCertIn Y y₀, .nat v]) (itciOV os)
        (itcsImpPartC L.q B) := by
  classical
  obtain ⟨a, ha, hp⟩ := itcs_imp_part_prog hi hf hm ht hb X Y x₀ y₀ v hX hY hv
    ⟨x₀, hmin x₀ hx⟩ (evenStab (q := L.q) (X.impPart v))
  by_cases htY : ∀ b ∈ Y.fiber, 2 ≤ (Y.comp v b).card
  · obtain ⟨ovs, hs, ho, hg⟩ := itcs_imp_item (P := P₀) L X Y v hmin htY ha
    refine ⟨ovs, _, hs, ho, hg, ?_⟩
    simpa only [if_pos htY] using hp
  · refine ⟨[], [], itcs_imp_reject X Y v hmin htY, List.Forall₂.nil, ?_, ?_⟩
    · intro o ho
      simp only [List.not_mem_nil] at ho
    · simpa only [if_neg htY, itciOV, List.map_nil] using hp

end GI.Impl
