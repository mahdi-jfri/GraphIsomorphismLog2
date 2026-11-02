import Workspace.Impl.GenExposeProg

/-!
# Computing the selected normalization interval

The fine end of the selected interval is the nontrivial block partition. No earlier coarse
partition can therefore hold the whole domain. The selected interval is exactly the first
coarse partition that does hold the domain, so the existing split-index program computes it.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

private theorem normPart_le_end {Ω : Type} {G : Subgroup (Equiv.Perm Ω)} {D : Set Ω}
    (l : List (Interval Ω)) : ∀ {f : Setoid Ω}, Chain G D f l →
      ∀ I ∈ l, ∀ v ∈ D, ∀ w ∈ D, I.part.r v w → (fineEnd f l).r v w := by
  induction l with
  | nil => intro f h I hI; cases hI
  | cons J l ih =>
    intro f h I hI v hv w hw hr
    rcases List.mem_cons.mp hI with rfl | hI
    · exact chain_le l h.2.2.2.2 v hv w hw hr
    · exact ih h.2.2.2.2 I hI v hv w hw hr

/-- No interval before the exposed top holds the whole domain. -/
theorem normPre_not_univ {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S)
    (I : Interval Ω) (hI : I ∈ Q.pre) : ¬ UnivOn S.dom I.part := by
  have hch := chain_append.mp Q.tower.chain |>.1
  obtain ⟨v, hv, hzero⟩ := Q.onto ⟨0, by have := Q.two_le; omega⟩
  obtain ⟨w, hw, hone⟩ := Q.onto ⟨1, by have := Q.two_le; omega⟩
  intro h
  have heq := (Q.fine_eq v hv w hw).mp (normPart_le_end Q.pre hch I hI v hv w hw (h v hv w hw))
  rw [hzero, hone] at heq
  have hnat : (0 : ℕ) = 1 := congrArg Fin.val heq
  omega

/-- The existing split-index computation selects exactly `Q.pre.length`. -/
theorem normSplitIdx_eq {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S) :
    splitIdx S.dom (Q.pre ++ Q.top :: Q.post) = Q.pre.length := by
  have hpre : (Q.pre.map (univBit S.dom)).findIdx (fun x => decide (x = 1)) = Q.pre.length := by
    have h := List.findIdx_eq_length_of_false (xs := Q.pre.map (univBit S.dom))
      (p := fun x => decide (x = 1)) (by
        intro x hx
        obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hx
        simp only [decide_eq_false_iff_not]
        exact fun h => normPre_not_univ Q I hI (univBit_eq_one.mp h))
    simpa only [List.length_map] using h
  have htop : univBit S.dom Q.top = 1 := univBit_eq_one.mpr Q.top_univ
  simp only [splitIdx, List.map_append, List.map_cons, List.findIdx_append, hpre,
    List.length_map, lt_self_iff_false, if_false, List.findIdx_cons, htop,
    decide_true, cond_true, Nat.zero_add]

/-- The split-index program computes the exact selector stored in `N.childLabels`. -/
theorem normSelection_spec {Pg : Program} {b bcls : ℕ} (h : Pg.HasAt b (hsplitFuns b bcls))
    (hcls : Pg.HasAt bcls (clsFuns bcls)) {Ω C : Type} {S : State Ω C} {n : ℕ}
    (en : Ω ≃ Fin n) (Q : PrimitiveQuotient S) (hne : S.dom.Nonempty)
    {hv : Val} (hh : HierValC en hv (Q.pre ++ Q.top :: Q.post)) :
    FunDet Pg b (.list [encFun (indF en S.dom), hv]) (.nat Q.pre.length)
      (hsplitK * ((Val.list [encFun (indF en S.dom), hv]).wt + 1) ^ 5) := by
  simpa only [normSplitIdx_eq] using hsplit_spec h hcls hne hh

end GI.Impl
