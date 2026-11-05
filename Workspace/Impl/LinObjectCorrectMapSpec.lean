module

public import Workspace.Impl.LinObjectCorrectMap

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

theorem linObjectCorrectOneAnswer_success {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n)))
    (Y Z : Multiset (CObj ℕ (Equiv.Perm (Fin n)))) (g : Equiv.Perm (Fin n)) (out : Val)
    (h : linObjectCorrectOneAnswer A Y Z g out) (hex : ∃ a ∈ A, Z ↼ a = Y) :
    ∃ a ∈ A, out = encPerm (g*a) ∧ Z ↼ a = Y := by
  rcases h with ⟨_,hno⟩ | hs
  · exact (hno hex).elim
  · exact hs

/-- Map the actual correction procedure over the compressed affine
stabilizer generators. Each choice of lifts is retained in the relation. -/
theorem linObjectCorrectMap_comp {P : Program} {b jsci jder jmem jm jh n C : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : linObjectCorrectMapAt P b jsci jder jmem jm jh hs hd hm hc)
    (ctx : List Val) (gs : List (Equiv.Perm (Fin n))) (R : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) → Prop)
    (hw : (Val.list [.list ctx,.list (gs.map encPerm)]).wt ≤ C)
    (hf : ∀ g ∈ gs, FunAll P (b+4) (.list (ctx ++ [encPerm g]))
      (fun out cost => (∃ k, out = encPerm k ∧ R g k) ∧ cost ≤ C)) :
    FunAll P b (.list [.list ctx,.list (gs.map encPerm)]) (fun out cost =>
      (∃ ks, out = .list (ks.map encPerm) ∧ List.Forall₂ R gs ks) ∧
      cost ≤ linMapBudget (Val.list [.list ctx,.list (gs.map encPerm)]).wt (1000*(100*(C+1)^2+1)^2)) := by
  have hi (g : Equiv.Perm (Fin n)) (hg : g ∈ gs) :
      FunAll P (b+3) (.list [.list ctx,encPerm g])
        (fun out cost => (∃ k, out = encPerm k ∧ R g k) ∧ cost ≤ 1000*(100*(C+1)^2+1)^2) := by
    apply linObjectCorrectItem_comp h.item ctx (encPerm g) _
    · have hctx : (Val.list ctx).wt ≤ C :=
        (wt_le_wt_list (by simp)).le.trans hw
      have hgW : (encPerm g).wt ≤ C :=
        (wt_le_wt_list (List.mem_map.mpr ⟨g,hg,rfl⟩)).le.trans
          ((wt_le_wt_list (by simp)).le.trans hw)
      have hpair := wt_list2_le (.list ctx) (encPerm g)
      have hp : C+1 ≤ (C+1)^2 := Nat.le_self_pow (by decide) _
      omega
    · exact (hf g hg).mono fun out cost hout => ⟨hout.1,by
        have hp : C+1 ≤ (C+1)^2 := Nat.le_self_pow (by decide) _
        omega⟩
  refine (linMapAll_spec h.map encPerm encPerm_injective (fun g out => ∃ k, out = encPerm k ∧ R g k)
    (.list ctx) gs (1000*(100*(C+1)^2+1)^2) hi).mono fun out cost hout => ?_
  obtain ⟨ws,rfl,hws⟩ := hout.1
  obtain ⟨ks,rfl,hks⟩ := linForall₂_encoded encPerm R hws
  exact ⟨⟨ks,rfl,hks⟩,hout.2⟩

end GI.Impl
