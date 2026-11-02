import Workspace.Impl.LinObjectCorrectOneSpec
import Workspace.Impl.LinMapAll

namespace GI.Impl
open GI.Cited GI.Lang

/-- Append the current generator to the stored correction context. -/
def linObjectCorrectItemF (correct : ℕ) : Expr :=
  .call correct (.snoc (arg 0) (arg 1))

def linObjectCorrectMapFuns (b jsci jder jmem jm jh : ℕ) : List Expr :=
  mapFuns b (b+3) ++ [linObjectCorrectItemF (b+4)] ++
    linObjectCorrectOneFuns (b+4) jsci jder jmem jm jh

private theorem linObjectCorrectMap_length (b f : ℕ) : (mapFuns b f).length = 3 := rfl

theorem linObjectCorrectMapFuns_length (b jsci jder jmem jm jh : ℕ) :
    (linObjectCorrectMapFuns b jsci jder jmem jm jh).length = 319 := by
  simp only [linObjectCorrectMapFuns,List.length_append,List.length_cons,List.length_nil,
    linObjectCorrectMap_length,linObjectCorrectOneFuns_length]

structure linObjectCorrectMapAt (P : Program) (b jsci jder jmem jm jh : ℕ)
    (hs : SolvableCosetIntersection) (hd : DerivedSubgroup) (hm : Membership) (hc : ConstructiveMembership) : Prop where
  map : P.HasAt b (mapFuns b (b+3))
  item : P.funs[b+3]? = some (linObjectCorrectItemF (b+4))
  correct : linObjectCorrectOneAt P (b+4) jsci jder jmem jm jh hs hd hm hc

theorem linObjectCorrectMapAt_of {P : Program} {b jsci jder jmem jm jh : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (h : P.HasAt b (linObjectCorrectMapFuns b jsci jder jmem jm jh))
    (hjs : P.prims[jsci]? = some (solvableCosetIntersectionPrim hs))
    (hjd : P.prims[jder]? = some (derivedSubgroupPrim hd))
    (hjm : P.prims[jmem]? = some (membershipPrim hm))
    (hjc : P.prims[jm]? = some (linMembershipPrim hc)) :
    linObjectCorrectMapAt P b jsci jder jmem jm jh hs hd hm hc := by
  have hi : P.HasAt (b+3) [linObjectCorrectItemF (b+4)] := by
    simpa only [linObjectCorrectMap_length] using h.left.right
  have hc' : P.HasAt (b+4) (linObjectCorrectOneFuns (b+4) jsci jder jmem jm jh) := by
    simpa only [List.length_append,List.length_cons,List.length_nil,linObjectCorrectMap_length,
      Nat.add_assoc,Nat.reduceAdd] using h.right
  exact ⟨h.left.left,hi.single,linObjectCorrectOneAt_of hc' hjs hjd hjm hjc⟩

/-- The small adapter has no arithmetic beyond appending one value. -/
theorem linObjectCorrectItem_comp {P : Program} {f correct C : ℕ}
    (he : P.funs[f]? = some (linObjectCorrectItemF correct)) (ctx : List Val) (g : Val)
    (R : Val → Prop) (hw : (Val.list [Val.list ctx,g]).wt ≤ C)
    (hc : FunAll P correct (.list (ctx ++ [g])) (fun out c => R out ∧ c ≤ C)) :
    FunAll P f (.list [.list ctx,g]) (fun out c => R out ∧ c ≤ 1000*(C+1)^2) := by
  have dr := Det.arg' (P:=P) (vs:=[Val.list ctx,g]) (rest:=[]) (j:=0) rfl
  have dg := Det.arg' (P:=P) (vs:=[Val.list ctx,g]) (rest:=[]) (j:=1) rfl
  have da := Det.snoc dr dg
  have wctx : (Val.list ctx).wt < (Val.list [Val.list ctx,g]).wt := wt_le_wt_list (by simp)
  have wg : g.wt < (Val.list [Val.list ctx,g]).wt := wt_le_wt_list (by simp)
  have wt := wt_list_snoc_le ctx g
  apply FunAll.intro he
  refine (normBound_call da hc).mono fun out cost hout => ⟨hout.1,?_⟩
  have hp : C+1 ≤ (C+1)^2 := Nat.le_self_pow (by decide) _
  omega

end GI.Impl
