import Workspace.Impl.LinActionItem

/-! Evaluate all newly returned cover generators in the retained full action. -/
namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 16000

def linActionRestrictFuns (b jm : ℕ) : List Expr :=
  mapFuns b (b + 3) ++ linActionItemFuns (b + 3) jm

theorem linActionRestrictFuns_length (b jm : ℕ) : (linActionRestrictFuns b jm).length = 70 := rfl

structure linActionRestrictAt (P : Program) (b jm : ℕ) (h : ConstructiveMembership) : Prop where
  map : P.HasAt b (mapFuns b (b + 3))
  item : linActionItemAt P (b + 3) jm h

theorem linActionRestrictAt_of {P : Program} {b jm : ℕ} {h : ConstructiveMembership}
    (hp : P.HasAt b (linActionRestrictFuns b jm)) (hj : P.prims[jm]? = some (linMembershipPrim h)) :
    linActionRestrictAt P b jm h where
  map := hp.block 0 rfl
  item := linActionItemAt_of (hp.block 3 rfl) hj

theorem linActionItemCost_mono (h : ConstructiveMembership) {W V : ℕ} (hW : W ≤ V) :
    linActionItemCost h W ≤ linActionItemCost h V := by
  simp only [linActionItemCost, linActionMemberCost, linActionMemberOut, linActionMemberArg, Prim.boundSize]
  gcongr

noncomputable def linActionRestrictCost (h : ConstructiveMembership) (W : ℕ) : ℕ :=
  linMapBudget W (linActionItemCost h (100 * (W + 1)))

set_option maxHeartbeats 1000000 in
theorem linActionRestrict_spec (h : ConstructiveMembership) {P : Program} {b jm n d : ℕ}
    (hp : linActionRestrictAt P b jm h) (gs : List (Equiv.Perm (Fin n))) (m : Fin d → ℕ)
    (hm : ∀ i, 0 < m i) (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m))
    (c : gens gs → linFiniteVec m) (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (xs : List (gens gs)) :
    FunDet P b (.list [linActionContext gs m ρ c, .list (xs.map fun x => encPerm x.val)])
      (.list (xs.map (linFiniteAffineVal m ρ c)))
      (linActionRestrictCost h (Val.list [linActionContext gs m ρ c, .list (xs.map fun x => encPerm x.val)]).wt) := by
  let W := (Val.list [linActionContext gs m ρ c, .list (xs.map fun x => encPerm x.val)]).wt
  apply linMapEncoded_spec hp.map (fun x : gens gs => encPerm x.val)
    (fun x y h => Subtype.ext (encPerm_injective h)) _ _ _ _
  intro x hx
  have wc : (linActionContext gs m ρ c).wt < W := wt_le_wt_list (by simp [W])
  have wys : (Val.list (xs.map fun y => encPerm y.val)).wt < W := wt_le_wt_list (by simp [W])
  have wx : (encPerm x.val).wt < W :=
    (wt_le_wt_list (List.mem_map.mpr ⟨x, hx, rfl⟩)).trans wys
  have wi := wt_list2_le (linActionContext gs m ρ c) (encPerm x.val)
  exact (linActionItem_spec h hp.item gs m hm ρ c hc x).mono (linActionItemCost_mono h (by omega))

theorem linActionRestrictCost_poly (h : ConstructiveMembership) : PBU (fun _ W _ => linActionRestrictCost h W) := by
  have hi := linPoly_subst (linActionItemCost_poly h) (PBU.const 0)
    (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  have hh := PBU.smul 10000 (PBU.mul (PBU.pow (PBU.addc PBU.W 1) 2)
    (PBU.addc (PBU.add hi PBU.W) 1))
  simpa only [linActionRestrictCost, linMapBudget, Nat.mul_assoc] using hh

end GI.Impl
