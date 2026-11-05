module

public import Workspace.Impl.LinObjectLocalRelation

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang Matrix

def linObjectLocalRelationsFuns (b jm : ℕ) : List Expr :=
  mapFuns b (b + 3) ++ linObjectLocalRelationFuns (b + 3) jm

theorem linObjectLocalRelationsFuns_length (b jm : ℕ) :
    (linObjectLocalRelationsFuns b jm).length = 64 := rfl

structure linObjectLocalRelationsAt (P : Program) (b jm : ℕ) (hm : ConstructiveMembership) : Prop where
  map : P.HasAt b (mapFuns b (b + 3))
  item : linObjectLocalRelationAt P (b + 3) jm hm

theorem linObjectLocalRelationsAt_of {P : Program} {b jm : ℕ} {hm : ConstructiveMembership}
    (h : P.HasAt b (linObjectLocalRelationsFuns b jm))
    (hj : P.prims[jm]? = some (linMembershipPrim hm)) : linObjectLocalRelationsAt P b jm hm where
  map := h.block 0 rfl
  item := linObjectLocalRelationAt_of (h.block 3 rfl) hj

theorem linObjectLocalRelationCost_mono (hm : ConstructiveMembership) {W V : ℕ} (hW : W ≤ V) :
    linObjectLocalRelationCost hm W ≤ linObjectLocalRelationCost hm V := by
  have he : linObjectLocalRelationCoordsBudget hm W ≤ linObjectLocalRelationCoordsBudget hm V :=
    linElementListCost_mono hm (by omega)
  have hp : linObjectLocalRelationPadBudget hm W ≤ linObjectLocalRelationPadBudget hm V :=
    linObjectPadCost_mono (by unfold linObjectLocalRelationPadArg; omega)
  have ha : linObjectLocalRelationAppendBudget hm W ≤ linObjectLocalRelationAppendBudget hm V := by
    unfold linObjectLocalRelationAppendBudget linAppendCost
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by
      unfold linObjectLocalRelationAppendArg; omega) 2)
  unfold linObjectLocalRelationCost
  omega

theorem linForall₂_encoded {α β : Type*} (enc : β → Val) (R : α → β → Prop)
    {xs : List α} {ws : List Val}
    (h : List.Forall₂ (fun x w => ∃ y, w = enc y ∧ R x y) xs ws) :
    ∃ ys, ws = ys.map enc ∧ List.Forall₂ R xs ys := by
  induction h with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons h _ ih =>
    obtain ⟨y, rfl, hy⟩ := h
    obtain ⟨ys, rfl, hys⟩ := ih
    exact ⟨y :: ys, rfl, .cons hy hys⟩

noncomputable def linObjectLocalRelationsCost (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  linMapBudget W (linObjectLocalRelationCost hm (100 * (W + 1)))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 12000 in
theorem linObjectLocalRelations_spec (hm : ConstructiveMembership)
    {P : Program} {b jm n N : ℕ} (h : linObjectLocalRelationsAt P b jm hm)
    (as : List (Equiv.Perm (Fin n))) (bss : List (List (Equiv.Perm (Fin n))))
    (hbs : ∀ bs ∈ bss, ∀ x ∈ bs, x ∈ gens as) (hN : ∀ bs ∈ bss, (1 :: bs).length ≤ N)
    (M : Matrix (Fin as.length) (Fin as.length) ℤ) {Q : Type*} [CommGroup Q]
    (π : gens as →* Q) :
    let ctx := Val.list [encGroup as, encIntMatrix M, encFun (fun i : Fin N => i.val),
      encFun (fun i : Fin as.length => i.val)]
    let a := Val.list [ctx, .list (bss.map encGroup)]
    FunAll P b a (fun out cost =>
      (∃ Ms : List (Matrix (Fin (as.length + N)) (Fin as.length) ℤ),
        out = .list (Ms.map encIntMatrix) ∧ List.Forall₂ (fun bs L =>
          ∃ C : Matrix (Fin N) (Fin as.length) ℤ, L = linRowStack M C ∧
            (linRelations C).map (linCoordMap (fun j : Fin as.length =>
              π (linIntoSubgroup (gens as) (as.get j)))) =
              Submodule.span ℤ (Set.range fun i : Fin (1 :: bs).length =>
                Additive.ofMul (π (linIntoSubgroup (gens as) ((1 :: bs).get i))))) bss Ms) ∧
      cost ≤ linObjectLocalRelationsCost hm a.wt) := by
  let ctx := Val.list [encGroup as, encIntMatrix M, encFun (fun i : Fin N => i.val),
    encFun (fun i : Fin as.length => i.val)]
  let a := Val.list [ctx, .list (bss.map encGroup)]
  let W := a.wt
  let R (bs : List (Equiv.Perm (Fin n))) (L : Matrix (Fin (as.length + N)) (Fin as.length) ℤ) :=
    ∃ C : Matrix (Fin N) (Fin as.length) ℤ, L = linRowStack M C ∧
      (linRelations C).map (linCoordMap (fun j : Fin as.length =>
        π (linIntoSubgroup (gens as) (as.get j)))) =
        Submodule.span ℤ (Set.range fun i : Fin (1 :: bs).length =>
          Additive.ofMul (π (linIntoSubgroup (gens as) ((1 :: bs).get i))))
  have wc : ctx.wt < W := wt_le_wt_list (by simp [a, W])
  have wb : (Val.list (bss.map encGroup)).wt < W := wt_le_wt_list (by simp [a, W])
  have hw (bs : List (Equiv.Perm (Fin n))) (hbs : bs ∈ bss) :
      (Val.list [ctx, encGroup bs]).wt ≤ 100 * (W + 1) := by
    have hg : (encGroup bs).wt < (Val.list (bss.map encGroup)).wt := wt_le_wt_list (by
      exact List.mem_map.mpr ⟨bs, hbs, rfl⟩)
    have hh := wt_list2_le ctx (encGroup bs)
    omega
  have hs (bs : List (Equiv.Perm (Fin n))) (hB : bs ∈ bss) :
      FunAll P (b + 3) (.list [ctx, encGroup bs]) (fun out cost =>
        (∃ L, out = encIntMatrix L ∧ R bs L) ∧
        cost ≤ linObjectLocalRelationCost hm (100 * (W + 1))) := by
    refine (linObjectLocalRelation_spec hm h.item as bs (hbs bs hB) (hN bs hB) M π).mono
      fun out cost ho => ?_
    obtain ⟨⟨C, rfl, hC⟩, hc⟩ := ho
    exact ⟨⟨linRowStack M C, rfl, C, rfl, hC⟩,
      hc.trans (linObjectLocalRelationCost_mono hm (hw bs hB))⟩
  refine (linMapAll_spec h.map encGroup encGroup_injective
    (fun bs out => ∃ L, out = encIntMatrix L ∧ R bs L) ctx bss
    (linObjectLocalRelationCost hm (100 * (W + 1))) hs).mono fun out cost ho => ?_
  obtain ⟨⟨ws, rfl, hws⟩, hc⟩ := ho
  obtain ⟨Ms, rfl, hMs⟩ := linForall₂_encoded encIntMatrix R hws
  exact ⟨⟨Ms, rfl, hMs⟩, hc⟩

theorem linObjectLocalRelationsCost_poly (hm : ConstructiveMembership) :
    PBU (fun _ W _ => linObjectLocalRelationsCost hm W) := by
  have hb : PBU (fun _ W _ => linObjectLocalRelationCost hm (100 * (W + 1))) :=
    linPoly_subst (f := fun _ W _ => linObjectLocalRelationCost hm W)
      (linObjectLocalRelationCost_poly hm) (PBU.const 0)
      (PBU.smul 100 (PBU.addc PBU.W 1)) (PBU.const 0)
  unfold linObjectLocalRelationsCost linMapBudget
  simpa only [Nat.mul_assoc] using PBU.smul 10000 (PBU.mul (PBU.pow (PBU.addc PBU.W 1) 2)
    (PBU.addc (PBU.add hb PBU.W) 1))

end GI.Impl
