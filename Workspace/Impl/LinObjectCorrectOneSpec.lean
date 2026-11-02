import Workspace.Impl.LinObjectCorrectOneCost

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

set_option maxHeartbeats 500000 in
set_option maxRecDepth 2500 in
theorem linObjectCorrectOne_spec {P : Program} {b jsci jder jmem jm jh n r : ℕ}
    {hs : SolvableCosetIntersection} {hd : DerivedSubgroup} {hm : Membership} {hc : ConstructiveMembership}
    (hh : HermiteFullRank) (h : linObjectCorrectOneAt P b jsci jder jmem jm jh hs hd hm hc)
    (hjh : P.prims[jh]? = some (linHermitePrim hh))
    {Q : Type*} [CommGroup Q] (as ns : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (hπ : Function.Surjective π) (hf : Function.Surjective (linObjectLiftCoord as π))
    (Y : List (TmRiO n)) (hok : TmRecObjOK Y.length Y)
    (hsol : IsSolvable (gens as)) (hNA : gens ns ≤ gens as)
    (H : Subgroup (Equiv.Perm (Fin n))) (hAH : gens as ≤ H)
    (hA : GI.Multicoset.Normalizes H (gens as)) (hN : GI.Multicoset.Normalizes H (gens ns))
    (hcomm : ∀ a ∈ gens as, ∀ b ∈ gens as, a*b*a⁻¹*b⁻¹ ∈ gens ns)
    (hal : as.length ≤ n^2) (hfix : Fixes (gens ns) (tmGlMs Y))
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y), π.ker ≤ (Aut (gens as) T).subgroupOf (gens as))
    (L : Fin (tmRiPcsO (gens as) Y).length → Matrix (Fin r) (Fin as.length) ℤ)
    (hdr : as.length ≤ r) (hfull : ∀ i, Function.Injective (L i).mulVec)
    (hL : ∀ i, LinearMap.ker ((linObjectLocalImages as π Y i).mkQ.comp (linObjectLiftCoord as π)) = linRelations (L i))
    (g : Equiv.Perm (Fin n)) (hg : g ∈ H)
    (hy : Conf (gens as) (tmGlMs Y) (tmGlMs Y ↼ g)) :
    let input := Val.list [encGroup as,encGroup ns,.list ((tmRiPcsO (gens as) Y).map tmGlObjsVal),
      linObjectBlockInput L,encPerm g]
    FunAll P b input (fun out cost => linObjectCorrectOneAnswer (gens as) (tmGlMs Y) (tmGlMs Y ↼ g) g out ∧
      cost ≤ linObjectCorrectOneCost hs hm hc hh input.wt) := by
  let refs := tmRiPcsO (gens as) Y
  let input := Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),linObjectBlockInput L,encPerm g]
  let W := input.wt
  let SB := linObjectCorrectOneShiftBudget hs hm hc W
  let LB := linObjectCorrectOneLiftBudget hs hm hc hh W
  let C := linObjectCorrectOneSource hs hm hc hh W
  have wa : (encGroup as).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wn : (encGroup ns).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wr : (Val.list (refs.map tmGlObjsVal)).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wl : (linObjectBlockInput L).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wg : (encPerm g).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have hn : n ≤ W := by
    have hh' := S_le_wt_encGroup as
    have hx : n+1 ≤ (as.length+2)*(n+1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hp : W + SB + LB + permK*(W+1)^3 + 1 ≤ (W + SB + LB + permK*(W+1)^3 + 1)^2 :=
    Nat.le_self_pow (by decide) _
  have wC : W ≤ C := by change W ≤ 100 * (W+SB+LB+permK*(W+1)^3+1)^2; omega
  have sC : SB ≤ C := by change SB ≤ 100 * (W+SB+LB+permK*(W+1)^3+1)^2; omega
  have lC : LB ≤ C := by change LB ≤ 100 * (W+SB+LB+permK*(W+1)^3+1)^2; omega
  have cC : permK*(W+1)^3 ≤ C := by change permK*(W+1)^3 ≤ 100 * (W+SB+LB+permK*(W+1)^3+1)^2; omega
  have hC : 100 ≤ C := by change 100 ≤ 100 * (W+SB+LB+permK*(W+1)^3+1)^2; omega
  have hoArg : (Val.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encPerm g]).wt ≤
      linObjectCorrectOneShiftArg W := by
    have hh' := wt_list4_le (encGroup as) (encGroup ns) (.list (refs.map tmGlObjsVal)) (encPerm g)
    have hp' : W+1 ≤ (W+1)^2 := Nat.le_self_pow (by decide) _
    unfold linObjectCorrectOneShiftArg
    omega
  have ho := linObjectShiftOffsets_spec h.offsets as ns π Y hok hsol hNA H hAH hA hN hcomm hal hfix g hg hy
  have ho' : FunAll P (b+1) (.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encPerm g])
      (fun w cost => (linObjectOffsetsOut as π refs (tmGlMs Y ↼ g) w ∧ w.wt ≤ SB) ∧ cost ≤ C) := by
    have hos : FunAll P (b+1) (.list [encGroup as,encGroup ns,.list (refs.map tmGlObjsVal),encPerm g])
        (fun w cost => linObjectOffsetsOut as π refs (tmGlMs Y ↼ g) w ∧ cost ≤ SB) :=
      ho.mono fun out cost hout => ⟨hout.1,hout.2.trans (linPolyEnvelope_bound
        (linObjectShiftOffsetsCost_poly hs hm hc) (Nat.zero_le _) hoArg (Nat.zero_le _))⟩
    exact hos.wt_lt.mono fun out cost hout => ⟨⟨hout.1.1,by omega⟩,hout.1.2.trans sC⟩
  have hl (v : Val) (hv : linObjectOffsetsOut as π refs (tmGlMs Y ↼ g) v ∧ v.wt ≤ SB) (wv : v.wt ≤ C) :
      FunAll P (b+181) (.list [encGroup as,linObjectBlockInput L,v])
        (fun ans cost => linObjectCorrectOneLiftResult g
          (linObjectCorrectOneAnswer (gens as) (tmGlMs Y) (tmGlMs Y ↼ g) g) ans ∧ cost ≤ C) := by
    obtain ⟨hv,wSB⟩ := hv
    obtain ⟨w,rfl,hw⟩ := hv
    have hwout : linObjectOffsetsOut as π refs (tmGlMs Y ↼ g) (linVecVal w) := ⟨w,rfl,hw⟩
    have hlArg : (Val.list [encGroup as,linObjectBlockInput L,linVecVal w]).wt ≤
        linObjectCorrectOneLiftArg hs hm hc W := by
      have hh' := wt_list3_le (encGroup as) (linObjectBlockInput L) (linVecVal w)
      have hp' : W+SB+1 ≤ (W+SB+1)^2 := Nat.le_self_pow (by decide) _
      unfold linObjectCorrectOneLiftArg
      change _ ≤ 100 * (W+SB+1)^2
      omega
    refine (linObjectLift_spec hh h.lift hjh as π (linObjectLocalImages as π Y) hf L hdr hfull hL w).mono
      fun ans cost hans => ⟨?_,hans.2.trans ((linPolyEnvelope_bound (linObjectLiftCost_poly hh)
        (Nat.zero_le _) hlArg (Nat.zero_le _)).trans lC)⟩
    rcases hans.1 with ⟨rfl,hno⟩ | ⟨a,ha,rfl,hrows⟩
    · refine Or.inl ⟨rfl,Or.inl ⟨rfl,?_⟩⟩
      intro hex
      have hz := (linObjectDiagonal_transport_iff (gens as) π hπ (tmGlMs Y) (tmGlMs Y ↼ g) hy hker).mpr hex
      exact hno (linObjectCommonLift_exists as π hπ Y _ hy hker w hwout hz)
    · exact Or.inr ⟨a,rfl,Or.inr ⟨a,ha,rfl,
        linObjectCommonLift_correct as π hπ Y _ hy hker w hwout a ha hrows⟩⟩
  exact linObjectCorrectOne_comp h.entry (encGroup as) (encGroup ns) (.list (refs.map tmGlObjsVal))
    (linObjectBlockInput L) g (fun v => linObjectOffsetsOut as π refs (tmGlMs Y ↼ g) v ∧ v.wt ≤ SB)
    (linObjectCorrectOneAnswer (gens as) (tmGlMs Y) (tmGlMs Y ↼ g) g) hC wC ho' hl
    (fun a => (compose_spec h.compose g a).mono ((Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by omega : n+1 ≤ W+1) 3)).trans cC))

end GI.Impl
