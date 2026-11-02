import Workspace.Impl.GenNormParent
import Workspace.Impl.GenNormLabels

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encKSetTuples)

/-- The mathematical pair computed on a position generator. The fallback is unused when the
position permutation belongs to the parent group. -/
noncomputable def normPairOf {Ω C : Type} {S : State Ω C} {n m k : ℕ} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k))
    (hS : Q.ProductStructure m k 1 e) (a : Perm (Fin n)) : Perm (Fin n) × Perm (Fin m) := by
  classical
  exact if ha : (toFin en).symm a ∈ S.G then
    (a, Q.permHom e hS (Q.ρ.rangeRestrict ⟨_, ha⟩)) else (a, 1)

/-- Pairing keeps the list of position generators. -/
theorem normPairOf_fst {Ω C : Type} {S : State Ω C} {n m k : ℕ} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k))
    (hS : Q.ProductStructure m k 1 e) (a : Perm (Fin n)) :
    (normPairOf en Q e hS a).1 = a := by
  unfold normPairOf
  split_ifs <;> rfl

/-- The recovered pairs of any parent generating list generate the parent graph. -/
theorem normParentGens_map {Ω C : Type} {S : State Ω C} {n m k : ℕ} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k))
    (hS : Q.ProductStructure m k 1 e) (gs : List (Perm (Fin n)))
    (hgen : GI.Cited.gens gs = groupFin en S.G) :
    normParentGens en Q e hS (gs.map (normPairOf en Q e hS)) := by
  have hm : ∀ a ∈ gs, (toFin en).symm a ∈ S.G := by
    intro a ha
    have h : a ∈ groupFin en S.G := hgen ▸ Subgroup.subset_closure ha
    obtain ⟨g, hg, he⟩ := mem_groupFin.mp h
    rw [← he, MulEquiv.symm_apply_apply]
    exact hg
  apply normParentGens_of
  · have heq : (gs.map (normPairOf en Q e hS)).map Prod.fst = gs := by
      rw [List.map_map]
      have hh : (Prod.fst ∘ normPairOf en Q e hS) = id := funext (normPairOf_fst en Q e hS)
      rw [hh, List.map_id]
    rw [heq]
    exact hgen
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    refine ⟨⟨(toFin en).symm a, hm a ha⟩, ?_⟩
    apply Prod.ext
    · rw [normPairOf_fst]
      change toFin en ((toFin en).symm a) = a
      exact MulEquiv.apply_symm_apply _ _
    · simp only [normPairOf, dif_pos (hm a ha)]
      rfl

/-- An explicit polynomial budget for mapping the pairing program over a generator list. -/
def normParentListCost (n m L W : ℕ) : ℕ :=
  let T := 2 * (W + 4 * (n + 1) ^ 2) + n + m + 26
  let U := L * (50 * (n + m + 1) ^ 2 + 1) + 4
  L * (10 ^ 28 * T ^ 12) + mapK * (L + 1) * (2 * (W + U) + 6 + U + 1)

set_option maxHeartbeats 2000000 in
/-- The map of the pairing program computes the list of graph pairs at polynomial cost. -/
theorem normParentList_spec {Pg : Program}
    {b f act bg recover point filter cand all test mem n m k : ℕ}
    (houter : Pg.HasAt b (mapFuns b f)) (hf : Pg.funs[f]? = some (normParentF act recover))
    (hact : Pg.funs[act]? = some (actF bg)) (hgather : Pg.HasAt bg (gatherFuns bg))
    (hmap : Pg.HasAt recover (mapFuns recover point))
    (hpoint : Pg.funs[point]? = some (normPointF filter))
    (hfilter : Pg.HasAt filter (filterFuns filter cand))
    (hcand : Pg.funs[cand]? = some (normCandidateF all))
    (hall : Pg.HasAt all (allFuns all test))
    (htest : Pg.funs[test]? = some (normIncTestF mem)) (hmem : Pg.HasAt mem (normMemFuns mem))
    {Ω C : Type} {S : State Ω C} (en : Ω ≃ Fin n) (Q : PrimitiveQuotient S)
    (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e)
    (num : Fin n → ℕ) (reps : List ℕ) (hnum : ∀ i, num i ≤ n)
    (hreps : ∀ r ∈ reps, r < n) (hd : reps.length = Q.d)
    (hb : ∀ v ∈ S.dom, (Q.blk v : ℕ) = num (en v))
    (hr : ∀ t (ht : t < reps.length), ∃ h : reps[t] < n, en.symm ⟨_, h⟩ ∈ S.dom ∧ num ⟨_, h⟩ = t)
    (gs : List (Perm (Fin n))) (hgs : ∀ a ∈ gs, (toFin en).symm a ∈ S.G) :
    FunDet Pg b (.list [.list [encFun num, natList reps, encKSetTuples e,
      encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m))], .list (gs.map encPerm)])
      (.list ((gs.map (normPairOf en Q e hS)).map pairV))
      (normParentListCost n m gs.length (Val.list [encFun num, natList reps, encKSetTuples e,
        encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m))]).wt) := by
  let ctx := Val.list [encFun num, natList reps, encKSetTuples e,
    encPerm (1 : Perm (Fin Q.d)), encPerm (1 : Perm (Fin m))]
  let T := 2 * (ctx.wt + 4 * (n + 1) ^ 2) + n + m + 26
  let U := gs.length * (50 * (n + m + 1) ^ 2 + 1) + 4
  have hstep : ∀ a ∈ gs, FunDet Pg f (.list [ctx, encPerm a])
      (pairV (normPairOf en Q e hS a)) (10 ^ 28 * T ^ 12) := by
    intro a ha
    have h := normParent_spec hf hact hgather hmap hpoint hfilter hcand hall htest hmem
      en Q e hS num reps hnum hreps hd hb hr a (hgs a ha)
    have heq : pairV (normPairOf en Q e hS a) =
        .list [encPerm a, encPerm (Q.permHom e hS (Q.ρ.rangeRestrict ⟨_, hgs a ha⟩))] := by
      simp only [normPairOf, dif_pos (hgs a ha)]
      rfl
    rw [heq]
    refine h.mono (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 12))
    have wp := wt_encPerm_le a
    have wa := wt_list2_le ctx (encPerm a)
    change (Val.list [ctx, encPerm a]).wt + n + m + 20 ≤ T
    dsimp only [T]
    omega
  have hm := mapList_spec houter gs encPerm (fun a => pairV (normPairOf en Q e hS a))
    (c := ctx) (B := 10 ^ 28 * T ^ 12)
    (fun a _ a' _ h => by rw [encPerm_injective h]) hstep
  have hout : (gs.map fun a => pairV (normPairOf en Q e hS a)) =
      (gs.map (normPairOf en Q e hS)).map pairV := by simp only [List.map_map, Function.comp_def]
  rw [hout] at hm
  refine hm.mono ?_
  have hsq : (n + 1) ^ 2 ≤ (n + m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have wi := wt_list_map_le gs encPerm (W := 4 * (n + 1) ^ 2) (fun a _ => wt_encPerm_le a)
  have wo := wt_list_map_le gs (fun a => pairV (normPairOf en Q e hS a))
    (W := 22 * (n + m + 1) ^ 2) (fun a _ => wt_pairV_le _)
  have hiU : (Val.list (gs.map encPerm)).wt ≤ U := by
    have h := Nat.mul_le_mul_left gs.length (show 2 * (4 * (n + 1) ^ 2) + 1 ≤
      50 * (n + m + 1) ^ 2 + 1 by omega)
    dsimp only [U]
    omega
  rw [hout] at wo
  have hoU : (Val.list ((gs.map (normPairOf en Q e hS)).map pairV)).wt ≤ U := by
    have h := Nat.mul_le_mul_left gs.length (show 2 * (22 * (n + m + 1) ^ 2) + 1 ≤
      50 * (n + m + 1) ^ 2 + 1 by omega)
    dsimp only [U]
    omega
  have wa := wt_list2_le ctx (.list (gs.map encPerm))
  change _ ≤ gs.length * (10 ^ 28 * T ^ 12) +
    mapK * (gs.length + 1) * (2 * (ctx.wt + U) + 6 + U + 1)
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  omega

/-- The pairs recomputed on a reduced normalized generating list encode exactly each child's
supplied labels and satisfy the `n²` bound. -/
theorem normReducedLabels {Ω C : Type} [Finite Ω] {S : State Ω C} {n : ℕ}
    (en : Ω ≃ Fin n) (Q : PrimitiveQuotient S) (c : Q.NormChoice) (htr : S.Transitive)
    (hq : GI.Assembly.P₀.q₀ < (Q.normalizationOf c).q)
    (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
    (gs : List (Perm (Fin n))) (hlen : gs.length ≤ n ^ 2)
    (hgen : GI.Cited.gens gs = groupFin en (Q.normGroup c.e c.hS))
    (j : Fin (Q.normAboveOf c htr hq hkc hkl).I.k) :
    LabValStd en ((Q.normAboveOf c htr hq hkc hkl).child j)
      (normLabelVal en Q c (gs.map (normPairOf en Q c.e c.hS)))
      ((Q.normAboveOf c htr hq hkc hkl).childLabels j) := by
  have hg : ∀ a ∈ gs, (toFin en).symm a ∈ Q.normGroup c.e c.hS := by
    intro a ha
    have h : a ∈ groupFin en (Q.normGroup c.e c.hS) := hgen ▸ Subgroup.subset_closure ha
    obtain ⟨g, hg, he⟩ := mem_groupFin.mp h
    rw [← he, MulEquiv.symm_apply_apply]
    exact hg
  apply normLabelVal_spec en Q c htr hq hkc hkl _ (by simpa using hlen) ?_ ?_ j
  · rw [List.map_map]
    have hh : (Prod.fst ∘ normPairOf en Q c.e c.hS) = id := funext (normPairOf_fst en Q c.e c.hS)
    rw [hh, List.map_id]
    exact hgen
  · intro p hp hpG
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    have hparent := Q.normGroup_le c.e c.hS (hg a ha)
    simp only [normPairOf, dif_pos hparent] at hpG ⊢
    rfl

end GI.Impl
