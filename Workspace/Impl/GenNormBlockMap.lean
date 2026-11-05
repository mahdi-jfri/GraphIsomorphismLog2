module

public import Workspace.Impl.GenNormBlocks
public import Workspace.Impl.Lift

@[expose] public section

/-!
# Mapping the Johnson block computation over the positions
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encKSetTuples)

/-- The polynomial cost of the whole position-to-block table. -/
def normBlockMapCost (n m W : ℕ) : ℕ :=
  n * (10 ^ 12 * (2 * W + 3 * n + m + 30) ^ 5) +
    mapK * (n + 1) * (2 * (W + 4 * (n + 1) ^ 2) + 6 + n * (14 * m + 9) + 4 + 1)

/-- All position indicators are computed by one map. -/
theorem normBlockAtList_spec {Pg : Program} {b f bits bit mem n m k : ℕ}
    (houter : Pg.HasAt b (mapFuns b f)) (hf : Pg.funs[f]? = some (normBlockCellF bits))
    (hmap : Pg.HasAt bits (mapFuns bits bit)) (hbit : Pg.funs[bit]? = some (normMemFlipF mem))
    (hmem : Pg.HasAt mem (normMemFuns mem))
    {Ω C : Type} {S : State Ω C} (en : Ω ≃ Fin n) (Q : PrimitiveQuotient S)
    (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (num : Fin n → ℕ)
    (hnum : ∀ i, num i = Q.labFin en i) (flip : Bool) :
    FunDet Pg b (.list [.list [encKSetTuples e, encFun num, encFun (indF en S.dom),
      encPerm (1 : Perm (Fin m)), boolVal flip], encPerm (1 : Perm (Fin n))])
      (.list ((List.finRange n).map (normBlockAt en Q e flip)))
      (normBlockMapCost n m (Val.list [encKSetTuples e, encFun num, encFun (indF en S.dom),
        encPerm (1 : Perm (Fin m)), boolVal flip]).wt) := by
  let ctx := Val.list [encKSetTuples e, encFun num, encFun (indF en S.dom),
    encPerm (1 : Perm (Fin m)), boolVal flip]
  let T := 2 * ctx.wt + 3 * n + m + 30
  have ht : ∀ i : Fin n, FunDet Pg f (.list [ctx, .nat i]) (normBlockAt en Q e flip i)
      (10 ^ 12 * T ^ 5) := by
    intro i
    have h := normBlockCell_spec hf hmap hbit hmem en Q e num hnum flip i
    refine h.mono (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 5))
    have wi := wt_nat_le (i : ℕ)
    have hi := i.2
    have wa := wt_list2_le ctx (.nat i)
    change (Val.list [ctx, .nat i]).wt + n + m + 20 ≤ T
    dsimp only [T]
    omega
  have h := tabulate_spec houter ht
  have hid : encFun (fun i : Fin n => (i : ℕ)) = encPerm (1 : Perm (Fin n)) := rfl
  rw [hid] at h
  refine h.mono ?_
  have hout : ∀ i : Fin n, (normBlockAt en Q e flip i).wt ≤ 7 * m + 4 := by
    intro i
    classical
    unfold normBlockAt
    by_cases hi : en.symm i ∈ S.dom
    · rw [if_pos hi]
      simpa only [Nat.mul_comm] using wt_encFun_le
        (fun j : Fin m => (decide (j ∈ (if flip then (Q.kset e (en.symm i))ᶜ else
          Q.kset e (en.symm i)))).toNat) (B := 1) (fun j => Bool.toNat_le _)
    · rw [if_neg hi]
      have hnil : (Val.list []).wt = 4 := rfl
      omega
  have wo := wt_list_map_le (List.finRange n) (normBlockAt en Q e flip) (fun i _ => hout i)
  simp only [List.length_finRange] at wo
  have wi := wt_encPerm_le (1 : Perm (Fin n))
  have wa := wt_list2_le ctx (encPerm (1 : Perm (Fin n)))
  change _ ≤ n * (10 ^ 12 * T ^ 5) + mapK * (n + 1) *
    (2 * (ctx.wt + 4 * (n + 1) ^ 2) + 6 + n * (14 * m + 9) + 4 + 1)
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  have heq : n * (2 * (7 * m + 4) + 1) = n * (14 * m + 9) := by ring
  rw [heq] at wo
  omega

private theorem normIndicatorNat (p : Prop) [Decidable p] :
    (decide p).toNat = (if p then 1 else 0 : ℕ) := by
  by_cases h : p <;> simp [h]

private theorem normNotIndicatorNat (p : Prop) [Decidable p] :
    (!decide p).toNat = (if p then 0 else 1 : ℕ) := by
  by_cases h : p <;> simp [h]

/-- The computed table is exactly the block map in the normalization's supplied labels. -/
theorem normBlockAtList_eq {Ω C : Type} {S : State Ω C} {n : ℕ}
    (en : Ω ≃ Fin n) (Q : PrimitiveQuotient S) (c : Q.NormChoice) :
    (Val.list ((List.finRange n).map (normBlockAt en Q c.e (decide (c.m < 2 * c.k))))) =
      normBlockMapVal en Q c := by
  classical
  by_cases hk : 2 * c.k ≤ c.m
  · have hlt : ¬ c.m < 2 * c.k := by omega
    simp [normBlockAt, normBlockMapVal, hk, hlt, normIndicatorNat, normNotIndicatorNat]
  · have hlt : c.m < 2 * c.k := by omega
    simp [normBlockAt, normBlockMapVal, hk, hlt, normIndicatorNat, normNotIndicatorNat]

/-- The map computes the exact Johnson block value used by `normLabelVal_spec`. -/
theorem normBlockMap_spec {Pg : Program} {b f bits bit mem n : ℕ}
    (houter : Pg.HasAt b (mapFuns b f)) (hf : Pg.funs[f]? = some (normBlockCellF bits))
    (hmap : Pg.HasAt bits (mapFuns bits bit)) (hbit : Pg.funs[bit]? = some (normMemFlipF mem))
    (hmem : Pg.HasAt mem (normMemFuns mem))
    {Ω C : Type} {S : State Ω C} (en : Ω ≃ Fin n) (Q : PrimitiveQuotient S)
    (c : Q.NormChoice) (num : Fin n → ℕ) (hnum : ∀ i, num i = Q.labFin en i) :
    FunDet Pg b (.list [.list [encKSetTuples c.e, encFun num, encFun (indF en S.dom),
      encPerm (1 : Perm (Fin c.m)), boolVal (decide (c.m < 2 * c.k))], encPerm (1 : Perm (Fin n))])
      (normBlockMapVal en Q c)
      (normBlockMapCost n c.m (Val.list [encKSetTuples c.e, encFun num, encFun (indF en S.dom),
        encPerm (1 : Perm (Fin c.m)), boolVal (decide (c.m < 2 * c.k))]).wt) := by
  have h := normBlockAtList_spec houter hf hmap hbit hmem en Q c.e num hnum
    (decide (c.m < 2 * c.k))
  rw [normBlockAtList_eq en Q c] at h
  exact h

end GI.Impl
