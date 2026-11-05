module

public import Workspace.Impl.GenNormOps
public import Workspace.Impl.GenNormCost

@[expose] public section

/-!
# One polynomial budget for every normalization preparation stage

The preparation has fourteen calls and a final list construction. At each call we enlarge a
bound on the stored values by the same polynomial. Iterating that polynomial a fixed number
of times is still polynomial. This lets the composition proof use one bound for all fields.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup Preimage PointwiseStab Membership)

/-- The normalized alternating degree is at most the number of positions plus two. -/
theorem normDegree_le {Ω C : Type} {S : State Ω C} {n m k : ℕ} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k))
    (hS : Q.ProductStructure m k 1 e) : m ≤ n + 2 := by
  let T := S.restrict (Q.normGroup e hS) (Q.normGroup_le e hS) S.x S.y (Q.pre ++ Q.top :: Q.post)
  let L : GiantLabels T := ⟨m, Q.normPi e hS, Q.normPi_surjective e hS⟩
  exact GiantLabels.q_le en L

/-- The graph-preimage primitive sees a polynomial-size encoding. -/
theorem normPreimage_wt {n m : ℕ} (ps : List (Perm (Fin n) × Perm (Fin m)))
    (ms : List (Perm (Fin m)))
    (hms : ∀ a ∈ ms, ∃ p ∈ Subgroup.closure {p | p ∈ ps}, MonoidHom.snd _ _ p = a) :
    (preimageEnc (pairInst (MonoidHom.snd _ _) ps ms hms)).wt ≤ 1000 * preM n m ps ms ^ 4 := by
  let I := pairInst (MonoidHom.snd _ _) ps ms hms
  let M := preM n m ps ms
  have hM : n + m + ps.length + ms.length + 2 = M := rfl
  have hm : 2 ≤ M := by omega
  have wg := wt_encGroup_le (I.ds.map GI.Cited.sumToFin)
  have wl : (I.ds.map GI.Cited.sumToFin).length = ps.length := by simp [I, pairInst]
  rw [wl] at wg
  change (encGroup (I.ds.map GI.Cited.sumToFin)).wt ≤
    40 * ((ps.length + 2) * (n + m + m + 1)) ^ 2 at wg
  have wg' := wt_encGroup_le ms
  have hg : (ps.length + 2) * (n + m + m + 1) ≤ 2 * M ^ 2 := by
    calc _ ≤ M * (2 * M) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hg' : (ms.length + 2) * (m + 1) ≤ M ^ 2 := by
    calc _ ≤ M * M := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hp := Nat.pow_le_pow_left hg 2
  have hp' := Nat.pow_le_pow_left hg' 2
  have heq : (2 * M ^ 2) ^ 2 = 4 * M ^ 4 := by ring
  have heq' : (M ^ 2) ^ 2 = M ^ 4 := by ring
  rw [heq] at hp
  rw [heq'] at hp'
  have wn := wt_nat_le (n + m)
  have wo := wt_list3_le (.nat (n + m)) (encGroup (I.ds.map GI.Cited.sumToFin)) (encGroup ms)
  have h14 : M ≤ M ^ 4 := Nat.le_self_pow (by norm_num) _
  change (Val.list [.nat (n + m), encGroup (I.ds.map GI.Cited.sumToFin), encGroup ms]).wt ≤
    1000 * M ^ 4
  omega

/-- Uniform bound for the alternating preimage call. -/
noncomputable def normGraphCost (hp : Preimage) (n m L : ℕ) : ℕ :=
  let M := n + m + L + m ^ 3 + 2
  (preimagePrim hp).boundSize (1000 * M ^ 4) + graphPreK * M ^ 8

/-- The graph preimage's full cost, including its cited call, is bounded by `normGraphCost`. -/
theorem normGraphCost_bound (hp : Preimage) {Ω C : Type} {S : State Ω C} {n m k : ℕ}
    (en : Ω ≃ Fin n) (Q : PrimitiveQuotient S)
    (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e)
    (ps : List (Perm (Fin n) × Perm (Fin m))) (hps : normParentGens en Q e hS ps) :
    (preimagePrim hp).bound (preimageEnc (pairInst (MonoidHom.snd _ _) ps (normAltGens m)
      (normAltGens_lift en Q e hS hps))) + graphPreK * preM n m ps (normAltGens m) ^ 8 ≤
        normGraphCost hp n m ps.length := by
  have h := prim_bound_le_wt (preimagePrim hp)
    (normPreimage_wt ps (normAltGens m) (normAltGens_lift en Q e hS hps))
  have heq : preM n m ps (normAltGens m) = n + m + ps.length + m ^ 3 + 2 := by
    simp only [preM, normAltGens, List.length_map, List.length_range]
  change _ ≤ (preimagePrim hp).boundSize (1000 * (n + m + ps.length + m ^ 3 + 2) ^ 4) +
    graphPreK * (n + m + ps.length + m ^ 3 + 2) ^ 8
  rw [heq] at h ⊢
  exact Nat.add_le_add_right h _

/-- An argument assembled from at most two levels of records fits this budget. -/
def normArgBudget (T : ℕ) : ℕ := 10 ^ 15 * (T + 1) ^ 4

/-- One bound for all stage functions on values and degrees bounded by `T`. -/
noncomputable def normStageBudget (hp : Preimage) (hst : PointwiseStab) (hm : Membership)
    (T : ℕ) : ℕ :=
  let A := normArgBudget T
  clsK * (T + 1) ^ 4 + 8000 * (T + 1) ^ 3 + normParentListCost T T T A +
    normAltCost T + normGraphCost hp T T T + normRawReduceCost hst T T T A +
    normCosetsCost hm T T A + hsplitK * (A + 1) ^ 5 + countK * (T + 1) ^ 3 +
    normBlockMapCost T T A + 10 ^ 6 * (A + T + T + 1) ^ 2 + normOrbitCost T A

/-- Enlarge the bound on all stored values after one stage call. -/
noncomputable def normGrow (hp : Preimage) (hst : PointwiseStab) (hm : Membership) (T : ℕ) : ℕ :=
  T + normArgBudget T + normStageBudget hp hst hm T + 100

/-- The total own budget of the fourteen preparation calls and the final packing. -/
noncomputable def normPrepCost (hp : Preimage) (hst : PointwiseStab) (hm : Membership)
    (n m W : ℕ) : ℕ := 100 * (normGrow hp hst hm)^[15] (W + n + m + 100)

theorem normGrow_le (hp : Preimage) (hst : PointwiseStab) (hm : Membership) (T : ℕ) :
    T ≤ normGrow hp hst hm T := by unfold normGrow; omega

theorem normGrow_args (hp : Preimage) (hst : PointwiseStab) (hm : Membership) (T : ℕ) :
    normArgBudget T ≤ normGrow hp hst hm T := by unfold normGrow; omega

theorem normGrow_stage (hp : Preimage) (hst : PointwiseStab) (hm : Membership) (T : ℕ) :
    normStageBudget hp hst hm T ≤ normGrow hp hst hm T := by unfold normGrow; omega

theorem normParentListCost_mono {n m L W n' m' L' W' : ℕ}
    (hn : n ≤ n') (hm : m ≤ m') (hL : L ≤ L') (hW : W ≤ W') :
    normParentListCost n m L W ≤ normParentListCost n' m' L' W' := by
  unfold normParentListCost
  dsimp only
  gcongr

theorem normGraphCost_mono (hp : Preimage) {n m L n' m' L' : ℕ}
    (hn : n ≤ n') (hm : m ≤ m') (hL : L ≤ L') :
    normGraphCost hp n m L ≤ normGraphCost hp n' m' L' := by
  unfold normGraphCost Prim.boundSize
  dsimp only
  gcongr

theorem normRawReduceCost_mono (hst : PointwiseStab) {n m L W n' m' L' W' : ℕ}
    (hn : n ≤ n') (hm : m ≤ m') (hL : L ≤ L') (hW : W ≤ W') :
    normRawReduceCost hst n m L W ≤ normRawReduceCost hst n' m' L' W' := by
  unfold normRawReduceCost Prim.boundSize groupW
  dsimp only
  gcongr

theorem normCosetsCost_mono (hm : Membership) {n L W n' L' W' : ℕ}
    (hn : n ≤ n') (hL : L ≤ L') (hW : W ≤ W') :
    normCosetsCost hm n L W ≤ normCosetsCost hm n' L' W' := by
  unfold normCosetsCost normOutsideCost Prim.boundSize groupW
  dsimp only
  gcongr

theorem normBlockMapCost_mono {n m W n' m' W' : ℕ}
    (hn : n ≤ n') (hm : m ≤ m') (hW : W ≤ W') :
    normBlockMapCost n m W ≤ normBlockMapCost n' m' W' := by
  unfold normBlockMapCost
  gcongr

theorem normOrbitCost_mono {n W n' W' : ℕ} (hn : n ≤ n') (hW : W ≤ W') :
    normOrbitCost n W ≤ normOrbitCost n' W' := by
  unfold normOrbitCost
  gcongr

/-- A preparation call fits the next common budget, both in output weight and time. -/
theorem normStage_call (hp : Preimage) (hst : PointwiseStab) (hm : Membership)
    {Pg : Program} {env : List Val} {expr : Expr} {f T : ℕ} {input : Val} {R : Val → Prop}
    (ha : Det Pg env expr input (normArgBudget T))
    (hf : FunAll Pg f input (fun w cost => R w ∧ cost ≤ normStageBudget hp hst hm T)) :
    EvalAll Pg env (.call f expr) (fun w cost =>
      R w ∧ w.wt ≤ normGrow hp hst hm T ∧ cost ≤ 2 * normGrow hp hst hm T) := by
  refine (normBound_call ha hf).mono fun w cost hw => ⟨hw.1, ?_, ?_⟩
  · exact hw.2.1.trans (normGrow_stage hp hst hm T)
  · have hc := hw.2.2
    unfold normGrow
    omega

/-- Stage bounds increase as calls are completed. -/
theorem normIter_mono (hp : Preimage) (hst : PointwiseStab) (hm : Membership) (T : ℕ) :
    Monotone (fun i => (normGrow hp hst hm)^[i] T) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [Function.iterate_succ_apply']
  exact normGrow_le hp hst hm _

end GI.Impl
