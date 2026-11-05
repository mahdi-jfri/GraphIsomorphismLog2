module

public import Workspace.Impl.LinObjectAdjoin

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linObjectAdjoinAppendBudget (W : ℕ) : ℕ := linAppendCost (100*(W+1)^2)
noncomputable def linObjectAdjoinBuildBudget (W : ℕ) : ℕ := mkGroupK*((2*W+3)*(W+1))^3
noncomputable def linObjectAdjoinReduceBudget (hm : Membership) (W : ℕ) : ℕ := reduceCost hm W (2*W+1)
noncomputable def linObjectAdjoinSource (hm : Membership) (W : ℕ) : ℕ :=
  100*(W+linObjectAdjoinAppendBudget W+linObjectAdjoinBuildBudget W+linObjectAdjoinReduceBudget hm W+1)^2
noncomputable def linObjectAdjoinCost (hm : Membership) (W : ℕ) : ℕ :=
  100000000*(linObjectAdjoinSource hm W+2)^2

theorem linObjectAdjoinCost_poly (hm : Membership) : PBU (fun _ W _ => linObjectAdjoinCost hm W) := by
  unfold linObjectAdjoinCost linObjectAdjoinSource linObjectAdjoinAppendBudget linObjectAdjoinBuildBudget
    linObjectAdjoinReduceBudget linAppendCost reduceCost memCost
  norm_poly

theorem linObjectGens_append {n : ℕ} (xs ys : List (Equiv.Perm (Fin n))) :
    gens (xs++ys) = gens xs ⊔ gens ys := by
  rw [gens,gens,gens,← Subgroup.closure_union]
  congr 1
  ext g
  exact List.mem_append

set_option maxHeartbeats 400000 in
theorem linObjectAdjoin_spec (hm : Membership) {P : Program} {b jmem n : ℕ}
    (h : linObjectAdjoinAt P b jmem) (hj : P.prims[jmem]? = some (membershipPrim hm))
    (xs : List (Equiv.Perm (Fin n))) (v : Val) (G : Subgroup (Equiv.Perm (Fin n))) (hv : GroupVal n v G) :
    let input := Val.list [.nat n,.list (xs.map encPerm),v]
    FunAll P b input (fun out cost => GroupValC n out (gens xs ⊔ G) ∧ cost ≤ linObjectAdjoinCost hm input.wt) := by
  obtain ⟨ys,rfl,rfl⟩ := hv
  let input := Val.list [.nat n,.list (xs.map encPerm),encGroup ys]
  let W := input.wt
  let AB := linObjectAdjoinAppendBudget W
  let BB := linObjectAdjoinBuildBudget W
  let RB := linObjectAdjoinReduceBudget hm W
  let C := linObjectAdjoinSource hm W
  let zs := xs++1::ys
  have wx : (Val.list (xs.map encPerm)).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wy : (encGroup ys).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wn : (Val.nat n).wt ≤ W := (wt_le_wt_list (by simp [input,W])).le
  have wraw : (Val.list ((1::ys).map encPerm)).wt ≤ W :=
    (wt_le_wt_list (by simp [encGroup,encPerms])).le.trans wy
  have hn : n ≤ W := by
    have hh := S_le_wt_encGroup ys
    have hh' : n+1 ≤ (ys.length+2)*(n+1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hx : xs.length ≤ W := by
    have hh := length_lt_wt_list (xs.map encPerm)
    simp only [List.length_map] at hh
    omega
  have hy : ys.length ≤ W := by
    have hh := length_lt_wt_list ((1::ys).map encPerm)
    simp only [List.length_map,List.length_cons] at hh
    omega
  have hz : zs.length ≤ 2*W+1 := by simp only [zs,List.length_append,List.length_cons]; omega
  have haArg : (Val.list [.list (xs.map encPerm),.list ((1::ys).map encPerm)]).wt ≤ 100*(W+1)^2 := by
    have hh := wt_list2_le (.list (xs.map encPerm)) (.list ((1::ys).map encPerm))
    have hp : W+1 ≤ (W+1)^2 := Nat.le_self_pow (by decide) _
    omega
  have ha : FunDet P (b+1) (.list [.list (xs.map encPerm),.list ((1::ys).map encPerm)])
      (.list (zs.map encPerm)) AB := by
    have hr := linAppend_spec h.append (xs.map encPerm) ((1::ys).map encPerm)
    have hb : linAppendCost (Val.list [.list (xs.map encPerm),.list ((1::ys).map encPerm)]).wt ≤ AB := by
      change linAppendCost _ ≤ linAppendCost (100*(W+1)^2)
      unfold linAppendCost
      gcongr
    simpa only [zs,List.map_append] using hr.mono hb
  have hb : FunDet P (b+4) (.list [.nat n,.list (zs.map encPerm)]) (encGroup zs) BB :=
    (mkGroup_spec h.build zs).mono (by
      change mkGroupK*((zs.length+2)*(n+1))^3 ≤ mkGroupK*((2*W+3)*(W+1))^3
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (Nat.mul_le_mul (by omega) (by omega)) 3))
  have hr : FunDet P (b+11) (encGroup zs) (encGroup (keepList zs)) RB :=
    (reduce_spec hm h.reduce hj zs).mono (linReduceCost_mono hm hn hz)
  have hp : W+AB+BB+RB+1 ≤ (W+AB+BB+RB+1)^2 := Nat.le_self_pow (by decide) _
  have wC : W ≤ C := by change W ≤ 100*(W+AB+BB+RB+1)^2; omega
  have aC : AB ≤ C := by change AB ≤ 100*(W+AB+BB+RB+1)^2; omega
  have bC : BB ≤ C := by change BB ≤ 100*(W+AB+BB+RB+1)^2; omega
  have rC : RB ≤ C := by change RB ≤ 100*(W+AB+BB+RB+1)^2; omega
  have hC : 100 ≤ C := by change 100 ≤ 100*(W+AB+BB+RB+1)^2; omega
  have hd := linObjectAdjoin_comp h (.nat n) (.list (xs.map encPerm)) (encGroup ys)
    (.list ((1::ys).map encPerm)) (.list (zs.map encPerm)) (encGroup zs) (encGroup (keepList zs))
    hC wC rfl (ha.mono aC) (hb.mono bC) (hr.mono rC)
  refine FunAll.mono hd fun out cost hout => ⟨?_,hout.2⟩
  rw [hout.1]
  refine ⟨keepList zs,rfl,?_,length_keepList_le zs⟩
  rw [gens_keepList]
  change gens (xs++1::ys) = _
  rw [gens_append_cons_of_mem (gens xs).one_mem,linObjectGens_append]

end GI.Impl
