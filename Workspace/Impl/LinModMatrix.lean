module

public import Workspace.Impl.LinModReduce
public import Workspace.Impl.LinMapEncoded

@[expose] public section

/-! Reduce integer vectors and dense matrices entrywise to F_p. -/
namespace GI.Impl
open GI.Cited GI.Lang

theorem linModReduceCost_mono {W V : ℕ} (h : W ≤ V) : linModReduceCost W ≤ linModReduceCost V := by
  unfold linModReduceCost linIntCodecCost
  gcongr

def linModVectorFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ linModReduceFuns (b + 3)

theorem linModVectorFuns_length (b : ℕ) : (linModVectorFuns b).length = 22 := rfl

def linModVectorCost (W : ℕ) : ℕ := linMapBudget W (linModReduceCost (4 * W + 6))

set_option maxHeartbeats 1000000 in
theorem linModVector_spec {P : Program} {b p : ℕ} (hp : P.HasAt b (linModVectorFuns b))
    (hpos : 0 < p) (zs : List ℤ) :
    FunDet P b (.list [.nat p, .list (zs.map encInt)])
      (.list (zs.map fun z : ℤ => Val.nat (z : ZMod p).val))
      (linModVectorCost (Val.list [.nat p, .list (zs.map encInt)]).wt) := by
  let W := (Val.list [.nat p, .list (zs.map encInt)]).wt
  apply linMapEncoded_spec (hp.block 0 rfl) encInt encInt_injective _ _ _ _
  intro z hz
  have wp : (Val.nat p).wt < W := wt_le_wt_list (by simp [W])
  have wz : (encInt z).wt < W :=
    (wt_le_wt_list (List.mem_map.mpr ⟨z, hz, rfl⟩)).trans (wt_le_wt_list (by simp [W]))
  have wi := wt_list2_le (.nat p) (encInt z)
  exact (linModReduce_spec (hp.block 3 rfl) hpos z).mono
    (linModReduceCost_mono (by omega))

theorem linModVectorCost_mono {W V : ℕ} (h : W ≤ V) : linModVectorCost W ≤ linModVectorCost V := by
  unfold linModVectorCost linMapBudget linModReduceCost linIntCodecCost
  gcongr

def linModMatrixFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ linModVectorFuns (b + 3)

theorem linModMatrixFuns_length (b : ℕ) : (linModMatrixFuns b).length = 25 := rfl

def linModMatrixCost (W : ℕ) : ℕ := linMapBudget W (linModVectorCost (4 * W + 6))

set_option maxHeartbeats 1000000 in
theorem linModMatrix_spec {P : Program} {b p : ℕ} (hp : P.HasAt b (linModMatrixFuns b))
    (hpos : 0 < p) (rows : List (List ℤ)) :
    FunDet P b (.list [.nat p, .list (rows.map fun zs => .list (zs.map encInt))])
      (.list (rows.map fun zs => .list (zs.map fun z : ℤ => Val.nat (z : ZMod p).val)))
      (linModMatrixCost (Val.list [.nat p, .list (rows.map fun zs => .list (zs.map encInt))]).wt) := by
  let enc (zs : List ℤ) := Val.list (zs.map encInt)
  let W := (Val.list [.nat p, .list (rows.map enc)]).wt
  have he : Function.Injective enc := by
    intro zs zs' hh
    have hh := Val.list.inj hh
    apply List.ext_getElem (by simpa using congrArg List.length hh)
    intro i hi hi'
    apply encInt_injective
    have h := congrArg (fun vs => vs[i]?) hh
    simpa only [List.getElem?_map, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hi', Option.map_some, Option.some.injEq] using h
  apply linMapEncoded_spec (hp.block 0 rfl) enc he _ _ _ _
  intro zs hzs
  have wp : (Val.nat p).wt < W := wt_le_wt_list (by simp [W])
  have wz : (enc zs).wt < W :=
    (wt_le_wt_list (List.mem_map.mpr ⟨zs, hzs, rfl⟩)).trans (wt_le_wt_list (by simp [W]))
  have wi := wt_list2_le (.nat p) (enc zs)
  exact (linModVector_spec (hp.block 3 rfl) hpos zs).mono
    (linModVectorCost_mono (by dsimp only [W, enc] at *; omega))

theorem linModMatrixCost_poly : PBU (fun _ W _ => linModMatrixCost W) := by
  unfold linModMatrixCost linModVectorCost linMapBudget linModReduceCost linIntCodecCost
  norm_poly

end GI.Impl
