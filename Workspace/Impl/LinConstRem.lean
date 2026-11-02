import Workspace.Impl.LinFiniteReduce
import Workspace.Impl.LinMapEncoded

/-! Reduce each entry of an integer row by one target-coordinate modulus. -/
namespace GI.Impl
open GI.Lang GI.Cited

def linScalarRemF (rem : ℕ) : Expr := .call rem (mk2 (arg 1) (arg 0))
def linScalarRemFuns (b : ℕ) : List Expr := [linScalarRemF ((b + 1) + 15)] ++ linIntFuns (b + 1)

theorem linScalarRemFuns_length (b : ℕ) : (linScalarRemFuns b).length = 19 := rfl

def linScalarRemCost (W : ℕ) : ℕ := 1000 * (W + linIntBinaryCost W + 1)

set_option maxHeartbeats 1000000 in
theorem linScalarRem_spec {P : Program} {b : ℕ} (hp : P.HasAt b (linScalarRemFuns b)) (m x : ℤ) :
    FunDet P b (.list [encInt m, encInt x]) (encInt (x % m))
      (linScalarRemCost (Val.list [encInt m, encInt x]).wt) := by
  have hs := (linInt_spec (hp.block 1 rfl)).rem x m
  have he : (Val.list [encInt x, encInt m]).wt = (Val.list [encInt m, encInt x]).wt := by
    simp [wt_list_eq, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  rw [he] at hs
  have dd := Det.call (Det.mk2
    (Det.arg' (P := P) (vs := [encInt m, encInt x]) (rest := []) (j := 1) rfl)
    (Det.arg' (P := P) (vs := [encInt m, encInt x]) (rest := []) (j := 0) rfl)) hs
  have wm : (encInt m).wt < (Val.list [encInt m, encInt x]).wt := wt_le_wt_list (by simp)
  have wx : (encInt x).wt < (Val.list [encInt m, encInt x]).wt := wt_le_wt_list (by simp)
  have wi := wt_list2_le (encInt x) (encInt m)
  have wo := hs.wt_lt
  apply FunDet.intro (hp.block (gs := [linScalarRemF ((b + 1) + 15)]) 0 rfl).single
  refine dd.mono ?_
  unfold linScalarRemCost
  rw [he] at wi
  omega

theorem linScalarRemCost_mono {W V : ℕ} (hW : W ≤ V) : linScalarRemCost W ≤ linScalarRemCost V := by
  have hh := linIntBinaryCost_mono hW
  unfold linScalarRemCost
  omega

def linConstRemFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ linScalarRemFuns (b + 3)

theorem linConstRemFuns_length (b : ℕ) : (linConstRemFuns b).length = 22 := rfl

def linConstRemCost (W : ℕ) : ℕ := linMapBudget W (linScalarRemCost (4 * W + 6))

set_option maxHeartbeats 1000000 in
theorem linConstRem_spec {P : Program} {b : ℕ} (hp : P.HasAt b (linConstRemFuns b))
    (m : ℤ) (xs : List ℤ) :
    FunDet P b (.list [encInt m, .list (xs.map encInt)]) (.list (xs.map fun x => encInt (x % m)))
      (linConstRemCost (Val.list [encInt m, .list (xs.map encInt)]).wt) := by
  let W := (Val.list [encInt m, .list (xs.map encInt)]).wt
  apply linMapEncoded_spec (hp.block 0 rfl) encInt encInt_injective _ _ _ _
  intro x hx
  have wm : (encInt m).wt < W := wt_le_wt_list (by simp [W])
  have wx : (encInt x).wt < W :=
    (wt_le_wt_list (List.mem_map.mpr ⟨x, hx, rfl⟩)).trans (wt_le_wt_list (by simp [W]))
  have wi := wt_list2_le (encInt m) (encInt x)
  exact (linScalarRem_spec (hp.block 3 rfl) m x).mono (linScalarRemCost_mono (by omega))

theorem linConstRemCost_mono {W V : ℕ} (hW : W ≤ V) : linConstRemCost W ≤ linConstRemCost V := by
  unfold linConstRemCost linMapBudget linScalarRemCost
  have hi := linIntBinaryCost_mono (show 4 * W + 6 ≤ 4 * V + 6 by omega)
  gcongr

theorem linConstRemCost_poly : PBU (fun _ W _ => linConstRemCost W) := by
  unfold linConstRemCost linMapBudget linScalarRemCost linIntBinaryCost linIntCoreBudget
    linIntPartsCost linIntCodecCost
  norm_poly

end GI.Impl
