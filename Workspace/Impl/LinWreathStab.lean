module

public import Workspace.Impl.LinWreathInput

@[expose] public section

/-! The executable two-copy vector stabilizer. VectorStabilizer is its only
cited hypothesis; the permutation and matrix tables are built by the program. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linWreathStabF (input j : ℕ) : Expr := .prim j (.call input (.var 0))
def linWreathStabFuns (b j : ℕ) : List Expr :=
  [linWreathStabF (b + 1) j] ++ linWreathInputFuns (b + 1)

theorem linWreathStabFuns_length (b j : ℕ) : (linWreathStabFuns b j).length = 72 := rfl

structure linWreathStabAt (P : Program) (b j : ℕ) (h : VectorStabilizer) : Prop where
  entry : P.funs[b]? = some (linWreathStabF (b + 1) j)
  input : linWreathInputAt P (b + 1)
  prim : P.prims[j]? = some (vectorStabilizerPrim h)

theorem linWreathStabAt_of (h : VectorStabilizer) {P : Program} {b j : ℕ}
    (hp : P.HasAt b (linWreathStabFuns b j))
    (hj : P.prims[j]? = some (vectorStabilizerPrim h)) : linWreathStabAt P b j h where
  entry := (hp.block (gs := [linWreathStabF (b + 1) j]) 0 rfl).single
  input := linWreathInputAt_of (hp.block 1 rfl)
  prim := hj

theorem linWreathInput_dimensions (I : VecStabInst) (w : Fin I.d → ZMod I.p) :
    I.n ≤ (Val.list [vecStabEnc I, encVec w]).wt ∧
      I.d ≤ (Val.list [vecStabEnc I, encVec w]).wt := by
  have wsrc : (vecStabEnc I).wt < (Val.list [vecStabEnc I, encVec w]).wt :=
    wt_le_wt_list (by simp)
  have wg : (encGroup I.gs).wt < (vecStabEnc I).wt := wt_le_wt_list (by simp [vecStabEnc])
  have wv : (encVec I.v).wt < (vecStabEnc I).wt := wt_le_wt_list (by simp [vecStabEnc])
  have hn := S_le_wt_encGroup I.gs
  have hd := length_lt_wt_list ((List.finRange I.d).map fun i => Val.nat (I.v i).val)
  simp only [List.length_map, List.length_finRange] at hd
  change I.d < (encVec I.v).wt at hd
  constructor
  · nlinarith
  · omega

noncomputable def linWreathStabCost (h : VectorStabilizer) (W : ℕ) : ℕ :=
  10000 * (W + linWreathInputCost W +
    (vectorStabilizerPrim h).boundSize (linWreathInputCost W) + 13 * (2 * W + 1) ^ 6 + 1)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4000 in
theorem linWreathStab_spec (h : VectorStabilizer) {P : Program} {b j : ℕ}
    (hp : linWreathStabAt P b j h) (I : VecStabInst) [Nonempty (Fin I.n)]
    (hd : 0 < I.d) (w : Fin I.d → ZMod I.p) :
    FunAll P b (.list [vecStabEnc I, encVec w]) (fun out cost =>
      GensVal (I.n + I.n) out (vecStabSub (linWreathVecInst I w)) ∧
        cost ≤ linWreathStabCost h (Val.list [vecStabEnc I, encVec w]).wt) := by
  let a := Val.list [vecStabEnc I, encVec w]
  let W := a.wt
  have hb := linWreathInput_spec hp.input I hd w
  have wo := hb.wt_lt.le
  have hsize := (vecStabEnc (linWreathVecInst I w)).size_le_wt.trans wo
  have hprim : (vectorStabilizerPrim h).bound (vecStabEnc (linWreathVecInst I w)) ≤
      (vectorStabilizerPrim h).boundSize (linWreathInputCost W) := by
    unfold Prim.bound Prim.boundSize
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hsize 2) _)
  have hn : I.n ≤ W := (linWreathInput_dimensions I w).1
  have hn' : I.n + I.n + 1 ≤ 2 * W + 1 := by omega
  have hpow := Nat.pow_le_pow_left hn' 6
  have dc := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hb
  have hh := vectorStabilizer_call h (linWreathVecInst I w) hp.prim dc
  apply FunAll.intro hp.entry
  refine hh.mono fun out cost ho => ⟨ho.1, ?_⟩
  have hc := ho.2
  change cost ≤ _ at hc
  change cost ≤ linWreathStabCost h W
  dsimp only [linWreathStabCost]
  change (vecStabEnc (linWreathVecInst I w)).wt ≤ linWreathInputCost W at wo
  change (W + 1 + linWreathInputCost W + (vecStabEnc (linWreathVecInst I w)).wt + 1) +
    (vectorStabilizerPrim h).bound (vecStabEnc (linWreathVecInst I w)) +
    13 * (I.n + I.n + 1) ^ 6 + 1 ≥ cost at hc
  omega

theorem linWreathStabCost_poly (h : VectorStabilizer) :
    PBU (fun _ W _ => linWreathStabCost h W) := by
  have hi := linWreathInputCost_poly
  have hb : PBU (fun _ W _ => (vectorStabilizerPrim h).boundSize (linWreathInputCost W)) :=
    PBU.smul (vectorStabilizerPrim h).c (PBU.pow (PBU.addc hi 2) (vectorStabilizerPrim h).k)
  exact PBU.smul 10000 (PBU.addc (PBU.add (PBU.add (PBU.add PBU.W hi) hb)
    (PBU.smul 13 (PBU.pow (PBU.addc (PBU.smul 2 PBU.W) 1) 6))) 1)

end GI.Impl
