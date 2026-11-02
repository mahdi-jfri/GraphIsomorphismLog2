import Workspace.Impl.LinFiniteCoordinates

/-! Canonical full finite-abelian coordinates, reduced componentwise after
an affine operation. The integer encodings are retained between SLP steps. -/
namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linFiniteIntVecVal {d : ℕ} (m : Fin d → ℕ) (x : linFiniteVec m) : Val :=
  linVecVal (fun i => ((x i).val : ℤ))

def linFiniteReduceFuns (b : ℕ) : List Expr :=
  linVectorBinaryFuns b ((b + 3) + 15) ++ linIntFuns (b + 3)

theorem linFiniteReduceFuns_length (b : ℕ) : (linFiniteReduceFuns b).length = 21 := rfl

def linFiniteReduceCost (W d : ℕ) : ℕ := linVectorBinaryCost W d (20 * (W + 1))

theorem linFiniteRemainderWt (x : ℤ) (m W : ℕ) (hm : 0 < m)
    (hw : (encInt (m : ℤ)).wt ≤ W) : (encInt (x % (m : ℤ))).wt ≤ 20 * (W + 1) := by
  apply linWtInt
  have hnonneg : 0 ≤ x % (m : ℤ) := Int.emod_nonneg x (by omega)
  have hlt : x % (m : ℤ) < m := Int.emod_lt_of_pos x (by omega)
  have habs : (x % (m : ℤ)).natAbs < m := by omega
  have hmb := linEncIntAbs (m : ℤ)
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw
  simp only [Int.natAbs_natCast] at hmb
  exact habs.trans (hmb.trans_le hp)

set_option maxHeartbeats 1000000 in
theorem linFiniteReduce_spec {P : Program} {b d : ℕ} (hp : P.HasAt b (linFiniteReduceFuns b))
    (m : Fin d → ℕ) (hm : ∀ i, 0 < m i) (x : Fin d → ℤ) :
    FunDet P b (.list [linVecVal x, linVecVal (fun i => (m i : ℤ))])
      (linFiniteIntVecVal m (fun i => (x i : ZMod (m i))))
      (linFiniteReduceCost (Val.list [linVecVal x, linVecVal (fun i => (m i : ℤ))]).wt d) := by
  let a := Val.list [linVecVal x, linVecVal (fun i => (m i : ℤ))]
  let W := a.wt
  have hs := linInt_spec (hp.block 3 rfl)
  have hmwt : (linVecVal (fun i => (m i : ℤ))).wt < W := wt_le_wt_list (by simp [W, a])
  have hB : ∀ i, (encInt (x i % (m i : ℤ))).wt ≤ 20 * (W + 1) := by
    intro i
    exact linFiniteRemainderWt (x i) (m i) W (hm i) ((linVecEntryWt _ i).trans hmwt).le
  have hh := linVectorBinary_spec (hp.block 0 rfl) (· % ·) hs.rem x (fun i => (m i : ℤ)) _ hB
  have he : (fun i => x i % (m i : ℤ)) = (fun i => (((x i : ZMod (m i)).val : ℕ) : ℤ)) := by
    funext i
    haveI : NeZero (m i) := ⟨Nat.ne_of_gt (hm i)⟩
    exact (ZMod.val_intCast (x i)).symm
  rw [he] at hh
  exact hh

theorem linFiniteReduceCost_poly : PBU (fun d W _ => linFiniteReduceCost W d) := by
  unfold linFiniteReduceCost linVectorBinaryCost linVectorAccWt linIntBinaryCost
    linIntCoreBudget linIntPartsCost linIntCodecCost
  norm_poly

end GI.Impl
