module

public import Workspace.Impl.LinAffineTransportMath

@[expose] public section

/-! One executable affine transporter over the prime field, using the
homogeneous representation and the two-copy vector procedure. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linAffineTransportF (input vector : ℕ) : Expr :=
  .letE (.call input (arg 0)) (.call vector (mk2 (.var 1) (.snoc (arg 1) (.nat 1))))

def linAffineTransportFuns (b j : ℕ) : List Expr :=
  [linAffineTransportF (b + 1) (b + 16)] ++ linAffineInputFuns (b + 1) ++ linVectorTransportFuns (b + 16) j

theorem linAffineTransportFuns_length (b j : ℕ) : (linAffineTransportFuns b j).length = 112 := rfl

structure linAffineTransportAt (P : Program) (b j : ℕ) (h : VectorStabilizer) : Prop where
  entry : P.funs[b]? = some (linAffineTransportF (b + 1) (b + 16))
  input : linAffineInputAt P (b + 1)
  vector : linVectorTransportAt P (b + 16) j h

theorem linAffineTransportAt_of (h : VectorStabilizer) {P : Program} {b j : ℕ}
    (hp : P.HasAt b (linAffineTransportFuns b j))
    (hj : P.prims[j]? = some (vectorStabilizerPrim h)) : linAffineTransportAt P b j h where
  entry := (hp.block (gs := [linAffineTransportF (b + 1) (b + 16)]) 0 rfl).single
  input := linAffineInputAt_of (hp.block 1 rfl)
  vector := linVectorTransportAt_of h (hp.block 16 rfl) hj

noncomputable def linVectorTransportCoefficient (h : VectorStabilizer) : ℕ :=
  (linVectorTransport_spec_poly h).choose
noncomputable def linVectorTransportDegree (h : VectorStabilizer) : ℕ :=
  (linVectorTransport_spec_poly h).choose_spec.choose

noncomputable def linAffineTransportVectorCost (h : VectorStabilizer) (W : ℕ) : ℕ :=
  linVectorTransportCoefficient h * (100 * (W + linAffineInputCost W + 1) + 1) ^ linVectorTransportDegree h
noncomputable def linAffineTransportCost (h : VectorStabilizer) (W : ℕ) : ℕ :=
  100000 * (W + linAffineInputCost W + linAffineTransportVectorCost h W + 1)

theorem linAffineInputCost_mono {W V : ℕ} (h : W ≤ V) : linAffineInputCost W ≤ linAffineInputCost V := by
  simp only [linAffineInputCost, linAffineLayerMapBudget, linAffineLayerMapInputBudget,
    linAffineLayerMatricesBudget, linAffineLayerItemBudget, linAffineMatrixCost,
    linAffineRowsCost, linAffineRowsAcc, linVectorAccWt]
  gcongr

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 6000 in
theorem linAffineTransport_spec (h : VectorStabilizer) {P : Program} {b j : ℕ}
    (hp : linAffineTransportAt P b j h) (I : VecStabInst) [NeZero I.n]
    (c : gens I.gs → Fin I.d → ZMod I.p)
    (hc : ∀ g k, c (g * k) = (I.φ g).val.mulVec (c k) + c g)
    (w : Fin I.d → ZMod I.p) :
    FunAll P b (.list [linAffineLayerInput I c, encVec w]) (fun out cost =>
      linAffineTransportOut I c hc w out ∧
        cost ≤ linAffineTransportCost h (Val.list [linAffineLayerInput I c, encVec w]).wt) := by
  let a := Val.list [linAffineLayerInput I c, encVec w]
  let W := a.wt
  let I' := linAffineLayerInst I c hc
  letI : NeZero I'.n := inferInstanceAs (NeZero I.n)
  let C := linAffineInputCost W
  let B := linAffineTransportVectorCost h W
  let arg := Val.list [vecStabEnc I', encVec (linExtend w 1)]
  have wsrc : (linAffineLayerInput I c).wt < W := wt_le_wt_list (by simp [W, a])
  have ww : (encVec w).wt < W := wt_le_wt_list (by simp [W, a])
  have hb := (linAffineInput_spec hp.input I c hc).mono (linAffineInputCost_mono wsrc.le)
  have wI : (vecStabEnc I').wt ≤ C := hb.wt_lt.le
  have wext : (encVec (linExtend w 1)).wt ≤ W + 8 := by
    rw [linAffineVectorExtend_value I.prime]
    have hh := wt_list_snoc_le ((List.finRange I.d).map fun i => Val.nat (w i).val) (.nat 1)
    have w1 : (Val.nat 1).wt = 3 := rfl
    change (Val.list ((List.finRange I.d).map fun i => Val.nat (w i).val)).wt < W at ww
    omega
  have warg : arg.wt ≤ 100 * (W + C + 1) := by
    have hh := wt_list2_le (vecStabEnc I') (encVec (linExtend w 1))
    dsimp only [arg]
    omega
  have hv : FunAll P (b + 16) arg (fun out cost =>
      linVectorTransportOut I' (linExtend w 1) out ∧ cost ≤ B) := by
    have hh := (linVectorTransport_spec_poly h).choose_spec.choose_spec hp.vector I'
      (show 0 < I'.d by exact Nat.succ_pos _) (linExtend w 1)
    refine FunAll.mono hh fun out cost ho => ⟨ho.1, ho.2.trans ?_⟩
    change linVectorTransportCoefficient h * (arg.wt + 1) ^ linVectorTransportDegree h ≤ B
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right warg 1) _)
  have ds := Det.call (Det.arg' (P := P) (vs := [linAffineLayerInput I c, encVec w])
    (rest := []) (j := 0) rfl) hb
  have dw := Det.arg' (P := P) (vs := [linAffineLayerInput I c, encVec w])
    (rest := [vecStabEnc I']) (j := 1) rfl
  have dext := Det.snoc dw (Det.nat 1)
  rw [← linAffineVectorExtend_value I.prime w] at dext
  have da := Det.mk2 (Det.var' (P := P) (env := [a, vecStabEnc I']) (i := 1) rfl) dext
  have call := normBound_call da hv
  apply FunAll.intro hp.entry
  apply EvalAll.letE ds
  intro v cs hs
  obtain ⟨rfl, hcs⟩ := hs
  refine call.mono fun out cost ho => ⟨linAffineTransportOut_of_vector I c hc w ho.1, ?_⟩
  have hcost := ho.2.2
  have wout := ho.2.1
  change _ ≤ linAffineTransportCost h W
  dsimp only [linAffineTransportCost]
  dsimp only [a, W, I', C, B, arg] at *
  omega

theorem linAffineTransportCost_poly (h : VectorStabilizer) :
    PBU (fun _ W _ => linAffineTransportCost h W) := by
  have hi := linAffineInputCost_poly
  have hv : PBU (fun _ W _ => linAffineTransportVectorCost h W) :=
    PBU.smul (linVectorTransportCoefficient h)
      (PBU.pow (PBU.addc (PBU.smul 100 (PBU.addc (PBU.add PBU.W hi) 1)) 1) (linVectorTransportDegree h))
  exact PBU.smul 100000 (PBU.addc (PBU.add (PBU.add PBU.W hi) hv) 1)

theorem linAffineTransport_spec_poly (h : VectorStabilizer) :
    ∃ K D : ℕ, ∀ {P : Program} {b j : ℕ}, linAffineTransportAt P b j h →
      ∀ (I : VecStabInst) [NeZero I.n]
        (c : gens I.gs → Fin I.d → ZMod I.p)
        (hc : ∀ g k, c (g * k) = (I.φ g).val.mulVec (c k) + c g) (w : Fin I.d → ZMod I.p),
      FunAll P b (.list [linAffineLayerInput I c, encVec w]) (fun out cost =>
        linAffineTransportOut I c hc w out ∧
          cost ≤ K * ((Val.list [linAffineLayerInput I c, encVec w]).wt + 1) ^ D) := by
  obtain ⟨K, D, hKD⟩ := linPoly_source_bound (linAffineTransportCost_poly h)
  refine ⟨K, D, ?_⟩
  intro P b j hp I _ c hc w
  exact FunAll.mono (linAffineTransport_spec h hp I c hc w) fun out cost ho =>
    ⟨ho.1, ho.2.trans (hKD 0 _ _ (Nat.zero_le _) le_rfl)⟩

end GI.Impl
