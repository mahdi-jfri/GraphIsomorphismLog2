import Workspace.Impl.LinWreathMatrix

/-! Instantiate the vector task on the explicit numbered two-copy cover. -/
namespace GI.Impl
open GI.Cited Equiv

@[simp] theorem linWreathCoverEquiv_val {n : ℕ} [Nonempty (Fin n)]
    (gs : List (Perm (Fin n))) (a : gens gs ≀ᵣ linTwo) :
    (linWreathCoverEquiv gs a).val = linWreathFinCover (gens gs) a := rfl

/-- No representation of the quotient as a permutation group is required.
The covering permutation group itself is supplied to the vector task. -/
noncomputable def linWreathVecInst (I : VecStabInst) [Nonempty (Fin I.n)]
    (w : Fin I.d → ZMod I.p) : VecStabInst where
  n := I.n + I.n
  gs := linWreathCoverGenerators I.gs
  solvable := linWreathCoverGenerators_solvable I.gs I.solvable
  p := I.p
  prime := I.prime
  p_le := I.p_le.trans (Nat.le_add_right _ _)
  d := I.d + I.d
  φ := (linWreathMatrixRep I.φ).comp (linWreathCoverEquiv I.gs).symm.toMonoidHom
  v := linWreathNumberLinear (linWreathPair I.v w)

theorem linWreathVecInst_mem (I : VecStabInst) [Nonempty (Fin I.n)]
    (w : Fin I.d → ZMod I.p) (a : gens I.gs ≀ᵣ linTwo) :
    linWreathCoverEquiv I.gs a ∈ vecStab (linWreathVecInst I w) ↔
      linWreathRep (R := ZMod I.p) (linMatrixLinearEquiv.toMonoidHom.comp I.φ) a
        (linWreathPair I.v w) = linWreathPair I.v w := by
  change (linWreathMatrixRep I.φ ((linWreathCoverEquiv I.gs).symm
    (linWreathCoverEquiv I.gs a))).val.mulVec _ = _ ↔ _
  rw [MulEquiv.symm_apply_apply]
  exact linWreathMatrixRep_fixed I.φ a I.v w

/-- The numbered stabilizer contains a swap exactly when the original vector
transporter is nonempty. -/
theorem linWreathVecInst_transport (I : VecStabInst) [Nonempty (Fin I.n)]
    (w : Fin I.d → ZMod I.p) :
    (∃ a : gens I.gs ≀ᵣ linTwo, a.right = linTwoSwap ∧
      linWreathCoverEquiv I.gs a ∈ vecStab (linWreathVecInst I w)) ↔
      ∃ g : gens I.gs, (I.φ g).val.mulVec I.v = w := by
  simp only [linWreathVecInst_mem]
  exact linWreath_transport_iff (R := ZMod I.p)
    (linMatrixLinearEquiv.toMonoidHom.comp I.φ) I.v w

/-- The first numbered point detects the copy permutation of every cover
element. This test uses one table lookup, not group enumeration. -/
theorem linWreathCover_first_swap_test {n : ℕ} [NeZero n] (gs : List (Perm (Fin n)))
    (a : gens gs ≀ᵣ linTwo) :
    n ≤ (linWreathFinCover (gens gs) a (0 : Fin (n + n)) : ℕ) ↔
      a.right = linTwoSwap := by
  have hz : (0 : Fin (n + n)) = linWreathNumber n ((0 : Fin n), 1) := by
    rw [linWreathNumber_one]
    rfl
  rw [hz, linWreathFinCover_apply, linWreathCover_apply]
  rcases linTwo_cases a.right with ha | ha
  · simp only [ha, one_mul, linWreathNumber_one, Fin.coe_castAdd]
    have hh := (a.left 1 • (0 : Fin n)).isLt
    simp only [linTwoSwap_ne_one.symm, iff_false]
    omega
  · simp only [ha, mul_one, linWreathNumber_swap, Fin.coe_natAdd, Nat.le_add_right,
      iff_self]

end GI.Impl
