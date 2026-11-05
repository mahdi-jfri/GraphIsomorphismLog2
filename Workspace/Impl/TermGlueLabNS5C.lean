module

public import Workspace.Impl.TermGlueLabNS5G
public import Workspace.Impl.TermGlueLabPOGen
public import Workspace.Impl.TermGlueLabPOEps
public import Workspace.Impl.TermGlueLabPGen
public import Workspace.Impl.TermGlueLabPSetZ
public import Workspace.Impl.TermGlueLabPLiftS

@[expose] public section

/-!
# The label driver: the cost bound of step 5

Proof of Theorem A.23, step 5. The cost bound `tmGLNS5Cost … B` of the step-5
function of the driver on inputs of weight at most `B`, and the monotonicity facts used to
reach it from the bounds of `tmGLPStep5_spec`, `tmGLPStep5O_spec`, `tmGLPGen_spec`,
`tmGLPGenO_spec` and `tmGLPEps_spec`. The lift bound `Y` of `tmGLPGen_spec` is
`tmGLPL1C pf (4 B)`: the size `|ps'| + 2k + q + 2` of the lift's input is at most `4 B`
(`tmGLN_lift_size`).
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv
open GI.Cited (Val encPerm encGroup encPerms gens)

/-- The per-generator bound of the plain step 5, for inputs of weight at most `B`. -/
def tmGLNS5G (pm pf : Prim) (Cs Ds Cv Dv Cc Dc Cm Dm B : ℕ) : ℕ → ℕ :=
  tmGLPGenC pm pf (tmGLPL1C pf (4 * B)) Cs Ds Cv Dv Cc Dc Cm Dm

/-- **The cost bound of step 5** for inputs of weight at most `B`. -/
def tmGLNS5Cost (pm pf : Prim) (FA FQ FI : ℕ → ℕ) (Ce De Cs Ds Cv Dv Cc Dc Cm Dm B : ℕ) : ℕ :=
  tmGLNS5C B
    (tmGLPStep5OC (tmGLPStep5C (tmGLPSetDC FA FQ FI Ce De)
      (tmGLPGenOC (tmGLNS5G pm pf Cs Ds Cv Dv Cc Dc Cm Dm B) (tmGLPEpsC pm pf B)) B) B)
    (tmGLPStep5C (tmGLPSetDC FA FQ FI Ce De) (tmGLNS5G pm pf Cs Ds Cv Dv Cc Dc Cm Dm B) B)

theorem tmGLN_L1C_mono (pf : Prim) {M M' : ℕ} (h : M ≤ M') : tmGLPL1C pf M ≤ tmGLPL1C pf M' := by
  unfold tmGLPL1C
  exact Nat.add_le_add (liftLabCost_mono pf h) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 8))

theorem tmGLN_step5C_mono {SC G : ℕ → ℕ} (hSC : Monotone SC) (hG : Monotone G) :
    Monotone (tmGLPStep5C SC G) := by
  intro W W' h
  have h1 := hSC h
  have h2 := tmGLPItemsC_mono hG (show tmGLPStep5W (SC W) W ≤ tmGLPStep5W (SC W') W' by
    unfold tmGLPStep5W; omega)
  unfold tmGLPStep5C
  omega

theorem tmGLN_step5OC_mono {C W C' W' : ℕ} (hC : C ≤ C') (hW : W ≤ W') :
    tmGLPStep5OC C W ≤ tmGLPStep5OC C' W' := by
  have := tmGLPConsC_mono (show 2 * C + 206 ≤ 2 * C' + 206 by omega)
  unfold tmGLPStep5OC
  omega

theorem tmGLN_S5C_mono {W CO CP W' CO' CP' : ℕ} (hW : W ≤ W') (hO : CO ≤ CO') (hP : CP ≤ CP') :
    tmGLNS5C W CO CP ≤ tmGLNS5C W' CO' CP' := by
  have := Nat.pow_le_pow_left (show W + 1 ≤ W' + 1 by omega) 2
  unfold tmGLNS5C
  omega

theorem tmGLN_epsC_q (pm pf : Prim) {q q' : ℕ} (h : q ≤ q') (W : ℕ) :
    tmGLPEpsC pm pf q W ≤ tmGLPEpsC pm pf q' W := by
  have : itParC q ≤ itParC q' := by
    unfold itParC; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  unfold tmGLPEpsC tmGLPOrC
  omega

/-- The size of the lift's input is at most `4` times the weight of the lift context. -/
theorem tmGLN_lift_size {Ω C : Type} {k m q : ℕ} (e : Ω ≃ Fin k) (S : State Ω C)
    (E : Fin m × Fin q ≃ S.dom) (ps' : List (Perm (Fin k) × Perm (Fin m))) :
    ps'.length + k + k + q + 2 ≤ 4 * (Val.list [liftLabCtx k m ps', coordsVal e S E]).wt := by
  set lc : Val := .list [liftLabCtx k m ps', coordsVal e S E] with hlc
  have w1 : (liftLabCtx k m ps').wt < lc.wt := wt_le_wt_list (by simp)
  have w2 : (coordsVal e S E).wt < lc.wt := wt_le_wt_list (by simp)
  have w3 : (encGroup (ps'.map encPair)).wt < (liftLabCtx k m ps').wt := by
    unfold liftLabCtx; exact wt_le_wt_list (by simp)
  have e4 : encGroup (ps'.map encPair) =
      .list [.nat (k + m), .list ((1 :: ps'.map encPair).map encPerm)] := rfl
  have w4 : (Val.list ((1 :: ps'.map encPair).map encPerm)).wt <
      (encGroup (ps'.map encPair)).wt := by rw [e4]; exact wt_le_wt_list (by simp)
  have w5 : (encPerm (1 : Perm (Fin (k + m)))).wt <
      (Val.list ((1 :: ps'.map encPair).map encPerm)).wt := wt_le_wt_list (by simp)
  have w6 := tmGLP_n_lt_wt (1 : Perm (Fin (k + m)))
  have w7 := length_lt_wt_list ((1 :: ps'.map encPair).map encPerm)
  simp only [List.length_map, List.length_cons] at w7
  have w8 := length_lt_wt_list ((List.finRange q).map fun j =>
    natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))
  simp only [List.length_map, List.length_finRange] at w8
  have e8 : (coordsVal e S E).wt = (Val.list ((List.finRange q).map fun j =>
    natList ((List.finRange m).map fun β => ((e (E (β, j)).val : Fin k) : ℕ)))).wt := rfl
  omega

end GI.Impl
