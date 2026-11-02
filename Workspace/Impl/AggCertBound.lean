import Workspace.Impl.AggCertFzSpec

/-!
# The certificate phase: the bound `X W₀`

`AsCertOK` asks a bound `X W₀` on the own work of the phase in terms of the weight bound `W₀` of
the input of the `GiantStep` call. The runner of the phase costs at most
`(calls + 1) runK (cpPhaseB k q P NT n D + 1)` (`cp_cert_core`), and the program for `F_x`, `F_y`
at most `cpFzB W` twice. Here `k`, `q`, `n`, `NT` and the parent weight `P` are bounded by
polynomials in `W₀`, and `D = κ!/2` is a constant.

* `cpG_mono`, `cpPhaseB_mono`, `cpFzB_mono`, `cpFzW_mono`: the budgets grow with their arguments;
  the cited bounds enter only through `Prim.boundSize`, which is monotone (`boundSize_mono`).
* `cp_wt_parV`, `cp_wt_init`: the weights of the parent data and of the start state.
* `cpCertX`: the bound of the phase.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

/-! ### Monotonicity -/

section Mono

variable (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

theorem cp_boundSize_mono (p : Prim) {B B' : ℕ} (h : B ≤ B') : p.boundSize B ≤ p.boundSize B' :=
  boundSize_mono p h

theorem cp_ckTestCost_mono {W W' : ℕ} (h : W ≤ W') : ckTestCost hm W ≤ ckTestCost hm W' := by
  unfold ckTestCost
  have := cp_boundSize_mono (membershipPrim hm) (show 4 * W + 20 ≤ 4 * W' + 20 by omega)
  gcongr

theorem cp_ckFindCost_mono {W W' : ℕ} (h : W ≤ W') : ckFindCost hm W ≤ ckFindCost hm W' := by
  unfold ckFindCost
  have := cp_ckTestCost_mono hm (show 4 * W + 6 ≤ 4 * W' + 6 by omega)
  gcongr

/-- **`cpG` grows with `W`.** -/
theorem cpG_mono {W W' : ℕ} (h : W ≤ W') : cpG hst hpre hm W ≤ cpG hst hpre hm W' := by
  unfold cpG
  have h1 := cardCost_mono hst (show 2 * W ≤ 2 * W' by omega)
  have h2 := cp_boundSize_mono (pointwiseStabPrim hst)
    (show 100 * W ^ 4 ≤ 100 * W' ^ 4 by gcongr)
  have h3 := cp_boundSize_mono (preimagePrim hpre)
    (show 1000 * W ^ 4 ≤ 1000 * W' ^ 4 by gcongr)
  have h4 := cp_ckFindCost_mono hm h
  gcongr

theorem cpBw_mono {k q P NT M₀ D k' q' P' NT' M₀' : ℕ} (hk : k ≤ k') (hq : q ≤ q') (hP : P ≤ P')
    (hN : NT ≤ NT') (hM : M₀ ≤ M₀') : cpBw k q P NT M₀ D ≤ cpBw k' q' P' NT' M₀' D := by
  unfold cpBw
  gcongr

theorem cpBm_mono {W W' : ℕ} (h : W ≤ W') : cpBm hst hpre hm W ≤ cpBm hst hpre hm W' := by
  unfold cpBm
  have := cpG_mono hst hpre hm h
  omega

/-- **`cpPhaseB` grows with its arguments** (with `D` fixed). -/
theorem cpPhaseB_mono {k q P NT n D k' q' P' NT' n' : ℕ} (hk : k ≤ k') (hq : q ≤ q')
    (hP : P ≤ P') (hN : NT ≤ NT') (hn : n ≤ n') :
    cpPhaseB hst hpre hm k q P NT n D ≤ cpPhaseB hst hpre hm k' q' P' NT' n' D := by
  unfold cpPhaseB
  simp only
  have hf : (2 * (NT - 1) + 2) * (n + 1) * (D + 2) ≤ (2 * (NT' - 1) + 2) * (n' + 1) * (D + 2) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
  generalize (2 * (NT - 1) + 2) * (n + 1) * (D + 2) = f0 at hf ⊢
  generalize (2 * (NT' - 1) + 2) * (n' + 1) * (D + 2) = f0' at hf ⊢
  have hB := cpBw_mono (D := D) hk hq hP hN hf
  generalize cpBw k q P NT f0 D = B at hB ⊢
  generalize cpBw k' q' P' NT' f0' D = B' at hB ⊢
  have h1 : 10 ^ 4 * (B + 2) ^ 2 ≤ 10 ^ 4 * (B' + 2) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have h2 := cpBm_mono hst hpre hm h1
  have hL : cpLoopC (cpBm hst hpre hm (10 ^ 4 * (B + 2) ^ 2)) B ≤
      cpLoopC (cpBm hst hpre hm (10 ^ 4 * (B' + 2) ^ 2)) B' := by
    unfold cpLoopC; omega
  exact Nat.add_le_add (Nat.mul_le_mul (by omega) hL) hB

theorem cpFzOutB_mono {W W' : ℕ} (h : W ≤ W') : cpFzOutB hst hpre hm W ≤ cpFzOutB hst hpre hm W' := by
  unfold cpFzOutB
  have := cpG_mono hst hpre hm h
  gcongr

theorem cpFzStepB_mono {W W' : ℕ} (h : W ≤ W') :
    cpFzStepB hst hpre hm W ≤ cpFzStepB hst hpre hm W' := by
  unfold cpFzStepB
  have := cpG_mono hst hpre hm h
  have := cpFzOutB_mono hst hpre hm h
  gcongr

theorem cpFzB_mono {W W' : ℕ} (h : W ≤ W') : cpFzB hst hpre hm W ≤ cpFzB hst hpre hm W' := by
  unfold cpFzB
  have := cpG_mono hst hpre hm h
  have := cpFzStepB_mono hst hpre hm h
  gcongr

theorem cpFzW_mono {k q B NT k' q' B' NT' D : ℕ} (hk : k ≤ k') (hq : q ≤ q') (hB : B ≤ B')
    (hN : NT ≤ NT') : cpFzW k q B NT D ≤ cpFzW k' q' B' NT' D := by
  unfold cpFzW
  gcongr

end Mono

/-! ### Weights of the start of the phase -/

section Wt

variable {k q : ℕ}

theorem cp_wt_idsVal : (idsVal k q).wt ≤ 22 * (k + q + 1) ^ 2 := wt_pairV_le ((1, 1) : Perm (Fin k) × Perm (Fin q))

/-- **The parent data.** -/
theorem cp_wt_parV {n D : ℕ} {sv : Val} {gp : GPairs k q} {osA : List (Fin (k + q))}
    (hgp : gp.length ≤ (k + q) ^ 2) (hos : osA.length ≤ k) :
    (cpParV k q n D sv (gpV gp) (encPts osA)).wt ≤
      2 * sv.wt + 2 * n + 2 * D + 300 * (k + q + 1) ^ 4 := by
  have h := wt_list_le [sv, .list [.nat k, .nat q], gpV gp, .nat n, .nat D, encPts osA,
    pSplitCtx k q, .nat (k + q)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at h
  have a1 := wt_list2_le (.nat k) (.nat q)
  have a2 := cp_wt_gp hgp
  have a3 := wt_nat_le n
  have a4 := wt_nat_le D
  have a5 := cp_wt_pts (q := q) hos
  have a6 := wt_list2_le (.nat k) (idsVal k q)
  have a7 := cp_wt_idsVal (k := k) (q := q)
  have a8 := wt_nat_le (k + q)
  have a9 := wt_nat_le k
  have a10 := wt_nat_le q
  obtain ⟨f1, -, -, f24, -⟩ := cp_pow_facts k q
  have : k + q + 1 ≤ (k + q + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have em : (pSplitCtx k q).wt = (Val.list [.nat k, idsVal k q]).wt := rfl
  unfold cpParV
  omega

end Wt

/-! ### The bound of the phase -/

/-- A size that dominates `k`, `q` and `n`. -/
def cpNW (W₀ : ℕ) : ℕ := W₀ + 3

/-- The number of representatives of one round, `D = κ!/2`. -/
noncomputable def cpDc : ℕ := P₀.κ.factorial / 2

/-- A bound on the number of test sets. -/
noncomputable def cpNTW (W₀ : ℕ) : ℕ := cpNW W₀ ^ P₀.κ

/-- A bound on the weight of the parent data. -/
noncomputable def cpPW (W₀ : ℕ) : ℕ := 2 * W₀ + 2 * cpNW W₀ + 2 * cpDc + 300 * (2 * cpNW W₀ + 1) ^ 4

/-- A bound on the weight of the start state. -/
noncomputable def cpSW (W₀ : ℕ) : ℕ := cpBw (cpNW W₀) (cpNW W₀) (cpPW W₀) (cpNTW W₀) 0 cpDc

/-- A bound on the weight of the output of the runner. -/
noncomputable def cpOW (W₀ : ℕ) : ℕ :=
  2 * (cpNTW W₀ * (421 * (2 * cpNW W₀ + 1) ^ 4) + cpNTW W₀ * (2801 * (2 * cpNW W₀ + 1) ^ 6) + 8)
    + 6

/-- The weight bound of the program for `F_x`, `F_y`, and of the other values of the wrapper. -/
noncomputable def cpWW (W₀ : ℕ) : ℕ :=
  cpFzW (cpNW W₀) (cpNW W₀) (2 * (cpPW W₀ + cpOW W₀ + 3) + 7) (cpNTW W₀) cpDc + cpSW W₀

/-- **The bound of the certificate phase**: the runner (at most `f₀` calls of the step loop) and
the two programs for `F_x`, `F_y`, with the overhead of the wrapper. -/
noncomputable def cpCertX (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) (W₀ : ℕ) :
    ℕ :=
  ((2 * cpNTW W₀ + 2) * (cpNW W₀ + 1) * (cpDc + 2) + 1) *
      (runK * (cpPhaseB hst hpre hm (cpNW W₀) (cpNW W₀) (cpSW W₀) (cpNTW W₀) (cpNW W₀) cpDc + 1)) +
    2 * cpFzB hst hpre hm (cpWW W₀) + 1000 * (cpWW W₀ + 20)

end GI.Impl
