import Workspace.Impl.VsHQ

/-!
# `c ^ k` by iteration

`vsHPowIt_spec`: the iteration of `vsHMulE` on `[c, k, 1]` returns `c ^ k`.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp len)

set_option maxHeartbeats 4000000 in
theorem vsHPowIt_spec {P : Program} {it st : ℕ} (hit : P.HasAt it (iterFuns it st))
    (hst : P.funs[st]? = some vsHMulE) {c k M : ℕ} (hM : ∀ i ≤ k, len (c ^ i) + len c + len k ≤ M) :
    FunDet P it (.list [.nat c, .nat k, .nat 1]) (.nat (c ^ k)) (10 ^ 4 * (k + 1) * (M + k + 10)) := by
  have hstep : ∀ i acc, i < k → acc = Val.nat (c ^ i) →
      FunAll P st (.list [.nat c, .nat i, acc])
        (fun w cost => w = Val.nat (c ^ (i + 1)) ∧ cost ≤ 10 * M + 100) := by
    rintro i acc hi rfl
    have a2 := Det.arg' (P := P) (vs := [Val.nat c, .nat i, .nat (c ^ i)]) (rest := []) (j := 2) rfl
    have a0 := Det.arg' (P := P) (vs := [Val.nat c, .nat i, .nat (c ^ i)]) (rest := []) (j := 0) rfl
    refine FunDet.intro hst ((Det.arith (op := .mul) a2 a0).mono ?_)
    have w3 := wt_list3_le (.nat c) (.nat i) (.nat (c ^ i))
    have l1 := hM i hi.le
    have l2 := hM (i + 1) hi
    have e1 : BinOp.eval .mul (c ^ i) c = c ^ (i + 1) := by simp [BinOp.eval, pow_succ]
    rw [e1]
    simp only [wt_nat'] at *
    have : len i ≤ len k := GI.Machine.len_mono hi.le
    omega
  refine (iter_spec hit (c := .nat c) (k := k) (acc0 := .nat 1)
    (Inv := fun i acc => acc = .nat (c ^ i)) (M := M + 2)
    (B := fun _ => 10 * M + 100) (by simp)
    (fun i acc hi h => by rw [h, wt_nat']; have := hM i hi; omega)
    (fun i acc hi h => hstep i acc hi h)).mono fun w cost hw => ⟨hw.1, ?_⟩
  have h2 := hw.2
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
  have w3 := wt_list3_le (.nat c) (.nat k) (.nat 1)
  simp only [wt_nat'] at w3
  have h0 := hM 0 (Nat.zero_le _)
  rw [pow_zero] at h0
  have lk := GI.Machine.len_le_self k
  have l1 : len 1 = 1 := GI.Machine.len_one
  have hX : (Val.list [Val.nat c, Val.nat k, Val.nat 1]).wt + k + (M + 2) + 1 ≤ 5 * (M + 10) + k := by
    omega
  have h3 : loopModK * (k + 1) * ((Val.list [Val.nat c, Val.nat k, Val.nat 1]).wt + k + (M + 2) + 1) ≤
      1000 * (k + 1) * (5 * (M + 10) + k) := Nat.mul_le_mul (le_refl _) hX
  have h4 : k * (10 * M + 100) ≤ 10 * (k + 1) * (M + k + 10) := by nlinarith
  have h5 : 1000 * (k + 1) * (5 * (M + 10) + k) ≤ 5000 * (k + 1) * (M + k + 10) := by
    have : 5 * (M + 10) + k ≤ 5 * (M + k + 10) := by omega
    calc 1000 * (k + 1) * (5 * (M + 10) + k) ≤ 1000 * (k + 1) * (5 * (M + k + 10)) :=
          Nat.mul_le_mul_left _ this
      _ = 5000 * (k + 1) * (M + k + 10) := by ring
  have e1 : 10 ^ 4 * (k + 1) * (M + k + 10) = 10 * (k + 1) * (M + k + 10) +
      5000 * (k + 1) * (M + k + 10) + 4990 * (k + 1) * (M + k + 10) := by ring
  have lk' : loopModK = 1000 := rfl
  rw [lk'] at h2 h3
  clear hw
  linarith

end GI.Impl
