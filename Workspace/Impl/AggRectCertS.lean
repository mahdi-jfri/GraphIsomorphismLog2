module

public import Workspace.Impl.AggRectCertF

@[expose] public section

/-!
# The certificate search meets its contract

`rc_cert_spec`: under `RcCertOk`, the function `f` (the program `rcCertF`) satisfies
`RcCertSpec P f rcCertB` with the certificate function `rcCertFn` and the polynomial bound
`rcCertB M = 10⁵⁰ (M + 21)⁴⁰`.

The input `rcCertIn X x₀` is `[rcTV (rcTab X.col), j, x₀]` (`rc_colVal_eq`). On it the lists
of the search are the lists of `AggRectCertMath.lean` (`rc_fib_eq`, `rc_fib_find`,
`rc_dtab_eq`), so the output is `rcOut (rcTab (rcDm X)) (rcFib X) (X.idx hx) |C|`, and
`rc_out_eq` turns it into the value of the certificate, or `[]`.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)

/-- The cost bound of the certificate search. -/
def rcCertB (M : ℕ) : ℕ := 10 ^ 50 * (M + 21) ^ 40

theorem rc_tab_length {q : ℕ} (X : PairCfg q) : (rcTab X.col).length = q := by simp [rcTab]

theorem rc_tab_rows {q : ℕ} (X : PairCfg q) :
    ∀ row ∈ rcTab X.col, row.length = (rcTab X.col).length := by
  intro row hr
  rw [rc_tab_length]
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hr
  simp

/-- **The certificate search meets `RcCertSpec`.** -/
theorem rc_cert_spec {P : Program} {f flt2 dg md dr gth fq fnd cf flt et rng mb br mbe cond mc
    mcd al cnt cd mg gt tw fe en : ℕ}
    (hP : RcCertOk P f flt2 dg md dr gth fq fnd cf flt et rng mb br mbe cond mc mcd al cnt cd mg gt
      tw fe en) : RcCertSpec P f rcCertB := by
  refine ⟨rcCertFn, fun {q} X x₀ hx => ?_⟩
  have hin : rcCertIn X x₀ = .list [rcTV (rcTab X.col), .nat X.j, .nat x₀] := by
    rw [rcCertIn, rc_colVal_eq]
  have hF : (List.range (rcTab X.col).length).filter
      (fun y => decide (rcAt (rcTab X.col) y y = X.j)) = rcFib X := by
    rw [rc_tab_length]; exact rc_fib_eq X
  have hi : ((List.range (rcTab X.col).length).filter
      (fun y => decide (rcAt (rcTab X.col) y y = X.j))).findIdx (fun y => decide (y = (x₀ : ℕ))) <
      ((List.range (rcTab X.col).length).filter
        (fun y => decide (rcAt (rcTab X.col) y y = X.j))).length := by
    rw [hF, rc_fib_find X hx, rc_fib_length]; exact (X.idx hx).isLt
  obtain ⟨hfd, hwt⟩ := rc_certF_spec hP (rcTab X.col) X.j x₀ (rc_tab_rows X)
    (by rw [rc_tab_length]; exact x₀.isLt) hi (W := (rcCertIn X x₀).wt + 20)
    (by rw [hin]; omega) (by omega)
  rw [hF, rc_fib_find X hx, rc_fib_length, rc_dtab_eq] at hfd hwt
  rw [hin] at hfd hwt ⊢
  obtain ⟨h1, h2⟩ := rc_out_eq X (X.idx hx)
  set M := (Val.list [rcTV (rcTab X.col), Val.nat X.j, Val.nat (x₀ : ℕ)]).wt with hM
  have e : M + 20 + 1 = M + 21 := by ring
  rw [e] at hfd hwt
  refine FunAll.mono hfd fun w c ⟨hw, hc⟩ => ⟨fun h => hw.trans (h1 h), fun h => hw.trans (h2 h),
    hc, ?_⟩
  rw [hw]
  unfold rcCertB
  refine hwt.trans ?_
  have h6 : (M + 21) ^ 6 ≤ (M + 21) ^ 40 := Nat.pow_le_pow_right (by omega) (by omega)
  calc 1000 * (M + 21) ^ 6 ≤ 10 ^ 50 * (M + 21) ^ 6 := Nat.mul_le_mul_right _ (by norm_num)
    _ ≤ 10 ^ 50 * (M + 21) ^ 40 := Nat.mul_le_mul_left _ h6

end GI.Impl
