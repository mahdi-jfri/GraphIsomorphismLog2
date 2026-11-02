import Workspace.Impl.AggLiftMath
import Workspace.Lang.Lib.Fold

/-!
# The hierarchy of a continuation, as a program

`LiftAndContinue` lowers the cap of the selected interval to `min(cap, c)` (`lcHier`). On
`[hv, i, c]`, `lcHierF` reads entry `i = [pv, ratio, cap, origin]` of the hierarchy value and
writes `[pv, ratio, cap - (cap - c), origin]` back (`set_spec`); `cap - (cap - c) = min(cap, c)`.
`lcHier_spec`: the output is a canonical value of `lcHier S i c`, at cost at most
`lcHierK (W + 10)²` for an input of weight `W`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp len)
open GI.Cited (Val)

variable {Ω C : Type} {k : ℕ}

/-- **The cap update** on `[hv, i, c]`, with `set` at `bset`. -/
def lcHierF (bset : ℕ) : Expr :=
  .letE (.get (arg 0) (arg 1))
    (.call bset (mk3 (arg 0) (arg 1)
      (mk4 (.get (.var 1) (.nat 0)) (.get (.var 1) (.nat 1))
        (.arith .sub (.get (.var 1) (.nat 2)) (.arith .sub (.get (.var 1) (.nat 2)) (arg 2)))
        (.get (.var 1) (.nat 3)))))

/-- The cost constant of the cap update. -/
def lcHierK : ℕ := 10 ^ 6

theorem lc_sum_set_le (vs : List Val) (i : ℕ) (w : Val) :
    ((vs.set i w).map Val.wt).sum ≤ (vs.map Val.wt).sum + w.wt := by
  induction vs generalizing i with
  | nil => simp
  | cons v vs ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons]; omega
    | succ i =>
      have := ih i
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]; omega

/-- **The cap update meets its specification.** -/
theorem lcHier_spec {P : Program} {f bset : ℕ} (hf : P.funs[f]? = some (lcHierF bset))
    (hs : P.HasAt bset (setFuns bset)) {e : Ω ≃ Fin k} {S : State Ω C} {vs : List Val}
    (hv : HierValC e (.list vs) S.hier) {i : ℕ} (hi : i < S.hier.length) (c : ℕ) :
    FunAll P f (.list [.list vs, .nat i, .nat c]) (fun w cost => (HierValC e w (lcHier S i c) ∧
      w.wt ≤ 8 * (Val.list [.list vs, .nat i, .nat c]).wt + 30) ∧ cost ≤ lcHierK * ((Val.list [.list vs, .nat i, .nat c]).wt + 10) ^ 2) := by
  set a := Val.list [.list vs, .nat i, .nat c] with ha
  set W := a.wt with hW
  have hv' := hv
  obtain ⟨vs', hvs, h2⟩ := hv'
  cases hvs
  have hlen : vs.length = S.hier.length := h2.length_eq
  have hiv : i < vs.length := hlen ▸ hi
  have hget := h2.get hiv hi
  simp only [List.get_eq_getElem] at hget
  obtain ⟨pv, hent, hnew⟩ := lc_intervalVal hget c
  set ent := vs[i] with hentd
  set cap := S.hier[i].cap with hcap
  set w' := Val.list [pv, .nat S.hier[i].ratio, .nat (cap - (cap - c)), .nat S.hier[i].origin]
    with hw'
  -- reads
  have g0 := Det.arg' (P := P) (vs := [.list vs, .nat i, .nat c]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [.list vs, .nat i, .nat c]) (rest := []) (j := 1) rfl
  set entL := Val.list [pv, .nat S.hier[i].ratio, .nat cap, .nat S.hier[i].origin] with hentL
  have de := Det.get' g0 g1 (v := entL) (by rw [List.getElem?_eq_getElem hiv]; exact congrArg _ hent)
  have ge := Det.var' (P := P) (env := [a, entL]) (i := 1) (v := entL) rfl
  have e0 := Det.get' ge (Det.nat 0) (v := pv) rfl
  have e1 := Det.get' ge (Det.nat 1) (v := .nat S.hier[i].ratio) rfl
  have e2 := Det.get' ge (Det.nat 2) (v := .nat cap) rfl
  have e3 := Det.get' ge (Det.nat 3) (v := .nat S.hier[i].origin) rfl
  have h0 := Det.arg' (P := P) (vs := [.list vs, .nat i, .nat c]) (rest := [entL]) (j := 0) rfl
  have h1 := Det.arg' (P := P) (vs := [.list vs, .nat i, .nat c]) (rest := [entL]) (j := 1) rfl
  have h2' := Det.arg' (P := P) (vs := [.list vs, .nat i, .nat c]) (rest := [entL]) (j := 2) rfl
  have dsub := Det.arith (op := .sub) e2 (Det.arith (op := .sub) e2 h2')
  have dw := Det.mk4 e0 e1 dsub e3
  have dm := Det.mk3 h0 h1 dw
  have hset := set_spec hs vs i w'
  have dc := Det.call dm hset
  -- weights
  have wvs : (Val.list vs).wt < W := wt_le_wt_list (by simp)
  have went : ent.wt < (Val.list vs).wt := wt_getElem_lt vs i hiv
  have hentw : ent.wt = entL.wt := by rw [hent]
  have hsum := sum_wt_lt_wt_list [pv, .nat S.hier[i].ratio, .nat cap, .nat S.hier[i].origin]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
  have hic : (Val.nat i).wt < W := wt_le_wt_list (by simp)
  have hcc : (Val.nat c).wt < W := wt_le_wt_list (by simp)
  have hcap' : (Val.nat (cap - (cap - c))).wt ≤ (Val.nat cap).wt := by
    rw [wt_nat, wt_nat]; have := GI.Machine.len_mono (show cap - (cap - c) ≤ cap by omega)
    omega
  have hcap2 : (Val.nat (BinOp.eval .sub cap (cap - c))).wt ≤ (Val.nat cap).wt := by
    simpa [BinOp.eval] using hcap'
  have hcap3 : (Val.nat (BinOp.eval .sub cap c)).wt ≤ (Val.nat cap).wt := by
    rw [wt_nat, wt_nat]; have := GI.Machine.len_mono (show cap - c ≤ cap by omega)
    simp only [BinOp.eval]; omega
  have ewe : w'.wt = (Val.list [pv, .nat S.hier[i].ratio, .nat (cap - (cap - c)),
    .nat S.hier[i].origin]).wt := rfl
  have eent : entL.wt = (Val.list [pv, .nat S.hier[i].ratio, .nat cap,
    .nat S.hier[i].origin]).wt := rfl
  have hWa : W = a.wt := rfl
  have hww : w'.wt ≤ 2 * W + 8 := by
    have := wt_list4_le pv (.nat S.hier[i].ratio) (.nat (cap - (cap - c))) (.nat S.hier[i].origin)
    omega
  have hout := wt_list_le (vs.set i w')
  have hsl := lc_sum_set_le vs i w'
  have hsv := sum_wt_lt_wt_list vs
  have hll : (vs.set i w').length = vs.length := List.length_set ..
  have hlv := length_lt_wt_list vs
  have h3 := wt_list3_le (.list vs) (.nat i) w'
  have hout' : (Val.list (vs.set i w')).wt ≤ 8 * W + 30 := by omega
  have hfd := FunDet.intro hf (Det.letE de dc)
  refine FunAll.mono hfd fun w cost hw => ⟨?_, ?_⟩
  · rw [hw.1]
    exact ⟨hierValC_lcHier hv hi c hnew, hout'⟩
  · refine hw.2.trans ?_
    have hbig : loopModK * (vs.length + 1) * ((Val.list [.list vs, .nat i, w']).wt + vs.length +
        (Val.list (vs.set i w')).wt + 1) ≤ loopModK * (W + 10) * (20 * W + 60) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have hk : loopModK * (W + 10) * (20 * W + 60) ≤ 60 * loopModK * (W + 10) ^ 2 := by
      have : (W + 10) * (20 * W + 60) ≤ 60 * (W + 10) ^ 2 := by nlinarith
      calc loopModK * (W + 10) * (20 * W + 60) = loopModK * ((W + 10) * (20 * W + 60)) := by ring
        _ ≤ loopModK * (60 * (W + 10) ^ 2) := Nat.mul_le_mul_left _ this
        _ = 60 * loopModK * (W + 10) ^ 2 := by ring
    have hsq : W + 10 ≤ (W + 10) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hlk : 60 * loopModK ≤ lcHierK / 2 := by simp [loopModK, lcHierK]
    have hlk' : 60 * loopModK * (W + 10) ^ 2 ≤ lcHierK / 2 * (W + 10) ^ 2 :=
      Nat.mul_le_mul_right _ hlk
    have hK : lcHierK / 2 * (W + 10) ^ 2 + lcHierK / 2 * (W + 10) ^ 2 ≤ lcHierK * (W + 10) ^ 2 := by
      simp only [lcHierK]; omega
    have ea : (Val.list [.list vs, .nat i, .nat c]).wt = W := rfl
    have hW1 : 100 * W + 1000 ≤ lcHierK / 2 * (W + 10) ^ 2 := by
      have : 100 * W + 1000 ≤ 100 * (W + 10) := by omega
      have h5 : 100 * (W + 10) ≤ 100 * (W + 10) ^ 2 := Nat.mul_le_mul_left _ hsq
      have h6 : 100 * (W + 10) ^ 2 ≤ lcHierK / 2 * (W + 10) ^ 2 :=
        Nat.mul_le_mul_right _ (by simp [lcHierK])
      omega
    rw [ea]
    have hja : (Val.list [.list vs, .nat i, .nat c]).wt = a.wt := rfl
    have eb1 : BinOp.eval .sub cap c = cap - c := rfl
    have eb2 : BinOp.eval .sub cap (cap - c) = cap - (cap - c) := rfl
    simp only [eb1, eb2] at *
    have ex3 : (Val.list [.list vs, .nat i, w']).wt = (Val.list [.list vs, .nat i,
      .list [pv, .nat S.hier[i].ratio, .nat (cap - (cap - c)), .nat S.hier[i].origin]]).wt := rfl
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3
    omega

end GI.Impl
