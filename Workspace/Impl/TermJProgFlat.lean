import Workspace.Impl.TermJProgPair

/-!
# Flattening a list of lists (program)

`tmJFlatF fl`: on a list of lists, `foldl` of `append` from `[]` (`tmJFlatStepF`), giving the
concatenation (`tmJ_flat_spec`), at cost at most `tmJFlatK X` for `X` the input weight.
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)

/-- The step: on `[c, acc, x]`, `acc ++ x`. -/
def tmJFlatStepF (app : ℕ) : Expr := .call app (mk2 (arg 1) (arg 2))

/-- On a list of lists: their concatenation. -/
def tmJFlatF (fl : ℕ) : Expr := .call fl (mk3 .nil (.var 0) .nil)

/-- The weight of a concatenation. -/
theorem tmJ_wt_flatten_le (xss : List (List Val)) :
    (Val.list xss.flatten).wt ≤ 4 * (Val.list (xss.map Val.list)).wt + 4 := by
  have h2 : (xss.flatten.map Val.wt).sum + xss.flatten.length ≤
      2 * ((xss.map Val.list).map Val.wt).sum := by
    induction xss with
    | nil => simp
    | cons x xs ih =>
      rw [List.flatten_cons, List.map_append, List.sum_append, List.length_append,
        List.map_cons, List.map_cons, List.sum_cons]
      have := sum_wt_lt_wt_list x
      have := length_lt_wt_list x
      omega
  have h1 := wt_list_le xss.flatten
  have h3 := sum_wt_lt_wt_list (xss.map Val.list)
  omega

/-- The cost of a flattening, in the input weight `X`. -/
def tmJFlatK (X : ℕ) : ℕ := 10 ^ 6 * (X + 1) ^ 3

/-- **Flattening.** -/
theorem tmJ_flat_spec {P : Program} {f fl app : ℕ} (hf : P.funs[f]? = some (tmJFlatF fl))
    (hfl : P.HasAt fl (foldlFuns fl (fl + 3))) (hst : P.funs[fl + 3]? = some (tmJFlatStepF app))
    (happ : P.HasAt app (appendFuns app)) (xss : List (List Val)) :
    FunDet P f (.list (xss.map Val.list)) (.list xss.flatten)
      (tmJFlatK (Val.list (xss.map Val.list)).wt) := by
  refine FunDet.intro hf ?_
  unfold tmJFlatF
  set X := (Val.list (xss.map Val.list)).wt with hX
  set xs := xss.map Val.list with hxs
  have hlen : xs.length = xss.length := by simp [hxs]
  have hfw : ∀ i, (Val.list (xss.take i).flatten).wt ≤ 4 * X + 4 := by
    intro i
    have h1 := wt_list_mono (List.IsPrefix.flatten (List.take_prefix i xss))
    have := tmJ_wt_flatten_le xss
    omega
  have hxsX : ∀ (i : ℕ) (hi : i < xs.length), xs[i].wt < X := fun i hi => wt_getElem_lt xs i hi
  have hF := foldl_spec (P := P) hfl (c := .list []) (xs := xs) (acc0 := .list [])
    (Inv := fun i acc => acc = .list (xss.take i).flatten) (M := 4 * X + 4)
    (B := fun _ => 10 ^ 5 * (X + 1) ^ 2) (by simp)
    (by rintro i acc - rfl; exact hfw i) (by
      rintro i acc hi rfl
      have hi' : i < xss.length := by rw [← hlen]; exact hi
      have hxi : xs[i] = .list xss[i] := by simp [hxs]
      refine FunAll.intro hst ?_
      unfold tmJFlatStepF
      set a := [Val.list [], Val.list (xss.take i).flatten, xs[i]] with ha
      have d1 := Det.arg' (P := P) (vs := a) (rest := []) (j := 1)
        (v := .list (xss.take i).flatten) rfl
      have d2 := Det.arg' (P := P) (vs := a) (rest := []) (j := 2) (v := .list xss[i])
        (by simp [ha, hxi])
      have hA := append_spec happ (xss.take i).flatten xss[i]
      refine EvalAll.call_funAll (Det.mk2 d1 d2) fun v ca hv => ?_
      obtain ⟨rfl, hca⟩ := hv
      refine hA.mono fun w' c' hw' => ?_
      obtain ⟨rfl, hc⟩ := hw'
      have e1 : (xss.take i).flatten ++ xss[i] = (xss.take (i + 1)).flatten := by
        rw [List.take_succ_eq_append_getElem hi', List.flatten_append]; simp
      refine ⟨?_, ?_⟩
      · show _ = _
        rw [e1]
      · show _ ≤ 10 ^ 5 * (X + 1) ^ 2
        have w1 := hfw i
        have w2 := hfw (i + 1)
        rw [← e1] at w2
        have w3 := hxsX i hi
        rw [hxi] at w3
        have w4 := length_lt_wt_list xss[i]
        have wa := wt_list3_le (Val.list []) (Val.list (xss.take i).flatten) (Val.list xss[i])
        have w0 : (Val.list []).wt ≤ 5 := by decide
        have wb := wt_list2_le (Val.list (xss.take i).flatten) (Val.list xss[i])
        have hy : xss[i].length + 1 ≤ X + 1 := by omega
        have hz : (Val.list [Val.list (xss.take i).flatten, Val.list xss[i]]).wt + xss[i].length +
            (Val.list ((xss.take i).flatten ++ xss[i])).wt + 1 ≤ 30 * (X + 1) := by omega
        have : loopModK * (xss[i].length + 1) *
            ((Val.list [Val.list (xss.take i).flatten, Val.list xss[i]]).wt + xss[i].length +
              (Val.list ((xss.take i).flatten ++ xss[i])).wt + 1) ≤ 1000 * (X + 1) * (30 * (X + 1)) := by
          unfold loopModK; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hy) hz
        have e2 : 1000 * (X + 1) * (30 * (X + 1)) = 30000 * (X + 1) ^ 2 := by ring
        have hX2 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
        have ra : (Val.list a).wt ≤ 2 * (5 + (4 * X + 4) + X) + 7 := by
          have : xs[i].wt = (Val.list xss[i]).wt := by rw [hxi]
          have := wt_list3_le (Val.list []) (Val.list (xss.take i).flatten) xs[i]
          rw [ha]; omega
        omega)
  have hn : xs.length < X := length_lt_wt_list xs
  have d0 := Det.mk3 (P := P) (env := [Val.list xs]) Det.nil (Det.var' (i := 0) rfl) Det.nil
  have hc := Det.call d0 (w := .list xss.flatten) (cb := xs.length * (10 ^ 5 * (X + 1) ^ 2) +
      loopModK * (xs.length + 1) * ((Val.list [.list [], .list xs, .list []]).wt + xs.length +
        (4 * X + 4) + 1)) (hF.mono fun w c h => ⟨by rw [h.1, hlen, List.take_length], by
          have := h.2
          simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
          exact this⟩)
  refine hc.mono ?_
  have w0 : (Val.list []).wt ≤ 5 := by decide
  have wa := wt_list3_le (Val.list []) (Val.list xs) (Val.list [])
  have wf := tmJ_wt_flatten_le xss
  have hX1 : 1 ≤ X + 1 := by omega
  have P1 : xs.length * (10 ^ 5 * (X + 1) ^ 2) ≤ 10 ^ 5 * (X + 1) ^ 3 := by
    calc xs.length * (10 ^ 5 * (X + 1) ^ 2) ≤ (X + 1) * (10 ^ 5 * (X + 1) ^ 2) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 5 * (X + 1) ^ 3 := by ring
  have P2 : loopModK * (xs.length + 1) * ((Val.list [.list [], .list xs, .list []]).wt + xs.length +
        (4 * X + 4) + 1) ≤ 1000 * (X + 1) * (20 * (X + 1)) := by
    unfold loopModK
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e2 : 1000 * (X + 1) * (20 * (X + 1)) = 20000 * (X + 1) ^ 2 := by ring
  have h23 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_right hX1 (by norm_num)
  have h12 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  show _ ≤ 10 ^ 6 * (X + 1) ^ 3
  omega

end GI.Impl
