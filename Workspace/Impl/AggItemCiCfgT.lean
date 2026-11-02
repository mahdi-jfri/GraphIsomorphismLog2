import Workspace.Impl.AggItemCiCfgS

/-!
# The configuration query: the fiber lists as a program

`itcqFlF fr ff` on `[rcColVal Z, j, z₀]` (the certificate input of a pair configuration)
reads `q` as the length of the color table, builds `[0, …, q - 1]` and keeps the points `a`
with `col a a = j` (`filter` with `itcqFbT`). The result is the list of the fiber points
`itcqFV Z` (`itcq_flF_spec`, by `itcq_fq_filter`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup)

variable {q : ℕ}

/-- On `[rcColVal Z, j, z₀]`: the fiber points of `Z`. -/
def itcqFlF (fr ff : ℕ) : Expr :=
  .call ff (mk2 (.var 0) (.call fr (.length (.get (.var 0) (.nat 0)))))

/-- The cost bound of `itcqFlF`. -/
def itcqFlC (W : ℕ) : ℕ := 10 ^ 6 * (W + 2) ^ 3

theorem itcq_rc_length (Z : PairCfg q) :
    ((List.finRange q).map (fun a => encFun (Z.col a))).length = q := by simp

theorem itcq_q_le (Z : PairCfg q) : q < (rcColVal Z).wt := by
  have := length_lt_wt_list ((List.finRange q).map fun a => encFun (Z.col a))
  rw [itcq_rc_length] at this
  exact this

/-- The weight of a list of numbers below `q`, of length at most `q`. -/
theorem itcq_fv_wt (Z : PairCfg q) : (itcqFV Z).wt ≤ 5 * (q + 1) ^ 2 := by
  refine wt_natList_le_sq (fun x hx => ?_) ?_
  · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx; exact a.isLt.le
  · simp only [List.length_map, itciFl_length]; exact Finset.card_le_univ _ |>.trans (by simp)

theorem itcq_range_wt (q : ℕ) : (natList (List.range q)).wt ≤ 5 * (q + 1) ^ 2 :=
  wt_natList_le_sq (fun x hx => (List.mem_range.1 hx).le) (by simp)

theorem itcq_flC_arith {W q a A b B C : ℕ} (hq : q ≤ W) (ha : a ≤ W + 2)
    (hA : A ≤ 5 * (W + 1) ^ 2) (hb : b ≤ 2 * (W + 5 * (W + 1) ^ 2) + 6) (hB : B ≤ 5 * (W + 1) ^ 2)
    (hC : C ≤ 10 * (20 * (W + 1) ^ 2 + 1) + loopModK * (q + 1) * (a + q + A + 1) +
      (q * (30 * (20 * (W + 1) ^ 2 + 1)) + loopModK * (q + 1) * (b + q + B + 1))) :
    C ≤ itcqFlC W := by
  unfold itcqFlC
  unfold loopModK at hC
  have hs : W + 1 ≤ (W + 1) ^ 2 := by nlinarith
  have hst : (W + 1) ^ 2 + 1 ≤ (W + 2) ^ 2 := by nlinarith
  have e3 : (W + 2) ^ 3 = (W + 2) * (W + 2) ^ 2 := by ring
  have h1 : 1000 * (q + 1) * (a + q + A + 1) ≤ 1000 * ((W + 2) * (7 * (W + 2) ^ 2)) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have h2 : 1000 * (q + 1) * (b + q + B + 1) ≤ 1000 * ((W + 2) * (18 * (W + 2) ^ 2)) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have h3 : q * (30 * (20 * (W + 1) ^ 2 + 1)) ≤ (W + 2) * (30 * (21 * (W + 2) ^ 2)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 : (W + 2) ^ 2 ≤ (W + 2) * (W + 2) ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
  have e1 : (W + 2) * (7 * (W + 2) ^ 2) = 7 * ((W + 2) * (W + 2) ^ 2) := by ring
  have e2 : (W + 2) * (18 * (W + 2) ^ 2) = 18 * ((W + 2) * (W + 2) ^ 2) := by ring
  have e4 : (W + 2) * (30 * (21 * (W + 2) ^ 2)) = 630 * ((W + 2) * (W + 2) ^ 2) := by ring
  omega

section Prog

variable {P : Program}

/-- **The fiber points** of `Z`, in cost `itcqFlC W` for `W` at least the input weight. -/
theorem itcq_flF_spec {f fr ff fb : ℕ} (hf : P.funs[f]? = some (itcqFlF fr ff))
    (hr : P.HasAt fr (rangeFuns fr)) (hff : P.HasAt ff (filterFuns ff fb))
    (hfb : P.funs[fb]? = some itcqFbT) (Z : PairCfg q) (z₀ : ℕ) {W : ℕ}
    (hW : (Val.list [rcColVal Z, .nat Z.j, .nat z₀]).wt ≤ W) :
    FunDet P f (.list [rcColVal Z, .nat Z.j, .nat z₀]) (itcqFV Z) (itcqFlC W) := by
  set cZ : Val := .list [rcColVal Z, .nat Z.j, .nat z₀] with hcZ
  have hcol : (rcColVal Z).wt < cZ.wt := wt_le_wt_list (by simp)
  have hq := itcq_q_le Z
  have hqW : q ≤ W := by omega
  have hsq : (q + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hRw := itcq_range_wt q
  have hFw := itcq_fv_wt Z
  have hW1 : W + 1 ≤ (W + 1) ^ 2 := by nlinarith
  have hRw' : (natList (List.range q)).wt ≤ 5 * (W + 1) ^ 2 := by omega
  have hFw' : (itcqFV Z).wt ≤ 5 * (W + 1) ^ 2 := by omega
  have v0 := StDC.var' (P := P) (env := [cZ]) (i := 0) (W := 20 * (W + 1) ^ 2) rfl (by omega)
  have g0 := StDC.get v0 (StDC.nat 0 (by omega)) (v := rcColVal Z) rfl (by omega)
  have ln := StDC.length g0 (by rw [itcq_rc_length]; omega)
  rw [itcq_rc_length] at ln
  have hrd : FunDet P fr (.nat q) (natList (List.range q))
      (loopModK * (q + 1) * ((Val.nat q).wt + q + (natList (List.range q)).wt + 1)) :=
    (range_spec hr q).mono fun w c ⟨hw, hc⟩ => ⟨hw, by subst hw; exact hc⟩
  have cr := StDC.call ln hrd (by omega)
  have hin : (Val.list [cZ, natList (List.range q)]).wt ≤ 2 * (W + 5 * (W + 1) ^ 2) + 6 := by
    have := wt_list2_le cZ (natList (List.range q)); omega
  have m2 := StDC.mk2 v0 cr (by omega) (by omega)
  have hfd : FunDet P ff (.list [cZ, natList (List.range q)]) (itcqFV Z)
      (q * (30 * (20 * (W + 1) ^ 2 + 1)) + loopModK * (q + 1) *
        ((Val.list [cZ, natList (List.range q)]).wt + q + (itcqFV Z).wt + 1)) := by
    have key := filter_spec (P := P) hff (c := cZ) (xs := (List.range q).map Val.nat)
      (q := itcqFq Z) (B := fun _ => 30 * (20 * (W + 1) ^ 2 + 1)) (by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
        have ha' := List.mem_range.1 ha
        have h2 := wt_list2_le cZ (.nat a)
        have := wt_nat_le a
        exact itcq_fbT_spec hfb Z z₀ ⟨a, ha'⟩ (by show (Val.list [cZ, .nat a]).wt ≤ 20 * (W + 1) ^ 2; omega))
    refine key.mono fun w c ⟨hw, hc⟩ => ⟨?_, ?_⟩
    · rw [hw, itcq_fq_filter]; rfl
    · have hw' : w = itcqFV Z := by rw [hw, itcq_fq_filter]; rfl
      subst hw'
      simp only [List.map_const', List.sum_replicate, List.length_map, List.length_range,
        smul_eq_mul] at hc
      exact hc
  have cf := StDC.call m2 hfd (by omega)
  refine StDC.funDet hf cf ?_
  have hqw := wt_nat_le q
  refine itcq_flC_arith (a := (Val.nat q).wt) hqW (by omega) hRw' (b := (Val.list [cZ, natList (List.range q)]).wt)
    hin hFw' ?_
  omega

end Prog

end GI.Impl
