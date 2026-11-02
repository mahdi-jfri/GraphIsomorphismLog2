import Workspace.Impl.HNFAbs
import Workspace.Lang.Lib.NatList

/-!
# Powers and the complement of the chosen rows, as programs

Two small programs used by the top-level Hermite program.

* `hnfPow`: on `[q, xs, 1]`, the number `q ^ xs.length`, by a fold that multiplies by `q`. The
  top level folds over the rows of `A`, so it gets `(r T)^r`.
* `hnfComplP`: on `[s, r]` (`s` a list of numbers below `r`), the list of the numbers below `r`
  that are not in `s`, in increasing order. It is `hnfCompl s` of `GI.Proved`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved
open GI.Machine (BinOp len len_le_iff)

/-! ### Powers -/

/-- On `[q, acc, x]`: `acc * q`. -/
def hnfPowStepF : Expr := .arith .mul (arg 1) (arg 0)

def hnfPowFuns (b : ℕ) : List Expr := foldlFuns b (b + 3) ++ [hnfPowStepF]

def hnfPowCost (Y : ℕ) : ℕ := Y * (100 * (Y + 10)) + 1000 * (Y + 1) * (6 * Y + 20)

theorem hnf_pow_le_of_le {q i n : ℕ} (h : i ≤ n) : q ^ i ≤ max 1 (q ^ n) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · rw [Nat.zero_pow hi]; exact Nat.zero_le _
  · exact (Nat.pow_le_pow_right hq h).trans (le_max_right _ _)

set_option maxHeartbeats 1000000 in
/-- **Powers.** -/
theorem hnfPow_spec {P : Program} {b : ℕ} (h : P.HasAt b (hnfPowFuns b)) (q : ℕ) (xs : List Val)
    {Y : ℕ} (hV : (Val.list [.nat q, .list xs, .nat 1]).wt ≤ Y) (hq : q ^ xs.length < 2 ^ Y) :
    FunDet P b (.list [.nat q, .list xs, .nat 1]) (.nat (q ^ xs.length)) (hnfPowCost Y) := by
  have hfold : P.HasAt b (foldlFuns b (b + 3)) := h.left
  have hstep : P.funs[b + 3]? = some hnfPowStepF := by
    simpa [hnfPowFuns, foldlFuns, loopFuns] using h 3 (by simp [hnfPowFuns, foldlFuns, loopFuns])
  have hY1 : 1 ≤ 2 ^ Y := Nat.one_le_two_pow
  have hpow : ∀ i, i ≤ xs.length → q ^ i < 2 ^ Y := fun i hi => by
    have := hnf_pow_le_of_le (q := q) hi
    have : max 1 (q ^ xs.length) < 2 ^ Y := by
      rcases Nat.lt_or_ge Y 1 with hY | hY
      · have : (Val.list [.nat q, .list xs, .nat 1]).wt ≥ 1 := by
          have := length_lt_wt_list [Val.nat q, .list xs, .nat 1]; simp at this; omega
        omega
      · have : 2 ≤ 2 ^ Y := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ Y := Nat.pow_le_pow_right (by decide) hY
        omega
    omega
  have wq : (Val.nat q).wt < Y := lt_of_lt_of_le (wt_le_wt_list (by simp)) hV
  have wxs : ∀ x ∈ xs, x.wt < Y := fun x hx =>
    lt_trans (wt_le_wt_list hx) (lt_of_lt_of_le (wt_le_wt_list (by simp)) hV)
  have hn : xs.length < Y := lt_trans (length_lt_wt_list xs)
    (lt_of_lt_of_le (wt_le_wt_list (by simp)) hV)
  have hf := foldl_spec hfold (c := .nat q) (xs := xs) (acc0 := .nat 1) (M := Y + 2)
    (B := fun _ => 100 * (Y + 10)) (Inv := fun i acc => acc = .nat (q ^ i)) (by simp)
    (fun i acc hi hacc => by rw [hacc]; exact hnf_nat_wt_le (hpow i hi))
    (fun i acc hi hacc => by
      subst hacc
      have d1 := Det.arg' (P := P) (vs := [Val.nat q, .nat (q ^ i), xs[i]]) (rest := []) (j := 1) rfl
      have d0 := Det.arg' (P := P) (vs := [Val.nat q, .nat (q ^ i), xs[i]]) (rest := []) (j := 0) rfl
      have dout := Det.arith (op := .mul) d1 d0
      have e : BinOp.mul.eval (q ^ i) q = q ^ (i + 1) := by
        show q ^ i * q = _; rw [pow_succ]
      rw [e] at dout
      refine ⟨_, hstep, dout.mono ?_⟩
      have w1 := wt_list3_le (.nat q) (.nat (q ^ i)) xs[i]
      have w2 := hnf_nat_wt_le (hpow i hi.le)
      have w3 := hnf_nat_wt_le (hpow (i + 1) hi)
      have w4 := wxs xs[i] (List.getElem_mem hi)
      beta_reduce
      omega)
  refine hf.mono fun w cst hw => ⟨hw.1, ?_⟩
  have hc := hw.2
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
  have h5 : xs.length * (100 * (Y + 10)) ≤ Y * (100 * (Y + 10)) := Nat.mul_le_mul_right _ hn.le
  have h6 : loopModK * (xs.length + 1) * ((Val.list [.nat q, .list xs, .nat 1]).wt + xs.length +
      (Y + 2) + 1) ≤ 1000 * (Y + 1) * (6 * Y + 20) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  unfold hnfPowCost
  exact hc.trans (Nat.add_le_add h5 h6)

/-! ### The complement of the chosen rows -/

/-- The number in a value (`0` for a list). -/
def hnfNatOf : Val → ℕ
  | .nat k => k
  | .list _ => 0

/-- On `[s, x]`: `1` if `x` is not in `s`. -/
def hnfComplTestF (cnt : ℕ) : Expr := .arith .eq (.call cnt (mk2 (arg 1) (arg 0))) (.nat 0)

/-- On `[s, r]`: filter `range r`. -/
def hnfComplF (rng filt : ℕ) : Expr := .call filt (mk2 (arg 0) (.call rng (arg 1)))

def hnfComplFuns (b : ℕ) : List Expr :=
  [hnfComplF (b + 1) (b + 4)] ++ rangeFuns (b + 1) ++ filterFuns (b + 4) (b + 7) ++
    [hnfComplTestF (b + 8)] ++ countFuns (b + 8)

theorem hnfComplFuns_length (b : ℕ) : (hnfComplFuns b).length = 13 := rfl

def hnfComplTestCost (Y : ℕ) : ℕ := countK * (Y + 1) ^ 3 + 1000 * (Y + 10)

def hnfComplCost (Y : ℕ) : ℕ :=
  Y * hnfComplTestCost Y + 10000 * (Y + 1) * (20 * (Y + 1) ^ 2 + 20)

variable {r : ℕ}

theorem hnfCompl_val (s : List (Fin r)) :
    (hnfCompl s).map Fin.val = (List.range r).filter fun k => decide ((s.map Fin.val).count k = 0) := by
  rw [← List.map_coe_finRange_eq_range, List.filter_map]
  unfold hnfCompl
  congr 1
  apply List.filter_congr
  intro i _
  simp only [Function.comp_apply, decide_eq_decide, List.count_eq_zero]
  constructor
  · intro hi hm
    obtain ⟨j, hj, hji⟩ := List.mem_map.mp hm
    exact hi (Fin.ext hji ▸ hj)
  · intro hi hm
    exact hi (List.mem_map_of_mem hm)

/-- The value of the complement. -/
def hnfComplVal (s : List (Fin r)) : Val := natList ((hnfCompl s).map Fin.val)

theorem hnfSVal_eq (s : List (Fin r)) : hnfSVal s = natList (s.map Fin.val) := by
  simp [hnfSVal, natList, List.map_map, Function.comp_def]

set_option maxHeartbeats 2000000 in
/-- **The complement.** -/
theorem hnfComplP_spec {P : Program} {b : ℕ} (h : P.HasAt b (hnfComplFuns b)) (s : List (Fin r))
    (hs : s.length ≤ r) {Y : ℕ} (hrY : r ≤ Y) (hV : (Val.list [hnfSVal s, .nat r]).wt ≤ Y) :
    FunDet P b (.list [hnfSVal s, .nat r]) (hnfComplVal s) (hnfComplCost Y) := by
  have hentry : P.funs[b]? = some (hnfComplF (b + 1) (b + 4)) := by
    simpa using (h.block (gs := [hnfComplF (b + 1) (b + 4)]) 0 rfl).single
  have hrng : P.HasAt (b + 1) (rangeFuns (b + 1)) := by simpa using h.block 1 rfl
  have hfilt : P.HasAt (b + 4) (filterFuns (b + 4) (b + 7)) := by simpa using h.block 4 rfl
  have htest : P.funs[b + 7]? = some (hnfComplTestF (b + 8)) := by
    simpa using (h.block (gs := [hnfComplTestF (b + 8)]) 7 rfl).single
  have hcnt : P.HasAt (b + 8) (countFuns (b + 8)) := by simpa using h.block 8 rfl
  set sv := s.map Fin.val with hsv
  have hsvn : hnfSVal s = natList sv := hnfSVal_eq s
  have wS : (hnfSVal s).wt < Y := lt_of_lt_of_le (wt_le_wt_list (by simp)) hV
  have wr : (Val.nat r).wt < Y := lt_of_lt_of_le (wt_le_wt_list (by simp)) hV
  have hsr : ∀ x ∈ sv, x < r := fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx; exact j.isLt
  have hsvl : sv.length ≤ r := by rw [hsv, List.length_map]; exact hs
  -- the range
  have wR : (natList (List.range r)).wt ≤ 5 * (r + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => (List.mem_range.mp hx).le) (by simp)
  have hrs : FunDet P (b + 1) (.nat r) (natList (List.range r))
      (loopModK * (r + 1) * ((Val.nat r).wt + r + 5 * (r + 1) ^ 2 + 1)) :=
    (range_spec hrng r).mono fun w cst hw => ⟨hw.1, by
      have h1 := hw.2; rw [hw.1] at h1
      exact h1.trans (Nat.mul_le_mul_left _ (by omega))⟩
  -- the test
  set q : Val → Bool := fun x => decide (sv.count (hnfNatOf x) = 0) with hq
  have hp : ∀ x ∈ (List.range r).map Val.nat, FunDet P (b + 7) (.list [natList sv, x])
      (boolVal (q x)) (hnfComplTestCost Y) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have hkr := List.mem_range.mp hk
    have dk := Det.arg' (P := P) (vs := [natList sv, Val.nat k]) (rest := []) (j := 1) rfl
    have ds := Det.arg' (P := P) (vs := [natList sv, Val.nat k]) (rest := []) (j := 0) rfl
    have hc := count_spec hcnt (xs := sv) (j := k) (B := Y) (fun x hx => by
      have := hsr x hx; omega) (by omega) (by omega)
    have dcall := Det.call (Det.mk2 dk ds) hc
    have dout := Det.arith (op := .eq) dcall (Det.nat 0)
    have e : BinOp.eq.eval (sv.count k) 0 = (q (.nat k)).toNat := by
      simp only [BinOp.eval, hq, hnfNatOf]
      split_ifs with h1 <;> simp [h1]
    rw [e] at dout
    apply FunDet.intro htest
    refine dout.mono ?_
    have w1 := wt_list2_le (natList sv) (.nat k)
    have w2 := wt_list2_le (.nat k) (natList sv)
    have w3 : (Val.nat (sv.count k)).wt ≤ r + 2 := by
      have := wt_nat_le (sv.count k); have := List.count_le_length (a := k) (l := sv); omega
    have w4 : (Val.nat (q (.nat k)).toNat).wt ≤ 3 := wt_boolVal_le _
    have w5 : (Val.nat k).wt ≤ r + 2 := by have := wt_nat_le k; omega
    have e0 : (Val.nat 0).wt = 2 := rfl
    have hsvw : (natList sv).wt < Y := by rw [← hsvn]; exact wS
    unfold hnfComplTestCost
    omega
  have hfl := filter_spec hfilt (c := natList sv) (xs := (List.range r).map Val.nat) (q := q)
    (B := fun _ => hnfComplTestCost Y) hp
  have efl : ((List.range r).map Val.nat).filter q = ((hnfCompl s).map Fin.val).map Val.nat := by
    rw [List.filter_map, hnfCompl_val]
    rfl
  have hcl : (hnfCompl s).length ≤ r := by
    unfold hnfCompl; exact (List.length_filter_le _ _).trans (by simp)
  have wC : (hnfComplVal s).wt ≤ 5 * (r + 1) ^ 2 := by
    unfold hnfComplVal
    exact wt_natList_le_sq (fun x hx => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx; exact j.isLt.le) (by simpa using hcl)
  have hfl' : FunDet P (b + 4) (.list [hnfSVal s, natList (List.range r)]) (hnfComplVal s)
      (r * hnfComplTestCost Y + loopModK * (r + 1) *
        ((Val.list [hnfSVal s, natList (List.range r)]).wt + r + 5 * (r + 1) ^ 2 + 1)) := by
    rw [hsvn]
    refine hfl.mono fun w cst hw => ⟨by rw [hw.1, efl]; rfl, ?_⟩
    have hc := hw.2
    have ew : w = hnfComplVal s := by rw [hw.1, efl]; rfl
    rw [ew] at hc
    simp only [List.map_const', List.sum_replicate, List.length_map, List.length_range,
      smul_eq_mul] at hc
    have e2 : (natList (List.range r)) = Val.list ((List.range r).map Val.nat) := rfl
    rw [← e2] at hc
    exact hc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _)
  -- the entry
  have d0 := Det.arg' (P := P) (vs := [hnfSVal s, Val.nat r]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [hnfSVal s, Val.nat r]) (rest := []) (j := 1) rfl
  have dr := Det.call d1 hrs
  have dout := Det.call (Det.mk2 d0 dr) hfl'
  apply FunDet.intro hentry
  refine dout.mono ?_
  have hsvw : (natList sv).wt < Y := by rw [← hsvn]; exact wS
  have w1 := wt_list2_le (hnfSVal s) (natList (List.range r))
  have hr2 : (r + 1) ^ 2 ≤ (Y + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hwr := wt_nat_le r
  have m1 : r * hnfComplTestCost Y ≤ Y * hnfComplTestCost Y := Nat.mul_le_mul_right _ hrY
  have hY2 : Y + 1 ≤ (Y + 1) ^ 2 := by nlinarith
  have hr1 : loopModK * (r + 1) ≤ 1000 * (Y + 1) := by
    show 1000 * (r + 1) ≤ 1000 * (Y + 1); omega
  have m2 : loopModK * (r + 1) * ((Val.list [hnfSVal s, natList (List.range r)]).wt + r +
      5 * (r + 1) ^ 2 + 1) ≤ 1000 * (Y + 1) * (20 * (Y + 1) ^ 2 + 20) :=
    Nat.mul_le_mul hr1 (by omega)
  have m3 : loopModK * (r + 1) * ((Val.nat r).wt + r + 5 * (r + 1) ^ 2 + 1) ≤
      1000 * (Y + 1) * (20 * (Y + 1) ^ 2 + 20) :=
    Nat.mul_le_mul hr1 (by omega)
  have m5 : (Y + 1) ^ 2 ≤ (Y + 1) * (20 * (Y + 1) ^ 2 + 20) := by
    calc (Y + 1) ^ 2 ≤ 1 * (20 * (Y + 1) ^ 2 + 20) := by omega
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have e1 : 1000 * (Y + 1) * (20 * (Y + 1) ^ 2 + 20) = 1000 * ((Y + 1) * (20 * (Y + 1) ^ 2 + 20)) := by ring
  have e2 : 10000 * (Y + 1) * (20 * (Y + 1) ^ 2 + 20) = 10000 * ((Y + 1) * (20 * (Y + 1) ^ 2 + 20)) := by ring
  unfold hnfComplCost
  rw [e2]
  omega

end GI.Impl
