module

public import Workspace.Impl.AggCmpWin
public import Workspace.Impl.AggCertMvInd

@[expose] public section

/-!
# Indicators of lists of numbers

The call of the comparison phase needs two indicators.

* The indicator of the test set `tset t` of a tuple, on the labels `0, …, q - 1`. With it the
  program finds the log of `tset t`: the logs of `CmLogsOK` are in the order of some
  `TestSetOrder`, which the program does not know, so it compares the indicator with the first
  entry `indT T` of each log (`cm_indT_eq`).
* The window indicator of the increment, on the positions `0, …, k - 1`, as in the certificate
  phase (`cp_count_pos`).

Both are the list of the counts `xs.count i` for `i < n` (`cmIndF`, `cm_ind_spec`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups GI.LocalCertificates Equiv
  Equiv.Perm
open GI.Cited (Val encPerm encPts)

/-- The step of the indicator: on `[xs, i]`, the number of `i` in `xs`. -/
def cmIndStepF (cn : ℕ) : Expr := .call cn (mk2 (arg 1) (arg 0))

/-- **The indicator**, on `[n, xs]`: the counts of `0, …, n - 1` in `xs`, with `range` at `r` and
the map of the step at `mi`. -/
def cmIndF (r mi : ℕ) : Expr := .letE (.call r (arg 0)) (.call mi (mk2 (arg 1) (.var 1)))

/-- The cost constant of the indicator. -/
def cmIndK : ℕ := 10 ^ 7

/-- **The indicator of a list of numbers.** -/
theorem cm_ind_spec {P : Program} {f r mi s cn : ℕ} (hf : P.funs[f]? = some (cmIndF r mi))
    (hr : P.HasAt r (rangeFuns r)) (hmi : P.HasAt mi (mapFuns mi s))
    (hs : P.funs[s]? = some (cmIndStepF cn)) (hcn : P.HasAt cn (countFuns cn)) (n : ℕ)
    (xs : List ℕ) {B : ℕ} (hB : ∀ x ∈ xs, x ≤ B) (hn : n ≤ B) (hl : xs.length ≤ B) :
    FunDet P f (.list [.nat n, natList xs]) (natList ((List.range n).map xs.count))
      (cmIndK * (B + 1) ^ 4) := by
  have hxw : (natList xs).wt ≤ 7 * (B + 1) ^ 2 := by
    have := wt_natList_le hB
    have : xs.length * (2 * B + 5) ≤ B * (2 * B + 5) := Nat.mul_le_mul_right _ hl
    nlinarith
  have hstep : ∀ i ∈ List.range n, FunDet P s (.list [natList xs, .nat i]) (.nat (xs.count i))
      (countK * (B + 1) ^ 3 + 200 * (B + 1) ^ 2 + 100) := by
    intro i hi
    have hi' : i ≤ B := by have := List.mem_range.mp hi; omega
    refine FunDet.intro hs ((Det.call (Det.mk2 (Det.arg' (rest := []) (j := 1) rfl)
      (Det.arg' (rest := []) (j := 0) rfl)) (count_spec hcn hB hi' hl)).mono ?_)
    have := wt_list2_le (.nat i) (natList xs)
    have := wt_list2_le (natList xs) (.nat i)
    have := wt_nat_le i
    have := wt_nat_le (xs.count i)
    have : xs.count i ≤ B := List.count_le_length.trans hl
    have : B + 1 ≤ (B + 1) ^ 2 := Nat.le_self_pow (by omega) _
    omega
  have hmap := mapList_spec hmi (List.range n) Val.nat (fun i => Val.nat (xs.count i))
    (c := natList xs) (fun a _ a' _ h => by cases h; rfl) hstep
  have hrange := GI.Impl.range_det hr n
  have hout : Val.list ((List.range n).map fun i => Val.nat (xs.count i)) =
      natList ((List.range n).map xs.count) := by simp [natList, List.map_map, Function.comp_def]
  rw [hout] at hmap
  refine FunDet.intro hf ((Det.letE (Det.call (Det.arg' (rest := []) (j := 0) rfl) hrange)
    (Det.call (Det.mk2 (Det.arg' (rest := [natList (List.range n)]) (j := 1) rfl)
      (Det.var' (i := 1) rfl)) hmap)).mono ?_)
  -- the cost
  have hrw : (natList (List.range n)).wt ≤ 7 * (B + 1) ^ 2 := by
    have := wt_natList_le (B := B) (xs := List.range n) fun x hx => by
      have := List.mem_range.mp hx; omega
    rw [List.length_range] at this
    have : n * (2 * B + 5) ≤ B * (2 * B + 5) := Nat.mul_le_mul_right _ hn
    nlinarith
  have how : (natList ((List.range n).map xs.count)).wt ≤ 7 * (B + 1) ^ 2 := by
    have := wt_natList_le (B := B) (xs := (List.range n).map xs.count) fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact List.count_le_length.trans hl
    rw [List.length_map, List.length_range] at this
    have : n * (2 * B + 5) ≤ B * (2 * B + 5) := Nat.mul_le_mul_right _ hn
    nlinarith
  have e1 : Val.list ((List.range n).map Val.nat) = natList (List.range n) := rfl
  have hmw := wt_list2_le (natList xs) (natList (List.range n))
  have hw1 := wt_list2_le (.nat n) (natList xs)
  have := wt_nat_le n
  have p1 : 1 ≤ B + 1 := by omega
  have p12 : B + 1 ≤ (B + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have p23 : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right p1 (by omega)
  have p34 : (B + 1) ^ 3 ≤ (B + 1) ^ 4 := Nat.pow_le_pow_right p1 (by omega)
  have hlen : (List.range n).length * (countK * (B + 1) ^ 3 + 200 * (B + 1) ^ 2 + 100) ≤
      (B + 1) * (100300 * (B + 1) ^ 3) := by
    rw [List.length_range]
    refine Nat.mul_le_mul (by omega) ?_
    simp only [countK]
    omega
  have hmk : mapK * ((List.range n).length + 1) *
      ((Val.list [natList xs, .list ((List.range n).map Val.nat)]).wt +
        (natList ((List.range n).map xs.count)).wt + 1) ≤ mapK * (B + 1) * (50 * (B + 1) ^ 2) := by
    rw [List.length_range, e1]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e2 : (B + 1) * (100300 * (B + 1) ^ 3) = 100300 * (B + 1) ^ 4 := by ring
  have e3 : mapK * (B + 1) * (50 * (B + 1) ^ 2) = 50000 * (B + 1) ^ 3 := by simp only [mapK]; ring
  have h7 : 7000 * (n + 1) ^ 3 ≤ 7000 * (B + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have : (Val.list [natList xs, natList (List.range n)]).wt =
      (Val.list [natList xs, .list ((List.range n).map Val.nat)]).wt := rfl
  simp only [cmIndK]
  omega

/-! ### The indicator of a test set -/

section Tset

variable {q κ : ℕ}

/-- **The counts of the digits of an injective tuple are the indicator of its set.** -/
theorem cm_indT_eq (t : Fin κ ↪ Fin q) :
    natList ((List.range q).map (stL fun i => ((t i : Fin q) : ℕ)).count) =
      indT (tset (t : Fin κ → Fin q)) := by
  classical
  unfold indT
  rw [encFun_eq_natList, ← List.map_coe_finRange_eq_range, List.map_map]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp_apply]
  have hnd : (stL fun i => ((t i : Fin q) : ℕ)).Nodup := by
    unfold stL
    refine (List.nodup_finRange κ).map fun i j h => ?_
    exact t.injective (Fin.ext h)
  rw [hnd.count]
  congr 1
  apply propext
  simp only [stL, List.mem_map, List.mem_finRange, true_and, tset, Finset.mem_image,
    Finset.mem_univ]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, Fin.ext hi⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩

end Tset

end GI.Impl
