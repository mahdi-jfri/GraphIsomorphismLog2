import Workspace.Impl.AggStructDesSrc
import Workspace.Impl.AggStructRel
import Workspace.Impl.GenProdSq

/-!
# The list of all `κ`-tuples of labels, as a program

The structures of a round color every `κ`-tuple of labels (`stCols_spec`). That module reads the
tuples as the list `(stTs q κ).map stTv`, in the order of `finFunctionFinEquiv`. This file
builds that list: the tuple of index `j < q^κ` is the list of base-`q` digits of `j`
(`stDDec_eq`), so the program maps the digit function `stDDecFuns` over `range (q^κ)`.

`it_ts_spec`: on `[q, κ]`, for `0 < q`, the entry `itTsF` returns `.list ((stTs q κ).map stTv)`
at cost `itTsC (q^κ + q + κ + 10)`, a polynomial of degree `8` in that number. No primitive is
called.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val)

/-- On `[[q, κ], j]`: the entries of the tuple of index `j`. -/
def itTvF (dc : ℕ) : Expr :=
  .get (.call dc (mk3 (mk2 (arg 1) .nil) (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))))
    (.nat 1)

/-- On `[q, κ]`: the list of all `κ`-tuples, by `map itTvF` over `range (q ^ κ)`. -/
def itTsF (pw rb mp : ℕ) : Expr :=
  .call mp (mk2 (.var 0) (.call rb (.call pw (.var 0))))

/-- The weight bound of the values of `itTvF`, for the size parameter `Y`. -/
def itTvW (Y : ℕ) : ℕ := 100 * (Y + 1) ^ 2

/-- The cost bound of `itTvF`. -/
def itTvC (Y : ℕ) : ℕ := 40 * (itTvW Y + 1) + stDDecK * (itTvW Y + 1) ^ 3

/-- The tuple of index `j` is its digits. -/
theorem it_tv_eq {q κ : ℕ} (j : Fin (q ^ κ)) :
    stTv (finFunctionFinEquiv.symm j) = natList (stDDec q κ j) := by
  rw [stDDec_eq]; rfl

theorem it_tv_spec {P : Program} {f dc : ℕ} (hf : P.funs[f]? = some (itTvF dc))
    (hdc : P.HasAt dc (stDDecFuns dc)) {q κ j : ℕ} (hq : 0 < q) (hj : j < q ^ κ) :
    FunDet P f (.list [.list [.nat q, .nat κ], .nat j]) (natList (stDDec q κ j))
      (itTvC (q ^ κ + q + κ + 10)) := by
  set Y := q ^ κ + q + κ + 10 with hY
  set W := itTvW Y with hW
  have hY1 : Y + 1 ≤ (Y + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hWg : W = 100 * (Y + 1) ^ 2 := rfl
  have hWY : 100 * (Y + 1) ≤ W := by omega
  have wq := wt_nat_le q
  have wk := wt_nat_le κ
  have wj := wt_nat_le j
  have hqk := wt_list2_le (.nat q) (.nat κ)
  have hv := wt_list2_le (.list [.nat q, .nat κ]) (.nat j)
  have hnil : (Val.list []).wt ≤ 4 := wt_list_nil.le
  have hjn := wt_list2_le (.nat j) (.list [])
  have hDA := wt_list3_le (.list [.nat j, .list []]) (.nat q) (.nat κ)
  have hdl : (natList (stDDec q κ j)).wt ≤ 5 * (Y + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by have := stDDec_lt hq x hx; omega)
      (by rw [stDDec_length]; omega)
  have hjd : j / q ^ κ ≤ j := Nat.div_le_self _ _
  have wjd := wt_nat_le (j / q ^ κ)
  have hout := wt_list2_le (.nat (j / q ^ κ)) (natList (stDDec q κ j))
  set env : List Val := [.list [.list [.nat q, .nat κ], .nat j]]
  have g0 : StDC P env (arg 0) (.list [.nat q, .nat κ]) 3 0 W :=
    StDC.arg rfl (by omega) (by omega) (by omega)
  have g1 : StDC P env (arg 1) (.nat j) 3 0 W := StDC.arg rfl (by omega) (by omega) (by omega)
  have a1 := StDC.mk2 g1 (StDC.nil (P := P) (env := env) (by omega)) (by omega) (by omega)
  have aq := StDC.get g0 (StDC.nat 0 (by omega)) (v := .nat q) rfl (by omega)
  have ak := StDC.get g0 (StDC.nat 1 (by omega)) (v := .nat κ) rfl (by omega)
  have a3 := StDC.mk3 a1 aq ak (by omega) (by omega)
  have hdec := stDDec_spec hdc hq (j := j) (e := κ) (X := W)
    (by unfold stDDA; omega)
  have c1 := StDC.call a3 hdec (by omega)
  have d := StDC.get c1 (StDC.nat 1 (by omega)) (v := natList (stDDec q κ j)) rfl (by omega)
  refine StDC.funDet hf d ?_
  unfold itTvC
  rw [← hW]
  omega

/-- The value of `itTvF` on an index. -/
def itTvVal (q κ : ℕ) : Val → Val
  | .nat j => natList (stDDec q κ j)
  | _ => .nat 0

/-- The cost bound of `itTsF`, for the size parameter `Y = q^κ + q + κ + 10`. -/
def itTsC (Y : ℕ) : ℕ :=
  Y * itTvC Y + mapK * (Y + 1) * (20 * (Y + 1) ^ 2 + Y * (10 * (Y + 1) ^ 2 + 1) + 20) +
    10000 * (Y + 1) ^ 3 + stDPowK * (3 * Y + 9 + 1) ^ 2 + Y * (10 * (Y + 1) ^ 2 + 1) +
    100 * (Y + 1) ^ 2 + 100 * Y + 100

/-- **The list of all `κ`-tuples.** On `[q, κ]`, for `0 < q`, the entry `itTsF pw rb mp` (with
the power at `pw`, `range` at `rb` and `map itTvF` at `mp`) returns `(stTs q κ).map stTv`. -/
theorem it_ts_spec {P : Program} {f pw rb mp tv dc : ℕ} (hf : P.funs[f]? = some (itTsF pw rb mp))
    (hpw : P.HasAt pw (stDPowFuns pw)) (hrb : P.HasAt rb (rangeFuns rb))
    (hmp : P.HasAt mp (mapFuns mp tv)) (htv : P.funs[tv]? = some (itTvF dc))
    (hdc : P.HasAt dc (stDDecFuns dc)) {q κ : ℕ} (hq : 0 < q) :
    FunDet P f (.list [.nat q, .nat κ]) (.list ((stTs q κ).map stTv))
      (itTsC (q ^ κ + q + κ + 10)) := by
  set Y := q ^ κ + q + κ + 10 with hY
  set n := q ^ κ with hn
  have hY1 : Y + 1 ≤ (Y + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have wq := wt_nat_le q
  have wk := wt_nat_le κ
  have wn := wt_nat_le n
  have hqk := wt_list2_le (.nat q) (.nat κ)
  -- the list of the indices and the list of the tuples
  have hxs : (natList (List.range n)).wt ≤ 5 * (Y + 1) ^ 2 :=
    wt_natList_le_sq (fun x hx => by have := List.mem_range.1 hx; omega) (by simp; omega)
  have hmap := map_det hmp (c := .list [.nat q, .nat κ]) (xs := (List.range n).map Val.nat)
    (F := itTvVal q κ) (B := itTvC Y) fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact it_tv_spec htv hdc hq (List.mem_range.1 hj)
  have hval : ((List.range n).map Val.nat).map (itTvVal q κ) = (stTs q κ).map stTv := by
    rw [List.map_map, stTs, List.map_map, ← List.map_coe_finRange_eq_range, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply]
    exact (it_tv_eq j).symm
  rw [hval] at hmap
  have hlen : ((List.range n).map Val.nat).length = n := by simp
  rw [hlen] at hmap
  have hout0 : (Val.list ((stTs q κ).map stTv)).wt ≤ n * (2 * (5 * (Y + 1) ^ 2) + 1) + 4 :=
    wt_list_le_of ((stTs q κ).map stTv) (c := 5 * (Y + 1) ^ 2) (fun v hv => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hv
      exact wt_stTv_le t (M := Y) (by omega) (by omega)) |>.trans (by simp [stTs_length, hn])
  have hout : (Val.list ((stTs q κ).map stTv)).wt ≤ n * (10 * (Y + 1) ^ 2 + 1) + 4 := by
    have e : 2 * (5 * (Y + 1) ^ 2) + 1 = 10 * (Y + 1) ^ 2 + 1 := by ring
    rw [e] at hout0; exact hout0
  -- the body
  have hpow := stDPow_spec hpw hq (q := q) (e := κ) (X := 3 * Y + 9) (by omega)
  have hrng := st_range_det hrb n
  have hin : (Val.list [.list [.nat q, .nat κ], natList (List.range n)]).wt ≤
      2 * (2 * (q + 2 + κ + 2) + 6 + 5 * (Y + 1) ^ 2) + 6 := by
    have := wt_list2_le (.list [.nat q, .nat κ]) (natList (List.range n)); omega
  have d0 : Det P [.list [.nat q, .nat κ]] (.var 0) (.list [.nat q, .nat κ]) _ := Det.var' rfl
  have d1 := Det.call (Det.call d0 hpow) hrng
  have d2 := Det.call (Det.mk2 d0 d1) hmap
  refine FunDet.intro hf (d2.mono ?_)
  have e1 : natList (List.range n) = .list ((List.range n).map .nat) := rfl

  have hn3 : n * (10 * (Y + 1) ^ 2 + 1) ≤ Y * (10 * (Y + 1) ^ 2 + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hm1 : mapK * (n + 1) * ((Val.list [.list [.nat q, .nat κ], natList (List.range n)]).wt +
      (Val.list ((stTs q κ).map stTv)).wt + 1) ≤
      mapK * (Y + 1) * (20 * (Y + 1) ^ 2 + Y * (10 * (Y + 1) ^ 2 + 1) + 20) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hm2 : n * itTvC Y ≤ Y * itTvC Y := Nat.mul_le_mul_right _ (by omega)
  have hr : 10000 * (n + 1) ^ 3 ≤ 10000 * (Y + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have hk1 : (Val.nat n).wt ≤ Y + 2 := by omega
  have hmr : (Val.list [.list [.nat q, .nat κ], .list ((List.range n).map Val.nat)]).wt =
      (Val.list [.list [.nat q, .nat κ], natList (List.range n)]).wt := rfl
  have wn' : (Val.nat (q ^ κ)).wt ≤ q ^ κ + 2 := wt_nat_le _
  rw [hmr]
  unfold itTsC
  omega

theorem itTsC_mono {Y Y' : ℕ} (h : Y ≤ Y') : itTsC Y ≤ itTsC Y' := by
  unfold itTsC itTvC itTvW
  gcongr

/-- The weight of the list of all `κ`-tuples. -/
theorem it_ts_wt (q κ : ℕ) :
    (Val.list ((stTs q κ).map stTv)).wt ≤
      q ^ κ * (10 * (q ^ κ + q + κ + 11) ^ 2 + 1) + 4 := by
  have h0 := wt_list_le_of ((stTs q κ).map stTv) (c := 5 * (q ^ κ + q + κ + 11) ^ 2)
    (fun v hv => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hv
      exact (wt_stTv_le t (M := q ^ κ + q + κ + 10) (by omega) (by omega)))
  have e : 2 * (5 * (q ^ κ + q + κ + 11) ^ 2) + 1 = 10 * (q ^ κ + q + κ + 11) ^ 2 + 1 := by ring
  rw [e, List.length_map, stTs_length] at h0
  exact h0

end GI.Impl
