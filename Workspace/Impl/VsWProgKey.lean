import Workspace.Impl.VsWProgBas
import Workspace.Proved.VsWKey

/-!
# The key program

* `vsWKeyFuns b` (57 functions), `vsWKey_spec`: on `[p, d, vsWVs us]` the key
  `vsWVs (vsWKey p d us)`, cost `10 ^ 8 (N + 1)^5`.
  Meaning: `GI.Proved.vsWKey_eq_iff` (`Proved/VsWKey.lean`).
-/

namespace GI.Impl

open GI.Lang GI.Cited

/-- One entry of the key, on `[[p, rows, d], i]`: sift `(e_i, [])` through the rows. -/
def vsWKeyItemF (sft unit : ℕ) : Expr :=
  .get (.call sft (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
    (mk2 (.call unit (mk2 (.get (arg 0) (.nat 2)) (arg 1))) .nil))) (.nat 0)

/-- The key, on `[p, d, vs]`. -/
def vsWKeyF (rows mp rng : ℕ) : Expr :=
  .call mp (mk2 (mk3 (arg 0) (.call rows (mk2 (arg 0) (arg 2))) (arg 1)) (.call rng (arg 1)))

/-- The key program at base `b` (57 functions). -/
def vsWKeyFuns (b : ℕ) : List Expr :=
  [vsWKeyF (b + 1) (b + 35) (b + 54)] ++ vsWRowsFuns (b + 1) ++ mapFuns (b + 35) (b + 38) ++
    [vsWKeyItemF (b + 39) (b + 51)] ++ vsSiftFuns (b + 39) (b + 42) ++ [vsSiftStepF (b + 43)] ++
    vsLinFuns (b + 43) ++ vsUnitFuns (b + 51) ++ rangeFuns (b + 54)

theorem vsWKeyFuns_length (b : ℕ) : (vsWKeyFuns b).length = 57 := rfl

theorem vsWKeyItem_spec {P : Program} {f sft st lin unit : ℕ}
    (hf : P.funs[f]? = some (vsWKeyItemF sft unit)) (hs : P.HasAt sft (vsSiftFuns sft st))
    (hst : P.funs[st]? = some (vsSiftStepF lin)) (hl : P.HasAt lin (vsLinFuns lin))
    (hu : P.HasAt unit (vsUnitFuns unit)) {p N d : ℕ} (hp1 : 1 < p) (hpN : p ≤ N) (hdN : d ≤ N)
    {rows : List VsRow} (hr : ∀ r ∈ rows, VsRowFits N d 0 r) (hrl : rows.length ≤ N)
    {i : ℕ} (hi : i < d) :
    FunDet P f (.list [.list [.nat p, .list (rows.map VsRow.val), .nat d], .nat i])
      (natList (vsSift p rows (vsUnit d i, [])).1) (10 ^ 7 * (N + 1) ^ 4) := by
  set c := Val.list [.nat p, .list (rows.map VsRow.val), .nat d]
  have g k {v : Val} (hv : [Val.nat p, .list (rows.map VsRow.val), .nat d][k]? = some v) :=
    Det.get' (Det.arg' (P := P) (rest := []) (vs := [c, .nat i]) (j := 0) rfl) (Det.nat k) hv
  have a1 := Det.arg' (P := P) (rest := []) (vs := [c, .nat i]) (j := 1) rfl
  have du := Det.call (Det.mk2 (g 2 rfl) a1) ((vsUnit_spec hu d i).mono fun w c hw => ⟨hw.1, by
      have := hw.2; rw [hw.1] at this; exact this⟩)
  have hP : VsPairFits p N (vsUnit d i, []) :=
    ⟨fun y hy => lt_of_le_of_lt (vsUnit_le_one d i y hy) hp1, by simp,
      by rw [vsUnit_length]; exact hdN, by simp⟩
  have hr' : ∀ r ∈ rows, VsRowFits N (vsUnit d i, ([] : List ℕ)).1.length
      (vsUnit d i, ([] : List ℕ)).2.length r := by
    intro r hr0; rw [vsUnit_length]; exact hr r hr0
  have dsift := Det.call (Det.mk3 (g 0 rfl) (g 1 rfl) (Det.mk2 du Det.nil))
    (vsSift_spec hs hst hl (by omega) hpN hP hr' hrl)
  have dget := Det.get' dsift (Det.nat 0) (show [natList (vsSift p rows (vsUnit d i, [])).1,
    natList (vsSift p rows (vsUnit d i, [])).2][0]? = some (natList (vsSift p rows (vsUnit d i, [])).1)
      from rfl)
  refine FunDet.intro hf (dget.mono ?_)
  have hfits := vsSift_fits (by omega) rows hP
  obtain ⟨l1, l2⟩ := vsSift_length p rows (vsUnit d i, [])
  have wrows := wt_vsRows_le hr (by omega)
  have wU := wt_vsUnit_le d i
  have wU' : 5 * (d + 2) ^ 2 ≤ 20 * (N + 1) ^ 2 := by
    have : (d + 2) ^ 2 ≤ (2 * (N + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  have hcu := vsWUP_cost (u := (natList (vsUnit d i)).wt) hdN (show i ≤ N by omega) wU
  have ws1 := wt_natList_le_sq (B := N) (xs := (vsSift p rows (vsUnit d i, [])).1)
    (fun y hy => (hfits.hx y hy).le.trans hpN) (by rw [l1, vsUnit_length]; exact hdN)
  have ws2 : (natList (vsSift p rows (vsUnit d i, [])).2).wt ≤ 4 := by
    rw [show (vsSift p rows (vsUnit d i, [])).2 = [] from List.eq_nil_of_length_eq_zero (by simpa using l2)]
    decide
  have wp := wt_nat_le p
  have wd := wt_nat_le d
  have wi := wt_nat_le i
  have wc := wt_list3_le (.nat p) (.list (rows.map VsRow.val)) (.nat d)
  have wa := wt_list2_le c (.nat i)
  have w2 := wt_list2_le (.nat d) (.nat i)
  have w3 := wt_list2_le (natList (vsUnit d i)) (.list [])
  have w4 := wt_list3_le (.nat p) (.list (rows.map VsRow.val))
    (.list [natList (vsUnit d i), .list []])
  have w5 := wt_list2_le (natList (vsSift p rows (vsUnit d i, [])).1)
    (natList (vsSift p rows (vsUnit d i, [])).2)
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have ec : c.wt = (Val.list [.nat p, .list (rows.map VsRow.val), .nat d]).wt := rfl
  have ep : vsPairVal (vsSift p rows (vsUnit d i, [])) = .list [natList (vsSift p rows
    (vsUnit d i, [])).1, natList (vsSift p rows (vsUnit d i, [])).2] := rfl
  have eA : vsSiftArg p rows (vsUnit d i, []) = .list [.nat p, .list (rows.map VsRow.val),
    .list [natList (vsUnit d i), .list []]] := rfl
  simp only [ep, eA, wt_list_nil] at *
  omega

set_option maxHeartbeats 1000000 in
/-- **The key program.** -/
theorem vsWKey_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsWKeyFuns b)) {p N d : ℕ}
    (hp1 : 1 < p) (hpN : p ≤ N) (hdN : d ≤ N) {us : List (List ℕ)}
    (hus : GI.Proved.VsWFit p d us) (hl : us.length ≤ N) :
    FunDet P b (.list [.nat p, .nat d, vsWVs us]) (vsWVs (vsWKey p d us))
      (10 ^ 8 * (N + 1) ^ 5) := by
  have h0 : P.funs[b]? = some (vsWKeyF (b + 1) (b + 35) (b + 54)) :=
    h.get (j := 0) (by rw [vsWKeyFuns_length]; omega)
  have hr : P.HasAt (b + 1) (vsWRowsFuns (b + 1)) := h.block 1 rfl
  have hm : P.HasAt (b + 35) (mapFuns (b + 35) (b + 38)) := h.block 35 rfl
  have hit : P.funs[b + 38]? = some (vsWKeyItemF (b + 39) (b + 51)) :=
    h.get (j := 38) (by rw [vsWKeyFuns_length]; omega)
  have hs : P.HasAt (b + 39) (vsSiftFuns (b + 39) (b + 42)) := h.block 39 rfl
  have hst : P.funs[b + 42]? = some (vsSiftStepF (b + 43)) :=
    h.get (j := 42) (by rw [vsWKeyFuns_length]; omega)
  have hl' : P.HasAt (b + 43) (vsLinFuns (b + 43)) := h.block 43 rfl
  have hu : P.HasAt (b + 51) (vsUnitFuns (b + 51)) := h.block 51 rfl
  have hrg : P.HasAt (b + 54) (rangeFuns (b + 54)) := h.block 54 rfl
  set A := Val.list [.nat p, .nat d, vsWVs us]
  have a k {v : Val} (hv : [Val.nat p, .nat d, vsWVs us][k]? = some v) :=
    Det.arg' (P := P) (rest := []) (vs := [Val.nat p, .nat d, vsWVs us]) (j := k) hv
  have hfit := vsWRows_fits (by omega) hpN hdN hus
  have eR : vsWRows p us = (vsInsertAll p (vsWPairs us)).1 := rfl
  have hrf : ∀ r ∈ vsWRows p us, VsRowFits N d 0 r := hfit.rows
  have hrl : (vsWRows p us).length ≤ N := hfit.nrows.trans hl
  have dr := Det.call (Det.mk2 (a 0 rfl) (a 2 rfl)) (vsWRows_spec hr (by omega) hpN hdN hus hl)
  have drg := Det.call (a 1 rfl) ((range_spec hrg d).mono fun w c hw => ⟨hw.1, by
    have := hw.2; rw [hw.1] at this; exact this⟩)
  have eN : natList (List.range d) = .list ((List.range d).map Val.nat) := rfl
  rw [eN] at drg
  have dmap := vsQ_map hm (List.range d) Val.nat
    (fun i => natList (vsSift p (vsWRows p us) (vsUnit d i, [])).1) valNat_injective
    (c := .list [.nat p, .list ((vsWRows p us).map VsRow.val), .nat d]) fun i hi =>
      vsWKeyItem_spec hit hs hst hl' hu hp1 hpN hdN hrf hrl (List.mem_range.mp hi)
  have e1 : (List.range d).map (fun i => natList (vsSift p (vsWRows p us) (vsUnit d i, [])).1) =
      (vsWKey p d us).map natList := by simp [vsWKey]
  rw [e1] at dmap
  refine FunDet.intro h0 ((Det.call (Det.mk2 (Det.mk3 (a 0 rfl) dr (a 1 rfl)) drg) dmap).mono ?_)
  have wrows := wt_vsRows_le hrf (by omega)
  have wkey := wt_vsWVs_le (VsWFit.bnd (GI.Proved.vsWKey_fit (d := d) hp1 us) hpN hdN)
    (by simp [vsWKey]; omega)
  have wus := wt_vsWVs_le (VsWFit.bnd hus hpN hdN) (show us.length ≤ N + 1 by omega)
  have wrg := wt_natList_le_sq (B := N) (xs := List.range d) (fun y hy => by
    simp at hy; omega) (by simp; omega)
  have wp := wt_nat_le p
  have wd := wt_nat_le d
  have wA := wt_list3_le (.nat p) (.nat d) (vsWVs us)
  have w2 := wt_list2_le (.nat p) (vsWVs us)
  have wc := wt_list3_le (.nat p) (.list ((vsWRows p us).map VsRow.val)) (.nat d)
  have wc2 := wt_list2_le (.list [.nat p, .list ((vsWRows p us).map VsRow.val), .nat d])
    (natList (List.range d))
  have q0 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hK : mapK = 1000 := rfl
  have hKl : loopModK = 1000 := rfl
  have krg : loopModK * (d + 1) * ((Val.nat d).wt + d + (natList (List.range d)).wt + 1) ≤
      1000 * (N + 1) * (10 * (N + 1) ^ 2) := by
    rw [hKl]; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have kmap : (List.range d).length * (10 ^ 7 * (N + 1) ^ 4) ≤ (N + 1) * (10 ^ 7 * (N + 1) ^ 4) :=
    Nat.mul_le_mul (by simp; omega) le_rfl
  have eK : (vsWVs (vsWKey p d us)).wt = (Val.list ((vsWKey p d us).map natList)).wt := rfl
  have kmap2 : mapK * ((List.range d).length + 1) *
      ((Val.list [.list [.nat p, .list ((vsWRows p us).map VsRow.val), .nat d],
        .list ((List.range d).map Val.nat)]).wt + (Val.list ((vsWKey p d us).map natList)).wt + 1) ≤
      1000 * (N + 1) * (500 * (N + 1) ^ 3) := by
    rw [hK]
    refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (by simp; omega)) ?_
    have : natList (List.range d) = .list ((List.range d).map Val.nat) := rfl
    rw [this] at wc2 wrg
    omega
  have e3 : (N + 1) * (10 ^ 7 * (N + 1) ^ 4) = 10 ^ 7 * (N + 1) ^ 5 := by ring
  have e4 : 1000 * (N + 1) * (500 * (N + 1) ^ 3) = 500000 * (N + 1) ^ 4 := by ring
  have e5 : 1000 * (N + 1) * (10 * (N + 1) ^ 2) = 10000 * (N + 1) ^ 3 := by ring
  have eA : A.wt = (Val.list [.nat p, .nat d, vsWVs us]).wt := rfl
  rw [eN] at wrg wc2 krg
  omega

end GI.Impl
