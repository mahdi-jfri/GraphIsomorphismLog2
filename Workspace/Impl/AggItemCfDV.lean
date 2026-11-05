module

public import Workspace.Impl.AggItemCfDCol
public import Workspace.Impl.AggStructDesV

@[expose] public section

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited
open GI.Machine (BinOp)

/-- A lookup costs only the weight of an input color, including the default. -/
theorem itCfD_col_wt (dl tl : List ℕ) (q κ m a b : ℕ) :
    (Val.nat (stDCol dl tl q κ m a b)).wt ≤ (natList dl).wt := by
  unfold stDCol
  rw [List.getD_eq_getElem?_getD]
  cases h : dl[stDHor q κ (stDE tl m a b) κ]? with
  | none =>
    have hw := (natList dl).two_le_size.trans (natList dl).size_le_wt
    simpa only [Option.getD_none, wt_nat, GI.Machine.len_zero, zero_add] using hw
  | some x =>
    simpa only [natList, Option.getD_some] using
      (wt_le_wt_list (vs := dl.map Val.nat)
        (List.mem_map.2 ⟨x, List.mem_of_getElem? h, rfl⟩)).le

theorem ItCfDCtx.wt_stDV {dl tl : List ℕ} {q κ : ℕ} (hc : ItCfDCtx dl tl q κ) (m : ℕ) :
    (natList (stDV dl tl q κ m)).wt ≤ 5 * (2 * (stDA dl tl q κ).wt + 1) ^ 2 := by
  have h := wt_list_le_of ((stDV dl tl q κ m).map Val.nat) (c := (natList dl).wt) (by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
    obtain ⟨z, _, rfl⟩ := List.mem_map.1 hx
    exact itCfD_col_wt dl tl q κ m z z)
  simp only [List.length_map, stDV_length] at h
  have hdw : (natList dl).wt < (stDA dl tl q κ).wt := wt_stDA_ge.2.2.1
  have hq := hc.le_wt.2.2
  have hm := Nat.mul_le_mul hq.le (show 2 * (natList dl).wt + 1 ≤
    2 * (stDA dl tl q κ).wt + 1 by omega)
  change (natList (stDV dl tl q κ m)).wt ≤ _ at h
  generalize (stDA dl tl q κ).wt = A at *
  clear * - h hm
  nlinarith

theorem itCfD_vf_spec {P : Program} {f cf h : ℕ} (hf : P.funs[f]? = some (stDVF cf))
    (hcf : P.funs[cf]? = some (stDColF h)) (hh : P.HasAt h (stDHorFuns h)) {dl tl : List ℕ}
    {q κ : ℕ} (hc : ItCfDCtx dl tl q κ) {m z : ℕ} (hz : z < q) {M : ℕ}
    (hM : (Val.list [stDA dl tl q κ, .nat m]).wt ≤ M) :
    FunDet P f (.list [.list [stDA dl tl q κ, .nat m], .nat z])
      (.nat (stDCol dl tl q κ m z z)) (stDVK * (M + 1) ^ 2) := by
  have hA : (stDA dl tl q κ).wt < (Val.list [stDA dl tl q κ, .nat m]).wt := wt_le_wt_list (by simp)
  have hm : (Val.nat m).wt < (Val.list [stDA dl tl q κ, .nat m]).wt := wt_le_wt_list (by simp)
  have hq := hc.le_wt.2.2
  have hzw := wt_nat_le z
  have hca : (stDCA dl tl q κ m z z).wt ≤ 8 * M + 8 := by
    have := wt_list4_le (stDA dl tl q κ) (.nat m) (.nat z) (.nat z); unfold stDCA; omega
  have hcol := itCfD_col_spec hcf hh hc m hz hz
  obtain ⟨x, hx⟩ : ∃ x, stDCol dl tl q κ m z z = x := ⟨_, rfl⟩
  rw [hx] at hcol ⊢
  have hxw : (Val.nat x).wt ≤ 2 * M + 2 := by
    have h := itCfD_col_wt dl tl q κ m z z
    rw [hx] at h
    have hdw : (natList dl).wt < (stDA dl tl q κ).wt := wt_stDA_ge.2.2.1
    omega
  set W := 30 * M + 60 with hW
  have hvs : (Val.list [.list [stDA dl tl q κ, .nat m], .nat z]).wt ≤ W := by
    have := wt_list2_le (.list [stDA dl tl q κ, .nat m]) (.nat z); omega
  have g0 : StDC P [.list [.list [stDA dl tl q κ, .nat m], .nat z]] (arg 0)
      (.list [stDA dl tl q κ, .nat m]) 3 0 W := StDC.arg rfl hvs (by omega) (by omega)
  have gA := StDC.get (v := stDA dl tl q κ) g0 (StDC.nat 0 (by omega)) rfl (by omega)
  have gm := StDC.get (v := .nat m) g0 (StDC.nat 1 (by omega)) rfl (by omega)
  have gz : StDC P [.list [.list [stDA dl tl q κ, .nat m], .nat z]] (arg 1) (.nat z) 3 0 W :=
    StDC.arg rfl hvs (by omega) (by omega)
  have g4 := StDC.mk4 gA gm gz gz (by
    have := wt_list4_le (stDA dl tl q κ) (.nat m) (.nat z) (.nat z); omega) (by omega)
  have gc := StDC.call g4 hcol (by omega)
  refine StDC.funDet hf gc ?_
  have h1 : (8 * M + 8 + 1) ^ 2 ≤ 81 * (M + 1) ^ 2 := by nlinarith
  have h3 : ((stDCA dl tl q κ m z z).wt + 1) ^ 2 ≤ (8 * M + 8 + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have h5 : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  generalize (M + 1) ^ 2 = X at *
  generalize ((stDCA dl tl q κ m z z).wt + 1) ^ 2 = Y at *
  have h6 : stDColK * Y ≤ stDColK * (81 * X) := Nat.mul_le_mul_left _ (h3.trans h1)
  unfold stDVK
  unfold stDColK at h6 ⊢
  omega

/-- **Range**, with a polynomial bound. -/
theorem itCfD_v_spec {P : Program} {f mb rb vf cf h : ℕ} (hf : P.funs[f]? = some (stDVMapF mb rb))
    (hmb : P.HasAt mb (mapFuns mb vf)) (hrb : P.HasAt rb (rangeFuns rb))
    (hvf : P.funs[vf]? = some (stDVF cf)) (hcf : P.funs[cf]? = some (stDColF h))
    (hh : P.HasAt h (stDHorFuns h)) {dl tl : List ℕ} {q κ : ℕ} (hc : ItCfDCtx dl tl q κ) (m : ℕ)
    {M : ℕ} (hM : (Val.list [stDA dl tl q κ, .nat m]).wt ≤ M) :
    FunDet P f (.list [stDA dl tl q κ, .nat m]) (natList (stDV dl tl q κ m))
      (stDVMK * (M + 1) ^ 3) := by
  have hA : (stDA dl tl q κ).wt < (Val.list [stDA dl tl q κ, .nat m]).wt := wt_le_wt_list (by simp)
  have hq := hc.le_wt.2.2
  have hqw : (Val.nat q).wt < (stDA dl tl q κ).wt := wt_stDA_ge.2.2.2.2.1
  have hX1 : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hX2 : (M + 1) ^ 2 ≤ (M + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hX3 : (M + 1) * (M + 1) ^ 2 = (M + 1) ^ 3 := by ring
  -- the map
  have hmap := map_spec hmb (c := .list [stDA dl tl q κ, .nat m]) (xs := (List.range q).map .nat)
    (R := fun x w => ∃ z, x = Val.nat z ∧ w = Val.nat (stDCol dl tl q κ m z z))
    (B := fun _ => stDVK * (M + 1) ^ 2) (fun x hx => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
      exact FunAll.mono (itCfD_vf_spec hvf hcf hh hc (List.mem_range.1 hz) hM) fun w c hw =>
        ⟨⟨z, rfl, hw.1⟩, hw.2⟩)
  have hV : ∀ ws, List.Forall₂ (fun x w => ∃ z, x = Val.nat z ∧ w = Val.nat (stDCol dl tl q κ m z z))
      ((List.range q).map .nat) ws → Val.list ws = natList (stDV dl tl q κ m) := by
    intro ws hws
    have := forall₂_map_eq (l := List.range q) (f := Val.nat)
      (g := fun z => Val.nat (stDCol dl tl q κ m z z)) (fun z _ w ⟨z', h1, h2⟩ => by
        cases h1; exact h2) hws
    rw [this]; simp [natList, stDV, List.map_map, Function.comp_def]
  have hVw := hc.wt_stDV m
  have hRw : (natList (List.range q)).wt ≤ 5 * (M + 1) ^ 2 := by
    have := wt_natList_le_sq (xs := List.range q) (B := q) (fun x hx => (List.mem_range.1 hx).le)
      (by simp)
    have : (q + 1) ^ 2 ≤ (M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hcw : (Val.list [.list [stDA dl tl q κ, .nat m], natList (List.range q)]).wt ≤
      16 * (M + 1) ^ 2 := by
    have := wt_list2_le (.list [stDA dl tl q κ, .nat m]) (natList (List.range q)); omega
  have hVw' : (natList (stDV dl tl q κ m)).wt ≤ 20 * (M + 1) ^ 2 := by
    have : (2 * (stDA dl tl q κ).wt + 1) ^ 2 ≤ (2 * (M + 1)) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have e : (2 * (M + 1)) ^ 2 = 4 * (M + 1) ^ 2 := by ring
    omega
  have hmapD : FunDet P mb (.list [.list [stDA dl tl q κ, .nat m], natList (List.range q)])
      (natList (stDV dl tl q κ m)) ((M + 1) * (stDVK * (M + 1) ^ 2) +
        mapK * (M + 1) * (40 * (M + 1) ^ 2)) := by
    refine hmap.mono fun w c hw => ?_
    obtain ⟨ws, rfl, hws, hcost⟩ := hw
    have hw' := hV ws hws
    refine ⟨hw', ?_⟩
    rw [hw'] at hcost
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map,
      List.length_range] at hcost
    have h1 : q * (stDVK * (M + 1) ^ 2) ≤ (M + 1) * (stDVK * (M + 1) ^ 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : mapK * (q + 1) * ((Val.list [.list [stDA dl tl q κ, .nat m],
        .list ((List.range q).map .nat)]).wt + (natList (stDV dl tl q κ m)).wt + 1) ≤
        mapK * (M + 1) * (40 * (M + 1) ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by
        rw [← st_natList_range]; omega)
    omega
  -- the body
  set W := 40 * (M + 1) ^ 2 with hW
  have g0 : StDC P [.list [stDA dl tl q κ, .nat m]] (arg 0) (stDA dl tl q κ) 3 0 W :=
    StDC.arg rfl (by omega) (by omega) (by omega)
  have gq := StDC.get (v := .nat q) g0 (StDC.nat 2 (by omega)) rfl (by omega)
  have gr := StDC.call gq (st_range_det hrb q) (by omega)
  have gv : StDC P [.list [stDA dl tl q κ, .nat m]] (.var 0) (.list [stDA dl tl q κ, .nat m]) 1 0
    W := StDC.var' rfl (by omega)
  have g2 := StDC.mk2 gv gr (hcw.trans (by omega)) (by omega)
  have gm := StDC.call g2 hmapD (by omega)
  refine StDC.funDet hf gm ?_
  have hd : 10000 * (q + 1) ^ 3 ≤ 10000 * (M + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have e1 : (M + 1) * (stDVK * (M + 1) ^ 2) = stDVK * (M + 1) ^ 3 := by rw [← hX3]; ring
  have e2 : mapK * (M + 1) * (40 * (M + 1) ^ 2) = 40 * mapK * (M + 1) ^ 3 := by rw [← hX3]; ring
  rw [e1, e2] at *
  generalize (M + 1) ^ 3 = Y at *
  generalize (M + 1) ^ 2 = X at *
  unfold stDVMK stDVK mapK
  omega


end GI.Impl
