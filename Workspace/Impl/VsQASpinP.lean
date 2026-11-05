module

public import Workspace.Impl.VsQABlkP

@[expose] public section

/-!
# The orbit sum of piece `0`

On `[[p, D, P₀], Bm]` the program `vsQASpinE` returns a basis of the span of the images
`M P₀`, `M ∈ Bm` (`vsQASpinB_spec`). With `Bm = vsQBm s` and `P₀` piece `0`, the span is
`vsQAW s Lb` (`vsQASpin_span`).
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

/-- On `[[p, D, P₀], M]`: the image `M P₀`. -/
def vsQASpinItE (img : ℕ) : Expr :=
  .call img (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1) (.get (arg 0) (.nat 2)))

/-- On `[[p, D, P₀], Bm]`: a basis of the span of the images. -/
def vsQASpinE (mp cat bas : ℕ) : Expr :=
  .call bas (mk2 (.get (arg 0) (.nat 0)) (.call cat (.call mp (mk2 (arg 0) (arg 1)))))

/-- The layout of the spin program. -/
structure VsQASpinAt (P : Program) (f mp it img cat bas : ℕ) : Prop where
  hf : P.funs[f]? = some (vsQASpinE mp cat bas)
  hmp : P.HasAt mp (mapFuns mp it)
  hit : P.funs[it]? = some (vsQASpinItE img)
  himg : P.HasAt img (vsWImgFuns img)
  hcat : P.HasAt cat (vsWFlatFuns cat)
  hbas : P.HasAt bas (vsWBasFuns bas)

/-- The images of `P₀` under the matrices of `Bm`. -/
noncomputable def vsQSpinL (p D : ℕ) (Bm : List (List (List ℕ))) (P₀ : List (List ℕ)) : List (List ℕ) :=
  Bm.flatMap fun M => vsWImg p D M P₀

/-- The cost of the spin program. -/
def vsQASpinCost (N : ℕ) : ℕ := 10 ^ 10 * (N + 1) ^ 7

theorem vsQSpinL_length {p D : ℕ} (Bm : List (List (List ℕ))) (P₀ : List (List ℕ)) :
    (vsQSpinL p D Bm P₀).length = Bm.length * P₀.length := by
  simp [vsQSpinL, vsWImg, List.length_flatMap, List.sum_replicate, List.map_const']

theorem vsQSpinL_fit {p D : ℕ} (hp : 0 < p) {Bm : List (List (List ℕ))} (hB : ∀ M ∈ Bm, VsWSq p D M)
    (P₀ : List (List ℕ)) : VsWFit p D (vsQSpinL p D Bm P₀) := by
  intro u hu
  simp only [vsQSpinL, List.mem_flatMap] at hu
  obtain ⟨M, hM, hu⟩ := hu
  exact vsWImg_fit hp (hB M hM) P₀ u hu

set_option maxHeartbeats 4000000 in
/-- **The spin program.** -/
theorem vsQASpinB_spec {P : Program} {f mp it img cat bas : ℕ} (L : VsQASpinAt P f mp it img cat bas)
    {p N D : ℕ} (hp : 0 < p) (hpN : p ≤ N) (hDN : D ≤ N) {Bm : List (List (List ℕ))}
    (hB : ∀ M ∈ Bm, VsWSq p D M) (hBl : Bm.length ≤ N) {P₀ : List (List ℕ)} (hP : VsWFit p D P₀)
    (hPl : P₀.length ≤ N) (hBP : Bm.length * P₀.length ≤ N) :
    FunDet P f (.list [.list [.nat p, .nat D, vsWVs P₀], vsFMatsVal Bm])
      (vsWVs (vsWBas p (vsQSpinL p D Bm P₀))) (vsQASpinCost N) := by
  set c := Val.list [.nat p, .nat D, vsWVs P₀]
  have g0 := Det.arg' (P := P) (rest := []) (vs := [c, vsFMatsVal Bm]) (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := [c, vsFMatsVal Bm]) (j := 1) rfl
  have wP := wt_vsWVs_le (VsWFit.bnd hP hpN hDN) (by omega)
  have := wt_nat_le p; have := wt_nat_le D; have := wt_nat_le 0; have := wt_nat_le 1
  have := wt_nat_le 2
  have wc := wt_list3_le (.nat p) (.nat D) (vsWVs P₀)
  have ec : c.wt = (Val.list [Val.nat p, .nat D, vsWVs P₀]).wt := rfl
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q45 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q56 : (N + 1) ^ 5 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q67 : (N + 1) ^ 6 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  -- the item
  have hit : ∀ M ∈ Bm, FunDet P it (.list [c, Val.list (M.map natList)]) (vsWVs (vsWImg p D M P₀))
      (10 ^ 7 * (N + 1) ^ 5) := by
    intro M hM
    have e0 := Det.arg' (P := P) (rest := []) (vs := [c, Val.list (M.map natList)]) (j := 0) rfl
    have e1 := Det.arg' (P := P) (rest := []) (vs := [c, Val.list (M.map natList)]) (j := 1) rfl
    have dp := Det.get' e0 (Det.nat 0) (show [Val.nat p, .nat D, vsWVs P₀][0]? = some (.nat p) from rfl)
    have dD := Det.get' e0 (Det.nat 1) (show [Val.nat p, .nat D, vsWVs P₀][1]? = some (.nat D) from rfl)
    have dP := Det.get' e0 (Det.nat 2) (show [Val.nat p, .nat D, vsWVs P₀][2]? = some (vsWVs P₀) from rfl)
    have hM' := hB M hM
    have di := Det.call (Det.mk4 dp dD e1 dP) (vsWImg_spec L.himg hp hpN hDN (A := M) (us := P₀)
      hM'.1 (by rw [hM'.2]; exact hDN) (by rw [hM'.2]; exact hP) hPl)
    refine FunDet.intro L.hit (di.mono ?_)
    have wM : (Val.list (M.map natList)).wt ≤ 11 * (N + 1) ^ 3 + 4 :=
      wt_vsWVs_le (VsWFit.bnd hM'.1 hpN hDN) (by rw [hM'.2]; omega)
    have wI : (vsWVs (vsWImg p D M P₀)).wt ≤ 11 * (N + 1) ^ 3 + 4 :=
      wt_vsWVs_le (VsWFit.bnd (vsWImg_fit hp hM' P₀) hpN hDN) (by simp [vsWImg]; omega)
    have w2 := wt_list2_le c (Val.list (M.map natList))
    have w4 := wt_list4_le (.nat p) (.nat D) (Val.list (M.map natList)) (vsWVs P₀)
    clear_value c
    omega
  have hmap := vsQ_map L.hmp (c := c) Bm (fun M => Val.list (M.map natList))
    (fun M => vsWVs (vsWImg p D M P₀)) vsQ_mats_inj hit
  have dmap := Det.call (Det.mk2 g0 g1) hmap
  set xss := Bm.map fun M => (vsWImg p D M P₀).map natList
  have ex : Val.list (Bm.map fun M => vsWVs (vsWImg p D M P₀)) = Val.list (xss.map Val.list) := by
    simp [xss, vsWVs, List.map_map, Function.comp_def]
  rw [ex] at dmap
  have hsp := vsQSpinL_fit hp hB P₀
  have hspl : (vsQSpinL p D Bm P₀).length ≤ N := by rw [vsQSpinL_length]; exact hBP
  have eo : Val.list xss.flatten = vsWVs (vsQSpinL p D Bm P₀) := by
    simp [xss, vsWVs, vsQSpinL, List.map_flatMap, List.flatten, List.map_map, Function.comp_def,
      List.flatMap]
  have wo : (vsWVs (vsQSpinL p D Bm P₀)).wt ≤ 11 * (N + 1) ^ 3 + 4 :=
    wt_vsWVs_le (VsWFit.bnd hsp hpN hDN) (by omega)
  have wi : (Val.list (xss.map Val.list)).wt ≤ 40 * (N + 1) ^ 4 := by
    have : Val.list (xss.map Val.list) = vsFMatsVal (Bm.map fun M => vsWImg p D M P₀) := by
      simp [xss, vsFMatsVal, List.map_map, Function.comp_def]
    rw [this]
    refine vsQ_wt_mats_le (fun Q hQ => ?_) (by simp; omega)
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hQ
    exact ⟨VsWFit.bnd (vsWImg_fit hp (hB M hM) P₀) hpN hDN, by simp [vsWImg]; omega⟩
  have dcat := Det.call dmap (vsWConcat_spec L.hcat (N := N) xss (by simp [xss]; omega)
    (fun xs hxs => by
      obtain ⟨M, -, rfl⟩ := List.mem_map.1 hxs
      simp [vsWImg]; omega)
    (by rw [eo]; omega) (by omega))
  rw [eo] at dcat
  have dp := Det.get' g0 (Det.nat 0) (show [Val.nat p, .nat D, vsWVs P₀][0]? = some (.nat p) from rfl)
  have dbas := Det.call (Det.mk2 dp dcat) (vsWBas_spec L.hbas hp hpN hDN hsp hspl)
  refine FunDet.intro L.hf (dbas.mono ?_)
  have wB : (vsFMatsVal Bm).wt ≤ 40 * (N + 1) ^ 4 :=
    vsQ_wt_mats_le (fun M hM => ⟨VsWFit.bnd (hB M hM).1 hpN hDN, by rw [(hB M hM).2]; exact hDN⟩) hBl
  have wBas : (vsWVs (vsWBas p (vsQSpinL p D Bm P₀))).wt ≤ 11 * (N + 1) ^ 3 + 4 :=
    wt_vsWVs_le (VsWFit.bnd (vsWBas_fit hp hsp) hpN hDN) (by
      have : (vsWBas p (vsQSpinL p D Bm P₀)).length ≤ (vsQSpinL p D Bm P₀).length := by
        simp only [vsWBas, List.length_map]; exact (vsWRows_fits hp hpN hDN hsp).nrows
      omega)
  have w1 := wt_list2_le c (vsFMatsVal Bm)
  have w2 := wt_list2_le (.nat p) (vsWVs (vsQSpinL p D Bm P₀))
  have hM1 : Bm.length * (10 ^ 7 * (N + 1) ^ 5) ≤ (N + 1) * (10 ^ 7 * (N + 1) ^ 5) :=
    Nat.mul_le_mul_right _ (by omega)
  have eM1 : (N + 1) * (10 ^ 7 * (N + 1) ^ 5) = 10 ^ 7 * (N + 1) ^ 6 := by ring
  have hM2 : mapK * (Bm.length + 1) * ((Val.list [c, Val.list (Bm.map fun M => Val.list (M.map natList))]).wt +
      (Val.list (xss.map Val.list)).wt + 1) ≤ 1000 * (N + 1) * (400 * (N + 1) ^ 4) :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by
      have e : Val.list (Bm.map fun M => Val.list (M.map natList)) = vsFMatsVal Bm := rfl
      rw [e]; omega)
  have eM2 : 1000 * (N + 1) * (400 * (N + 1) ^ 4) = 400000 * (N + 1) ^ 5 := by ring
  have mk : mapK = 1000 := rfl
  have e : Val.list (Bm.map fun M => Val.list (M.map natList)) = vsFMatsVal Bm := rfl
  rw [e] at hM2 ⊢
  unfold vsQASpinCost
  clear_value c xss
  omega

end GI.Impl
