module

public import Workspace.Impl.VsPAb

@[expose] public section

/-!
# Commutators and their discrete logarithms

* `vsPCommE`, `vsPComm_spec`: on `[y, g]`, the permutation `⁅y, g⁆ = y g y⁻¹ g⁻¹`.
* `vsPKeyItemE`, `vsPKeyItem_spec`: on `[[pc, y], g]` with `pc = [ctx, gs, Zp]`, the position of
  the stored local matrix of `⁅y, g⁆` in the list `Zp` (the powers of `ζ`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open scoped commutatorElement

variable {I : VecStabInst}

/-- On `[y, g]`: `⁅y, g⁆`. -/
def vsPCommE (comp inv : ℕ) : Expr :=
  .call comp (mk2 (.call comp (mk2 (arg 0) (arg 1)))
    (.call comp (mk2 (.call inv (arg 0)) (.call inv (arg 1)))))

/-- The cost of a commutator. -/
def vsPCommCost (n : ℕ) : ℕ := 10 ^ 7 * (n + 1) ^ 4


theorem vsPComm_spec {P : Program} {f comp inv n : ℕ} (hf : P.funs[f]? = some (vsPCommE comp inv))
    (hcomp : P.HasAt comp (composeFuns comp)) (hinv : P.HasAt inv (invFuns inv))
    (y g : Perm (Fin n)) :
    FunDet P f (.list [encPerm y, encPerm g]) (encPerm ⁅y, g⁆) (vsPCommCost n) := by
  have a0 := Det.arg' (P := P) (vs := [encPerm y, encPerm g]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [encPerm y, encPerm g]) (rest := []) (j := 1) rfl
  have d1 := Det.call (Det.mk2 a0 a1) (compose_spec hcomp y g)
  have i0 := Det.call a0 (inv_spec hinv y)
  have i1 := Det.call a1 (inv_spec hinv g)
  have d2 := Det.call (Det.mk2 i0 i1) (compose_spec hcomp y⁻¹ g⁻¹)
  have d3 := Det.call (Det.mk2 d1 d2) (compose_spec hcomp (y * g) (y⁻¹ * g⁻¹))
  have e : y * g * (y⁻¹ * g⁻¹) = ⁅y, g⁆ := by rw [commutatorElement_def]; group
  rw [e] at d3
  refine FunDet.intro hf (d3.mono ?_)
  have w1 := wt_encPerm_le y
  have w2 := wt_encPerm_le g
  have w3 := wt_encPerm_le (y * g)
  have w4 := wt_encPerm_le y⁻¹
  have w5 := wt_encPerm_le g⁻¹
  have w6 := wt_encPerm_le (y⁻¹ * g⁻¹)
  have w7 := wt_encPerm_le ⁅y, g⁆
  have w8 := wt_list2_le (encPerm y) (encPerm g)
  have w9 := wt_list2_le (encPerm y⁻¹) (encPerm g⁻¹)
  have w10 := wt_list2_le (encPerm (y * g)) (encPerm (y⁻¹ * g⁻¹))
  have q1 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q2 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q0 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [vsPCommCost, permK, invK]
  omega

theorem vsWVs_inj {us us' : List (List ℕ)} (h : vsWVs us = vsWVs us') : us = us' :=
  List.map_injective_iff.2 (fun _ _ e => vsFMat_natList_inj e) (Val.list.inj h)

/-- The search test "is `v` the stored matrix `M`". -/
noncomputable def vsPQM (M : List (List ℕ)) (v : Val) : Bool := by
  classical exact decide (∃ A, v = vsWVs A ∧ A = M)

open Classical in
theorem vsPQM_enc (M A : List (List ℕ)) : vsPQM M (vsWVs A) = decide (A = M) := by
  unfold vsPQM
  refine Bool.decide_congr ⟨fun ⟨A', e, h⟩ => ?_, fun h => ⟨A, rfl, h⟩⟩
  rw [vsWVs_inj e]; exact h

/-- The position of `Λ(⁅y, g⁆)` in `Zp`. -/
noncomputable def vsPKeyIdx (I : VecStabInst) (ws' cs : List (List ℕ)) (Zp : List (List (List ℕ)))
    (y g : Perm (Fin I.n)) : ℕ :=
  Zp.findIdx (fun A => decide (A = vsPLocL I ws' cs ⁅y, g⁆))

/-- The context of the pairing: `[ctx, gs, Zp]`. -/
def vsPPc (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (hs gs : List (Perm (Fin I.n))) (Zp : List (List (List ℕ))) : Val :=
  .list [vsPCtx I ws' cs rows hs, .list (gs.map encPerm), .list (Zp.map vsWVs)]

/-- On `[[pc, y], g]`: the position of `Λ(⁅y, g⁆)` in `Zp`. -/
def vsPKeyItemE (comm loc fd : ℕ) : Expr :=
  .letE (.call comm (mk2 (.get (arg 0) (.nat 1)) (arg 1)))
  (.letE (.call loc (mk3 (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 0))
      (.get (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.nat 1)) (.var 1)))
    (.call fd (mk2 (.var 2) (.get (.get (arg 0) (.nat 0)) (.nat 2)))))

/-- The cost of an item. -/
def vsPKeyItemCost (Cφ N W : ℕ) : ℕ :=
  vsPLocCost Cφ N + (N + 1) * 10 ^ 8 * (N + 1) ^ 4 + 10 ^ 4 * (N + 1) * (3 * W + 1000 * (N + 1) ^ 4) +
    10 ^ 8 * (N + 1) ^ 4 + 100 * W

set_option maxHeartbeats 4000000 in
theorem vsPKeyItem_spec {P : Program} {f comm comp inv loc fd eqb phi Cφ N W : ℕ}
    (hf : P.funs[f]? = some (vsPKeyItemE comm loc fd))
    (hcomm : P.funs[comm]? = some (vsPCommE comp inv)) (hcomp : P.HasAt comp (composeFuns comp))
    (hinv : P.HasAt inv (invFuns inv))
    (hloc : P.funs[loc]? = some (vsPLocE phi (loc + 1))) (hwl : P.HasAt (loc + 1) (vsWLocFuns (loc + 1)))
    (hfd : P.HasAt fd (findFuns fd eqb)) (heq : P.HasAt eqb (vsPEqFuns eqb))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs gs : List (Perm (Fin I.n))}
    {Zp : List (List (List ℕ))} (H : VsPCtxOK I N W ws' cs rows hs)
    (hZ : ∀ A ∈ Zp, VsWSq I.p cs.length A) (hZl : Zp.length ≤ N)
    (hpc : (vsPPc I ws' cs rows hs gs Zp).wt ≤ W)
    {y g : Perm (Fin I.n)} (hy : y ∈ gens I.gs) (hg : g ∈ gens I.gs) :
    FunDet P f (.list [.list [vsPPc I ws' cs rows hs gs Zp, encPerm y], encPerm g])
      (.nat (vsPKeyIdx I ws' cs Zp y g)) (vsPKeyItemCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set cv := [vsQGam I, vsWFrVal I.p I.d ws' cs, .nat I.p, .list (rows.map VsRow.val),
    natList (vsWZ (cs.length * cs.length)), encGroup hs, .nat I.n] with hcv
  set pcv := [Val.list cv, .list (gs.map encPerm), .list (Zp.map vsWVs)] with hpcv
  set A := Val.list [.list [vsPPc I ws' cs rows hs gs Zp, encPerm y], encPerm g]
  have a0 : Det P [A] (arg 0) (.list [.list pcv, encPerm y]) _ :=
    Det.arg' (P := P) (vs := [.list [vsPPc I ws' cs rows hs gs Zp, encPerm y], encPerm g]) (rest := [])
      (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [.list [vsPPc I ws' cs rows hs gs Zp, encPerm y], encPerm g])
    (rest := []) (j := 1) rfl
  have dy := Det.get' a0 (Det.nat 1) (show [Val.list pcv, encPerm y][1]? = some (encPerm y) from rfl)
  have dc := Det.call (Det.mk2 dy a1) (vsPComm_spec hcomm hcomp hinv y g)
  set E1 := [A, encPerm ⁅y, g⁆]
  have b0 : Det P E1 (arg 0) (.list [.list pcv, encPerm y]) _ :=
    Det.arg' (P := P) (vs := [.list [vsPPc I ws' cs rows hs gs Zp, encPerm y], encPerm g])
      (rest := [encPerm ⁅y, g⁆]) (j := 0) rfl
  have bP := Det.get' b0 (Det.nat 0) (show [Val.list pcv, encPerm y][0]? = some (.list pcv) from rfl)
  have bC := Det.get' bP (Det.nat 0) (show pcv[0]? = some (.list cv) from rfl)
  have bΓ := Det.get' bC (Det.nat 0) (show cv[0]? = some (vsQGam I) from rfl)
  have bF := Det.get' bC (Det.nat 1) (show cv[1]? = some (vsWFrVal I.p I.d ws' cs) from rfl)
  have v1 := Det.var' (P := P) (env := E1) (i := 1) rfl
  have hcm : ⁅y, g⁆ ∈ gens I.gs := by
    rw [commutatorElement_def]; exact mul_mem (mul_mem (mul_mem hy hg) (inv_mem hy)) (inv_mem hg)
  have dl := Det.call (Det.mk3 bΓ bF v1) (vsPLoc_spec hloc hwl hphi H.sz H.gam H.n H.fr hcm)
  set M := vsPLocL I ws' cs ⁅y, g⁆
  set E2 := [A, encPerm ⁅y, g⁆, vsWVs M]
  have e0 : Det P E2 (arg 0) (.list [.list pcv, encPerm y]) _ :=
    Det.arg' (P := P) (vs := [.list [vsPPc I ws' cs rows hs gs Zp, encPerm y], encPerm g])
      (rest := [encPerm ⁅y, g⁆, vsWVs M]) (j := 0) rfl
  have eP := Det.get' e0 (Det.nat 0) (show [Val.list pcv, encPerm y][0]? = some (.list pcv) from rfl)
  have eZ := Det.get' eP (Det.nat 2) (show pcv[2]? = some (.list (Zp.map vsWVs)) from rfl)
  have v2 := Det.var' (P := P) (env := E2) (i := 2) rfl
  have hMsq : VsWSq I.p cs.length M := vsPLocL_sq _
  have hq : ∀ v ∈ Zp.map vsWVs, FunDet P eqb (.list [vsWVs M, v]) (boolVal (vsPQM M v))
      (10 ^ 8 * (N + 1) ^ 4) := by
    intro v hv
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hv
    rw [vsPQM_enc]
    have := vsPEq_spec heq H.sz.pN H.dd hMsq (hZ B hB)
    have e : decide (M = B) = decide (B = M) := Bool.decide_congr ⟨Eq.symm, Eq.symm⟩
    rw [e] at this; exact this
  have dF := Det.call (Det.mk2 v2 eZ) ((find_spec hfd hq).mono fun w c hw => ⟨hw.1, hw.2⟩)
  have eF : (Zp.map vsWVs).findIdx (vsPQM M) = vsPKeyIdx I ws' cs Zp y g := by
    rw [List.findIdx_map]
    unfold vsPKeyIdx
    congr 1
    funext A
    exact vsPQM_enc M A
  rw [eF] at dF
  refine FunDet.intro hf ((Det.letE dc (Det.letE dl dF)).mono ?_)
  have hn := H.n
  have hDN : cs.length ≤ N := le_trans (Nat.le_mul_self _) H.dd
  have wM := wt_vsWVs_le (N := N) (VsWFit.bnd hMsq.1 H.sz.pN hDN) (by rw [hMsq.2]; omega)
  have epc : (vsPPc I ws' cs rows hs gs Zp).wt = (Val.list pcv).wt := rfl
  have wZ : (Val.list (Zp.map vsWVs)).wt ≤ W := by
    have := wt_le_wt_list (show Val.list (Zp.map vsWVs) ∈ pcv by simp [hpcv]); omega
  have wcv : (Val.list cv).wt ≤ W := by
    have := wt_le_wt_list (show Val.list cv ∈ pcv by simp [hpcv]); omega
  have hmc := wt_le_wt_list (show vsQGam I ∈ cv by simp [hcv])
  have hmf := wt_le_wt_list (show vsWFrVal I.p I.d ws' cs ∈ cv by simp [hcv])
  have wy := wt_encPerm_le y
  have wg := wt_encPerm_le g
  have wc := wt_encPerm_le ⁅y, g⁆
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hn4 : (I.n + 1) ^ 4 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have w1 := wt_list2_le (.list pcv) (encPerm y)
  have w2 := wt_list2_le (.list [.list pcv, encPerm y]) (encPerm g)
  have eA : A.wt = (Val.list [.list [.list pcv, encPerm y], encPerm g]).wt := rfl
  have w3 := wt_list2_le (encPerm y) (encPerm g)
  have w4 := wt_list3_le (vsQGam I) (vsWFrVal I.p I.d ws' cs) (encPerm ⁅y, g⁆)
  have w5 := wt_list2_le (vsWVs M) (.list (Zp.map vsWVs))
  have hsum : ((Zp.map vsWVs).map fun _ => 10 ^ 8 * (N + 1) ^ 4).sum ≤
      (N + 1) * (10 ^ 8 * (N + 1) ^ 4) := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map]
    exact Nat.mul_le_mul_right _ (by omega)
  have hloop : loopModK * ((Zp.map vsWVs).length + 1) * ((Val.list [vsWVs M,
      .list (Zp.map vsWVs)]).wt + 2 * (Zp.map vsWVs).length + 3) ≤
      10 ^ 4 * (N + 1) * (3 * W + 1000 * (N + 1) ^ 4) := by
    have h1 : (Zp.map vsWVs).length + 1 ≤ 10 * (N + 1) := by rw [List.length_map]; omega
    have h2 : (Val.list [vsWVs M, .list (Zp.map vsWVs)]).wt + 2 * (Zp.map vsWVs).length + 3 ≤
        3 * W + 1000 * (N + 1) ^ 4 := by
      have : (Zp.map vsWVs).length ≤ (Val.list (Zp.map vsWVs)).wt :=
        (length_lt_wt_list _).le
      have : N + 1 ≤ (N + 1) ^ 4 := Nat.le_self_pow (by omega) _
      omega
    calc loopModK * ((Zp.map vsWVs).length + 1) * _ ≤ 1000 * (10 * (N + 1)) *
          (3 * W + 1000 * (N + 1) ^ 4) := Nat.mul_le_mul (Nat.mul_le_mul_left 1000 h1) h2
      _ = 10 ^ 4 * (N + 1) * (3 * W + 1000 * (N + 1) ^ 4) := by ring
  have hFl : (Zp.map vsWVs).findIdx (vsPQM M) ≤ (Zp.map vsWVs).length := List.findIdx_le_length
  have wF := wt_nat_le (vsPKeyIdx I ws' cs Zp y g)
  have hk : vsPKeyIdx I ws' cs Zp y g ≤ N := by
    rw [← eF]; rw [List.length_map] at hFl; omega
  have hpcW : (Val.list pcv).wt ≤ W := by omega
  unfold vsPKeyItemCost vsPLocCost
  have q5 : N + 1 ≤ (N + 1) ^ 4 := Nat.le_self_pow (by omega) _
  have hWN : W ≤ (N + 1) * (3 * W + 1000 * (N + 1) ^ 4) := by nlinarith
  have hN4 : (N + 1) ^ 4 ≤ (N + 1) * (10 ^ 8 * (N + 1) ^ 4) := by nlinarith
  have em : (N + 1) * 10 ^ 8 * (N + 1) ^ 4 = (N + 1) * (10 ^ 8 * (N + 1) ^ 4) := by ring
  have ej : (Val.list [Val.list [vsPPc I ws' cs rows hs gs Zp, encPerm y], encPerm g]).wt =
      (Val.list [.list [.list pcv, encPerm y], encPerm g]).wt := rfl
  simp only [vsPCommCost]
  omega

/-- The key of `y`: the discrete logarithms of `⁅y, g⁆` for the generators `g`. -/
noncomputable def vsPKey (I : VecStabInst) (ws' cs : List (List ℕ)) (Zp : List (List (List ℕ)))
    (gs : List (Perm (Fin I.n))) (y : Perm (Fin I.n)) : List ℕ :=
  gs.map (vsPKeyIdx I ws' cs Zp y)

/-- On `[pc, y]`: the key of `y`. -/
def vsPKeyE (mp : ℕ) : Expr := .call mp (mk2 (mk2 (arg 0) (arg 1)) (.get (arg 0) (.nat 1)))

/-- The cost of a key. -/
def vsPKeyCost (Cφ N W : ℕ) : ℕ := (N + 1) * vsPKeyItemCost Cφ N W +
  10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 2) + 100 * W + 1000 * (N + 1) ^ 2

set_option maxHeartbeats 4000000 in
theorem vsPKey_spec {P : Program} {f mp it comm comp inv loc fd eqb phi Cφ N W : ℕ}
    (hf : P.funs[f]? = some (vsPKeyE mp)) (hmp : P.HasAt mp (mapFuns mp it))
    (hit : P.funs[it]? = some (vsPKeyItemE comm loc fd))
    (hcomm : P.funs[comm]? = some (vsPCommE comp inv)) (hcomp : P.HasAt comp (composeFuns comp))
    (hinv : P.HasAt inv (invFuns inv))
    (hloc : P.funs[loc]? = some (vsPLocE phi (loc + 1))) (hwl : P.HasAt (loc + 1) (vsWLocFuns (loc + 1)))
    (hfd : P.HasAt fd (findFuns fd eqb)) (heq : P.HasAt eqb (vsPEqFuns eqb))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs gs : List (Perm (Fin I.n))}
    {Zp : List (List (List ℕ))} (H : VsPCtxOK I N W ws' cs rows hs)
    (hZ : ∀ A ∈ Zp, VsWSq I.p cs.length A) (hZl : Zp.length ≤ N)
    (hpc : (vsPPc I ws' cs rows hs gs Zp).wt ≤ W) (hgs : ∀ g ∈ gs, g ∈ gens I.gs)
    (hgl : gs.length ≤ N) {y : Perm (Fin I.n)} (hy : y ∈ gens I.gs) :
    FunDet P f (.list [vsPPc I ws' cs rows hs gs Zp, encPerm y])
      (natList (vsPKey I ws' cs Zp gs y)) (vsPKeyCost Cφ N W) := by
  set pc := vsPPc I ws' cs rows hs gs Zp
  set pcv := [vsPCtx I ws' cs rows hs, .list (gs.map encPerm), .list (Zp.map vsWVs)] with hpcv
  have a0 := Det.arg' (P := P) (vs := [pc, encPerm y]) (rest := []) (j := 0) rfl
  have a0' : Det P [.list [pc, encPerm y]] (arg 0) (.list pcv) _ := a0
  have a1 := Det.arg' (P := P) (vs := [pc, encPerm y]) (rest := []) (j := 1) rfl
  have dg := Det.get' a0' (Det.nat 1) (show pcv[1]? = some (.list (gs.map encPerm)) from rfl)
  have dm := Det.call (Det.mk2 (Det.mk2 a0 a1) dg) (vsQ_map hmp gs encPerm
    (fun a => .nat (vsPKeyIdx I ws' cs Zp y a)) encPerm_injective (c := .list [pc, encPerm y])
    fun a ha => vsPKeyItem_spec hit hcomm hcomp hinv hloc hwl hfd heq hphi H hZ hZl hpc hy (hgs a ha))
  have e : Val.list (gs.map fun a => .nat (vsPKeyIdx I ws' cs Zp y a)) =
      natList (vsPKey I ws' cs Zp gs y) := by
    simp [natList, vsPKey, List.map_map]
  rw [e] at dm
  refine FunDet.intro hf (dm.mono ?_)
  have hn := H.n
  have hidx : ∀ a ∈ gs, vsPKeyIdx I ws' cs Zp y a ≤ N := by
    intro a _
    have : vsPKeyIdx I ws' cs Zp y a ≤ Zp.length := List.findIdx_le_length
    omega
  have wK : (natList (vsPKey I ws' cs Zp gs y)).wt ≤ 5 * (N + 1) ^ 2 := by
    apply wt_natList_le_sq
    · intro x hx
      simp only [vsPKey, List.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact hidx a ha
    · simp [vsPKey]; exact hgl
  have wy := wt_encPerm_le y
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have w1 := wt_list2_le pc (encPerm y)
  have epc : pc.wt = (Val.list pcv).wt := rfl
  have wgs : (Val.list (gs.map encPerm)).wt ≤ W := by
    have := wt_le_wt_list (show Val.list (gs.map encPerm) ∈ pcv by simp [hpcv]); omega
  have w2 := wt_list2_le (.list [pc, encPerm y]) (.list (gs.map encPerm))
  have hloop : mapK * ((gs.length) + 1) * ((Val.list [.list [pc, encPerm y],
      .list (gs.map encPerm)]).wt + (natList (vsPKey I ws' cs Zp gs y)).wt + 1) ≤
      10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 2) := by
    have h1 : gs.length + 1 ≤ N + 1 := by omega
    have h2 : (Val.list [.list [pc, encPerm y], .list (gs.map encPerm)]).wt +
        (natList (vsPKey I ws' cs Zp gs y)).wt + 1 ≤ 10 * (W + 100 * (N + 1) ^ 2) := by
      have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    calc mapK * (gs.length + 1) * _ ≤ 1000 * (N + 1) * (10 * (W + 100 * (N + 1) ^ 2)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 1000 h1) h2
      _ = 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 2) := by ring
  have hsum : gs.length * vsPKeyItemCost Cφ N W ≤ (N + 1) * vsPKeyItemCost Cφ N W :=
    Nat.mul_le_mul_right _ (by omega)
  have wa := wt_list2_le pc (encPerm y)
  have hmk : mapK = 1000 := rfl
  have e2 : (Val.list [Val.list [pc, encPerm y], Val.list (List.map encPerm gs)]).wt =
      (Val.list [Val.list [pc, encPerm y], Val.list (List.map encPerm gs)]).wt := rfl
  have e3 : (Val.list (gs.map fun a => Val.nat (vsPKeyIdx I ws' cs Zp y a))).wt =
      (natList (vsPKey I ws' cs Zp gs y)).wt := by rw [e]
  have hW1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hl : (gs.map encPerm).length = gs.length := List.length_map _
  unfold vsPKeyCost
  omega

/-! ### The powers of `ζ` -/

/-- The stored local matrices of `c0^t`, `t < r`. -/
noncomputable def vsPZp (I : VecStabInst) (ws' cs : List (List ℕ)) (c0 : Perm (Fin I.n)) (r : ℕ) :
    List (List (List ℕ)) :=
  (List.range r).map fun t => vsPLocL I ws' cs (c0 ^ t)

/-- On `[[ctx, c0, 1], t]`: the stored local matrix of `c0^t`. -/
def vsPZItemE (pow loc : ℕ) : Expr :=
  .call loc (mk3 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.get (.get (arg 0) (.nat 0)) (.nat 1))
    (.call pow (mk4 (.nat 0) (.get (arg 0) (.nat 1)) (arg 1) (.get (arg 0) (.nat 2)))))

/-- On `[ctx, c0, r]`: the list `Zp`. -/
def vsPZpE (mp rng : ℕ) : Expr :=
  .letE (.call rng (vsPC 6)) (.call mp (mk2 (mk3 (arg 0) (arg 1) (.var 1)) (.call rng (arg 2))))

/-- The cost of an item. -/
def vsPZItemCost (Cφ N W : ℕ) : ℕ := vsPLocCost Cφ N + 10 ^ 7 * (N + 1) ^ 5 + 100 * W

set_option maxHeartbeats 4000000 in
theorem vsPZItem_spec {P : Program} {f pow loc phi Cφ N W : ℕ}
    (hf : P.funs[f]? = some (vsPZItemE pow loc)) (hpow : P.HasAt pow (vsPPowFuns pow))
    (hloc : P.funs[loc]? = some (vsPLocE phi (loc + 1))) (hwl : P.HasAt (loc + 1) (vsWLocFuns (loc + 1)))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {c0 : Perm (Fin I.n)} (hc0 : c0 ∈ gens I.gs) {t : ℕ}
    (ht : t ≤ N) :
    FunDet P f (.list [.list [vsPCtx I ws' cs rows hs, encPerm c0, encPerm (1 : Perm (Fin I.n))], .nat t])
      (vsWVs (vsPLocL I ws' cs (c0 ^ t))) (vsPZItemCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set cv := [vsQGam I, vsWFrVal I.p I.d ws' cs, .nat I.p, .list (rows.map VsRow.val),
    natList (vsWZ (cs.length * cs.length)), encGroup hs, .nat I.n] with hcv
  set A := Val.list [.list [C, encPerm c0, encPerm (1 : Perm (Fin I.n))], .nat t]
  have a0 : Det P [A] (arg 0) (.list [.list cv, encPerm c0, encPerm (1 : Perm (Fin I.n))]) _ :=
    Det.arg' (P := P) (vs := [.list [C, encPerm c0, encPerm (1 : Perm (Fin I.n))], .nat t]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [.list [C, encPerm c0, encPerm (1 : Perm (Fin I.n))], .nat t]) (rest := [])
    (j := 1) rfl
  have dC := Det.get' a0 (Det.nat 0)
    (show [Val.list cv, encPerm c0, encPerm (1 : Perm (Fin I.n))][0]? = some (.list cv) from rfl)
  have dΓ := Det.get' dC (Det.nat 0) (show cv[0]? = some (vsQGam I) from rfl)
  have dF := Det.get' dC (Det.nat 1) (show cv[1]? = some (vsWFrVal I.p I.d ws' cs) from rfl)
  have dc := Det.get' a0 (Det.nat 1)
    (show [Val.list cv, encPerm c0, encPerm (1 : Perm (Fin I.n))][1]? = some (encPerm c0) from rfl)
  have d1 := Det.get' a0 (Det.nat 2)
    (show [Val.list cv, encPerm c0, encPerm (1 : Perm (Fin I.n))][2]? = some (encPerm 1) from rfl)
  have dp := Det.call (Det.mk4 (Det.nat 0) dc a1 d1) (vsPPow_spec hpow c0 1 t)
  rw [mul_one] at dp
  have dl := Det.call (Det.mk3 dΓ dF dp) (vsPLoc_spec hloc hwl hphi H.sz H.gam H.n H.fr
    (pow_mem hc0 t))
  refine FunDet.intro hf (dl.mono ?_)
  have hn := H.n
  have wC : C.wt ≤ W := H.cw
  have ecv : (Val.list cv).wt = C.wt := rfl
  have hmc := wt_le_wt_list (show vsQGam I ∈ cv by simp [hcv])
  have hmf := wt_le_wt_list (show vsWFrVal I.p I.d ws' cs ∈ cv by simp [hcv])
  have wc := wt_encPerm_le c0
  have w1 := wt_encPerm_le (1 : Perm (Fin I.n))
  have wct := wt_encPerm_le (c0 ^ t)
  have wt' := wt_nat_le t
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hn3 : (I.n + 1) ^ 3 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hpc := vsPPowCost_le (n := I.n) (e := t) (k := N) (by have := vsP_bits_le t; omega)
  have hpc' : 10 ^ 6 * (N + 1) ^ 2 * (I.n + 1) ^ 3 ≤ 10 ^ 6 * (N + 1) ^ 5 := by
    calc 10 ^ 6 * (N + 1) ^ 2 * (I.n + 1) ^ 3 ≤ 10 ^ 6 * (N + 1) ^ 2 * (N + 1) ^ 3 :=
          Nat.mul_le_mul_left _ hn3
      _ = 10 ^ 6 * (N + 1) ^ 5 := by ring
  have w3 := wt_list3_le (.list cv) (encPerm c0) (encPerm (1 : Perm (Fin I.n)))
  have w2 := wt_list2_le (.list [.list cv, encPerm c0, encPerm (1 : Perm (Fin I.n))]) (.nat t)
  have eA : A.wt = (Val.list [.list [C, encPerm c0, encPerm (1 : Perm (Fin I.n))], .nat t]).wt := rfl
  have eA2 : (Val.list [.list [C, encPerm c0, encPerm (1 : Perm (Fin I.n))], .nat t]).wt =
      (Val.list [.list [.list cv, encPerm c0, encPerm (1 : Perm (Fin I.n))], .nat t]).wt := rfl
  have w4 := wt_list4_le (.nat 0) (encPerm c0) (.nat t) (encPerm (1 : Perm (Fin I.n)))
  have w5 := wt_list3_le (vsQGam I) (vsWFrVal I.p I.d ws' cs) (encPerm (c0 ^ t))
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have w0 : (Val.nat 0).wt = 2 := rfl
  have hDN : cs.length ≤ N := le_trans (Nat.le_mul_self _) H.dd
  have hsq := vsPLocL_sq (I := I) (ws' := ws') (cs := cs) (c0 ^ t)
  have wz := wt_vsWVs_le (N := N) (VsWFit.bnd hsq.1 H.sz.pN hDN) (by rw [hsq.2]; omega)
  have q4 : (N + 1) ^ 3 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold vsPZItemCost
  omega

/-- The cost of `Zp`. -/
def vsPZpCost (Cφ N W : ℕ) : ℕ :=
  (N + 1) * vsPZItemCost Cφ N W + 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 4) + 10 ^ 5 * (N + 1) ^ 3 +
    100 * W + 1000 * (N + 1) ^ 4

set_option maxHeartbeats 4000000 in
theorem vsPZp_spec {P : Program} {f mp it rng pow loc phi Cφ N W : ℕ}
    (hf : P.funs[f]? = some (vsPZpE mp rng)) (hmp : P.HasAt mp (mapFuns mp it))
    (hit : P.funs[it]? = some (vsPZItemE pow loc)) (hrng : P.HasAt rng (rangeFuns rng))
    (hpow : P.HasAt pow (vsPPowFuns pow))
    (hloc : P.funs[loc]? = some (vsPLocE phi (loc + 1))) (hwl : P.HasAt (loc + 1) (vsWLocFuns (loc + 1)))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {c0 : Perm (Fin I.n)} (hc0 : c0 ∈ gens I.gs) {r : ℕ}
    (hr : r ≤ N) :
    FunDet P f (.list [vsPCtx I ws' cs rows hs, encPerm c0, .nat r])
      (.list ((vsPZp I ws' cs c0 r).map vsWVs)) (vsPZpCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set cv := [vsQGam I, vsWFrVal I.p I.d ws' cs, .nat I.p, .list (rows.map VsRow.val),
    natList (vsWZ (cs.length * cs.length)), encGroup hs, .nat I.n] with hcv
  set A := Val.list [C, encPerm c0, .nat r]
  have a0 := Det.arg' (P := P) (vs := [C, encPerm c0, .nat r]) (rest := []) (j := 0) rfl
  have a0' : Det P [A] (arg 0) (.list cv) _ := a0
  have c6 := Det.get' a0' (Det.nat 6) (show cv[6]? = some (.nat I.n) from rfl)
  have d1 := Det.call c6 (GI.Lang.range_det hrng I.n)
  set E := [A, encPerm (1 : Perm (Fin I.n))]
  have b0 := Det.arg' (P := P) (vs := [C, encPerm c0, .nat r]) (rest := [encPerm (1 : Perm (Fin I.n))])
    (j := 0) rfl
  have b1 := Det.arg' (P := P) (vs := [C, encPerm c0, .nat r]) (rest := [encPerm (1 : Perm (Fin I.n))])
    (j := 1) rfl
  have b2 := Det.arg' (P := P) (vs := [C, encPerm c0, .nat r]) (rest := [encPerm (1 : Perm (Fin I.n))])
    (j := 2) rfl
  have v1 := Det.var' (P := P) (env := E) (i := 1) rfl
  have dR := Det.call b2 ((vsP_range_det hrng r).mono fun w c hw => ⟨hw.1, hw.2⟩)
  have eR : natList (List.range r) = .list ((List.range r).map Val.nat) := rfl
  rw [eR] at dR
  have dm := Det.call (Det.mk2 (Det.mk3 b0 b1 v1) dR) (vsQ_map hmp (List.range r) Val.nat
    (fun t => vsWVs (vsPLocL I ws' cs (c0 ^ t))) (fun _ _ h => Val.nat.inj h)
    (c := .list [C, encPerm c0, encPerm (1 : Perm (Fin I.n))])
    fun t ht => vsPZItem_spec hit hpow hloc hwl hphi H hc0 (by simp at ht; omega))
  have e : Val.list ((List.range r).map fun t => vsWVs (vsPLocL I ws' cs (c0 ^ t))) =
      .list ((vsPZp I ws' cs c0 r).map vsWVs) := by simp [vsPZp, List.map_map]
  rw [e] at dm
  refine FunDet.intro hf ((Det.letE d1 dm).mono ?_)
  have hn := H.n
  have wC : C.wt ≤ W := H.cw
  have ecv : (Val.list cv).wt = C.wt := rfl
  have hDN : cs.length ≤ N := le_trans (Nat.le_mul_self _) H.dd
  have wZ : (Val.list ((vsPZp I ws' cs c0 r).map vsWVs)).wt ≤ 40 * (N + 1) ^ 4 := by
    have h1 := vs_wt_list_le_of ((vsPZp I ws' cs c0 r).map vsWVs) (c := 11 * (N + 1) ^ 3 + 4) (by
      intro v hv
      simp only [vsPZp, List.map_map, List.mem_map, List.mem_range, Function.comp] at hv
      obtain ⟨t, -, rfl⟩ := hv
      have hsq := vsPLocL_sq (I := I) (ws' := ws') (cs := cs) (c0 ^ t)
      exact wt_vsWVs_le (VsWFit.bnd hsq.1 H.sz.pN hDN) (by rw [hsq.2]; omega))
    unfold vsPZp at h1 ⊢
    simp only [List.length_map, List.length_range] at h1
    have : r * (2 * (11 * (N + 1) ^ 3 + 4) + 1) ≤ (N + 1) * (31 * (N + 1) ^ 3) := by
      have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
      exact Nat.mul_le_mul (by omega) (by omega)
    have e : (N + 1) * (31 * (N + 1) ^ 3) = 31 * (N + 1) ^ 4 := by ring
    have : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have wR : (Val.list ((List.range r).map Val.nat)).wt ≤ 5 * (N + 1) ^ 2 := by
    have := wt_natList_le_sq (xs := List.range r) (B := N) (fun y hy => by simp at hy; omega)
      (by simp; omega)
    exact this
  have e2 : Val.list ((List.range r).map fun t => vsWVs (vsPLocL I ws' cs (c0 ^ t))) =
      .list ((vsPZp I ws' cs c0 r).map vsWVs) := e
  have wc := wt_encPerm_le c0
  have w1 := wt_encPerm_le (1 : Perm (Fin I.n))
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hn3 : (I.n + 1) ^ 3 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have w3 := wt_list3_le C (encPerm c0) (.nat r)
  have w3' := wt_list3_le C (encPerm c0) (encPerm (1 : Perm (Fin I.n)))
  have wr := wt_nat_le r
  have wn := wt_nat_le I.n
  have w2 := wt_list2_le (.list [C, encPerm c0, encPerm (1 : Perm (Fin I.n))])
    (.list ((List.range r).map Val.nat))
  have hsum : (List.range r).length * vsPZItemCost Cφ N W ≤ (N + 1) * vsPZItemCost Cφ N W := by
    rw [List.length_range]; exact Nat.mul_le_mul_right _ (by omega)
  have hrng := vsP_rng_le (m := r) (N := N) hr
  have hloop : mapK * ((List.range r).length + 1) * ((Val.list [.list [C, encPerm c0,
      encPerm (1 : Perm (Fin I.n))], .list ((List.range r).map Val.nat)]).wt +
      (Val.list ((vsPZp I ws' cs c0 r).map vsWVs)).wt + 1) ≤
      10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 4) := by
    have h1 : (List.range r).length + 1 ≤ N + 1 := by rw [List.length_range]; omega
    have q1 : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (Val.list [.list [C, encPerm c0, encPerm (1 : Perm (Fin I.n))],
        .list ((List.range r).map Val.nat)]).wt +
        (Val.list ((vsPZp I ws' cs c0 r).map vsWVs)).wt + 1 ≤ 10 * (W + 100 * (N + 1) ^ 4) := by
      have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    calc mapK * ((List.range r).length + 1) * _ ≤ 1000 * (N + 1) * (10 * (W + 100 * (N + 1) ^ 4)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 1000 h1) h2
      _ = 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 4) := by ring
  have eA : A.wt = (Val.list [C, encPerm c0, .nat r]).wt := rfl
  have q1 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q2 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hWN : W ≤ 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 4) := by nlinarith
  have hN4 : (N + 1) ^ 4 ≤ 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 4) := by
    have : (N + 1) ^ 4 ≤ (N + 1) * (N + 1) ^ 4 := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  have hr8 : 8000 * (I.n + 1) ^ 3 ≤ 8000 * (N + 1) ^ 3 := by omega
  have hbig : 10 ^ 4 * W + 10 ^ 6 * (N + 1) ^ 4 ≤ 10 ^ 4 * (N + 1) * (W + 100 * (N + 1) ^ 4) := by
    have h1 : W + 100 * (N + 1) ^ 4 ≤ (N + 1) * (W + 100 * (N + 1) ^ 4) :=
      Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q14 : N + 1 ≤ (N + 1) ^ 4 := Nat.le_self_pow (by omega) _
  have q24 : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold vsPZpCost
  omega

end GI.Impl
