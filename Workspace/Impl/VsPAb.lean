import Workspace.Impl.VsPGrow

/-!
# Do the local matrices of a list commute?

* `vsPNcE`: on `[[ctx, g], h]`, `1` if `Λ(gh) ≠ Λ(hg)` (as stored local matrices).
* `vsPAbE`: on `[ctx, ⟨ns⟩]`, `1` if all pairs of `1 :: ns` give equal `Λ(gh)`, `Λ(hg)`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- On `[[ctx, g], h]`. -/
def vsPNcE (comp loc eq : ℕ) : Expr :=
  .letE (.call comp (mk2 (.get (arg 0) (.nat 1)) (arg 1)))
  (.letE (.call comp (mk2 (arg 1) (.get (arg 0) (.nat 1))))
    (.ite (.call eq (mk2
      (.call loc (mk3 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.get (.get (arg 0) (.nat 0)) (.nat 1))
        (.var 1)))
      (.call loc (mk3 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (.get (.get (arg 0) (.nat 0)) (.nat 1))
        (.var 2))))) (.nat 0) (.nat 1)))

/-- The pair test, on values. -/
noncomputable def vsPQC2 (I : VecStabInst) (ws' cs : List (List ℕ)) (g : Perm (Fin I.n))
    (v : Val) : Bool := by
  classical exact decide (∃ h : Perm (Fin I.n), v = encPerm h ∧
    vsPLocL I ws' cs (g * h) ≠ vsPLocL I ws' cs (h * g))

open Classical in
theorem vsPQC2_enc (ws' cs : List (List ℕ)) (g h : Perm (Fin I.n)) :
    vsPQC2 I ws' cs g (encPerm h) = decide (vsPLocL I ws' cs (g * h) ≠ vsPLocL I ws' cs (h * g)) := by
  unfold vsPQC2
  refine Bool.decide_congr ⟨fun ⟨h', e, hne⟩ => ?_, fun hne => ⟨h, rfl, hne⟩⟩
  rw [encPerm_injective e]; exact hne

/-- The cost of the pair test. -/
def vsPNcCost (Cφ N W : ℕ) : ℕ := 2 * vsPLocCost Cφ N + 10 ^ 9 * (N + 1) ^ 4 + 100 * W

set_option maxHeartbeats 4000000 in
theorem vsPNc_spec {P : Program} {f comp loc eq phi Cφ N W : ℕ}
    (hf : P.funs[f]? = some (vsPNcE comp loc eq)) (hcomp : P.HasAt comp (composeFuns comp))
    (hloc : P.funs[loc]? = some (vsPLocE phi (loc + 1))) (hwl : P.HasAt (loc + 1) (vsWLocFuns (loc + 1)))
    (heq : P.HasAt eq (vsPEqFuns eq))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {g h : Perm (Fin I.n)} (hg : g ∈ gens I.gs)
    (hh : h ∈ gens I.gs) :
    FunDet P f (.list [.list [vsPCtx I ws' cs rows hs, encPerm g], encPerm h])
      (boolVal (vsPQC2 I ws' cs g (encPerm h))) (vsPNcCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set cv := [vsQGam I, vsWFrVal I.p I.d ws' cs, .nat I.p, .list (rows.map VsRow.val),
    natList (vsWZ (cs.length * cs.length)), encGroup hs, .nat I.n] with hcv
  set A := Val.list [.list [C, encPerm g], encPerm h]
  have a0 : Det P [A] (arg 0) (.list [.list cv, encPerm g]) _ :=
    Det.arg' (P := P) (vs := [.list [C, encPerm g], encPerm h]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [.list [C, encPerm g], encPerm h]) (rest := []) (j := 1) rfl
  have dg := Det.get' a0 (Det.nat 1) (show [Val.list cv, encPerm g][1]? = some (encPerm g) from rfl)
  have dgh := Det.call (Det.mk2 dg a1) (compose_spec hcomp g h)
  set E1 := [A, encPerm (g * h)]
  have b0 : Det P E1 (arg 0) (.list [.list cv, encPerm g]) _ :=
    Det.arg' (P := P) (vs := [.list [C, encPerm g], encPerm h]) (rest := [encPerm (g * h)]) (j := 0) rfl
  have b1 := Det.arg' (P := P) (vs := [.list [C, encPerm g], encPerm h]) (rest := [encPerm (g * h)])
    (j := 1) rfl
  have bg := Det.get' b0 (Det.nat 1) (show [Val.list cv, encPerm g][1]? = some (encPerm g) from rfl)
  have dhg := Det.call (Det.mk2 b1 bg) (compose_spec hcomp h g)
  set E2 := [A, encPerm (g * h), encPerm (h * g)]
  have e0 : Det P E2 (arg 0) (.list [.list cv, encPerm g]) _ :=
    Det.arg' (P := P) (vs := [.list [C, encPerm g], encPerm h])
      (rest := [encPerm (g * h), encPerm (h * g)]) (j := 0) rfl
  have eC := Det.get' e0 (Det.nat 0) (show [Val.list cv, encPerm g][0]? = some (.list cv) from rfl)
  have eΓ := Det.get' eC (Det.nat 0) (show cv[0]? = some (vsQGam I) from rfl)
  have eF := Det.get' eC (Det.nat 1) (show cv[1]? = some (vsWFrVal I.p I.d ws' cs) from rfl)
  have v1 := Det.var' (P := P) (env := E2) (i := 1) rfl
  have v2 := Det.var' (P := P) (env := E2) (i := 2) rfl
  have l1 := Det.call (Det.mk3 eΓ eF v1) (vsPLoc_spec hloc hwl hphi H.sz H.gam H.n H.fr
    (mul_mem hg hh))
  have l2 := Det.call (Det.mk3 eΓ eF v2) (vsPLoc_spec hloc hwl hphi H.sz H.gam H.n H.fr
    (mul_mem hh hg))
  have hDD := H.dd
  have dE := Det.call (Det.mk2 l1 l2) (vsPEq_spec heq H.sz.pN hDD (vsPLocL_sq (g * h))
    (vsPLocL_sq (h * g)))
  rw [vsPQC2_enc]
  apply FunDet.intro hf
  -- weights
  have wC : C.wt ≤ W := H.cw
  have ecv : (Val.list cv).wt = C.wt := rfl
  have hn := H.n
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hn3 : (I.n + 1) ^ 3 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have wg := wt_encPerm_le g
  have wh := wt_encPerm_le h
  have wgh := wt_encPerm_le (g * h)
  have whg := wt_encPerm_le (h * g)
  have w1 := wt_list2_le (.list cv) (encPerm g)
  have w2 := wt_list2_le (.list [.list cv, encPerm g]) (encPerm h)
  have eA : A.wt = (Val.list [.list [C, encPerm g], encPerm h]).wt := rfl
  have eA2 : (Val.list [.list [C, encPerm g], encPerm h]).wt =
      (Val.list [.list [.list cv, encPerm g], encPerm h]).wt := rfl
  have w3 := wt_list2_le (encPerm g) (encPerm h)
  have w4 := wt_list2_le (encPerm h) (encPerm g)
  have hmc := wt_le_wt_list (show vsQGam I ∈ cv by simp [hcv])
  have hmf := wt_le_wt_list (show vsWFrVal I.p I.d ws' cs ∈ cv by simp [hcv])
  have w5 := wt_list3_le (vsQGam I) (vsWFrVal I.p I.d ws' cs) (encPerm (g * h))
  have w6 := wt_list3_le (vsQGam I) (vsWFrVal I.p I.d ws' cs) (encPerm (h * g))
  have hDN : cs.length ≤ N := le_trans (Nat.le_mul_self _) hDD
  have sq1 := vsPLocL_sq (I := I) (ws' := ws') (cs := cs) (g * h)
  have sq2 := vsPLocL_sq (I := I) (ws' := ws') (cs := cs) (h * g)
  have wl1 := wt_vsWVs_le (N := N) (VsWFit.bnd sq1.1 H.sz.pN hDN) (by rw [sq1.2]; omega)
  have wl2 := wt_vsWVs_le (N := N) (VsWFit.bnd sq2.1 H.sz.pN hDN) (by rw [sq2.2]; omega)
  have w7 := wt_list2_le (vsWVs (vsPLocL I ws' cs (g * h))) (vsWVs (vsPLocL I ws' cs (h * g)))
  have hpk : permK * (I.n + 1) ^ 3 ≤ 30000 * (N + 1) ^ 3 := by
    rw [show permK = 30000 from rfl]; omega
  have wt0 := wt_nat_le 0
  have wt1 := wt_nat_le 1
  have wb := wt_boolVal_le (decide (vsPLocL I ws' cs (g * h) = vsPLocL I ws' cs (h * g)))
  have hq5 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  by_cases he : vsPLocL I ws' cs (g * h) = vsPLocL I ws' cs (h * g)
  · have dE1 := dE
    rw [show boolVal (decide (vsPLocL I ws' cs (g * h) = vsPLocL I ws' cs (h * g))) = .nat 1 by
      simp [he]] at dE1
    rw [show boolVal (decide (vsPLocL I ws' cs (g * h) ≠ vsPLocL I ws' cs (h * g))) = .nat 0 by
      simp [he]]
    refine (Det.letE dgh (Det.letE dhg (Det.ite_pos dE1 one_ne_zero (Det.nat 0)))).mono ?_
    unfold vsPNcCost vsPLocCost
    omega
  · have dE0 := dE
    rw [show boolVal (decide (vsPLocL I ws' cs (g * h) = vsPLocL I ws' cs (h * g))) = .nat 0 by
      simp [he]] at dE0
    rw [show boolVal (decide (vsPLocL I ws' cs (g * h) ≠ vsPLocL I ws' cs (h * g))) = .nat 1 by
      simp [he]]
    refine (Det.letE dgh (Det.letE dhg (Det.ite_zero dE0 (Det.nat 1)))).mono ?_
    unfold vsPNcCost vsPLocCost
    omega

/-! ### All pairs -/

/-- On `[[ctx, L], g]`: `1` if some `h ∈ L` has `Λ(gh) ≠ Λ(hg)`. -/
def vsPNoE (fi : ℕ) : Expr :=
  .arith .lt (.call fi (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1))))
    (.length (.get (arg 0) (.nat 1)))

/-- On `[ctx, ⟨ns⟩]`: `1` if all pairs of `1 :: ns` commute (as local matrices). -/
def vsPAbE (fo : ℕ) : Expr :=
  .letE (.get (arg 1) (.nat 1))
    (.arith .eq (.call fo (mk2 (mk2 (arg 0) (.var 1)) (.var 1))) (.length (.var 1)))

/-- The outer test, on values. -/
noncomputable def vsPQO (I : VecStabInst) (ws' cs : List (List ℕ)) (L : List (Perm (Fin I.n)))
    (v : Val) : Bool := by
  classical exact decide (∃ g : Perm (Fin I.n), v = encPerm g ∧
    ∃ h ∈ L, vsPLocL I ws' cs (g * h) ≠ vsPLocL I ws' cs (h * g))

open Classical in
theorem vsPQO_enc (ws' cs : List (List ℕ)) (L : List (Perm (Fin I.n))) (g : Perm (Fin I.n)) :
    vsPQO I ws' cs L (encPerm g) =
      decide (∃ h ∈ L, vsPLocL I ws' cs (g * h) ≠ vsPLocL I ws' cs (h * g)) := by
  unfold vsPQO
  refine Bool.decide_congr ⟨fun ⟨g', e, hne⟩ => ?_, fun hne => ⟨g, rfl, hne⟩⟩
  rw [encPerm_injective e]; exact hne

/-- The cost of the inner test. -/
def vsPNoCost (Cφ N W : ℕ) : ℕ :=
  (N + 1) ^ 2 * vsPNcCost Cφ N W + 10 ^ 4 * (N + 1) ^ 2 * (W + 400 * (N + 1) ^ 6) + 100 * W +
    10 ^ 5 * (N + 1) ^ 6

set_option maxHeartbeats 4000000 in
theorem vsPNo_spec {P : Program} {f fi nc comp loc eq phi Cφ N W : ℕ}
    (hf : P.funs[f]? = some (vsPNoE fi)) (hfi : P.HasAt fi (findFuns fi nc))
    (hnc : P.funs[nc]? = some (vsPNcE comp loc eq)) (hcomp : P.HasAt comp (composeFuns comp))
    (hloc : P.funs[loc]? = some (vsPLocE phi (loc + 1))) (hwl : P.HasAt (loc + 1) (vsWLocFuns (loc + 1)))
    (heq : P.HasAt eq (vsPEqFuns eq))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {L : List (Perm (Fin I.n))} (hL : ∀ h ∈ L, h ∈ gens I.gs)
    (hLl : L.length ≤ (N + 1) ^ 2) (hLw : (Val.list (L.map encPerm)).wt ≤ 400 * (N + 1) ^ 6)
    {g : Perm (Fin I.n)} (hg : g ∈ gens I.gs) :
    FunDet P f (.list [.list [vsPCtx I ws' cs rows hs, .list (L.map encPerm)], encPerm g])
      (boolVal (vsPQO I ws' cs L (encPerm g))) (vsPNoCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set xs := L.map encPerm
  set A := Val.list [.list [C, .list xs], encPerm g]
  have a0 : Det P [A] (arg 0) (.list [C, .list xs]) _ :=
    Det.arg' (P := P) (vs := [.list [C, .list xs], encPerm g]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [.list [C, .list xs], encPerm g]) (rest := []) (j := 1) rfl
  have dC := Det.get' a0 (Det.nat 0) (show [C, Val.list xs][0]? = some C from rfl)
  have dL := Det.get' a0 (Det.nat 1) (show [C, Val.list xs][1]? = some (.list xs) from rfl)
  have hq : ∀ v ∈ xs, FunDet P nc (.list [.list [C, encPerm g], v])
      (boolVal (vsPQC2 I ws' cs g v)) (vsPNcCost Cφ N W) := by
    intro v hv
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hv
    exact vsPNc_spec hnc hcomp hloc hwl heq hphi H hg (hL h hh)
  have dF := Det.call (Det.mk2 (Det.mk2 dC a1) dL) ((find_spec hfi hq).mono fun w c hw => ⟨hw.1, hw.2⟩)
  have dT := Det.arith' (op := .lt) dF (Det.length dL) rfl
  have ev : Val.nat (GI.Machine.BinOp.eval .lt (xs.findIdx (vsPQC2 I ws' cs g)) xs.length) =
      boolVal (vsPQO I ws' cs L (encPerm g)) := by
    rw [vsPQO_enc]
    simp only [GI.Machine.BinOp.eval, boolVal]
    have e : xs.findIdx (vsPQC2 I ws' cs g) < xs.length ↔
        ∃ h ∈ L, vsPLocL I ws' cs (g * h) ≠ vsPLocL I ws' cs (h * g) := by
      rw [List.findIdx_lt_length]
      simp only [xs, List.mem_map, exists_exists_and_eq_and, vsPQC2_enc, decide_eq_true_eq]
    by_cases hc : ∃ h ∈ L, vsPLocL I ws' cs (g * h) ≠ vsPLocL I ws' cs (h * g)
    · rw [if_pos (e.2 hc)]
      have : (decide (∃ h ∈ L, vsPLocL I ws' cs (g * h) ≠ vsPLocL I ws' cs (h * g))).toNat = 1 := by
        rw [Bool.toNat_eq_one]; simpa only [decide_eq_true_eq] using hc
      rw [this]
    · rw [if_neg (fun h => hc (e.1 h))]
      have : (decide (∃ h ∈ L, vsPLocL I ws' cs (g * h) ≠ vsPLocL I ws' cs (h * g))).toNat = 0 := by
        rw [Bool.toNat_eq_zero]; simpa only [decide_eq_false_iff_not] using hc
      rw [this]
  rw [ev] at dT
  refine FunDet.intro hf (dT.mono ?_)
  have hn := H.n
  have wC : C.wt ≤ W := H.cw
  have hxl : xs.length ≤ (N + 1) ^ 2 := by simp only [xs, List.length_map]; exact hLl
  have wxs : (Val.list xs).wt ≤ 400 * (N + 1) ^ 6 := hLw
  have hn6 : (I.n + 1) ^ 6 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hN6 : (N + 1) ^ 2 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hsum : (xs.map fun _ => vsPNcCost Cφ N W).sum ≤ (N + 1) ^ 2 * vsPNcCost Cφ N W := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hxl
  have wg := wt_encPerm_le g
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have w1 := wt_list2_le C (encPerm g)
  have w2 := wt_list2_le (.list [C, encPerm g]) (.list xs)
  have hloop : loopModK * (xs.length + 1) * ((Val.list [.list [C, encPerm g], .list xs]).wt +
      2 * xs.length + 3) ≤ 10 ^ 4 * (N + 1) ^ 2 * (W + 400 * (N + 1) ^ 6) := by
    have h1 : xs.length + 1 ≤ 2 * (N + 1) ^ 2 := by omega
    have h2 : (Val.list [.list [C, encPerm g], .list xs]).wt + 2 * xs.length + 3 ≤
        5 * (W + 400 * (N + 1) ^ 6) := by omega
    calc loopModK * (xs.length + 1) * _ ≤ 1000 * (2 * (N + 1) ^ 2) * (5 * (W + 400 * (N + 1) ^ 6)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 1000 h1) h2
      _ = 10 ^ 4 * (N + 1) ^ 2 * (W + 400 * (N + 1) ^ 6) := by ring
  have wF := wt_nat_le (xs.findIdx (vsPQC2 I ws' cs g))
  have hFl : xs.findIdx (vsPQC2 I ws' cs g) ≤ xs.length := List.findIdx_le_length
  have wb := wt_boolVal_le (vsPQO I ws' cs L (encPerm g))
  have w3 := wt_list2_le (.list [C, .list xs]) (encPerm g)
  have w4 := wt_list2_le C (.list xs)
  have eA : A.wt = (Val.list [.list [C, .list xs], encPerm g]).wt := rfl
  have hwl : xs.length ≤ (Val.list xs).wt := (length_lt_wt_list xs).le
  have hy : GI.Machine.BinOp.lt.eval (xs.findIdx (vsPQC2 I ws' cs g)) xs.length ≤ 1 := by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega
  unfold vsPNoCost
  omega

/-- The cost of the full test. -/
def vsPAbCost (Cφ N W : ℕ) : ℕ :=
  (N + 1) ^ 2 * vsPNoCost Cφ N W + 10 ^ 4 * (N + 1) ^ 2 * (W + 1000 * (N + 1) ^ 6) + 100 * W +
    10 ^ 5 * (N + 1) ^ 6

set_option maxHeartbeats 4000000 in
/-- **Do the local matrices of `1 :: ns` commute pairwise?** -/
theorem vsPAb_spec {P : Program} {f fo no fi nc comp loc eq phi Cφ N W : ℕ}
    (hf : P.funs[f]? = some (vsPAbE fo)) (hfo : P.HasAt fo (findFuns fo no))
    (hno : P.funs[no]? = some (vsPNoE fi)) (hfi : P.HasAt fi (findFuns fi nc))
    (hnc : P.funs[nc]? = some (vsPNcE comp loc eq)) (hcomp : P.HasAt comp (composeFuns comp))
    (hloc : P.funs[loc]? = some (vsPLocE phi (loc + 1))) (hwl : P.HasAt (loc + 1) (vsWLocFuns (loc + 1)))
    (heq : P.HasAt eq (vsPEqFuns eq))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {ns : List (Perm (Fin I.n))}
    (hns : ∀ h ∈ ns, h ∈ gens I.gs) (hnl : ns.length ≤ I.n ^ 2) :
    FunDet P f (.list [vsPCtx I ws' cs rows hs, encGroup ns])
      (boolVal (decide (∀ g ∈ 1 :: ns, ∀ h ∈ 1 :: ns,
        vsPLocL I ws' cs (g * h) = vsPLocL I ws' cs (h * g)))) (vsPAbCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set L := 1 :: ns
  set xs := L.map encPerm
  have eG : encGroup ns = .list [.nat I.n, .list xs] := rfl
  set A := Val.list [C, encGroup ns]
  have hn := H.n
  have hL : ∀ h ∈ L, h ∈ gens I.gs := by
    intro h hh; rcases List.mem_cons.mp hh with rfl | hh
    · exact one_mem _
    · exact hns h hh
  have wG := wt_encGroup_le_sq hnl
  have hn6 : (I.n + 1) ^ 6 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have wxs : (Val.list xs).wt ≤ (encGroup ns).wt := by
    rw [eG]; exact (wt_le_wt_list (show Val.list xs ∈ [Val.nat I.n, Val.list xs] by simp)).le
  have hLl : L.length ≤ (N + 1) ^ 2 := by
    simp only [L, List.length_cons]
    have : I.n ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hn 2
    nlinarith
  have a0 := Det.arg' (P := P) (vs := [C, encGroup ns]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [C, encGroup ns]) (rest := []) (j := 1) rfl
  rw [eG] at a1
  have dl := Det.get' a1 (Det.nat 1) (show [Val.nat I.n, .list xs][1]? = some (.list xs) from rfl)
  set E := [A, Val.list xs]
  have b0 := Det.arg' (P := P) (vs := [C, encGroup ns]) (rest := [Val.list xs]) (j := 0) rfl
  have v1 := Det.var' (P := P) (env := E) (i := 1) rfl
  have hq : ∀ v ∈ xs, FunDet P no (.list [.list [C, .list xs], v])
      (boolVal (vsPQO I ws' cs L v)) (vsPNoCost Cφ N W) := by
    intro v hv
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hv
    exact vsPNo_spec hno hfi hnc hcomp hloc hwl heq hphi H hL hLl
      (by have : (Val.list (L.map encPerm)).wt = (Val.list xs).wt := rfl; omega) (hL g hg)
  have dF := Det.call (Det.mk2 (Det.mk2 b0 v1) v1) ((find_spec hfo hq).mono fun w c hw => ⟨hw.1, hw.2⟩)
  have dT := Det.arith' (op := .eq) dF (Det.length v1) rfl
  have ev : Val.nat (GI.Machine.BinOp.eval .eq (xs.findIdx (vsPQO I ws' cs L)) xs.length) =
      boolVal (decide (∀ g ∈ L, ∀ h ∈ L, vsPLocL I ws' cs (g * h) = vsPLocL I ws' cs (h * g))) := by
    simp only [GI.Machine.BinOp.eval, boolVal]
    have e : xs.findIdx (vsPQO I ws' cs L) = xs.length ↔
        ∀ g ∈ L, ∀ h ∈ L, vsPLocL I ws' cs (g * h) = vsPLocL I ws' cs (h * g) := by
      rw [List.findIdx_eq_length]
      simp only [xs, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        vsPQO_enc, decide_eq_false_iff_not, not_exists, not_and, not_not]
    by_cases hc : ∀ g ∈ L, ∀ h ∈ L, vsPLocL I ws' cs (g * h) = vsPLocL I ws' cs (h * g)
    · rw [if_pos (e.2 hc)]
      have : (decide (∀ g ∈ L, ∀ h ∈ L, vsPLocL I ws' cs (g * h) =
          vsPLocL I ws' cs (h * g))).toNat = 1 := by
        rw [Bool.toNat_eq_one]; simpa only [decide_eq_true_eq] using hc
      rw [this]
    · rw [if_neg (fun h => hc (e.1 h))]
      have : (decide (∀ g ∈ L, ∀ h ∈ L, vsPLocL I ws' cs (g * h) =
          vsPLocL I ws' cs (h * g))).toNat = 0 := by
        rw [Bool.toNat_eq_zero]; simpa only [decide_eq_false_iff_not] using hc
      rw [this]
  rw [ev] at dT
  refine FunDet.intro hf ((Det.letE dl dT).mono ?_)
  have wC : C.wt ≤ W := H.cw
  have hxl : xs.length ≤ (N + 1) ^ 2 := by simp only [xs, List.length_map]; exact hLl
  have hN6 : (N + 1) ^ 2 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hsum : (xs.map fun _ => vsPNoCost Cφ N W).sum ≤ (N + 1) ^ 2 * vsPNoCost Cφ N W := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hxl
  have w2 := wt_list2_le C (.list xs)
  have w3 := wt_list2_le (.list [C, .list xs]) (.list xs)
  have hloop : loopModK * (xs.length + 1) * ((Val.list [.list [C, .list xs], .list xs]).wt +
      2 * xs.length + 3) ≤ 10 ^ 4 * (N + 1) ^ 2 * (W + 1000 * (N + 1) ^ 6) := by
    have h1 : xs.length + 1 ≤ 2 * (N + 1) ^ 2 := by omega
    have h2 : (Val.list [.list [C, .list xs], .list xs]).wt + 2 * xs.length + 3 ≤
        5 * (W + 1000 * (N + 1) ^ 6) := by omega
    calc loopModK * (xs.length + 1) * _ ≤ 1000 * (2 * (N + 1) ^ 2) * (5 * (W + 1000 * (N + 1) ^ 6)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 1000 h1) h2
      _ = 10 ^ 4 * (N + 1) ^ 2 * (W + 1000 * (N + 1) ^ 6) := by ring
  have hFl : xs.findIdx (vsPQO I ws' cs L) ≤ xs.length := List.findIdx_le_length
  have wF := wt_nat_le (xs.findIdx (vsPQO I ws' cs L))
  have wb := wt_boolVal_le (decide (∀ g ∈ L, ∀ h ∈ L, vsPLocL I ws' cs (g * h) =
    vsPLocL I ws' cs (h * g)))
  have hwl : xs.length ≤ (Val.list xs).wt := (length_lt_wt_list xs).le
  have eA : A.wt = (Val.list [C, Val.list [.nat I.n, .list xs]]).wt := rfl
  have w4 := wt_list2_le C (Val.list [.nat I.n, .list xs])
  have wn := wt_nat_le I.n
  have eG' : (encGroup ns).wt = (Val.list [.nat I.n, .list xs]).wt := rfl
  have eA' : (Val.list [C, encGroup ns]).wt = (Val.list [C, Val.list [.nat I.n, .list xs]]).wt :=
    rfl
  have hy : GI.Machine.BinOp.eq.eval (xs.findIdx (vsPQO I ws' cs L)) xs.length ≤ 1 := by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega
  unfold vsPAbCost
  omega

/-! ### A non-commuting pair -/

/-- On `[ctx, ⟨ns⟩]`: `[i, j]` with `i` the first entry of `L = 1 :: ns` that fails to commute
with some entry, and `j` the first entry failing to commute with `L[i]`. -/
def vsPPairE (fo fi : ℕ) : Expr :=
  .letE (.get (arg 1) (.nat 1))
  (.letE (.call fo (mk2 (mk2 (arg 0) (.var 1)) (.var 1)))
    (mk2 (.var 2) (.call fi (mk2 (mk2 (arg 0) (.get (.var 1) (.var 2))) (.var 1)))))

/-- The cost of the pair search. -/
def vsPPairCost (Cφ N W : ℕ) : ℕ := vsPAbCost Cφ N W + vsPNoCost Cφ N W + 1000 * W

set_option maxHeartbeats 4000000 in
/-- **A non-commuting pair.** If the local matrices of `L = 1 :: ns` do not all commute, the
program returns indices `i, j < |L|` with `Λ(L[i] L[j]) ≠ Λ(L[j] L[i])`. -/
theorem vsPPair_spec {P : Program} {f fo no fi nc comp loc eq phi Cφ N W : ℕ}
    (hf : P.funs[f]? = some (vsPPairE fo fi)) (hfo : P.HasAt fo (findFuns fo no))
    (hno : P.funs[no]? = some (vsPNoE fi)) (hfi : P.HasAt fi (findFuns fi nc))
    (hnc : P.funs[nc]? = some (vsPNcE comp loc eq)) (hcomp : P.HasAt comp (composeFuns comp))
    (hloc : P.funs[loc]? = some (vsPLocE phi (loc + 1))) (hwl : P.HasAt (loc + 1) (vsWLocFuns (loc + 1)))
    (heq : P.HasAt eq (vsPEqFuns eq))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {ns : List (Perm (Fin I.n))}
    (hns : ∀ h ∈ ns, h ∈ gens I.gs) (hnl : ns.length ≤ I.n ^ 2)
    (hnc' : ¬ ∀ g ∈ 1 :: ns, ∀ h ∈ 1 :: ns, vsPLocL I ws' cs (g * h) = vsPLocL I ws' cs (h * g)) :
    ∃ i j, ∃ hi : i < (1 :: ns).length, ∃ hj : j < (1 :: ns).length,
      vsPLocL I ws' cs ((1 :: ns)[i] * (1 :: ns)[j]) ≠ vsPLocL I ws' cs ((1 :: ns)[j] * (1 :: ns)[i]) ∧
      FunDet P f (.list [vsPCtx I ws' cs rows hs, encGroup ns]) (.list [.nat i, .nat j])
        (vsPPairCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set L := 1 :: ns
  set xs := L.map encPerm
  have eG : encGroup ns = .list [.nat I.n, .list xs] := rfl
  set A := Val.list [C, encGroup ns]
  have hn := H.n
  have hL : ∀ h ∈ L, h ∈ gens I.gs := by
    intro h hh; rcases List.mem_cons.mp hh with rfl | hh
    · exact one_mem _
    · exact hns h hh
  have wG := wt_encGroup_le_sq hnl
  have hn6 : (I.n + 1) ^ 6 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have wxs : (Val.list xs).wt ≤ (encGroup ns).wt := by
    rw [eG]; exact (wt_le_wt_list (show Val.list xs ∈ [Val.nat I.n, Val.list xs] by simp)).le
  have hLl : L.length ≤ (N + 1) ^ 2 := by
    simp only [L, List.length_cons]
    have : I.n ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hn 2
    nlinarith
  have hLw : (Val.list (L.map encPerm)).wt ≤ 400 * (N + 1) ^ 6 := by
    have : (Val.list (L.map encPerm)).wt = (Val.list xs).wt := rfl
    omega
  -- the first index
  set i := xs.findIdx (vsPQO I ws' cs L)
  have hex : ∃ v ∈ xs, vsPQO I ws' cs L v = true := by
    by_contra hc
    push Not at hc
    apply hnc'
    intro g hg h hh
    have := hc (encPerm g) (List.mem_map_of_mem hg)
    rw [vsPQO_enc] at this
    by_contra hne
    have h2 : decide (∃ h ∈ L, vsPLocL I ws' cs (g * h) ≠ vsPLocL I ws' cs (h * g)) = true :=
      decide_eq_true ⟨h, hh, hne⟩
    rw [h2] at this
    exact this rfl
  have hi : i < xs.length := List.findIdx_lt_length.2 hex
  have hiL : i < L.length := by simpa [xs] using hi
  have hpi := List.findIdx_getElem (p := vsPQO I ws' cs L) (w := hi)
  have exi : xs[i] = encPerm L[i] := by simp [xs]
  rw [exi, vsPQO_enc, decide_eq_true_eq] at hpi
  -- the second index
  set j := xs.findIdx (vsPQC2 I ws' cs L[i])
  have hex2 : ∃ v ∈ xs, vsPQC2 I ws' cs L[i] v = true := by
    obtain ⟨h, hh, hne⟩ := hpi
    exact ⟨encPerm h, List.mem_map_of_mem hh, by rw [vsPQC2_enc]; simpa using hne⟩
  have hj : j < xs.length := List.findIdx_lt_length.2 hex2
  have hjL : j < L.length := by simpa [xs] using hj
  have hpj := List.findIdx_getElem (p := vsPQC2 I ws' cs L[i]) (w := hj)
  have exj : xs[j] = encPerm L[j] := by simp [xs]
  rw [exj, vsPQC2_enc, decide_eq_true_eq] at hpj
  refine ⟨i, j, hiL, hjL, hpj, ?_⟩
  -- the program
  have a0 := Det.arg' (P := P) (vs := [C, encGroup ns]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [C, encGroup ns]) (rest := []) (j := 1) rfl
  rw [eG] at a1
  have dl := Det.get' a1 (Det.nat 1) (show [Val.nat I.n, .list xs][1]? = some (.list xs) from rfl)
  set E := [A, Val.list xs]
  have b0 := Det.arg' (P := P) (vs := [C, encGroup ns]) (rest := [Val.list xs]) (j := 0) rfl
  have v1 := Det.var' (P := P) (env := E) (i := 1) rfl
  have hq : ∀ v ∈ xs, FunDet P no (.list [.list [C, .list xs], v])
      (boolVal (vsPQO I ws' cs L v)) (vsPNoCost Cφ N W) := by
    intro v hv
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hv
    exact vsPNo_spec hno hfi hnc hcomp hloc hwl heq hphi H hL hLl hLw (hL g hg)
  have dF := Det.call (Det.mk2 (Det.mk2 b0 v1) v1) ((find_spec hfo hq).mono fun w c hw => ⟨hw.1, hw.2⟩)
  set E2 := [A, Val.list xs, Val.nat i]
  have c0 := Det.arg' (P := P) (vs := [C, encGroup ns]) (rest := [Val.list xs, Val.nat i]) (j := 0) rfl
  have u1 := Det.var' (P := P) (env := E2) (i := 1) rfl
  have u2 := Det.var' (P := P) (env := E2) (i := 2) rfl
  have dxi := Det.get' u1 u2 (show xs[i]? = some (encPerm L[i]) by rw [List.getElem?_eq_getElem hi, exi])
  have hq2 : ∀ v ∈ xs, FunDet P nc (.list [.list [C, encPerm L[i]], v])
      (boolVal (vsPQC2 I ws' cs L[i] v)) (vsPNcCost Cφ N W) := by
    intro v hv
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hv
    exact vsPNc_spec hnc hcomp hloc hwl heq hphi H (hL _ (List.getElem_mem hiL)) (hL h hh)
  have dF2 := Det.call (Det.mk2 (Det.mk2 c0 dxi) u1) ((find_spec hfi hq2).mono fun w c hw => ⟨hw.1, hw.2⟩)
  have dO := Det.mk2 u2 dF2
  refine FunDet.intro hf ((Det.letE dl (Det.letE dF dO)).mono ?_)
  have wC : C.wt ≤ W := H.cw
  have hxl : xs.length ≤ (N + 1) ^ 2 := by simp only [xs, List.length_map]; exact hLl
  have hN6 : (N + 1) ^ 2 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hsum : (xs.map fun _ => vsPNoCost Cφ N W).sum ≤ (N + 1) ^ 2 * vsPNoCost Cφ N W := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hxl
  have hsum2 : (xs.map fun _ => vsPNcCost Cφ N W).sum ≤ (N + 1) ^ 2 * vsPNcCost Cφ N W := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hxl
  have w2 := wt_list2_le C (.list xs)
  have w3 := wt_list2_le (.list [C, .list xs]) (.list xs)
  have wxi := wt_encPerm_le (L[i]'hiL)
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have w4 := wt_list2_le C (encPerm (L[i]'hiL))
  have w5 := wt_list2_le (.list [C, encPerm (L[i]'hiL)]) (.list xs)
  have hloop : loopModK * (xs.length + 1) * ((Val.list [.list [C, .list xs], .list xs]).wt +
      2 * xs.length + 3) ≤ 10 ^ 4 * (N + 1) ^ 2 * (W + 1000 * (N + 1) ^ 6) := by
    have h1 : xs.length + 1 ≤ 2 * (N + 1) ^ 2 := by omega
    have h2 : (Val.list [.list [C, .list xs], .list xs]).wt + 2 * xs.length + 3 ≤
        5 * (W + 1000 * (N + 1) ^ 6) := by omega
    calc loopModK * (xs.length + 1) * _ ≤ 1000 * (2 * (N + 1) ^ 2) * (5 * (W + 1000 * (N + 1) ^ 6)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 1000 h1) h2
      _ = 10 ^ 4 * (N + 1) ^ 2 * (W + 1000 * (N + 1) ^ 6) := by ring
  have hloop2 : loopModK * (xs.length + 1) * ((Val.list [.list [C, encPerm (L[i]'hiL)], .list xs]).wt +
      2 * xs.length + 3) ≤ 10 ^ 4 * (N + 1) ^ 2 * (W + 400 * (N + 1) ^ 6) := by
    have h1 : xs.length + 1 ≤ 2 * (N + 1) ^ 2 := by omega
    have h2 : (Val.list [.list [C, encPerm (L[i]'hiL)], .list xs]).wt + 2 * xs.length + 3 ≤
        5 * (W + 400 * (N + 1) ^ 6) := by omega
    calc loopModK * (xs.length + 1) * _ ≤ 1000 * (2 * (N + 1) ^ 2) * (5 * (W + 400 * (N + 1) ^ 6)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 1000 h1) h2
      _ = 10 ^ 4 * (N + 1) ^ 2 * (W + 400 * (N + 1) ^ 6) := by ring
  have hwl : xs.length ≤ (Val.list xs).wt := (length_lt_wt_list xs).le
  have eA : A.wt = (Val.list [C, Val.list [.nat I.n, .list xs]]).wt := rfl
  have eA' : (Val.list [C, encGroup ns]).wt = (Val.list [C, Val.list [.nat I.n, .list xs]]).wt :=
    rfl
  have w6 := wt_list2_le C (Val.list [.nat I.n, .list xs])
  have wn := wt_nat_le I.n
  have eG' : (encGroup ns).wt = (Val.list [.nat I.n, .list xs]).wt := rfl
  have wi := wt_nat_le i
  have wj := wt_nat_le j
  have hjx : j ≤ xs.length := List.findIdx_le_length
  have w7 := wt_list2_le (.nat i) (.nat j)
  have eAb : vsPAbCost Cφ N W = (N + 1) ^ 2 * vsPNoCost Cφ N W +
      10 ^ 4 * (N + 1) ^ 2 * (W + 1000 * (N + 1) ^ 6) + 100 * W + 10 ^ 5 * (N + 1) ^ 6 := rfl
  have eNo : vsPNoCost Cφ N W = (N + 1) ^ 2 * vsPNcCost Cφ N W +
      10 ^ 4 * (N + 1) ^ 2 * (W + 400 * (N + 1) ^ 6) + 100 * W + 10 ^ 5 * (N + 1) ^ 6 := rfl
  have ePair : vsPPairCost Cφ N W = vsPAbCost Cφ N W + vsPNoCost Cφ N W + 1000 * W := rfl
  rw [ePair]
  have ei : (Val.nat (List.findIdx (vsPQO I ws' cs L) xs)).wt = (Val.nat i).wt := rfl
  have ej : (Val.nat (List.findIdx (vsPQC2 I ws' cs (L[i]'hiL)) xs)).wt = (Val.nat j).wt := rfl
  have eo : (Val.list [Val.nat i, Val.nat (List.findIdx (vsPQC2 I ws' cs (L[i]'hiL)) xs)]).wt =
      (Val.list [Val.nat i, Val.nat j]).wt := rfl
  omega

end GI.Impl
