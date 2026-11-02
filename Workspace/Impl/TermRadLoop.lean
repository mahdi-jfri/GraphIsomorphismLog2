import Workspace.Impl.TermRadStep

/-!
# T2, one factor: the specification of the step

`radStep_spec`: the step on factor `i` keeps the invariant `RadInv` (the group of the `h` with
`radCond … i h` becomes the group of those with `radCond … (i + 1) h`), at cost at most
`radStepCost` of the weight of its argument.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The cost of the nonabelian branch, bounded in terms of `W` and `Y = 1000 (W + 1)⁶`. -/
theorem rad_else_spec (hqc : QuotientCentralizer) (hni : NormalizedIntersection)
    {P : Program} {mg jni jqc : ℕ} (hmg : P.HasAt mg (mkGroupFuns mg))
    (hjq : P.prims[jqc]? = some (quotientCentralizerPrim hqc))
    (hji : P.prims[jni]? = some (normalizedIntersectionPrim hni))
    {gs ns : List (Perm (Fin n))} {cs acc : Val} {i : ℕ} {us vs' : List (Perm (Fin n))}
    {v3 v4 : Val} {A : Subgroup (Perm (Fin n))} (hA : GroupVal n acc A)
    (hAH : A ≤ gens gs) (hnU : ∀ g ∈ gens gs, ∀ x ∈ gens us, g * x * g⁻¹ ∈ gens us)
    (hnV : ∀ g ∈ gens gs, ∀ x ∈ gens vs', g * x * g⁻¹ ∈ gens vs')
    (hVU : gens vs' ≤ gens us) (hUH : gens us ≤ gens gs)
    (hU : (encGroup us).wt ≤ 14 * radW (encGroup gs) (encGroup ns) cs acc i + 14)
    (hV : (encGroup vs').wt ≤ 14 * radW (encGroup gs) (encGroup ns) cs acc i + 14)
    (hnW : n + 1 ≤ radW (encGroup gs) (encGroup ns) cs acc i) :
    EvalAll P ([.list [.list [encGroup gs, encGroup ns, cs], .nat i, acc]] ++ [encGroup us] ++
        [encGroup vs'] ++ [v3] ++ [v4])
      (.letE (.prim jqc (mk4 radHvE (.var 2) radHvE (.var 1)))
        (.letE (.prim jni (mk2 (arg 2) (.call mg (mk2 radNE (.var 5)))))
          (.call mg (mk2 radNE (.var 6)))))
      (fun w c => (∃ ks : List (Perm (Fin n)), w = encGroup ks ∧ ks.length ≤ n ^ 2 ∧
          ∀ h, h ∈ gens ks ↔ h ∈ A ∧ h ∈ gens gs ∧
            ∀ x ∈ gens us, h * x * h⁻¹ * x⁻¹ ∈ gens vs') ∧
        c ≤ (quotientCentralizerPrim hqc).boundSize (1000 * (radW (encGroup gs) (encGroup ns) cs
            acc i + 1) ^ 6) + (normalizedIntersectionPrim hni).boundSize (1000 *
            (radW (encGroup gs) (encGroup ns) cs acc i + 1) ^ 6) +
          100 * (1000 * (radW (encGroup gs) (encGroup ns) cs acc i + 1) ^ 6) ^ 2) := by
  have hw := rad_wt_facts (encGroup gs) (encGroup ns) cs acc i
  set W := radW (encGroup gs) (encGroup ns) cs acc i with hWdef
  set Y := 1000 * (W + 1) ^ 6 with hY
  have hW6 : W + 1 ≤ (W + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have hn6 : (n + 1) ^ 6 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_left (by omega) _
  have hn9 : 8 * mkGroupK * (n + 1) ^ 9 ≤ Y ^ 2 := by
    have : (n + 1) ^ 9 ≤ (W + 1) ^ 12 :=
      (Nat.pow_le_pow_left (show n + 1 ≤ W + 1 by omega) 9).trans
        (Nat.pow_le_pow_right (by omega) (by omega))
    have e : Y ^ 2 = 1000000 * (W + 1) ^ 12 := by rw [hY]; ring
    simp only [mkGroupK]; omega
  have hY1 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have dhv := rad_d_hv (P := P) (hv := encGroup gs) (nv := encGroup ns) (cs := cs) (acc := acc)
    (i := i) (rest := [encGroup us, encGroup vs', v3, v4])
  have dn := rad_d_n (P := P) (hv := encGroup gs) (nv := encGroup ns) (cs := cs) (acc := acc)
    (i := i) (rest := [encGroup us, encGroup vs', v3, v4]) (gs := gs) rfl
  have dqa := Det.mk4 dhv (Det.var' (P := P) (i := 2) (v := encGroup vs') rfl) dhv
    (Det.var' (P := P) (i := 1) (v := encGroup us) rfl)
  have hqarg := wt_list4_le (encGroup gs) (encGroup vs') (encGroup gs) (encGroup us)
  have hqs : (Val.list [encGroup gs, encGroup vs', encGroup gs, encGroup us]).size ≤ Y :=
    (Val.size_le_wt _).trans (by omega)
  have hnorm : ∀ g ∈ gens gs, ∀ k ∈ gens vs', g * k * g⁻¹ ∈ gens vs' := hnV
  refine EvalAll.letE (quotientCentralizer_call hqc hjq dqa ⟨gs, rfl, rfl⟩ ⟨vs', rfl, rfl⟩
    ⟨gs, rfl, rfl⟩ ⟨us, rfl, rfl⟩ (hVU.trans hUH) hnorm (hVU.trans hUH) hVU le_rfl hUH hnU)
    fun v5 c5 h5 => ?_
  obtain ⟨⟨C, hC, hCm⟩, hc5⟩ := h5
  have hb5 := (quotientCentralizerPrim hqc).bound_le hqs
  -- `A ∩ C`
  have dacc := rad_d_acc (P := P) (hv := encGroup gs) (nv := encGroup ns) (cs := cs) (acc := acc)
    (i := i) (rest := [encGroup us, encGroup vs', v3, v4, v5])
  have dn5 := rad_d_n (P := P) (hv := encGroup gs) (nv := encGroup ns) (cs := cs) (acc := acc)
    (i := i) (rest := [encGroup us, encGroup vs', v3, v4, v5]) (gs := gs) rfl
  obtain ⟨cks, hcl, hcg, dC, hCw⟩ := rad_mk_det hmg dn5 (Det.var' (P := P) (i := 5) (v := v5) rfl) hC
  have hCn : Normalizes A C := by
    intro g hg y hy
    exact rad_qc_normalized hnU hnV hCm g (hAH hg) y hy
  have dna := Det.mk2 dacc dC
  have hnarg := wt_list2_le acc (encGroup cks)
  have hns : (Val.list [acc, encGroup cks]).size ≤ Y := (Val.size_le_wt _).trans (by omega)
  refine EvalAll.letE (normalizedIntersection_call hni hji dna hA ⟨cks, rfl, hcg⟩ hCn)
    fun v6 c6 h6 => ?_
  obtain ⟨hv6, hc6⟩ := h6
  have hb6 := (normalizedIntersectionPrim hni).bound_le hns
  have dn6 := rad_d_n (P := P) (hv := encGroup gs) (nv := encGroup ns) (cs := cs) (acc := acc)
    (i := i) (rest := [encGroup us, encGroup vs', v3, v4, v5, v6]) (gs := gs) rfl
  obtain ⟨ks, hkl, hkg, dK, hKw⟩ := rad_mk_det hmg dn6 (Det.var' (P := P) (i := 6) (v := v6) rfl) hv6
  refine dK.post fun c hc => ⟨⟨ks, rfl, hkl, fun h => ?_⟩, ?_⟩
  · rw [hkg, Subgroup.mem_inf, hCm]
  · -- the cost
    have w5 := GensVal.wt_le hC
    have w6 := GensVal.wt_le hv6
    have hl1 := wt_list2_le (.nat n) v5
    have hl2 := wt_list2_le (.nat n) v6
    have hnw : (Val.nat n).wt < (encGroup gs).wt := wt_le_wt_list (vs := [.nat n, _]) (by simp)
    have hKw' : (encGroup ks).wt ≤ Y := by omega
    clear dK dn6 dC dn5 dna dacc dqa dhv dn
    omega

/-- Where the step and its modules sit in the program. -/
structure RadStepAt (P : Program) (g ap mg le jder jni jqc jmem : ℕ) (hder : DerivedSubgroup)
    (hqc : QuotientCentralizer) (hni : NormalizedIntersection) (hmem : Membership) : Prop where
  step : P.funs[g]? = some (radStepBody ap mg le jder jni jqc)
  ap : P.HasAt ap (appendFuns ap)
  mg : P.HasAt mg (mkGroupFuns mg)
  le : P.HasAt le (leFuns le jmem)
  jd : P.prims[jder]? = some (derivedSubgroupPrim hder)
  jq : P.prims[jqc]? = some (quotientCentralizerPrim hqc)
  ji : P.prims[jni]? = some (normalizedIntersectionPrim hni)
  jm : P.prims[jmem]? = some (membershipPrim hmem)

/-- The chief series as a value. -/
def radCsVal (L : List (List (Perm (Fin n)))) : Val := .list (L.map fun hs => .list (hs.map encPerm))

open Classical in
/-- **The step on factor `i`** (paragraph after Lemma A.21). -/
theorem radStep_spec {hder : DerivedSubgroup} {hqc : QuotientCentralizer}
    {hni : NormalizedIntersection} {hmem : Membership}
    {P : Program} {g ap mg le jder jni jqc jmem : ℕ}
    (hP : RadStepAt P g ap mg le jder jni jqc jmem hder hqc hni hmem)
    {gs ns : List (Perm (Fin n))} {L : List (List (Perm (Fin n)))}
    (hNH : gens ns ≤ gens gs) (hn : GI.Multicoset.Normalizes (gens gs) (gens ns))
    (hs : IsChiefSeries (gens gs) (L.map gens)) (hl : ∀ hs ∈ L, hs.length ≤ n ^ 2)
    {i : ℕ} (hi : i + 1 < L.length) {acc : Val}
    (hinv : RadInv (gens gs) (gens ns) (L.map gens) (encGroup gs) i acc) :
    FunAll P g (.list [.list [encGroup gs, encGroup ns, radCsVal L], .nat i, acc])
      (fun w c => RadInv (gens gs) (gens ns) (L.map gens) (encGroup gs) (i + 1) w ∧
        c ≤ radStepCost (derivedSubgroupPrim hder) (quotientCentralizerPrim hqc)
          (normalizedIntersectionPrim hni) (membershipPrim hmem)
          (radW (encGroup gs) (encGroup ns) (radCsVal L) acc i)) := by
  obtain ⟨A, hA, hAm, hAw⟩ := hinv
  have hw := rad_wt_facts (encGroup gs) (encGroup ns) (radCsVal L) acc i
  set W := radW (encGroup gs) (encGroup ns) (radCsVal L) acc i with hWdef
  set Y := 1000 * (W + 1) ^ 6 with hY
  have hcs : radCsVal L = .list (L.map fun hs => .list (hs.map encPerm)) := rfl
  have hnW : n + 1 ≤ W := by
    have := S_le_wt_encGroup gs
    have : n + 1 ≤ (gs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hLW : L.length < W := by
    have h1 := length_lt_wt_list (L.map fun hs => Val.list (hs.map encPerm))
    simp only [List.length_map] at h1
    have : (radCsVal L).wt = (Val.list (L.map fun hs => Val.list (hs.map encPerm))).wt := rfl
    omega
  have hW6 : W + 1 ≤ (W + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have hW2 : (W + 1) ^ 2 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn6 : (n + 1) ^ 6 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_left (by omega) _
  have hn2 : (n + 1) ^ 2 ≤ (W + 1) ^ 6 :=
    (Nat.pow_le_pow_left (show n + 1 ≤ W + 1 by omega) 2).trans hW2
  have hn9 : 8 * mkGroupK * (n + 1) ^ 9 ≤ Y ^ 2 := by
    have : (n + 1) ^ 9 ≤ (W + 1) ^ 12 :=
      (Nat.pow_le_pow_left (show n + 1 ≤ W + 1 by omega) 9).trans
        (Nat.pow_le_pow_right (by omega) (by omega))
    have e : Y ^ 2 = 1000000 * (W + 1) ^ 12 := by rw [hY]; ring
    simp only [mkGroupK]; omega
  have hY1 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY2 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  -- the chief terms and their facts
  have hi0 : i < L.length := by omega
  have hti : radTerm (L.map gens) i = gens (L[i]'hi0) := rad_term_map hi0
  have hti1 : radTerm (L.map gens) (i + 1) = gens (L[i + 1]'hi) := rad_term_map hi
  have hCi : gens (L[i]'hi0) ≤ gens gs := by have := rad_term_le hs i; rwa [hti] at this
  have hCi1 : gens (L[i + 1]'hi) ≤ gens gs := by have := rad_term_le hs (i + 1); rwa [hti1] at this
  have hnCi : ∀ g ∈ gens gs, ∀ x ∈ gens (L[i]'hi0), g * x * g⁻¹ ∈ gens (L[i]'hi0) := by
    have := rad_term_normalized hs i; rwa [hti] at this
  have hnCi1 : ∀ g ∈ gens gs, ∀ x ∈ gens (L[i + 1]'hi), g * x * g⁻¹ ∈ gens (L[i + 1]'hi) := by
    have := rad_term_normalized hs (i + 1); rwa [hti1] at this
  have hCle : gens (L[i + 1]'hi) ≤ gens (L[i]'hi0) := by
    have := (hs.2.2.2 i (by simpa using hi)).1.le
    simpa using this
  have hwi : (Val.list ((L[i]'hi0).map encPerm)).wt ≤ W := by
    have : (Val.list ((L[i]'hi0).map encPerm)).wt < (radCsVal L).wt :=
      wt_le_wt_list (List.mem_map.mpr ⟨(L[i]'hi0), List.getElem_mem hi0, rfl⟩)
    omega
  have hwi1 : (Val.list ((L[i + 1]'hi).map encPerm)).wt ≤ W := by
    have : (Val.list ((L[i + 1]'hi).map encPerm)).wt < (radCsVal L).wt :=
      wt_le_wt_list (List.mem_map.mpr ⟨(L[i + 1]'hi), List.getElem_mem hi, rfl⟩)
    omega
  -- `U = N C_i`
  obtain ⟨dU, hUw⟩ := rad_union_det (P := P) (rest := []) hP.ap (gs := gs) (ns := ns) rfl rfl
    (rad_d_csj hcs hi0 rad_d_i) hwi
  refine FunAll.intro hP.step (EvalAll.letE dU fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  -- `V = N C_{i+1}`
  have dip := Det.arith' (z := i + 1) (P := P) (op := .add)
    (rad_d_i (hv := encGroup gs) (nv := encGroup ns) (cs := radCsVal L) (acc := acc)
      (rest := [encGroup (ns ++ (L[i]'hi0))])) (Det.nat 1) rfl
  obtain ⟨dV, hVw⟩ := rad_union_det (P := P) (rest := [encGroup (ns ++ (L[i]'hi0))]) hP.ap
    (gs := gs) (ns := ns) rfl rfl (rad_d_csj hcs hi dip) hwi1
  refine EvalAll.letE dV fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  -- `D = ⁅C_i, C_i⁆`
  have dn3 := rad_d_n (P := P) (hv := encGroup gs) (nv := encGroup ns) (cs := radCsVal L)
    (acc := acc) (i := i) (rest := [encGroup (ns ++ (L[i]'hi0)), encGroup (ns ++ (L[i + 1]'hi))]) (gs := gs) rfl
  obtain ⟨hs3, hl3, hg3, dC3, hw3⟩ := rad_mk_det hP.mg dn3 (rad_d_csj hcs hi0 rad_d_i)
    (SeriesVal.getElem hl i hi0)
  have hs3s : (encGroup hs3).size ≤ Y := (Val.size_le_wt _).trans (by omega)
  refine EvalAll.letE (derivedSubgroup_call hder hP.jd dC3 ⟨hs3, rfl, rfl⟩) fun v3 c3 h3 => ?_
  obtain ⟨hv3, hc3⟩ := h3
  have hb3 := (derivedSubgroupPrim hder).bound_le hs3s
  -- the test `D ≤ V`
  have dn4 := rad_d_n (P := P) (hv := encGroup gs) (nv := encGroup ns) (cs := radCsVal L)
    (acc := acc) (i := i) (rest := [encGroup (ns ++ (L[i]'hi0)), encGroup (ns ++ (L[i + 1]'hi)), v3])
    (gs := gs) rfl
  obtain ⟨ds, hdl, hdg, dD, hDw⟩ := rad_mk_det hP.mg dn4 (Det.var' (P := P) (i := 3) (v := v3) rfl) hv3
  have hles := le_spec hmem hP.le hP.jm (⟨ns ++ (L[i + 1]'hi), rfl, rfl⟩ :
    GroupVal n (encGroup (ns ++ (L[i + 1]'hi))) (gens (ns ++ (L[i + 1]'hi)))) ds
  have d4 := Det.call (Det.mk2 (Det.var' (P := P) (i := 2) (v := encGroup (ns ++ (L[i + 1]'hi))) rfl) dD)
    hles
  set b := decide (gens ds ≤ gens (ns ++ (L[i + 1]'hi))) with hb
  refine EvalAll.letE d4 fun v4 c4 h4 => ?_
  obtain ⟨rfl, hc4⟩ := h4
  simp only [← hWdef] at hc1 hc2 hc3 hc4 hUw hVw
  -- the weights and bounds of the test
  have hlarg := wt_list2_le (encGroup (ns ++ (L[i + 1]'hi))) (encGroup ds)
  have hmarg := wt_list2_le (encGroup (ns ++ (L[i + 1]'hi))) (encPerm (1 : Perm (Fin n)))
  have hp1 := wt_encPerm_le (1 : Perm (Fin n))
  have hms : (Val.list [encGroup (ns ++ (L[i + 1]'hi)), encPerm (1 : Perm (Fin n))]).size ≤ Y :=
    (Val.size_le_wt _).trans (by omega)
  have hbm := (membershipPrim hmem).bound_le hms
  have hX : (Val.list [encGroup (ns ++ (L[i + 1]'hi)), encGroup ds]).wt ≤ Y := by omega
  have hXm := Nat.mul_le_mul hX hbm
  have hX3 : (Val.list [encGroup (ns ++ (L[i + 1]'hi)), encGroup ds]).wt ^ 3 ≤ Y ^ 3 :=
    Nat.pow_le_pow_left hX 3
  -- the meaning of the test
  have hDeq : gens ds = ⁅gens (L[i]'hi0), gens (L[i]'hi0)⁆ := by rw [hdg, hg3]
  have hVeq : gens (ns ++ (L[i + 1]'hi)) = gens ns ⊔ radTerm (L.map gens) (i + 1) := by
    rw [rad_gens_append, hti1]
  have hUeq : gens (ns ++ (L[i]'hi0)) = gens ns ⊔ radTerm (L.map gens) i := by rw [rad_gens_append, hti]
  have w3 := GensVal.wt_le hv3
  have hl4 := wt_list2_le (.nat n) v3
  have hl5 := wt_list2_le (.nat n) (.list ((L[i]'hi0).map encPerm))
  have hnw : (Val.nat n).wt < (encGroup gs).wt := wt_le_wt_list (vs := [.nat n, _]) (by simp)
  have hcost_pre : c1 + c2 + c3 + c4 ≤ 200 * Y + 6 * Y ^ 2 + (derivedSubgroupPrim hder).boundSize Y +
      Y * (membershipPrim hmem).boundSize Y + 20000 * Y ^ 3 := by
    clear dD dn4 dC3 dn3 dV dip dU d4 hles
    have : (boolVal b).wt ≤ 3 := wt_boolVal_le b
    clear_value Y W
    omega
  clear dD dn4 dC3 dn3 dV dip dU d4 hles
  cases hbv : b
  · -- nonabelian factor
    have hna : ¬ ⁅radTerm (L.map gens) i, radTerm (L.map gens) i⁆ ≤
        gens ns ⊔ radTerm (L.map gens) (i + 1) := by
      rw [hti, ← hDeq, ← hVeq]
      simpa [hb] using hbv
    have dc := Det.var' (P := P) (env := [.list [.list [encGroup gs, encGroup ns, radCsVal L],
      .nat i, acc]] ++ [encGroup (ns ++ (L[i]'hi0))] ++ [encGroup (ns ++ (L[i + 1]'hi))] ++ [v3] ++
      [boolVal false]) (i := 4) (v := .nat 0) rfl
    have hAH : A ≤ gens gs := fun h hh => ((hAm h).mp hh).1
    have hnU : ∀ g ∈ gens gs, ∀ x ∈ gens (ns ++ (L[i]'hi0)), g * x * g⁻¹ ∈ gens (ns ++ (L[i]'hi0)) := by
      rw [rad_gens_append]; exact rad_sup_normalized hn hnCi
    have hnV : ∀ g ∈ gens gs, ∀ x ∈ gens (ns ++ (L[i + 1]'hi)), g * x * g⁻¹ ∈ gens (ns ++ (L[i + 1]'hi)) := by
      rw [rad_gens_append]; exact rad_sup_normalized hn hnCi1
    have hVU : gens (ns ++ (L[i + 1]'hi)) ≤ gens (ns ++ (L[i]'hi0)) := by
      rw [rad_gens_append, rad_gens_append]; exact sup_le_sup_left hCle _
    have hUH : gens (ns ++ (L[i]'hi0)) ≤ gens gs := by rw [rad_gens_append]; exact sup_le hNH hCi
    have he := rad_else_spec hqc hni (P := P) (cs := radCsVal L) (i := i) (v3 := v3)
      (v4 := boolVal false) hP.mg hP.jq hP.ji hA hAH hnU hnV hVU hUH hUw hVw hnW
    refine (rad_ite_zero dc he).mono fun w c hwc => ?_
    obtain ⟨ce, ⟨⟨ks, rfl, hkl, hkm⟩, hce⟩, hcw⟩ := hwc
    refine ⟨⟨gens ks, ⟨ks, rfl, rfl⟩, fun h => ?_, ?_⟩, ?_⟩
    · rw [hkm, hAm, rad_cond_succ, ← hUeq, ← hVeq]
      constructor
      · rintro ⟨h1, -, h3⟩
        exact ⟨h1, fun _ x hx => h3 x hx⟩
      · rintro ⟨h1, h3⟩
        exact ⟨h1, h1.1, h3 (by rwa [hVeq])⟩
    · have := wt_encGroup_le_sq hkl
      omega
    · have hkw := wt_encGroup_le_sq hkl
      have hY3 : Y ≤ Y ^ 3 := hY1.trans hY2
      unfold radStepCost
      rw [← hY]
      rw [← hWdef, ← hY] at hce
      have h1 := wt_nat_le 0
      have hkY : (encGroup ks).wt ≤ Y := by omega
      clear_value Y W
      have hYpos : 1 ≤ Y := by omega
      clear * - hcost_pre hce hcw h1 hkY hY1 hY2 hY3 hYpos
      omega
  · -- abelian factor: the group does not change
    have hab : ⁅radTerm (L.map gens) i, radTerm (L.map gens) i⁆ ≤
        gens ns ⊔ radTerm (L.map gens) (i + 1) := by
      rw [hti, ← hDeq, ← hVeq]
      simpa [hb] using hbv
    have dc := Det.var' (P := P) (env := [.list [.list [encGroup gs, encGroup ns, radCsVal L],
      .nat i, acc]] ++ [encGroup (ns ++ (L[i]'hi0))] ++ [encGroup (ns ++ (L[i + 1]'hi))] ++ [v3] ++
      [boolVal true]) (i := 4) (v := .nat 1) rfl
    have dt := Det.ite_pos (e := .letE (.prim jqc (mk4 radHvE (.var 2) radHvE (.var 1)))
        (.letE (.prim jni (mk2 (arg 2) (.call mg (mk2 radNE (.var 5)))))
          (.call mg (mk2 radNE (.var 6))))) dc (by decide)
      (rad_d_acc (P := P) (hv := encGroup gs) (nv := encGroup ns) (cs := radCsVal L) (acc := acc)
        (i := i) (rest := [encGroup (ns ++ (L[i]'hi0)), encGroup (ns ++ (L[i + 1]'hi)), v3, boolVal true]))
    refine dt.post fun c hc => ⟨⟨A, hA, fun h => ?_, hAw⟩, ?_⟩
    · rw [hAm, rad_cond_succ]
      exact ⟨fun h1 => ⟨h1, fun hna => absurd hab hna⟩, fun h1 => h1.1⟩
    · have hY3 : Y ≤ Y ^ 3 := hY1.trans hY2
      unfold radStepCost
      rw [← hY]
      rw [← hWdef] at hc
      have h1 := wt_nat_le 1
      have hWY : W + 1 ≤ Y := by omega
      have hacc : acc.wt < W := hw.2.2.2.1
      clear_value Y W
      clear * - hcost_pre hc h1 hWY hacc hY1 hY2 hY3
      omega

end GI.Impl
