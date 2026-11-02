import Workspace.Impl.AggCmpStCh
import Workspace.Impl.AggCertMvKey

/-!
# The start of a pair: the modules within the budget

Each module that the start of a pair calls, in the budget form of the move program (`CpFB`, one
module budget `cpG`, as in `AggCertMvKey.lean`): the label points of a tuple (`cm_bud_sh`), the
orbit of the label points (`cm_bud_tup`), the search for the label points of the second tuple
(`cm_bud_kfd`), the stabilizer of the label points (`cm_bud_stab`), the identity on positions
(`cm_bud_rng`) and the first part of a pair (`cm_bud_gat`). The reduction of the stabilizer is
`cp_bud_kr`.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

/-- The size facts that the bound `Bw` gives. -/
theorem cm_st_sizes {k P M₀ N q Bw : ℕ} (hBw : cmBw P k q M₀ (N * N) ≤ Bw) :
    10 ^ 5 * ((N + 1) * (k + q + 1) ^ 6) ≤ Bw ∧ P < Bw := by
  have h1 : N ≤ N * N := Nat.le_mul_self N
  have h2 : (N + 1) * (k + q + 1) ^ 6 ≤ (M₀ + N * N + 1) * (k + q + 1) ^ 6 :=
    Nat.mul_le_mul_right _ (by omega)
  unfold cmBw at hBw
  have : 10 ^ 4 * (M₀ + N * N + 1) * (k + q + 1) ^ 6 =
    10 ^ 4 * ((M₀ + N * N + 1) * (k + q + 1) ^ 6) := by ring
  have h3 : 1 ≤ (k + q + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ (M₀ + N * N + 1) * (k + q + 1) ^ 6 := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

section Bud

variable (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) {W : ℕ} {Pg : Program}
  {b jp : ℕ} (hsa : CmStAt Pg b jp) {k q κ : ℕ}

include hsa

omit hsa in
/-- A list of the numbers of the label points of a tuple is light. -/
theorem cm_wt_key {X : List (Fin (k + q))} (hX : X.length ≤ q) :
    (natList (ptsKey X)).wt ≤ 7 * (k + q + 1) ^ 2 := by
  have h := wt_natList_le (xs := ptsKey X) (B := k + q) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact i.isLt.le)
  have hl : (ptsKey X).length ≤ q := by unfold ptsKey; rw [List.length_map]; exact hX
  have : (ptsKey X).length * (2 * (k + q) + 5) ≤ (k + q + 1) * (2 * (k + q) + 5) :=
    Nat.mul_le_mul_right _ (by omega)
  nlinarith

omit hsa in
theorem cm_lab_length (t : Fin κ → Fin q) : (cmLabPts k t).length = κ := by
  simp [cmLabPts, labPts]

/-- **The label points of a tuple, within the budget.** -/
theorem cm_bud_sh (t : Fin κ → Fin q) (hκ : κ ≤ q) (hW : 100 * (k + q + 1) ^ 6 ≤ W) :
    CpFB Pg (cmShM b) (.list [.nat k, stTv t]) W (cpG hst hpre hm W)
      (fun w => w = natList (ptsKey (cmLabPts k t))) := by
  have h := sbSh_spec hsa.shM hsa.add (k := k) (d := stL fun i => ((t i : Fin q) : ℕ))
    (Y := k + q) (by
      intro x hx
      have := stL_le (stL_le_of_fin t) x hx
      omega) (by simp [stL]; omega) (by omega)
  rw [cm_shift_eq] at h
  have hw := cm_wt_key (k := k) (q := q) (X := cmLabPts k t) (by rw [cm_lab_length]; exact hκ)
  obtain ⟨f1, -, -, f24, f46, -, -, -, -, -⟩ := cp_pow_facts k q
  refine CpFB.det h ?_ (by omega) rfl
  have h1 : sbShK * (k + q + 1) ^ 3 ≤ sbShK * (W + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by
      have : k + q + 1 ≤ (k + q + 1) ^ 6 := Nat.le_self_pow (by omega) _
      omega) 3)
  have h2 := cp_poly_le (W := W) (K := sbShK) (d := 3) (by simp [sbShK]) (by norm_num) (by omega)
  have := cpG_poly hst hpre hm (W := W)
  omega

/-- **The orbit of the label points, within the budget.** -/
theorem cm_bud_tup (O : TestTupleOrder q κ) {ps : List (Perm (Fin k) × Perm (Fin q))}
    (hpl : ps.length ≤ (k + q) ^ 2) (t : Fin κ ↪ Fin q)
    (hW : 100 * ((O.tuples.length + 1) * (k + q + 1) ^ 6) ≤ W) :
    CpFB Pg (cmTup b) (.list [.list [.nat k, .nat q], .list (ps.map pairV),
        natList (ptsKey (cmLabPts k (t : Fin κ → Fin q))), .nat O.tuples.length]) W
      (cpG hst hpre hm W)
      (fun w => ∃ Lo : List (List (Fin (k + q)) × Perm (Fin (k + q))), w = encPairs ptsKey Lo ∧
        (Lo.map Prod.fst).Nodup ∧
        (∀ y, y ∈ Lo.map Prod.fst ↔ y ∈ actOrbit (fun g (xs : List (Fin (k + q))) => xs.map g)
          (ps.map encPair) (cmLabPts k (t : Fin κ → Fin q))) ∧
        (∀ p ∈ Lo, p.2 ∈ gens (ps.map encPair) ∧ (cmLabPts k (t : Fin κ → Fin q)).map p.2 = p.1) ∧
        Lo.length ≤ O.tuples.length ∧
        (encPairs ptsKey Lo).wt ≤ 70 * ((O.tuples.length + 1) * (k + q + 1) ^ 6)) := by
  have hκ : κ ≤ q := by simpa using Fintype.card_le_of_embedding t
  have hB := cm_orbit_le O ps t
  obtain ⟨f1, f2, -, f24, f46, -, -, -, -, -⟩ := cp_pow_facts k q
  have g0 : k + q + 1 ≤ (k + q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  set P := (O.tuples.length + 1) * (k + q + 1) ^ 6 with hP
  have g2 : (k + q + 1) ^ 6 ≤ P := Nat.le_mul_of_pos_left _ (by omega)
  have g3 : O.tuples.length + 1 ≤ P := Nat.le_mul_of_pos_right _ (by omega)
  refine FunAll.mono (graphTup_spec hsa.tup ps _ hB) ?_
  rintro w c ⟨Lo, rfl, hnd, hmem, hgood, hc⟩
  have hlen : Lo.length ≤ O.tuples.length := by
    have := cp_length_eq_ncard hnd hmem
    rw [List.length_map] at this
    omega
  have hLw : (encPairs ptsKey Lo).wt ≤ 70 * P := by
    have hent : ∀ v ∈ Lo.map (GI.Lang.encPair ptsKey), v.wt ≤ 30 * (k + q + 1) ^ 2 := by
      intro v hv
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
      have hpl1 : p.1.length ≤ q := by
        rw [← (hgood p hp).2, List.length_map, cm_lab_length]; exact hκ
      have h1 := cm_wt_key (k := k) (q := q) hpl1
      have h2 := wt_encPerm_le p.2
      have h3 := wt_list2_le (natList (ptsKey p.1)) (encPerm p.2)
      have : (GI.Lang.encPair ptsKey p).wt = (Val.list [natList (ptsKey p.1), encPerm p.2]).wt :=
        rfl
      omega
    have := cp_wt_list (vs := Lo.map (GI.Lang.encPair ptsKey)) (n := O.tuples.length)
      (c := 30 * (k + q + 1) ^ 2) (by simpa using hlen) hent
    have e : (encPairs ptsKey Lo).wt = (Val.list (Lo.map (GI.Lang.encPair ptsKey))).wt := rfl
    have g1 : O.tuples.length * (2 * (30 * (k + q + 1) ^ 2) + 1) ≤ 61 * P := by
      have : 2 * (30 * (k + q + 1) ^ 2) + 1 ≤ 61 * (k + q + 1) ^ 6 := by omega
      calc O.tuples.length * (2 * (30 * (k + q + 1) ^ 2) + 1)
          ≤ (O.tuples.length + 1) * (61 * (k + q + 1) ^ 6) := Nat.mul_le_mul (by omega) this
        _ = 61 * P := by rw [hP]; ring
    omega
  refine ⟨⟨Lo, rfl, hnd, hmem, hgood, hlen, hLw⟩, by omega, ?_⟩
  -- the cost
  have hM : tupM k q ps O.tuples.length (cmLabPts k (t : Fin κ → Fin q)).length ≤ W := by
    unfold tupM
    rw [cm_lab_length]
    omega
  have h3 : graphTupK * tupM k q ps O.tuples.length (cmLabPts k (t : Fin κ → Fin q)).length ^ 12
      ≤ graphTupK * (W + 1) ^ 12 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 12)
  have h5 := cp_poly_le (W := W) (K := graphTupK) (d := 12) (by simp [graphTupK]) (by norm_num)
    (by omega)
  have := cpG_poly hst hpre hm (W := W)
  omega

/-- **The search for the label points of the second tuple, within the budget.** -/
theorem cm_bud_kfd (y : List (Fin (k + q))) (Lo : List (List (Fin (k + q)) × Perm (Fin (k + q))))
    (hw : (Val.list [natList (ptsKey y), encPairs ptsKey Lo]).wt ≤ W) :
    CpFB Pg (cmKFd b) (.list [natList (ptsKey y), encPairs ptsKey Lo]) W (cpG hst hpre hm W)
      (fun w => w = .nat (Lo.findIdx (fun r => decide (r.1 = y)))) := by
  have hy : (natList (ptsKey y)).wt < W := lt_of_lt_of_le (cm_wt_lt_of_mem (by simp)) hw
  have hLo : (encPairs ptsKey Lo).wt < W := lt_of_lt_of_le (cm_wt_lt_of_mem (by simp)) hw
  have hW1 : 1 ≤ W := by omega
  have hE : ∀ x ∈ Lo.map (GI.Lang.encPair ptsKey), x.wt < W := fun x hx =>
    lt_trans (cm_wt_lt_of_mem hx) hLo
  have hF := find_spec hsa.kfd (c := natList (ptsKey y)) (xs := Lo.map (GI.Lang.encPair ptsKey))
    (q := pairTest (k + q) ptsKey y) (B := fun _ => 100000 * W ^ 2) (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      have hpw := hE _ hx
      have hp1 : (natList (ptsKey p.1)).wt ≤ W := by
        have := cm_wt_lt_of_mem (vs := [natList (ptsKey p.1), encPerm p.2])
          (v := natList (ptsKey p.1)) (by simp)
        have e : (GI.Lang.encPair ptsKey p).wt =
          (Val.list [natList (ptsKey p.1), encPerm p.2]).wt := rfl
        omega
      have hW2 : W ≤ W ^ 2 := Nat.le_self_pow (by norm_num) _
      have := orbTest_spec hsa.tst hsa.eqN ptsKey hW1 y p hy.le hp1 (by omega)
      rw [pairTest_encPair ptsKey_injective]
      have e : decide (ptsKey y = ptsKey p.1) = decide (p.1 = y) :=
        Bool.decide_congr ⟨fun h => (ptsKey_injective h).symm, fun h => h ▸ rfl⟩
      rw [e] at this
      exact this)
  have hlen : Lo.length + 2 ≤ W := by
    have := length_lt_wt_list (Lo.map (GI.Lang.encPair ptsKey))
    have e : (encPairs ptsKey Lo).wt = (Val.list (Lo.map (GI.Lang.encPair ptsKey))).wt := rfl
    simp only [List.length_map] at this
    omega
  refine FunAll.mono hF fun w cost hw' => ?_
  obtain ⟨hw1, hc⟩ := hw'
  rw [findIdx_map_pairTest ptsKey_injective] at hw1
  subst hw1
  refine ⟨rfl, ?_, ?_⟩
  · have h1 : Lo.findIdx (fun r => decide (r.1 = y)) ≤ Lo.length := List.findIdx_le_length
    have := wt_nat_le (Lo.findIdx (fun r => decide (r.1 = y)))
    omega
  · rw [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
    have e1 : (Val.list [natList (ptsKey y), .list (Lo.map (GI.Lang.encPair ptsKey))]).wt =
      (Val.list [natList (ptsKey y), encPairs ptsKey Lo]).wt := rfl
    rw [e1] at hc
    have h1 : Lo.length * (100000 * W ^ 2) ≤ (W + 1) * (100000 * (W + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
    have h2 : loopModK * (Lo.length + 1) * ((Val.list [natList (ptsKey y), encPairs ptsKey Lo]).wt +
        2 * Lo.length + 3) ≤ loopModK * (W + 1) * (3 * (W + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e2 : (W + 1) * (100000 * (W + 1) ^ 2) + loopModK * (W + 1) * (3 * (W + 1)) ≤
        10 ^ 6 * (W + 1) ^ 3 := by
      simp only [loopModK]; nlinarith
    have h5 := cp_poly_le (W := W) (K := 10 ^ 6) (d := 3) (by norm_num) (by norm_num) hW1
    have := cpG_poly hst hpre hm (W := W)
    omega

/-- **The stabilizer of the label points, within the budget.** -/
theorem cm_bud_stab (hjp : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    {ps : List (Perm (Fin k) × Perm (Fin q))} (hpl : ps.length ≤ (k + q) ^ 2)
    {X : List (Fin (k + q))} (hX : X.length ≤ q) (hW : 10 ^ 10 * (k + q + 1) ^ 12 ≤ W) :
    CpFB Pg (cmStab b) (.list [.list [.nat k, .nat q], .list (ps.map pairV), natList (ptsKey X)])
      W (cpG hst hpre hm W)
      (fun w => ∃ qs : List (Perm (Fin k) × Perm (Fin q)), w = .list (qs.map pairV) ∧
        qs.length ≤ (k + q) ^ 2 ∧
        Subgroup.closure {p | p ∈ qs} = Subgroup.closure {p | p ∈ ps} ⊓ fixPts k q X) := by
  have h := graphStabP_spec hst hsa.stab hjp ps X
  rw [encPts_eq_natList] at h
  obtain ⟨f1, f2, -, f24, f46, -, -, -, f9, -⟩ := cp_pow_facts k q
  have w6 : (k + q + 1) ^ 6 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  refine FunAll.mono h ?_
  rintro w cw ⟨qs, rfl, hl, hcl, hc⟩
  refine ⟨⟨qs, rfl, hl, hcl⟩, ?_, ?_⟩
  · have := cp_wt_gp (k := k) (q := q) hl
    unfold gpV at this
    omega
  · have h1 := stabBound_le hst ps X 0 0
    rw [encPts_eq_natList] at h1
    set M := imgM k q ps X 0 0 with hM
    have hMW : 2 * M ≤ W := by
      have : M ≤ 21 * (k + q + 1) ^ 2 := by rw [hM]; unfold imgM; omega
      omega
    have h4 : (2 * M) ^ 4 ≤ W ^ 4 := Nat.pow_le_pow_left hMW 4
    have e4 : (2 * M) ^ 4 = 16 * M ^ 4 := by ring
    have h2 := boundSize_mono (pointwiseStabPrim hst) (B := 200 * M ^ 4) (B' := 100 * W ^ 4)
      (by omega)
    have hs : stabPM k q ps X ≤ W + 1 := by unfold stabPM; omega
    have h3 : graphStabK * stabPM k q ps X ^ 8 ≤ graphStabK * (W + 1) ^ 8 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 8)
    have h5 := cp_poly_le (W := W) (K := graphStabK) (d := 8) (by simp [graphStabK])
      (by norm_num) (by omega)
    unfold cpG
    omega

/-- **The identity on positions, within the budget.** -/
theorem cm_bud_rng (hW : 100 * (k + 1) ^ 2 ≤ W) :
    CpFB Pg (cmRng b) (.nat k) W (cpG hst hpre hm W)
      (fun w => w = encPerm (1 : Perm (Fin k))) := by
  have hw := wt_encPerm_le (1 : Perm (Fin k))
  refine FunAll.mono (range_spec hsa.rng k) fun w c ⟨hw', hc⟩ => ?_
  rw [← cm_encPerm_one] at hw'
  subst hw'
  refine ⟨rfl, by omega, ?_⟩
  have hk := wt_nat_le k
  have hW1 : 1 ≤ W := by have := Nat.one_le_pow 2 (k + 1) (by omega); omega
  have h1 : loopModK * (k + 1) * ((Val.nat k).wt + k + (encPerm (1 : Perm (Fin k))).wt + 1) ≤
      loopModK * (W + 1) * (3 * (W + 1)) := by
    have : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e : loopModK * (W + 1) * (3 * (W + 1)) = 3000 * (W + 1) ^ 2 := by simp only [loopModK]; ring
  have h5 := cp_poly_le (W := W) (K := 3000) (d := 2) (by norm_num) (by norm_num) hW1
  have := cpG_poly hst hpre hm (W := W)
  omega

/-- **The first part of a pair, within the budget.** -/
theorem cm_bud_gat (p : Perm (Fin k) × Perm (Fin q)) (hW : 100 * (k + q + 1) ^ 6 ≤ W) :
    CpFB Pg (cmGat b) (.list [encPerm (encPair p), encPerm (1 : Perm (Fin k))]) W
      (cpG hst hpre hm W) (fun w => w = encPerm p.1) := by
  have h := gatherLeft_spec hsa.gat p.1 p.2
  rw [← encPair_eq] at h
  obtain ⟨f1, f2, f3, f24, f46, -, -, -, -, -⟩ := cp_pow_facts k q
  have hw := wt_encPerm_le p.1
  have hW1 : 1 ≤ W := by have := Nat.one_le_pow 6 (k + q + 1) (by omega); omega
  refine CpFB.det h ?_ (by omega) rfl
  have h1 : gatherK * (40 * (k + q + 1) ^ 2) ^ 3 = gatherK * 64000 * (k + q + 1) ^ 6 := by ring
  have h2 : (k + q + 1) ^ 6 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_left (by
    have : k + q + 1 ≤ (k + q + 1) ^ 6 := Nat.le_self_pow (by omega) _
    omega) 6
  have h5 := cp_poly_le (W := W) (K := gatherK * 64000) (d := 6) (by simp [gatherK])
    (by norm_num) hW1
  have h6 : gatherK * 64000 * (k + q + 1) ^ 6 ≤ gatherK * 64000 * (W + 1) ^ 6 :=
    Nat.mul_le_mul_left _ h2
  have := cpG_poly hst hpre hm (W := W)
  rw [h1]
  exact h6.trans (h5.trans this)

end Bud

end GI.Impl
