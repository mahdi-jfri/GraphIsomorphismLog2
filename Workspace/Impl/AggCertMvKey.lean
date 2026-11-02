import Workspace.Impl.AggCertMvReps


/-!
# The move program: helpers of the first window call

Budget forms of the modules that the first window call of a round uses (`cp_bud_kstab`,
`cp_bud_pEnc`, `cp_bud_mkG`, `cp_bud_find`, `cp_bud_kr`), and the cache key read from the
program state (`cp_key_eb`). They are used in `AggCertMvStart.lean`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)
open GI.Machine (BinOp)

section Bud

variable (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) {W : ℕ} {Pg : Program}

/-- **The kernel in graph form, within the budget.** -/
theorem cp_bud_kstab {k : ℕ} {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} [Fintype S.dom]
    {L : GiantLabels S} {πd : S.domGroup →* alternatingGroup (Fin L.q)} {b jp : ℕ}
    (hb : Pg.HasAt b (graphStabFuns b jp)) (hj : Pg.prims[jp]? = some (pointwiseStabPrim hst))
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g)
    {T : Finset (Fin L.q)} {A : Subgroup (Perm S.dom)} (hA : A ≤ Pgrp S.domGroup πd T)
    {ps : GPairs k L.q} (hps : PairGens e L (S.liftGroup A) ps)
    (hpl : ps.length ≤ (k + L.q) ^ 2) (hW : 10 ^ 10 * (k + L.q + 1) ^ 12 ≤ W) :
    CpFB Pg b (.list [.list [.nat k, .nat L.q], gpV ps, natList (ptsKey (labPts k (tlist T)))]) W
      (cpG hst hpre hm W)
      (fun w => ∃ ns : GPairs k L.q, w = gpV ns ∧ ns.length ≤ (k + L.q) ^ 2 ∧
        PairGens e L (S.liftGroup (kernelIn (phiT S.domGroup πd T) A)) ns) := by
  have h := graphStabP_spec hst hb hj ps (labPts k (tlist T))
  rw [encPts_eq_natList] at h
  obtain ⟨f1, f2, -, f24, f46, -, -, -, f9, -⟩ := cp_pow_facts k L.q
  have w6 : (k + L.q + 1) ^ 6 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hX : (labPts k (tlist T)).length ≤ L.q := by
    rw [labPts, List.length_map, length_tlist]
    exact (Finset.card_le_univ _).trans (by simp)
  refine FunAll.mono h ?_
  rintro w cw ⟨ns, rfl, hl, hcl, hc⟩
  refine ⟨⟨ns, rfl, hl, pairGens_kernelIn πd hπ hA hps hcl⟩, ?_, ?_⟩
  · have := cp_wt_gp (k := k) (q := L.q) hl
    unfold gpV at this
    omega
  · have h1 := stabBound_le hst ps (labPts k (tlist T)) 0 0
    rw [encPts_eq_natList] at h1
    set M := imgM k L.q ps (labPts k (tlist T)) 0 0 with hM
    have hMW : 2 * M ≤ W := by
      have : M ≤ 21 * (k + L.q + 1) ^ 2 := by rw [hM]; unfold imgM; omega
      omega
    have h4 : (2 * M) ^ 4 ≤ W ^ 4 := Nat.pow_le_pow_left hMW 4
    have e4 : (2 * M) ^ 4 = 16 * M ^ 4 := by ring
    have h2 := boundSize_mono (pointwiseStabPrim hst) (B := 200 * M ^ 4) (B' := 100 * W ^ 4)
      (by omega)
    have hs : stabPM k L.q ps (labPts k (tlist T)) ≤ W + 1 := by unfold stabPM; omega
    have h3 : graphStabK * stabPM k L.q ps (labPts k (tlist T)) ^ 8 ≤ graphStabK * (W + 1) ^ 8 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 8)
    have h5 := cp_poly_le (W := W) (K := graphStabK) (d := 8) (by simp [graphStabK])
      (by norm_num) (by omega)
    unfold cpG
    omega

/-- **Encoding a graph form, within the budget.** -/
theorem cp_bud_pEnc {k q b : ℕ} (hb : Pg.HasAt b (pEncMapFuns b)) {ps : GPairs k q}
    (hpl : ps.length ≤ (k + q) ^ 2) (hW : 10 ^ 10 * (k + q + 1) ^ 12 ≤ W)
    (hwa : (Val.list [.nat k, gpV ps]).wt ≤ W) :
    CpFB Pg b (.list [.nat k, gpV ps]) W (cpG hst hpre hm W)
      (fun w => w = .list ((ps.map encPair).map encPerm)) := by
  obtain ⟨f1, f2, -, f24, f46, e4, -, -, f9, -⟩ := cp_pow_facts k q
  have w12 : (k + q + 1) ^ 4 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have w3 : (k + q + 1) ^ 3 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hmap : (ps.map fun p => encPerm (encPair p)) = (ps.map encPair).map encPerm := by
    simp [List.map_map, Function.comp_def]
  have h := pEncMap_spec hb ps
  rw [hmap] at h
  have hout : (Val.list ((ps.map encPair).map encPerm)).wt ≤ 9 * (k + q + 1) ^ 4 + 4 := by
    have := cp_wt_list (vs := (ps.map encPair).map encPerm) (n := (k + q + 1) ^ 2)
      (c := 4 * (k + q + 1) ^ 2) (by simp only [List.length_map]; omega) (by
        intro v hv
        obtain ⟨g, -, rfl⟩ := List.mem_map.1 hv
        exact wt_encPerm_le g)
    have : (k + q + 1) ^ 2 * (2 * (4 * (k + q + 1) ^ 2) + 1) ≤ 9 * (k + q + 1) ^ 4 := by
      rw [← e4]; nlinarith
    omega
  refine CpFB.det h ?_ (by omega) rfl
  have c1 : ps.length * pEncCost k q ≤ W * (natStepK * W) := by
    unfold pEncCost
    exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))
  have c2 : mapK * (ps.length + 1) * ((Val.list [.nat k, .list (ps.map pairV)]).wt +
      (Val.list ((ps.map encPair).map encPerm)).wt + 1) ≤ 1000 * (W + 1) * (3 * W + 3) := by
    have hm' : mapK = 1000 := rfl
    have : (Val.list [.nat k, .list (ps.map pairV)]).wt ≤ W := hwa
    rw [hm']
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e5 : W * (natStepK * W) + 1000 * (W + 1) * (3 * W + 3) ≤ 10 ^ 10 * (W + 1) ^ 2 := by
    simp only [natStepK]; nlinarith
  have hp := cp_poly_le (W := W) (K := 10 ^ 10) (d := 2) (by norm_num) (by norm_num) (by omega)
  have := cpG_poly hst hpre hm (W := W)
  omega

/-- **A group value from encoded pairs, within the budget.** -/
theorem cp_bud_mkG {k q b : ℕ} (hb : Pg.HasAt b (mkGroupFuns b)) {ps : GPairs k q}
    (hpl : ps.length ≤ (k + q) ^ 2) (hW : 10 ^ 10 * (k + q + 1) ^ 12 ≤ W) :
    CpFB Pg b (.list [.nat (k + q), .list ((ps.map encPair).map encPerm)]) W (cpG hst hpre hm W)
      (fun w => w = encGroup (ps.map encPair)) := by
  obtain ⟨f1, f2, -, f24, f46, e4, -, -, f9, -⟩ := cp_pow_facts k q
  have w6 : (k + q + 1) ^ 6 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have w3 : (k + q + 1) ^ 3 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  refine CpFB.det (mkGroup_spec hb (ps.map encPair)) ?_ ?_ rfl
  · have hl : ((ps.map encPair).length + 2) * (k + q + 1) ≤ W := by
      rw [List.length_map]
      have : (ps.length + 2) * (k + q + 1) ≤ 3 * (k + q + 1) ^ 2 * (k + q + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have : 3 * (k + q + 1) ^ 2 * (k + q + 1) = 3 * (k + q + 1) ^ 3 := by ring
      omega
    have h3 : mkGroupK * (((ps.map encPair).length + 2) * (k + q + 1)) ^ 3 ≤
        mkGroupK * (W + 1) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
    have hp := cp_poly_le (W := W) (K := mkGroupK) (d := 3) (by simp [mkGroupK]) (by norm_num)
      (by omega)
    have := cpG_poly hst hpre hm (W := W)
    omega
  · have := cp_wt_encGroupPairs (k := k) (q := q) hpl
    omega

/-- **The cache lookup, within the budget.** -/
theorem cp_bud_find {k q b jm : ℕ} (hb : Pg.HasAt b (ckFindFuns b jm))
    (hj : Pg.prims[jm]? = some (membershipPrim hm)) (ps ns : GPairs k q)
    (c : List (CacheEntry k q)) (hwa : (Val.list [ckKeyV ps ns, .list (c.map ckEntV)]).wt ≤ W) :
    CpFB Pg b (.list [ckKeyV ps ns, .list (c.map ckEntV)]) W (cpG hst hpre hm W)
      (fun w => w = .nat (c.findIdx (ckTest ps ns))) := by
  refine CpFB.det (ckFind_spec hm hb hj ps ns c hwa) (cpG_find hst hpre hm) ?_ rfl
  have h1 : c.findIdx (ckTest ps ns) ≤ c.length := List.findIdx_le_length
  have h2 := length_lt_wt_list (c.map ckEntV)
  have h3 : (Val.list (c.map ckEntV)).wt < (Val.list [ckKeyV ps ns, .list (c.map ckEntV)]).wt :=
    wt_le_wt_list (by simp)
  have := wt_nat_le (c.findIdx (ckTest ps ns))
  simp only [List.length_map] at h2
  omega

/-- **The window group, within the budget.** -/
theorem cp_bud_kr {k q b jp : ℕ} (hb : Pg.HasAt b (krFuns b jp))
    (hj : Pg.prims[jp]? = some (pointwiseStabPrim hst)) {ns : GPairs k q}
    (hnl : ns.length ≤ (k + q) ^ 2) (hW : 10 ^ 10 * (k + q + 1) ^ 12 ≤ W) :
    CpFB Pg b (.list [.nat k, gpV ns]) W (cpG hst hpre hm W)
      (fun w => ∃ hs : List (Perm (Fin k)), w = encGroup hs ∧ gens hs = gens (ns.map Prod.fst) ∧
        hs.length ≤ k ^ 2) := by
  obtain ⟨f1, f2, -, f24, f46, e4, -, -, f9, f66⟩ := cp_pow_facts k q
  have w6 : (k + q + 1) ^ 6 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  refine FunAll.mono (kr_spec hst hb hj ns) ?_
  rintro w cw ⟨hs, rfl, hg, hl, hc⟩
  refine ⟨⟨hs, rfl, hg, hl⟩, ?_, ?_⟩
  · have := wt_encGroup_le_sq hl
    omega
  · have hM : pM k q ns ≤ W := by unfold pM; omega
    have h4 : (pM k q ns) ^ 4 ≤ W ^ 4 := Nat.pow_le_pow_left hM 4
    have h2 := boundSize_mono (pointwiseStabPrim hst) (B := 100 * pM k q ns ^ 4)
      (B' := 100 * W ^ 4) (by omega)
    have h3 : krK * pM k q ns ^ 9 ≤ krK * (W + 1) ^ 9 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 9)
    have h5 := cp_poly_le (W := W) (K := krK) (d := 9) (by simp [krK]) (by norm_num) (by omega)
    unfold cpG
    omega

end Bud

section Help

variable {P : Program} {env : List Val} {W : ℕ}

theorem CpFB.toDet {f : ℕ} {v w : Val} {C : ℕ} (h : CpFB P f v W C (fun x => x = w)) :
    FunDet P f v w C :=
  FunAll.mono h fun _ _ h => ⟨h.1, h.2.2⟩

/-- A representative list of the cosets of `N` in `A` is not empty. -/
theorem cp_reps_ne_nil {V : Type} {AN : Subgroup (Perm V) × Subgroup (Perm V)}
    {l : List (Perm V)} (h : RepsOK AN l) : l ≠ [] := by
  rintro rfl
  have := h.2.1 (show (1 : Perm V) ∈ (AN.1 : Set (Perm V)) from AN.1.one_mem)
  simp at this

end Help

section Key

variable (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) {W : ℕ} {Pg : Program}

set_option maxHeartbeats 2000000 in
/-- **The cache key**, read from the program state: the group values of the graph form `ps` of
the stage (entry 8 of `kst`) and of the kernel pairs `ns` (variable 1). -/
theorem cp_key_eb {b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm) {env : List Val}
    {ks : List Val} {x : Val} (h0 : env[0]? = some (.list [.list ks, x]))
    (hw : (Val.list [.list ks, x]).wt ≤ W) {pl sl : List Val} (hp : ks[0]? = some (.list pl))
    (hs : pl[0]? = some (.list sl)) {k q : ℕ} (hk : sl[0]? = some (.nat k))
    (hkq : pl[7]? = some (.nat (k + q))) {ps ns : GPairs k q} (h8 : ks[8]? = some (gpV ps))
    (h1 : env[1]? = some (gpV ns)) (hpl : ps.length ≤ (k + q) ^ 2)
    (hnl : ns.length ≤ (k + q) ^ 2) (hW : 10 ^ 10 * (k + q + 1) ^ 12 ≤ W) :
    CpEB Pg env (cpKeyE b) W (4 * cpG hst hpre hm W + 100 * (W + 20))
      (fun v => v = ckKeyV ps ns) := by
  obtain ⟨f1, f2, f3, f24, f46, e4, e6, f8, f9, f66⟩ := cp_pow_facts k q
  have hk12 : k + q + 1 ≤ (k + q + 1) ^ 12 := Nat.le_self_pow (by omega) _
  have w612 : (k + q + 1) ^ 6 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have w4 : (k + q + 1) ^ 4 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hpsW := cp_wt_gp hpl
  have hnsW := cp_wt_gp hnl
  have hnW : (gpV ns).wt ≤ W := by omega
  have hkV := wt_nat_le k
  have hpA : (Val.list [.nat k, gpV ps]).wt ≤ W := by
    have := wt_list2_le (.nat k) (gpV ps); omega
  have hnA : (Val.list [.nat k, gpV ns]).wt ≤ W := by
    have := wt_list2_le (.nat k) (gpV ns); omega
  have hencW : ∀ qs : GPairs k q, qs.length ≤ (k + q) ^ 2 →
      (Val.list ((qs.map encPair).map encPerm)).wt ≤ 9 * (k + q + 1) ^ 4 + 4 := by
    intro qs hq
    have := cp_wt_list (vs := (qs.map encPair).map encPerm) (n := (k + q + 1) ^ 2)
      (c := 4 * (k + q + 1) ^ 2) (by simp only [List.length_map]; omega) (by
        intro v hv
        obtain ⟨g, -, rfl⟩ := List.mem_map.1 hv
        exact wt_encPerm_le g)
    have : (k + q + 1) ^ 2 * (2 * (4 * (k + q + 1) ^ 2) + 1) ≤ 9 * (k + q + 1) ^ 4 := by
      rw [← e4]; nlinarith
    omega
  have hgW1 := cp_wt_encGroupPairs (k := k) (q := q) hpl
  have hgW2 := cp_wt_encGroupPairs (k := k) (q := q) hnl
  have he1 := hencW ps hpl
  have he2 := hencW ns hnl
  have hkeyW : (ckKeyV ps ns).wt ≤ 1500 * (k + q + 1) ^ 6 := by
    have := wt_list2_le (encGroup (ps.map encPair)) (encGroup (ns.map encPair))
    unfold ckKeyV; omega
  have hkqV : (Val.nat (k + q)).wt ≤ k + q + 2 := wt_nat_le _
  have hm1 := wt_list2_le (.nat (k + q)) (.list ((ps.map encPair).map encPerm))
  have hm2 := wt_list2_le (.nat (k + q)) (.list ((ns.map encPair).map encPerm))
  have hksW : (Val.list ks).wt < W :=
    lt_of_lt_of_le (cp_wt_get (vs := [.list ks, x]) (j := 0) rfl) hw
  have hplW := (cp_wt_get hp).trans hksW
  have hslW := (cp_wt_get hs).trans hplW
  have dk : Det Pg env (cpSf 0) (.nat k) (5 * (W + 20)) :=
    Det.rd (cp_rdP h0 hw hp hs (by omega)) le_rfl hk ((cp_wt_get hk).trans hslW).le (by omega)
  have dq := cp_rdP (P := Pg) h0 hw hp hkq (by omega)
  have d8 := cp_rdK (P := Pg) h0 hw h8 (by omega)
  have d1 := Det.call (Det.mk2 dk d8) (cp_bud_pEnc hst hpre hm hat.pEnc hpl hW hpA).toDet
  have dM1 := Det.call (Det.mk2 dq d1) (cp_bud_mkG hst hpre hm hat.mkG hpl hW).toDet
  have d2 := Det.call (Det.mk2 dk (Det.rv (P := Pg) h1 hnW))
    (cp_bud_pEnc hst hpre hm hat.pEnc hnl hW hnA).toDet
  have dM2 := Det.call (Det.mk2 dq d2) (cp_bud_mkG hst hpre hm hat.mkG hnl hW).toDet
  have hkw : (Val.list [encGroup (ps.map encPair), encGroup (ns.map encPair)]).wt ≤
    1500 * (k + q + 1) ^ 6 := hkeyW
  refine CpEB.det (Det.mk2 dM1 dM2) ?_ (by omega) rfl
  have := wt_list2_le (.nat k) (gpV ps)
  have := wt_list2_le (.nat k) (gpV ns)
  omega

end Key

end GI.Impl
