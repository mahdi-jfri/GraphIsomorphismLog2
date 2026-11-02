import Workspace.Impl.AggCertMvInd

/-!
# The move program: the end of a round

After the window call of the last representative, `cpCloseF` (at `b + 10`) closes the round.

* The closure module (`clos_spec`, one **Preimage** call) turns the graph form of `G` and the
  generators collected from the answers into the graph form of the next group `A_{t+1}`. Its
  precondition asks that each generator be the position form of an element of `G`; this holds
  because the answers lie in `G` (`cp_stage_mem_G`, `cp_hms`).
* A filter with the test `cpDiffTestF` (at `b + 8`) keeps the outside points that are not in
  the increment (`cp_bud_filt`).
* The new program state is that of `CpSt.close`, and `cp_answer_close` says what it stands for.

`cp_close_spec` is the result used later.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)
open GI.Machine (BinOp)
open scoped Pointwise

section Gens

variable {k : ℕ} {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- **The generators of the new stage come from `G`.** -/
theorem cp_stage_mem_G
    {dn : List (Perm (Fin k) × Option (Perm (Fin k) × List (Perm (Fin k))))}
    (B : Perm (Fin k) × Option (Perm (Fin k) × List (Perm (Fin k))) → Set (Perm Ω))
    (hG : ∀ i ∈ dn, (toFin e).symm i.1 ∈ S.G) (ho : ∀ i ∈ dn, AnsSet e i.2 (B i))
    (hB : ∀ i ∈ dn, B i ⊆ S.G) {m : Perm (Fin k)} (hm : m ∈ stageGens dn) :
    ∃ g ∈ S.G, toFin e g = m := by
  obtain ⟨i, hi, hmi⟩ := mem_stageGens.mp hm
  have h1 : m ∈ gens (ansGens i.1 i.2) := Subgroup.subset_closure hmi
  rw [closure_ansGens e i.1 i.2 (B i) (ho i hi)] at h1
  have h2 : Subgroup.closure (toFin e '' ((toFin e).symm i.1 • B i)) ≤
      S.G.map (toFin e).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨_, S.G.mul_mem (hG i hi) (hB i hi hb), rfl⟩
  obtain ⟨g, hg, hgm⟩ := h2 h1
  exact ⟨g, hg, hgm⟩

/-- **The precondition of the closure module**, for a position form of an element of `G`. -/
theorem cp_hms {gp : List (Perm (Fin k) × Perm (Fin L.q))} (hgp : PairGens e L S.G gp)
    {m : Perm (Fin k)} (hm : ∃ g ∈ S.G, toFin e g = m) :
    ∃ p ∈ Subgroup.closure {p | p ∈ gp.map Prod.swap}, MonoidHom.snd _ _ p = m := by
  obtain ⟨g, hg, rfl⟩ := hm
  set p0 : Perm (Fin k) × Perm (Fin L.q) :=
    (toFin e g, ((L.π ⟨g, hg⟩ : alternatingGroup (Fin L.q)) : Perm (Fin L.q)))
  have hp0 : p0 ∈ Subgroup.closure {p | p ∈ gp} := by
    rw [hgp, mem_graphOf]
    exact ⟨g, hg, hg, rfl, rfl⟩
  refine ⟨p0.swap, (clMem_closure_swap gp p0.swap).mpr (by simpa using hp0), rfl⟩

end Gens

section Prog

variable {k : ℕ} {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {q : ℕ}
  (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

/-- The test of the filter, on `[incP, x]`: whether the position `x` is not in `incP`. -/
theorem cp_diffTest {Pg : Program} {b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    {l : List S.dom} (hl : l.length ≤ k) {x : ℕ} (hx : x ≤ k + q) :
    FunDet Pg (b + 8) (.list [natList (cpPosN e q l), .nat x])
      (boolVal (decide ((cpPosN e q l).count x = 0)))
      (100 * (k + q + 1) ^ 2 + countK * (k + q + 1) ^ 3 + 200) := by
  refine FunDet.intro hat.diffTest ?_
  unfold cpDiffTestF
  have hc := count_spec hat.cnt (xs := cpPosN e q l) (j := x) (B := k + q) cp_posN_le hx
    (by rw [cp_posN_length]; omega)
  have hz : BinOp.eq.eval ((cpPosN e q l).count x) 0 =
      (decide ((cpPosN e q l).count x = 0)).toNat := by
    simp only [BinOp.eval]; split_ifs with h <;> simp [h]
  refine (Det.arith' (Det.call (Det.mk2 (Det.arg' (rest := []) (j := 1) rfl)
    (Det.arg' (rest := []) (j := 0) rfl)) hc) (Det.nat 0) hz).mono ?_
  have hPl : (cpPosN e q l).length ≤ k := by rw [cp_posN_length]; exact hl
  have hPw : (natList (cpPosN e q l)).wt ≤ k * (2 * (k + q) + 5) + 4 := by
    have := wt_natList_le (B := k + q) (xs := cpPosN e q l) cp_posN_le
    have := Nat.mul_le_mul_right (2 * (k + q) + 5) hPl
    omega
  have hsq : k * (2 * (k + q) + 5) ≤ 5 * (k + q + 1) ^ 2 := by
    have : k * (2 * (k + q) + 5) ≤ (k + q + 1) * (5 * (k + q + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e1 : (k + q + 1) * (5 * (k + q + 1)) = 5 * (k + q + 1) ^ 2 := by ring
    omega
  have := wt_list2_le (natList (cpPosN e q l)) (.nat x)
  have := wt_list2_le (.nat x) (natList (cpPosN e q l))
  have := wt_nat_le x
  have := wt_nat_le ((cpPosN e q l).count x)
  have : (cpPosN e q l).count x ≤ k := List.count_le_length.trans hPl
  have : (decide ((cpPosN e q l).count x = 0)).toNat ≤ 1 := by
    cases decide ((cpPosN e q l).count x = 0) <;> simp
  have : k + q + 1 ≤ (k + q + 1) ^ 2 := Nat.le_self_pow (by omega) _
  omega

/-- **The outside points of the next window**, within the budget. -/
theorem cp_bud_filt {Pg : Program} {b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    {incl os : List S.dom} (hl : incl.length ≤ k) (hos : os.length ≤ k) {W : ℕ}
    (hW : 10 ^ 10 * (k + q + 1) ^ 12 ≤ W) :
    CpFB Pg (cpFilt b) (.list [natList (cpPosN e q incl), encPts (os.map (domPos e q))]) W
      (cpG hst hpre hm W)
      (fun w => w = encPts ((os.filter fun v =>
        decide ((cpPosN e q incl).count (domPos e q v : ℕ) = 0)).map (domPos e q))) := by
  set P := cpPosN e q incl with hP
  set p : S.dom → Bool := fun v => decide (P.count (domPos e q v : ℕ) = 0) with hp
  set tst : Val → Bool := fun x => match x with
    | .nat i => decide (P.count i = 0)
    | _ => false with htst
  rw [encPts_map_posOf, encPts_map_posOf]
  have hxs : ∀ x ∈ os.map (fun v => Val.nat (domPos e q v : ℕ)),
      FunDet Pg (b + 8) (.list [natList P, x]) (boolVal (tst x))
        (100 * (k + q + 1) ^ 2 + countK * (k + q + 1) ^ 3 + 200) := by
    intro x hx
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
    exact cp_diffTest hat hl (domPos e q v).isLt.le
  have hf := filter_spec hat.filt hxs
  have hout : (os.map fun v => Val.nat (domPos e q v : ℕ)).filter tst =
      (os.filter p).map fun v => Val.nat (domPos e q v : ℕ) := by
    rw [List.filter_map]; rfl
  have hos' : (os.filter p).length ≤ k := (List.filter_sublist).length_le.trans hos
  have hwo := cp_wt_pts (q := q) (X := (os.filter p).map (domPos e q))
    (by rw [List.length_map]; exact hos')
  have hwi := cp_wt_pts (q := q) (X := os.map (domPos e q)) (by rw [List.length_map]; exact hos)
  rw [encPts_map_posOf] at hwo hwi
  have hPl : P.length ≤ k := by rw [hP, cp_posN_length]; exact hl
  have hPw : (natList P).wt ≤ k * (2 * (k + q) + 5) + 4 := by
    have := wt_natList_le (B := k + q) (xs := P) cp_posN_le
    have := Nat.mul_le_mul_right (2 * (k + q) + 5) hPl
    omega
  have hsq : k * (2 * (k + q) + 5) ≤ 5 * (k + q + 1) ^ 2 := by
    have : k * (2 * (k + q) + 5) ≤ (k + q + 1) * (5 * (k + q + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e1 : (k + q + 1) * (5 * (k + q + 1)) = 5 * (k + q + 1) ^ 2 := by ring
    omega
  have hk2 : (k + q + 1) ^ 2 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hk3 : (k + q + 1) ^ 3 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hk1 : k + q + 1 ≤ (k + q + 1) ^ 12 := Nat.le_self_pow (by omega) _
  refine FunAll.mono hf fun w c hw => ?_
  obtain ⟨rfl, hc⟩ := hw
  rw [hout] at hc ⊢
  refine ⟨rfl, by omega, ?_⟩
  -- the cost
  have hA := wt_list2_le (natList P) (.list (os.map fun v => Val.nat (domPos e q v : ℕ)))
  have hsum : ((os.map fun v => Val.nat (domPos e q v : ℕ)).map
      fun _ => 100 * (k + q + 1) ^ 2 + countK * (k + q + 1) ^ 3 + 200).sum ≤
      k * (100 * (k + q + 1) ^ 12 + countK * (k + q + 1) ^ 12 + 200) := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map]
    exact Nat.mul_le_mul hos (by
      have := Nat.mul_le_mul_left countK hk3
      omega)
  have hlen : (os.map fun v => Val.nat (domPos e q v : ℕ)).length ≤ k := by
    rw [List.length_map]; exact hos
  have hC1 : countK = 100000 := rfl
  have hL1 : loopModK = 1000 := rfl
  rw [hC1] at hsum hc
  rw [hL1] at hc
  have h1 : k * (100 * (k + q + 1) ^ 12 + 100000 * (k + q + 1) ^ 12 + 200) ≤
      (W + 1) * (100100 * (W + 1) + 200) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : 1000 * ((os.map fun v => Val.nat (domPos e q v : ℕ)).length + 1) *
      ((Val.list [natList P, .list (os.map fun v => Val.nat (domPos e q v : ℕ))]).wt +
        (os.map fun v => Val.nat (domPos e q v : ℕ)).length +
        (Val.list ((os.filter p).map fun v => Val.nat (domPos e q v : ℕ))).wt + 1) ≤
      1000 * (W + 1) * (W + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e2 : (W + 1) * (100100 * (W + 1) + 200) = 100100 * (W + 1) ^ 2 + 200 * (W + 1) := by ring
  have e3 : 1000 * (W + 1) * (W + 1) = 1000 * (W + 1) ^ 2 := by ring
  have hp2 := cp_poly_le (W := W) (K := 102000) (d := 2) (by norm_num) (by norm_num) (by omega)
  have : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have := cpG_poly hst hpre hm (W := W)
  omega

theorem cp_filt_mem {incl os : List S.dom} (v : S.dom) :
    v ∈ os.filter (fun v => decide ((cpPosN e q incl).count (domPos e q v : ℕ) = 0)) ↔
      v ∈ os ∧ v ∉ incl := by
  rw [List.mem_filter, decide_eq_true_iff, List.count_eq_zero, mem_cpPosN_iff]

/-- **The closure module, within the budget.** -/
theorem cp_bud_clos {Pg : Program} {b jpre : ℕ} (hb : Pg.HasAt b (closFuns b jpre))
    (hj : Pg.prims[jpre]? = some (preimagePrim hpre)) (gp : List (Perm (Fin k) × Perm (Fin q)))
    (ms : List (Perm (Fin k)))
    (hms : ∀ m ∈ ms, ∃ p ∈ Subgroup.closure {p | p ∈ gp.map Prod.swap},
      MonoidHom.snd _ _ p = m) {W : ℕ}
    (hM : k + q + gp.length + ms.length + 2 ≤ W) (hW : 10 ^ 10 * (k + q + 1) ^ 12 ≤ W) :
    CpFB Pg b (.list [.list [.nat k, .nat q], .list (gp.map pairV), .list (ms.map encPerm)]) W
      (cpG hst hpre hm W) (fun w => ∃ qs : List (Perm (Fin k) × Perm (Fin q)),
        w = .list (qs.map pairV) ∧ qs.length ≤ (k + q) ^ 2 ∧
        Subgroup.closure {p | p ∈ qs} =
          Subgroup.closure {p | p ∈ gp} ⊓ (gens ms).comap (MonoidHom.fst _ _)) := by
  refine FunAll.mono (clos_spec hpre hb hj gp ms hms) ?_
  rintro w c ⟨qs, rfl, hl, hq, hc⟩
  refine ⟨⟨qs, rfl, hl, hq⟩, ?_, ?_⟩
  · have := cp_wt_gp (k := k) (q := q) hl
    have : (k + q + 1) ^ 4 ≤ (k + q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
    unfold gpV at *
    omega
  · have hpM : preM q k (gp.map Prod.swap) ms ≤ W := by
      unfold preM; rw [List.length_map]; omega
    have hpw := lcPreEnc_wt (gp.map Prod.swap) ms hms
    have hsz := (GI.Lang.preimageEnc (pairInst (MonoidHom.snd _ _) (gp.map Prod.swap) ms
      hms)).size_le_wt
    have h4 : 1000 * preM q k (gp.map Prod.swap) ms ^ 4 ≤ 1000 * W ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpM 4)
    have hb1 := (preimagePrim hpre).bound_le (v := GI.Lang.preimageEnc (pairInst
      (MonoidHom.snd _ _) (gp.map Prod.swap) ms hms)) (B := 1000 * W ^ 4) (by omega)
    have h8 : 2 * graphPreK * preM q k (gp.map Prod.swap) ms ^ 8 ≤ 2 * graphPreK * (W + 1) ^ 8 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 8)
    have hp := cp_poly_le (W := W) (K := 2 * graphPreK) (d := 8) (by simp [graphPreK])
      (by norm_num) (by
        have : 1 ≤ (k + q + 1) ^ 12 := Nat.one_le_pow _ _ (by omega)
        omega)
    have := cpG_pre4_poly hst hpre hm (W := W)
    omega

end Prog

end GI.Impl

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)
open GI.Machine (BinOp)

section Close

variable {k : ℕ} {Ω C : Type} [DecidableEq Ω] {e : Ω ≃ Fin k} {c : C → ℕ}
  {S : State Ω C} [Fintype S.dom] {L : GiantLabels S}
  {πd : S.domGroup →* alternatingGroup (Fin L.q)}
  (hst : PointwiseStab) (hpre : Preimage) (hm : Membership)

set_option maxHeartbeats 4000000 in
/-- **The end of a round.** On `[kst, gens']`, with `gens'` the generators of all the answers of
the round, `cpCloseF` returns the program state of the next round. -/
theorem cp_close_spec {Pg : Program} {b jp jpre jm : ℕ} (hat : CpMvAt Pg b jp jpre jm)
    (hjpre : Pg.prims[jpre]? = some (preimagePrim hpre))
    {sv : Val} {gp : GPairs k L.q} {osA : List (Fin (k + L.q))} {D : ℕ}
    (ctx : CpCtx e c S L πd sv gp osA D) {NT M₀ Bw W : ℕ}
    (hBw : cpBw k L.q (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)).wt NT M₀ D
      ≤ Bw) (hW : 10 ^ 4 * (Bw + 2) ^ 2 ≤ W)
    {m f : ℕ} {σ : CpSt k L.q} {acc : List (StagePair S)} {T : Finset (Fin L.q)}
    {rec : List ((Subgroup (Perm S.dom) × Subgroup (Perm S.dom)) × List (Perm S.dom))}
    {acc' : List (Set (Perm S.dom))} {u : Val}
    {dn : List (Perm (Fin k) × Option (Perm (Fin k) × List (Perm (Fin k))))} {a : Perm (Fin k)}
    {hs : List (Perm (Fin k))} {dv : Val} {incl : List S.dom}
    (hm' : m = cpMeas (Fintype.card S.dom) D (.win acc T σ.Ts σ.s σ.t [] acc')) (hmf : m ≤ f)
    (hM : σ.cache.length + m ≤ M₀) (hNT : σ.res.length + σ.Ts.length + 1 ≤ NT)
    (hlen : CpLen D σ) (hT : T = σ.T)
    (hWI : CpWinInv e πd σ acc T rec
      (cpInnerV [] (stageGens dn) hs dv (incl.map (domPos e L.q)) a) u [] acc')
    (hl : ((grp (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t,
      kernelIn (cpPhi S πd T) (grp (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t)),
      (dn.map Prod.fst ++ [a]).map (domOfPos e S)) ∈ rec)
    (hG : ∀ b ∈ dn.map Prod.fst ++ [a], (toFin e).symm b ∈ S.G)
    (ho : ∀ p ∈ dn, AnsSet e p.2 (cpCall πd T σ.s σ.t (domOfPos e S p.1)).answer)
    (hacc : acc' = cpAcc S (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t
      ((dn.map Prod.fst ++ [a]).map (domOfPos e S)))
    (hnd : incl.Nodup)
    (hinc : ∀ v, v ∈ incl ↔ v ∈ inc (cpPhi S πd T) (dstr S (cpZ S σ.s)) σ.t)
    {o : Option (Perm (Fin k) × List (Perm (Fin k)))}
    (hao : AnsSet e o (cpCall πd T σ.s σ.t (domOfPos e S a)).answer)
    (harg : (Val.list [σ.val (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA))
        (cpInnerV [] (stageGens dn) hs dv (incl.map (domPos e L.q)) a),
      .list ((stageGens (dn ++ [(a, o)])).map encPerm)]).wt ≤ 4 * Bw) :
    CpFB Pg (b + 10) (.list [σ.val (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA))
        (cpInnerV [] (stageGens dn) hs dv (incl.map (domPos e L.q)) a),
      .list ((stageGens (dn ++ [(a, o)])).map encPerm)]) W
      (2 * cpG hst hpre hm W + 800 * (W + 20))
      (CpMvPost e S L πd (cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA)) D Bw M₀
        NT m ((fun R => cpAt S πd (dstr S S.x) (dstr S S.y) R
          (.win acc T σ.Ts σ.s σ.t [] acc')) '' Cands rec) f) := by
  set par := cpParV k L.q (Fintype.card S.dom) D sv (gpV gp) (encPts osA) with hpar
  set inner := cpInnerV [] (stageGens dn) hs dv (incl.map (domPos e L.q)) a with hinner
  set gs' := stageGens (dn ++ [(a, o)]) with hgs'
  subst hT
  obtain ⟨hW1, hW2, hW3, hW4, hW5⟩ := cp_W_facts hBw hW
  have hk12 : k + L.q + 1 ≤ (k + L.q + 1) ^ 12 := Nat.le_self_pow (by omega) _
  have hkW : k + L.q + 1 ≤ W := by omega
  set ks := σ.vals par inner with hks
  have hsv : σ.val par inner = .list ks := rfl
  set gV : Val := .list (gs'.map encPerm) with hgV
  have hgVe : (Val.list (gs'.map encPerm)).wt = gV.wt := rfl
  have hwW : (Val.list [.list ks, gV]).wt ≤ W := by rw [← hsv]; omega
  have hksW : (Val.list ks).wt < W :=
    lt_of_lt_of_le (cp_wt_get (vs := [.list ks, gV]) (j := 0) rfl) hwW
  have hp0 : ks[0]? = some (.list [sv, .list [.nat k, .nat L.q], gpV gp,
    .nat (Fintype.card S.dom), .nat D, encPts osA, pSplitCtx k L.q, .nat (k + L.q)]) := rfl
  have hi0 : ks[10]? = some (.list [.list (([] : List (Perm (Fin k))).map encPerm),
    .list ((stageGens dn).map encPerm), encGroup hs, dv, encPts (incl.map (domPos e L.q)),
    encPerm a]) := rfl
  have hlen0 := hlen
  obtain ⟨hlt, hlo, hl0, hlx, hlp, hlr, hlc⟩ := hlen
  have hWI0 := hWI
  obtain ⟨hR, ht, -, -⟩ := hWI
  obtain ⟨os, hndo, hos, hosP⟩ := hR.os
  have hcard := cp_card_dom_le (S := S) e
  have hosl : os.length ≤ k := cp_os_length_le e hndo
  have hincl : incl.length ≤ k := cp_os_length_le e hnd
  have h0 : ∀ rest : List Val, (Val.list [.list ks, gV] :: rest)[0]? =
      some (.list [.list ks, gV]) := fun _ => rfl
  refine CpFB.intro hat.close ?_
  rw [hsv]
  unfold cpCloseF
  -- the generators come from `G`
  have hms : ∀ m ∈ gs', ∃ p ∈ Subgroup.closure {p | p ∈ gp.map Prod.swap},
      MonoidHom.snd _ _ p = m := by
    intro m hm
    refine cp_hms ctx.hgp (cp_stage_mem_G (S := S)
      (B := fun i => (cpCall πd σ.T σ.s σ.t (domOfPos e S i.1)).answer) ?_ ?_ ?_ hm)
    · intro i hi
      exact hG _ (by
        rcases List.mem_append.mp hi with hi | hi
        · exact List.mem_append_left _ (List.mem_map_of_mem hi)
        · rw [List.mem_singleton.mp hi]; exact List.mem_append_right _ (List.mem_singleton_self _))
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact ho i hi
      · rw [List.mem_singleton.mp hi]; exact hao
    · intro i _
      exact windowCall_answer_le S _ _ _
  -- the weights of the pieces
  have hgVw : gV.wt < W := (cp_wt_get (vs := [.list ks, gV]) (j := 1) rfl).trans_le hwW
  have hgl : gs'.length < W := by
    have := length_lt_wt_list (gs'.map encPerm)
    rw [List.length_map] at this
    omega
  have hgpl := ctx.hgpl
  have hgpw := cp_wt_gp hgpl
  have hk4 : (k + L.q + 1) ^ 4 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hk2' : (k + L.q) ^ 2 ≤ (k + L.q + 1) ^ 12 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hcW : (Val.list [.list [.nat k, .nat L.q], gpV gp, gV]).wt ≤ W := by
    have := wt_list3_le (.list [.nat k, .nat L.q]) (gpV gp) gV
    have := wt_list2_le (.nat k) (.nat L.q)
    have := wt_nat_le k; have := wt_nat_le L.q
    have : gV.wt < 4 * Bw + 1 := by
      have := cp_wt_get (vs := [.list ks, gV]) (j := 1) rfl
      have : (Val.list [Val.list ks, gV]).wt ≤ 4 * Bw := by rw [← hsv]; exact harg
      omega
    omega
  have hgV2 : gV.wt < 4 * Bw + 1 := by
    have := cp_wt_get (vs := [.list ks, gV]) (j := 1) rfl
    have : (Val.list [Val.list ks, gV]).wt ≤ 4 * Bw := by rw [← hsv]; exact harg
    omega
  have hglB : gs'.length < 4 * Bw + 1 := by
    have := length_lt_wt_list (gs'.map encPerm)
    rw [List.length_map] at this
    omega
  have dA := Det.mk3 (cp_rdP (P := Pg) (h0 []) hwW hp0 (j := 1) (v := .list [.nat k, .nat L.q])
    rfl (by omega)) (cp_rdP (P := Pg) (h0 []) hwW hp0 (j := 2) (v := gpV gp) rfl (by omega))
    (Det.rd (a := 1) (Det.rv (P := Pg) (env := [.list [.list ks, gV]]) (i := 0) rfl hwW) le_rfl
      (show [Val.list ks, gV][1]? = some gV from rfl) hgVw.le (by omega))
  have hbc := cp_bud_clos hst hpre hm hat.clos hjpre gp gs' hms (W := W) (by omega) hW2
  refine (CpEB.letE (CpEB.call (CpEB.det dA le_rfl hcW
      (Q := fun v => v = .list [.list [.nat k, .nat L.q], gpV gp, gV]) rfl)
    fun v hv _ => hv ▸ hbc) (Cb := cpG hst hpre hm W + 700 * (W + 20))
    fun qv hqv hqW => ?_).mono (by omega) fun _ h => h
  obtain ⟨qs, rfl, hqsl, hqs⟩ := hqv
  -- the filter
  have h1 : ∀ rest : List Val, (Val.list [.list ks, gV] :: rest)[0]? =
      some (.list [.list ks, gV]) := fun _ => rfl
  have hincW : (encPts (incl.map (domPos e L.q))).wt ≤ W := by
    have := cp_wt_pts (q := L.q) (X := incl.map (domPos e L.q)) (by rw [List.length_map]; omega)
    have : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hosW : (encPts σ.osP).wt ≤ W := by
    have := cp_wt_pts (q := L.q) hlo
    have : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have dF := Det.mk2 (cp_rdI (P := Pg) (h1 [gpV qs]) hwW hi0 (j := 4) rfl (by omega))
    (cp_rdK (P := Pg) (h1 [gpV qs]) hwW (j := 9) (v := encPts σ.osP) rfl (by omega))
  have hfW : (Val.list [encPts (incl.map (domPos e L.q)), encPts σ.osP]).wt ≤ W := by
    have := wt_list2_le (encPts (incl.map (domPos e L.q))) (encPts σ.osP)
    have := cp_wt_pts (q := L.q) (X := incl.map (domPos e L.q)) (by rw [List.length_map]; omega)
    have := cp_wt_pts (q := L.q) hlo
    have : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hbf := cp_bud_filt (e := e) (q := L.q) hst hpre hm hat (incl := incl) (os := os)
    hincl hosl (W := W) hW2
  rw [← encPts_posN, ← hosP] at hbf
  set os' := os.filter fun v => decide ((cpPosN e L.q incl).count (domPos e L.q v : ℕ) = 0)
    with hos'
  refine (CpEB.letE (CpEB.call (CpEB.det dF le_rfl hfW
      (Q := fun v => v = .list [encPts (incl.map (domPos e L.q)), encPts σ.osP]) rfl)
    fun v hv _ => hv ▸ hbf) (Cb := 500 * (W + 20)) fun ov hov hoW => ?_).mono
    (by omega) fun _ h => h
  subst hov
  -- the new program state
  have hos'l : os'.length ≤ k := (List.filter_sublist).length_le.trans hosl
  have hnd' : os'.Nodup := hndo.filter _
  have hmem' : ∀ v, v ∈ os' ↔ v ∉ win (cpPhi S πd σ.T) (dstr S (cpZ S σ.s)) σ.t ∧ v ∉ incl := by
    intro v
    rw [hos', cp_filt_mem, hos]
  set σ' := σ.close qs (os'.map (domPos e L.q)) (incl.map (domPos e L.q)) with hσ'
  have hlen' : CpLen D σ' := ⟨by simp only [hσ', CpSt.close]; omega,
    by simpa [hσ', CpSt.close] using hos'l, hl0, hlx, hqsl, hlr, hlc⟩
  have hlog' : CpLogLen σ' := { hR.loglen with
    lz := cpLgLen_snoc hR.loglen.lz (by rw [hR.lz_len]; omega) ⟨hlp, by simpa using hincl⟩ }
  have hnew := cp_wt_new (par := par) hlen' hlog' (by simp only [hσ', CpSt.close]; omega)
    (by simp only [hσ', CpSt.close]; omega) (by simp only [hσ', CpSt.close]; omega) hBw
  obtain ⟨m', st', Ss', hlt', hsub, hrep, hst'⟩ := cp_answer_close (st := .nat 0) hm' hmf hM
    hNT hWI0 hl hG ho hacc hinc hnd hlp hao ctx.hgp hqs hnd' hmem' rfl hlen' hnew
  subst hst'
  have hK : (σ'.val par (.list [])).wt < Bw :=
    lt_of_lt_of_le (cp_wt_get (vs := [σ'.val par (.list []), .nat 0]) (j := 0) rfl) hnew
  have htW : σ.t + 1 ≤ W := by omega
  set env := [Val.list [.list ks, gV], gpV qs, encPts (os'.map (domPos e L.q))] with henv
  have hsW : (σ'.val par (.list [])).wt ≤ W := by omega
  have d12 : Det Pg env (.snoc (cpKf 12) (mk2 (cpKf 8) (cpIf 4)))
      (.list ((σ.lz ++ [(σ.ps, incl.map (domPos e L.q))]).map cpSgV)) (25 * (W + 20)) := by
    have := Det.snoc (cp_rdK (P := Pg) (h1 [gpV qs, encPts (os'.map (domPos e L.q))]) hwW
        (j := 12) rfl (by omega))
      (Det.mk2 (cp_rdK (P := Pg) (h1 [gpV qs, encPts (os'.map (domPos e L.q))]) hwW (j := 8) rfl
          (by omega))
        (cp_rdI (P := Pg) (h1 [gpV qs, encPts (os'.map (domPos e L.q))]) hwW hi0 (j := 4) rfl
          (by omega)))
    have hv : Val.list (σ.lz.map cpSgV ++ [.list [gpV σ.ps, encPts (incl.map (domPos e L.q))]]) =
        .list ((σ.lz ++ [(σ.ps, incl.map (domPos e L.q))]).map cpSgV) := by
      simp [cpSgV]
    rw [hv] at this
    refine this.mono ?_
    have := wt_list2_le (gpV σ.ps) (encPts (incl.map (domPos e L.q)))
    have := cp_wt_get (vs := ks) (j := 8) (v := gpV σ.ps) rfl
    have h1 := cp_wt_get (vs := σ'.vals par (.list [])) (j := 12)
      (v := .list ((σ.lz ++ [(σ.ps, incl.map (domPos e L.q))]).map cpSgV)) rfl
    have h2 : (Val.list (σ'.vals par (.list []))).wt ≤ W := hsW
    omega
  have dK := cp_mkList' (P := Pg) (env := env) (W := W) (c := 25 * (W + 20))
    (v := σ'.val par (.list []))
    [(cpKf 0, par), (cpKf 1, .list (σ.Ts.map (tsV k))), (cpKf 2, boolVal σ.s),
      (cpKf 3, .list (σ.res.map resV)), (cpKf 4, .list (σ.cache.map ckEntV)),
      (cpKf 5, gpV σ.p0), (cpKf 6, gpV σ.px),
      (.arith .add (cpKf 7) (.nat 1), .nat (σ.t + 1)), (.var 1, gpV qs),
      (.var 2, encPts (os'.map (domPos e L.q))), (.nil, .list []), (cpKf 11, tsV k σ.T),
      (.snoc (cpKf 12) (mk2 (cpKf 8) (cpIf 4)),
        .list ((σ.lz ++ [(σ.ps, incl.map (domPos e L.q))]).map cpSgV)),
      (cpKf 13, .list (σ.lx.map cpSgV)), (cpKf 14, .list (σ.logs.map cpLogV))] rfl (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 0) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 1) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 2) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 3) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 4) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 5) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 6) rfl (by omega)).mono (by omega)
      · exact (Det.arith' (cp_rdK (P := Pg) (h1 _) hwW (j := 7) rfl (by omega)) (Det.nat 1)
          (z := σ.t + 1) rfl).mono (by omega)
      · exact (Det.rv (P := Pg) (env := env) (i := 1) rfl hqW).mono (by omega)
      · exact (Det.rv (P := Pg) (env := env) (i := 2) rfl hoW).mono (by omega)
      · exact Det.nil.mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 11) rfl (by omega)).mono (by omega)
      · exact d12
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 13) rfl (by omega)).mono (by omega)
      · exact (cp_rdK (P := Pg) (h1 _) hwW (j := 14) rfl (by omega)).mono (by omega))
    hsW
  have := wt_list2_le (σ'.val par (.list [])) (.nat 0)
  have := wt_list2_le (.nat 2) (.list [σ'.val par (.list []), .nat 0])
  have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
  have : (Val.nat 2).wt ≤ 4 := wt_nat_le 2
  refine CpEB.det (Det.mk2 (Det.nat 2) (Det.mk2 dK (Det.nat 0))) ?_ (by omega)
    (Or.inr ⟨m', _, Ss', hlt', hsub, hrep, rfl⟩)
  simp only [List.length_cons, List.length_nil]
  omega

end Close

end GI.Impl
