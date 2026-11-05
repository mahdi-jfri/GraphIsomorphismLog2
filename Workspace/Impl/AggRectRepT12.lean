module

public import Workspace.Impl.AggRectRepT11

@[expose] public section

/-!
# The program in the single-label case

`rcR_case_car`: when the small list of `π(G_x)` is `[a]`, the main function returns the value of
`rcRRf e I hx W R hc`, with graph pairs of its group. Stage 3 runs Preimage on the pairs
`(g, ρ(g) ⊕ π(g))` of the carrier of Lemma A.30 (`rcRPhi`), with the generators
`embed(σ) ⊕ σ` of the side stabilizer (`rcREmb`).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm GI.Assembly GI.StabilizerQuotient GI.Rectangle GI.Lang
open GI.Cited (Val gens encPerm encGroup encPts PointwiseStab Preimage)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

theorem rcR_L_getD_lt {k : ℕ} (σ : Perm (Fin k)) (hk : 0 < k) (v : ℕ) :
    (rcRL fun i => (σ i : ℕ)).getD v 0 < k := by
  by_cases hv : v < k
  · rw [show v = ((⟨v, hv⟩ : Fin k) : ℕ) from rfl, rcR_L_getD]
    exact (σ _).2
  · rw [List.getD_eq_default _ _ (by simp [rcRL]; omega)]
    exact hk

theorem rcR_rowT_getD {dl rl : List ℕ} {k j : ℕ} (hj : j < k) :
    (rcRRowT dl rl k).getD j 0 = rcRRowN' dl rl k j := by
  unfold rcRRowT
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

section Car

variable [Finite Ω] {k : ℕ} (e : Ω ≃ Fin k) (I : AggregationData P₀ S L) {x : Ω}
  (hx : x ∈ S.dom) {W R : Finset (Fin L.q)} (hc : RectConds P₀ S L W R) {P : Program}
  {J : RcRIdx}

include hc in
/-- **The single-label case.** -/
theorem rcR_case_car (ok : RcROk P J) (hst : PointwiseStab)
    (hj : P.prims[J.jp]? = some (pointwiseStabPrim hst)) (hpre : Preimage)
    (hjp : P.prims[J.jpre]? = some (preimagePrim hpre))
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps) (svs : List Val)
    (hsv0 : svs[0]? = some (.nat k)) (hsv2 : svs[2]? = some (natList (rcRL (rcRDom e S))))
    {rv : Val} (hsv6 : svs[6]? = some rv) (hrv : OptVal (RowValC e) rv S.rows)
    (hxd : (rcRL (rcRDom e S)).findIdx (fun t => t == 1) = (e x : ℕ))
    {a : Fin L.q} (hsm : rcRSmall (rcRStab S L x) = [a])
    {M Wb : ℕ} (hA : (rcRInV svs ps W R).wt ≤ M) (hW : 10 ^ 6 * (M + 1) ^ 10 ≤ Wb) :
    CpFB P J.main (rcRInV svs ps W R) Wb (rcRCostM hst hpre Wb)
      (fun w => ∃ hs : List (Perm (Fin k) × Perm (Fin L.q)),
        w = rcRepVal e (rcRRf e I hx W R hc) hs ∧ PairGens e L (rcRRf e I hx W R hc).H hs ∧
          hs.length ≤ k ^ 2) := by
  classical
  -- bounds
  have hdl : (rcRL (rcRDom e S)).length = k := by simp [rcRL]
  have hk : k ≤ M := (rcR_In_k hsv2 hdl ps _ _).trans hA
  have hq : L.q ≤ M := (rcR_In_q svs ps (rcR_ind_length W) _).trans hA
  have hq8 := rcR_q8 I
  have hM : 1 ≤ M := by omega
  have hk0 : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) (e x).2
  have hxM : (e x : ℕ) ≤ M := by have := (e x).2; omega
  have hnil : (Val.list []).wt ≤ 4 := by
    have := wt_list_le ([] : List Val); simpa using this
  have hX2 : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hX5 : 1 ≤ (M + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hX6 : 1 ≤ (M + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hX10 : M + 1 ≤ (M + 1) ^ 10 := by
    calc M + 1 = (M + 1) ^ 1 := (pow_one _).symm
      _ ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  -- the carrier
  obtain ⟨f, -, hrf⟩ := rcR_rf_car e I hx hc hsm
  have hrec := (rcR_rec_spec I hc.1 f).1
  rw [hrec] at hrv
  obtain ⟨u, ⟨rv', cv, ⟨lab, hrv', -, hrl⟩, -, rfl⟩, rfl⟩ := hrv
  rw [rcR_encFun_eq] at hrv'
  subst hrv'
  set m := (rcRRec I hc.1 f).m with hmdef
  have hD : ∀ g ∈ S.G, ∀ v ∈ S.dom, g v ∈ S.dom := fun g hg v hv => (S.dom_inv g hg v).2 hv
  have hm : (rcRKeysN (rcRL (rcRDom e S)) (rcRL lab) k).length = m :=
    (rcR_keysN_length e S.dom (rcRRec I hc.1 f).rows (rcRDom e S) lab (fun _ => rfl) hrl).trans
      (rcR_keys_card (rcR_spec0 I hc.1 f))
  have hmk : m ≤ k := hm ▸ rcR_keysN_len _ _ k
  -- the first two points of `W`
  obtain ⟨h0, h1, hw0, hw1, hw⟩ := rcR_W01 (W := W) (by have := hc.2.2.1; omega)
  have hw' : (⟨_, h0⟩ : Fin L.q) ≠ ⟨_, h1⟩ := fun h => hw (congrArg Fin.val h)
  have hsmv : (rcRSmall (rcRStab S L x)).map Fin.val = [(a : ℕ)] := by rw [hsm]; rfl
  obtain ⟨hF1, hF2⟩ := rcR_front e ok hst hj hps svs hsv0 hsv2 hxd W R hsmv
    (d₁ := a) (d₂ := a) rfl rfl hA hW
  -- the maps of stage 3
  let ρf : Perm (Fin k) × Perm (Fin L.q) → Perm (Fin m) := fun p =>
    ((rcRRhoN e I hc.1 f (rcRPre e p) : alternatingGroup _) : Perm (Fin m))
  let τf : Perm (Fin L.q) → Perm (Fin m) := fun σ =>
    if h : σ ∈ alternatingGroup (Fin L.q) then
      ((rcRCarD e I hc.1 f).d.embedAlt ⟨σ, h⟩).1
    else 1
  have hρ : ∀ p ∈ ps, (List.range m).map (fun r => (rcRRowT (rcRL (rcRDom e S)) (rcRL lab) k).getD
      ((rcRL fun i => (p.1 i : ℕ)).getD ((rcRKeysN (rcRL (rcRDom e S)) (rcRL lab) k).getD r 0) 0)
        0) = rcRL fun r => (ρf p r : ℕ) := by
    intro p hp
    have hpre := rcR_pre_spec e hps p hp
    have hh : ∀ v : Fin k, (fun v => (rcRL fun i => (p.1 i : ℕ)).getD v 0) v =
        e (((rcRPre e p : S.G) : Perm Ω) (e.symm v)) := by
      intro v
      simp only
      rw [rcR_L_getD, show p.1 = (gpair e L (rcRPre e p)).1 by rw [hpre]]
      rfl
    have := rcR_rhoL_eq e S.dom (rcRRec I hc.1 f).rows (rcRDom e S) lab (fun _ => rfl) hrl
      (rcR_spec0 I hc.1 f) (rcR_m_pos I hc.1 f) hD (rcRPre e p)
      (h := fun v => (rcRL fun i => (p.1 i : ℕ)).getD v 0) hh
    refine Eq.trans ?_ this
    unfold rcRRhoL
    exact List.map_congr_left fun r _ => rcR_rowT_getD (rcR_L_getD_lt p.1 hk0 _)
  have hmalt : ∀ σ ∈ rcRGens W R ⟨_, h0⟩ ⟨_, h1⟩, σ ∈ alternatingGroup (Fin L.q) := by
    intro σ hσ
    obtain ⟨a', b', rfl⟩ := rcR_mem_gens.1 hσ
    exact rcR_gen_mem_alt hw' a' b'
  have hτ : ∀ σ ∈ rcRGens W R ⟨_, h0⟩ ⟨_, h1⟩, (List.range m).map (fun j => if j < L.q then
      (rcRL fun i => (σ i : ℕ)).getD j 0 else j) = rcRL fun r => (τf σ r : ℕ) := by
    intro σ hσ
    rw [rcR_range_finRange]
    refine List.map_congr_left fun j _ => ?_
    have hτσ : τf σ = ((rcRCarD e I hc.1 f).d.embedAlt ⟨σ, hmalt σ hσ⟩).1 :=
      dif_pos (hmalt σ hσ)
    rw [hτσ]
    have he := rcR_embed_apply e I hc.1 f ⟨σ, hmalt σ hσ⟩ j
    by_cases hj : (j : ℕ) < L.q
    · rw [if_pos hj, show (j : ℕ) = ((⟨j, hj⟩ : Fin L.q) : ℕ) from rfl, rcR_L_getD]
      erw [he, dif_pos hj]
      rfl
    · rw [if_neg hj]
      erw [he, dif_neg hj]
  have hE1 : ps.map (fun p => (p.1, encPair (ρf p, p.2))) =
      ps.map fun p => rcRPhi e I hc.1 f (rcRPre e p) := by
    refine List.map_congr_left fun p hp => ?_
    have hpre := rcR_pre_spec e hps p hp
    have hphi : rcRPhi e I hc.1 f (rcRPre e p) = ((gpair e L (rcRPre e p)).1,
        encPair (ρf p, (gpair e L (rcRPre e p)).2)) := rfl
    rw [hphi, hpre]
  have hE2 : (rcRGens W R ⟨_, h0⟩ ⟨_, h1⟩).map (fun σ => encPair (τf σ, σ)) =
      (rcRGensA W R ⟨_, h0⟩ ⟨_, h1⟩ hw').map (rcREmb e I hc.1 f) := by
    unfold rcRGensA
    conv_lhs => rw [← List.attach_map_subtype_val (rcRGens W R ⟨_, h0⟩ ⟨_, h1⟩)]
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun σ _ => ?_
    simp only [Function.comp_apply]
    have hτσ : τf σ.1 = ((rcRCarD e I hc.1 f).d.embedAlt ⟨σ.1, hmalt σ.1 σ.2⟩).1 :=
      dif_pos (hmalt σ.1 σ.2)
    rw [hτσ]
    rfl
  have hms : ∀ m' ∈ (rcRGens W R ⟨_, h0⟩ ⟨_, h1⟩).map (fun σ => encPair (τf σ, σ)),
      ∃ p ∈ Subgroup.closure {p | p ∈ ps.map fun p => (p.1, encPair (ρf p, p.2))},
        MonoidHom.snd _ _ p = m' := by
    intro m' hm'
    rw [hE2] at hm'
    rw [hE1]
    exact rcR_pre_car e I hc.1 f hps hw' m' hm'
  -- weights
  have hR1w : ∀ R1, rcRQ1 e S L x R1 → R1.wt ≤ 50 * (M + 1) ^ 2 := by
    rintro R1 ⟨qs, rfl, -⟩; exact rcR_wt_R1 hq hxM qs
  have hR2w := fun R2 (h : rcRQ2 e S L x W R ([(a : ℕ)].length == 1) a a R2) =>
    rcR_wt_Q2 e hk hq h
  have hrowl : ∀ y ∈ rcRRowT (rcRL (rcRDom e S)) (rcRL lab) k, y ≤ M := fun y hy =>
    (rcR_rowT_le _ _ k y hy).trans hk
  have hrowL : (rcRRowT (rcRL (rcRDom e S)) (rcRL lab) k).length ≤ M := by
    simp [rcRRowT]; exact hk
  have hR3w : ∀ qs : List (Perm (Fin k) × Perm (Fin (m + L.q))),
      qs.length ≤ (k + (m + L.q)) ^ 2 →
      (Val.list [.list (qs.map pairV), natList (rcRRowT (rcRL (rcRDom e S)) (rcRL lab) k)]).wt ≤
        500000 * (M + 1) ^ 6 := fun qs hl =>
    rcR_wt_R3c hk hq hmk qs hl _ hrowl hrowL
  refine (rcR_main_run ok (Q3 := fun _ _ R3 => ∃ qs : List (Perm (Fin k) × Perm (Fin (m + L.q))),
      R3 = .list [.list (qs.map pairV), natList (rcRRowT (rcRL (rcRDom e S)) (rcRL lab) k)] ∧
      qs.length ≤ (k + (m + L.q)) ^ 2 ∧
      gens (qs.map Prod.fst) = (((rcRRf e I hx W R hc).H).subgroupOf S.G).map (rcRPos e))
    (C1 := (pointwiseStabPrim hst).boundSize Wb + 10 ^ 22 * (Wb + 1) ^ 8)
    (C3 := (preimagePrim hpre).boundSize Wb + 10 ^ 18 * (Wb + 1) ^ 8)
    (C2 := 10 ^ 11 * (Wb + 1) ^ 12)
    (C4 := (pointwiseStabPrim hst).boundSize Wb + 10 ^ 26 * (Wb + 1) ^ 9)
    (hF1.mono (by have := rcR_st1_uni e hst svs hA hk hq hW (x := x); omega) fun _ h => h)
    (fun R1 h _ => hF2 R1 h) ?_ ?_ (by omega)
    (fun R1 h1 => (rcR_wt_four _ R1 (.list []) (.list []) hM hA (hR1w R1 h1) (by
      omega) (by
      omega) hW).2.1)
    (fun R1 R2 _ h2 => (rcR_wt_four _ (.list []) R2 (.list []) hM hA (by
      omega) (hR2w R2 h2) (by
      omega) hW).2.2)
    (fun R1 R2 R3 h1 h2 ⟨qs, h3, hl, _⟩ => (rcR_wt_four _ R1 R2 R3 hM hA (hR1w R1 h1)
      (hR2w R2 h2) (h3 ▸ hR3w qs hl) hW).1)).mono (by unfold rcRCostM; omega) fun _ h => h
  · -- stage 3
    rintro R1 R2 - ⟨Lt, rfl, hT, hl, hl3⟩ - -
    have hR2 : rcRSt2Val a a (Lt.map fun p => ptsKey p.1)
        (rcRGenLs (rcRInd W) (rcRInd R) (rcRW0 (rcRInd W)) (rcRW1 (rcRInd W) L.q) L.q)
        ([(a : ℕ)].length == 1) (decide (a ∈ rcROrb (rcRStab S L x) a)) k =
        .list [.nat a, .nat a, rcTV (Lt.map fun p => ptsKey p.1),
          .list ((rcRGens W R ⟨_, h0⟩ ⟨_, h1⟩).map encPerm), .nat 1,
          .nat (decide (a ∈ rcROrb (rcRStab S L x) a)).toNat, natList (List.range k)] := by
      unfold rcRSt2Val; rw [rcR_gensV W R h0 h1]; rfl
    have hw2 := (rcR_wt_four _ (.list []) _ (.list []) hM hA (by omega)
      (rcR_wt_Q2 e (W := W) (R := R) (car := ([(a : ℕ)].length == 1)) hk hq
        ⟨Lt, rfl, hT, hl, hl3⟩) (by omega) hW).2.2
    rw [hR2] at hw2 ⊢
    refine ⟨_, 1, rfl, rfl, fun _ => ?_, fun h => absurd h (by norm_num)⟩
    refine (rcR_carF_spec ok hpre hjp svs hsv0 _ hsv2 (rcRL lab) _ _ hsv6 ps (rcRInd W)
      (rcRInd R) _ _ _ _ _ (rcRGens W R ⟨_, h0⟩ ⟨_, h1⟩) hm ρf hρ τf hτ hms hA hk hq ?_ hW
      hw2).mono le_rfl ?_
    · rw [rcR_gens_length]
      calc L.q * L.q ≤ (M + 1) * (M + 1) := Nat.mul_le_mul (by omega) (by omega)
        _ = (M + 1) ^ 2 := (pow_two _).symm
    · rintro w ⟨qs, hw, hl, hcl⟩
      refine ⟨qs, hw, hl, ?_⟩
      rw [hE1, hE2] at hcl
      rw [hrf]
      exact rcR_H_car e I hc.1 f hps hc.2.1 hw0 hw1 hw' hcl
  · -- stage 4
    rintro R1 R2 R3 ⟨qs1, rfl, -⟩ ⟨Lt, rfl, hT, hl, hl3⟩ ⟨qs, rfl, hql, hH⟩ - - -
    have hIn4 := (rcR_wt_four _ _ _ _ hM hA (rcR_wt_R1 hq hxM qs1)
      (rcR_wt_Q2 e (W := W) (R := R) (car := ([(a : ℕ)].length == 1)) hk hq
        ⟨Lt, rfl, hT, hl, hl3⟩) (hR3w qs hql) hW).1
    have hLk : ∀ y ∈ Lt.map (fun p => ptsKey p.1), ∀ z ∈ y, z ≤ 2 * M := by
      intro y hy z hz
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hy
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
      have := i.2; omega
    have hrw : (natList (rcRRowT (rcRL (rcRDom e S)) (rcRL lab) k)).wt ≤ 5 * (M + 1) ^ 2 :=
      wt_natList_le_sq hrowl hrowL
    unfold rcRSt1Val rcRSt2Val at hIn4 ⊢
    refine (rcR_st4_spec ok hst hj svs hsv0 _ hsv2 ps (rcRInd W) (rcRInd R) (rcR_ind_length W)
      (rcR_ind_length R) _ _ _ _ _ _ (Lt.map fun p => ptsKey p.1)
      ([(a : ℕ)].length == 1) (decide (a ∈ rcROrb (rcRStab S L x) a)) qs
      (rcRRowT (rcRL (rcRDom e S)) (rcRL lab) k)
      hLk (rcR_wt_keys hk hq Lt hl hl3) hrw hql (by omega) hA hk hq hW ?_).mono le_rfl ?_
    · exact hIn4
    rintro w ⟨hs, rfl, hg, hhl⟩
    obtain ⟨hpg, hpi⟩ := rcR_hs_final e hx (rcRRf e I hx W R hc).le (hg.trans hH) hT hq8
      (rcR_stab_keep I hx hc.1 (Or.inr ⟨rfl, hsm⟩))
    refine ⟨_, rcR_val_eq e _ hs _ _ hpi
      (fun i => rcR_cells_car e I hx hc hsm hT hrec lab hrl _ i)
      (rcR_twist e I hx hc (Or.inr ⟨a, hsm⟩)), hpg, ?_⟩
    rw [List.length_map]; exact hhl

end Car

end GI.Impl
