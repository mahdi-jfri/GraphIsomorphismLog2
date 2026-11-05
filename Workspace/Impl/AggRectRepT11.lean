module

public import Workspace.Impl.AggRectRepT10

@[expose] public section

/-!
# The program in the pair case

`rcR_case_pair`: when the small list of `π(G_x)` is `[d₁, d₂]`, the main function returns the
value of `rcRRf e I hx W R hc`, with graph pairs of its group.
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm GI.Assembly GI.StabilizerQuotient GI.Rectangle GI.Lang
open GI.Cited (Val gens encPerm encGroup encPts PointwiseStab Preimage)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-- The cost of the main function, for the stage bound `Wb`. -/
noncomputable def rcRCostM (hst : PointwiseStab) (hpre : Preimage) (Wb : ℕ) : ℕ :=
  ((pointwiseStabPrim hst).boundSize Wb + 10 ^ 22 * (Wb + 1) ^ 8) + 10 ^ 11 * (Wb + 1) ^ 12 +
    2 * ((preimagePrim hpre).boundSize Wb + 10 ^ 18 * (Wb + 1) ^ 8) +
    ((pointwiseStabPrim hst).boundSize Wb + 10 ^ 26 * (Wb + 1) ^ 9) + 100 * Wb + 100

section Pair

variable [Finite Ω] {k : ℕ} (e : Ω ≃ Fin k) (I : AggregationData P₀ S L) {x : Ω}
  (hx : x ∈ S.dom) {W R : Finset (Fin L.q)} (hc : RectConds P₀ S L W R) {P : Program}
  {J : RcRIdx}

/-- Stage 1 within the uniform bound. -/
theorem rcR_st1_uni (hst : PointwiseStab) {ps : List (Perm (Fin k) × Perm (Fin L.q))}
    (svs : List Val) {M Wb : ℕ} (hA : (rcRInV svs ps W R).wt ≤ M) (hk : k ≤ M) (hq : L.q ≤ M)
    (hW : 10 ^ 6 * (M + 1) ^ 10 ≤ Wb) :
    (pointwiseStabPrim hst).bound (.list [encGroup (ps.map encPair),
      encPts [Fin.castAdd L.q (e x)]]) ≤ (pointwiseStabPrim hst).boundSize Wb := by
  refine Prim.bound_le _ ?_
  have h1 := rcR_wt_stabIn hk hq ps ((rcR_In_ps svs ps _ _).trans hA) (Fin.castAdd L.q (e x))
  have h2 := Val.size_le_wt (Val.list [encGroup (ps.map encPair), encPts [Fin.castAdd L.q (e x)]])
  have h3 : (M + 1) ^ 4 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  omega

include hc in
/-- **The pair case.** -/
theorem rcR_case_pair (ok : RcROk P J) (hst : PointwiseStab)
    (hj : P.prims[J.jp]? = some (pointwiseStabPrim hst)) (hpre : Preimage)
    (hjp : P.prims[J.jpre]? = some (preimagePrim hpre))
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps) (svs : List Val)
    (hsv0 : svs[0]? = some (.nat k)) (hsv2 : svs[2]? = some (natList (rcRL (rcRDom e S))))
    (hxd : (rcRL (rcRDom e S)).findIdx (fun t => t == 1) = (e x : ℕ))
    {d₁ d₂ : Fin L.q} (hlt : d₁ < d₂) (hsm : rcRSmall (rcRStab S L x) = [d₁, d₂])
    {M Wb : ℕ} (hA : (rcRInV svs ps W R).wt ≤ M) (hW : 10 ^ 6 * (M + 1) ^ 10 ≤ Wb) :
    CpFB P J.main (rcRInV svs ps W R) Wb (rcRCostM hst hpre Wb)
      (fun w => ∃ hs : List (Perm (Fin k) × Perm (Fin L.q)),
        w = rcRepVal e (rcRRf e I hx W R hc) hs ∧ PairGens e L (rcRRf e I hx W R hc).H hs ∧
          hs.length ≤ k ^ 2) := by
  -- bounds
  have hdl : (rcRL (rcRDom e S)).length = k := by simp [rcRL]
  have hk : k ≤ M := (rcR_In_k hsv2 hdl ps _ _).trans hA
  have hq : L.q ≤ M := (rcR_In_q svs ps (rcR_ind_length W) _).trans hA
  have hq8 := rcR_q8 I
  have hM : 1 ≤ M := by omega
  have hxM : (e x : ℕ) ≤ M := by have := (e x).2; omega
  -- the first two points of `W`
  obtain ⟨h0, h1, hw0, hw1, hw⟩ := rcR_W01 (W := W) (by have := hc.2.2.1; omega)
  have hw' : (⟨_, h0⟩ : Fin L.q) ≠ ⟨_, h1⟩ := fun h => hw (congrArg Fin.val h)
  have hsmv : (rcRSmall (rcRStab S L x)).map Fin.val = [(d₁ : ℕ), (d₂ : ℕ)] := by rw [hsm]; rfl
  obtain ⟨hF1, hF2⟩ := rcR_front e ok hst hj hps svs hsv0 hsv2 hxd W R hsmv
    (d₁ := d₁) (d₂ := d₂) rfl rfl hA hW
  have hR1w : ∀ R1, rcRQ1 e S L x R1 → R1.wt ≤ 50 * (M + 1) ^ 2 := by
    rintro R1 ⟨qs, rfl, -⟩; exact rcR_wt_R1 hq hxM qs
  have hR2w := fun R2 (h : rcRQ2 e S L x W R ([(d₁ : ℕ), (d₂ : ℕ)].length == 1) d₁ d₂ R2) =>
    rcR_wt_Q2 e hk hq h
  have hR3w : ∀ qs : List (Perm (Fin k) × Perm (Fin L.q)), qs.length ≤ (k + L.q) ^ 2 →
      (Val.list [.list (qs.map pairV), .list []]).wt ≤ 500000 * (M + 1) ^ 6 := fun qs hl =>
    (rcR_wt_R3p hk hq qs hl).trans (by omega)
  have hnil : (Val.list []).wt ≤ 4 := by
    have := wt_list_le ([] : List Val); simpa using this
  have hX2 : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hX5 : 1 ≤ (M + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hX6 : 1 ≤ (M + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hX10 : M + 1 ≤ (M + 1) ^ 10 := by
    calc M + 1 = (M + 1) ^ 1 := (pow_one _).symm
      _ ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  refine (rcR_main_run ok (Q3 := fun _ _ R3 => ∃ qs : List (Perm (Fin k) × Perm (Fin L.q)),
      R3 = .list [.list (qs.map pairV), .list []] ∧ qs.length ≤ (k + L.q) ^ 2 ∧
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
    have hR2 : rcRSt2Val d₁ d₂ (Lt.map fun p => ptsKey p.1)
        (rcRGenLs (rcRInd W) (rcRInd R) (rcRW0 (rcRInd W)) (rcRW1 (rcRInd W) L.q) L.q)
        ([(d₁ : ℕ), (d₂ : ℕ)].length == 1) (decide (d₂ ∈ rcROrb (rcRStab S L x) d₁)) k =
        .list [.nat d₁, .nat d₂, rcTV (Lt.map fun p => ptsKey p.1),
          .list ((rcRGens W R ⟨_, h0⟩ ⟨_, h1⟩).map encPerm), .nat 0,
          .nat (decide (d₂ ∈ rcROrb (rcRStab S L x) d₁)).toNat, natList (List.range k)] := by
      unfold rcRSt2Val; rw [rcR_gensV W R h0 h1]; rfl
    have hw2 := (rcR_wt_four _ (.list []) _ (.list []) hM hA (by
      omega)
      (rcR_wt_Q2 e (W := W) (R := R) (car := ([(d₁ : ℕ), (d₂ : ℕ)].length == 1)) hk hq
        ⟨Lt, rfl, hT, hl, hl3⟩) (by
      omega) hW).2.2
    rw [hR2] at hw2 ⊢
    refine ⟨_, 0, rfl, rfl, fun h => absurd rfl h, fun _ => ?_⟩
    refine (rcR_pairF_spec ok hpre hjp svs hsv0 ps (rcRInd W) (rcRInd R) _ _ _ _ _ _
      (rcRGens W R ⟨_, h0⟩ ⟨_, h1⟩) (rcR_pre_pair e hc hps hw') hA hk hq ?_ hW hw2).mono
      (by omega) ?_
    · rw [rcR_gens_length]
      calc L.q * L.q ≤ (M + 1) * (M + 1) := Nat.mul_le_mul (by omega) (by omega)
        _ = (M + 1) ^ 2 := (pow_two _).symm
    · rintro w ⟨qs, hw, hl, hcl⟩
      exact ⟨qs, hw, hl, rcR_H_pair e I hx hc hsm hps hw0 hw1 hw' hcl⟩
  · -- stage 4
    rintro R1 R2 R3 ⟨qs1, rfl, -⟩ ⟨Lt, rfl, hT, hl, hl3⟩ ⟨qs, rfl, hql, hH⟩ - - -
    have hIn4 := (rcR_wt_four _ _ _ _ hM hA (rcR_wt_R1 hq hxM qs1)
      (rcR_wt_Q2 e (W := W) (R := R) (car := ([(d₁ : ℕ), (d₂ : ℕ)].length == 1)) hk hq
        ⟨Lt, rfl, hT, hl, hl3⟩) (hR3w qs hql) hW).1
    have hLk : ∀ y ∈ Lt.map (fun p => ptsKey p.1), ∀ z ∈ y, z ≤ 2 * M := by
      intro y hy z hz
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hy
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
      have := i.2; omega
    have hrw : (natList ([] : List ℕ)).wt ≤ 5 * (M + 1) ^ 2 :=
      wt_natList_le_sq (xs := []) (B := M) (by simp) (by simp)
    unfold rcRSt1Val rcRSt2Val at hIn4 ⊢
    rw [show (Val.list [.list (qs.map pairV), .list []]) =
      .list [.list (qs.map pairV), natList []] from rfl] at hIn4 ⊢
    refine (rcR_st4_spec ok hst hj svs hsv0 _ hsv2 ps (rcRInd W) (rcRInd R) (rcR_ind_length W)
      (rcR_ind_length R) _ _ _ _ _ _ (Lt.map fun p => ptsKey p.1)
      ([(d₁ : ℕ), (d₂ : ℕ)].length == 1) (decide (d₂ ∈ rcROrb (rcRStab S L x) d₁)) qs []
      hLk (rcR_wt_keys hk hq Lt hl hl3) hrw hql (by omega) hA hk hq hW ?_).mono le_rfl ?_
    · exact hIn4
    rintro w ⟨hs, rfl, hg, hhl⟩
    obtain ⟨hpg, hpi⟩ := rcR_hs_final e hx (rcRRf e I hx W R hc).le (hg.trans hH) hT hq8
      (rcR_stab_keep I hx hc.1 (Or.inl hsm))
    refine ⟨_, rcR_val_eq e _ hs _ _ hpi (fun i => rcR_cells_pair e I hx hc hsm hT [] i)
      (rcR_twist e I hx hc (Or.inl ⟨d₁, d₂, hlt, hsm⟩)), hpg, ?_⟩
    rw [List.length_map]; exact hhl

end Pair

end GI.Impl
