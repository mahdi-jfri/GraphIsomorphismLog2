import Workspace.Impl.AggRectRepT8

/-!
# Stages 1 and 2 on a state

`rcR_front`: on the input `[sv, q, ⟨ps⟩, W, R]` of a state, stage 1 returns the support data at
the base point `x` (its label part generates `π(G_x)`), and stage 2 returns the orbit table of
the base tuple and the generators of `P`. The small list of `π(G_x)` is passed as `sm`, with
first and last entries `d₁`, `d₂`.
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm GI.Assembly GI.StabilizerQuotient GI.Rectangle GI.Lang
open GI.Cited (Val gens encPerm encGroup encPts PointwiseStab)

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

section Front

variable {k : ℕ} (e : Ω ≃ Fin k) {x : Ω} {P : Program} {J : RcRIdx}

/-- The input of the program on a state. -/
noncomputable abbrev rcRInV (svs : List Val) (ps : List (Perm (Fin k) × Perm (Fin L.q)))
    (W R : Finset (Fin L.q)) : Val :=
  .list [.list svs, .nat L.q, .list (ps.map pairV), natList (rcRInd W), natList (rcRInd R)]

/-- What stage 1 gives. -/
def rcRQ1 (S : State Ω C) (L : GiantLabels S) (x : Ω) (R1 : Val) : Prop :=
  ∃ qs : List (Perm (Fin k) × Perm (Fin L.q)), R1 = rcRSt1Val (e x) qs ∧
    gens (qs.map Prod.snd) = rcRStab S L x

/-- What stage 2 gives. -/
def rcRQ2 (S : State Ω C) (L : GiantLabels S) (x : Ω) (W R : Finset (Fin L.q)) (car : Bool)
    (d₁ d₂ : Fin L.q) (R2 : Val) : Prop :=
  ∃ Lt : List (List (Fin (k + L.q)) × Perm (Fin (k + L.q))),
    R2 = rcRSt2Val d₁ d₂ (Lt.map fun p => ptsKey p.1)
      (rcRGenLs (rcRInd W) (rcRInd R) (rcRW0 (rcRInd W)) (rcRW1 (rcRInd W) L.q) L.q) car
      (decide (d₂ ∈ rcROrb (rcRStab S L x) d₁)) k ∧
    RcRTab e x d₁ d₂ (Lt.map fun p => ptsKey p.1) ∧ Lt.length ≤ k * L.q * L.q ∧
    ∀ p ∈ Lt, p.1.length = 3

theorem rcR_dom_le1 : ∀ y ∈ rcRL (rcRDom e S), y ≤ 1 := by
  intro y hy
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
  unfold rcRDom
  split_ifs <;> omega

theorem rcR_ind_le1 {q : ℕ} (W : Finset (Fin q)) : ∀ y ∈ rcRInd W, y ≤ 1 := by
  intro y hy
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
  split_ifs <;> omega

/-- **Stages 1 and 2.** -/
theorem rcR_front (ok : RcROk P J) (hst : PointwiseStab)
    (hj : P.prims[J.jp]? = some (pointwiseStabPrim hst))
    {ps : List (Perm (Fin k) × Perm (Fin L.q))} (hps : PairGens e L S.G ps) (svs : List Val)
    (hsv0 : svs[0]? = some (.nat k)) (hsv2 : svs[2]? = some (natList (rcRL (rcRDom e S))))
    (hxd : (rcRL (rcRDom e S)).findIdx (fun t => t == 1) = (e x : ℕ))
    (W R : Finset (Fin L.q)) {sm : List ℕ} (hsm : (rcRSmall (rcRStab S L x)).map Fin.val = sm)
    {d₁ d₂ : Fin L.q} (hd1 : sm.getD 0 0 = d₁) (hd2 : sm.getD (sm.length - 1) 0 = d₂)
    {M Wb : ℕ} (hA : (rcRInV svs ps W R).wt ≤ M) (hW : 10 ^ 6 * (M + 1) ^ 10 ≤ Wb) :
    CpFB P J.st1 (rcRInV svs ps W R) Wb
      ((pointwiseStabPrim hst).bound (.list [encGroup (ps.map encPair),
        encPts [Fin.castAdd L.q (e x)]]) + 10 ^ 22 * (Wb + 1) ^ 8) (rcRQ1 e S L x) ∧
    ∀ R1, rcRQ1 e S L x R1 →
      CpFB P J.st2 (.list [rcRInV svs ps W R, R1]) Wb (10 ^ 11 * (Wb + 1) ^ 12)
        (rcRQ2 e S L x W R (sm.length == 1) d₁ d₂) := by
  have hdl : (rcRL (rcRDom e S)).length = k := by simp [rcRL]
  have hk : k ≤ M := (rcR_In_k hsv2 hdl ps _ _).trans hA
  have hq : L.q ≤ M := (rcR_In_q svs ps (rcR_ind_length W) _).trans hA
  have hW4 : 10 ^ 4 * (M + 1) ^ 8 ≤ Wb := by
    have : (M + 1) ^ 8 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
    omega
  constructor
  · refine (rcR_st1_spec ok hst hj svs _ hsv0 hsv2 hdl (rcR_dom_le1 e) hxd (e x).2 ps _ _ hA hk hq
      hW4).mono le_rfl ?_
    rintro w ⟨qs, hw, -, hcl⟩
    exact ⟨qs, hw, rcR_stab_gens e hps hcl⟩
  · rintro R1 ⟨qs, rfl, hg⟩
    have hsm' := rcR_small_nat (qs.map Prod.snd)
    rw [hg, hsm] at hsm'
    have hR1 : rcRSt1Val (e x) qs = .list [.nat (e x),
        natList ((List.finRange L.q).map (orbitLabels (qs.map Prod.snd))),
        natList (List.range L.q), natList sm] := by
      unfold rcRSt1Val; rw [hsm']
    rw [hR1]
    have hsmlt : ∀ y ∈ sm, y < L.q := by
      intro y hy; rw [← hsm] at hy
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hy; exact c.2
    have hsml : sm.length ≤ L.q := by
      rw [← hsm, List.length_map]
      exact (List.length_filter_le _ _).trans (by simp)
    have hx₀ : ptsKey (rcRTup (e x) [d₁, d₂]) =
        [(e x : ℕ), k + sm.getD 0 0, k + sm.getD (sm.length - 1) 0] := by
      rw [hd1, hd2]; exact rcR_ptsKey_tup (L := L) (e x) d₁ d₂
    have hxM : (e x : ℕ) ≤ M := by have := (e x).2; omega
    refine (rcR_st2_spec ok svs hsv0 ps (rcRInd W) (rcRInd R) _ sm (rcR_ind_length W)
      (rcR_ind_le1 W) (rcR_labs_lt _) (by simp) hsmlt hsml _ hx₀ (rcR_tup_ncard e hps d₁ d₂) hA hk
      hq hxM hW).mono le_rfl ?_
    rintro w ⟨Lt, hw, hL, hLl⟩
    refine ⟨Lt, ?_, rcR_tab_of e hps hL, hLl, ?_⟩
    · rw [hw, hd1, hd2, rcR_uno_eq, hg]
    · intro p hp
      have hm : p.1 ∈ Lt.map Prod.fst := List.mem_map_of_mem hp
      obtain ⟨g, -, hgx⟩ := (hL p.1).1 hm
      rw [← hgx]
      simp [rcRTup]

end Front

end GI.Impl
