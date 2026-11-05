module

public import Workspace.Impl.AggCertMvBase
public import Workspace.Impl.AggLiftChild

@[expose] public section

/-!
# The modules of the move program, within one budget

For every module that the move program calls, its specification in the form `CpFB`: the
output, a weight at most `W`, and a cost at most `cpG W`, when the sizes of the inputs are at
most polynomial in `W`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Endpoint GI.LocalGroups Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

section Bud

variable (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) {W : ℕ}

theorem cpG_poly : 10 ^ 25 * W ^ 24 ≤ cpG hst hpre hm W := by unfold cpG; omega

theorem cpG_pre4 : (preimagePrim hpre).boundSize (1000 * W ^ 4) ≤ cpG hst hpre hm W := by
  unfold cpG; omega

theorem cpG_pre : (preimagePrim hpre).boundSize W ≤ cpG hst hpre hm W := by
  refine le_trans (boundSize_mono _ ?_) (cpG_pre4 hst hpre hm)
  rcases Nat.eq_zero_or_pos W with h | h
  · simp [h]
  · have : W ≤ W ^ 4 := Nat.le_self_pow (by omega) _
    omega

theorem cpG_stab : (pointwiseStabPrim hst).boundSize (100 * W ^ 4) ≤ cpG hst hpre hm W := by
  unfold cpG; omega

theorem cpG_find : ckFindCost hm W ≤ cpG hst hpre hm W := by unfold cpG; omega

theorem cpG_card : (2 * W + 2) * cardCost hst (2 * W) ≤ cpG hst hpre hm W := by unfold cpG; omega

/-- A polynomial `K (W + 1)^d` with `K ≤ 10¹⁷` and `d ≤ 24`, for `W ≥ 1`, is within
`10²⁵ W²⁴`. -/
theorem cp_poly_le {K d : ℕ} (hK : K ≤ 10 ^ 17) (hd : d ≤ 24) (hW : 1 ≤ W) :
    K * (W + 1) ^ d ≤ 10 ^ 25 * W ^ 24 := by
  have a : (W + 1) ^ d ≤ (2 * W) ^ 24 :=
    (Nat.pow_le_pow_left (by omega) d).trans (Nat.pow_le_pow_right (by omega) hd)
  have b : (2 * W) ^ 24 = 2 ^ 24 * W ^ 24 := by ring
  have c : K * (W + 1) ^ d ≤ 10 ^ 17 * (2 ^ 24 * W ^ 24) := Nat.mul_le_mul hK (b ▸ a)
  have : 10 ^ 17 * (2 ^ 24 * W ^ 24) ≤ 10 ^ 25 * W ^ 24 := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by norm_num)
  omega

theorem cpG_pre_poly :
    (preimagePrim hpre).boundSize W + 10 ^ 25 * W ^ 24 ≤ cpG hst hpre hm W := by
  have h : (preimagePrim hpre).boundSize W ≤ (preimagePrim hpre).boundSize (1000 * W ^ 4) := by
    refine boundSize_mono _ ?_
    rcases Nat.eq_zero_or_pos W with h | h
    · simp [h]
    · have : W ≤ W ^ 4 := Nat.le_self_pow (by omega) _
      omega
  unfold cpG; omega

theorem cpG_pre4_poly :
    (preimagePrim hpre).boundSize (1000 * W ^ 4) + 10 ^ 25 * W ^ 24 ≤ cpG hst hpre hm W := by
  unfold cpG; omega

end Bud

section Mods

variable (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) {W : ℕ} {P : Program}

/-- **Tail.** -/
theorem cp_bud_tail {b : ℕ} (h : P.HasAt b (tailFuns b)) (x : Val) (xs : List Val)
    (hw : (Val.list (x :: xs)).wt ≤ W) :
    CpFB P b (.list (x :: xs)) W (cpG hst hpre hm W) (fun w => w = .list xs) := by
  have h1 := length_lt_wt_list (x :: xs)
  simp only [List.length_cons] at h1
  have h2 : (Val.list xs).wt ≤ (Val.list (x :: xs)).wt :=
    wt_list_sublist (List.sublist_cons_self x xs)
  refine CpFB.det (GI.Lang.tail_spec h x xs) ?_ (by omega) rfl
  have a : loopModK * (xs.length + 1) * (3 * (Val.list (x :: xs)).wt + 1) ≤
      1000 * (W + 1) * (3 * W + 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have b : 1000 * (W + 1) * (3 * W + 3) = 3000 * (W + 1) ^ 2 := by ring
  have c := cp_poly_le (W := W) (K := 3000) (d := 2) (by norm_num) (by norm_num) (by omega)
  have := cpG_poly hst hpre hm (W := W)
  have e : loopModK = 1000 := rfl
  rw [e] at a ⊢
  omega

variable {k : ℕ} {Ω C : Type} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}

/-- **`P_T` in graph form.** -/
theorem cp_bud_pt {b jpre : ℕ} (hb : P.HasAt b (ptFuns b jpre))
    (hj : P.prims[jpre]? = some (preimagePrim hpre)) {ps : List (Perm (Fin k) × Perm (Fin L.q))}
    (hps : PairGens e L S.G ps) (hpl : ps.length ≤ (k + L.q) ^ 2)
    (πd : S.domGroup →* alternatingGroup (Fin L.q))
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) (T : Finset (Fin L.q))
    (hW : 10 ^ 10 * (k + L.q + 1) ^ 12 ≤ W) :
    CpFB P b (.list [.list [.nat k, .nat L.q], .list (ps.map pairV), indT T]) W
      (cpG hst hpre hm W) (fun w => ∃ qs : List (Perm (Fin k) × Perm (Fin L.q)),
        w = .list (qs.map pairV) ∧ qs.length ≤ (k + L.q) ^ 2 ∧
        PairGens e L (S.liftGroup (Pgrp S.domGroup πd T)) qs) := by
  obtain ⟨f1, f2, -, f24, f46, -, -, -, f9, -⟩ := cp_pow_facts k L.q
  have w12 : (k + L.q + 1) ^ 6 ≤ (k + L.q + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
  refine FunAll.mono (ptGraph_spec hpre hb hj hps πd hπ T) ?_
  rintro w cw ⟨qs, rfl, hl, hq, hc⟩
  refine ⟨⟨qs, rfl, hl, hq⟩, ?_, ?_⟩
  · have := cp_wt_gp (k := k) (q := L.q) hl
    unfold gpV at this
    omega
  · -- the preimage instance
    have hpw := lcPreEnc_wt ps (mtGens L.q T) (mtGens_snd hps T)
    have hlen : (mtGens L.q T).length = L.q ^ 3 := by simp [mtGens]
    have hM : preM k L.q ps (mtGens L.q T) ≤ 4 * (k + L.q + 1) ^ 3 := by
      unfold preM
      rw [hlen]
      have : L.q ^ 3 ≤ (k + L.q + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      have : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      have : k + L.q + 1 ≤ (k + L.q + 1) ^ 3 := Nat.le_self_pow (by omega) _
      have : 1 ≤ (k + L.q + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    have hM4 : preM k L.q ps (mtGens L.q T) ^ 4 ≤ 256 * (k + L.q + 1) ^ 12 := by
      have := Nat.pow_le_pow_left hM 4
      have e : (4 * (k + L.q + 1) ^ 3) ^ 4 = 256 * (k + L.q + 1) ^ 12 := by ring
      omega
    have hsz := (GI.Lang.preimageEnc (pairInst (MonoidHom.snd _ _) ps (mtGens L.q T)
      (mtGens_snd hps T))).size_le_wt
    have hb1 := (preimagePrim hpre).bound_le (v := GI.Lang.preimageEnc (pairInst (MonoidHom.snd _ _)
      ps (mtGens L.q T) (mtGens_snd hps T))) (B := W) (by omega)
    have hpt : ptM k L.q ps ≤ W := by
      unfold ptM
      have : (k + L.q + 1) ^ 2 ≤ (k + L.q + 1) ^ 12 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have h2 : ptK * ptM k L.q ps ^ 24 ≤ ptK * (W + 1) ^ 24 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 24)
    have h3 := cp_poly_le (W := W) (K := ptK) (d := 24) (by simp [ptK]) le_rfl (by omega)
    have := cpG_poly hst hpre hm (W := W)
    have := cpG_pre_poly hst hpre hm (W := W)
    omega

end Mods

end GI.Impl
