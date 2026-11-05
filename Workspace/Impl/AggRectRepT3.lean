module

public import Workspace.Impl.AggRectRepT2
public import Workspace.Impl.AggPre
public import Workspace.Impl.GenNormBudget

@[expose] public section

/-!
# Stage 3 of the representation program, pairs

`rcR_pairF_spec`: in the pair cases the group of the representation comes from one
**Preimage** call (`graphPre_spec`) on the graph pairs `ps` of `G` and the generators of `P`.
-/

namespace GI.Impl

open GI.Lang
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encPerms encPts encGroup gens Preimage)
open Equiv

/-- A pair of two budgets. -/
theorem rcR_mk2B {P : Program} {env : List Val} {W : ℕ} {a b : Expr} {Ca Cb C : ℕ}
    {Qa Qb : Val → Prop} (ha : CpEB P env a W Ca Qa) (hb : CpEB P env b W Cb Qb)
    (hw : ∀ va vb, Qa va → Qb vb → va.wt ≤ W → vb.wt ≤ W → (Val.list [va, vb]).wt ≤ W)
    (h : Ca + Cb + 3 * W + 20 ≤ C) :
    CpEB P env (mk2 a b) W C (fun v => ∃ va vb, Qa va ∧ Qb vb ∧ v = .list [va, vb]) := by
  refine EvalAll.snoc (Ra := fun v c => ∃ va, Qa va ∧ va.wt ≤ W ∧ v = .list [va] ∧
      c ≤ Ca + 2 * W + 12) ?_ hb ?_
  · refine EvalAll.snoc (Ra := fun v c => v = .list [] ∧ c = (Val.list []).wt + 1)
      (EvalAll.nil ⟨rfl, rfl⟩) ha ?_
    rintro va ca vb cb ⟨rfl, rfl⟩ ⟨h1, h2, h3⟩
    refine ⟨[], rfl, vb, h1, h2, rfl, ?_⟩
    have := wt_list1_le vb
    simp only [List.nil_append]
    have : (Val.list []).wt = 4 := by simp
    omega
  · rintro va ca vb cb ⟨va', h1, h2, rfl, h3⟩ ⟨h4, h5, h6⟩
    refine ⟨[va'], rfl, ⟨va', vb, h1, h4, rfl⟩, hw va' vb h1 h4 h2 h5, ?_⟩
    have := hw va' vb h1 h4 h2 h5
    simp only [List.cons_append, List.nil_append]
    omega

/-- The cost of one Preimage call within the bound `W`. -/
theorem rcR_pre_cost (hpre : Preimage) {k q M W : ℕ} (ps : List (Perm (Fin k) × Perm (Fin q)))
    (ms : List (Perm (Fin q)))
    (hms : ∀ m ∈ ms, ∃ p ∈ Subgroup.closure {p | p ∈ ps}, MonoidHom.snd _ _ p = m)
    (hM : preM k q ps ms ≤ 5 * (M + 1) ^ 2) (hW : 10 ^ 6 * (M + 1) ^ 10 ≤ W) :
    (preimagePrim hpre).bound (preimageEnc (pairInst (MonoidHom.snd _ _) ps ms hms)) +
        graphPreK * preM k q ps ms ^ 8 ≤
      (preimagePrim hpre).boundSize W + 10 ^ 14 * (W + 1) ^ 8 := by
  have h1 := normPreimage_wt ps ms hms
  have h4 : preM k q ps ms ^ 4 ≤ (5 * (M + 1) ^ 2) ^ 4 := rcR_pow_mono hM 4
  have h5 : (5 * (M + 1) ^ 2) ^ 4 = 625 * (M + 1) ^ 8 := by ring
  have h6 : (M + 1) ^ 8 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  have hsz := (preimageEnc (pairInst (MonoidHom.snd _ _) ps ms hms)).size_le_wt
  have hb := (preimagePrim hpre).bound_le
    (v := preimageEnc (pairInst (MonoidHom.snd _ _) ps ms hms)) (B := W) (by omega)
  have h7 : preM k q ps ms ≤ W + 1 := by
    have : (M + 1) ^ 2 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
    omega
  have h8 := Nat.mul_le_mul_left graphPreK (rcR_pow_mono h7 8)
  have hK : graphPreK = 10 ^ 14 := rfl
  rw [hK] at h8 ⊢
  omega

section Pair

variable {P : Program} {I : RcRIdx}

set_option maxHeartbeats 4000000 in
/-- **Stage 3, pairs.** -/
theorem rcR_pairF_spec (ok : RcROk P I) (hpre : Preimage)
    (hj : P.prims[I.jpre]? = some (preimagePrim hpre)) {k q : ℕ} (svs : List Val)
    (hsv0 : svs[0]? = some (.nat k)) (ps : List (Perm (Fin k) × Perm (Fin q))) (wl rl : List ℕ)
    (a0 a1 a2 a4 a5 a6 : Val) (ms : List (Perm (Fin q)))
    (hms : ∀ m ∈ ms, ∃ p ∈ Subgroup.closure {p | p ∈ ps}, MonoidHom.snd _ _ p = m) {M W : ℕ}
    (hA : (Val.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl]).wt ≤ M)
    (hk : k ≤ M) (hq : q ≤ M) (hml : ms.length ≤ (M + 1) ^ 2) (hW : 10 ^ 6 * (M + 1) ^ 10 ≤ W)
    (hIn : (Val.list [.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl],
      .list [a0, a1, a2, .list (ms.map encPerm), a4, a5, a6]]).wt ≤ W) :
    CpFB P I.pairF (.list [.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl],
        .list [a0, a1, a2, .list (ms.map encPerm), a4, a5, a6]]) W
      ((preimagePrim hpre).boundSize W + 10 ^ 15 * (W + 1) ^ 8)
      (fun w => ∃ qs : List (Perm (Fin k) × Perm (Fin q)), w = .list [.list (qs.map pairV), .list []] ∧
        qs.length ≤ (k + q) ^ 2 ∧
        Subgroup.closure {p | p ∈ qs} =
          Subgroup.closure {p | p ∈ ps} ⊓ (gens ms).comap (MonoidHom.snd _ _)) := by
  obtain ⟨Av, hAv⟩ : ∃ Av : Val,
      Av = .list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl] := ⟨_, rfl⟩
  obtain ⟨Rv, hRv⟩ : ∃ Rv : Val, Rv = .list [a0, a1, a2, .list (ms.map encPerm), a4, a5, a6] :=
    ⟨_, rfl⟩
  rw [← hAv] at hA hIn ⊢
  rw [← hRv] at hIn ⊢
  have hp1 : M + 1 ≤ (M + 1) ^ 2 := by
    calc M + 1 = (M + 1) ^ 1 := (pow_one _).symm
      _ ≤ (M + 1) ^ 2 := rcR_pow_le_pow (by omega) (by norm_num)
  have hp2 : (M + 1) ^ 2 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  have hp6 : (M + 1) ^ 6 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  have hU : W + 1 ≤ (W + 1) ^ 8 := by
    calc W + 1 = (W + 1) ^ 1 := (pow_one _).symm
      _ ≤ (W + 1) ^ 8 := rcR_pow_le_pow (by omega) (by norm_num)
  have wsv : (Val.list svs).wt < Av.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have wpv : (Val.list (ps.map pairV)).wt < Av.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have wkv : (Val.nat k).wt < (Val.list svs).wt := wt_le_wt_list (List.mem_of_getElem? hsv0)
  have hL8 : 1000 * (W + 1) ≤ (W + 1) ^ 8 := rcR_lin_le (by
    have : 1 ≤ (M + 1) ^ 10 := Nat.one_le_pow _ _ (by omega)
    omega) (by norm_num)
  have wAv : Av.wt < (Val.list [Av, Rv]).wt := wt_le_wt_list (by simp)
  have wRv : Rv.wt < (Val.list [Av, Rv]).wt := wt_le_wt_list (by simp)
  have wmv : (Val.list (ms.map encPerm)).wt < Rv.wt := by rw [hRv]; exact wt_le_wt_list (by simp)
  have dA := (rcRDW.arg (P := P) (vs := [Av, Rv]) (rest := []) (j := 0) (v := Av) hIn rfl).cast hAv
  have dR := (rcRDW.arg (P := P) (vs := [Av, Rv]) (rest := []) (j := 1) (v := Rv) hIn rfl).cast hRv
  have dk := rcRDW.get (rcRDW.get dA (j := 0) (v := .list svs) rfl) hsv0
  have dq := rcRDW.get dA (j := 1) (v := .nat q) rfl
  have dps := rcRDW.get dA (j := 2) (v := .list (ps.map pairV)) rfl
  have dms := rcRDW.get dR (j := 3) (v := .list (ms.map encPerm)) rfl
  have wms : (Val.list (ms.map encPerm)).wt ≤ 52 * (M + 1) ^ 6 := by
    have h1 := wt_list_encPerms_le ms
    have h2 : (ms.length + 1) * (q + 1) ≤ 2 * (M + 1) ^ 3 :=
      calc (ms.length + 1) * (q + 1) ≤ (2 * (M + 1) ^ 2) * (M + 1) :=
            Nat.mul_le_mul (by omega) (by omega)
        _ = 2 * (M + 1) ^ 3 := by ring
    have h3 := rcR_pow_mono h2 2
    have h4 : (2 * (M + 1) ^ 3) ^ 2 = 4 * (M + 1) ^ 6 := by ring
    omega
  have wk2 := wt_list2_le (.nat k) (.nat q)
  have wk := wt_nat_le k
  have wq := wt_nat_le q
  have wI := wt_list3_le (.list [.nat k, .nat q]) (.list (ps.map pairV)) (.list (ms.map encPerm))
  have dI := rcRDW.mk3 (rcRDW.mk2 dk dq (by omega)) dps dms (by omega)
  have hpM : preM k q ps ms ≤ 5 * (M + 1) ^ 2 := by
    unfold preM
    have := length_lt_wt_list (ps.map pairV)
    rw [List.length_map] at this
    omega
  have hc := rcR_pre_cost hpre ps ms hms hpM hW
  have wnil : (Val.list []).wt ≤ 4 := by simp
  refine CpFB.intro ok.pairF ?_
  have hpre' : CpFB P I.pre (.list [.list [.nat k, .nat q], .list (ps.map pairV),
      .list (ms.map encPerm)]) W ((preimagePrim hpre).boundSize W + 10 ^ 14 * (W + 1) ^ 8)
      (fun w => ∃ qs : List (Perm (Fin k) × Perm (Fin q)), w = .list (qs.map pairV) ∧
        qs.length ≤ (k + q) ^ 2 ∧
        Subgroup.closure {p | p ∈ qs} =
          Subgroup.closure {p | p ∈ ps} ⊓ (gens ms).comap (MonoidHom.snd _ _)) := by
    refine FunAll.mono (graphPre_spec hpre ok.pre hj ps ms hms) ?_
    rintro w c ⟨qs, rfl, hl, hcl, hc'⟩
    exact ⟨⟨qs, rfl, hl, hcl⟩, by have := rcR_wt_qs hk hq qs hl; omega, by omega⟩
  have hcall := rcR_callC (C := (preimagePrim hpre).boundSize W + (10 ^ 14 + 1) * (W + 1) ^ 8)
    (rcR_detC dI (C := 100 * W + 100) (by omega) (Q := (· = .list [.list [.nat k, .nat q],
      .list (ps.map pairV), .list (ms.map encPerm)])) rfl) (fun v hv _ => by subst hv; exact hpre')
    (by omega)
  refine (rcR_mk2B hcall (rcR_detC (rcRDW.nil (P := P) (env := [.list [Av, Rv]]) (W := W)
      (by omega)) le_rfl (Q := (· = .list [])) rfl) ?_ (by omega)).mono le_rfl ?_
  · rintro va vb ⟨qs, rfl, hl, -⟩ rfl - -
    have := rcR_wt_qs hk hq qs hl
    have := wt_list2_le (.list (qs.map pairV)) (.list [])
    omega
  · rintro v ⟨va, vb, ⟨qs, rfl, hl, hcl⟩, rfl, rfl⟩
    exact ⟨qs, rfl, hl, hcl⟩

end Pair

end GI.Impl
