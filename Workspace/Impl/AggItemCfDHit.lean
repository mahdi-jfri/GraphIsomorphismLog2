module

public import Workspace.Impl.AggItemCfDSplit
public import Workspace.Impl.AggStructDesHit

@[expose] public section

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited
open GI.Machine (BinOp)

def ItCfDSplitOK (P : Program) (sp : ℕ) : Prop :=
  ∀ {dl tl : List ℕ} {q κ : ℕ}, ItCfDCtx dl tl q κ → ∀ (m : ℕ),
    stDBal (stDV dl tl q κ m) q = false → ∀ {M : ℕ},
    (Val.list [.list [stDA dl tl q κ, .nat m], natList (stDV dl tl q κ m)]).wt ≤ M →
    FunDet P sp (.list [.list [stDA dl tl q κ, .nat m], natList (stDV dl tl q κ m)])
      (boolVal (stDSplit dl tl q κ m (stDV dl tl q κ m)
        ((stDV dl tl q κ m).getD (stDZ (stDV dl tl q κ m) q) 0)))
      (stDSplitK * (M + 1) ^ 8)

theorem itCfD_split_ok {P : Program} {f fd fr ad rb cf h dv dv' cb rf df : ℕ}
    (hf : P.funs[f]? = some (stDSplitF fd fr ad rb cf))
    (hfd : P.HasAt fd (findFuns fd dv)) (hdv : P.funs[dv]? = some (stDDomF dv'))
    (hdv' : P.funs[dv']? = some (stDDomVF cb)) (hcb : P.HasAt cb (countFuns cb))
    (hfr : P.HasAt fr (findFuns fr rf)) (hrf : P.funs[rf]? = some stDRefF)
    (had : P.HasAt ad (anyFuns ad df)) (hdf : P.funs[df]? = some (stDDifF rf cf))
    (hrb : P.HasAt rb (rangeFuns rb)) (hcf : P.funs[cf]? = some (stDColF h))
    (hh : P.HasAt h (stDHorFuns h)) : ItCfDSplitOK P f :=
  fun hc m hb _ hM => itCfD_split_spec hf hfd hdv hdv' hcb hfr hrf had hdf hrb hcf hh hc m hb hM


theorem itCfD_hit2_spec {P : Program} {f ad rb sp dv dv' cb : ℕ}
    (hf : P.funs[f]? = some (stDHit2F ad rb sp))
    (had : P.HasAt ad (anyFuns ad dv)) (hdv : P.funs[dv]? = some (stDDomF dv'))
    (hdv' : P.funs[dv']? = some (stDDomVF cb)) (hcb : P.HasAt cb (countFuns cb))
    (hrb : P.HasAt rb (rangeFuns rb)) (hsp : ItCfDSplitOK P sp)
    {dl tl : List ℕ} {q κ : ℕ} (hc : ItCfDCtx dl tl q κ) {m : ℕ} (hm : m ≤ κ) {M : ℕ}
    (hM : (Val.list [.list [stDA dl tl q κ, .nat m], natList (stDV dl tl q κ m)]).wt ≤ M) :
    FunDet P f (.list [.list [stDA dl tl q κ, .nat m], natList (stDV dl tl q κ m)])
      (boolVal (stDHit dl tl q κ m)) (stDHit2K * (M + 1) ^ 8) := by
  have hVl := stDV_length dl tl q κ m
  have hsp' := @hsp dl tl q κ hc m
  unfold stDHit
  obtain ⟨V, hVd⟩ : ∃ V, stDV dl tl q κ m = V := ⟨_, rfl⟩
  rw [hVd] at hVl hM hsp' ⊢
  have hAw : (stDA dl tl q κ).wt < M := by
    have h1 : (Val.list [stDA dl tl q κ, .nat m]).wt <
        (Val.list [.list [stDA dl tl q κ, .nat m], natList V]).wt := wt_le_wt_list (by simp)
    have h2 : (stDA dl tl q κ).wt < (Val.list [stDA dl tl q κ, .nat m]).wt :=
      wt_le_wt_list (by simp)
    omega
  have hmw : (Val.nat m).wt < M := by
    have h1 : (Val.list [stDA dl tl q κ, .nat m]).wt <
        (Val.list [.list [stDA dl tl q κ, .nat m], natList V]).wt := wt_le_wt_list (by simp)
    have h2 : (Val.nat m).wt < (Val.list [stDA dl tl q κ, .nat m]).wt :=
      wt_le_wt_list (by simp)
    omega
  have hqM : q < M := by have := hc.le_wt.2.2; omega
  have hκM : κ < M := by have := hc.le_wt.2.1; omega
  have hmM : m < M := by omega
  have hVB : (natList V).wt ≤ 2 * M := by
    have hw : (natList V).wt <
      (Val.list [.list [stDA dl tl q κ, .nat m], natList V]).wt := wt_le_wt_list (by simp)
    omega
  have hY1 : 1 ≤ M + 1 := by omega
  have hqq : q * q ≤ (M + 1) ^ 2 := by
    have := Nat.mul_le_mul (show q ≤ M + 1 by omega) (show q ≤ M + 1 by omega); nlinarith
  have hY2 : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  obtain ⟨W, hW⟩ : ∃ W, W = 1000 * (M + 1) ^ 2 + 1000 := ⟨_, rfl⟩
  have ha_eq : (Val.list [.list [Val.list [natList dl, natList tl, .nat q, .nat κ], .nat m],
      natList V]).wt = (Val.list [.list [stDA dl tl q κ, .nat m], natList V]).wt := rfl
  obtain ⟨gA, gm, gV, gq, -⟩ := stDS_parts (P := P) (m := m) (Vv := natList V)
    (Avs := [natList dl, natList tl, .nat q, .nat κ]) rfl rfl [] (W := W) (by omega) (by omega)
    (by omega)
  have gκ : StDC P [.list [.list [stDA dl tl q κ, .nat m], natList V]] stDSκ (.nat κ) 7 0 W :=
    StDC.get gA (StDC.nat 3 (by omega)) rfl (by have := wt_nat_le κ; omega)
  have gc1 := StDC.arith' gm gκ (op := .lt) (z := BinOp.eval .lt m κ) rfl
    (by simp only [BinOp.eval]; split_ifs <;> omega)
  have gc2 := StDC.arith' (StDC.arith' gm (StDC.nat 1 (by omega)) (op := .add)
    (show BinOp.eval .add m 1 = m + 1 from rfl) (by omega)) gκ (op := .lt)
    (z := BinOp.eval .lt (m + 1) κ) rfl (by simp only [BinOp.eval]; split_ifs <;> omega)
  -- the class test over all labels
  have hcV : (Val.list [natList V, .nat q]).wt ≤ 20 * (2 * M + 1) ^ 2 :=
    itCfD_ctxV_wt hVB hVl (by omega)
  have hM2 : (2 * M + 1) ^ 2 ≤ 4 * (M + 1) ^ 2 := by nlinarith
  have hrq : (natList (List.range q)).wt ≤ 5 * (M + 1) ^ 2 := by
    have := wt_natList_le_sq (xs := List.range q) (B := q) (fun x hx => (List.mem_range.1 hx).le)
      (by simp)
    have : (q + 1) ^ 2 ≤ (M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  obtain ⟨E1, hE1⟩ : ∃ E1, 10000 * (q + 1) ^ 3 = E1 := ⟨_, rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ E2, q * (2 * itCfDDomK * (2 * M + 1) ^ 3) +
      loopModK * (200 * (M + 1) ^ 2 + 1) * (3 * (200 * (M + 1) ^ 2) + 3) = E2 := ⟨_, rfl⟩
  obtain ⟨E3, hE3⟩ : ∃ E3, stDSplitK * (M + 1) ^ 8 = E3 := ⟨_, rfl⟩
  have hr := st_range_det hrb q
  rw [hE1] at hr
  have hdom := st_any_det had (c := .list [natList V, .nat q]) (n := q) (t := stDDom V q)
    (B := 2 * itCfDDomK * (2 * M + 1) ^ 3) (X := 200 * (M + 1) ^ 2)
    (fun i hi => itCfD_dom_spec hdv hdv' hcb hVB hVl (by omega) hi)
    (by have := wt_list2_le (.list [natList V, .nat q]) (natList (List.range q)); omega)
    (by omega)
  rw [hE2] at hdom
  have gany := StDC.call (StDC.mk2 (StDC.mk2 gV gq (by omega) (by omega))
    (StDC.call gq hr (by omega))
    (by have := wt_list2_le (.list [natList V, .nat q]) (natList (List.range q)); omega)
    (by omega)) hdom (by have := wt_boolVal_le ((List.range q).any (stDDom V q)); omega)
  have hW1 : (boolVal true).wt ≤ W := by have := wt_boolVal_le true; omega
  have hW0 : (boolVal false).wt ≤ W := by have := wt_boolVal_le false; omega
  have hcost : 60 * (W + 1) + (E1 + E2 + E3) ≤ stDHit2K * (M + 1) ^ 8 := by
    have hP := fun i j (h : i ≤ j) => Nat.pow_le_pow_right hY1 h
    have t1 : q * (2 * itCfDDomK * (2 * M + 1) ^ 3) ≤ 16 * itCfDDomK * (M + 1) ^ 4 := by
      have := Nat.pow_le_pow_left (show 2 * M + 1 ≤ 2 * (M + 1) by omega) 3
      calc q * (2 * itCfDDomK * (2 * M + 1) ^ 3) ≤ (M + 1) * (2 * itCfDDomK * (2 * (M + 1)) ^ 3) :=
            Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ this)
        _ = 16 * itCfDDomK * (M + 1) ^ 4 := by ring
    have t2 : loopModK * (200 * (M + 1) ^ 2 + 1) * (3 * (200 * (M + 1) ^ 2) + 3) ≤
        loopModK * 201 * 603 * (M + 1) ^ 4 := by
      have h1 : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      calc _ ≤ loopModK * (201 * (M + 1) ^ 2) * (603 * (M + 1) ^ 2) :=
            st_mul3 le_rfl (by omega) (by omega)
        _ = _ := by ring
    have t6 : 10000 * (q + 1) ^ 3 ≤ 80000 * (M + 1) ^ 3 := by
      have := Nat.pow_le_pow_left (show q + 1 ≤ 2 * (M + 1) by omega) 3
      calc _ ≤ 10000 * (2 * (M + 1)) ^ 3 := Nat.mul_le_mul_left _ this
        _ = _ := by ring
    have hp2 := hP 2 8 (by norm_num)
    have hp3 := hP 3 8 (by norm_num)
    have hp4 := hP 4 8 (by norm_num)
    rw [← hE1, ← hE2, ← hE3, hW]
    simp only [stDHit2K, stDSplitK, itCfDDomK, loopModK] at t1 t2 ⊢
    norm_num at t1 t2 ⊢
    linarith
  by_cases h1 : m < κ
  · have hx1 : BinOp.eval .lt m κ ≠ 0 := by simp [BinOp.eval, h1]
    by_cases h2 : (List.range q).any (stDDom V q) = true
    · have hb : stDBal V q = false := by simp [stDBal, h2]
      have hx2 : ((List.range q).any (stDDom V q)).toNat ≠ 0 := by simp [h2]
      by_cases h3 : m + 1 < κ
      · have hx3 : BinOp.eval .lt (m + 1) κ ≠ 0 := by simp [BinOp.eval, h3]
        have hs := hsp' hb (M := M) hM
        rw [hE3] at hs
        have gsp := StDC.call (StDC.var' (P := P)
          (env := [.list [.list [stDA dl tl q κ, .nat m], natList V]]) (i := 0) rfl
          (W := W) (by omega)) hs (by
            have := wt_boolVal_le (stDSplit dl tl q κ m V (V.getD (stDZ V q) 0)); omega)
        have g := st_iteT (e := .nat 0) gc1 hx1 (st_iteT (e := .nat 1) gany hx2
          (st_iteT (e := .nat 0) gc2 hx3 gsp (by
            have := wt_boolVal_le (stDSplit dl tl q κ m V (V.getD (stDZ V q) 0)); omega))
            (by have := wt_boolVal_le (stDSplit dl tl q κ m V (V.getD (stDZ V q) 0)); omega))
          (by have := wt_boolVal_le (stDSplit dl tl q κ m V (V.getD (stDZ V q) 0)); omega)
        simp only [decide_eq_true h1, decide_eq_true h3, hb, Bool.true_and, Bool.false_or]
        exact StDC.funDet hf (g.mono (n' := 60) (E' := E1 + E2 + E3) (by omega) (by omega)) hcost
      · have hx3 : BinOp.eval .lt (m + 1) κ = 0 := by simp [BinOp.eval, h3]
        have g := st_iteT (e := .nat 0) gc1 hx1 (st_iteT (e := .nat 1) gany hx2
          (st_iteF (t := .call sp (.var 0)) gc2 hx3 (StDC.nat 0 (by omega)) hW0) hW0) hW0
        simp only [decide_eq_true h1, decide_eq_false h3, hb, Bool.true_and, Bool.false_or,
          Bool.false_and]
        exact StDC.funDet hf (g.mono (n' := 60) (E' := E1 + E2 + E3) (by omega) (by omega)) hcost
    · have hx2 : ((List.range q).any (stDDom V q)).toNat = 0 := by simp at h2 ⊢; simpa using h2
      have hb : stDBal V q = true := by simp only [stDBal]; simpa using h2
      have g := st_iteT (e := .nat 0) gc1 hx1 (st_iteF
        (t := .ite (.arith .lt (.arith .add stDSm (.nat 1)) stDSκ) (.call sp (.var 0)) (.nat 0))
        gany hx2 (StDC.nat 1 (by omega)) hW1) hW1
      simp only [decide_eq_true h1, hb, Bool.true_and, Bool.true_or]
      exact StDC.funDet hf (g.mono (n' := 60) (E' := E1 + E2 + E3) (by omega) (by omega)) hcost
  · have hx1 : BinOp.eval .lt m κ = 0 := by simp [BinOp.eval, h1]
    have g := st_iteF (t := .ite (.call ad (mk2 (mk2 stDSV stDSq) (.call rb stDSq)))
      (.ite (.arith .lt (.arith .add stDSm (.nat 1)) stDSκ) (.call sp (.var 0)) (.nat 0))
      (.nat 1)) gc1 hx1 (StDC.nat 0 (by omega)) hW0
    simp only [decide_eq_false h1, Bool.false_and]
    exact StDC.funDet hf (g.mono (n' := 60) (E' := E1 + E2 + E3) (by omega) (by omega)) hcost


def ItCfDHitOK (P : Program) (ht : ℕ) : Prop :=
  ∀ {dl tl : List ℕ} {q κ : ℕ}, ItCfDCtx dl tl q κ → ∀ {m : ℕ}, m ≤ κ → ∀ {M : ℕ},
    (Val.list [stDA dl tl q κ, .nat m]).wt ≤ M →
    FunDet P ht (.list [stDA dl tl q κ, .nat m]) (boolVal (stDHit dl tl q κ m))
      (stDHitK * (M + 1) ^ 16)

theorem itCfD_hit_ok {P : Program} {f h2 vm ad rb sp dv dv' cb mb vf cf h : ℕ}
    (hf : P.funs[f]? = some (stDHitF h2 vm))
    (hh2 : P.funs[h2]? = some (stDHit2F ad rb sp))
    (had : P.HasAt ad (anyFuns ad dv)) (hdv : P.funs[dv]? = some (stDDomF dv'))
    (hdv' : P.funs[dv']? = some (stDDomVF cb)) (hcb : P.HasAt cb (countFuns cb))
    (hrb : P.HasAt rb (rangeFuns rb)) (hsp : ItCfDSplitOK P sp)
    (hvm : P.funs[vm]? = some (stDVMapF mb rb))
    (hmb : P.HasAt mb (mapFuns mb vf)) (hvf : P.funs[vf]? = some (stDVF cf))
    (hcf : P.funs[cf]? = some (stDColF h)) (hh : P.HasAt h (stDHorFuns h)) :
    ItCfDHitOK P f := by
  intro dl tl q κ hc m hm M hM
  have hV := itCfD_v_spec hvm hmb hrb hvf hcf hh hc m hM
  have hVw := hc.wt_stDV m
  have hAw : (stDA dl tl q κ).wt < M := by
    have : (stDA dl tl q κ).wt < (Val.list [stDA dl tl q κ, .nat m]).wt :=
      wt_le_wt_list (by simp)
    omega
  obtain ⟨M', hM'⟩ : ∃ M', 50 * (M + 1) ^ 2 = M' := ⟨_, rfl⟩
  have hM2 : (2 * (stDA dl tl q κ).wt + 1) ^ 2 ≤ 4 * (M + 1) ^ 2 := by nlinarith
  have hY2 : M + 1 ≤ (M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hw2 : (Val.list [.list [stDA dl tl q κ, .nat m], natList (stDV dl tl q κ m)]).wt ≤ M' := by
    have := wt_list2_le (.list [stDA dl tl q κ, .nat m]) (natList (stDV dl tl q κ m))
    omega
  have h2 := itCfD_hit2_spec hh2 had hdv hdv' hcb hrb hsp hc hm hw2
  obtain ⟨E1, hE1⟩ : ∃ E1, stDVMK * (M + 1) ^ 3 = E1 := ⟨_, rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ E2, stDHit2K * (M' + 1) ^ 8 = E2 := ⟨_, rfl⟩
  rw [hE1] at hV
  rw [hE2] at h2
  obtain ⟨W, hW⟩ : ∃ W, W = M' := ⟨_, rfl⟩
  have g0 := StDC.var' (P := P) (env := [.list [stDA dl tl q κ, .nat m]]) (i := 0) rfl
    (W := W) (by omega)
  have g := StDC.call (StDC.mk2 g0 (StDC.call g0 hV (by omega)) (by omega) (by omega)) h2
    (by have := wt_boolVal_le (stDHit dl tl q κ m); omega)
  refine StDC.funDet hf g ?_
  have hY1 : 1 ≤ M + 1 := by omega
  have hP := fun i j (h : i ≤ j) => Nat.pow_le_pow_right hY1 h
  have hp2 := hP 2 16 (by norm_num)
  have hp3 := hP 3 16 (by norm_num)
  have t2 : (M' + 1) ^ 8 ≤ 51 ^ 8 * (M + 1) ^ 16 := by
    have : M' + 1 ≤ 51 * (M + 1) ^ 2 := by
      have : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    calc (M' + 1) ^ 8 ≤ (51 * (M + 1) ^ 2) ^ 8 := Nat.pow_le_pow_left this 8
      _ = 51 ^ 8 * (M + 1) ^ 16 := by ring
  rw [← hE1, ← hE2, hW, ← hM']
  rw [← hM'] at t2
  simp only [stDHitK, stDHit2K, stDVMK]
  norm_num at t2 ⊢
  nlinarith

end GI.Impl
