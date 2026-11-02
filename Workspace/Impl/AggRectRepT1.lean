import Workspace.Impl.AggRectRepS6
import Workspace.Impl.AggCertBud
import Workspace.Lang.Lib.SmallGroup

/-!
# Stage 1 of the representation program

`rcR_st1_spec`: on `A = [sv, q, ⟨ps⟩, W, R]`, stage 1 computes the base point `x` (the first
domain position, `findEq 1`), graph pairs `qs` of `G_x` (**PointwiseStab** through
`graphStabP`), the orbit labels of their second parts, `range q`, and the labels whose orbit has
at most two points.

All values stay below a bound `W` with `10⁴ (M + 1)⁸ ≤ W`, for a bound `M` of the input weight,
`k`, `q` and the number of pairs.
-/

namespace GI.Impl

open GI.Lang
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encPerms encPts PointwiseStab gens)
open Equiv

/-! ### Budgets with stated costs -/

theorem rcR_letC {P : Program} {env : List Val} {W : ℕ} {e body : Expr} {Ca Cb C : ℕ}
    {Qa Q : Val → Prop} (ha : CpEB P env e W Ca Qa)
    (hb : ∀ v, Qa v → v.wt ≤ W → CpEB P (env ++ [v]) body W Cb Q) (h : Ca + Cb + W + 1 ≤ C) :
    CpEB P env (.letE e body) W C Q :=
  (CpEB.letE ha hb).mono h fun _ h => h

theorem rcR_callC {P : Program} {env : List Val} {W : ℕ} {f : ℕ} {a : Expr} {Ca Cb C : ℕ}
    {Qa Q : Val → Prop} (ha : CpEB P env a W Ca Qa)
    (hb : ∀ v, Qa v → v.wt ≤ W → CpFB P f v W Cb Q) (h : Ca + Cb + W + 1 ≤ C) :
    CpEB P env (.call f a) W C Q :=
  (CpEB.call ha hb).mono h fun _ h => h

theorem rcR_detC {P : Program} {env : List Val} {W : ℕ} {e : Expr} {v : Val} {c C : ℕ}
    {Q : Val → Prop} (h : rcRDW P env e v W c) (hc : c ≤ C) (hq : Q v) : CpEB P env e W C Q :=
  CpEB.det h.1 hc h.2 hq

/-! ### Bounds -/

theorem rcR_pow_mono {a b : ℕ} (h : a ≤ b) (d : ℕ) : a ^ d ≤ b ^ d := Nat.pow_le_pow_left h d

theorem rcR_pow_le_pow {a i j : ℕ} (ha : 1 ≤ a) (h : i ≤ j) : a ^ i ≤ a ^ j :=
  Nat.pow_le_pow_right ha h

/-- The weight of the graph pairs of a stabilizer. -/
theorem rcR_wt_qs {k q M : ℕ} (hk : k ≤ M) (hq : q ≤ M) (qs : List (Perm (Fin k) × Perm (Fin q)))
    (hl : qs.length ≤ (k + q) ^ 2) : (Val.list (qs.map pairV)).wt ≤ 3200 * (M + 1) ^ 6 := by
  have h1 := wt_pairList_le qs
  have h2 : (k + q) ^ 2 ≤ (2 * M + 1) ^ 2 := rcR_pow_mono (by omega) 2
  have h3 : pM k q qs ≤ 4 * (M + 1) ^ 2 := by
    unfold pM; nlinarith
  have h4 : pM k q qs ^ 3 ≤ (4 * (M + 1) ^ 2) ^ 3 := rcR_pow_mono h3 3
  have h5 : (4 * (M + 1) ^ 2) ^ 3 = 64 * (M + 1) ^ 6 := by ring
  omega

/-- The weight of the encoded second parts. -/
theorem rcR_wt_snds {k q M : ℕ} (hk : k ≤ M) (hq : q ≤ M)
    (qs : List (Perm (Fin k) × Perm (Fin q))) (hl : qs.length ≤ (k + q) ^ 2) :
    (Val.list ((qs.map Prod.snd).map encPerm)).wt ≤ 208 * (M + 1) ^ 6 := by
  have h1 := wt_list_encPerms_le (qs.map Prod.snd)
  rw [List.length_map] at h1
  have h2 : (k + q) ^ 2 ≤ (2 * M + 1) ^ 2 := rcR_pow_mono (by omega) 2
  have h3 : (qs.length + 1) * (q + 1) ≤ 4 * (M + 1) ^ 3 := by
    have : qs.length + 1 ≤ 4 * (M + 1) ^ 2 := by nlinarith
    calc (qs.length + 1) * (q + 1) ≤ (4 * (M + 1) ^ 2) * (M + 1) :=
          Nat.mul_le_mul this (by omega)
      _ = 4 * (M + 1) ^ 3 := by ring
  have h4 : ((qs.length + 1) * (q + 1)) ^ 2 ≤ (4 * (M + 1) ^ 3) ^ 2 := rcR_pow_mono h3 2
  have h5 : (4 * (M + 1) ^ 3) ^ 2 = 16 * (M + 1) ^ 6 := by ring
  omega

theorem rcR_wt_range (q M : ℕ) (hq : q ≤ M) : (natList (List.range q)).wt ≤ 5 * (M + 1) ^ 2 := by
  have := wt_natList_le_sq (xs := List.range q) (B := M) (fun x hx => by
    rw [List.mem_range] at hx; omega) (by rw [List.length_range]; exact hq)
  exact this

theorem rcR_wt_filter (l : List ℕ) (t : ℕ → Bool) : (natList (l.filter t)).wt ≤ (natList l).wt :=
  wt_list_sublist ((List.filter_sublist (p := t) (l := l)).map Val.nat)

end GI.Impl

namespace GI.Impl

open GI.Lang
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encPerms encPts encGroup PointwiseStab gens)
open Equiv

/-! ### Stage 1 -/

/-- The second entry of a list value. -/
def rcRSndV : Val → Val
  | .list (_ :: b :: _) => b
  | _ => .nat 0

theorem rcR_snds_eq {k q : ℕ} (qs : List (Perm (Fin k) × Perm (Fin q))) :
    (qs.map pairV).map rcRSndV = (qs.map Prod.snd).map encPerm := by
  simp only [List.map_map]; rfl

/-- **The second parts of the graph pairs.** -/
theorem rcR_mSnd_spec {P : Program} {I : RcRIdx} (ok : RcROk P I) {k q : ℕ}
    (qs : List (Perm (Fin k) × Perm (Fin q))) {W : ℕ}
    (hin : (Val.list [.nat 0, .list (qs.map pairV)]).wt ≤ W)
    (hout : (Val.list ((qs.map Prod.snd).map encPerm)).wt ≤ W) :
    FunDet P I.mSnd (.list [.nat 0, .list (qs.map pairV)])
      (.list ((qs.map Prod.snd).map encPerm)) (3100 * (W + 1) ^ 3) := by
  have h := rcR_mapW1 ok.mSnd (c := .nat 0) (xs := qs.map pairV) (g := rcRSndV) (K := 10) (W := W)
    (fun v hv => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hv
      exact rcR_g1_spec ok.g1 (.nat 0) (encPerm p.1) (encPerm p.2) [])
    hin (by rw [rcR_snds_eq]; exact hout)
  rw [rcR_snds_eq] at h
  exact h

/-- The value of stage 1. -/
noncomputable def rcRSt1Val {k q : ℕ} (x : ℕ) (qs : List (Perm (Fin k) × Perm (Fin q))) : Val :=
  .list [.nat x, natList ((List.finRange q).map (orbitLabels (qs.map Prod.snd))),
    natList (List.range q), natList ((List.range q).filter fun c => decide
      ((((List.finRange q).map (orbitLabels (qs.map Prod.snd))).count
        (((List.finRange q).map (orbitLabels (qs.map Prod.snd))).getD c 0)) ≤ 2))]

section St1

variable {P : Program} {I : RcRIdx}

set_option maxHeartbeats 4000000 in
/-- **Stage 1.** -/
theorem rcR_st1_spec (ok : RcROk P I) (hst : PointwiseStab)
    (hj : P.prims[I.jp]? = some (pointwiseStabPrim hst)) {k q : ℕ} (svs : List Val)
    (dl : List ℕ) (hsv0 : svs[0]? = some (.nat k)) (hsv2 : svs[2]? = some (natList dl))
    (hdl : dl.length = k) (hdl1 : ∀ x ∈ dl, x ≤ 1) {x : ℕ} (hx : dl.findIdx (· == 1) = x)
    (hxk : x < k) (ps : List (Perm (Fin k) × Perm (Fin q))) (Wv Rv : Val) {M W : ℕ}
    (hA : (Val.list [.list svs, .nat q, .list (ps.map pairV), Wv, Rv]).wt ≤ M)
    (hk : k ≤ M) (hq : q ≤ M) (hW : 10 ^ 4 * (M + 1) ^ 8 ≤ W) :
    CpFB P I.st1 (.list [.list svs, .nat q, .list (ps.map pairV), Wv, Rv]) W
      ((pointwiseStabPrim hst).bound (.list [encGroup (ps.map encPair),
        encPts [(⟨x, by omega⟩ : Fin (k + q))]]) + 10 ^ 22 * (W + 1) ^ 8)
      (fun w => ∃ qs : List (Perm (Fin k) × Perm (Fin q)), w = rcRSt1Val x qs ∧
        qs.length ≤ (k + q) ^ 2 ∧
        Subgroup.closure {p | p ∈ qs} = Subgroup.closure {p | p ∈ ps} ⊓
          fixPts k q [(⟨x, by omega⟩ : Fin (k + q))]) := by
  obtain ⟨A, hAv⟩ : ∃ A : Val, A = .list [.list svs, .nat q, .list (ps.map pairV), Wv, Rv] :=
    ⟨_, rfl⟩
  rw [← hAv] at hA ⊢
  have hM1 : M + 1 ≤ (M + 1) ^ 8 := by
    calc M + 1 = (M + 1) ^ 1 := (pow_one _).symm
      _ ≤ (M + 1) ^ 8 := rcR_pow_le_pow (by omega) (by norm_num)
  have hMW : 10 ^ 4 * (M + 1) ≤ W := le_trans (Nat.mul_le_mul_left _ hM1) hW
  have hW8 : W + 1 ≤ (W + 1) ^ 8 := by
    calc W + 1 = (W + 1) ^ 1 := (pow_one _).symm
      _ ≤ (W + 1) ^ 8 := rcR_pow_le_pow (by omega) (by norm_num)
  have hsvw : (Val.list svs).wt < A.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have hpw : (Val.list (ps.map pairV)).wt < A.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have hqw : (Val.nat q).wt < A.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have hkw : (Val.nat k).wt < (Val.list svs).wt := wt_le_wt_list (List.mem_of_getElem? hsv0)
  have hdw : (natList dl).wt < (Val.list svs).wt := wt_le_wt_list (List.mem_of_getElem? hsv2)
  have hAl : A = .list [.list svs, .nat q, .list (ps.map pairV), Wv, Rv] := hAv
  have hAW : (Val.list [.list svs, .nat q, .list (ps.map pairV), Wv, Rv]).wt ≤ W := by
    rw [← hAl]; omega
  have hMW8 : (M + 1) ^ 3 ≤ (W + 1) ^ 8 :=
    (rcR_pow_mono (show M + 1 ≤ W + 1 by omega) 3).trans (rcR_pow_le_pow (by omega) (by norm_num))
  have wkk := wt_nat_le k
  have wqq := wt_nat_le q
  -- the deterministic prefix
  have dk := rcRDW.get (rcRDW.arg (P := P) (rest := []) (W := W) (j := 0)
    (vs := [.list svs, .nat q, .list (ps.map pairV), Wv, Rv]) hAW rfl) hsv0
  rw [← hAl] at dk
  refine CpFB.intro ok.st1 (rcR_letC (Cb := (pointwiseStabPrim hst).bound
    (.list [encGroup (ps.map encPair), encPts [(⟨x, by omega⟩ : Fin (k + q))]]) +
    (10 ^ 21 + 3 * 10 ^ 15) * (W + 1) ^ 8 + 100 * W) (rcR_detC dk (C := 10 * W + 100) (by omega)
    (Q := (· = .nat k)) rfl) ?_ (by omega))
  rintro _ rfl -
  have ddv := rcRDW.get (rcRDW.arg (P := P) (rest := [.nat k]) (W := W) (j := 0)
    (vs := [.list svs, .nat q, .list (ps.map pairV), Wv, Rv]) hAW rfl) hsv2
  rw [← hAl] at ddv
  refine rcR_letC (Cb := (pointwiseStabPrim hst).bound
    (.list [encGroup (ps.map encPair), encPts [(⟨x, by omega⟩ : Fin (k + q))]]) +
    (10 ^ 21 + 2 * 10 ^ 15) * (W + 1) ^ 8 + 80 * W) (rcR_detC ddv (C := 10 * W + 100) (by omega)
    (Q := (· = natList dl)) rfl) ?_ (by omega)
  rintro _ rfl -
  have hfe := findEq_spec ok.fEq (xs := dl) (j := 1) (B := M) (fun y hy => by
    have := hdl1 y hy; omega) (by omega) (by omega)
  have ex : (dl.findIdx fun y => decide (y = 1)) = x := by rw [← hx]; rfl
  rw [ex] at hfe
  have dx := rcRDW.call (rcRDW.mk2 (rcRDW.nat (P := P) (W := W) (env := [A, .nat k, natList dl]) 1
      (by omega)) (rcRDW.var (i := 2) rfl (by omega))
      (by have := wt_list2_le (.nat 1) (natList dl); have := wt_nat_le 1; omega)) hfe
    (by have := wt_nat_le x; omega)
  refine rcR_letC (Cb := (pointwiseStabPrim hst).bound
    (.list [encGroup (ps.map encPair), encPts [(⟨x, by omega⟩ : Fin (k + q))]]) +
    (10 ^ 21 + 10 ^ 15) * (W + 1) ^ 8 + 60 * W) (rcR_detC dx
    (C := 10 ^ 6 * (W + 1) ^ 8) (by have hK : findEqK = 10 ^ 5 := rfl; rw [hK]; omega)
    (Q := (· = .nat x)) rfl) ?_ (by omega)
  rintro _ rfl -
  -- the stabilizer
  have hxq : x < k + q := by omega
  have eX : encPts [(⟨x, hxq⟩ : Fin (k + q))] = .list [.nat x] := rfl
  have wk2 := wt_list2_le (.nat k) (.nat q)
  have wx1 := wt_list1_le (.nat x)
  have wxx := wt_nat_le x
  have wst := wt_list3_le (.list [.nat k, .nat q]) (.list (ps.map pairV)) (.list [.nat x])
  have hkq : (Val.list [.nat k, .nat q]).wt ≤ W := by omega
  have hx1 : (Val.list [.nat x]).wt ≤ W := by omega
  have hst3 : (Val.list [.list [.nat k, .nat q], .list (ps.map pairV), .list [.nat x]]).wt ≤ W := by
    omega
  have dinp := rcRDW.mk3 (rcRDW.mk2 (rcRDW.var (P := P) (W := W) (env := [.list [.list svs,
      .nat q, .list (ps.map pairV), Wv, Rv], .nat k, natList dl, .nat x]) (i := 1) rfl (by omega)) (rcRDW.arg (rest := [.nat k, natList dl, .nat x])
      (vs := [.list svs, .nat q, .list (ps.map pairV), Wv, Rv]) (j := 1) (v := .nat q) hAW
      rfl) (by omega))
    (rcRDW.arg (rest := [.nat k, natList dl, .nat x])
      (vs := [.list svs, .nat q, .list (ps.map pairV), Wv, Rv]) (j := 2)
      (v := .list (ps.map pairV)) hAW rfl)
    (rcRDW.mk1 (rcRDW.var (P := P) (W := W) (i := 3) rfl (by omega)) hx1) hst3
  rw [← hAl] at dinp
  have hspec := graphStabP_spec hst ok.stab hj ps [(⟨x, hxq⟩ : Fin (k + q))]
  rw [eX] at hspec
  have hM68 : (M + 1) ^ 6 ≤ (M + 1) ^ 8 := rcR_pow_le_pow (by omega) (by norm_num)
  refine rcR_letC (Cb := 10 ^ 21 * (W + 1) ^ 8) (rcR_callC
    (Q := fun w => ∃ qs : List (Perm (Fin k) × Perm (Fin q)), w = .list (qs.map pairV) ∧
      qs.length ≤ (k + q) ^ 2 ∧ Subgroup.closure {p | p ∈ qs} = Subgroup.closure {p | p ∈ ps} ⊓
        fixPts k q [(⟨x, hxq⟩ : Fin (k + q))])
    (C := (pointwiseStabPrim hst).bound
    (.list [encGroup (ps.map encPair), encPts [(⟨x, by omega⟩ : Fin (k + q))]]) +
    10 ^ 15 * (W + 1) ^ 8)
    (Cb := (pointwiseStabPrim hst).bound
    (.list [encGroup (ps.map encPair), encPts [(⟨x, by omega⟩ : Fin (k + q))]]) +
    10 ^ 14 * (W + 1) ^ 8) (rcR_detC dinp (C := 100 * W + 1000) (by omega)
      (Q := (· = .list [.list [.nat k, .nat q], .list (ps.map pairV), .list [.nat x]])) rfl)
    (fun v hv _ => by
      subst hv
      refine hspec.mono fun w c ⟨qs, hw, hl, hcl, hc⟩ => ⟨⟨qs, hw, hl, hcl⟩, ?_, ?_⟩
      · rw [hw]; have := rcR_wt_qs hk hq qs hl; omega
      · have h1 : stabPM k q ps [(⟨x, hxq⟩ : Fin (k + q))] ≤ W + 1 := by
          unfold stabPM; simp only [List.length_cons, List.length_nil]
          have := length_lt_wt_list (ps.map pairV); rw [List.length_map] at this; omega
        have h2 := rcR_pow_mono h1 8
        have hK : graphStabK = 10 ^ 14 := rfl
        rw [hK] at hc
        calc c ≤ _ := hc
          _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ h2) _)
    (by omega)) ?_ (by omega)
  rintro _ ⟨qs, rfl, hl, hcl⟩ -
  subst hAl
  obtain ⟨labs, hlabs⟩ : ∃ labs, labs = (List.finRange q).map (orbitLabels (qs.map Prod.snd)) :=
    ⟨_, rfl⟩
  have hlab1 : ∀ y ∈ labs, y < q := by
    intro y hy
    rw [hlabs] at hy
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hy
    exact ((orbitLabels_spec (qs.map Prod.snd)).2 c).1
  have hlabl : labs.length = q := by rw [hlabs, List.length_map, List.length_finRange]
  have wlab : (natList labs).wt ≤ 5 * (M + 1) ^ 2 := wt_natList_le_sq (B := M)
    (fun y hy => by have := hlab1 y hy; omega) (by omega)
  have helab : encFun (orbitLabels (qs.map Prod.snd)) = natList labs := by
    rw [hlabs, encFun_eq_natList]
  have hM28 : (M + 1) ^ 2 ≤ (M + 1) ^ 8 := rcR_pow_le_pow (by omega) (by norm_num)
  have wqs := rcR_wt_qs hk hq qs hl
  have wsn := rcR_wt_snds hk hq qs hl
  have wR := rcR_wt_range q M hq
  have wF := rcR_wt_filter (List.range q) (fun c => decide (labs.count (labs.getD c 0) ≤ 2))
  -- the second parts and the orbit labels
  have w0 := wt_nat_le 0
  have wi1 := wt_list2_le (.nat 0) (.list (qs.map pairV))
  have dS := rcRDW.call (rcRDW.mk2 (rcRDW.nat (P := P) (W := W) (env := [.list [.list svs, .nat q,
      .list (ps.map pairV), Wv, Rv], .nat k, natList dl, .nat x, .list (qs.map pairV)]) 0
      (by omega)) (rcRDW.var (i := 4) rfl (by omega)) (by omega))
    (rcR_mSnd_spec ok qs (W := W) (by omega) (by omega)) (by omega)
  have wi2 := wt_list2_le (.nat q) (.list ((qs.map Prod.snd).map encPerm))
  have dO := rcRDW.cast (rcRDW.call (rcRDW.mk2 (rcRDW.arg (rest := [.nat k, natList dl, .nat x,
      .list (qs.map pairV)]) (vs := [.list svs, .nat q, .list (ps.map pairV), Wv, Rv]) (j := 1)
      (v := .nat q) hAW rfl) dS (by omega))
    (orbitFuns_spec ok.orb (qs.map Prod.snd)) (by rw [helab]; omega)) helab
  -- `range q`
  have hrng : FunDet P I.rng (.nat q) (natList (List.range q))
      (loopModK * (q + 1) * ((Val.nat q).wt + q + (natList (List.range q)).wt + 1)) :=
    (range_spec ok.rng q).mono fun w c ⟨hw, hc⟩ => ⟨hw, by rw [hw] at hc; exact hc⟩
  have dR := rcRDW.call (rcRDW.arg (rest := [.nat k, natList dl, .nat x,
      .list (qs.map pairV), natList labs]) (vs := [.list svs, .nat q, .list (ps.map pairV), Wv, Rv])
      (j := 1) (v := .nat q) hAW rfl) hrng (by omega)
  -- the small labels
  have hfil := rcR_filterN ok.fSm (c := natList labs) (xs := List.range q)
    (t := fun c => decide (labs.count (labs.getD c 0) ≤ 2)) (K := 10 ^ 10) (d := 3) (W := W)
    (fun c hc => (rcR_smP_spec ok.gD ok.smP ok.cnt labs c (fun y hy => by
      have := hlab1 y hy
      have := rcR_natList_len labs
      have : (natList labs).wt < (Val.list [natList labs, .nat c]).wt := wt_le_wt_list (by simp)
      omega)).mono (by
        have h1 := rcR_wt_elemN (c := natList labs) hc
        have h2 := wt_list2_le (natList labs) (natList (List.range q))
        have := rcR_cube_cost (K := 10 ^ 7) (W := W)
          (a := (Val.list [natList labs, .nat c]).wt) (by omega)
        norm_num at this ⊢
        omega))
    (by have := wt_list2_le (natList labs) (natList (List.range q)); omega) (by omega)
  have wi3 := wt_list2_le (natList labs) (natList (List.range q))
  have dF := rcRDW.call (rcRDW.mk2 (rcRDW.var (P := P) (W := W) (env := [.list [.list svs, .nat q,
      .list (ps.map pairV), Wv, Rv], .nat k, natList dl, .nat x, .list (qs.map pairV),
      natList labs, natList (List.range q)]) (i := 5) rfl (by omega))
      (rcRDW.var (i := 6) rfl (by omega)) (by omega)) hfil (by omega)
  have wi4 := wt_list4_le (.nat x) (natList labs) (natList (List.range q))
    (natList ((List.range q).filter fun c => decide (labs.count (labs.getD c 0) ≤ 2)))
  have dres := rcRDW.mk4 (rcRDW.var (P := P) (W := W) (env := [.list [.list svs, .nat q,
      .list (ps.map pairV), Wv, Rv], .nat k, natList dl, .nat x, .list (qs.map pairV),
      natList labs, natList (List.range q), natList ((List.range q).filter fun c =>
        decide (labs.count (labs.getD c 0) ≤ 2))]) (i := 3) rfl (by omega))
    (rcRDW.var (i := 5) rfl (by omega)) (rcRDW.var (i := 6) rfl (by omega))
    (rcRDW.var (i := 7) rfl (by omega)) (by omega)
  have dall := rcRDW.letE dO (rcRDW.letE dR (rcRDW.letE dF dres))
  refine rcR_detC dall ?_ ⟨qs, by rw [rcRSt1Val, ← hlabs], hl, hcl⟩
  -- the cost
  have c1 : orbitK * (((qs.map Prod.snd).length + 1) * (q + 1)) ^ 5 ≤ 10 ^ 6 * (W + 1) ^ 5 := by
    rw [List.length_map]
    have h2 : (k + q) ^ 2 ≤ (2 * M + 1) ^ 2 := rcR_pow_mono (by omega) 2
    have h3 : (qs.length + 1) * (q + 1) ≤ W + 1 := by
      have : qs.length + 1 ≤ 4 * (M + 1) ^ 2 := by nlinarith
      have h4 : (qs.length + 1) * (q + 1) ≤ (4 * (M + 1) ^ 2) * (M + 1) :=
        Nat.mul_le_mul this (by omega)
      have h5 : (4 * (M + 1) ^ 2) * (M + 1) = 4 * (M + 1) ^ 3 := by ring
      have h6 : (M + 1) ^ 3 ≤ (M + 1) ^ 8 := rcR_pow_le_pow (by omega) (by norm_num)
      omega
    exact Nat.mul_le_mul_left _ (rcR_pow_mono h3 5)
  have c2 : loopModK * (q + 1) * ((Val.nat q).wt + q + (natList (List.range q)).wt + 1) ≤
      1000 * (W + 1) ^ 8 := by
    have h1 : (q + 1) * ((Val.nat q).wt + q + (natList (List.range q)).wt + 1) ≤
        (W + 1) * (W + 1) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : (W + 1) * (W + 1) ≤ (W + 1) ^ 8 := rcR_sq_pw (by norm_num)
    have hK : loopModK = 1000 := rfl
    rw [hK, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (h1.trans h2)
  have p5 : (W + 1) ^ 3 ≤ (W + 1) ^ 8 := rcR_pow_le_pow (by omega) (by norm_num)
  have p6 : (W + 1) ^ 5 ≤ (W + 1) ^ 8 := rcR_pow_le_pow (by omega) (by norm_num)
  norm_num at c1 ⊢
  omega

end St1

end GI.Impl
