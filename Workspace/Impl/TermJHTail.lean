import Workspace.Impl.TermJHLayout
import Workspace.Impl.AggItemPartEven

/-!
# The transporter of one label: the tail

`tmJHTailF`, on `[ctx, encPerm z, encPerm u]` with `u = (d, π)` and all `d i ∈ N`, returns
`z · tmJCorrE Tl odd lg c`, where `c` solves `∏ φ(g_k)^{c_k} = lab(d)` and `odd` says that `π` is
odd (`tmJH_tail_spec`). The steps are: decode `u` (`tmJH_dec_spec`), solve for `c`
(`tmJH_coef_spec`), the parity of `π` (`it_par_spec`), the local product (`tmJH_lam_spec`), the
correction (`tmJH_corr_spec`) and one product.
-/

namespace GI.Impl

open GI.Lang GI.Assembly GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens encInt encIntMatrix)
open scoped IsMulCommutative

/-! ### Small facts -/

theorem tmJH_lt_wt_encPerm {n : ℕ} (σ : Perm (Fin n)) : n < (encPerm σ).wt := by
  have h := length_lt_wt_list ((List.finRange n).map fun i => Val.nat (σ i))
  simp only [List.length_map, List.length_finRange] at h
  exact h

theorem tmJH_parity_ne {q : ℕ} (π : Perm (Fin q)) : itpNInv π % 2 ≠ 0 ↔ sign π = -1 := by
  rw [Ne, ← Nat.even_iff, ← itp_sign_one_iff]
  rcases Int.units_eq_one_or (sign π) with h | h <;> rw [h] <;> decide

/-! ### The tail -/

/-- The budget of the tail, in the weight `W` of its input. -/
def tmJHTailBud (Kc Dc W : ℕ) : ℕ :=
  10 ^ 30 * (W + 1) ^ 16 + 10 * (Kc * (27 * (W + 1) ^ 3) ^ Dc) +
    10 * (10 ^ 17 * (12 * (W + 1) ^ 2 + 2 * (Kc * (27 * (W + 1) ^ 3) ^ Dc)) ^ 9)

theorem tmJH_tailBud_poly (Kc Dc : ℕ) : PBU fun _ W _ => tmJHTailBud Kc Dc W := by
  unfold tmJHTailBud
  have hW1 : PBU fun _ W _ => W + 1 := PBU.addc PBU.W 1
  have hC : PBU fun _ W _ => Kc * (27 * (W + 1) ^ 3) ^ Dc :=
    PBU.smul Kc (PBU.pow (PBU.smul 27 (PBU.pow hW1 3)) Dc)
  exact PBU.add (PBU.add (PBU.smul _ (PBU.pow hW1 16)) (PBU.smul 10 hC))
    (PBU.smul 10 (PBU.smul _ (PBU.pow (PBU.add (PBU.smul 12 (PBU.pow hW1 2)) (PBU.smul 2 hC)) 9)))

set_option maxHeartbeats 16000000 in
/-- **The tail of the per-label program.** -/
theorem tmJH_tail_spec (hcm : GI.Cited.ConstructiveMembership) (hH : GI.Cited.HermiteFullRank) :
    ∃ K D : ℕ, ∀ {P : Program} {p : TmJHPos}, TmJHAt P p →
      P.prims[p.jm]? = some (linMembershipPrim hcm) → P.prims[p.jh]? = some (linHermitePrim hH) →
      ∀ {m q : ℕ} {N : Subgroup (Perm (Fin m))} {A : Type} [CommGroup A] {φ : N →* A}
        (gsG gsNq : List (Perm (Fin (m * q)))) (vs : List Val) (σS σN : List (Perm (Fin m)))
        [((gens σS).subgroupOf (gens σN)).Normal]
        [IsMulCommutative ((gens σN) ⧸ (gens σS).subgroupOf (gens σN))],
        gens σS ≤ gens σN → TmJSameKer φ (tmJHPsi σS σN) →
        ∀ (lg : List (Fin q × Perm (Fin m))) (Tl : List (Fin q × Fin q × Perm (Fin m)))
          (Bm : Matrix (Fin lg.length) (Fin σN.length) ℤ)
          (M : Matrix (Fin σN.length) (Fin σN.length) ℤ),
        linPresentationCertificate M (tmJHF σS σN) →
        (∀ k : Fin lg.length, (lg.get k).2 ∈ N) →
        (∀ k, tmJHF σS σN (Bm k) = Additive.ofMul (QuotientGroup.mk'
          ((gens σS).subgroupOf (gens σN)) (linIntoSubgroup (gens σN) (lg.get k).2))) →
        0 < m →
        ∀ (z : Perm (Fin (m * q))) (d : Fin q → Perm (Fin m)) (π : Perm (Fin q)), (∀ i, d i ∈ N) →
        (∃ e : Fin lg.length → ℤ, tmJSumT N φ lg e = tmJLab N φ d) →
        (sign π = -1 → Tl ≠ []) →
        FunAll P (p.b + 1) (.list [tmJHCtx gsG gsNq vs σS σN lg Tl Bm M, encPerm z,
            encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π)))])
          (fun out cost => ∃ (c : Fin lg.length → ℤ) (odd : Bool),
            tmJSumT N φ lg c = tmJLab N φ d ∧ (odd = true ↔ sign π = -1) ∧
            out = encPerm (z * toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
              (tmJCorrE Tl odd lg c)) ∧
            cost ≤ K * ((Val.list [tmJHCtx gsG gsNq vs σS σN lg Tl Bm M, encPerm z,
              encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
                (tmJP (d, π)))]).wt + 1) ^ D) := by
  obtain ⟨Kc, Dc, hC⟩ := tmJH_coef_spec hcm hH
  obtain ⟨K, D, hKD⟩ := tmJH_poly (tmJH_tailBud_poly Kc Dc)
  refine ⟨K, D, fun {P p} hA hjm hjh {m q N A _ φ} gsG gsNq vs σS σN _ _ hle hk lg Tl Bm M hcert
    hlg hB hm z d π hd hex hTl => ?_⟩
  refine FunAll.intro hA.htail ?_
  unfold tmJHTailF
  set ctxL : List Val := [encGroup gsG, encGroup gsNq, .list vs, .list (σN.map encPerm),
    encGroup σS, encGroup σN, tmJLgVal lg, tmJTlVal Tl, encIntMatrix Bm, encIntMatrix M,
    tmJLocCtx m q] with hctxL
  have hctx : tmJHCtx gsG gsNq vs σS σN lg Tl Bm M = .list ctxL := rfl
  set fpf := (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) with hfpf
  set uu := toFin fpf (tmJP (d, π)) with huu
  set inp : List Val := [tmJHCtx gsG gsNq vs σS σN lg Tl Bm M, encPerm z, encPerm uu] with hinp
  set W := (Val.list inp).wt with hW
  refine EvalAll.mono (Q := fun out cost => ∃ (c : Fin lg.length → ℤ) (odd : Bool),
    tmJSumT N φ lg c = tmJLab N φ d ∧ (odd = true ↔ sign π = -1) ∧
    out = encPerm (z * toFin fpf (tmJCorrE Tl odd lg c)) ∧ cost ≤ tmJHTailBud Kc Dc W) ?_
    (by rintro out cost ⟨c, odd, h1, h2, h3, h4⟩; exact ⟨c, odd, h1, h2, h3, h4.trans (hKD W)⟩)
  -- weights
  have wc : (tmJHCtx gsG gsNq vs σS σN lg Tl Bm M).wt < W := wt_le_wt_list (by simp [hinp])
  have wz : (encPerm z).wt < W := wt_le_wt_list (by simp [hinp])
  have wu : (encPerm uu).wt < W := wt_le_wt_list (by simp [hinp])
  rw [hctx] at wc
  have wsl : ∀ v ∈ ctxL, v.wt < W := fun v hv => (wt_le_wt_list hv).trans wc
  have w6 := wsl (tmJLgVal lg) (by simp [hctxL])
  have w7 := wsl (tmJTlVal Tl) (by simp [hctxL])
  have w10 := wsl (tmJLocCtx m q) (by simp [hctxL])
  have wm : (encPerm (1 : Perm (Fin m))).wt < (tmJLocCtx m q).wt := wt_le_wt_list (by simp [tmJLocCtx])
  have wq : (encPerm (1 : Perm (Fin q))).wt < (tmJLocCtx m q).wt := wt_le_wt_list (by simp [tmJLocCtx])
  have hm1 : m + 1 ≤ W := by have := tmJH_lt_wt_encPerm (1 : Perm (Fin m)); omega
  have hq1 : q + 1 ≤ W := by have := tmJH_lt_wt_encPerm (1 : Perm (Fin q)); omega
  have hn1 : m * q + 1 ≤ W := by have := tmJH_lt_wt_encPerm z; omega
  have hW1 : 1 ≤ W + 1 := by omega
  have hV : (m + 1) * (q + 1) ≤ (W + 1) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have hpw : ∀ i j, i ≤ j → (W + 1) ^ i ≤ (W + 1) ^ j := fun i j h => Nat.pow_le_pow_right hW1 h
  -- step 1: decode `u`
  have a0 := Det.arg' (P := P) (vs := inp) (rest := []) (j := 0) (v := .list ctxL) rfl
  have a2 := Det.arg' (P := P) (vs := inp) (rest := []) (j := 2) (v := encPerm uu) rfl
  have g10 := Det.get' a0 (Det.nat 10) (vs := ctxL) (v := tmJLocCtx m q) rfl
  have cd := Det.call (Det.mk2 a2 g10) (tmJH_dec_spec hA.hdec hA.hrg hA.htbR hA.hdecR hA.htbE
    hA.hdecE hA.htbP hA.hdecP hm d π)
  refine EvalAll.letE cd (fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  -- step 2: the coefficients
  set v1 : Val := .list [tmJDsVal d, encPerm π] with hv1
  have b0 := Det.arg' (P := P) (vs := inp) (rest := [v1]) (j := 0) (v := .list ctxL) rfl
  have b1 := Det.var' (P := P) (env := [Val.list inp, v1]) (i := 1) (v := v1) rfl
  have gds := Det.get' b1 (Det.nat 0) (vs := [tmJDsVal d, encPerm π]) (v := tmJDsVal d) rfl
  have hCf := hC hA.coefAt hjm hjh gsG gsNq vs σS σN hle hk lg Tl Bm M hcert hlg hB d hd hex
  rw [hctx] at hCf
  have cc := tmJH_callA (Det.mk2 b0 gds) (hCf.mono fun w c h => (show (∃ c' : Fin lg.length → ℤ,
      w = .list [.nat 1, linVecVal c'] ∧ tmJSumT N φ lg c' = tmJLab N φ d) ∧ _ from
    ⟨let ⟨c', h1, h2, _⟩ := h; ⟨c', h1, h2⟩, let ⟨_, _, _, h3⟩ := h; h3⟩))
  refine EvalAll.letE cc (fun v2 c2 h2 => ?_)
  obtain ⟨⟨cv, rfl, hsum⟩, hw2, hc2⟩ := h2
  -- step 3: parity, local product, correction, product
  set v2 : Val := .list [.nat 1, linVecVal cv] with hv2
  set env3 : List Val := [Val.list inp, v1, v2] with henv3
  have e0 := Det.arg' (P := P) (vs := inp) (rest := [v1, v2]) (j := 0) (v := .list ctxL) rfl
  have e1 := Det.arg' (P := P) (vs := inp) (rest := [v1, v2]) (j := 1) (v := encPerm z) rfl
  have e7 := Det.get' e0 (Det.nat 7) (vs := ctxL) (v := tmJTlVal Tl) rfl
  have e10 := Det.get' e0 (Det.nat 10) (vs := ctxL) (v := tmJLocCtx m q) rfl
  have e6 := Det.get' e0 (Det.nat 6) (vs := ctxL) (v := tmJLgVal lg) rfl
  have x1 := Det.var' (P := P) (env := env3) (i := 1) (v := v1) rfl
  have x2 := Det.var' (P := P) (env := env3) (i := 2) (v := v2) rfl
  have gπ := Det.get' x1 (Det.nat 1) (vs := [tmJDsVal d, encPerm π]) (v := encPerm π) rfl
  have gcv := Det.get' x2 (Det.nat 1) (vs := [.nat 1, linVecVal cv]) (v := linVecVal cv) rfl
  have cpar := Det.call gπ (it_par_spec hA.hpar hA.hrng hA.hmp hA.hib hA.hflt hA.hit hA.hfld2
    hA.hst π)
  have clam := Det.call (Det.mk3 e6 gcv e10) (tmJH_lam_spec hA.lamAt lg cv)
  have hne : itpNInv π % 2 ≠ 0 → Tl ≠ [] := fun h => hTl ((tmJH_parity_ne π).1 h)
  have ccorr := Det.call (Det.mk4 e7 e10 cpar clam) (tmJH_corr_spec hA.corrAt Tl _ hne
    (tmJLam lg cv))
  have cfin := Det.call (Det.mk2 e1 ccorr) (compose_spec hA.hcomp z
    (toFin fpf ((if itpNInv π % 2 = 0 then 1 else tmJSw0 Tl) * tmJLam lg cv)))
  refine EvalAll.mono cfin ?_
  rintro w c ⟨rfl, hc⟩
  refine ⟨cv, decide (itpNInv π % 2 ≠ 0), hsum, by rw [decide_eq_true_iff, tmJH_parity_ne], ?_, ?_⟩
  · have hEq : (if itpNInv π % 2 = 0 then 1 else tmJSw0 Tl) * tmJLam lg cv =
        tmJCorrE Tl (decide (itpNInv π % 2 ≠ 0)) lg cv := by
      unfold tmJCorrE
      by_cases h0 : itpNInv π % 2 = 0 <;> simp only [h0, ne_eq, not_true_eq_false,
        not_false_eq_true, decide_false, decide_true, if_true, if_false, Bool.false_eq_true]
    rw [hEq]
  -- the cost
  have hcv : (linVecVal cv).wt < v2.wt := wt_le_wt_list (by simp [hv2])
  have hv1w := wt_list2_le (tmJDsVal d) (encPerm π)
  have hds := wt_tmJDsVal_le d
  have hπ := wt_encPerm_le π
  have hdsW : (tmJDsVal d).wt ≤ 9 * (W + 1) ^ 3 := by
    have h1 : 9 * (q + 1) * (m + 1) ^ 2 ≤ 9 * (W + 1) * (W + 1) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left (by omega) 2)
    have h2 : 9 * (W + 1) * (W + 1) ^ 2 = 9 * (W + 1) ^ 3 := by ring
    omega
  have hπW : (encPerm π).wt ≤ 4 * (W + 1) ^ 2 :=
    hπ.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have wcin := wt_list2_le (Val.list ctxL) (tmJDsVal d)
  have hCin : (Val.list [Val.list ctxL, tmJDsVal d]).wt + 1 ≤ 27 * (W + 1) ^ 3 := by
    have := hpw 1 3 (by norm_num); rw [pow_one] at this; omega
  have hCc : Kc * ((Val.list [Val.list ctxL, tmJDsVal d]).wt + 1) ^ Dc ≤
      Kc * (27 * (W + 1) ^ 3) ^ Dc := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hCin _)
  generalize hCcd : Kc * (27 * (W + 1) ^ 3) ^ Dc = Cc at *
  -- the pieces of the last step
  have wl3 := wt_list3_le (tmJLgVal lg) (linVecVal cv) (tmJLocCtx m q)
  have hZl : (Val.list [tmJLgVal lg, linVecVal cv, tmJLocCtx m q]).wt + (m + 1) * (q + 1) ≤
      12 * (W + 1) ^ 2 + 2 * Cc := by
    have := hpw 1 2 (by norm_num); rw [pow_one] at this; omega
  have hlamK : tmJHLamK ((Val.list [tmJLgVal lg, linVecVal cv, tmJLocCtx m q]).wt +
      (m + 1) * (q + 1)) ≤ 10 ^ 17 * (12 * (W + 1) ^ 2 + 2 * Cc) ^ 9 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hZl 9)
  have wlam := wt_encPerm_le (toFin fpf (tmJLam lg cv))
  have hn2 : (m * q + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hn3 : (m * q + 1) ^ 3 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have wk := wt_nat_le (itpNInv π % 2)
  have hk2 : itpNInv π % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have wl4 := wt_list4_le (tmJTlVal Tl) (tmJLocCtx m q) (.nat (itpNInv π % 2))
    (encPerm (toFin fpf (tmJLam lg cv)))
  have hZc : (Val.list [tmJTlVal Tl, tmJLocCtx m q, .nat (itpNInv π % 2),
      encPerm (toFin fpf (tmJLam lg cv))]).wt + (m + 1) * (q + 1) ≤ 20 * (W + 1) ^ 2 := by
    have := hpw 1 2 (by norm_num); rw [pow_one] at this; omega
  have hcorrK : tmJHCorrK ((Val.list [tmJTlVal Tl, tmJLocCtx m q, .nat (itpNInv π % 2),
      encPerm (toFin fpf (tmJLam lg cv))]).wt + (m + 1) * (q + 1)) ≤ 10 ^ 27 * (W + 1) ^ 16 := by
    unfold tmJHCorrK
    calc 10 ^ 16 * _ ^ 8 ≤ 10 ^ 16 * (20 * (W + 1) ^ 2) ^ 8 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hZc 8)
      _ ≤ 10 ^ 27 * (W + 1) ^ 16 := by
          rw [mul_pow, ← pow_mul]; norm_num; nlinarith [Nat.zero_le ((W + 1) ^ 16)]
  have hpar : itParC q ≤ 10 ^ 7 * (W + 1) ^ 4 := by
    unfold itParC; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  have hdecK : tmJHDecK ((m + 1) * (q + 1)) ≤ 10 ^ 10 * (W + 1) ^ 8 := by
    unfold tmJHDecK
    calc 10 ^ 10 * ((m + 1) * (q + 1)) ^ 4 ≤ 10 ^ 10 * ((W + 1) ^ 2) ^ 4 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hV 4)
      _ = 10 ^ 10 * (W + 1) ^ 8 := by rw [← pow_mul]
  have hperm : permK * (m * q + 1) ^ 3 ≤ 30000 * (W + 1) ^ 3 := by
    unfold permK; exact Nat.mul_le_mul_left _ hn3
  have wcorr := wt_encPerm_le (toFin fpf ((if itpNInv π % 2 = 0 then 1 else tmJSw0 Tl) *
    tmJLam lg cv))
  have wfin := wt_encPerm_le (z * toFin fpf ((if itpNInv π % 2 = 0 then 1 else tmJSw0 Tl) *
    tmJLam lg cv))
  have wf2 := wt_list2_le (encPerm z) (encPerm (toFin fpf ((if itpNInv π % 2 = 0 then 1 else
    tmJSw0 Tl) * tmJLam lg cv)))
  have wl2 := wt_list2_le (encPerm uu) (tmJLocCtx m q)
  have wv2 := wt_list2_le (Val.nat 1) (linVecVal cv)
  have wn1 : (Val.nat 1).wt ≤ 3 := by decide
  have hp2 := hpw 2 16 (by norm_num)
  have hp3 := hpw 3 16 (by norm_num)
  have hp4 := hpw 4 16 (by norm_num)
  have hp8 := hpw 8 16 (by norm_num)
  have hp1 := hpw 1 16 (by norm_num)
  rw [pow_one] at hp1
  have r0 : (Val.list inp).wt = W := rfl
  have r1 : (Val.list [tmJHCtx gsG gsNq vs σS σN lg Tl Bm M, encPerm z, encPerm uu]).wt = W := rfl
  have r2 : (Val.list [Val.list ctxL, encPerm z, encPerm uu]).wt = W := by rw [← hctx]
  simp only [hv1, hv2, hfpf] at *
  unfold tmJHTailBud
  rw [hCcd]
  omega

end GI.Impl
