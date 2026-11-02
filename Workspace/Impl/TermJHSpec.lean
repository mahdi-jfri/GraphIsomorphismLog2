import Workspace.Impl.TermJHMain

/-!
# The transporter of one label: the specification

For one label `h`, `tmJHMainF` (at `p.b`), on `[ctx, encPerm h]`,
1. builds the constant pair `x₀ = (h; 1)` (`tmJH_cst_spec`);
2. factors `x₀ = g w` in `⟨G|_dom⟩ ⟨N^q⟩` by one NormalizedFactor call, so `g` is a lift of
   `(h; 1)` with top permutation `1` (paper, proof of Theorem A.18: "Standard
   constructive quotient operations then give all displayed maps and lifts");
3. takes the local transporter `z = (d', π')` of the class `h` (`tmJL_spec`);
4. runs the tail on `u = z⁻¹ g` (`tmJH_tail_spec`).

`tmJH_spec` states the result on `Fin (m q)`. The facts about the row terminal that the tail
needs (`u = (d, π)` with all `d i ∈ N`, the zero-sum equation is solvable, an odd `π` needs a
transposition) enter as the hypothesis `hcorr`, for every possible result of steps 2 and 3. They
are proved from `tmJH_exists` and `tmJH_odd_ne` where the program is used.
-/

namespace GI.Impl

open GI.Lang GI.Assembly GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens encInt encIntMatrix)
open scoped IsMulCommutative

variable {m q : ℕ}

/-- A pair `(d, π)` as a permutation of `Fin (m q)`. -/
abbrev tmJHPm (d : Fin q → Perm (Fin m)) (π : Perm (Fin q)) : Perm (Fin (m * q)) :=
  toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π))

/-- The constant pair `(h; 1)` on `Fin (m q)`. -/
abbrev tmJHCs (q : ℕ) (h : Perm (Fin m)) : Perm (Fin (m * q)) :=
  tmJHPm (fun _ => h : Fin q → Perm (Fin m)) 1

/-- **The result of the per-label program**: a lift `g` of `(h; 1)` from the factorization, a
local transporter `z = (d', π')` of the class `h`, the decomposition `z⁻¹ g = (d, π)`, a solution
`c` of the zero-sum equation and the parity `odd` of `π`; the output is
`z · tmJCorrE Tl odd lg c`. -/
def TmJHOut {A : Type} [CommGroup A] (N : Subgroup (Perm (Fin m))) (φ : N →* A)
    (gsG gsNq : List (Perm (Fin (m * q)))) (Ac : Fin q × Fin q → Set (Perm (Fin m)))
    (lg : List (Fin q × Perm (Fin m))) (Tl : List (Fin q × Fin q × Perm (Fin m)))
    (h : Perm (Fin m)) (out : Val) : Prop :=
  ∃ g ∈ gens gsG, (∃ w ∈ gens gsNq, tmJHCs q h = g * w) ∧
    ∃ (d' : Fin q → Perm (Fin m)) (π' : Perm (Fin q)), (∀ a, d' a ∈ Ac (a, π' a) ∧ h⁻¹ * d' a ∈ N) ∧
    ∃ (d : Fin q → Perm (Fin m)) (π : Perm (Fin q)) (c : Fin lg.length → ℤ) (odd : Bool),
      (∀ i, d i ∈ N) ∧ (tmJHPm d' π')⁻¹ * g = tmJHPm d π ∧
      tmJSumT N φ lg c = tmJLab N φ d ∧ (odd = true ↔ sign π = -1) ∧
      out = encPerm (tmJHPm d' π' *
        toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJCorrE Tl odd lg c))

/-- The budget of the main function, in the weight `W` of its input. -/
def tmJHMainBud (pm pf : Prim) (Kt Dt W : ℕ) : ℕ :=
  10 ^ 18 * (W + 1) ^ 16 + pf.c * (22 * (W + 1) ^ 4) ^ pf.k +
    2 * (tmJLK pm pf * (10 * (W + 1)) ^ tmJLD pm pf) + 2 * (Kt * (21 * (W + 1) ^ 4) ^ Dt)

theorem tmJH_mainBud_poly (pm pf : Prim) (Kt Dt : ℕ) :
    PBU fun _ W _ => tmJHMainBud pm pf Kt Dt W := by
  unfold tmJHMainBud
  have hW1 : PBU fun _ W _ => W + 1 := PBU.addc PBU.W 1
  have h4 : PBU fun _ W _ => (W + 1) ^ 4 := PBU.pow hW1 4
  exact PBU.add (PBU.add (PBU.add (PBU.smul _ (PBU.pow hW1 16))
    (PBU.smul _ (PBU.pow (PBU.smul 22 h4) _)))
    (PBU.smul 2 (PBU.smul _ (PBU.pow (PBU.smul 10 hW1) _))))
    (PBU.smul 2 (PBU.smul _ (PBU.pow (PBU.smul 21 h4) _)))

/-- **The transporter of one label** (the per-label program of Theorem A.23). -/
theorem tmJH_spec (hm : GI.Cited.Membership) (hfac : GI.Cited.NormalizedFactor)
    (hcm : GI.Cited.ConstructiveMembership) (hH : GI.Cited.HermiteFullRank) :
    ∃ K D : ℕ, ∀ {P : Program} {p : TmJHPos}, TmJHAt P p →
      P.prims[p.jm]? = some (linMembershipPrim hcm) → P.prims[p.jh]? = some (linHermitePrim hH) →
      P.prims[p.jmem]? = some (membershipPrim hm) →
      P.prims[p.jf]? = some (normalizedFactorPrim hfac) →
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
        0 < m → 0 < q →
        ∀ {C : Type} (H : Subgroup (Perm (Fin m))), GI.Multicoset.Normalizes H N → gens σN = N →
        ∀ (x y : Fin q → Fin m → C) (Ac : Fin q × Fin q → Set (Perm (Fin m))),
        (∀ a j, Ac (a, j) = {u | u ∈ H ∧ x a ∘ ⇑u = y j}) →
        List.Forall₂ (fun v ij => AnsC (Equiv.refl (Fin m)) v (Ac ij)) vs (tmCosets q) →
        GI.Lang.Normalizes (gens gsG) (gens gsNq) →
        ∀ h : Perm (Fin m),
        (∃ g ∈ gens gsG, ∃ w ∈ gens gsNq, tmJHCs q h = g * w) →
        (∃ π : Perm (Fin q), ∀ a, ∃ u ∈ Ac (a, π a), h⁻¹ * u ∈ N) →
        (∀ g, g ∈ gens gsG → (∃ w ∈ gens gsNq, tmJHCs q h = g * w) →
          ∀ (d' : Fin q → Perm (Fin m)) (π' : Perm (Fin q)),
            (∀ a, d' a ∈ Ac (a, π' a) ∧ h⁻¹ * d' a ∈ N) →
          ∃ (d : Fin q → Perm (Fin m)) (π : Perm (Fin q)), (∀ i, d i ∈ N) ∧
            (tmJHPm d' π')⁻¹ * g = tmJHPm d π ∧
            (∃ e : Fin lg.length → ℤ, tmJSumT N φ lg e = tmJLab N φ d) ∧
            (sign π = -1 → Tl ≠ [])) →
        FunAll P p.b (.list [tmJHCtx gsG gsNq vs σS σN lg Tl Bm M, encPerm h])
          (fun out cost => TmJHOut N φ gsG gsNq Ac lg Tl h out ∧
            cost ≤ K * ((Val.list [tmJHCtx gsG gsNq vs σS σN lg Tl Bm M, encPerm h]).wt + 1) ^ D) := by
  obtain ⟨Kt, Dt, hT⟩ := tmJH_tail_spec hcm hH
  obtain ⟨K, D, hKD⟩ :=
    tmJH_poly (tmJH_mainBud_poly (membershipPrim hm) (normalizedFactorPrim hfac) Kt Dt)
  refine ⟨K, D, fun {P p} hA hjm hjh hjmem hjf {m q N A _ φ} gsG gsNq vs σS σN _ _ hle hk lg Tl
    Bm M hcert hlg hB hm0 hq0 {C} H hn hσN x y Ac hAdef hvs hnorm h hx hmatch hcorr => ?_⟩
  refine FunAll.intro hA.hmain ?_
  unfold tmJHMainF
  set ctxL : List Val := [encGroup gsG, encGroup gsNq, .list vs, .list (σN.map encPerm),
    encGroup σS, encGroup σN, tmJLgVal lg, tmJTlVal Tl, encIntMatrix Bm, encIntMatrix M,
    tmJLocCtx m q] with hctxL
  have hctx : tmJHCtx gsG gsNq vs σS σN lg Tl Bm M = .list ctxL := rfl
  set inp : List Val := [tmJHCtx gsG gsNq vs σS σN lg Tl Bm M, encPerm h] with hinp
  obtain ⟨W, hWe⟩ : ∃ W, (Val.list inp).wt = W := ⟨_, rfl⟩
  refine EvalAll.mono (Q := fun out cost => TmJHOut N φ gsG gsNq Ac lg Tl h out ∧
    cost ≤ tmJHMainBud (membershipPrim hm) (normalizedFactorPrim hfac) Kt Dt W) ?_
    (fun out cost hc => ⟨hc.1, hc.2.trans (by rw [← hWe]; exact hKD _)⟩)
  -- weights of the input
  have wc : (tmJHCtx gsG gsNq vs σS σN lg Tl Bm M).wt < W := hWe ▸ wt_le_wt_list (by simp [hinp])
  have wh : (encPerm h).wt < W := hWe ▸ wt_le_wt_list (by simp [hinp])
  rw [hctx] at wc
  have wsl : ∀ v ∈ ctxL, v.wt < W := fun v hv => (wt_le_wt_list hv).trans wc
  have w0 := wsl (encGroup gsG) (by simp [hctxL])
  have w1 := wsl (encGroup gsNq) (by simp [hctxL])
  have w2 := wsl (.list vs) (by simp [hctxL])
  have w3 := wsl (.list (σN.map encPerm)) (by simp [hctxL])
  have w10 := wsl (tmJLocCtx m q) (by simp [hctxL])
  have wlc : ∀ v ∈ [encPerm (1 : Perm (Fin m)), encPerm (1 : Perm (Fin q)), .nat q, .nat m],
      v.wt < W := fun v hv => (wt_le_wt_list hv).trans w10
  have wm1 := wlc (encPerm (1 : Perm (Fin m))) (by simp)
  have wq1 := wlc (encPerm (1 : Perm (Fin q))) (by simp)
  have wqn := wlc (.nat q) (by simp)
  have wmn := wlc (.nat m) (by simp)
  have hmX : m + 1 ≤ W + 1 := by have := tmJH_lt_wt_encPerm (1 : Perm (Fin m)); omega
  have hqX : q + 1 ≤ W + 1 := by have := tmJH_lt_wt_encPerm (1 : Perm (Fin q)); omega
  have hX1 : 1 ≤ W + 1 := by omega
  have hpw : ∀ i j, i ≤ j → (W + 1) ^ i ≤ (W + 1) ^ j := fun i j h => Nat.pow_le_pow_right hX1 h
  have hV : (m + 1) * (q + 1) ≤ (W + 1) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul hmX hqX
  have hn1 : m * q + 1 ≤ (W + 1) ^ 2 := by
    have : m * q + 1 ≤ (m + 1) * (q + 1) := by
      have e : (m + 1) * (q + 1) = m * q + m + q + 1 := by ring
      omega
    omega
  have hn2 : (m * q + 1) ^ 2 ≤ (W + 1) ^ 4 := by
    calc (m * q + 1) ^ 2 ≤ ((W + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hn1 2
      _ = (W + 1) ^ 4 := by rw [← pow_mul]
  have hn3 : (m * q + 1) ^ 3 ≤ (W + 1) ^ 6 := by
    calc (m * q + 1) ^ 3 ≤ ((W + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hn1 3
      _ = (W + 1) ^ 6 := by rw [← pow_mul]
  have hn4 : (m * q + 1) ^ 4 ≤ (W + 1) ^ 8 := by
    calc (m * q + 1) ^ 4 ≤ ((W + 1) ^ 2) ^ 4 := Nat.pow_le_pow_left hn1 4
      _ = (W + 1) ^ 8 := by rw [← pow_mul]
  have hp1 := hpw 1 4 (by norm_num)
  rw [pow_one] at hp1
  have hp2 := hpw 2 4 (by norm_num)
  have hp46 := hpw 4 6 (by norm_num)
  have hp68 := hpw 6 8 (by norm_num)
  have hp816 := hpw 8 16 (by norm_num)
  have wP : ∀ σ : Perm (Fin (m * q)), (encPerm σ).wt ≤ 4 * (W + 1) ^ 4 := fun σ =>
    (wt_encPerm_le σ).trans (by omega)
  -- step 1: the constant pair
  have a0 := Det.arg' (P := P) (vs := inp) (rest := []) (j := 0) (v := .list ctxL) rfl
  have a1 := Det.arg' (P := P) (vs := inp) (rest := []) (j := 1) (v := encPerm h) rfl
  have g10 := Det.get' a0 (Det.nat 10) (vs := ctxL) (v := tmJLocCtx m q) rfl
  have hcst := tmJH_cst_spec (q := q) hA.hcst hA.hiv hA.hrep hA.hpr h
  have c1 := (Det.call (Det.mk2 a1 g10) hcst).mono (c' := 10 ^ 17 * (W + 1) ^ 16) (by
    have wl := wt_list2_le (encPerm h) (tmJLocCtx m q)
    have hK : tmJHCstK ((m + 1) * (q + 1)) ≤ 10 ^ 16 * (W + 1) ^ 16 := by
      unfold tmJHCstK
      calc 10 ^ 16 * ((m + 1) * (q + 1)) ^ 8 ≤ 10 ^ 16 * ((W + 1) ^ 2) ^ 8 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hV 8)
        _ = 10 ^ 16 * (W + 1) ^ 16 := by rw [← pow_mul]
    have := wP (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
      (tmJP ((fun _ => h : Fin q → Perm (Fin m)), (1 : Perm (Fin q)))))
    omega)
  refine EvalAll.letE c1 (fun v1 k1 h1 => ?_)
  obtain ⟨rfl, hk1⟩ := h1
  -- step 2: the factorization `x₀ = g w`
  have b0 := Det.arg' (P := P) (vs := inp) (rest := [encPerm (tmJHCs q h)]) (j := 0)
    (v := .list ctxL) rfl
  have bG := Det.get' b0 (Det.nat 0) (vs := ctxL) (v := encGroup gsG) rfl
  have bN := Det.get' b0 (Det.nat 1) (vs := ctxL) (v := encGroup gsNq) rfl
  have bx := Det.var' (P := P) (env := [Val.list inp, encPerm (tmJHCs q h)]) (i := 1)
    (v := encPerm (tmJHCs q h)) rfl
  have c2 := normalizedFactor_call hfac hjf (Det.mk3 bG bN bx) (G := gens gsG) (N := gens gsNq)
    ⟨gsG, rfl, rfl⟩ ⟨gsNq, rfl, rfl⟩ hnorm hx
  refine EvalAll.letE c2 (fun v2 k2 h2 => ?_)
  obtain ⟨⟨g, hg, w, hw, hxe, rfl⟩, hk2⟩ := h2
  have hk2' : k2 ≤ 10 ^ 4 * (W + 1) ^ 4 + (normalizedFactorPrim hfac).c *
      (22 * (W + 1) ^ 4) ^ (normalizedFactorPrim hfac).k := by
    have wl := wt_list3_le (encGroup gsG) (encGroup gsNq) (encPerm (tmJHCs q h))
    have := wP (tmJHCs q h)
    have hb := tmJL_prim_le (normalizedFactorPrim hfac)
      (v := .list [encGroup gsG, encGroup gsNq, encPerm (tmJHCs q h)])
      (W := 20 * (W + 1) ^ 4) (by omega)
    have hb' : (normalizedFactorPrim hfac).c * (20 * (W + 1) ^ 4 + 2) ^
        (normalizedFactorPrim hfac).k ≤ (normalizedFactorPrim hfac).c *
        (22 * (W + 1) ^ 4) ^ (normalizedFactorPrim hfac).k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega
  -- step 3: the local transporter `z`
  have wv2 : (Val.list [encPerm g, encPerm w]).wt ≤ 22 * (W + 1) ^ 4 := by
    have := wt_list2_le (encPerm g) (encPerm w)
    have := wP g
    have := wP w
    omega
  have e0 := Det.arg' (P := P) (vs := inp)
    (rest := [encPerm (tmJHCs q h), .list [encPerm g, encPerm w]]) (j := 0) (v := .list ctxL) rfl
  have e1 := Det.arg' (P := P) (vs := inp)
    (rest := [encPerm (tmJHCs q h), .list [encPerm g, encPerm w]]) (j := 1) (v := encPerm h) rfl
  have e2 := Det.get' e0 (Det.nat 2) (vs := ctxL) (v := .list vs) rfl
  have e3 := Det.get' e0 (Det.nat 3) (vs := ctxL) (v := .list (σN.map encPerm)) rfl
  have e10 := Det.get' e0 (Det.nat 10) (vs := ctxL) (v := tmJLocCtx m q) rfl
  have eq := Det.get' e10 (Det.nat 2) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat q) rfl
  have em := Det.get' e10 (Det.nat 3) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat m) rfl
  have eL := Det.snoc (Det.mk4 e1 e2 e3 eq) em
  simp only [List.cons_append, List.nil_append] at eL
  have hL := tmJL_spec hm hfac hA.hL hjmem hjf hq0 H N hn σN hσN x y Ac hAdef vs hvs h hmatch
  have c3 := tmJH_callA eL hL
  refine EvalAll.letE c3 (fun v3 k3 h3 => ?_)
  obtain ⟨⟨d', π', hd', rfl⟩, -, hk3⟩ := h3
  have wl5 := wt_list_le [encPerm h, .list vs, .list (σN.map encPerm), .nat q, .nat m]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wl5
  have wLi : (Val.list [encPerm h, .list vs, .list (σN.map encPerm), .nat q, .nat m]).wt + 1 ≤
      10 * (W + 1) := by omega
  have hk3' : k3 ≤ 10 ^ 3 * (W + 1) ^ 4 + 2 * (tmJLK (membershipPrim hm)
      (normalizedFactorPrim hfac) * (10 * (W + 1)) ^ tmJLD (membershipPrim hm)
        (normalizedFactorPrim hfac)) := by
    have hB' := Nat.mul_le_mul_left (tmJLK (membershipPrim hm) (normalizedFactorPrim hfac))
      (Nat.pow_le_pow_left wLi (tmJLD (membershipPrim hm) (normalizedFactorPrim hfac)))
    have wl4 := wt_list4_le (encPerm h) (.list vs) (.list (σN.map encPerm)) (.nat q)
    have wlc := wt_list4_le (encPerm (1 : Perm (Fin m))) (encPerm (1 : Perm (Fin q))) (.nat q)
      (.nat m)
    omega
  -- step 4: the tail on `u = z⁻¹ g`
  obtain ⟨d, π, hd, hu, hex, hTl⟩ := hcorr g hg ⟨w, hw, hxe⟩ d' π' hd'
  have f0 := Det.arg' (P := P) (vs := inp) (rest := [encPerm (tmJHCs q h),
    .list [encPerm g, encPerm w], encPerm (tmJHPm d' π')]) (j := 0) (v := .list ctxL) rfl
  have f3 := Det.var' (P := P) (env := [Val.list inp, encPerm (tmJHCs q h),
    .list [encPerm g, encPerm w], encPerm (tmJHPm d' π')]) (i := 3) (v := encPerm (tmJHPm d' π')) rfl
  have f2 := Det.var' (P := P) (env := [Val.list inp, encPerm (tmJHCs q h),
    .list [encPerm g, encPerm w], encPerm (tmJHPm d' π')]) (i := 2)
    (v := .list [encPerm g, encPerm w]) rfl
  have fg := Det.get' f2 (Det.nat 0) (vs := [encPerm g, encPerm w]) (v := encPerm g) rfl
  have fi := Det.call f3 (inv_spec hA.hiv (tmJHPm d' π'))
  have fc := Det.call (Det.mk2 fi fg) (compose_spec hA.hcomp (tmJHPm d' π')⁻¹ g)
  rw [hu] at fc
  have hTs := hT hA hjm hjh gsG gsNq vs σS σN hle hk lg Tl Bm M hcert hlg hB hm0
    (tmJHPm d' π') d π hd hex hTl
  rw [hctx] at hTs
  have c4 := tmJH_callA (Det.mk3 f0 f3 fc) (hTs.mono fun o c hc => (show (∃ (c' : Fin lg.length → ℤ)
      (odd : Bool), tmJSumT N φ lg c' = tmJLab N φ d ∧ (odd = true ↔ sign π = -1) ∧
      o = encPerm (tmJHPm d' π' * toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
        (tmJCorrE Tl odd lg c'))) ∧ _ from
    ⟨let ⟨c', odd, h1, h2, h3, _⟩ := hc; ⟨c', odd, h1, h2, h3⟩,
      let ⟨_, _, _, _, _, h4⟩ := hc; h4⟩))
  refine c4.mono ?_
  rintro o c ⟨⟨cv, odd, hsum, hodd, rfl⟩, -, hc⟩
  refine ⟨⟨g, hg, ⟨w, hw, hxe⟩, d', π', hd', d, π, cv, odd, hd, hu, hsum, hodd, rfl⟩, ?_⟩
  -- the cost
  simp only [tmJHPm, tmJHCs] at *
  have wo := wP (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d', π')) *
    toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJCorrE Tl odd lg cv))
  have wz := wP (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d', π')))
  have wzi := wP (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d', π')))⁻¹
  have wgg := wP g
  have wu := wP (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π)))
  have wl2 := wt_list2_le (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))
    (tmJP (d', π')))⁻¹) (encPerm g)
  have wl3 := wt_list3_le (Val.list ctxL)
    (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d', π'))))
    (encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π))))
  have hTin : (Val.list [Val.list ctxL,
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d', π'))),
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJP (d, π)))]).wt + 1 ≤
      21 * (W + 1) ^ 4 := by omega
  have hTc := Nat.mul_le_mul_left Kt (Nat.pow_le_pow_left hTin Dt)
  have hI : invK * (m * q + 1) ^ 4 ≤ 100000 * (W + 1) ^ 8 := by
    unfold invK; exact Nat.mul_le_mul_left _ hn4
  have hP : permK * (m * q + 1) ^ 3 ≤ 30000 * (W + 1) ^ 8 := by
    unfold permK; exact Nat.mul_le_mul_left _ (hn3.trans hp68)
  unfold tmJHMainBud
  generalize Kt * (21 * (W + 1) ^ 4) ^ Dt = T at *
  generalize tmJLK (membershipPrim hm) (normalizedFactorPrim hfac) *
    (10 * (W + 1)) ^ tmJLD (membershipPrim hm) (normalizedFactorPrim hfac) = L at *
  generalize (normalizedFactorPrim hfac).c *
    (22 * (W + 1) ^ 4) ^ (normalizedFactorPrim hfac).k = F at *
  omega

end GI.Impl
