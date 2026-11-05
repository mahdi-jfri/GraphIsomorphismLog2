module

public import Workspace.Impl.TermJHProg2
public import Workspace.Impl.TermJSolPoly
public import Workspace.Impl.PolyBd
public import Workspace.Lang.Lib.LinIntColumn

@[expose] public section

/-!
# The transporter of one label: the context and the coefficients

* `tmJHCtx`: the context of the per-label program, a list of eleven slots.
* `tmJHCoefF`, on `[ctx, tmJDsVal d]`: a vector `c` with `∏ φ(g_k)^{c_k} = lab(d)`
  (`tmJH_coef_spec`). If the quotient `⟨σN⟩ / ⟨σS⟩` has no generators, every label is `1` and
  `c = 0`. Otherwise the program writes `∏ (d i)⁻¹` in the coordinates (`tmJV_sum_spec`, which
  calls the cited constructive membership) and solves `s + c B + y M = 0`
  (`tmJSol_solve_spec_poly`, which calls the cited Hermite normal form).
* `tmJH_poly`: a uniform bound `PBU` in one variable gives `f W ≤ K (W + 1)^D`.
-/

namespace GI.Impl

open GI.Lang GI.Assembly GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens encInt encIntMatrix)
open scoped IsMulCommutative

/-! ### Polynomial bounds in one variable -/

theorem tmJH_poly {f : ℕ → ℕ} (h : PBU fun _ W _ => f W) :
    ∃ K D : ℕ, ∀ W, f W ≤ K * (W + 1) ^ D := by
  obtain ⟨C, D, h⟩ := h
  refine ⟨C * 2 ^ D, D, fun W => ?_⟩
  have h1 := h 0 W 0
  unfold PB at h1
  have h2 : (W + 0 + 0 + 2) ^ D ≤ 2 ^ D * (W + 1) ^ D := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) D
  calc f W ≤ C * (W + 0 + 0 + 2) ^ D := h1
    _ ≤ C * (2 ^ D * (W + 1) ^ D) := Nat.mul_le_mul_left _ h2
    _ = C * 2 ^ D * (W + 1) ^ D := by ring

/-! ### The context -/

variable {m q : ℕ}

/-- **The context of the per-label program.** Its slots are
0. the generators of `G|_dom` on `Fin (m q)`,
1. the generators of `N^q` on `Fin (m q)`,
2. the answers `vs` of the row transporters (the input of `tmJLF`),
3. the generators `σN` of `N` as a list of permutations (the input of `tmJLF`),
4. and 5. the groups `⟨σS⟩` and `⟨σN⟩` of the Lin* presentation,
6. the pairs `lg` of the local generators,
7. the triples `Tl` of the lifted transpositions,
8. the matrix `B` (row `k` is the coordinate vector of `g_k`),
9. the relation matrix `M`,
10. the local context `tmJLocCtx m q`. -/
def tmJHCtx (gsG gsNq : List (Perm (Fin (m * q)))) (vs : List Val) (σS σN : List (Perm (Fin m)))
    (lg : List (Fin q × Perm (Fin m))) (Tl : List (Fin q × Fin q × Perm (Fin m)))
    (Bm : Matrix (Fin lg.length) (Fin σN.length) ℤ)
    (M : Matrix (Fin σN.length) (Fin σN.length) ℤ) : Val :=
  .list [encGroup gsG, encGroup gsNq, .list vs, .list (σN.map encPerm), encGroup σS, encGroup σN,
    tmJLgVal lg, tmJTlVal Tl, encIntMatrix Bm, encIntMatrix M, tmJLocCtx m q]

/-! ### The coefficients -/

/-- The entry of the zero vector: `encInt 0`. -/
def tmJHZeroF : Expr := mk2 (.nat 0) .nil

/-- On `[ctx, tmJDsVal d]`: `[1, linVecVal c]` with `∏ φ(g_k)^{c_k} = lab(d)`. -/
def tmJHCoefF (sol vsum zm : ℕ) : Expr :=
  .ite (.length (.get (arg 0) (.nat 3)))
    (.call sol (mk3 (.get (arg 0) (.nat 9)) (.get (arg 0) (.nat 8))
      (.call vsum (mk3 (.get (arg 0) (.nat 4)) (.get (arg 0) (.nat 5)) (arg 1)))))
    (mk2 (.nat 1) (.call zm (mk2 .nil (.get (arg 0) (.nat 6)))))

/-- Where the pieces of the coefficient program sit. -/
structure TmJHCoefAt (P : Program) (f sol jh vsum jm zm z0 : ℕ) : Prop where
  hf : P.funs[f]? = some (tmJHCoefF sol vsum zm)
  hsol : P.HasAt sol (tmJSolFuns sol jh)
  hvsum : P.HasAt vsum (tmJVSumFuns vsum jm)
  hzm : P.HasAt zm (mapFuns zm z0)
  hz0 : P.funs[z0]? = some tmJHZeroF

/-- A call of a function with a result property and a cost bound, after a deterministic
argument. -/
theorem tmJH_callA {P : Program} {env : List Val} {a : Expr} {f : ℕ} {v : Val} {ca B : ℕ}
    {R : Val → Prop} (ha : Det P env a v ca) (hf : FunAll P f v (fun w c => R w ∧ c ≤ B)) :
    EvalAll P env (.call f a) (fun w c => R w ∧ w.wt < B ∧ c ≤ ca + 2 * B + 1) :=
  EvalAll.call_funAll ha fun v' ca' h => by
    obtain ⟨rfl, h'⟩ := h
    exact hf.wt_lt.mono fun w cb hw => ⟨hw.1.1, by omega, by omega⟩

/-- The same after an argument with a specification. -/
theorem tmJH_callE {P : Program} {env : List Val} {a : Expr} {f : ℕ} {Ra : Val → ℕ → Prop}
    {R : Val → Val → Prop} {B : Val → ℕ → ℕ} (ha : EvalAll P env a Ra)
    (hf : ∀ v ca, Ra v ca → FunAll P f v (fun w c => R v w ∧ c ≤ B v ca)) :
    EvalAll P env (.call f a) (fun w c => ∃ v ca, Ra v ca ∧ R v w ∧ w.wt < B v ca ∧
      c ≤ ca + 2 * B v ca + 1) :=
  EvalAll.call_funAll ha fun v ca h => (hf v ca h).wt_lt.mono fun w cb hw =>
    ⟨v, ca, h, hw.1.1, by omega, by omega⟩

theorem tmJH_encInt_zero : encInt (0 : ℤ) = .list [.nat 0, .list []] := rfl

theorem tmJH_forall₂_const {xs ws : List Val} {v : Val} (h : List.Forall₂ (fun _ w => w = v) xs ws) :
    ws = List.replicate xs.length v := by
  induction h with
  | nil => rfl
  | cons h _ ih => subst h; rw [ih]; rfl

theorem tmJH_linVec_zero (n : ℕ) :
    linVecVal (0 : Fin n → ℤ) = .list (List.replicate n (encInt 0)) := by
  unfold linVecVal
  congr 1
  simp [List.map_const']

/-- The budget of the coefficient program, in the weight `W` of its input. -/
def tmJHCoefBud (K1 D1 K2 D2 W : ℕ) : ℕ :=
  10 ^ 8 * (W + 1) ^ 2 + 10 * (K1 * (6 * W + 8) ^ D1) +
    10 * (K2 * (4 * W + 2 * (K1 * (6 * W + 8) ^ D1) + 8) ^ D2)

theorem tmJH_coefBud_poly (K1 D1 K2 D2 : ℕ) : PBU fun _ W _ => tmJHCoefBud K1 D1 K2 D2 W := by
  unfold tmJHCoefBud
  have hV1 : PBU fun _ W _ => K1 * (6 * W + 8) ^ D1 :=
    PBU.smul K1 (PBU.pow (PBU.addc (PBU.smul 6 PBU.W) 8) D1)
  exact PBU.add (PBU.add (PBU.smul _ (PBU.pow (PBU.addc PBU.W 1) 2)) (PBU.smul 10 hV1))
    (PBU.smul 10 (PBU.smul K2 (PBU.pow (PBU.addc (PBU.add (PBU.smul 4 PBU.W) (PBU.smul 2 hV1)) 8)
      D2)))

set_option maxHeartbeats 2000000 in
/-- **The coefficient program.** -/
theorem tmJH_coef_spec (hm : GI.Cited.ConstructiveMembership) (hH : GI.Cited.HermiteFullRank) :
    ∃ K D : ℕ, ∀ {P : Program} {f sol jh vsum jm zm z0 : ℕ}, TmJHCoefAt P f sol jh vsum jm zm z0 →
      P.prims[jm]? = some (linMembershipPrim hm) → P.prims[jh]? = some (linHermitePrim hH) →
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
        ∀ (d : Fin q → Perm (Fin m)), (∀ i, d i ∈ N) →
        (∃ e : Fin lg.length → ℤ, tmJSumT N φ lg e = tmJLab N φ d) →
        FunAll P f (.list [tmJHCtx gsG gsNq vs σS σN lg Tl Bm M, tmJDsVal d]) (fun out cost =>
          ∃ c : Fin lg.length → ℤ, out = .list [.nat 1, linVecVal c] ∧
            tmJSumT N φ lg c = tmJLab N φ d ∧
            cost ≤ K * ((Val.list [tmJHCtx gsG gsNq vs σS σN lg Tl Bm M, tmJDsVal d]).wt + 1) ^ D) := by
  obtain ⟨K1, D1, hV⟩ := tmJV_sum_spec hm
  obtain ⟨K2, D2, hS⟩ := tmJSol_solve_spec_poly hH
  obtain ⟨K, D, hKD⟩ := tmJH_poly (tmJH_coefBud_poly K1 D1 K2 D2)
  refine ⟨K, D, fun {P f sol jh vsum jm zm z0} hA hjm hjh {m q N A _ φ} gsG gsNq vs σS σN _ _
    hle hk lg Tl Bm M hcert hlg hB d hd hex => ?_⟩
  refine FunAll.intro hA.hf ?_
  unfold tmJHCoefF
  -- names for the slots
  set ctxL : List Val := [encGroup gsG, encGroup gsNq, .list vs, .list (σN.map encPerm),
    encGroup σS, encGroup σN, tmJLgVal lg, tmJTlVal Tl, encIntMatrix Bm, encIntMatrix M,
    tmJLocCtx m q] with hctxL
  have hctx : tmJHCtx gsG gsNq vs σS σN lg Tl Bm M = .list ctxL := rfl
  rw [hctx]
  set inp : List Val := [.list ctxL, tmJDsVal d] with hinp
  set W := (Val.list inp).wt with hW
  refine EvalAll.mono (Q := fun out cost => ∃ c : Fin lg.length → ℤ,
    out = .list [.nat 1, linVecVal c] ∧ tmJSumT N φ lg c = tmJLab N φ d ∧
      cost ≤ tmJHCoefBud K1 D1 K2 D2 W) ?_
    (by rintro out cost ⟨c, h1, h2, h3⟩; exact ⟨c, h1, h2, h3.trans (hKD W)⟩)
  -- weights
  have wc : (Val.list ctxL).wt < W := wt_le_wt_list (by simp [hinp])
  have wds : (tmJDsVal d).wt < W := wt_le_wt_list (by simp [hinp])
  have wsl : ∀ v ∈ ctxL, v.wt < W := fun v hv => (wt_le_wt_list hv).trans wc
  have w3 := wsl (.list (σN.map encPerm)) (by simp [hctxL])
  have w4 := wsl (encGroup σS) (by simp [hctxL])
  have w5 := wsl (encGroup σN) (by simp [hctxL])
  have w6 := wsl (tmJLgVal lg) (by simp [hctxL])
  have w8 := wsl (encIntMatrix Bm) (by simp [hctxL])
  have w9 := wsl (encIntMatrix M) (by simp [hctxL])
  have hlen : (σN.map encPerm).length = σN.length := by simp
  have hlenl : σN.length < W := by
    have := length_lt_wt_list (σN.map encPerm)
    rw [hlen] at this; omega
  have hlg_len : lg.length < W := by
    have := length_lt_wt_list (lg.map fun p => Val.list [.nat p.1, encPerm p.2])
    simp only [List.length_map] at this
    change lg.length < (tmJLgVal lg).wt at this
    omega
  -- the slot reads
  have a0 := Det.arg' (P := P) (vs := inp) (rest := []) (j := 0) (v := .list ctxL) rfl
  have a1 := Det.arg' (P := P) (vs := inp) (rest := []) (j := 1) (v := tmJDsVal d) rfl
  have g3 := Det.get' a0 (Det.nat 3) (vs := ctxL) (v := .list (σN.map encPerm)) rfl
  have g4 := Det.get' a0 (Det.nat 4) (vs := ctxL) (v := encGroup σS) rfl
  have g5 := Det.get' a0 (Det.nat 5) (vs := ctxL) (v := encGroup σN) rfl
  have g6 := Det.get' a0 (Det.nat 6) (vs := ctxL) (v := tmJLgVal lg) rfl
  have g8 := Det.get' a0 (Det.nat 8) (vs := ctxL) (v := encIntMatrix Bm) rfl
  have g9 := Det.get' a0 (Det.nat 9) (vs := ctxL) (v := encIntMatrix M) rfl
  have cl := Det.length g3
  rw [hlen] at cl
  refine EvalAll.ite cl (fun _ _ h => ⟨_, h.1⟩) fun x cc hx => ?_
  obtain ⟨hx1, hx2⟩ := hx
  cases hx1
  by_cases ht : σN.length = 0
  · -- no generators: `c = 0`
    rw [if_pos ht]
    have h0 : σN = [] := List.length_eq_zero_iff.1 ht
    have hz : ∀ x ∈ lg.map (fun p => Val.list [.nat p.1, encPerm p.2]),
        FunAll P z0 (.list [.list [], x]) (fun w cost => w = encInt 0 ∧ cost ≤ 100) := by
      intro x _
      refine FunAll.intro hA.hz0 ?_
      unfold tmJHZeroF
      refine EvalAll.mono (Det.mk2 (Det.nat 0) Det.nil (P := P) (env := [.list [.list [], x]])) ?_
      rintro w c ⟨rfl, hc⟩
      refine ⟨rfl, hc.trans ?_⟩
      decide
    have hmap : FunAll P zm (.list [.list [], tmJLgVal lg]) (fun w cost =>
        w = linVecVal (0 : Fin lg.length → ℤ) ∧ cost ≤ 2 * 10 ^ 6 * (W + 1) ^ 2) := by
      refine (map_spec hA.hzm hz).mono ?_
      rintro w cost ⟨ws, rfl, hws, hcb⟩
      have hws' := tmJH_forall₂_const hws
      simp only [List.length_map] at hws'
      subst hws'
      refine ⟨(tmJH_linVec_zero _).symm, ?_⟩
      have hsum : ((lg.map fun p => Val.list [.nat p.1, encPerm p.2]).map fun _ => 100).sum =
          lg.length * 100 := by
        rw [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul]
      rw [hsum] at hcb
      have hwr : (Val.list (List.replicate lg.length (encInt 0))).wt ≤ 300 * (lg.length + 1) := by
        have := wt_list_le (List.replicate lg.length (encInt 0))
        simp only [List.map_replicate, List.sum_replicate, List.length_replicate,
          smul_eq_mul] at this
        have e0 : (encInt (0 : ℤ)).wt ≤ 100 := by decide
        nlinarith
      have w2 := wt_list2_le (.list []) (tmJLgVal lg)
      have wn : (Val.list []).wt ≤ 5 := by decide
      have hlgv : (Val.list [Val.list [], tmJLgVal lg]).wt = (Val.list [Val.list [],
        .list (lg.map fun p => Val.list [.nat p.1, encPerm p.2])]).wt := rfl
      have hW1 : lg.length + 1 ≤ W + 1 := by omega
      have hp : mapK * ((lg.map fun p => Val.list [.nat p.1, encPerm p.2]).length + 1) *
          ((Val.list [Val.list [], .list (lg.map fun p => Val.list [.nat p.1, encPerm p.2])]).wt +
          (Val.list (List.replicate lg.length (encInt 0))).wt + 1) ≤
          1000 * (W + 1) * (1000 * (W + 1)) := by
        unfold mapK
        rw [List.length_map]
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hW1) (by omega)
      have e2 : 1000 * (W + 1) * (1000 * (W + 1)) = 1000000 * (W + 1) ^ 2 := by ring
      have hW2 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
      omega
    have cz := tmJH_callA (Det.mk2 Det.nil g6) hmap
    refine (EvalAll.mk2_last (Det.nat 1) cz).mono ?_
    rintro out cost ⟨vb, cb, ⟨rfl, hwb, hcb⟩, rfl, hcost⟩
    refine ⟨0, rfl, tmJH_triv hk h0 lg d hd, ?_⟩
    -- the cost
    have w2 := wt_list2_le (.list []) (tmJLgVal lg)
    have w2' := wt_list2_le (.nat 1) (linVecVal (0 : Fin lg.length → ℤ))
    have wn : (Val.list []).wt ≤ 5 := by decide
    have wn1 : (Val.nat 1).wt ≤ 3 := by decide
    have hW2 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    unfold tmJHCoefBud
    omega
  · -- generators: write the offset vector and solve
    rw [if_neg ht]
    have hus : ∀ u ∈ (List.finRange q).map (fun i => (d i)⁻¹), u ∈ gens σN := by
      intro u hu
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hu
      exact (gens σN).inv_mem ((hk.1 _).1 (hd i))
    have hds : tmJDsVal d = .list (((List.finRange q).map fun i => (d i)⁻¹).map encPerm) := by
      unfold tmJDsVal; rw [List.map_map]; rfl
    have hv := hV hA.hvsum hjm σS σN hle ((List.finRange q).map fun i => (d i)⁻¹) hus
    rw [← hds] at hv
    have cv := tmJH_callA (Det.mk3 g4 g5 a1) hv
    have cs := tmJH_callE (EvalAll.snoc_det (Det.mk2 g9 g8) cv)
      (R := fun v out => ∃ s : Fin σN.length → ℤ,
        v = .list [encIntMatrix M, encIntMatrix Bm, linVecVal s] ∧
        Additive.ofMul ((((List.finRange q).map fun i => (d i)⁻¹).map fun u =>
          QuotientGroup.mk' ((gens σS).subgroupOf (gens σN)) (linIntoSubgroup (gens σN) u)).prod) =
          tmJHF σS σN s ∧ tmJSolSolveAnswer M Bm s out)
      (B := fun v _ => K2 * (v.wt + 1) ^ D2) (fun v ca h => by
        obtain ⟨w, cb, ⟨⟨s, rfl, hs⟩, -, -⟩, rfl, -⟩ := h
        exact (hS hA.hsol hjh (Nat.pos_of_ne_zero ht) M hcert.1 Bm s).mono
          fun out c h => ⟨⟨s, rfl, hs, h.1⟩, h.2⟩)
    refine cs.mono ?_
    rintro out cost ⟨v, ca, ⟨w, cw, ⟨⟨s0, rfl, hs0⟩, hwt, hcw⟩, rfl, hca⟩,
      ⟨s, hvs, hs, hans⟩, hwo, hcb⟩
    have hss : s0 = s := by
      have h1 : linVecVal s0 = linVecVal s := by
        simp only [List.cons_append, List.nil_append, Val.list.injEq, List.cons.injEq] at hvs
        exact hvs.2.2.1
      exact linVecVal_injective h1
    subst hss
    rcases hans with ⟨rfl, hno⟩ | ⟨c, rfl, y, hcy⟩
    · exact absurd (tmJH_solvable hk hcert hlg Bm hB d hd hs hex) hno
    refine ⟨c, rfl, tmJH_sound hk hcert.2.2.1 hlg Bm hB d hd hs hcy, ?_⟩
    -- the cost
    simp only [List.nil_append, List.cons_append] at hca hcb hwo
    have wi3 := wt_list3_le (encGroup σS) (encGroup σN) (tmJDsVal d)
    have hX : (Val.list [encGroup σS, encGroup σN, tmJDsVal d]).wt + 1 ≤ 6 * W + 8 := by omega
    have hV1 : K1 * ((Val.list [encGroup σS, encGroup σN, tmJDsVal d]).wt + 1) ^ D1 ≤
        K1 * (6 * W + 8) ^ D1 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX _)
    have wi3' := wt_list3_le (encIntMatrix M) (encIntMatrix Bm) (linVecVal s0)
    have hY : (Val.list [encIntMatrix M, encIntMatrix Bm, linVecVal s0]).wt + 1 ≤
        4 * W + 2 * (K1 * (6 * W + 8) ^ D1) + 8 := by omega
    have hV2 : K2 * ((Val.list [encIntMatrix M, encIntMatrix Bm, linVecVal s0]).wt + 1) ^ D2 ≤
        K2 * (4 * W + 2 * (K1 * (6 * W + 8) ^ D1) + 8) ^ D2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hY _)
    have wo' := wt_list2_le (.nat 1) (linVecVal c)
    have wn1 : (Val.nat 1).wt ≤ 3 := by decide
    have wg := wt_list2_le (encIntMatrix M) (encIntMatrix Bm)
    have hW2 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    unfold tmJHCoefBud
    omega

end GI.Impl
