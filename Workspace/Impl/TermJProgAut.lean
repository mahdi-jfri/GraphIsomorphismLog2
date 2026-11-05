module

public import Workspace.Impl.TermJProgAutP

@[expose] public section

/-!
# The generators of `Aut_J(x)` (program)

`tmJAutF`, on `[ctx, us]` with the context `ctx = tmJHCtx …` of `tmJ_prep_spec`, returns the
three lists of generators of `tmJ_autJ_gens` (paper, proof of Theorem A.23, the paragraph on
`Aut_J(X)`), as permutations of `Fin (m q)`:

1. `S1`: the local `N*`-stabilizers `tmJLoc a s` of all rows (`tmJ_ns_all`);
2. `S2`: the products `tmJLam lg c` for the rows `c` of a kernel matrix of the sum map
   (`tmJSol_ker_spec_poly`, then `tmJ_s2_spec`); empty when `σN = []`;
3. `S3`: the products `t₀ t` for the triples `t` of `Tl`, with `t₀` the first one
   (`tmJ_swS_det`, `tmJ_ts_det`); empty when `Tl = []`.

`tmJ_aut_spec` states the result.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val encPerm encGroup encPerms gens encIntMatrix NormalizedIntersection
  HermiteFullRank)

variable {m q : ℕ}

/-- The third list: `t₀ t` for the triples `t` of `Tl`, with `t₀` the first one. -/
def tmJS3List : List (Fin q × Fin q × Perm (Fin m)) → List (Perm (Fin m × Fin q))
  | [] => []
  | x :: Tl => tmJTsList (tmJSw x.1 x.2.1 x.2.2) (x :: Tl)

/-- **An `if` whose branches have specifications.** -/
theorem tmJ_iteAll {P : Program} {env : List Val} {c t e : Expr} {x cc C : ℕ}
    {Q : Val → Prop} (hc : Det P env c (.nat x) cc)
    (ht : x ≠ 0 → EvalAll P env t (fun w c => Q w ∧ c ≤ C))
    (he : x = 0 → EvalAll P env e (fun w c => Q w ∧ c ≤ C)) :
    EvalAll P env (.ite c t e) (fun w c' => Q w ∧ c' ≤ cc + 2 * C + 1) := by
  refine EvalAll.ite hc (fun _ _ h => ⟨x, h.1⟩) fun y cc' h => ?_
  obtain ⟨h1, h2⟩ := h
  injection h1 with h1
  subst h1
  split_ifs with hy
  · exact (he hy).wt_lt.mono fun w cb hw => ⟨hw.1.1, by omega⟩
  · exact (ht hy).wt_lt.mono fun w cb hw => ⟨hw.1.1, by omega⟩

/-- **A `let` whose value has a specification.** -/
theorem tmJ_letAll {P : Program} {env : List Val} {a body : Expr} {B C : ℕ}
    {R Q : Val → Prop} (ha : EvalAll P env a (fun w c => R w ∧ c ≤ B))
    (hb : ∀ w, R w → w.wt < B → EvalAll P (env ++ [w]) body (fun u c => Q u ∧ c ≤ C)) :
    EvalAll P env (.letE a body) (fun u c => Q u ∧ c ≤ B + 2 * C + 1) :=
  EvalAll.letE ha.wt_lt fun w cw hw =>
    (hb w hw.1.1 (by have := hw.1.2; have := hw.2; omega)).wt_lt.mono fun u cu hu =>
      ⟨hu.1.1, by have := hw.1.2; have := hu.1.2; have := hu.2; omega⟩

/-- Entry `i` of the first triple of `Tl` (entry `7` of the context). -/
def tmJAutHd (i : ℕ) : Expr := .get (.get (.get (arg 0) (.nat 7)) (.nat 0)) (.nat i)

/-- On `[ctx, us]`: the three lists of generators of `Aut_J`, appended. -/
def tmJAutF (ns ker s2 ts sw app : ℕ) : Expr :=
  .letE (.call ns (mk3 (arg 1) (.get (arg 0) (.nat 10)) (.get (arg 0) (.nat 4))))
  (.letE (.ite (.length (.get (arg 0) (.nat 3)))
      (.letE (.call ker (mk2 (.get (arg 0) (.nat 9)) (.get (arg 0) (.nat 8))))
        (.call s2 (mk3 (.get (arg 0) (.nat 6)) (.var 2) (.get (arg 0) (.nat 10)))))
      .nil)
  (.letE (.ite (.length (.get (arg 0) (.nat 7)))
      (.call ts (mk2 (mk2 (.get (arg 0) (.nat 10))
          (.call sw (mk4 (tmJAutHd 2) (.get (arg 0) (.nat 10)) (tmJAutHd 0) (tmJAutHd 1))))
        (.get (arg 0) (.nat 7))))
      .nil)
  (.call app (mk2 (.call app (mk2 (.var 1) (.var 2))) (.var 3)))))

/-- Where the pieces of `tmJAutF` sit. -/
structure TmJAutAt (P : Program) (f ns ker s2 ts sw app jni jh : ℕ) : Prop where
  hf : P.funs[f]? = some (tmJAutF ns ker s2 ts sw app)
  hns : ∃ rg mpR row mp locA dsA tbA tbe pr prg prt prte fl app',
    TmJNsAt P ns rg mpR row jni mp locA dsA tbA tbe pr prg prt prte fl app'
  hker : ∃ kb, ker = kb + 1 ∧ P.HasAt kb (tmJSolFuns kb jh)
  hs2 : ∃ mp lam fld st pw dc pp comp iv locA dsA rg tbA tbe pr prg prt prte,
    TmJS2At P s2 mp lam fld st pw dc pp comp iv locA dsA rg tbA tbe pr prg prt prte
  hts : ∃ mp e cp iv tbD swDE tbP swPE pr prg prt prte,
    P.funs[ts]? = some (tmJTsF mp) ∧ P.HasAt mp (mapFuns mp e) ∧
    P.funs[e]? = some (tmJTsEF sw cp) ∧ P.funs[sw]? = some (tmJSwSF iv tbD tbP pr) ∧
    P.HasAt iv (invFuns iv) ∧ P.HasAt tbD (mapFuns tbD swDE) ∧
    P.funs[swDE]? = some tmJSwDEF ∧ P.HasAt tbP (mapFuns tbP swPE) ∧
    P.funs[swPE]? = some tmJSwPEF ∧ TmJPairAt P pr prg prt prte ∧ P.HasAt cp (composeFuns cp)
  happ : P.HasAt app (appendFuns app)

theorem tmJTsPK_mono : Monotone tmJTsPK := by
  intro a b h
  unfold tmJTsPK
  gcongr

theorem tmJNsPK_mono (p : Prim) : Monotone (tmJNsPK p) := by
  intro a b h
  unfold tmJNsPK Prim.boundSize tmJNsK
  gcongr

/-- The bound of `tmJAutF`, in the input weight `W`, a primitive bound `p` and the constants
of the kernel step. -/
def tmJAutK (p : Prim) (Kk Dk W : ℕ) : ℕ :=
  10 ^ 4 * (W + tmJNsPK p (6 * W + 7) + Kk * (4 * W + 7) ^ Dk +
    tmJS2K (4 * W + 2 * (Kk * (4 * W + 7) ^ Dk) + 7) + 10 ^ 14 * (8 * W + 9) ^ 16 +
    tmJTsPK (6 * W + 4 * (10 ^ 14 * (8 * W + 9) ^ 16) + 18) +
    6 * loopModK * (2 * (tmJNsPK p (6 * W + 7) +
      tmJS2K (4 * W + 2 * (Kk * (4 * W + 7) ^ Dk) + 7)) + 30) ^ 2 +
    6 * loopModK * (12 * (tmJNsPK p (6 * W + 7) +
      tmJS2K (4 * W + 2 * (Kk * (4 * W + 7) ^ Dk) + 7)) +
      2 * tmJTsPK (6 * W + 4 * (10 ^ 14 * (8 * W + 9) ^ 16) + 18) + 200) ^ 2 + 100)

theorem tmJAutK_poly (p : Prim) (Kk Dk : ℕ) : TmJPoly (tmJAutK p Kk Dk) := by
  have hW : TmJPoly fun W => W := TmJPoly.id
  have hN : TmJPoly fun W => tmJNsPK p (6 * W + 7) :=
    TmJPoly.comp_mono (tmJNsPK_poly p) (tmJNsPK_mono p)
      (TmJPoly.add (TmJPoly.smul 6 hW) (TmJPoly.const 7))
  have hK : TmJPoly fun W => Kk * (4 * W + 7) ^ Dk :=
    TmJPoly.smul _ (TmJPoly.pow (TmJPoly.add (TmJPoly.smul 4 hW) (TmJPoly.const 7)) _)
  have hS2 : TmJPoly fun W => tmJS2K (4 * W + 2 * (Kk * (4 * W + 7) ^ Dk) + 7) := by
    unfold tmJS2K
    exact TmJPoly.smul _ (TmJPoly.pow (TmJPoly.add (TmJPoly.add (TmJPoly.add
      (TmJPoly.smul 4 hW) (TmJPoly.smul 2 hK)) (TmJPoly.const 7)) (TmJPoly.const 1)) _)
  have hSw : TmJPoly fun W => 10 ^ 14 * (8 * W + 9) ^ 16 :=
    TmJPoly.smul _ (TmJPoly.pow (TmJPoly.add (TmJPoly.smul 8 hW) (TmJPoly.const 9)) _)
  have hT : TmJPoly fun W => tmJTsPK (6 * W + 4 * (10 ^ 14 * (8 * W + 9) ^ 16) + 18) :=
    TmJPoly.comp_mono tmJTsPK_poly tmJTsPK_mono
      (TmJPoly.add (TmJPoly.add (TmJPoly.smul 6 hW) (TmJPoly.smul 4 hSw)) (TmJPoly.const 18))
  have hA1 : TmJPoly fun W => 6 * loopModK * (2 * (tmJNsPK p (6 * W + 7) +
      tmJS2K (4 * W + 2 * (Kk * (4 * W + 7) ^ Dk) + 7)) + 30) ^ 2 :=
    TmJPoly.smul _ (TmJPoly.pow (TmJPoly.add (TmJPoly.smul 2 (TmJPoly.add hN hS2))
      (TmJPoly.const 30)) 2)
  have hA2 : TmJPoly fun W => 6 * loopModK * (12 * (tmJNsPK p (6 * W + 7) +
      tmJS2K (4 * W + 2 * (Kk * (4 * W + 7) ^ Dk) + 7)) +
      2 * tmJTsPK (6 * W + 4 * (10 ^ 14 * (8 * W + 9) ^ 16) + 18) + 200) ^ 2 :=
    TmJPoly.smul _ (TmJPoly.pow (TmJPoly.add (TmJPoly.add (TmJPoly.smul 12 (TmJPoly.add hN hS2))
      (TmJPoly.smul 2 hT)) (TmJPoly.const 200)) 2)
  unfold tmJAutK
  exact TmJPoly.smul _ (TmJPoly.add (TmJPoly.add (TmJPoly.add (TmJPoly.add (TmJPoly.add
    (TmJPoly.add (TmJPoly.add (TmJPoly.add hW hN) hK) hS2) hSw) hT) hA1) hA2) (TmJPoly.const 100))

theorem tmJ_finRange_map_closure {n : ℕ} {G : Type*} [AddCommGroup G] (K : Fin n → G) :
    {c | c ∈ (List.finRange n).map K} = Set.range K := by
  ext c
  simp [List.mem_map, List.mem_finRange, Set.mem_range]

theorem tmJ_wt_append_le (xs ys : List Val) :
    (Val.list (xs ++ ys)).wt ≤ 3 * (Val.list [.list xs, .list ys]).wt + 4 := by
  have sxy := sum_wt_lt_wt_list [Val.list xs, Val.list ys]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at sxy
  have sx := sum_wt_lt_wt_list xs
  have sy := sum_wt_lt_wt_list ys
  have lx := length_lt_wt_list xs
  have ly := length_lt_wt_list ys
  have := wt_list_le (xs ++ ys)
  simp only [List.map_append, List.sum_append, List.length_append] at this
  omega

/-- What the program returns: the three lists of `tmJ_autJ_gens`. -/
def tmJAutOut (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m))))
    (σS σN : List (Perm (Fin m))) (lg : List (Fin q × Perm (Fin m)))
    (Tl : List (Fin q × Fin q × Perm (Fin m))) (Bm : Matrix (Fin lg.length) (Fin σN.length) ℤ)
    (M : Matrix (Fin σN.length) (Fin σN.length) ℤ) (out : Val) : Prop :=
  ∃ (hsA : Fin q → List (Perm (Fin m))) (Ks : List (Fin lg.length → ℤ)),
    (∀ a r gs, O a a = some (r, gs) → gens (hsA a) = gens gs ⊓ gens σS) ∧
    (σN = [] → Ks = []) ∧
    (σN ≠ [] → ∀ c, c ∈ AddSubgroup.closure {c | c ∈ Ks} ↔
      ∃ y : Fin σN.length → ℤ, Matrix.vecMul c Bm + Matrix.vecMul y M = 0) ∧
    out = tmJPermsVal (tmJNsList hsA ++ Ks.map (tmJLam lg) ++ tmJS3List Tl)

set_option backward.isDefEq.respectTransparency false in
/-- **The generators of `Aut_J(x)`.** -/
theorem tmJ_aut_spec (hni : NormalizedIntersection) (hH : HermiteFullRank) :
    ∃ K D : ℕ, ∀ {P : Program} {f ns ker s2 ts sw app jni jh : ℕ},
      TmJAutAt P f ns ker s2 ts sw app jni jh →
      P.prims[jni]? = some (normalizedIntersectionPrim hni) →
      P.prims[jh]? = some (linHermitePrim hH) →
      ∀ {m q : ℕ} (gsG gsNq : List (Perm (Fin (m * q)))) (vs : List Val)
        (σS σN : List (Perm (Fin m))) (lg : List (Fin q × Perm (Fin m)))
        (Tl : List (Fin q × Fin q × Perm (Fin m)))
        (Bm : Matrix (Fin lg.length) (Fin σN.length) ℤ)
        (M : Matrix (Fin σN.length) (Fin σN.length) ℤ), M.det ≠ 0 →
      ∀ (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) (us : List Val),
        (∀ a a' : Fin q, us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (O a a'))) →
        (∀ a, ∃ r gs, O a a = some (r, gs) ∧ GI.Multicoset.Normalizes (gens gs) (gens σS)) →
      FunAll P f (.list [tmJHCtx gsG gsNq vs σS σN lg Tl Bm M, .list us]) (fun out cost =>
        tmJAutOut O σS σN lg Tl Bm M out ∧
        cost ≤ K * ((Val.list [tmJHCtx gsG gsNq vs σS σN lg Tl Bm M, .list us]).wt + 1) ^ D) := by
  obtain ⟨Kk, Dk, hKer⟩ := tmJSol_ker_spec_poly hH
  obtain ⟨K, D, hKD⟩ := tmJAutK_poly (normalizedIntersectionPrim hni) Kk Dk
  refine ⟨K, D, ?_⟩
  intro P f ns ker s2 ts sw app jni jh hA hjni hjh m q gsG gsNq vs σS σN lg Tl Bm M hM O us hus
    hloc
  obtain ⟨rg, mpR, row, mp, locA, dsA, tbA, tbe, pr, prg, prt, prte, fl, app', hNs⟩ := hA.hns
  obtain ⟨kb, rfl, hkb⟩ := hA.hker
  obtain ⟨mp2, lam, fld, st, pw, dc, pp, comp, iv2, locA2, dsA2, rg2, tbA2, tbe2, pr2, prg2, prt2,
    prte2, hS2⟩ := hA.hs2
  obtain ⟨mpT, eT, cp, iv, tbD, swDE, tbP, swPE, prT, prgT, prtT, prteT, htsf, hmpT, heT, hswf,
    hiv, htbD, hswDE, htbP, hswPE, hprT, hcp⟩ := hA.hts
  refine FunAll.intro hA.hf ?_
  unfold tmJAutF
  -- the context as a list
  obtain ⟨L, hL⟩ : ∃ L : List Val, [encGroup gsG, encGroup gsNq, .list vs,
      .list (σN.map encPerm), encGroup σS, encGroup σN, tmJLgVal lg, tmJTlVal Tl,
      encIntMatrix Bm, encIntMatrix M, tmJLocCtx m q] = L := ⟨_, rfl⟩
  have hctx : tmJHCtx gsG gsNq vs σS σN lg Tl Bm M = .list L := by rw [← hL]; rfl
  rw [hctx]
  obtain ⟨W, hW⟩ : ∃ W, (Val.list [.list L, .list us]).wt = W := ⟨_, rfl⟩
  rw [hW]
  have wL : (Val.list L).wt < W := hW ▸ wt_le_wt_list (by simp)
  have wus : (Val.list us).wt < W := hW ▸ wt_le_wt_list (by simp)
  have wE : ∀ (i : ℕ) (v : Val), L[i]? = some v → v.wt < W := by
    intro i v hv
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hv
    exact (wt_getElem_lt L i hi).trans wL
  have hlc : L[10]? = some (tmJLocCtx m q) := by rw [← hL]; rfl
  have heS : L[4]? = some (encGroup σS) := by rw [← hL]; rfl
  have hσN : L[3]? = some (.list (σN.map encPerm)) := by rw [← hL]; rfl
  have hlg : L[6]? = some (tmJLgVal lg) := by rw [← hL]; rfl
  have htl : L[7]? = some (tmJTlVal Tl) := by rw [← hL]; rfl
  have hbm : L[8]? = some (encIntMatrix Bm) := by rw [← hL]; rfl
  have hMm : L[9]? = some (encIntMatrix M) := by rw [← hL]; rfl
  have wlc := wE 10 _ hlc
  have weS := wE 4 _ heS
  have wσN := wE 3 _ hσN
  have wlg := wE 6 _ hlg
  have wtl := wE 7 _ htl
  have wbm := wE 8 _ hbm
  have wMm := wE 9 _ hMm
  have gE : ∀ (rest : List Val) (i : ℕ) (v : Val), L[i]? = some v →
      Det P (Val.list [.list L, .list us] :: rest) (.get (arg 0) (.nat i)) v
        (2 * W + i + v.wt + 9) := by
    intro rest i v hv
    refine (Det.get' (Det.arg' (P := P) (vs := [.list L, .list us]) (rest := rest) (j := 0)
      (v := .list L) rfl) (Det.nat i) hv).mono ?_
    rw [hW]; omega
  -- the bounds
  obtain ⟨Bn, hBn⟩ : ∃ Bn, tmJNsPK (normalizedIntersectionPrim hni) (6 * W + 7) = Bn := ⟨_, rfl⟩
  obtain ⟨Bk, hBk⟩ : ∃ Bk, Kk * (4 * W + 7) ^ Dk = Bk := ⟨_, rfl⟩
  obtain ⟨Bs2, hBs2⟩ : ∃ Bs2, tmJS2K (4 * W + 2 * Bk + 7) = Bs2 := ⟨_, rfl⟩
  obtain ⟨Bsw, hBsw⟩ : ∃ Bsw, 10 ^ 14 * (8 * W + 9) ^ 16 = Bsw := ⟨_, rfl⟩
  obtain ⟨Bts, hBts⟩ : ∃ Bts, tmJTsPK (6 * W + 4 * Bsw + 18) = Bts := ⟨_, rfl⟩
  obtain ⟨Ba1, hBa1⟩ : ∃ Ba1, 6 * loopModK * (2 * (Bn + Bs2) + 30) ^ 2 = Ba1 := ⟨_, rfl⟩
  obtain ⟨Ba2, hBa2⟩ : ∃ Ba2, 6 * loopModK * (12 * (Bn + Bs2) + 2 * Bts + 200) ^ 2 = Ba2 :=
    ⟨_, rfl⟩
  obtain ⟨Sb, hSb⟩ : ∃ Sb, W + Bn + Bk + Bs2 + Bsw + Bts + Ba1 + Ba2 + 100 = Sb := ⟨_, rfl⟩
  have hK : tmJAutK (normalizedIntersectionPrim hni) Kk Dk W = 10 ^ 4 * Sb := by
    unfold tmJAutK
    rw [← hSb, ← hBa2, ← hBa1, ← hBts, ← hBsw, ← hBs2, ← hBk, ← hBn]
  have hfin : 10 ^ 4 * Sb ≤ K * (W + 1) ^ D := hK ▸ hKD W
  -- step 1: the local `N*`-stabilizers
  have dNs := tmJ_ns_all hni hNs hjni O us hus σS hloc
  have wNin : (Val.list [.list us, tmJLocCtx m q, encGroup σS]).wt ≤ 6 * W + 7 := by
    have := wt_list3_le (.list us) (tmJLocCtx m q) (encGroup σS); omega
  have dNs' := dNs.mono (Q' := fun w c => (∃ hsA : Fin q → List (Perm (Fin m)),
      w = tmJPermsVal (tmJNsList hsA) ∧
      ∀ a r gs, O a a = some (r, gs) → gens (hsA a) = gens gs ⊓ gens σS) ∧ c ≤ Bn)
    fun w c h => ⟨h.1, h.2.trans (hBn ▸ tmJNsPK_mono _ wNin)⟩
  have a1 := Det.arg' (P := P) (vs := [.list L, .list us]) (rest := []) (j := 1)
    (v := .list us) rfl
  have c1 := (Det.mk3 a1 (gE [] 10 _ hlc) (gE [] 4 _ heS)).mono (c' := 40 * Sb) (by
    rw [hW]; omega)
  refine (tmJ_letCall (C := 1400 * Sb) c1 dNs' ?_).mono fun u cu hu => ⟨hu.1, by omega⟩
  rintro s1V ⟨hsA, rfl, hsA'⟩ ws1
  -- step 2: the kernel rows and their products (empty when `σN = []`)
  have wnil : (Val.list []).wt ≤ 10 := by
    have hw : (Val.list []).wt = 4 := by simp [Val.wt, GI.Lang.cellWt, GI.Machine.len_zero]
    omega
  refine (tmJ_letAll (B := 310 * Sb) (C := 500 * Sb)
    (R := fun w => (∃ Ks : List (Fin lg.length → ℤ), (σN = [] → Ks = []) ∧
      (σN ≠ [] → ∀ c, c ∈ AddSubgroup.closure {c | c ∈ Ks} ↔
        ∃ y : Fin σN.length → ℤ, Matrix.vecMul c Bm + Matrix.vecMul y M = 0) ∧
      w = tmJPermsVal (Ks.map (tmJLam lg))) ∧ w.wt ≤ Bs2 + 10) ?_ ?_).mono
    fun u cu hu => ⟨hu.1, by omega⟩
  · have hlen := Det.length (gE [tmJPermsVal (tmJNsList hsA)] 3 _ hσN)
    refine (tmJ_iteAll (C := 150 * Sb) hlen ?_ ?_).mono fun w c h => ⟨h.1, by
      have := h.2; have := wt_nat_le (σN.map encPerm).length
      have := length_lt_wt_list (σN.map encPerm); omega⟩
    · intro hx
      have ht : 0 < σN.length := by
        rw [List.length_map] at hx; exact Nat.pos_of_ne_zero hx
      have hσ : σN ≠ [] := by
        intro h; rw [h] at ht; exact absurd ht (by simp)
      have dK := hKer hkb hjh ht M hM Bm
      have wKin : (Val.list [encIntMatrix M, encIntMatrix Bm]).wt + 1 ≤ 4 * W + 7 := by
        have := wt_list2_le (encIntMatrix M) (encIntMatrix Bm); omega
      have dK' := dK.mono (Q' := fun w c => tmJSolKerAnswer M Bm w ∧ c ≤ Bk) fun w c h =>
        ⟨h.1, h.2.trans (hBk ▸ Nat.mul_le_mul_left _ (Nat.pow_le_pow_left wKin _))⟩
      have kA := (Det.mk2 (gE [tmJPermsVal (tmJNsList hsA)] 9 _ hMm)
        (gE [tmJPermsVal (tmJNsList hsA)] 8 _ hbm)).mono (c' := 40 * Sb) (by
          have := wt_list2_le (encIntMatrix M) (encIntMatrix Bm); omega)
      refine (tmJ_letCall (C := 50 * Sb) kA dK' ?_).mono fun w c h => ⟨h.1, by omega⟩
      rintro kV ⟨Km, rfl, hK1, -⟩ wk
      have dS := tmJ_s2_spec hS2 lg Km
      have wSin : (Val.list [tmJLgVal lg, encIntMatrix Km, tmJLocCtx m q]).wt ≤
          4 * W + 2 * Bk + 7 := by
        have := wt_list3_le (tmJLgVal lg) (encIntMatrix Km) (tmJLocCtx m q); omega
      have hS2c : tmJS2K (Val.list [tmJLgVal lg, encIntMatrix Km, tmJLocCtx m q]).wt ≤ Bs2 := by
        rw [← hBs2]; unfold tmJS2K
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      have wSout := FunDet.wt_lt dS
      have sA := (Det.mk3 (gE [tmJPermsVal (tmJNsList hsA), encIntMatrix Km] 6 _ hlg)
        (Det.var' (P := P) (env := [Val.list [.list L, .list us], tmJPermsVal (tmJNsList hsA),
          encIntMatrix Km]) (i := 2) (v := encIntMatrix Km) rfl)
        (gE [tmJPermsVal (tmJNsList hsA), encIntMatrix Km] 10 _ hlc)).mono (c' := 40 * Sb) (by
          have := wt_list3_le (tmJLgVal lg) (encIntMatrix Km) (tmJLocCtx m q); omega)
      refine (tmJ_lastCall sA dS).mono fun w c h => ⟨⟨⟨(List.finRange lg.length).map Km,
        fun h' => absurd h' hσ, fun _ e => ?_, ?_⟩, ?_⟩, by omega⟩
      · rw [tmJ_finRange_map_closure]; exact hK1 e
      · rw [h.1]; simp only [List.map_map, Function.comp_def]
      · rw [h.1]; omega
    · intro hx
      have hσ : σN = [] := by
        rw [List.length_map] at hx; exact List.eq_nil_of_length_eq_zero hx
      refine EvalAll.mono Det.nil fun w c h => ⟨⟨⟨[], fun _ => rfl, fun h' => absurd hσ h', ?_⟩,
        ?_⟩, by omega⟩
      · rw [h.1]; rfl
      · rw [h.1]; omega
  rintro s2V ⟨⟨Ks, hKs1, hKs2, rfl⟩, ws2⟩ ws2'
  -- step 3: the products `t₀ t` (empty when `Tl = []`)
  refine (tmJ_letAll (B := 210 * Sb) (C := 100 * Sb)
    (R := fun w => w = tmJPermsVal (tmJS3List Tl) ∧ w.wt ≤ Bts + 10) ?_ ?_).mono
    fun u cu hu => ⟨hu.1, by omega⟩
  · have h7 := gE [tmJPermsVal (tmJNsList hsA), tmJPermsVal (Ks.map (tmJLam lg))] 7 _ htl
    have hlen := Det.length (vs := Tl.map tmJTrVal) h7
    refine (tmJ_iteAll (C := 100 * Sb) hlen ?_ ?_).mono fun w c h => ⟨h.1, by
      have := h.2; have := wt_nat_le (Tl.map tmJTrVal).length
      have := length_lt_wt_list (Tl.map tmJTrVal)
      have : (Val.list (Tl.map tmJTrVal)).wt = (tmJTlVal Tl).wt := rfl
      omega⟩
    · intro hx
      have hne : Tl ≠ [] := fun h => hx (by rw [h]; rfl)
      obtain ⟨x, Tl', rfl⟩ := List.exists_cons_of_ne_nil hne
      have hd := Det.get' h7 (Det.nat 0) (vs := (x :: Tl').map tmJTrVal) (v := tmJTrVal x) rfl
      have wx : (tmJTrVal x).wt < W := by
        have : (tmJTrVal x).wt < (Val.list ((x :: Tl').map tmJTrVal)).wt :=
          wt_le_wt_list (by simp)
        have e : (Val.list ((x :: Tl').map tmJTrVal)).wt = (tmJTlVal (x :: Tl')).wt := rfl
        omega
      have e0 := Det.get' hd (Det.nat 0) (vs := [.nat x.1, .nat x.2.1, encPerm x.2.2])
        (v := .nat x.1) rfl
      have e1 := Det.get' hd (Det.nat 1) (vs := [.nat x.1, .nat x.2.1, encPerm x.2.2])
        (v := .nat x.2.1) rfl
      have e2 := Det.get' hd (Det.nat 2) (vs := [.nat x.1, .nat x.2.1, encPerm x.2.2])
        (v := encPerm x.2.2) rfl
      have wb : (encPerm x.2.2).wt < (tmJTrVal x).wt := wt_le_wt_list (by simp)
      have wa : (Val.nat x.1).wt < (tmJTrVal x).wt := wt_le_wt_list (by simp)
      have wa' : (Val.nat x.2.1).wt < (tmJTrVal x).wt := wt_le_wt_list (by simp)
      have glc := gE [tmJPermsVal (tmJNsList hsA), tmJPermsVal (Ks.map (tmJLam lg))] 10 _ hlc
      have dSw := tmJ_swS_det hswf hiv htbD hswDE htbP hswPE hprT x.1 x.2.1 x.2.2
      have wSwin : (Val.list [encPerm x.2.2, tmJLocCtx m q, .nat x.1, .nat x.2.1]).wt + 1 ≤
          8 * W + 9 := by
        have := wt_list4_le (encPerm x.2.2) (tmJLocCtx m q) (.nat x.1) (.nat x.2.1); omega
      have hSwc : 10 ^ 14 * ((Val.list [encPerm x.2.2, tmJLocCtx m q, .nat x.1,
          .nat x.2.1]).wt + 1) ^ 16 ≤ Bsw := by
        rw [← hBsw]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left wSwin _)
      have wSw := FunDet.wt_lt dSw
      have swc := Det.call (Det.mk4 e2 glc e0 e1) dSw
      have dTs := tmJ_ts_det htsf hmpT heT hswf hiv htbD hswDE htbP hswPE hprT hcp
        (tmJSw x.1 x.2.1 x.2.2) (x :: Tl')
      have wTsin : (Val.list [.list [tmJLocCtx m q, encPerm (toFin (finProdFinEquiv :
          Fin m × Fin q ≃ Fin (m * q)) (tmJSw x.1 x.2.1 x.2.2))], tmJTlVal (x :: Tl')]).wt ≤
          6 * W + 4 * Bsw + 18 := by
        have := wt_list2_le (.list [tmJLocCtx m q, encPerm (toFin (finProdFinEquiv :
          Fin m × Fin q ≃ Fin (m * q)) (tmJSw x.1 x.2.1 x.2.2))]) (tmJTlVal (x :: Tl'))
        have := wt_list2_le (tmJLocCtx m q) (encPerm (toFin (finProdFinEquiv :
          Fin m × Fin q ≃ Fin (m * q)) (tmJSw x.1 x.2.1 x.2.2)))
        omega
      have hTsc : tmJTsPK (Val.list [.list [tmJLocCtx m q, encPerm (toFin (finProdFinEquiv :
          Fin m × Fin q ≃ Fin (m * q)) (tmJSw x.1 x.2.1 x.2.2))], tmJTlVal (x :: Tl')]).wt ≤ Bts := by
        rw [← hBts]; exact tmJTsPK_mono wTsin
      have wTs := FunDet.wt_lt dTs
      have tsc := (Det.call (Det.mk2 (Det.mk2 glc swc) h7) dTs).mono (c' := 100 * Sb) (by
        have := wt_list4_le (encPerm x.2.2) (tmJLocCtx m q) (.nat x.1) (.nat x.2.1)
        have := wt_list2_le (.list [tmJLocCtx m q, encPerm (toFin (finProdFinEquiv :
          Fin m × Fin q ≃ Fin (m * q)) (tmJSw x.1 x.2.1 x.2.2))]) (tmJTlVal (x :: Tl'))
        have := wt_list2_le (tmJLocCtx m q) (encPerm (toFin (finProdFinEquiv :
          Fin m × Fin q ≃ Fin (m * q)) (tmJSw x.1 x.2.1 x.2.2)))
        omega)
      refine EvalAll.mono tsc fun w c h => ⟨⟨by rw [h.1]; rfl, by rw [h.1]; omega⟩, h.2⟩
    · intro hx
      have hT : Tl = [] := by
        rw [List.length_map] at hx; exact List.eq_nil_of_length_eq_zero hx
      subst hT
      refine EvalAll.mono Det.nil fun w c h => ⟨⟨by rw [h.1]; rfl, by rw [h.1]; omega⟩, by omega⟩
  rintro s3V ⟨rfl, ws3⟩ ws3'
  -- the body: append the three lists
  obtain ⟨xs, hxs⟩ : ∃ xs : List Val, (tmJNsList hsA).map (fun σ =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ)) = xs := ⟨_, rfl⟩
  obtain ⟨ys, hys⟩ : ∃ ys : List Val, (Ks.map (tmJLam lg)).map (fun σ =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ)) = ys := ⟨_, rfl⟩
  obtain ⟨zs, hzs⟩ : ∃ zs : List Val, (tmJS3List Tl).map (fun σ =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ)) = zs := ⟨_, rfl⟩
  have e1 : tmJPermsVal (tmJNsList hsA) = .list xs := by rw [← hxs]; rfl
  have e2 : tmJPermsVal (Ks.map (tmJLam lg)) = .list ys := by rw [← hys]; rfl
  have e3 : tmJPermsVal (tmJS3List Tl) = .list zs := by rw [← hzs]; rfl
  rw [e1] at ws1; rw [e2] at ws2; rw [e3] at ws3
  have v1 := Det.var' (P := P) (env := [Val.list [.list L, .list us], tmJPermsVal (tmJNsList hsA),
    tmJPermsVal (Ks.map (tmJLam lg)), tmJPermsVal (tmJS3List Tl)]) (i := 1) (v := .list xs)
    (by rw [e1]; rfl)
  have v2 := Det.var' (P := P) (env := [Val.list [.list L, .list us], tmJPermsVal (tmJNsList hsA),
    tmJPermsVal (Ks.map (tmJLam lg)), tmJPermsVal (tmJS3List Tl)]) (i := 2) (v := .list ys)
    (by rw [e2]; rfl)
  have v3 := Det.var' (P := P) (env := [Val.list [.list L, .list us], tmJPermsVal (tmJNsList hsA),
    tmJPermsVal (Ks.map (tmJLam lg)), tmJPermsVal (tmJS3List Tl)]) (i := 3) (v := .list zs)
    (by rw [e3]; rfl)
  have w1 := wt_list2_le (.list xs) (.list ys)
  have hA1 : 6 * loopModK * ((Val.list [.list xs, .list ys]).wt + 1) ^ 2 ≤ Ba1 := by
    rw [← hBa1]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have o1 := tmJ_wt_append_le xs ys
  have ap1 := Det.call (Det.mk2 v1 v2) (tmJ_app_det hA.happ xs ys)
  have w2 := wt_list2_le (.list (xs ++ ys)) (.list zs)
  have hA2 : 6 * loopModK * ((Val.list [.list (xs ++ ys), .list zs]).wt + 1) ^ 2 ≤ Ba2 := by
    rw [← hBa2]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have o2 := tmJ_wt_append_le (xs ++ ys) zs
  have ap2 := (Det.call (Det.mk2 ap1 v3) (tmJ_app_det hA.happ (xs ++ ys) zs)).mono
    (c' := 100 * Sb) (by omega)
  refine EvalAll.mono ap2 fun w c h => ⟨⟨hsA, Ks, hsA', hKs1, hKs2, ?_⟩, h.2⟩
  rw [h.1, ← hxs, ← hys, ← hzs]
  simp only [tmJPermsVal, List.map_append]

end GI.Impl
