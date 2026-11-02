import Workspace.Impl.GenProdCoord
import Workspace.Impl.GenProdSplice
import Workspace.Impl.GenProdTabs

/-!
# The product refinement: the new hierarchy

On `[h', t, m, l, r, lead, k, ids]`, where `h'` is the exposed hierarchy `pre ++ top :: post` and
`t = |pre|`, `phier_spec` computes the hierarchy `pre ++ coordHier ++ post` of the product
refinement: the ratio `binom(m, l)`, the clamped cap `min(cap top, binom(m, l))` and the origin
of `top`, the `r` coordinate intervals (`cvAll_spec`), and the splice (`splice_spec`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)

/-- The minimum of two numbers, by a comparison. -/
def minE (a b : Expr) : Expr := .ite (.arith .lt a b) a b

theorem Det.minE {P : Program} {env : List Val} {a b : Expr} {x y ca cb : ℕ}
    (ha : Det P env a (.nat x) ca) (hb : Det P env b (.nat y) cb) :
    Det P env (minE a b) (.nat (min x y))
    (2 * ca + 2 * cb + (Val.nat x).wt + (Val.nat y).wt + 10) := by
  by_cases h : x < y
  · have hc := Det.arith' (op := .lt) ha hb (z := 1) (by simp [Machine.BinOp.eval, h])
    have := Det.ite_pos (e := b) hc one_ne_zero ha
    rw [min_eq_left h.le]
    exact this.mono (by omega)
  · have hc := Det.arith' (op := .lt) ha hb (z := 0) (by simp [Machine.BinOp.eval, h])
    have := Det.ite_zero (t := a) hc hb
    rw [min_eq_right (not_lt.1 h)]
    exact this.mono (by omega)

/-- The new hierarchy, on `[h', t, m, l, r, lead, k, ids]`. -/
def phierE (bch bcv bspl : ℕ) : Expr :=
  .letE (.call bch (mk2 (arg 2) (arg 3)))
  (.letE (.get (arg 0) (arg 1))
  (.letE (.call bcv (Expr.mkList [arg 5, arg 6, arg 4, .var 1,
      minE (.get (.var 2) (.nat 2)) (.var 1), .get (.var 2) (.nat 3), arg 7]))
  (.call bspl (mk3 (arg 0) (arg 1) (.var 3)))))

def phierK : ℕ := 10 ^ 60

section math

variable {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S) {m l r : ℕ}
  (E : Fin Q.d ≃ (Fin r → Product.KSet m l)) {k : ℕ} (e : Ω ≃ Fin k)

include Q E e in
/-- The ratio of a coordinate interval is at most the number of points. -/
theorem choose_le_card (hr : 1 ≤ r) : m.choose l ≤ k := by
  have hd := Q.card_kset_pow E
  have hdk := Q.d_le_card e
  have : m.choose l ≤ m.choose l ^ r := Nat.le_self_pow (by omega) _
  omega

/-- **The spliced hierarchy.** -/
theorem hierValC_splice {hv : List Val} (hH : List.Forall₂ (IntervalValC e) hv
      (Q.pre ++ Q.top :: Q.post)) {M : List Val} {J : List (Interval Ω)}
    (hM : List.Forall₂ (IntervalValC e) M J) :
    HierValC e (.list (hv.take Q.pre.length ++ M ++ hv.drop (Q.pre.length + 1)))
      (Q.pre ++ J ++ Q.post) := by
  refine ⟨_, rfl, ?_⟩
  have h1 := List.forall₂_take Q.pre.length hH
  have h2 := List.forall₂_drop (Q.pre.length + 1) hH
  rw [List.take_left' rfl] at h1
  have e2 : (Q.pre ++ Q.top :: Q.post).drop (Q.pre.length + 1) = Q.post := by
    rw [← List.drop_drop, List.drop_left' rfl]; rfl
  rw [e2] at h2
  exact List.rel_append (List.rel_append h1 hM) h2

end math

theorem phier_cost {X Z k m l r c1 c2 c3 c4 cw tw Mw ow capw ow' lw iw cc ch : ℕ}
    (hZ : Z = X + k * k + m + l + 1) (hk : r + 1 ≤ k * k) (hc : ch ≤ k)
    (h1 : c1 ≤ 2 * (2 * X + 8) + 2 * (2 * (m + 2 + (l + 2)) + 6) + 7 +
      10 ^ 5 * (l + 1) * (2 * (m + 2 + (l + 2)) + 6 + l + m + 10) ^ 2 + cw + 1)
    (hcw : cw ≤ ch + 2)
    (h2 : c2 ≤ 2 * X + 5 + (2 * X + 6) + tw + 1) (htw : tw < X)
    (h3 : c3 ≤ 7 * (20 * X + 100 + 2 * capw + 2 * ow' + 4 * cw + 4 * tw + cc + 1) + 5 +
      10 ^ 8 * (cc + r + 10) ^ 4 + Mw + 1)
    (hcap : capw + ow' ≤ tw)
    (hcc : cc ≤ 2 * (lw + (k + 2) + (r + 2) + cw + (ch + 2) + ow' + iw) + 11)
    (hlw : lw ≤ 4 * (k * k + 1) ^ 2) (hiw : iw ≤ 4 * (k + 1) ^ 2)
    (hMw : Mw < 10 ^ 8 * (cc + r + 10) ^ 4)
    (h4 : c4 ≤ 3 * (2 * X + 7) + Mw + 3 * (2 * (X + (r + 2) + Mw) + 7) + 8 +
      10 ^ 6 * (2 * (X + (r + 2) + Mw) + 7 + 1) ^ 3 + ow + 1)
    (how : ow ≤ 10 ^ 6 * (2 * (X + (r + 2) + Mw) + 7 + 1) ^ 3) :
    c1 + (c2 + (c3 + c4 + ow + 1) + ow + 1) + ow + 1 ≤ phierK * Z ^ 24 := by
  have hZ1 : 1 ≤ Z := by omega
  have hkk : k ≤ k * k := Nat.le_mul_self k
  -- the context of the coordinate intervals
  have hk2 : (k * k + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hk2' : (k + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have p12 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  have hcc' : cc + r + 10 ≤ 60 * Z ^ 2 := by omega
  have hc4 := Nat.pow_le_pow_left hcc' 4
  have e4 : (60 * Z ^ 2) ^ 4 = 12960000 * Z ^ 8 := by ring
  rw [e4] at hc4
  have hM8 : 10 ^ 8 * (cc + r + 10) ^ 4 ≤ 10 ^ 8 * (12960000 * Z ^ 8) := Nat.mul_le_mul_left _ hc4
  -- the splice
  have p28 : Z ^ 2 ≤ Z ^ 8 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have hs : 2 * (X + (r + 2) + Mw) + 7 + 1 ≤ 10 ^ 16 * Z ^ 8 := by omega
  have hs3 := Nat.pow_le_pow_left hs 3
  have e3 : (10 ^ 16 * Z ^ 8) ^ 3 = 10 ^ 48 * Z ^ 24 := by ring
  rw [e3] at hs3
  have hS : 10 ^ 6 * (2 * (X + (r + 2) + Mw) + 7 + 1) ^ 3 ≤ 10 ^ 6 * (10 ^ 48 * Z ^ 24) :=
    Nat.mul_le_mul_left _ hs3
  -- the binomial coefficient
  have hb : 2 * (m + 2 + (l + 2)) + 6 + l + m + 10 ≤ 30 * Z := by omega
  have hb2 := Nat.pow_le_pow_left hb 2
  have hb3 := Nat.mul_le_mul (show l + 1 ≤ Z by omega) hb2
  have e2 : Z * (30 * Z) ^ 2 = 900 * Z ^ 3 := by ring
  rw [e2] at hb3
  have hB : 10 ^ 5 * (l + 1) * (2 * (m + 2 + (l + 2)) + 6 + l + m + 10) ^ 2 ≤
      10 ^ 5 * (900 * Z ^ 3) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hb3
  have p38 : Z ^ 3 ≤ Z ^ 8 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have p824 : Z ^ 8 ≤ Z ^ 24 := Nat.pow_le_pow_right hZ1 (by norm_num)
  unfold phierK
  generalize 10 ^ 6 * (2 * (X + (r + 2) + Mw) + 7 + 1) ^ 3 = SP at *
  generalize 10 ^ 8 * (cc + r + 10) ^ 4 = CV at *
  generalize 10 ^ 5 * (l + 1) * (2 * (m + 2 + (l + 2)) + 6 + l + m + 10) ^ 2 = CH at *
  generalize (k * k + 1) ^ 2 = A at *
  generalize (k + 1) ^ 2 = B at *
  omega

/-- **The new hierarchy as a program.** -/
theorem phier_spec {P : Program} {f bch bcv bspl bapp fcv bmap fl bfind ft : ℕ}
    (hf : P.funs[f]? = some (phierE bch bcv bspl)) (hch : P.HasAt bch (chooseFuns bch))
    (hcv : P.HasAt bcv (cvAllFuns bcv fcv)) (hfcv : P.funs[fcv]? = some (cvF bmap))
    (hmap : P.HasAt bmap (mapFuns bmap fl)) (hfl : P.funs[fl]? = some (cvLabF bfind))
    (hfind : P.HasAt bfind (findFuns bfind ft)) (hft : P.funs[ft]? = some cvTestF)
    (hspl : P.HasAt bspl (spliceFuns bspl bapp)) (happ : P.HasAt bapp (appendFuns bapp))
    {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S) {m l r : ℕ}
    (E : Fin Q.d ≃ (Fin r → Product.KSet m l)) (hr : 1 ≤ r) {k : ℕ} (e : Ω ≃ Fin k)
    {hv : Val} (hH : HierValC e hv (Q.pre ++ Q.top :: Q.post)) :
    FunAll P f (.list [hv, .nat Q.pre.length, .nat m, .nat l, .nat r, encFun (leadF Q E e),
        .nat k, encFun fun j : Fin k => (j : ℕ)])
      (fun w c => HierValC e w (Q.pre ++ Q.coordHier E ++ Q.post) ∧
        c ≤ phierK * ((Val.list [hv, .nat Q.pre.length, .nat m, .nat l, .nat r,
          encFun (leadF Q E e), .nat k, encFun fun j : Fin k => (j : ℕ)]).wt + k * k + m + l +
          1) ^ 24) := by
  obtain ⟨vs, rfl, hF⟩ := hH
  set t := Q.pre.length with ht
  set xs : List Val := [.list vs, .nat t, .nat m, .nat l, .nat r, encFun (leadF Q E e), .nat k,
    encFun fun j : Fin k => (j : ℕ)] with hxs
  set x := Val.list xs with hx
  obtain ⟨X, hX⟩ : ∃ X, X = x.wt := ⟨_, rfl⟩
  have ha : ∀ (j : ℕ) (v : Val), xs[j]? = some v → ∀ rest : List Val,
      Det P (x :: rest) (arg j) v (2 * X + j + 5) := fun j v hj rest => by
    rw [hX]; exact Det.arg' hj
  have hlen := hF.length_eq
  simp only [List.length_append, List.length_cons] at hlen
  have htl : t < vs.length := by omega
  -- the top interval
  obtain ⟨pv, -, htop⟩ : IntervalValC e vs[t] Q.top := by
    have := (List.forall₂_iff_get.1 hF).2 t htl (by simp; omega)
    simpa [List.get_eq_getElem, ht] using this
  -- the ratio
  set c := m.choose l with hc
  have d1 : Det P [x] (.call bch (mk2 (arg 2) (arg 3))) (.nat c)
      ((2 * X + 2 + 5) + (2 * X + 3 + 5) + 2 * (Val.list [.nat m, .nat l]).wt + 7 +
        numK * (l + 1) * ((Val.list [.nat m, .nat l]).wt + l + m + 10) ^ 2 + (Val.nat c).wt + 1) :=
    Det.call (Det.mk2 (ha 2 _ rfl []) (ha 3 _ rfl [])) (choose_spec hch m l)
  -- the top interval as a value
  set tv := vs[t] with htv
  have d2 : Det P [x, .nat c] (.get (arg 0) (arg 1)) tv
      ((2 * X + 0 + 5) + (2 * X + 1 + 5) + tv.wt + 1) :=
    Det.get' (ha 0 _ rfl _) (ha 1 _ rfl _) (by simp [htv, htl])
  -- the coordinate intervals
  set env3 := [x, .nat c, tv] with henv3
  have dtop : Det P env3 (.var 2)
      (.list [pv, .nat Q.top.ratio, .nat Q.top.cap, .nat Q.top.origin]) (tv.wt + 1) := by
    rw [← htop]; exact Det.var' rfl
  have dcap : Det P env3 (.get (.var 2) (.nat 2)) (.nat Q.top.cap) (tv.wt + 1 + (2 + 3) +
      (Val.nat Q.top.cap).wt + 1) := Det.get' dtop (Det.nat 2) rfl
  have dori : Det P env3 (.get (.var 2) (.nat 3)) (.nat Q.top.origin) (tv.wt + 1 + (3 + 3) +
      (Val.nat Q.top.origin).wt + 1) := Det.get' dtop (Det.nat 3) rfl
  have dc : Det P env3 (.var 1) (.nat c) ((Val.nat c).wt + 1) := Det.var' rfl
  have dmin := Det.minE dcap dc
  have wcap : (Val.nat Q.top.cap).wt + (Val.nat Q.top.origin).wt ≤ tv.wt := by
    have := sum_wt_lt_wt_list [pv, .nat Q.top.ratio, .nat Q.top.cap, .nat Q.top.origin]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
    rw [htop]; omega
  set cm := min Q.top.cap c with hcm
  set lead := encFun (leadF Q E e) with hlead
  set idsk := encFun fun j : Fin k => (j : ℕ) with hidsk
  set cc := cvCtx (leadF Q E e) r c cm Q.top.origin with hcc
  obtain ⟨Cb, hCb⟩ : ∃ Cb, Cb = 20 * X + 100 + 2 * (Val.nat Q.top.cap).wt +
      2 * (Val.nat Q.top.origin).wt + 4 * (Val.nat c).wt + 4 * tv.wt := ⟨_, rfl⟩
  have dctx : Det P env3 (Expr.mkList [arg 5, arg 6, arg 4, .var 1,
      minE (.get (.var 2) (.nat 2)) (.var 1), .get (.var 2) (.nat 3), arg 7]) cc
      (7 * (Cb + cc.wt + 1) + 5) :=
    Det.mkList (P := P) (env := env3) (c := Cb)
      [(arg 5, lead), (arg 6, .nat k), (arg 4, .nat r), (.var 1, .nat c),
        (minE (.get (.var 2) (.nat 2)) (.var 1), .nat cm), (.get (.var 2) (.nat 3),
          .nat Q.top.origin), (arg 7, idsk)] (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (ha 5 _ rfl _).mono (by omega)
      · exact (ha 6 _ rfl _).mono (by omega)
      · exact (ha 4 _ rfl _).mono (by omega)
      · exact dc.mono (by omega)
      · exact dmin.mono (by omega)
      · exact dori.mono (by omega)
      · exact (ha 7 _ rfl _).mono (by omega))
  set Mv := Val.list ((List.range r).map (cvVal (leadF Q E e) r c cm Q.top.origin)) with hMv
  have cv := cvAll_spec hcv hfcv hmap hfl hfind hft (leadF Q E e) r c cm Q.top.origin
  have hMw := FunDet.wt_lt cv
  have d3 := Det.call dctx cv
  set env4 := [x, .nat c, tv, Mv] with henv4
  have dl : Det P env4 (arg 0) (.list vs) (2 * X + 0 + 5) := ha 0 _ rfl _
  have dt : Det P env4 (arg 1) (.nat t) (2 * X + 1 + 5) := ha 1 _ rfl _
  have dM : Det P env4 (.var 3) Mv (Mv.wt + 1) := Det.var' rfl
  have sp := splice_spec hspl happ vs ((List.range r).map (cvVal (leadF Q E e) r c cm
    Q.top.origin)) htl
  have how := FunDet.wt_lt sp
  have d4 := Det.call (Det.mk3 dl dt dM) sp
  refine FunAll.mono (FunDet.intro hf (Det.letE d1 (Det.letE d2 (Det.letE d3 d4)))) ?_
  rintro w cost ⟨rfl, hcost⟩
  refine ⟨?_, hcost.trans ?_⟩
  · have hMF : List.Forall₂ (IntervalValC e) ((List.range r).map (cvVal (leadF Q E e) r c cm
        Q.top.origin)) (Q.coordHier E) := by
      obtain ⟨Ms, hMs, hMF⟩ := hierValC_coord Q E e
      cases hMs
      exact hMF
    exact hierValC_splice Q e hF hMF
  · -- the cost
    have e1 : (cvCtx (leadF Q E e) r c cm Q.top.origin).wt = cc.wt := rfl
    have e1' : cvAllK * ((cvCtx (leadF Q E e) r c cm Q.top.origin).wt + r + 10) ^ 4 =
        10 ^ 8 * (cc.wt + r + 10) ^ 4 := rfl
    have e2 : (Val.list ((List.range r).map (cvVal (leadF Q E e) r c cm Q.top.origin))).wt =
        Mv.wt := rfl
    have e2' : spliceK * ((Val.list [.list vs, .nat t, .list ((List.range r).map
        (cvVal (leadF Q E e) r c cm Q.top.origin))]).wt + 1) ^ 3 =
        spliceK * ((Val.list [.list vs, .nat t, Mv]).wt + 1) ^ 3 := rfl
    have e3 : m.choose l = c := rfl
    have hk := two_pow_succ_le Q E e
    have hr2 : r + 1 < 2 ^ (r + 1) := Nat.lt_two_pow_self
    have hch := choose_le_card Q E e hr
    have wml := wt_list2_le (.nat m) (.nat l)
    have wm := wt_nat_le m
    have wl := wt_nat_le l
    have wc := wt_nat_le c
    have wk := wt_nat_le k
    have wr := wt_nat_le r
    have wcm := wt_nat_le cm
    have hcmc : cm ≤ c := min_le_right _ _
    have hpow : numK * (l + 1) * ((Val.list [.nat m, .nat l]).wt + l + m + 10) ^ 2 ≤
        10 ^ 5 * (l + 1) * (2 * (m + 2 + (l + 2)) + 6 + l + m + 10) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    have wcc : cc.wt ≤ 2 * (lead.wt + (k + 2) + (r + 2) + (Val.nat c).wt + (c + 2) +
        (Val.nat Q.top.origin).wt + idsk.wt) + 11 := by
      have := wt_list_le [lead, .nat k, .nat r, .nat c, .nat cm, .nat Q.top.origin, idsk]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.length_cons, List.length_nil] at this
      have hcc' : cc = Val.list [lead, .nat k, .nat r, .nat c, .nat cm, .nat Q.top.origin, idsk] :=
        rfl
      rw [hcc']; omega
    have hlw : lead.wt ≤ 4 * (k * k + 1) ^ 2 := wt_encFun_le_sq _ (leadF_le Q E e)
    have hiw : idsk.wt ≤ 4 * (k + 1) ^ 2 := wt_ids_le k
    have htw : tv.wt < X := by
      have h1 : tv.wt < (Val.list vs).wt := by rw [htv]; exact wt_getElem_lt vs t htl
      have h2 : (Val.list vs).wt < X := hX ▸ wt_le_wt_list (by simp [hxs])
      omega
    have hsum := sum_wt_lt_wt_list xs
    simp only [hxs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
    have w3 := wt_list3_le (.list vs) (.nat t) Mv
    have ex : (Val.list [.list vs, .nat t, .nat m, .nat l, .nat r, lead, .nat k, idsk]).wt = X := by
      rw [hX]
    have hsp : spliceK * ((Val.list [.list vs, .nat t, Mv]).wt + 1) ^ 3 ≤
        10 ^ 6 * (2 * (X + (r + 2) + Mv.wt) + 7 + 1) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
    have ecv : cvAllK * (cc.wt + r + 10) ^ 4 = 10 ^ 8 * (cc.wt + r + 10) ^ 4 := rfl
    have hk' : r + 1 ≤ k * k := hr2.le.trans hk
    rw [← hX]
    refine phier_cost (X := X) (cw := (Val.nat c).wt) (tw := tv.wt) (Mw := Mv.wt)
      (capw := (Val.nat Q.top.cap).wt) (ow' := (Val.nat Q.top.origin).wt) (lw := lead.wt)
      (iw := idsk.wt) (cc := cc.wt) (ch := c) rfl hk' hch ?_ wc ?_ htw ?_ wcap ?_ hlw hiw
      (by omega) ?_ (by omega)
    · omega
    · omega
    · omega
    · omega
    · omega

end GI.Impl
