module

public import Workspace.Degree.Enum
public import Workspace.Impl.GenProdStep

@[expose] public section

/-!
# The product step of the degree algorithm

The text of `Workspace/Impl/GenProdStep.lean`, with two changes.

* The children meet `ChildPost` in place of `Iface.Post`, as in `Degree/Enum.lean`.
* The general algorithm runs the orbit loop with the bound `r!`, and its cost is polynomial in that
  bound. Here `r!` can be far above `D^(r-1)`, so the program uses the true index `B = |G| / |K|`,
  which the order primitive computes from the coordinate group `K`.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens Membership Preimage GroupOrder)
open scoped Pointwise

/-- The index of a subgroup, from the two orders. -/
theorem card_div_card_eq_index {Ω : Type} [Finite Ω] {k : ℕ} (e : Ω ≃ Fin k)
    {K G : Subgroup (Perm Ω)} (h : K ≤ G) :
    Nat.card (groupFin e G) / Nat.card (groupFin e K) = (K.subgroupOf G).index := by
  have e1 : ∀ H : Subgroup (Perm Ω), Nat.card (groupFin e H) = Nat.card H := fun H => by
    unfold groupFin
    exact Nat.card_congr (Subgroup.equivMapOfInjective H _ (toFin e).injective).symm.toEquiv
  rw [e1, e1, ← Subgroup.card_mul_index (K.subgroupOf G),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]
  exact Nat.mul_div_cancel_left _ Nat.card_pos

/-- The bound of the orbit loop: on the first three variables of `prodE`, the index of the
coordinate group. -/
def prodIdxE (bones bpk jo : ℕ) : Expr :=
  .letE (.call bones (mk2 (.nat 0) (.get (.var 1) (.nat 2))))
  (.letE (.call bpk (mk4 (mk2 (.get (arg 0) (.nat 0)) (.get (.var 1) (.nat 3)))
      (mk2 (.arith .mul (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0))) (.var 2))
      (.get (.var 1) (.nat 0)) (.var 3)))
    (.arith .div (.prim jo (.get (arg 0) (.nat 1))) (.prim jo (.var 4))))

/-- The product step. Only the third binding differs from `prodE` of the general algorithm. -/
def prodDE (bpt bsq bco bpu bones bpk bph bt jo : ℕ) : Expr :=
  let V := arg 0
  let EX := arg 1
  let CS := arg 2
  let K := Expr.get V (.nat 0)
  let GLs := Expr.get (.get V (.nat 1)) (.nat 1)
  let T := fun i => Expr.get (.var 1) (.nat i)
  .letE (.call bpt (Expr.mkList [.get CS (.nat 4), .get EX (.nat 3), .get CS (.nat 1),
      .get CS (.nat 3), K]))
  (.letE (.call bsq (mk2 (mk2 K (T 2)) GLs))
  (.letE (prodIdxE bones bpk jo)
  (.letE (.call bco (Expr.mkList [.nat 0, .var 2, T 0, .var 3, .arith .mul K K]))
  (.letE (.call bpu (mk2 (mk2 K (T 3)) (.var 4)))
  (.letE (.call bones (mk2 (.nat 0) (T 2)))
  (.letE (.call bpk (mk4 (mk2 K (T 3)) (mk2 (.arith .mul K K) (.var 2)) (T 0) (.var 6)))
  (.letE (.call bph (Expr.mkList [.get EX (.nat 2), .get EX (.nat 4), .get CS (.nat 1),
      .get CS (.nat 2), .get CS (.nat 3), T 1, K, T 3]))
  (.call bt (mk2 (mk3 V (.var 7) (.var 8)) (.var 5))))))))))

/-- **The own cost of the product step.** `B` is the index. The extra terms pay for the coordinate
group, which is found twice, and for the two orders. -/
noncomputable def prodCostD (hO : GroupOrder) (hp : Preimage) (hm : Membership) (k W B : ℕ)
    (gv Kv : Val) : ℕ :=
  2 * prodCost hp hm k W B + (groupOrderPrim hO).bound gv + (groupOrderPrim hO).bound Kv +
    2 * W + 4 * k ^ 2 + 200

variable {Ω C : Type}

set_option maxHeartbeats 2000000 in
/-- **The orbit of the mask labeling has at most `|G : K|` points**, for the coordinate group `K`. -/
theorem ncard_orbit_mask_le_index {S : State Ω C} (Q : PrimitiveQuotient S) {m l r k : ℕ} [Finite Ω]
    (E : Fin Q.d ≃ (Fin r → Product.KSet m l)) (e : Ω ≃ Fin k) (hS : Q.ProductStructure m l r E)
    (hb : 2 ≤ m.choose l) {gs : List (Perm (Fin k))} (hG : genGroup gs = groupFin e S.G) :
    (actOrbit sqAct gs (maskF Q E e)).ncard ≤
      ((Q.coordinateGroup E hS hb).subgroupOf S.G).index := by
  classical
  set KG := Q.coordinateGroup E hS hb with hKG
  let F : S.G ⧸ KG.subgroupOf S.G → (Fin (k * k) → ℕ) := fun q =>
    sqAct (toFin e ((q.out : S.G) : Perm Ω)) (maskF Q E e)
  have hsub : actOrbit sqAct gs (maskF Q E e) ⊆ Set.range F := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hG] at ht
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 ht
    refine ⟨QuotientGroup.mk ⟨g, hg⟩, ?_⟩
    set x' : S.G := (QuotientGroup.mk ⟨g, hg⟩ : S.G ⧸ KG.subgroupOf S.G).out with hx'
    have hq : (QuotientGroup.mk x' : S.G ⧸ KG.subgroupOf S.G) = QuotientGroup.mk ⟨g, hg⟩ :=
      QuotientGroup.out_eq' _
    have hmem : x'⁻¹ * ⟨g, hg⟩ ∈ KG.subgroupOf S.G := QuotientGroup.eq.1 hq
    have hst := (sqAct_maskF_iff Q E e hS hb (x'⁻¹ * ⟨g, hg⟩ : S.G).2).2
      (Subgroup.mem_subgroupOf.1 hmem)
    have e1 : (toFin e g : Perm (Fin k)) = toFin e (x' : Perm Ω) *
        toFin e ((x'⁻¹ * ⟨g, hg⟩ : S.G) : Perm Ω) := by
      rw [← map_mul]; simp
    change sqAct (toFin e (x' : Perm Ω)) (maskF Q E e) = sqAct (toFin e g) (maskF Q E e)
    rw [e1, isAct_sq.mul, hst]
  calc (actOrbit sqAct gs (maskF Q E e)).ncard ≤ (Set.range F).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (F '' Set.univ).ncard := by rw [Set.image_univ]
    _ ≤ (Set.univ : Set (S.G ⧸ KG.subgroupOf S.G)).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = (KG.subgroupOf S.G).index := by rw [Set.ncard_univ]; rfl

set_option maxHeartbeats 16000000 in
/-- **The product step meets its specification.** On a canonical value of a transitive state, the
output of the exposure with quotient `Q` and a product structure `E` of `Q` with `r ≥ 2`, the
step returns the exact answer. -/
theorem prod_specD {Ω C : Type} (Bc : State Ω C → ℝ) (hO : GroupOrder) (hp : Preimage) (hm : Membership)
    {Pg : Program} {F : Funs} {f bpt bsq bco bpu bones bpk bph bt jo : ℕ}
    (hf : Pg.funs[f]? = some (prodDE bpt bsq bco bpu bones bpk bph bt jo))
    (hjo : Pg.prims[jo]? = some (groupOrderPrim hO))
    -- the tables
    {bprows bm fadd brep bga brange bm0 bm1 fs0 fs1 bl beq : ℕ}
    (hpt : Pg.funs[bpt]? = some (ptabsE bprows brange bm0 bm1))
    (hprows : Pg.funs[bprows]? = some (prowsE bm brep bga)) (hbm : Pg.HasAt bm (mapFuns bm fadd))
    (hfadd : Pg.funs[fadd]? = some addOneF) (hrep : Pg.HasAt brep (replicateFuns brep))
    (hga : Pg.HasAt bga (gatherFuns bga)) (hrange : Pg.HasAt brange (rangeFuns brange))
    (hm0 : Pg.HasAt bm0 (mapFuns bm0 fs0)) (hfs0 : Pg.funs[fs0]? = some (pselF bl 0))
    (hm1 : Pg.HasAt bm1 (mapFuns bm1 fs1)) (hfs1 : Pg.funs[fs1]? = some (pselF bl 1))
    (hl : Pg.HasAt bl (pbFuns bl beq)) (heq : Pg.HasAt beq (eqNatsFuns beq))
    -- the squares and back
    {fsq bsm fse fu bmt fe : ℕ}
    (hsq : Pg.HasAt bsq (mapFuns bsq fsq)) (hfsq : Pg.funs[fsq]? = some (tabWrapF bsm))
    (hbsm : Pg.HasAt bsm (mapFuns bsm fse)) (hfse : Pg.funs[fse]? = some sqEntF)
    (hfu : Pg.funs[fu]? = some (tabWrapF bmt)) (hbmt : Pg.HasAt bmt (mapFuns bmt fe))
    (hfe : Pg.funs[fe]? = some unsqEntF)
    -- `r!`, the cosets, the pairs and the ones
    (hco : Pg.HasAt bco (cosetsFuns bco))
    {fpu fone : ℕ} (hpu : Pg.HasAt bpu (mapFuns bpu fpu))
    (hfpu : Pg.funs[fpu]? = some (pairUnsqF fu))
    (hones : Pg.HasAt bones (mapFuns bones fone)) (hfone : Pg.funs[fone]? = some oneF)
    -- the coordinate group
    {bcls bker jpre jm bmu bred : ℕ}
    (hpk : Pg.funs[bpk]? = some (pkerE bcls bker bmu bred)) (hcls : Pg.HasAt bcls (clsFuns bcls))
    (hker : Pg.HasAt bker (kerNFFuns bker jpre jm))
    (hjp : Pg.prims[jpre]? = some (preimagePrim hp))
    (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    (hmu : Pg.HasAt bmu (mapFuns bmu fu)) (hred : Pg.HasAt bred (reduceFuns bred jm))
    -- the hierarchy
    {bch bcv bspl bapp fcv bmap fl bfind ft : ℕ}
    (hph : Pg.funs[bph]? = some (phierE bch bcv bspl)) (hch : Pg.HasAt bch (chooseFuns bch))
    (hcv : Pg.HasAt bcv (cvAllFuns bcv fcv)) (hfcv : Pg.funs[fcv]? = some (cvF bmap))
    (hmap : Pg.HasAt bmap (mapFuns bmap fl)) (hfcl : Pg.funs[fl]? = some (cvLabF bfind))
    (hfind : Pg.HasAt bfind (findFuns bfind ft)) (hft : Pg.funs[ft]? = some cvTestF)
    (hspl : Pg.HasAt bspl (spliceFuns bspl bapp)) (happ : Pg.HasAt bapp (appendFuns bapp))
    -- the tail
    {btm fch bg bc g comp inv bn : ℕ}
    (hbt : Pg.funs[bt]? = some (tailF btm bc bn))
    (hbtm : Pg.HasAt btm (mapFuns btm fch)) (hfch : Pg.funs[fch]? = some (enumChildF F bg))
    (hbg : Pg.HasAt bg (gatherFuns bg))
    (hbc : Pg.HasAt bc (foldlFuns bc g)) (hg : Pg.funs[g]? = some (combStep comp inv bapp))
    (hcomp : Pg.HasAt comp (composeFuns comp)) (hinv : Pg.HasAt inv (invFuns inv))
    (hbn : Pg.HasAt bn (cosetNFFuns bn jm))
    -- the state, the quotient and the product structure
    {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {gv dv xv yv hv rv fv hh : Val} {N : ℕ}
    {S : State Ω C}
    (hcan : Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S)
    (Q : PrimitiveQuotient S) {m l r : ℕ} (E : Fin Q.d ≃ (Fin r → Product.KSet m l))
    (hS : Q.ProductStructure m l r E) (hr : 2 ≤ r)
    (hkeep : CarrierOK (Q.coordinateGroup E hS (Q.two_le_choose E)) S.dom S.rows
      (Q.pre ++ Q.coordHier E ++ Q.post))
    {gv' rep hv' : Val} (hH : HierValC e hv' (Q.pre ++ Q.top :: Q.post))
    (hcall : ∀ (I : DispatchStep P₀ S), I.kind = .product r →
      I.K = Q.coordinateGroup E hS (Q.two_le_choose E) →
      I.hier' = Q.pre ++ Q.coordHier E ++ Q.post → ∀ (t : Perm (Fin k)) (val : Val),
      Canon e c val (tailChild S I.toData e t) →
      FunAll Pg F.cont val (ChildPost Bc (tailChild S I.toData e t) e)) :
    FunAll Pg f (.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N],
        .list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length],
        .list [.nat 1, .nat m, .nat l, .nat r, GI.Cited.encKSetTuples E]])
      (fun u cost => AnsC e u S.answer ∧ ∃ (I : DispatchStep P₀ S) (Kv : Val) (L : List (Perm (Fin k))),
        I.kind = .product r ∧ I.K = Q.coordinateGroup E hS (Q.two_le_choose E) ∧
        I.hier' = Q.pre ++ Q.coordHier E ++ Q.post ∧
        I.n = ((Q.coordinateGroup E hS (Q.two_le_choose E)).subgroupOf S.G).index ∧
        GroupValC k Kv (groupFin e I.K) ∧ L.length ≤ I.n ∧
        (cost : ℝ) ≤ prodCostD hO hp hm k (Val.list
          [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N],
          .list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length],
          .list [.nat 1, .nat m, .nat l, .nat r, GI.Cited.encKSetTuples E]]).wt I.n gv Kv +
          (L.map fun t => Bc (tailChild S I.toData e t)).sum) := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  obtain ⟨gv0, dv0, xv0, yv0, hv0, rv0, hgv, -, -, -, -, -, heqv⟩ := hcan.val
  simp only [Val.list.injEq, List.cons.injEq] at heqv
  obtain ⟨-, rfl, -, -, -, -, -, -, -, -, -⟩ := heqv
  obtain ⟨gs, rfl, hgens, hgl⟩ := hgv
  have hb := Q.two_le_choose E
  have hr1 : 1 ≤ r := by omega
  obtain ⟨hlm, hmk⟩ := ml_le_card Q E e hr1
  have hp2 := two_pow_succ_le Q E e
  have hrp : r + 1 < 2 ^ (r + 1) := Nat.lt_two_pow_self
  have hkk : k ≤ k * k := Nat.le_mul_self k
  have hG : genGroup (1 :: gs) = groupFin e S.G := by rw [genGroup_one_cons, hgens]
  set v := Val.list [.nat k, encGroup gs, dv, xv, yv, hv, rv, fv, hh, .nat N] with hvdef
  set ex := Val.list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length] with hexdef
  set cs := Val.list [.nat 1, .nat m, .nat l, .nat r, GI.Cited.encKSetTuples E] with hcsdef
  set a := Val.list [v, ex, cs] with ha
  obtain ⟨W, hW⟩ : ∃ W, W = a.wt := ⟨_, rfl⟩
  rw [← hW]
  set KG := Q.coordinateGroup E hS hb with hKG
  have hKle : KG ≤ S.G := Subgroup.map_subtype_le _
  set B := (KG.subgroupOf S.G).index with hB
  obtain ⟨Y, hY⟩ : ∃ Y, Y = prodY k W B := ⟨_, rfl⟩
  have hBpos : 1 ≤ B := Nat.one_le_iff_ne_zero.2 Subgroup.index_ne_zero_of_finite
  have hrB : r ≤ k * k := by omega
  -- the weights of the parts of the input
  have wa := sum_wt_lt_wt_list [v, ex, cs]
  have wv := sum_wt_lt_wt_list [Val.nat k, encGroup gs, dv, xv, yv, hv, rv, fv, hh, .nat N]
  have wx := sum_wt_lt_wt_list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length]
  have wz := sum_wt_lt_wt_list [Val.nat 1, .nat m, .nat l, .nat r, GI.Cited.encKSetTuples E]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at wa wv wx wz
  have ea : (Val.list [v, ex, cs]).wt = W := by rw [hW]
  have ev : (Val.list [Val.nat k, encGroup gs, dv, xv, yv, hv, rv, fv, hh, .nat N]).wt = v.wt :=
    rfl
  have ex' : (Val.list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length]).wt = ex.wt := rfl
  have ez : (Val.list [Val.nat 1, .nat m, .nat l, .nat r, GI.Cited.encKSetTuples E]).wt =
    cs.wt := rfl
  have eg : (encGroup gs).wt = (Val.list [.nat k, .list ((1 :: gs).map encPerm)]).wt := rfl
  have wgl : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
    wt_le_wt_list (vs := [.nat k, .list ((1 :: gs).map encPerm)]) (by simp)
  have hYW : W + 1 ≤ Y := by rw [hY, prodY]; omega
  have hYk : k * k + 1 ≤ Y := by rw [hY, prodY]; omega
  have hYB : B + 1 ≤ Y := by rw [hY, prodY]; omega
  have hY1 : 1 ≤ Y := by omega
  have wnk := wt_nat_le k
  have wnm := wt_nat_le m
  have wnl := wt_nat_le l
  have wnr := wt_nat_le r
  -- the arguments
  have hA : ∀ (j : ℕ) (w : Val), [v, ex, cs][j]? = some w → ∀ rest : List Val,
      Det Pg (a :: rest) (arg j) w (2 * W + j + 5) := fun j w hj rest => by
    rw [hW]; exact Det.arg' hj
  have hV : ∀ (j : ℕ) (w : Val), [Val.nat k, encGroup gs, dv, xv, yv, hv, rv, fv, hh,
      .nat N][j]? = some w → ∀ rest : List Val, j < 10 →
      Det Pg (a :: rest) (.get (arg 0) (.nat j)) w (4 * W + 20) := fun j w hj rest hj10 => by
    have hw : w.wt < v.wt := by
      obtain ⟨h1, rfl⟩ := List.getElem?_eq_some_iff.mp hj
      exact wt_getElem_lt _ _ h1
    exact (Det.get' (hA 0 v rfl rest) (Det.nat j) hj).mono (by omega)
  have hEX : ∀ (j : ℕ) (w : Val), [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length][j]? =
      some w → ∀ rest : List Val, j < 5 → Det Pg (a :: rest) (.get (arg 1) (.nat j)) w
      (4 * W + 20) := fun j w hj rest hj5 => by
    have hw : w.wt < ex.wt := by
      obtain ⟨h1, rfl⟩ := List.getElem?_eq_some_iff.mp hj
      exact wt_getElem_lt _ _ h1
    exact (Det.get' (hA 1 ex rfl rest) (Det.nat j) hj).mono (by omega)
  have hCS : ∀ (j : ℕ) (w : Val), [Val.nat 1, .nat m, .nat l, .nat r,
      GI.Cited.encKSetTuples E][j]? = some w → ∀ rest : List Val, j < 5 →
      Det Pg (a :: rest) (.get (arg 2) (.nat j)) w (4 * W + 20) := fun j w hj rest hj5 => by
    have hw : w.wt < cs.wt := by
      obtain ⟨h1, rfl⟩ := List.getElem?_eq_some_iff.mp hj
      exact wt_getElem_lt _ _ h1
    exact (Det.get' (hA 2 cs rfl rest) (Det.nat j) hj).mono (by omega)
  have dK : ∀ rest : List Val, Det Pg (a :: rest) (.get (arg 0) (.nat 0)) (.nat k) (4 * W + 20) :=
    fun rest => hV 0 _ rfl rest (by norm_num)
  have dKK : ∀ rest : List Val, Det Pg (a :: rest)
      (.arith .mul (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0))) (.nat (k * k))
      (8 * W + 43 + k * k) := fun rest =>
    (Det.arith' (z := k * k) (dK rest) (dK rest) rfl).mono (by omega)
  have dGL : ∀ rest : List Val, Det Pg (a :: rest) (.get (.get (arg 0) (.nat 1)) (.nat 1))
      (.list ((1 :: gs).map encPerm)) (6 * W + 30) := fun rest =>
    (Det.get' (hV 1 _ rfl rest (by norm_num)) (Det.nat 1)
      (show [Val.nat k, Val.list ((1 :: gs).map encPerm)][1]? =
        some (.list ((1 :: gs).map encPerm)) from rfl)).mono (by omega)
  -- powers of `Y`
  have hpY : ∀ d, d ≤ 48 → Y ^ d ≤ Y ^ 48 := fun d hd => Nat.pow_le_pow_right hY1 hd
  have p1 : Y ≤ Y ^ 48 := by simpa using hpY 1 (by norm_num)
  have p2 := hpY 2 (by norm_num)
  have p3 := hpY 3 (by norm_num)
  have pY2 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have pY3 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hk2 : (k + 1) ^ 2 ≤ (k * k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hY2 : (k * k + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hYk 2
  have hkY6 : (k + 1) ^ 6 ≤ Y ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hkk2 : k ^ 2 = k * k := sq k
  -- step 1: the tables
  have wmask : (encFun (maskF Q E e)).wt ≤ 4 * (k * k + 1) ^ 2 :=
    wt_encFun_le_sq _ (maskF_le Q E e)
  have wlead : (encFun (leadF Q E e)).wt ≤ 4 * (k * k + 1) ^ 2 :=
    wt_encFun_le_sq _ (leadF_le Q E e)
  have wids2 : (encFun fun j : Fin (k * k) => (j : ℕ)).wt ≤ 4 * (k * k + 1) ^ 2 := wt_ids_le _
  have widsk : (encFun fun j : Fin k => (j : ℕ)).wt ≤ 4 * (k + 1) ^ 2 := wt_ids_le _
  have wT1 : (Val.list [encFun (maskF Q E e), encFun (leadF Q E e),
      encFun fun j : Fin (k * k) => (j : ℕ), encFun fun j : Fin k => (j : ℕ)]).wt ≤ 40 * Y ^ 2 := by
    have := wt_list4_le (encFun (maskF Q E e)) (encFun (leadF Q E e))
      (encFun fun j : Fin (k * k) => (j : ℕ)) (encFun fun j : Fin k => (j : ℕ))
    omega
  have wX1 : (Val.list [GI.Cited.encKSetTuples E, encFun (Q.labFin e), .nat m, .nat r,
      .nat k]).wt ≤ 10 * W + 10 := by
    have := wt_list_le [GI.Cited.encKSetTuples E, encFun (Q.labFin e), .nat m, .nat r, .nat k]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    omega
  have d1 : Det Pg [a] (.call bpt (Expr.mkList [.get (arg 2) (.nat 4), .get (arg 1) (.nat 3),
      .get (arg 2) (.nat 1), .get (arg 2) (.nat 3), .get (arg 0) (.nat 0)]))
      (.list [encFun (maskF Q E e), encFun (leadF Q E e), encFun fun j : Fin (k * k) => (j : ℕ),
        encFun fun j : Fin k => (j : ℕ)]) (10 ^ 102 * Y ^ 48) := by
    have hml := Det.mkList (P := Pg) (env := [a]) (c := 4 * W + 20)
      [(.get (arg 2) (.nat 4), GI.Cited.encKSetTuples E), (.get (arg 1) (.nat 3),
        encFun (Q.labFin e)), (.get (arg 2) (.nat 1), .nat m), (.get (arg 2) (.nat 3), .nat r),
        (.get (arg 0) (.nat 0), .nat k)] (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl
        · exact hCS 4 _ rfl [] (by norm_num)
        · exact hEX 3 _ rfl [] (by norm_num)
        · exact hCS 1 _ rfl [] (by norm_num)
        · exact hCS 3 _ rfl [] (by norm_num)
        · exact dK [])
    refine (Det.call hml (ptabs_spec hpt hprows hbm hfadd hrep hga hrange hm0 hfs0 hm1 hfs1 hl
      heq Q E e)).mono ?_
    simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil]
    have hx : (Val.list [GI.Cited.encKSetTuples E, encFun (Q.labFin e), .nat m, .nat r,
        .nat k]).wt + k * k + 1 ≤ 12 * Y := by omega
    have hpw := Nat.mul_le_mul_left ptabsK (cpow_le 24 hx (by norm_num) hY1)
    unfold ptabsK at hpw ⊢
    norm_num at hpw
    omega
  -- the tables in the environment
  set T1v := Val.list [encFun (maskF Q E e), encFun (leadF Q E e),
    encFun fun j : Fin (k * k) => (j : ℕ), encFun fun j : Fin k => (j : ℕ)] with hT1v
  have dT : ∀ (i : ℕ) (w : Val) (rest : List Val), [encFun (maskF Q E e), encFun (leadF Q E e),
      encFun fun j : Fin (k * k) => (j : ℕ), encFun fun j : Fin k => (j : ℕ)][i]? = some w →
      i < 4 → Det Pg (a :: T1v :: rest) (.get (.var 1) (.nat i)) w (100 * Y ^ 2) :=
    fun i w rest hi hi4 => by
      have hw : w.wt < T1v.wt := by
        obtain ⟨h1, rfl⟩ := List.getElem?_eq_some_iff.mp hi
        exact wt_getElem_lt _ _ h1
      have eT : (Val.list [encFun (maskF Q E e), encFun (leadF Q E e),
        encFun fun j : Fin (k * k) => (j : ℕ), encFun fun j : Fin k => (j : ℕ)]).wt = T1v.wt := rfl
      exact (Det.get' (Det.var' (P := Pg) (env := a :: T1v :: rest) (i := 1) rfl) (Det.nat i)
        hi).mono (by omega)
  -- step 2: the squares of the generators
  have hsq1 : (1 :: gs).map sqPerm = 1 :: gs.map sqPerm := by simp [sqPerm_one]
  have wSQ : (Val.list ((1 :: gs.map sqPerm).map encPerm)).wt ≤ 13 * Y ^ 3 := by
    have h1 := wt_list_le_of ((1 :: gs.map sqPerm).map encPerm) (c := 4 * (k * k + 1) ^ 2) (by
      intro w hw; obtain ⟨g, -, rfl⟩ := List.mem_map.1 hw; exact wt_encPerm_le g)
    simp only [List.length_map, List.length_cons] at h1
    have h2 := Nat.mul_le_mul (show gs.length + 1 ≤ Y by omega)
      (show 2 * (4 * (k * k + 1) ^ 2) + 1 ≤ 9 * Y ^ 2 by omega)
    have e2 : Y * (9 * Y ^ 2) = 9 * Y ^ 3 := by ring
    omega
  have d2 : Det Pg [a, T1v] (.call bsq (mk2 (mk2 (.get (arg 0) (.nat 0)) (.get (.var 1) (.nat 2)))
      (.get (.get (arg 0) (.nat 1)) (.nat 1)))) (.list ((1 :: gs.map sqPerm).map encPerm))
      (10 ^ 12 * Y ^ 48) := by
    have hc := mapConv_spec hsq sqPerm (1 :: gs) (fun g _ => sqPerm_spec hfsq hbsm hfse g)
    rw [hsq1] at hc
    refine (Det.call (Det.mk2 (Det.mk2 (dK _) (dT 2 _ _ rfl (by norm_num))) (dGL _)) hc).mono ?_
    simp only [List.length_cons]
    have w1 := wt_list2_le (.nat k) (encFun fun j : Fin (k * k) => (j : ℕ))
    have w2 := wt_list2_le (.list [.nat k, encFun fun j : Fin (k * k) => (j : ℕ)])
      (.list ((1 :: gs).map encPerm))
    have q1 := Nat.mul_le_mul (show gs.length + 1 ≤ Y by omega)
      (Nat.mul_le_mul_left sqConvK hkY6)
    have q2 := Nat.mul_le_mul (Nat.mul_le_mul_left mapK (show gs.length + 1 + 1 ≤ 2 * Y by omega))
      (show (Val.list [.list [.nat k, encFun fun j : Fin (k * k) => (j : ℕ)],
        .list ((1 :: gs).map encPerm)]).wt + (Val.list ((1 :: gs.map sqPerm).map encPerm)).wt + 1
        ≤ 100 * Y ^ 3 by omega)
    have e1 : Y * (sqConvK * Y ^ 6) = 10 ^ 8 * Y ^ 7 := by simp only [sqConvK]; ring
    have e2 : mapK * (2 * Y) * (100 * Y ^ 3) = 200000 * Y ^ 4 := by simp only [mapK]; ring
    have p4 := hpY 4 (by norm_num)
    have p7 := hpY 7 (by norm_num)
    omega
  have hBo : (actOrbit labAct (1 :: gs.map sqPerm) (maskF Q E e)).ncard ≤ B := by
    rw [← hsq1, actOrbit_sq]; exact ncard_orbit_mask_le_index Q E e hS hb hG
  set SQv := Val.list ((1 :: gs.map sqPerm).map encPerm) with hSQv
  -- step 6: the table of ones
  have wones : (encFun fun _ : Fin (k * k) => 1).wt ≤ 4 * (k * k + 1) ^ 2 :=
    wt_encFun_le_sq _ fun x => by have := x.isLt; omega
  have d6 : ∀ rest, Det Pg (a :: T1v :: rest)
      (.call bones (mk2 (.nat 0) (.get (.var 1) (.nat 2)))) (encFun fun _ : Fin (k * k) => 1)
      (10 ^ 7 * Y ^ 48) := fun rest => by
    refine (Det.call (Det.mk2 (Det.nat 0) (dT 2 _ _ rfl (by norm_num)))
      (ones_det hones hfone (k * k))).mono ?_
    have w1 := wt_list2_le (.nat 0) (encFun fun j : Fin (k * k) => (j : ℕ))
    have w0 : (Val.nat 0).wt ≤ 0 + 2 := wt_nat_le 0
    have h3 : (k * k + 1) ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left hYk 3
    omega
  -- step 7: the coordinate group
  set ONES := encFun fun _ : Fin (k * k) => (1 : ℕ) with hONES
  have hhs : gens (gs.map sqPerm) = (groupFin e S.G).map sqHom := by rw [gens_map_sq, hgens]
  have wEG : (encGroup (gs.map sqPerm)).wt ≤ 320 * (k * k + 1) ^ 6 := by
    refine wt_encGroup_le_sq ?_
    have : k * k ≤ (k * k) ^ 2 := Nat.le_self_pow (by norm_num) _
    simp only [List.length_map]; omega
  have eEG : (encGroup (gs.map sqPerm)).wt = (Val.list [.nat (k * k), SQv]).wt := rfl
  have hk6 : (k * k + 1) ^ 2 ≤ (k * k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hY6 : (k * k + 1) ^ 6 ≤ Y ^ 6 := Nat.pow_le_pow_left hYk 6
  have p6 := hpY 6 (by norm_num)
  have d7 : ∀ (rest : List Val) (j : ℕ), (a :: T1v :: SQv :: rest)[j]? = some ONES →
      EvalAll Pg (a :: T1v :: SQv :: rest)
      (.call bpk (mk4 (mk2 (.get (arg 0) (.nat 0)) (.get (.var 1) (.nat 3)))
        (mk2 (.arith .mul (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0))) (.var 2))
        (.get (.var 1) (.nat 0)) (.var j)))
      (fun w cw => GroupValC k w (groupFin e (Q.coordinateGroup E hS hb)) ∧
        cw ≤ 2 * ONES.wt + pkerCost hp hm k (pkerW k) + 10 ^ 7 * Y ^ 48 + w.wt) := fun rest j hj => by
    set env7 := a :: T1v :: SQv :: rest with henv7
    have dargs := Det.mk4 (Det.mk2 (dK env7.tail) (dT 3 _ env7.tail.tail rfl (by norm_num)))
      (Det.mk2 (dKK env7.tail) (Det.var' (P := Pg) (env := env7) (i := 2) (v := SQv) rfl))
      (dT 0 _ env7.tail.tail rfl (by norm_num))
      (Det.var' (P := Pg) (env := env7) (i := j) (v := ONES) hj)
    refine EvalAll.call_funAll dargs fun v0 ca h0 => ?_
    obtain ⟨rfl, hca⟩ := h0
    refine (pker_spec hp hm hpk hcls hker hjp hjm hmu hfu hbmt hfe hred Q E e hS hb
      (maskF_le Q E e) hhs).mono fun w cost hw => ⟨hw.1, ?_⟩
    have wones' : (encFun fun _ : Fin (k * k) => (1 : ℕ)).wt ≤ 4 * (k * k + 1) ^ 2 :=
      wt_encFun_le_sq _ fun x => by have := x.isLt; omega
    have eON : ONES.wt = (encFun fun _ : Fin (k * k) => (1 : ℕ)).wt := rfl
    have hin : (Val.list [cK k, encGroup (gs.map sqPerm), encFun (maskF Q E e),
        encFun fun _ : Fin (k * k) => (1 : ℕ)]).wt ≤ pkerW k := by
      calc _ ≤ 2 * ((cK k).wt + (encGroup (gs.map sqPerm)).wt + (encFun (maskF Q E e)).wt +
            (encFun fun _ : Fin (k * k) => (1 : ℕ)).wt) + 8 := wt_list4_le _ _ _ _
        _ ≤ 2 * (20 * (k + 1) ^ 2 + 320 * (k * k + 1) ^ 6 + 4 * (k * k + 1) ^ 2 +
            4 * (k * k + 1) ^ 2) + 8 := by
          have a1 : (cK k).wt ≤ 20 * (k + 1) ^ 2 := wt_cK_le k
          gcongr
        _ ≤ pkerW k := by
          have a3 : (k + 1) ^ 2 ≤ (k * k + 1) ^ 6 := hk2.trans hk6
          have a4 : 1 ≤ (k * k + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
          clear * - a3 a4 hk6
          unfold pkerW; omega
    have hpc := pkerCost_mono hp hm k hin
    have h2 := hw.2
    have w1 := wt_list2_le (.nat k) (encFun fun j : Fin k => (j : ℕ))
    have w2 := wt_list2_le (.nat (k * k)) SQv
    have wkk : (Val.nat (k * k)).wt ≤ k * k + 2 := wt_nat_le _
    have e1 : (Val.list [Val.list [.nat k, encFun fun j : Fin k => (j : ℕ)],
        Val.list [.nat (k * k), SQv], encFun (maskF Q E e), ONES]).wt =
        (Val.list [cK k, encGroup (gs.map sqPerm), encFun (maskF Q E e),
          encFun fun _ : Fin (k * k) => (1 : ℕ)]).wt := rfl
    have hpk' : pkerW k ≤ 1000 * Y ^ 6 := by unfold pkerW; omega
    omega
  -- step 3: the index
  have dKo : ∀ rest, Det Pg (a :: rest) (.get (arg 0) (.nat 1)) (encGroup gs) (4 * W + 20) :=
    fun rest => hV 1 _ rfl rest (by norm_num)
  have d3 : EvalAll Pg [a, T1v, SQv] (prodIdxE bones bpk jo) (fun w cw => w = .nat B ∧
      ∃ Kv : Val, GroupValC k Kv (groupFin e KG) ∧ cw ≤ prodCost hp hm k W B + 2 * Y ^ 48 * 10 ^ 7 +
        (groupOrderPrim hO).bound (encGroup gs) + (groupOrderPrim hO).bound Kv + 4 * k ^ 2) := by
    unfold prodIdxE
    refine EvalAll.letE (d6 [SQv]) ?_
    rintro _ c6' ⟨rfl, hc6'⟩
    refine EvalAll.letE (d7 [ONES] 3 rfl) fun Kv c7' h7' => ?_
    obtain ⟨hKv', hc7'⟩ := h7'
    have o1 := groupOrder_call hO hjo (dKo [T1v, SQv, ONES, Kv]) (G := groupFin e S.G)
      ⟨gs, rfl, hgens⟩
    have o2 := groupOrder_call hO hjo (Det.var' (P := Pg) (env := [a, T1v, SQv, ONES, Kv]) (i := 4)
      (v := Kv) rfl) hKv'.groupVal
    have o3 := Det.arith (op := .div) o1 o2
    have hdiv : GI.Machine.BinOp.eval .div (Nat.card (groupFin e S.G)) (Nat.card (groupFin e KG)) = B :=
      card_div_card_eq_index e hKle
    rw [hdiv] at o3
    refine EvalAll.mono o3 ?_
    rintro w cw ⟨rfl, hcw⟩
    refine ⟨rfl, Kv, hKv', ?_⟩
    have wKv : Kv.wt ≤ groupW k := hKv'.wt_le
    have hgW : groupW k ≤ 160 * Y ^ 4 := by
      have h1 : k ^ 2 + 2 ≤ 2 * Y := by omega
      have h2 : (k ^ 2 + 2) * (k + 1) ≤ 2 * Y * Y := Nat.mul_le_mul h1 (by omega)
      have h3 := Nat.pow_le_pow_left h2 2
      have e3 : (2 * Y * Y) ^ 2 = 4 * Y ^ 4 := by ring
      unfold groupW; omega
    have wNB : (Val.nat B).wt ≤ B + 2 := wt_nat_le _
    have p4 := hpY 4 (by norm_num)
    have wON : ONES.wt ≤ 4 * (k * k + 1) ^ 2 := wones
    unfold prodCost
    rw [← hY]
    omega
  -- step 4: the cosets on the squares
  have d4 : EvalAll Pg [a, T1v, SQv, .nat B] (.call bco (Expr.mkList [.nat 0, .var 2,
      .get (.var 1) (.nat 0), .var 3, .arith .mul (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0))]))
      (fun w cw => ∃ L : List ((Fin (k * k) → ℕ) × Perm (Fin (k * k))), w = encPairs labKey L ∧
        (L.map Prod.fst).Nodup ∧
        (∀ y, y ∈ L.map Prod.fst ↔ y ∈ actOrbit labAct (1 :: gs.map sqPerm) (maskF Q E e)) ∧
        (∀ p ∈ L, p.2 ∈ genGroup (1 :: gs.map sqPerm) ∧ labAct p.2 (maskF Q E e) = p.1) ∧
        cw ≤ 10 ^ 19 * Y ^ 48 + w.wt) := by
    have wB : (Val.nat B).wt ≤ B + 2 := wt_nat_le _
    have wkk : (Val.nat (k * k)).wt ≤ k * k + 2 := wt_nat_le _
    have w0 : (Val.nat 0).wt ≤ 0 + 2 := wt_nat_le _
    have hml := Det.mkList (P := Pg) (env := [a, T1v, SQv, .nat B]) (c := 100 * Y ^ 3)
      [(.nat 0, .nat 0), (.var 2, SQv), (.get (.var 1) (.nat 0), encFun (maskF Q E e)),
        (.var 3, .nat B), (.arith .mul (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0)),
          .nat (k * k))] (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl
        · exact (Det.nat 0).mono (by omega)
        · exact (Det.var' (P := Pg) (env := [a, T1v, SQv, .nat B]) (i := 2) (v := SQv) rfl).mono
            (by omega)
        · exact (dT 0 _ _ rfl (by norm_num)).mono (by omega)
        · exact (Det.var' (P := Pg) (env := [a, T1v, SQv, .nat B]) (i := 3) (v := .nat B)
            rfl).mono (by omega)
        · exact (dKK _).mono (by omega))
    have wl5 := wt_list_le [.nat 0, SQv, encFun (maskF Q E e), .nat B, .nat (k * k)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at wl5 hml
    refine EvalAll.call_funAll hml fun v0 ca h0 => ?_
    obtain ⟨rfl, hca⟩ := h0
    refine (cosets_spec hco (1 :: gs.map sqPerm) (maskF Q E e) (maskF_le Q E e) hBo).mono
      fun w cost hw => ?_
    obtain ⟨L, h1, h2, h3, h4, h5⟩ := hw
    refine ⟨L, h1, h2, h3, h4, ?_⟩
    simp only [List.length_cons, List.length_map] at h5
    have hx : gs.length + 1 + B + 4 * (k * k + 1) ^ 2 + 20 ≤ 30 * Y ^ 2 := by omega
    have hpw := Nat.mul_le_mul_left cosetsK (Nat.pow_le_pow_left hx 6)
    have e6 : (30 * Y ^ 2) ^ 6 = 729000000 * Y ^ 12 := by ring
    rw [e6] at hpw
    have p12 := hpY 12 (by norm_num)
    simp only [cosetsK] at hpw h5
    omega
  refine FunAll.intro hf (EvalAll.letE d1 fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  refine EvalAll.letE d2 fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  refine EvalAll.letE d3 fun v3 c3 h3 => ?_
  obtain ⟨rfl, Kv0, hKv0, hc3⟩ := h3
  refine EvalAll.letE d4 fun v4 c4 h4 => ?_
  obtain ⟨L, rfl, hnd, horb, hpL, hc4⟩ := h4
  -- step 5: the pairs moved back to the points
  have hLB : L.length ≤ B := by rw [length_eq_ncard hnd horb]; exact hBo
  have hGsq : genGroup (1 :: gs.map sqPerm) = (groupFin e S.G).map sqHom := by
    rw [← hsq1, genGroup_map_sq, hG]
  have hsqp : ∀ p ∈ L, sqPerm (unsq p.2) = p.2 := fun p hp =>
    (mem_map_sq (hGsq ▸ (hpL p hp).1)).2
  have wkey : ∀ p ∈ L, (natList (labKey p.1)).wt ≤ 4 * (k * k + 1) ^ 2 := fun p hp => by
    rw [natList_labKey, ← (hpL p hp).2]
    exact wt_encFun_le_sq _ fun i => maskF_le Q E e _
  have wpair : ∀ p ∈ L, (Val.list [natList (labKey p.1), encPerm p.2]).wt ≤ 22 * Y ^ 2 :=
    fun p hp => by
      have h1 := wt_list2_le (natList (labKey p.1)) (encPerm p.2)
      have h2 : (encPerm p.2).wt ≤ 4 * (k * k + 1) ^ 2 := wt_encPerm_le _
      have h3 := wkey p hp
      omega
  have wpair' : ∀ p ∈ L, (Val.list [natList (labKey p.1), encPerm (unsq p.2)]).wt ≤
      22 * Y ^ 2 := fun p hp => by
    have h1 := wt_list2_le (natList (labKey p.1)) (encPerm (unsq p.2))
    have h2 : (encPerm (unsq p.2)).wt ≤ 4 * (k + 1) ^ 2 := wt_encPerm_le _
    have h3 := wkey p hp
    omega
  have hLY : L.length * (2 * (22 * Y ^ 2) + 1) ≤ 45 * Y ^ 3 := by
    have h2 := Nat.mul_le_mul (show L.length ≤ Y by omega) (le_refl (2 * (22 * Y ^ 2) + 1))
    have e2 : Y * (2 * (22 * Y ^ 2) + 1) = 44 * Y ^ 3 + Y := by ring
    omega
  have wPL : (Val.list (L.map (encPair labKey))).wt ≤ 45 * Y ^ 3 + 4 := by
    have h1 := wt_list_le_of (L.map (encPair labKey)) (c := 22 * Y ^ 2) (by
      intro w hw; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw; exact wpair p hp)
    rw [List.length_map] at h1
    omega
  set XS := L.map fun p => Val.list [natList (labKey p.1), encPerm (unsq p.2)] with hXS
  have wXS : (Val.list XS).wt ≤ 45 * Y ^ 3 + 4 := by
    have h1 := wt_list_le_of XS (c := 22 * Y ^ 2) (by
      intro w hw; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw; exact wpair' p hp)
    have hl : XS.length = L.length := by rw [hXS, List.length_map]
    rw [hl] at h1
    omega
  have wcK : (cK k).wt ≤ 20 * (k + 1) ^ 2 := wt_cK_le k
  have ePL : (encPairs labKey L).wt = (Val.list (L.map (encPair labKey))).wt := rfl
  have ecK : (Val.list [.nat k, encFun fun j : Fin k => (j : ℕ)]).wt = (cK k).wt := rfl
  have d5 : Det Pg [a, T1v, SQv, .nat B, encPairs labKey L]
      (.call bpu (mk2 (mk2 (.get (arg 0) (.nat 0)) (.get (.var 1) (.nat 3))) (.var 4)))
      (.list XS) (10 ^ 11 * Y ^ 48) := by
    have hmap := map_img_det hpu (c := cK k) L (encPair labKey)
      (fun p => .list [natList (labKey p.1), encPerm (unsq p.2)]) (fun p _ q _ h => by
        simp only [encPair, Val.list.injEq, List.cons.injEq] at h ⊢
        obtain ⟨h1, h2, -⟩ := h
        rw [h1, encPerm_injective h2]; simp) (B := 10 ^ 9 * Y ^ 6) (fun p hp => by
        have h := pairUnsq_spec hfpu hfu hbmt hfe (natList (labKey p.1)) (unsq p.2)
        rw [hsqp p hp] at h
        refine h.mono ?_
        have h1 := wt_list2_le (cK k) (.list [natList (labKey p.1), encPerm p.2])
        have h2 := wpair p hp
        have h6 : sqConvK * (k + 1) ^ 6 ≤ 10 ^ 8 * Y ^ 6 := Nat.mul_le_mul_left _ hkY6
        have p26 : Y ^ 2 ≤ Y ^ 6 := Nat.pow_le_pow_right hY1 (by norm_num)
        simp only [sqConvK] at h6 ⊢
        omega)
    refine (Det.call (Det.mk2 (Det.mk2 (dK _) (dT 3 _ _ rfl (by norm_num)))
      (Det.var' (P := Pg) (env := [a, T1v, SQv, .nat B, encPairs labKey L]) (i := 4)
        (v := encPairs labKey L) rfl)) hmap).mono ?_
    have w1 := wt_list2_le (.nat k) (encFun fun j : Fin k => (j : ℕ))
    have w2 := wt_list2_le (cK k) (.list (L.map (encPair labKey)))
    have e2 : (Val.list [Val.list [.nat k, encFun fun j : Fin k => (j : ℕ)],
        encPairs labKey L]).wt = (Val.list [cK k, .list (L.map (encPair labKey))]).wt := rfl
    have e3 : (Val.list (List.map (fun p => Val.list [natList (labKey p.1),
        encPerm (unsq p.2)]) L)).wt = (Val.list XS).wt := rfl
    have q1 := Nat.mul_le_mul (show L.length ≤ Y by omega) (le_refl (10 ^ 9 * Y ^ 6))
    have q2 := Nat.mul_le_mul (Nat.mul_le_mul_left mapK (show L.length + 1 ≤ 2 * Y by omega))
      (show (Val.list [cK k, .list (L.map (encPair labKey))]).wt + (Val.list (L.map fun p =>
        Val.list [natList (labKey p.1), encPerm (unsq p.2)])).wt + 1 ≤ 200 * Y ^ 3 by omega)
    have e4 : Y * (10 ^ 9 * Y ^ 6) = 10 ^ 9 * Y ^ 7 := by ring
    have e5 : mapK * (2 * Y) * (200 * Y ^ 3) = 400000 * Y ^ 4 := by simp only [mapK]; ring
    have p4 := hpY 4 (by norm_num)
    have p7 := hpY 7 (by norm_num)
    omega
  refine EvalAll.letE d5 fun v5 c5 h5 => ?_
  obtain ⟨rfl, hc5⟩ := h5
  refine EvalAll.letE (d6 _) fun v6 c6 h6 => ?_
  obtain ⟨rfl, hc6⟩ := h6
  refine EvalAll.letE (d7 [.nat B, encPairs labKey L, .list XS, ONES] 6 rfl) fun Kv c7 h7 => ?_
  obtain ⟨hKv, hc7⟩ := h7
  -- step 8: the new hierarchy
  set env8 := [a, T1v, SQv, .nat B, encPairs labKey L, .list XS, ONES, Kv] with henv8
  set PH := Val.list [hv', .nat Q.pre.length, .nat m, .nat l, .nat r, encFun (leadF Q E e),
    .nat k, encFun fun j : Fin k => (j : ℕ)] with hPH
  have wPH : PH.wt ≤ 40 * Y ^ 2 := by
    have := wt_list_le [hv', .nat Q.pre.length, .nat m, .nat l, .nat r, encFun (leadF Q E e),
      .nat k, encFun fun j : Fin k => (j : ℕ)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    have e1 : (Val.list [hv', .nat Q.pre.length, .nat m, .nat l, .nat r, encFun (leadF Q E e),
      .nat k, encFun fun j : Fin k => (j : ℕ)]).wt = PH.wt := rfl
    omega
  have d8 : EvalAll Pg env8 (.call bph (Expr.mkList [.get (arg 1) (.nat 2), .get (arg 1) (.nat 4),
      .get (arg 2) (.nat 1), .get (arg 2) (.nat 2), .get (arg 2) (.nat 3),
      .get (.var 1) (.nat 1), .get (arg 0) (.nat 0), .get (.var 1) (.nat 3)]))
      (fun w cw => HierValC e w (Q.pre ++ Q.coordHier E ++ Q.post) ∧
        w.wt ≤ 10 ^ 101 * Y ^ 48 ∧ cw ≤ 3 * 10 ^ 101 * Y ^ 48) := by
    have hml := Det.mkList (P := Pg) (env := env8) (c := 100 * Y ^ 2)
      [(.get (arg 1) (.nat 2), hv'), (.get (arg 1) (.nat 4), .nat Q.pre.length),
        (.get (arg 2) (.nat 1), .nat m), (.get (arg 2) (.nat 2), .nat l),
        (.get (arg 2) (.nat 3), .nat r), (.get (.var 1) (.nat 1), encFun (leadF Q E e)),
        (.get (arg 0) (.nat 0), .nat k), (.get (.var 1) (.nat 3), encFun fun j : Fin k => (j : ℕ))]
      (by
        intro p hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact (hEX 2 _ rfl _ (by norm_num)).mono (by omega)
        · exact (hEX 4 _ rfl _ (by norm_num)).mono (by omega)
        · exact (hCS 1 _ rfl _ (by norm_num)).mono (by omega)
        · exact (hCS 2 _ rfl _ (by norm_num)).mono (by omega)
        · exact (hCS 3 _ rfl _ (by norm_num)).mono (by omega)
        · exact dT 1 _ _ rfl (by norm_num)
        · exact (dK _).mono (by omega)
        · exact dT 3 _ _ rfl (by norm_num))
    simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil] at hml
    refine EvalAll.call_funAll hml fun v0 ca h0 => ?_
    obtain ⟨rfl, hca⟩ := h0
    refine ((phier_spec hph hch hcv hfcv hmap hfcl hfind hft hspl happ Q E hr1 e hH).wt_lt).mono
      fun w cost hw => ?_
    obtain ⟨⟨hw1, hw2⟩, hw3⟩ := hw
    have hx : PH.wt + k * k + m + l + 1 ≤ 50 * Y ^ 2 := by omega
    have hq : phierK * (PH.wt + k * k + m + l + 1) ^ 24 ≤ 6 * 10 ^ 100 * Y ^ 48 :=
      calc _ ≤ phierK * (50 * Y ^ 2) ^ 24 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hx 24)
        _ = (phierK * 50 ^ 24) * Y ^ 48 := by ring
        _ ≤ 6 * 10 ^ 100 * Y ^ 48 := Nat.mul_le_mul_right _ (by unfold phierK; norm_num)
    have e1 : (Val.list [hv', .nat Q.pre.length, .nat m, .nat l, .nat r, encFun (leadF Q E e),
      .nat k, encFun fun j : Fin k => (j : ℕ)]).wt = PH.wt := rfl
    rw [e1] at hw2 hca
    refine ⟨hw1, by omega, by omega⟩
  refine EvalAll.letE d8 fun Hv c8 h8 => ?_
  obtain ⟨hHv, wHv, hc8⟩ := h8
  -- the dispatcher step
  have hpc := prod_cosetList Q E e hS hb hG L hnd (by rw [hsq1]; exact horb)
    (by rw [hsq1]; exact hpL)
  let ts := L.map fun p => unsq p.2
  let reps : CosetReps S.G (Q.productRed P₀ ⟨m, l, r, E, hS, hr⟩).K :=
    CosetReps.ofList _ hpc.1 hpc.2.1 hpc.2.2
  let Ds : DispatchStep P₀ S := .product Q inferInstance ⟨m, l, r, E, hS, hr⟩ reps hkeep
  have hlen : ts.length = Ds.n := by
    have := cosetList_length _ hpc.1 hpc.2.1 hpc.2.2
    simp only [List.length_map] at this
    exact (List.length_map _).trans this
  have hτ : ∀ j : Fin Ds.n, Ds.τ j = (toFin e).symm (ts.getD j 1) := fun j => by
    have hj : (j : ℕ) < ts.length := by rw [hlen]; exact j.2
    rw [List.getD_eq_getElem _ _ hj]
    show (ts.map (toFin e).symm)[(j : ℕ)]'_ = _
    rw [List.getElem_map]
  have hxs : ∀ i (hi : i < XS.length), ∃ key, XS[i] = .list [key, encPerm (ts.getD i 1)] := by
    intro i hi
    have hi' : i < L.length := by simpa [hXS] using hi
    refine ⟨natList (labKey L[i].1), ?_⟩
    simp [hXS, ts, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  -- the tail
  set env9 := [a, T1v, SQv, .nat B, encPairs labKey L, .list XS, ONES, Kv, Hv] with henv9
  set TI := Val.list [.list [v, Kv, Hv], .list XS] with hTI
  have hKw : Kv.wt ≤ groupW k := hKv.wt_le
  have hgW : groupW k ≤ 160 * Y ^ 4 := by
    have h1 : k ^ 2 + 2 ≤ 2 * Y := by omega
    have h2 : (k ^ 2 + 2) * (k + 1) ≤ 2 * Y * Y := Nat.mul_le_mul h1 (by omega)
    have h3 := Nat.pow_le_pow_left h2 2
    have e3 : (2 * Y * Y) ^ 2 = 4 * Y ^ 4 := by ring
    unfold groupW; omega
  have p4 := hpY 4 (by norm_num)
  have wTI : TI.wt ≤ 5 * 10 ^ 101 * Y ^ 48 := by
    have h1 := wt_list3_le v Kv Hv
    have h2 := wt_list2_le (.list [v, Kv, Hv]) (.list XS)
    have e2 : (Val.list [.list [v, Kv, Hv], .list XS]).wt = TI.wt := rfl
    omega
  have lTI := sum_wt_lt_wt_list [.list [v, Kv, Hv], .list XS]
  have l3 := sum_wt_lt_wt_list [v, Kv, Hv]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at lTI l3
  have eTI : (Val.list [.list [v, Kv, Hv], .list XS]).wt = TI.wt := rfl
  have dargs : Det Pg env9 (mk2 (mk3 (arg 0) (.var 7) (.var 8)) (.var 5)) TI
      (2 * W + 10 * TI.wt + 30) :=
    (Det.mk2 (Det.mk3 (hA 0 v rfl _) (Det.var' (P := Pg) (env := env9) (i := 7) (v := Kv) rfl)
      (Det.var' (P := Pg) (env := env9) (i := 8) (v := Hv) rfl))
      (Det.var' (P := Pg) (env := env9) (i := 5) (v := .list XS) rfl)).mono (by omega)
  refine EvalAll.call_funAll dargs fun v0 ca h0 => ?_
  obtain ⟨rfl, hca⟩ := h0
  refine (tail_spec Bc hm hbt hbtm hfch hbg hbc hg hcomp hinv happ hbn hjm hcan Ds.toData hKv
    hHv ts hlen hτ XS (by simp [hXS, ts]) hxs (hcall Ds rfl rfl rfl)).mono ?_
  rintro u cost ⟨hAu, hc⟩
  refine ⟨hAu, Ds, Kv0, ts, rfl, rfl, rfl, rfl, hKv0, hlen.le, ?_⟩
  have hu := hAu.wt_le
  have hsum : ∑ i ∈ Finset.range Ds.toData.n, Bc (tailChild S Ds.toData e (ts.getD i 1)) =
      (ts.map fun t => Bc (tailChild S Ds.toData e t)).sum := by
    change ∑ i ∈ Finset.range Ds.n, _ = _
    rw [← hlen]
    exact sum_range_getD _ fun t => Bc (tailChild S Ds.toData e t)
  rw [hsum] at hc
  have hc' : (cost : ℝ) ≤ (tailCost hm k TI.wt : ℕ) +
      (ts.map fun t => Bc (tailChild S Ds.toData e t)).sum := hc
  have htc := tailCost_mono hm k (show TI.wt ≤ 10 ^ 105 * Y ^ 48 by omega)
  have ha6 : 6 ≤ ansW k := by unfold ansW; omega
  have hpw : (encPairs labKey L).wt ≤ 45 * Y ^ 3 + 4 := by rw [ePL]; exact wPL
  have hnB : Ds.n = B := rfl
  rw [hnB]
  have wON : ONES.wt ≤ 4 * (k * k + 1) ^ 2 := wones
  have key0 : c1 + c2 + c4 + c5 + c6 + c7 + c8 + ca + 9 * (u.wt + 1) +
      tailCost hm k TI.wt + 2 * Y ^ 48 * 10 ^ 7 ≤ prodCost hp hm k W B := by
    unfold prodCost
    rw [← hY]
    omega
  have key : c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + ca + 9 * (u.wt + 1) +
      tailCost hm k TI.wt ≤ prodCostD hO hp hm k W B (encGroup gs) Kv0 := by
    unfold prodCostD
    omega
  have key' := (Nat.cast_le (α := ℝ)).mpr key
  push_cast at key' ⊢
  linarith


end GI.Degree
