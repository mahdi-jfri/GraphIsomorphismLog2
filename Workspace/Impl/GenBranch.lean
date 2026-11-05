module

public import Workspace.Impl.GenProdStep
public import Workspace.Impl.GenCase
public import Workspace.Impl.GenChild
public import Workspace.Impl.GenExposeProg

@[expose] public section

/-!
# The branch of the general dispatcher after the case decision

After the exposure (`expose_spec`, output `x`) and the case decision (`case_spec`, output `w`),
the general dispatcher takes one of three branches:

* `w = [0]`: the quotient is small, and the enumeration step runs (`enum_spec`);
* `w = [1, m, l, r, E]` with `r ≥ 2`: the product step runs (`prod_spec`);
* `w = [1, m, l, 1, E]`: the normalization runs.

The normalization is not implemented here. It enters as the hypothesis `NormSpec`: a function
that, on `[v, x, w]` with `r = 1`, returns a canonical answer of a run `Run.normalize`, at a cost
of at most `Cn k W` plus the cost of the children, for some function `Cn` of the number of points
`k` and the input weight `W`.

* `ds_hcall`: the induction hypothesis gives the calls on the children of any dispatcher step.
* `branchE`, `branch_spec`: the branch as a program, with cost `brCost`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens Preimage Membership encKSetTuples)

variable {Ω C : Type}

/-- **The calls on the children of a dispatcher step meet their specification**, by the
induction hypothesis: each child is a good `Continue` call (`dispatch_child_good`) of smaller
measure (`dispatch_child_mlt`). -/
theorem ds_hcall (I : Iface) {Pg : Program} {F : Funs} {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ}
    (hc : Function.Injective c) [Finite Ω] {S : State Ω C} (hgood : Good P₀ .cont S)
    (hs : (S.N : ℝ) ^ P₀.γ < S.size) (htr : S.Transitive) (hIH : I.IH Pg F .cont S)
    (Ds : DispatchStep P₀ S) :
    ∀ T : State Ω C, ∀ y', T.Inst Ds.K S.dom S.x y' → T.N = S.N → T.hier = Ds.hier' →
      ∀ val, Canon e c val T → FunAll Pg F.cont val (I.Post .cont T e val) :=
  fun T _ hT hN hh val hv =>
    hIH .cont T (dispatch_child_good hgood Ds hT hN hh)
      (dispatch_child_mlt (by have := P₀_κ; omega) hs htr Ds hT hN hh) k e c hc val hv

/-- **The hypothesis on the normalization.** The function `f` of `Pg`, on `[v, x, w]` where `v`
is a canonical value of a good transitive state above the threshold and off the floor, `x` the
output of the exposure for a quotient `Q` that kills the columns and keeps the levels, and
`w = [1, m, l, 1, E]` a product structure of `Q` with one coordinate where `Q` fails the
integer small test, returns a canonical answer of a run `Run.normalize`. Its own cost is at most
`Cn k W` for the input weight `W`. -/
def NormSpec (I : Iface) (Pg : Program) (F : Funs) (f : ℕ) (Cn : ℕ → ℕ → ℕ) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} (e : Ω ≃ Fin k) (c : C → ℕ), Function.Injective c →
    ∀ {gv dv xv yv hv rv fv hh : Val} {N : ℕ} {S : State Ω C},
    Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S → Good P₀ .cont S →
    (S.N : ℝ) ^ P₀.γ < S.size → S.Transitive → ¬ S.FloorEntered → I.IH Pg F .cont S →
    ∀ (Q : PrimitiveQuotient S), Q.KillsCols → Q.KeepsLevels → ∀ {x : Val}, ExposeOut e Q x →
    ∀ {m l : ℕ} (E : Fin Q.d ≃ (Fin 1 → Product.KSet m l)), Q.ProductStructure m l 1 E →
    ¬ Q.SmallZ P₀.smallExp →
    FunAll Pg f (.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N], x,
        .list [.nat 1, .nat m, .nat l, .nat 1, encKSetTuples E]])
      (fun u cost => ∃ (A : Set (Perm Ω)) (rn : Run P₀ .cont S none A),
        rn.kind = .normalize ∧ AnsC e u A ∧
        (cost : ℝ) ≤ Cn k (Val.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N], x,
          .list [.nat 1, .nat m, .nat l, .nat 1, encKSetTuples E]]).wt + I.childCost rn)

/-- The enumeration step at the function `f`: the conclusion of `enum_spec` for every input. -/
def EnumAt (I : Iface) (hp : Preimage) (hm : Membership) (Pg : Program) (F : Funs) (f : ℕ) :
    Prop :=
  ∀ {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {gv dv xv yv hv rv fv hh : Val} {N : ℕ}
    {S : State Ω C},
    Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S →
    (S.N : ℝ) ^ P₀.γ < S.size → S.Transitive → ¬ S.FloorEntered →
    ∀ (Q : PrimitiveQuotient S), Q.Small P₀.a →
    CarrierOK Q.kernel S.dom S.rows (Q.pre ++ Q.top :: Q.post) →
    ∀ {lv hv' : Val}, (ReprVal k lv fun i j => Q.labFin e i = Q.labFin e j) →
    HierValC e hv' (Q.pre ++ Q.top :: Q.post) → ∀ {B : ℕ}, Nat.card Q.ρ.range ≤ B →
    (∀ T : State Ω C, ∀ y', T.Inst Q.kernel S.dom S.x y' → T.N = S.N →
      T.hier = Q.pre ++ Q.top :: Q.post →
      ∀ val, Canon e c val T → FunAll Pg F.cont val (I.Post .cont T e val)) →
    FunAll Pg f (.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N], lv, hv', .nat B])
      (fun u cost => ∃ (A : Set (Perm Ω)) (r : Run P₀ .cont S none A), r.kind = .dispatch ∧
        AnsC e u A ∧ (cost : ℝ) ≤ enumCost hp hm k (Val.list [.list [.nat k, gv, dv, xv, yv, hv,
          rv, fv, hh, .nat N], lv, hv', .nat B]).wt B + I.childCost r)

theorem enumAt_of (I : Iface) (hp : Preimage) (hm : Membership) {Pg : Program} {F : Funs}
    {f bco bk bt bm fch bg bc g comp inv app bn jm jpre : ℕ}
    (hf : Pg.funs[f]? = some (enumF bco bk bt))
    (hco : Pg.HasAt bco (cosetsFuns bco))
    (hbk : Pg.HasAt bk (kerNFFuns bk jpre jm)) (hjp : Pg.prims[jpre]? = some (preimagePrim hp))
    (hbt : Pg.funs[bt]? = some (tailF bm bc bn))
    (hbm : Pg.HasAt bm (mapFuns bm fch)) (hch : Pg.funs[fch]? = some (enumChildF F bg))
    (hga : Pg.HasAt bg (gatherFuns bg))
    (hbc : Pg.HasAt bc (foldlFuns bc g)) (hg : Pg.funs[g]? = some (combStep comp inv app))
    (hcomp : Pg.HasAt comp (composeFuns comp)) (hinv : Pg.HasAt inv (invFuns inv))
    (happ : Pg.HasAt app (appendFuns app))
    (hbn : Pg.HasAt bn (cosetNFFuns bn jm)) (hjm : Pg.prims[jm]? = some (membershipPrim hm)) :
    EnumAt I hp hm Pg F f :=
  fun hcan hs htr hfl Q hsmall hkeep _ _ hR hH _ hB hcall =>
    enum_spec I hp hm hf hco hbk hjp hbt hbm hch hga hbc hg hcomp hinv happ hbn hjm hcan hs htr hfl Q hsmall hkeep hR hH hB hcall

/-- The product step at the function `f`: the conclusion of `prod_spec` for every input. -/
def ProdAt (I : Iface) (hp : Preimage) (hm : Membership) (Pg : Program) (F : Funs) (f : ℕ) :
    Prop :=
  ∀ {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {gv dv xv yv hv rv fv hh : Val} {N : ℕ}
    {S : State Ω C},
    Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S →
    (S.N : ℝ) ^ P₀.γ < S.size → S.Transitive → ¬ S.FloorEntered →
    ∀ (Q : PrimitiveQuotient S) {m l r : ℕ} (E : Fin Q.d ≃ (Fin r → Product.KSet m l))
      (hS : Q.ProductStructure m l r E), 2 ≤ r →
    CarrierOK (Q.coordinateGroup E hS (Q.two_le_choose E)) S.dom S.rows
      (Q.pre ++ Q.coordHier E ++ Q.post) →
    ∀ {gv' rep hv' : Val}, HierValC e hv' (Q.pre ++ Q.top :: Q.post) →
    (∀ T : State Ω C, ∀ y', T.Inst (Q.coordinateGroup E hS (Q.two_le_choose E)) S.dom
      S.x y' → T.N = S.N → T.hier = Q.pre ++ Q.coordHier E ++ Q.post →
      ∀ val, Canon e c val T → FunAll Pg F.cont val (I.Post .cont T e val)) →
    FunAll Pg f (.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N],
        .list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length],
        .list [.nat 1, .nat m, .nat l, .nat r, encKSetTuples E]])
      (fun u cost => ∃ (A : Set (Perm Ω)) (rn : Run P₀ .cont S none A), rn.kind = .dispatch ∧
        AnsC e u A ∧ (cost : ℝ) ≤ prodCost hp hm k (Val.list
          [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N],
          .list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length],
          .list [.nat 1, .nat m, .nat l, .nat r, encKSetTuples E]]).wt r.factorial +
          I.childCost rn)

theorem prodAt_of (I : Iface) (hp : Preimage) (hm : Membership) {Pg : Program} {F : Funs}
    {f bpt bsq bfact bco bpu bones bpk bph bt : ℕ}
    (hf : Pg.funs[f]? = some (prodE bpt bsq bfact bco bpu bones bpk bph bt))
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
    (hfact : Pg.HasAt bfact (factFuns bfact)) (hco : Pg.HasAt bco (cosetsFuns bco))
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
    (hbn : Pg.HasAt bn (cosetNFFuns bn jm)) :
    ProdAt I hp hm Pg F f :=
  fun hcan hs htr hfl Q _ _ _ E hS hr hkeep _ _ _ hH hcall =>
    prod_spec I hp hm hf hpt hprows hbm hfadd hrep hga hrange hm0 hfs0 hm1 hfs1 hl heq hsq hfsq hbsm hfse hfu hbmt hfe hfact hco hpu hfpu hones hfone hpk hcls hker hjp hjm hmu hred hph hch hcv hfcv hmap hfcl hfind hft hspl happ hbt hbtm hfch hbg hbc hg hcomp hinv hbn hcan hs htr hfl Q E hS hr hkeep hH hcall

/-- The branch on `[v, x, w, B]`: enumeration on `[v, rep, h', B]` when `w = [0]`, the product
step on `[v, x, w]` when `w = [1, m, l, r, E]` with `r ≥ 2`, and the normalization on `[v, x, w]`
when `r = 1`. -/
def branchE (fen fpr fno : ℕ) : Expr :=
  .ite (.get (arg 2) (.nat 0))
    (.ite (.arith .lt (.nat 1) (.get (arg 2) (.nat 3)))
      (.call fpr (mk3 (arg 0) (arg 1) (arg 2)))
      (.call fno (mk3 (arg 0) (arg 1) (arg 2))))
    (.call fen (mk4 (arg 0) (.get (arg 1) (.nat 1)) (.get (arg 1) (.nat 2)) (arg 3)))

/-- The number of coordinates in a case output `[1, m, l, r, E]` (`0` otherwise). -/
def caseR : Val → ℕ
  | .list [_, _, _, .nat r, _] => r
  | _ => 0

theorem enumCost_mono (hp : Preimage) (hm : Membership) (k B : ℕ) {W W' : ℕ} (h : W ≤ W') :
    enumCost hp hm k W B ≤ enumCost hp hm k W' B := by
  unfold enumCost
  have h1 := Nat.mul_le_mul_left cosetsK
    (Nat.pow_le_pow_left (show W + B + 4 * (k + 1) ^ 2 + 20 ≤ W' + B + 4 * (k + 1) ^ 2 + 20 by
      omega) 6)
  have h2 := kerNFCost_mono hp hm k (show 2 * W + 6 ≤ 2 * W' + 6 by omega)
  have h3 : tailInW k W B ≤ tailInW k W' B := by unfold tailInW; omega
  have h4 := tailCost_mono hm k h3
  omega

/-- **The own cost of the branch**, for an input of weight `W`, a bound `B` on the order of the
quotient group, `r` coordinates (`r = 0` for the enumeration) and the normalization cost `Cn`.
Only the enumeration depends on `B`. -/
noncomputable def brCost (hp : Preimage) (hm : Membership) (Cn : ℕ → ℕ → ℕ) (k W B r : ℕ) : ℕ :=
  (if r = 0 then enumCost hp hm k (2 * W + 10) B else prodCost hp hm k W r.factorial + Cn k W) +
    40 * W + 3 * ansW k + 400

theorem prodCost_mono (hp : Preimage) (hm : Membership) (k B : ℕ) {W W' : ℕ} (h : W ≤ W') :
    prodCost hp hm k W B ≤ prodCost hp hm k W' B := by
  unfold prodCost
  have h1 : prodY k W B ^ 48 ≤ prodY k W' B ^ 48 :=
    Nat.pow_le_pow_left (by unfold prodY; omega) 48
  have h2 := tailCost_mono hm k (Nat.mul_le_mul_left (10 ^ 105) h1)
  have h3 := Nat.mul_le_mul_left (10 ^ 110) h1
  omega

/-- **The branch meets its specification.** On `[v, x, w, B]`, where `v` is a canonical value
of a good transitive state above the threshold and off the floor, `x` the output of the
exposure for a quotient `Q` that kills the columns and keeps the levels, `w` the output of the
case decision for `Q` and `B ≥ |ρ(G)|`, the branch returns a canonical answer of a run
`Run.dispatch` or `Run.normalize`, at a cost of at most `brCost` plus the cost of the children. -/
theorem branch_spec (I : Iface) (hp : Preimage) (hm : Membership) {Pg : Program} {F : Funs}
    {f fen fpr fno : ℕ} (hf : Pg.funs[f]? = some (branchE fen fpr fno))
    (hen : EnumAt I hp hm Pg F fen) (hpr : ProdAt I hp hm Pg F fpr)
    {Cn : ℕ → ℕ → ℕ} (hno : NormSpec I Pg F fno Cn)
    (hCn : ∀ {k W W' : ℕ}, W ≤ W' → Cn k W ≤ Cn k W')
    {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} (hc : Function.Injective c)
    {gv dv xv yv hv rv fv hh : Val} {N : ℕ} {S : State Ω C}
    (hcan : Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S)
    (hgood : Good P₀ .cont S) (hs : (S.N : ℝ) ^ P₀.γ < S.size) (htr : S.Transitive)
    (hfl : ¬ S.FloorEntered) (hIH : I.IH Pg F .cont S)
    (Q : PrimitiveQuotient S) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
    {x w : Val} (hx : ExposeOut e Q x) (hw : CaseOut Q w) {B : ℕ} (hB : Nat.card Q.ρ.range ≤ B) :
    FunAll Pg f (.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N], x, w, .nat B])
      (fun u cost => ∃ (A : Set (Perm Ω)) (rn : Run P₀ .cont S none A),
        rn.kind ∈ [CallKind.dispatch, CallKind.normalize] ∧ AnsC e u A ∧
        (cost : ℝ) ≤ brCost hp hm Cn k (Val.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh,
          .nat N], x, w, .nat B]).wt B (caseR w) + I.childCost rn) := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  obtain ⟨gv', rep, hv', rfl, hgv', hrep, hnum, hH⟩ := hx
  set v := Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] with hvdef
  set x := Val.list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length] with hxdef
  set a := Val.list [v, x, w, .nat B] with ha
  obtain ⟨W, hW⟩ : ∃ W, W = a.wt := ⟨_, rfl⟩
  rw [← hW]
  have hA : ∀ (j : ℕ) (w' : Val), [v, x, w, .nat B][j]? = some w' → ∀ rest : List Val,
      Det Pg (a :: rest) (arg j) w' (2 * W + j + 5) := fun j w' hj rest => by
    rw [hW]; exact Det.arg' hj
  have wa := sum_wt_lt_wt_list [v, x, w, .nat B]
  have wx := sum_wt_lt_wt_list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at wa wx
  have ea : (Val.list [v, x, w, .nat B]).wt = W := by rw [hW]
  have ex : (Val.list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length]).wt = x.wt := rfl
  have hu6 : 6 ≤ ansW k := by unfold ansW; omega
  have hWx : (Val.list [v, x, w]).wt ≤ W := by
    rw [← ea]; exact wt_list_mono ⟨[.nat B], rfl⟩
  refine FunAll.intro hf ?_
  rcases hw with ⟨rfl, hsmall⟩ | ⟨m, l, r, E, rfl, hS, hr1, hnz⟩
  · -- the enumeration
    have dc : Det Pg [a] (.get (arg 2) (.nat 0)) (.nat 0) (3 * W + 20) :=
      (Det.get' (hA 2 _ rfl []) (Det.nat 0) (show [Val.nat 0][0]? = some (.nat 0) from rfl)).mono
        (by have := wt_nat_le 0; omega)
    refine EvalAll.ite dc (fun _ _ h => ⟨0, h.1⟩) fun y cc h => ?_
    obtain ⟨h1, hcc⟩ := h
    cases h1
    rw [if_pos rfl]
    have dargs := Det.mk4 (hA 0 v rfl []) (Det.get' (hA 1 x rfl []) (Det.nat 1)
      (show [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length][1]? = some rep from rfl))
      (Det.get' (hA 1 x rfl []) (Det.nat 2)
        (show [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length][2]? = some hv' from rfl))
      (hA 3 (.nat B) rfl [])
    refine EvalAll.call_funAll dargs fun v0 ca h0 => ?_
    obtain ⟨rfl, hca⟩ := h0
    have hkeep := Q.kernel_keeps hkc hkl
    refine (hen hcan hs htr hfl Q hsmall hkeep hrep hH hB (ds_hcall I hc hgood hs htr hIH
      (.enumeration Q inferInstance htr hsmall (CosetReps.default _ _) hkeep))).mono ?_
    rintro u cost ⟨A, rn, hk, hAu, hcost⟩
    refine ⟨A, rn, by simp [hk], hAu, ?_⟩
    have hu := hAu.wt_le
    have hWe : (Val.list [v, rep, hv', .nat B]).wt ≤ 2 * W + 10 := by
      have := wt_list4_le v rep hv' (.nat B); omega
    have hmo := enumCost_mono hp hm k B hWe
    have w1 := wt_nat_le 1
    have w2 := wt_nat_le 2
    have key : cc + (ca + enumCost hp hm k (Val.list [v, rep, hv', .nat B]).wt B + u.wt + 1) +
        u.wt + 1 ≤ brCost hp hm Cn k W B (caseR (.list [.nat 0])) := by
      have h0 : caseR (Val.list [.nat 0]) = 0 := rfl
      unfold brCost; rw [h0, if_pos rfl]; omega
    have key' := (Nat.cast_le (α := ℝ)).mpr key
    push_cast at key' ⊢
    linarith
  · -- the product step or the normalization
    set z := Val.list [.nat 1, .nat m, .nat l, .nat r, encKSetTuples E] with hzdef
    have dc : Det Pg [a] (.get (arg 2) (.nat 0)) (.nat 1) (3 * W + 20) :=
      (Det.get' (hA 2 _ rfl []) (Det.nat 0)
        (show [Val.nat 1, .nat m, .nat l, .nat r, encKSetTuples E][0]? = some (.nat 1)
          from rfl)).mono (by have := wt_nat_le 1; have := wt_nat_le 0; omega)
    refine EvalAll.ite dc (fun _ _ h => ⟨1, h.1⟩) fun y cc h => ?_
    obtain ⟨h1, hcc⟩ := h
    cases h1
    rw [if_neg one_ne_zero]
    have wz := sum_wt_lt_wt_list [Val.nat 1, .nat m, .nat l, .nat r, encKSetTuples E]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at wz
    have ez : (Val.list [Val.nat 1, .nat m, .nat l, .nat r, encKSetTuples E]).wt = z.wt := rfl
    have dr : Det Pg [a] (.get (arg 2) (.nat 3)) (.nat r) (3 * W + 20) :=
      (Det.get' (hA 2 _ rfl []) (Det.nat 3)
        (show [Val.nat 1, .nat m, .nat l, .nat r, encKSetTuples E][3]? = some (.nat r)
          from rfl)).mono (by have := wt_nat_le 3; omega)
    have dlt := Det.arith' (op := .lt) (Det.nat (P := Pg) (env := [a]) 1) dr rfl
    have dargs := Det.mk3 (hA 0 v rfl []) (hA 1 x rfl []) (hA 2 z rfl [])
    have hW3 : (Val.list [v, x, z]).wt ≤ W := hWx
    have hcr : caseR z = r := rfl
    rw [hcr]
    refine EvalAll.ite dlt (fun _ _ h => ⟨_, h.1⟩) fun y c2 h => ?_
    obtain ⟨h1, hc2⟩ := h
    cases h1
    by_cases hr2 : 2 ≤ r
    · -- the product step
      have h1 : GI.Machine.BinOp.eval .lt 1 r = 1 := by
        show (if 1 < r then 1 else 0) = 1; rw [if_pos (by omega)]
      rw [h1, if_neg one_ne_zero]
      refine EvalAll.call_funAll dargs fun v0 ca h0 => ?_
      obtain ⟨rfl, hca⟩ := h0
      have hkeep : CarrierOK (Q.coordinateGroup E hS (Q.two_le_choose E)) S.dom S.rows
          (Q.pre ++ Q.coordHier E ++ Q.post) :=
        Q.productRed_keeps P₀ hkc hkl ⟨m, l, r, E, hS, hr2⟩
      refine (hpr hcan hs htr hfl Q E hS hr2 hkeep hH (ds_hcall I hc hgood hs htr hIH
        (.product Q inferInstance ⟨m, l, r, E, hS, hr2⟩ (CosetReps.default _ _) hkeep))).mono ?_
      rintro u cost ⟨A, rn, hk, hAu, hcost⟩
      refine ⟨A, rn, by simp [hk], hAu, ?_⟩
      have hu := hAu.wt_le
      have hmo := prodCost_mono hp hm k r.factorial hW3
      have h1' : GI.Machine.BinOp.eval .lt 1 r = 1 := h1
      rw [h1'] at hc2
      have key : cc + (c2 + (ca + prodCost hp hm k (Val.list [v, x, z]).wt r.factorial +
          u.wt + 1) + u.wt + 1) + u.wt + 1 ≤ brCost hp hm Cn k W B r := by
        unfold brCost; rw [if_neg (by omega)]; have := wt_nat_le 1; omega
      have key' := (Nat.cast_le (α := ℝ)).mpr key
      push_cast at key' ⊢
      linarith
    · -- the normalization
      obtain rfl : r = 1 := by omega
      have h0 : GI.Machine.BinOp.eval .lt 1 1 = 0 := rfl
      rw [h0, if_pos rfl]
      refine EvalAll.call_funAll dargs fun v0 ca h0 => ?_
      obtain ⟨rfl, hca⟩ := h0
      refine (hno e c hc hcan hgood hs htr hfl hIH Q hkc hkl ⟨gv', rep, hv', rfl, hgv', hrep, hnum, hH⟩
        E hS hnz).mono ?_
      rintro u cost ⟨A, rn, hk, hAu, hcost⟩
      refine ⟨A, rn, by simp [hk], hAu, ?_⟩
      have hu := hAu.wt_le
      have hmo : Cn k (Val.list [v, x, z]).wt ≤ Cn k W := hCn hW3
      rw [h0] at hc2
      have key : cc + (c2 + (ca + Cn k (Val.list [v, x, z]).wt + u.wt + 1) + u.wt + 1) +
          u.wt + 1 ≤ brCost hp hm Cn k W B 1 := by
        unfold brCost; rw [if_neg one_ne_zero]; have := wt_nat_le 1; omega
      have key' := (Nat.cast_le (α := ℝ)).mpr key
      push_cast at key' ⊢
      linarith

end GI.Impl
