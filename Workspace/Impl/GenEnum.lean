module

public import Workspace.Impl.Orbit
public import Workspace.Impl.GenChild
public import Workspace.Impl.GenKernel
public import Workspace.Impl.Combine
public import Workspace.Impl.MapGhost
public import Workspace.Lang.Lib.Tabulate

@[expose] public section

/-!
# The enumeration step of the dispatcher

Algorithm 5: "if enumeration … applies, apply that reduction and solve its children with
`Continue`; return their exact combined answer". For a small primitive quotient `Q` the
reduction splits `G` into the cosets `τ_j K` of the block kernel `K`, and the child on `τ_j K`
runs under `K` with target `y ∘ τ_j` and the exposed hierarchy (`Run.dispatch`).

This file has the call on one coset (`enumChildF`, `enumChild_spec`): it computes `y ∘ τ_j` with
`gather`, builds the child value (`dispChildVal`) and calls `Continue` on it. It returns the
pair `[encPerm τ_j, answer]`, the input of the combination (`Workspace/Impl/Combine.lean`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens Membership Preimage)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-- Entry `j` of the state value inside the context `[v, K, h']` of the call on one coset. -/
def ctxV (j : ℕ) : Expr := .get (.get (arg 0) (.nat 0)) (.nat j)

/-- **The call on one coset.** On `[[v, K, h'], [key, encPerm t]]`: `y' := gather (y, t)`, then
`[encPerm t, Continue (child value)]`, where the child value is `v` with the group `K`, the
target `y'` and the hierarchy `h'`. `bg` is the base of `gather`. -/
def enumChildF (F : Funs) (bg : ℕ) : Expr :=
  .letE (.call bg (mk2 (ctxV 4) (.get (arg 1) (.nat 1))))
    (mk2 (.get (arg 1) (.nat 1)) (.call F.cont (Expr.mkList
      [ctxV 0, .get (arg 0) (.nat 1), ctxV 2, ctxV 3, .var 1, .get (arg 0) (.nat 2), ctxV 6,
        ctxV 7, ctxV 8, ctxV 9])))

/-- The own cost bound of the call on one coset, for a context and pair of weight at most `Z`. -/
def enumChildB (Z : ℕ) : ℕ := 10 ^ 7 * (Z + 1) ^ 3

/-- **The call on one coset meets its specification.** -/
theorem enumChild_spec (I : Iface) {Pg : Program} {F : Funs} {f bg : ℕ}
    (hf : Pg.funs[f]? = some (enumChildF F bg)) (hga : Pg.HasAt bg (gatherFuns bg))
    {e : Ω ≃ Fin k} {c : C → ℕ} {gv dv xv yv hv rv fv hh : Val} {N : ℕ} {S : State Ω C}
    (hcan : Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S)
    (Ds : DispatchStep P₀ S) (t : Perm (Fin k)) {T : State Ω C}
    (hT : T.Inst Ds.K S.dom S.x (S.y ∘ (toFin e).symm t)) (hN : T.N = S.N)
    (hh' : T.hier = Ds.hier') (hbk : T.book = S.book) {Kv hv' : Val}
    (hK : GroupValC k Kv (groupFin e Ds.K)) (hH : HierValC e hv' Ds.hier')
    (hcall : ∀ val, Canon e c val T → FunAll Pg F.cont val (I.Post .cont T e val)) (key : Val) :
    FunAll Pg f (.list [.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N], Kv, hv'],
        .list [key, encPerm t]])
      (fun w cost => (∃ u, w = .list [encPerm t, u] ∧ AnsC e u T.answer) ∧
        ∃ cb : ℕ, (∃ (A : Set (Perm Ω)) (r : Run P₀ .cont T none A), (cb : ℝ) ≤ r.total I.work) ∧
          cost ≤ enumChildB (5 * (Val.list [.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh,
            .nat N], Kv, hv'], .list [key, encPerm t]]).wt + ansW k + 20 * (k + 1) ^ 2 + 10) +
            cb) := by
  obtain ⟨gv0, dv0, xv0, yv0, hv0, rv0, -, -, -, hyv, -, -, heq⟩ := hcan.val
  simp only [Val.list.injEq, List.cons.injEq] at heq
  obtain ⟨-, -, -, -, rfl, -, -, -, -, -, -⟩ := heq
  set v := Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] with hvdef
  set ctx := Val.list [v, Kv, hv'] with hctx
  set x := Val.list [key, encPerm t] with hx
  set a := Val.list [ctx, x] with ha
  -- the target coloring after `t`
  set τ := (toFin e).symm t with hτ
  have htτ : toFin e τ = t := MulEquiv.apply_symm_apply _ _
  set yv' := encFun fun i => c ((S.y ∘ τ) (e.symm i)) with hyv'
  have hyv0 : yv = .list ((List.finRange k).map fun i => Val.nat (c (S.y (e.symm i)))) := hyv
  have hg := gather_spec hga (L := (List.finRange k).map fun i => Val.nat (c (S.y (e.symm i))))
    (is := (List.finRange k).map fun i => (t i : ℕ)) (by simp)
  have hgy : (((List.finRange k).map fun i => (t i : ℕ)).map fun j =>
      ((List.finRange k).map fun i => Val.nat (c (S.y (e.symm i)))).getD j (.nat 0)) =
      (List.finRange k).map fun i => Val.nat (c ((S.y ∘ τ) (e.symm i))) := by
    rw [← htτ]; exact gather_colors e c S.y τ
  rw [hgy] at hg
  have hy' : ColorVal e c yv' (S.y ∘ τ) := rfl
  have hyc : ∀ b, c ((S.y ∘ τ) b) < 2 * k := fun b => (hcan.colors (τ b)).2
  have hcanT := canon_dispChild (k := k) hcan Ds hT hN hh' hbk hK hy' hyc hH
  have hcallT := hcall _ hcanT
  -- weights
  have wv : v.wt < ctx.wt := wt_le_wt_list (by simp)
  have wK : Kv.wt < ctx.wt := wt_le_wt_list (by simp)
  have wH : hv'.wt < ctx.wt := wt_le_wt_list (by simp)
  have wc : ctx.wt < a.wt := wt_le_wt_list (by simp)
  have wx : x.wt < a.wt := wt_le_wt_list (by simp)
  have wt : (encPerm t).wt < x.wt := wt_le_wt_list (by simp)
  have wy : yv.wt < v.wt := wt_le_wt_list (by simp)
  have wyv' : yv'.wt ≤ 4 * (2 * k + 1) ^ 2 := by
    have := wt_encFun_le (fun i => c ((S.y ∘ τ) (e.symm i))) (B := 2 * k)
      fun i => (hyc _).le
    nlinarith
  have ea : (Val.list [ctx, x]).wt = a.wt := rfl
  have ev : (Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]).wt = v.wt := rfl
  have ec : (Val.list [v, Kv, hv']).wt = ctx.wt := rfl
  have ex : (Val.list [key, encPerm t]).wt = x.wt := rfl
  -- the entries of the state value
  have dctx : ∀ rest, Det Pg (a :: rest) (.get (arg 0) (.nat 0)) v (3 * a.wt + 10) := fun rest =>
    (Det.get' (Det.arg' (vs := [ctx, x]) (rest := rest) (j := 0) rfl) (Det.nat 0)
      (show [v, Kv, hv'][0]? = some v from rfl)).mono (by omega)
  have dent : ∀ rest j (hj : j < 10), Det Pg (a :: rest) (ctxV j)
      [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N][j] (5 * a.wt + 30) := fun rest j hj => by
    have := wt_getElem_lt [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] j (by simpa using hj)
    exact (Det.get' (dctx rest) (Det.nat j) (List.getElem?_eq_getElem (by simpa using hj))).mono
      (by omega)
  have dt : ∀ rest, Det Pg (a :: rest) (.get (arg 1) (.nat 1)) (encPerm t) (3 * a.wt + 10) :=
    fun rest => (Det.get' (Det.arg' (vs := [ctx, x]) (rest := rest) (j := 1) rfl) (Det.nat 1)
      (show [key, encPerm t][1]? = some (encPerm t) from rfl)).mono (by omega)
  -- gather
  have hgath := Det.call (Det.mk2 (dent [] 4 (by omega)) (dt [])) (by
    rw [hyv0, encPerm_eq_natList]; exact hg)
  refine FunAll.intro hf (EvalAll.letE hgath fun yw cy hyw => ?_)
  obtain ⟨rfl, hcy⟩ := hyw
  have hyw : Val.list ((List.finRange k).map fun i => Val.nat (c ((S.y ∘ τ) (e.symm i)))) = yv' :=
    rfl
  rw [hyw] at hcy ⊢
  -- the child value
  have hval := Det.mkList (P := Pg) (env := [a, yv']) (c := 5 * a.wt + 30 + 5 * (k + 1) ^ 2 * 4)
    [(ctxV 0, .nat k), (.get (arg 0) (.nat 1), Kv), (ctxV 2, dv), (ctxV 3, xv), (.var 1, yv'),
      (.get (arg 0) (.nat 2), hv'), (ctxV 6, rv), (ctxV 7, fv), (ctxV 8, hh), (ctxV 9, .nat N)]
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (dent [yv'] 0 (by omega)).mono (by omega)
      · exact (Det.get' (Det.arg' (vs := [ctx, x]) (rest := [yv']) (j := 0) rfl) (Det.nat 1)
          (show [v, Kv, hv'][1]? = some Kv from rfl)).mono (by omega)
      · exact (dent [yv'] 2 (by omega)).mono (by omega)
      · exact (dent [yv'] 3 (by omega)).mono (by omega)
      · exact (Det.var' (i := 1) rfl).mono (by nlinarith)
      · exact (Det.get' (Det.arg' (vs := [ctx, x]) (rest := [yv']) (j := 0) rfl) (Det.nat 2)
          (show [v, Kv, hv'][2]? = some hv' from rfl)).mono (by omega)
      · exact (dent [yv'] 6 (by omega)).mono (by omega)
      · exact (dent [yv'] 7 (by omega)).mono (by omega)
      · exact (dent [yv'] 8 (by omega)).mono (by omega)
      · exact (dent [yv'] 9 (by omega)).mono (by omega))
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hval
  have hcl := call_child I hval hcallT
  refine (EvalAll.snoc_det (Det.mk1 (dt [yv'])) hcl).mono ?_
  rintro w cw ⟨u, cu, ⟨A, r, cb, hA, hcb, hcu⟩, rfl, hcw⟩
  have hAT := r.exact
  subst hAT
  refine ⟨⟨u, rfl, hA⟩, cb, ⟨_, r, hcb⟩, ?_⟩
  have wu := hA.wt_le
  set Z := 5 * a.wt + ansW k + 20 * (k + 1) ^ 2 + 10 with hZ
  have hZ1 : Z + 1 ≤ (Z + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hX : (Val.list [Val.list ((List.finRange k).map fun i => Val.nat (c (S.y (e.symm i)))),
      natList ((List.finRange k).map fun i => (t i : ℕ))]).wt + 1 ≤ Z + 1 := by
    rw [← hyv0, ← encPerm_eq_natList]
    have := wt_list2_le yv (encPerm t)
    omega
  have hX3 := Nat.pow_le_pow_left hX 3
  have hg3 := Nat.mul_le_mul_left gatherK hX3
  have w10 := wt_list_le [.nat k, Kv, dv, xv, yv', hv', rv, fv, hh, .nat N]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w10
  have w10' := sum_wt_lt_wt_list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at w10'
  have hk2 : (2 * k + 1) ^ 2 ≤ 4 * (k + 1) ^ 2 :=
    calc (2 * k + 1) ^ 2 ≤ (2 * (k + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 * (k + 1) ^ 2 := by ring
  have wtu := wt_list2_le (encPerm t) u
  have etu : (Val.list ([encPerm t] ++ [u])).wt = (Val.list [encPerm t, u]).wt := rfl
  have w1 := wt_list_le [encPerm t]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at w1
  have ev' : v.wt = (Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]).wt := rfl
  unfold enumChildB
  have hgK : gatherK * (Z + 1) ^ 3 ≤ 100000 * (Z + 1) ^ 3 := by simp [gatherK]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hcy
  clear hval hcl hgath hcallT hcanT hcall
  have hq := wt_list2_le yv (encPerm t)
  have hfin : cy + cw + (Val.list ([encPerm t] ++ [u])).wt + 1 ≤
      1000 * (Z + 1) + gatherK * (Z + 1) ^ 3 + cb := by omega
  omega

/-! ### Answers and pieces -/

theorem enumChildB_mono {Z Z' : ℕ} (h : Z ≤ Z') : enumChildB Z ≤ enumChildB Z' :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)

/-- A canonical answer is the value of an accumulator with the image of the answer as set. -/
theorem AnsC.acc {e : Ω ≃ Fin k} {u : Val} {A : Set (Perm Ω)} (h : AnsC e u A) :
    ∃ a : Acc k, u = encAcc a ∧ accSet a = toFin e '' A := by
  rcases h with ⟨rfl, rfl⟩ | ⟨x, gs, rfl, -, hA⟩
  · exact ⟨none, rfl, by simp [accSet]⟩
  · exact ⟨some (x, gs), rfl, hA.symm⟩

/-- A normal form of the image of a set is a canonical answer of the set. -/
theorem CosetC.ansC {e : Ω ≃ Fin k} {u : Val} {A : Set (Perm Ω)}
    (h : CosetC k u (toFin e '' A)) : AnsC e u A := by
  rcases h with ⟨rfl, hA⟩ | ⟨x, hs, rfl, hl, hA⟩
  · exact Or.inl ⟨rfl, Set.image_eq_empty.mp hA⟩
  · exact Or.inr ⟨x, hs, rfl, hl, hA⟩

/-- The exact answer is empty or a left coset, and so is its image. -/
theorem image_answer_cases (e : Ω ≃ Fin k) (S : State Ω C) :
    toFin e '' S.answer = ∅ ∨ ∃ (x : Perm (Fin k)) (H : Subgroup (Perm (Fin k))),
      toFin e '' S.answer = x • (H : Set _) := by
  rcases S.answer.eq_empty_or_nonempty with h | ⟨t, ht⟩
  · left; rw [h, Set.image_empty]
  · right
    refine ⟨toFin e t, groupFin e (autGroup S.G S.dom S.dom_inv S.x), ?_⟩
    rw [show S.answer = _ from answer_eq_smul_aut S.dom_inv ht, toFin_image_coset]

/-- The image of a translate. -/
theorem image_toFin_smul (e : Ω ≃ Fin k) (t : Perm Ω) (A : Set (Perm Ω)) :
    toFin e '' (t • A) = toFin e t • (toFin e '' A) :=
  Set.image_smul_distrib (toFin e) t A

theorem combM_mono (n : ℕ) {W W' : ℕ} (h : W ≤ W') : combM n W ≤ combM n W' :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (by omega)) 2)

theorem combCost_mono (n : ℕ) {W W' : ℕ} (h : W ≤ W') : combCost n W ≤ combCost n W' := by
  unfold combCost
  have hm := combM_mono n h
  have h1 : (4 * W + 2 * combM n W + 7 + (n + 1) ^ 4) ^ 2 ≤
      (4 * W' + 2 * combM n W' + 7 + (n + 1) ^ 4) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 := Nat.mul_le_mul_left combK h1
  have h3 : loopModK * (2 * W + combM n W + 1) ≤ loopModK * (2 * W' + combM n W' + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  exact Nat.mul_le_mul (by omega) (by omega)

theorem cosetNFCost_mono (h : Membership) (n : ℕ) {W W' : ℕ} (hW : W ≤ W') :
    cosetNFCost h n W ≤ cosetNFCost h n W' := by
  unfold cosetNFCost
  have := reduceCost_mono h n hW
  omega

/-! ### The children, the combination and the normal form -/

/-- **The tail of a dispatcher step.** On `[[v, K, h'], pairs]`: the call on each coset
(`map`), the combination of the pieces, and its normal form. -/
def tailF (bm bc bn : ℕ) : Expr :=
  .letE (.call bm (.var 0)) (.call bn (.call bc (mk3 (.nat 0) (.var 1) .nil)))

/-- The weight bound of one piece `[encPerm t, answer]`. -/
def pieceW (k : ℕ) : ℕ := 2 * (4 * (k + 1) ^ 2 + ansW k) + 6

/-- The weight bound of the list of pieces, for an input of weight `W`. -/
def piecesW (k W : ℕ) : ℕ := W * (2 * pieceW k + 1) + 4

/-- The weight bound of the input of the combination. -/
def combInW (k W : ℕ) : ℕ := 2 * piecesW k W + 30

/-- The weight bound of the output of the combination. -/
def combOutW (k W : ℕ) : ℕ := 100 * ((combInW k W + 2) * (k + 1)) ^ 2

/-- **The own cost of the tail**, for an input of weight `W`. -/
noncomputable def tailCost (hm : Membership) (k W : ℕ) : ℕ :=
  W * enumChildB (10 * W + ansW k + 20 * (k + 1) ^ 2 + 40) +
    mapQK * (W + 1) * (W + piecesW k W + 1) + combCost k (combInW k W) +
    cosetNFCost hm k (combOutW k W) + 6 * combInW k W + 2 * combOutW k W + 2 * ansW k + 100

/-- The child of a dispatcher step on the coset of `(toFin e).symm t`. -/
noncomputable def tailChild (S : State Ω C) (Ds : DispatchStep P₀ S) (e : Ω ≃ Fin k)
    (t : Perm (Fin k)) : State Ω C :=
  S.restrict Ds.K Ds.K_le S.x (S.y ∘ (toFin e).symm t) Ds.hier'

theorem tailChild_book (S : State Ω C) (Ds : DispatchStep P₀ S) (e : Ω ≃ Fin k)
    (t : Perm (Fin k)) : (tailChild S Ds e t).book = S.book := by
  simp only [tailChild, State.book, State.restrict_rows_of _ _ _ _ _ _ Ds.keeps,
    State.restrict_floor_of _ _ _ _ _ _ Ds.keeps, State.restrict_h_of _ _ _ _ _ _ Ds.keeps]

/-- **The tail of a dispatcher step meets its specification**: for coset representatives `ts`
of the step (as permutations of `Fin k`), the tail returns a canonical answer of the run
`Run.dispatch` of the step, at a cost of at most `tailCost` plus the cost of the children. -/
theorem tail_spec (I : Iface) (hm : Membership) {Pg : Program} {F : Funs}
    {f bm fch bg bc g comp inv app bn jm : ℕ}
    (hf : Pg.funs[f]? = some (tailF bm bc bn))
    (hbm : Pg.HasAt bm (mapFuns bm fch)) (hch : Pg.funs[fch]? = some (enumChildF F bg))
    (hga : Pg.HasAt bg (gatherFuns bg))
    (hbc : Pg.HasAt bc (foldlFuns bc g)) (hg : Pg.funs[g]? = some (combStep comp inv app))
    (hcomp : Pg.HasAt comp (composeFuns comp)) (hinv : Pg.HasAt inv (invFuns inv))
    (happ : Pg.HasAt app (appendFuns app))
    (hbn : Pg.HasAt bn (cosetNFFuns bn jm)) (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    {e : Ω ≃ Fin k} {c : C → ℕ} {gv dv xv yv hv rv fv hh : Val} {N : ℕ} {S : State Ω C}
    (hcan : Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S)
    (hs : (S.N : ℝ) ^ P₀.γ < S.size) (htr : S.Transitive) (hfl : ¬ S.FloorEntered)
    (Ds : DispatchStep P₀ S) {Kv hv' : Val}
    (hK : GroupValC k Kv (groupFin e Ds.K)) (hH : HierValC e hv' Ds.hier')
    (ts : List (Perm (Fin k))) (hlen : ts.length = Ds.n)
    (hτ : ∀ j : Fin Ds.n, Ds.τ j = (toFin e).symm (ts.getD j 1))
    (xs : List Val) (hxl : xs.length = ts.length)
    (hxs : ∀ i (hi : i < xs.length), ∃ key, xs[i] = .list [key, encPerm (ts.getD i 1)])
    (hcall : ∀ T : State Ω C, ∀ y', T.Inst Ds.K S.dom S.x y' → T.N = S.N → T.hier = Ds.hier' →
      ∀ val, Canon e c val T → FunAll Pg F.cont val (I.Post .cont T e val)) :
    FunAll Pg f (.list [.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N], Kv, hv'],
        .list xs])
      (fun u cost => ∃ (A : Set (Perm Ω)) (r : Run P₀ .cont S none A), r.kind = .dispatch ∧
        AnsC e u A ∧ (cost : ℝ) ≤ tailCost hm k (Val.list [.list [.list [.nat k, gv, dv, xv, yv,
          hv, rv, fv, hh, .nat N], Kv, hv'], .list xs]).wt + I.childCost r) := by
  set v := Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] with hvdef
  set ctx := Val.list [v, Kv, hv'] with hctx
  set a := Val.list [ctx, .list xs] with ha
  set W := a.wt with hW
  set n := xs.length with hn
  set T : ℕ → State Ω C := fun i => tailChild S Ds e (ts.getD i 1) with hT
  have hsumW := sum_wt_lt_wt_list [ctx, .list xs]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsumW
  have ea : (Val.list [ctx, .list xs]).wt = W := rfl
  have hnW : n < W := (length_lt_wt_list xs).trans (by omega)
  -- the calls on the cosets
  have hmap := mapQ_spec hbm (c := ctx) (xs := xs)
    (R := fun i w => ∃ u, w = .list [encPerm (ts.getD i 1), u] ∧ AnsC e u (T i).answer)
    (Q := fun i cb => ∃ (A : Set (Perm Ω)) (r : Run P₀ .cont (T i) none A),
      (cb : ℝ) ≤ r.total I.work)
    (B := fun _ => enumChildB (10 * W + ansW k + 20 * (k + 1) ^ 2 + 40)) (fun i hi => by
      obtain ⟨key, hkey⟩ := hxs i hi
      have hxi := wt_getElem_lt xs i hi
      rw [hkey] at hxi ⊢
      have hTi : (T i).Inst Ds.K S.dom S.x (S.y ∘ (toFin e).symm (ts.getD i 1)) :=
        ⟨rfl, rfl, rfl, rfl⟩
      refine (enumChild_spec I hch hga hcan Ds (ts.getD i 1) hTi rfl rfl
        (tailChild_book S Ds e _) hK hH (hcall _ _ hTi rfl rfl) key).mono ?_
      rintro w cost ⟨hR, cb, hQ, hcost⟩
      refine ⟨hR, cb, hQ, ?_⟩
      change cost ≤ enumChildB (5 * (Val.list [ctx, .list [key, encPerm (ts.getD i 1)]]).wt +
        ansW k + 20 * (k + 1) ^ 2 + 10) + cb at hcost
      have h2 := wt_list2_le ctx (.list [key, encPerm (ts.getD i 1)])
      exact hcost.trans (Nat.add_le_add_right (enumChildB_mono (by omega)) _))
  set Bc := enumChildB (10 * W + ansW k + 20 * (k + 1) ^ 2 + 40) with hBc
  have hcm : EvalAll Pg [a] (.call bm (.var 0)) (fun w cm => ∃ ws, w = .list ws ∧
      ws.length = n ∧ (∀ i (hi : i < ws.length), ∃ u, ws[i] = .list [encPerm (ts.getD i 1), u] ∧
        AnsC e u (T i).answer) ∧ ∃ cs : ℕ → ℕ, (∀ i, i < n → ∃ (A : Set (Perm Ω))
          (r : Run P₀ .cont (T i) none A), (cs i : ℝ) ≤ r.total I.work) ∧
        cm ≤ ∑ i ∈ Finset.range n, (Bc + cs i) + mapQK * (n + 1) * (W + w.wt + 1) + W + w.wt + 2) :=
    EvalAll.call_funAll (Det.var' (i := 0) (v := a) rfl) fun v0 ca h0 => by
      obtain ⟨rfl, hca⟩ := h0
      exact hmap.mono fun w cost hw => by
        obtain ⟨ws, rfl, hwl, hR, cs, hQ, hc⟩ := hw
        have hc' : cost ≤ ∑ i ∈ Finset.range n, (Bc + cs i) +
            mapQK * (n + 1) * (W + (Val.list ws).wt + 1) := by rw [ea] at hc; exact hc
        exact ⟨ws, rfl, hwl, hR, cs, hQ, by omega⟩
  refine FunAll.intro hf (EvalAll.letE hcm fun wsv cm hwsv => ?_)
  obtain ⟨ws, rfl, hwl, hR, cs, hQ, hcmb⟩ := hwsv
  -- the pieces
  have hpc : ∀ i : Fin ws.length, ∃ q : Acc k, ws[i] = encPiece (ts.getD i 1, q) ∧
      accSet q = toFin e '' (T i).answer := fun i => by
    obtain ⟨u, hu, hA⟩ := hR i i.2
    obtain ⟨q, rfl, hq⟩ := hA.acc
    exact ⟨q, hu, hq⟩
  choose qs hqs using hpc
  set ps : List (Perm (Fin k) × Acc k) := List.ofFn fun i : Fin ws.length => (ts.getD i 1, qs i)
    with hps
  have hws : ws = ps.map encPiece := List.ext_getElem (by simp [hps]) fun i h1 h2 => by
    simp only [hps, List.getElem_map, List.getElem_ofFn]
    exact (hqs ⟨i, h1⟩).1
  -- the run
  have hnD : n = Ds.n := hxl.trans hlen
  choose A' r' hr' using fun j : Fin Ds.n => hQ j (by omega)
  have hchild : ∀ j : Fin Ds.n, (T j).Inst Ds.K S.dom S.x (S.y ∘ Ds.τ j) := fun j => by
    rw [hτ j]; exact ⟨rfl, rfl, rfl, rfl⟩
  let r := Run.dispatch hs htr hfl Ds (fun j => T j) hchild (fun _ => rfl) (fun _ => rfl)
    (fun j => tailChild_book S Ds e _) A' r'
  -- the answer
  have hU : unionSet ps = toFin e '' ⋃ j, Ds.τ j • A' j := by
    ext g
    rw [Set.image_iUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨q, hq, hg⟩
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      refine ⟨⟨i, by omega⟩, ?_⟩
      rw [image_toFin_smul, hτ, MulEquiv.apply_symm_apply, (r' _).exact]
      have := (hqs i).2
      simp only at hg this ⊢
      rw [← this]; exact hg
    · rintro ⟨j, hg⟩
      refine ⟨(ts.getD j 1, qs ⟨j, by omega⟩), List.mem_ofFn.mpr ⟨⟨j, by omega⟩, rfl⟩, ?_⟩
      rw [image_toFin_smul, hτ, MulEquiv.apply_symm_apply, (r' _).exact] at hg
      have := (hqs ⟨j, by omega⟩).2
      simp only at hg this ⊢
      rw [this]; exact hg
  have hCE := combine_cosetOrEmpty ps (by rw [hU, r.exact]; exact image_answer_cases e S)
  -- the combination and the normal form
  have hmk := Det.mk3 (P := Pg) (env := [a, .list ws]) (Det.nat 0) (Det.var' (i := 1) rfl) Det.nil
  have hcomb := Det.call hmk (by
    rw [hws]; exact comb_spec hbc hg hcomp hinv happ (.nat 0) ps)
  refine EvalAll.call_funAll hcomb fun w0 ca h0 => ?_
  obtain ⟨rfl, hca⟩ := h0
  refine (cosetNF_spec hm hbn hjm hCE).mono fun u cb hu => ?_
  obtain ⟨hC, hcb⟩ := hu
  rw [hU] at hC
  refine ⟨_, r, rfl, CosetC.ansC hC, ?_⟩
  have hch : I.childCost r = ∑ j : Fin Ds.n, (r' j).total I.work := by
    simp only [r, Iface.childCost, Run.children, List.map_ofFn, List.sum_ofFn, Function.comp_def,
      Iface.charge, reduceCtorEq, if_false, add_zero]
  -- weights
  have hwu := (CosetC.ansC hC).wt_le
  have hpw : ∀ x ∈ ws, x.wt ≤ pieceW k := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨u', hu', hA'⟩ := hR i hi
    rw [hu']
    have := wt_list2_le (encPerm (ts.getD i 1)) u'
    have := wt_encPerm_le (ts.getD i 1)
    have := hA'.wt_le
    unfold pieceW; omega
  have hWS : (Val.list ws).wt ≤ piecesW k W := by
    have := wt_list_le_of ws hpw
    have : ws.length * (2 * pieceW k + 1) ≤ W * (2 * pieceW k + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    unfold piecesW; omega
  have hwc : (Val.list [.nat 0, .list ws, .list []]).wt ≤ combInW k W := by
    have h1 := wt_list3_le (.nat 0) (.list ws) (.list [])
    have := wt_nat_le 0
    rw [wt_list_nil] at h1
    unfold combInW; omega
  rw [← hws] at hca
  have hcc := combCost_mono k hwc
  have hL : ∀ c0 gs, combine ps = some (c0, gs) → gs.length ≤ combInW k W := by
    intro c0 gs h
    have h1 := length_combine ps c0 gs h
    have h2 := sum_accLen_le ps
    have h3 := sum_wt_lt_wt_list (ps.map encPiece)
    rw [← hws] at h2 h3
    have : (Val.list ws).wt < (Val.list [.nat 0, .list ws, .list []]).wt := wt_le_wt_list (by simp)
    omega
  have hacc : (encAcc (combine ps)).wt ≤ combOutW k W := wt_encAcc_le (combine ps) hL
  have hnf := cosetNFCost_mono hm k hacc
  have hmapb : mapQK * (n + 1) * (W + (Val.list ws).wt + 1) ≤
      mapQK * (W + 1) * (W + piecesW k W + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hsum : ∑ i ∈ Finset.range n, (Bc + cs i) = n * Bc + ∑ i ∈ Finset.range n, cs i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hnB : n * Bc ≤ W * Bc := Nat.mul_le_mul_right _ hnW.le
  have hpieces : W ≤ piecesW k W := by
    unfold piecesW
    have : W ≤ W * (2 * pieceW k + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have key : cm + (ca + cb + u.wt + 1) + u.wt + 1 ≤
      tailCost hm k W + ∑ i ∈ Finset.range n, cs i := by
    unfold tailCost
    rw [← hBc]
    have hci : combInW k W = 2 * piecesW k W + 30 := rfl
    omega
  have hcs : (∑ i ∈ Finset.range n, (cs i : ℝ)) ≤ ∑ j : Fin Ds.n, (r' j).total I.work := by
    rw [hnD, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_le_sum fun j _ => hr' j
  rw [hch]
  have := (Nat.cast_le (α := ℝ)).mpr key
  push_cast at this ⊢
  linarith

/-! ### The enumeration step -/

theorem kerNFCost_mono (hp : Preimage) (hm : Membership) (n : ℕ) {T T' : ℕ} (h : T ≤ T') :
    kerNFCost hp hm n T ≤ kerNFCost hp hm n T' := by
  unfold kerNFCost Prim.boundSize
  have h1 : (3 * T + 2) ^ (preimagePrim hp).k ≤ (3 * T' + 2) ^ (preimagePrim hp).k :=
    Nat.pow_le_pow_left (by omega) _
  have h2 := Nat.mul_le_mul_left (preimagePrim hp).c h1
  have h3 := Nat.mul_le_mul_left kerK (Nat.pow_le_pow_left h 9)
  omega

theorem genGroup_one_cons (gs : List (Perm (Fin k))) : genGroup (1 :: gs) = gens gs := by
  have : {g | g ∈ (1 :: gs)} = insert 1 {g | g ∈ gs} := by ext g; simp
  rw [genGroup, this, Subgroup.closure_insert_one]; rfl

/-- **The enumeration step.** On `[v, r, h', B]`, where `r` is the block numbering of a small
primitive quotient, `h'` the exposed hierarchy and `B` a bound on the order of the quotient
group: the coset representatives of the block kernel (`cosets`, the orbit of the block
numbering), the block kernel (`kerNF`), then the tail. -/
def enumF (bco bk bt : ℕ) : Expr :=
  .letE (.call bco (Expr.mkList [.nat 0, .get (.get (arg 0) (.nat 1)) (.nat 1), arg 1, arg 3,
      .get (arg 0) (.nat 0)]))
    (.letE (.call bk (mk2 (.get (arg 0) (.nat 1)) (arg 1)))
      (.call bt (mk2 (mk3 (arg 0) (.var 2) (arg 2)) (.var 1))))

/-- The weight bound of the list of pairs, for at most `B` pairs. -/
def pairsW (k B : ℕ) : ℕ := B * (2 * (16 * (k + 1) ^ 2 + 6) + 1) + 4

/-- The weight bound of the input of the tail. -/
def tailInW (k W B : ℕ) : ℕ := 2 * (2 * (W + groupW k) + 7 + pairsW k B) + 6

theorem tailCost_mono (hm : Membership) (k : ℕ) {W W' : ℕ} (h : W ≤ W') :
    tailCost hm k W ≤ tailCost hm k W' := by
  have hp : piecesW k W ≤ piecesW k W' := by
    unfold piecesW; have := Nat.mul_le_mul_right (2 * pieceW k + 1) h; omega
  have hc : combInW k W ≤ combInW k W' := by unfold combInW; omega
  have ho : combOutW k W ≤ combOutW k W' := by
    unfold combOutW
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (by omega)) 2)
  have h1 := Nat.mul_le_mul h (enumChildB_mono (Z := 10 * W + ansW k + 20 * (k + 1) ^ 2 + 40)
    (Z' := 10 * W' + ansW k + 20 * (k + 1) ^ 2 + 40) (by omega))
  have h2 : mapQK * (W + 1) * (W + piecesW k W + 1) ≤ mapQK * (W' + 1) * (W' + piecesW k W' + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have h3 := combCost_mono k hc
  have h4 := cosetNFCost_mono hm k ho
  unfold tailCost
  omega

/-- A list of pairs whose points are distinct and make up a set has as many entries as the set. -/
theorem length_eq_ncard {X : Type} {L : List (X × Perm (Fin k))} {O : Set X}
    (hnd : (L.map Prod.fst).Nodup) (horb : ∀ y, y ∈ L.map Prod.fst ↔ y ∈ O) :
    L.length = O.ncard := by
  classical
  have hO : O = ↑(L.map Prod.fst).toFinset := by ext y; simp [← horb y]
  rw [hO, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map]

/-- **The own cost of the enumeration step**, for an input of weight `W` and a bound `B`. -/
noncomputable def enumCost (hp : Preimage) (hm : Membership) (k W B : ℕ) : ℕ :=
  cosetsK * (W + B + 4 * (k + 1) ^ 2 + 20) ^ 6 + kerNFCost hp hm k (2 * W + 6) +
    tailCost hm k (tailInW k W B) + 20 * tailInW k W B + 200 * W + 4 * groupW k + 4 * pairsW k B +
    4 * ansW k + 1000

/-- **The enumeration step meets its specification.** On a canonical value of a transitive state
with a small primitive quotient `Q`, the block numbering `lv` of `Q`, the exposed hierarchy `hv'`
and a bound `B ≥ |ρ(G)|`, the step returns a canonical answer of the run `Run.dispatch` of the
enumeration of `Q`, at a cost of at most `enumCost` plus the cost of the children. -/
theorem enum_spec (I : Iface) (hp : Preimage) (hm : Membership) {Pg : Program} {F : Funs}
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
    (hbn : Pg.HasAt bn (cosetNFFuns bn jm)) (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    {e : Ω ≃ Fin k} {c : C → ℕ} {gv dv xv yv hv rv fv hh : Val} {N : ℕ} {S : State Ω C}
    (hcan : Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S)
    (hs : (S.N : ℝ) ^ P₀.γ < S.size) (htr : S.Transitive) (hfl : ¬ S.FloorEntered)
    (Q : PrimitiveQuotient S) (hsmall : Q.Small P₀.a)
    (hkeep : CarrierOK Q.kernel S.dom S.rows (Q.pre ++ Q.top :: Q.post))
    {lv hv' : Val} (hR : ReprVal k lv fun i j => Q.labFin e i = Q.labFin e j)
    (hH : HierValC e hv' (Q.pre ++ Q.top :: Q.post)) {B : ℕ} (hB : Nat.card Q.ρ.range ≤ B)
    (hcall : ∀ T : State Ω C, ∀ y', T.Inst Q.kernel S.dom S.x y' → T.N = S.N →
      T.hier = Q.pre ++ Q.top :: Q.post →
      ∀ val, Canon e c val T → FunAll Pg F.cont val (I.Post .cont T e val)) :
    FunAll Pg f (.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N], lv, hv', .nat B])
      (fun u cost => ∃ (A : Set (Perm Ω)) (r : Run P₀ .cont S none A), r.kind = .dispatch ∧
        AnsC e u A ∧ (cost : ℝ) ≤ enumCost hp hm k (Val.list [.list [.nat k, gv, dv, xv, yv, hv,
          rv, fv, hh, .nat N], lv, hv', .nat B]).wt B + I.childCost r) := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  obtain ⟨gv0, dv0, xv0, yv0, hv0, rv0, hgv, -, -, -, -, -, heq⟩ := hcan.val
  simp only [Val.list.injEq, List.cons.injEq] at heq
  obtain ⟨-, rfl, -, -, -, -, -, -, -, -, -⟩ := heq
  obtain ⟨gs, rfl, hgens, hgl⟩ := hgv
  have hG : genGroup (1 :: gs) = groupFin e S.G := by rw [genGroup_one_cons, hgens]
  obtain ⟨rl, rfl, hrl, hidem⟩ := hR
  set lab : Fin k → ℕ := fun i => (rl i : ℕ) with hlab
  have hfib : ∀ i j, lab i = lab j ↔ Q.labFin e i = Q.labFin e j := fun i j => by
    rw [hlab, Fin.val_inj, hrl]
  have hlab_le : ∀ i, lab i ≤ k := fun i => (rl i).isLt.le
  have hBo : (actOrbit labAct (1 :: gs) lab).ncard ≤ B := (Q.ncard_orbit_le' e hG hfib).trans hB
  set v := Val.list [.nat k, encGroup gs, dv, xv, yv, hv, rv, fv, hh, .nat N] with hvdef
  set a := Val.list [v, encFun lab, hv', .nat B] with ha
  set W := a.wt with hW
  -- weights
  have w4 := sum_wt_lt_wt_list [v, encFun lab, hv', .nat B]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at w4
  have ea : (Val.list [v, encFun lab, hv', .nat B]).wt = W := rfl
  have wg : (encGroup gs).wt < v.wt := wt_le_wt_list (by simp)
  have wk : (Val.nat k).wt < v.wt := wt_le_wt_list (by simp)
  have wgl : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
    wt_le_wt_list (vs := [.nat k, .list ((1 :: gs).map encPerm)]) (by simp)
  -- the arguments
  have dv0 : ∀ rest, Det Pg (a :: rest) (arg 0) v (2 * W + 5) := fun rest =>
    (Det.arg' (vs := [v, encFun lab, hv', .nat B]) (j := 0) rfl).mono (by omega)
  have dgv : ∀ rest, Det Pg (a :: rest) (.get (arg 0) (.nat 1)) (encGroup gs) (4 * W + 20) :=
    fun rest => (Det.get' (dv0 rest) (Det.nat 1) (show [Val.nat k, encGroup gs, dv, xv, yv, hv,
      rv, fv, hh, Val.nat N][1]? = some (encGroup gs) from rfl)).mono (by omega)
  have dgl : ∀ rest, Det Pg (a :: rest) (.get (.get (arg 0) (.nat 1)) (.nat 1))
      (.list ((1 :: gs).map encPerm)) (6 * W + 40) := fun rest =>
    (Det.get' (dgv rest) (Det.nat 1) (show [Val.nat k, Val.list ((1 :: gs).map encPerm)][1]? =
      some (.list ((1 :: gs).map encPerm)) from rfl)).mono (by omega)
  have dlab : ∀ rest, Det Pg (a :: rest) (arg 1) (encFun lab) (2 * W + 6) := fun rest =>
    (Det.arg' (vs := [v, encFun lab, hv', .nat B]) (j := 1) rfl).mono (by omega)
  have dhv : ∀ rest, Det Pg (a :: rest) (arg 2) hv' (2 * W + 7) := fun rest =>
    (Det.arg' (vs := [v, encFun lab, hv', .nat B]) (j := 2) rfl).mono (by omega)
  have dB : ∀ rest, Det Pg (a :: rest) (arg 3) (.nat B) (2 * W + 8) := fun rest =>
    (Det.arg' (vs := [v, encFun lab, hv', .nat B]) (j := 3) rfl).mono (by omega)
  have dk : ∀ rest, Det Pg (a :: rest) (.get (arg 0) (.nat 0)) (.nat k) (4 * W + 20) :=
    fun rest => (Det.get' (dv0 rest) (Det.nat 0) (show [Val.nat k, encGroup gs, dv, xv, yv, hv,
      rv, fv, hh, Val.nat N][0]? = some (.nat k) from rfl)).mono (by omega)
  have hargs : Det Pg [a] (Expr.mkList [.nat 0, .get (.get (arg 0) (.nat 1)) (.nat 1), arg 1,
      arg 3, .get (arg 0) (.nat 0)])
      (.list [.nat 0, .list ((1 :: gs).map encPerm), encFun lab, .nat B, .nat k])
      (5 * (6 * W + 40 + (Val.list [.nat 0, .list ((1 :: gs).map encPerm), encFun lab, .nat B,
        .nat k]).wt + 1) + 5) := Det.mkList (P := Pg) (env := [a]) (c := 6 * W + 40)
    [(.nat 0, .nat 0), (.get (.get (arg 0) (.nat 1)) (.nat 1), .list ((1 :: gs).map encPerm)),
      (arg 1, encFun lab), (arg 3, .nat B), (.get (arg 0) (.nat 0), .nat k)] (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact (Det.nat 0).mono (by omega)
      · exact dgl []
      · exact (dlab []).mono (by omega)
      · exact (dB []).mono (by omega)
      · exact (dk []).mono (by omega))
  have wl5 : (Val.list [.nat 0, .list ((1 :: gs).map encPerm), encFun lab, .nat B, .nat k]).wt ≤
      2 * ((Val.nat 0).wt + (Val.list ((1 :: gs).map encPerm)).wt + (encFun lab).wt +
        (Val.nat B).wt + (Val.nat k).wt) + 5 + 4 := by
    have := wt_list_le [.nat 0, .list ((1 :: gs).map encPerm), encFun lab, .nat B, .nat k]
    simpa [Nat.add_assoc] using this
  have := wt_nat_le 0
  -- the coset representatives
  have hcos : EvalAll Pg [a] (.call bco (Expr.mkList [.nat 0, .get (.get (arg 0) (.nat 1))
      (.nat 1), arg 1, arg 3, .get (arg 0) (.nat 0)])) (fun w cw =>
      ∃ L : List ((Fin k → ℕ) × Perm (Fin k)), w = encPairs labKey L ∧ (L.map Prod.fst).Nodup ∧
        (∀ y, y ∈ L.map Prod.fst ↔ y ∈ actOrbit labAct (1 :: gs) lab) ∧
        (∀ p ∈ L, p.2 ∈ genGroup (1 :: gs) ∧ labAct p.2 lab = p.1) ∧
        cw ≤ 100 * W + 300 + cosetsK * ((1 :: gs).length + B + 4 * (k + 1) ^ 2 + 20) ^ 6 +
          w.wt) :=
    EvalAll.call_funAll hargs fun v0 ca h0 => by
      obtain ⟨rfl, hca⟩ := h0
      exact (cosets_spec hco (1 :: gs) lab hlab_le hBo).mono fun w cost hw => by
        obtain ⟨L, h1, h2, h3, h4, h5⟩ := hw
        exact ⟨L, h1, h2, h3, h4, by omega⟩
  refine FunAll.intro hf (EvalAll.letE hcos fun Lv cL hL => ?_)
  obtain ⟨L, rfl, hnd, horb, hpL, hcL⟩ := hL
  -- the block kernel
  have wgr := wt_list2_le (encGroup gs) (encFun lab)
  have hker : EvalAll Pg [a, encPairs labKey L] (.call bk (mk2 (.get (arg 0) (.nat 1)) (arg 1)))
      (fun w cw => GroupValC k w (groupFin e Q.kernel) ∧
        cw ≤ 20 * W + 60 + kerNFCost hp hm k (2 * W + 6) + w.wt) :=
    EvalAll.call_funAll (Det.mk2 (dgv _) (dlab _)) fun v0 ca h0 => by
      obtain ⟨rfl, hca⟩ := h0
      exact (kerNF_kernel hp hm hbk hjp hjm Q e ⟨gs, rfl, hgens⟩ ⟨rl, rfl, hrl, hidem⟩).mono
        fun w cost hw => ⟨hw.1, by
          have h2 : cost ≤ kerNFCost hp hm k (Val.list [encGroup gs, encFun lab]).wt := hw.2
          have := kerNFCost_mono hp hm k (show (Val.list [encGroup gs, encFun lab]).wt ≤
            2 * W + 6 by omega)
          omega⟩
  refine EvalAll.letE hker fun Kv cK hK => ?_
  obtain ⟨hKv, hcK⟩ := hK
  -- the dispatcher step
  let reps := Q.cosetRepsOfPairs e hG hfib L hnd horb hpL
  let Ds : DispatchStep P₀ S := .enumeration Q inferInstance htr hsmall reps hkeep
  have hpc := Q.pairs_cosetList e hG hfib L hnd horb hpL
  have hlen : (L.map Prod.snd).length = Ds.n := by
    have := cosetList_length _ hpc.1 hpc.2.1 hpc.2.2
    simp only [List.length_map] at this ⊢
    exact this
  have hτ : ∀ j : Fin Ds.n, Ds.τ j = (toFin e).symm ((L.map Prod.snd).getD j 1) := fun j => by
    have hj : (j : ℕ) < (L.map Prod.snd).length := by rw [hlen]; exact j.2
    rw [List.getD_eq_getElem _ _ hj]
    show ((L.map Prod.snd).map (toFin e).symm)[(j : ℕ)]'_ = _
    rw [List.getElem_map]
  -- weights of the pairs and of the input of the tail
  have hLB : L.length ≤ B := by rw [length_eq_ncard hnd horb]; exact hBo
  have hpw : ∀ x ∈ L.map (encPair labKey), x.wt ≤ 16 * (k + 1) ^ 2 + 6 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have h1 := wt_list2_le (natList (labKey p.1)) (encPerm p.2)
    have h2 := wt_encPerm_le p.2
    have h3 : (natList (labKey p.1)).wt ≤ 4 * (k + 1) ^ 2 := by
      rw [natList_labKey, ← (hpL p hp).2]
      exact wt_encFun_le_sq _ fun i => hlab_le _
    show (Val.list [natList (labKey p.1), encPerm p.2]).wt ≤ _
    omega
  have hxw : (encPairs labKey L).wt ≤ pairsW k B := by
    have h1 := wt_list_le_of _ hpw
    rw [List.length_map] at h1
    have h2 := Nat.mul_le_mul_right (2 * (16 * (k + 1) ^ 2 + 6) + 1) hLB
    show (Val.list (L.map (encPair labKey))).wt ≤ _
    unfold pairsW; omega
  have hKw := hKv.wt_le
  have hctxw := wt_list3_le v Kv hv'
  have htw := wt_list2_le (.list [v, Kv, hv']) (encPairs labKey L)
  have hTin : (Val.list [.list [v, Kv, hv'], encPairs labKey L]).wt ≤ tailInW k W B := by
    unfold tailInW; omega
  have htc := tailCost_mono hm k hTin
  have hgl : (1 :: gs).length ≤ W := by
    have := length_lt_wt_list ((1 :: gs).map encPerm)
    rw [List.length_map] at this
    omega
  have hcK6 : cosetsK * ((1 :: gs).length + B + 4 * (k + 1) ^ 2 + 20) ^ 6 ≤
      cosetsK * (W + B + 4 * (k + 1) ^ 2 + 20) ^ 6 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6)
  -- the tail
  have hxs : ∀ i (hi : i < (L.map (encPair labKey)).length), ∃ key,
      (L.map (encPair labKey))[i] = .list [key, encPerm ((L.map Prod.snd).getD i 1)] := by
    intro i hi
    rw [List.length_map] at hi
    exact ⟨natList (labKey L[i].1), by simp [encPair, List.getElem?_eq_getElem hi]⟩
  refine EvalAll.call_funAll (Det.mk2 (Det.mk3 (dv0 _) (Det.var' (i := 2) rfl) (dhv _))
    (Det.var' (i := 1) rfl)) fun v0 ca h0 => ?_
  obtain ⟨rfl, hca⟩ := h0
  refine (tail_spec I hm hbt hbm hch hga hbc hg hcomp hinv happ hbn hjm hcan hs htr hfl Ds hKv hH
    (L.map Prod.snd) hlen hτ (L.map (encPair labKey)) (by simp) hxs hcall).mono ?_
  rintro u cost ⟨A, r, hk, hA, hc⟩
  refine ⟨A, r, hk, hA, ?_⟩
  have hu := hA.wt_le
  have hc' : (cost : ℝ) ≤ (tailCost hm k (Val.list [.list [v, Kv, hv'],
      encPairs labKey L]).wt : ℕ) + I.childCost r := hc
  have key : cL + (cK + (ca + u.wt + 1) + u.wt + 1) + u.wt + 1 +
      tailCost hm k (Val.list [.list [v, Kv, hv'], encPairs labKey L]).wt ≤ enumCost hp hm k W B := by
    unfold enumCost
    have : (Val.list [v, Kv, hv']).wt ≤ tailInW k W B := by unfold tailInW; omega
    omega
  have key' := (Nat.cast_le (α := ℝ)).mpr key
  push_cast at key' ⊢
  linarith

end GI.Impl
