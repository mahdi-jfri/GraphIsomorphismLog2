module

public import Workspace.Degree.Enum
public import Workspace.Impl.GenNormStep

@[expose] public section

/-!
# The normalization step of the degree algorithm

The text of `normChild_spec`, `normTail_spec` and `normStep_spec` of the general algorithm, with
`ChildPost` in place of `Iface.Post`. Each child is called in the mode that its transitivity
selects, and the step returns the exact answer. The preparation of the data is the one of the
general algorithm.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup encKSetTuples Preimage PointwiseStab Membership)
open scoped Pointwise

/-- Either mode of a child call. -/
theorem normModeCall_specD {Pg : Program} {F : Funs} {env : List Val}
    {Ω C : Type} {n : ℕ} {en : Ω ≃ Fin n} {S : State Ω C} {Bc : State Ω C → ℝ}
    {sv lv : Val} {b : Bool} {se le be : Expr} {cs cl cb : ℕ}
    (hs : Det Pg env se sv cs) (hl : Det Pg env le lv cl)
    (hb : Det Pg env be (boolVal b) cb)
    (hcall : FunAll Pg (F.get (normMode b)) (if b then .list [sv, lv] else sv)
      (ChildPost Bc S en)) :
    EvalAll Pg env (normModeCall F se le be) (fun u cost => ∃ c : ℕ,
      AnsC en u S.answer ∧ (c : ℝ) ≤ Bc S ∧
        cost ≤ cb + cs + cl + 5 * (sv.wt + lv.wt + 10) + c + 2 * u.wt + 2) := by
  unfold normModeCall
  refine EvalAll.ite hb (fun _ _ h => ⟨b.toNat, h.1⟩) fun y cm hy => ?_
  obtain ⟨hy, hcm⟩ := hy
  change Val.nat y = boolVal b at hy
  have hy' : y = b.toNat := Val.nat.inj hy
  subst hy'
  cases b with
  | false =>
    simp only [Bool.toNat_false, if_pos rfl]
    change FunAll Pg F.cont sv (ChildPost Bc S en) at hcall
    refine (call_childD hs hcall).mono fun u cu hu => ?_
    obtain ⟨c, hA, hc, hcu⟩ := hu
    exact ⟨c, hA, hc, by omega⟩
  | true =>
    simp only [Bool.toNat_true, Nat.one_ne_zero, if_false]
    change FunAll Pg F.giant (.list [sv, lv]) (ChildPost Bc S en) at hcall
    have h1 : EvalAll Pg env (.call F.giant (mk2 se le)) (fun u cu => ∃ cb' : ℕ,
        AnsC en u S.answer ∧ (cb' : ℝ) ≤ Bc S ∧
        cu ≤ (cs + cl + 2 * (Val.list [sv, lv]).wt + 7) + cb' + u.wt + 1) :=
      EvalAll.call_funAll (Det.mk2 hs hl) fun v ca hv => by
        obtain ⟨rfl, hca⟩ := hv
        exact hcall.mono fun u cb' ⟨hA, hc⟩ => ⟨cb', hA, hc, by omega⟩
    refine h1.mono fun u cu hu => ?_
    obtain ⟨c, hA, hc, hcu⟩ := hu
    have hw := wt_list2_le sv lv
    exact ⟨c, hA, hc, by omega⟩

set_option maxHeartbeats 2000000 in
/-- The recursive child is canonical, has `SmallInv`, and receives its exact supplied labels. -/
theorem normChild_specD {Pg : Program} {F : Funs} {f bg : ℕ}
    (hf : Pg.funs[f]? = some (normChildF F bg)) (hga : Pg.HasAt bg (gatherFuns bg))
    {Ω C : Type} [Finite Ω] {k : ℕ} {e : Ω ≃ Fin k} {cc : C → ℕ}
    {gv dv xv yv hv rv fv hh : Val} {N : ℕ} {S : State Ω C} {Bc : State Ω C → ℝ}
    (hcan : Canon e cc (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S)
    (Q : PrimitiveQuotient S) (nc : Q.NormChoice) (htr : S.Transitive)
    (hq : P₀.q₀ < (Q.normalizationOf nc).q) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
    (j : Fin (Q.normAboveOf nc htr hq hkc hkl).I.k) (t : Perm (Fin k))
    (ht : nc.τ j = (toFin e).symm t) {Kv hv' lv : Val} (b : Bool)
    (hK : GroupValC k Kv (groupFin e (Q.normGroup nc.e nc.hS)))
    (hH : HierValC e hv' (Q.pre ++ Q.top :: Q.post))
    (hcall : ∀ val, Canon e cc val ((Q.normAboveOf nc htr hq hkc hkl).child j) →
      FunAll Pg (F.get (normMode b)) (if b then .list [val, lv] else val)
        (ChildPost Bc ((Q.normAboveOf nc htr hq hkc hkl).child j) e)) :
    FunAll Pg f (.list [.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N],
        Kv, hv', lv, boolVal b], encPerm t])
      (fun w cost => (∃ u, w = .list [encPerm t, u] ∧
        AnsC e u ((Q.normAboveOf nc htr hq hkc hkl).child j).answer) ∧
        ∃ cb : ℕ, (cb : ℝ) ≤ Bc ((Q.normAboveOf nc htr hq hkc hkl).child j) ∧
        cost ≤ normChildB (5 * (Val.list [.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv,
          hh, .nat N], Kv, hv', lv, boolVal b], encPerm t]).wt + ansW k + 20 * (k + 1) ^ 2 + 10) + cb) := by
  obtain ⟨gv0, dv0, xv0, yv0, hv0, rv0, -, -, -, hyv, -, -, heq⟩ := hcan.val
  simp only [Val.list.injEq, List.cons.injEq] at heq
  obtain ⟨-, -, -, -, rfl, -, -, -, -, -, -⟩ := heq
  set v := Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] with hvdef
  set ctx := Val.list [v, Kv, hv', lv, boolVal b] with hctx
  set x := encPerm t with hx
  set a := Val.list [ctx, x] with ha
  let NN := Q.normAboveOf nc htr hq hkc hkl
  let T := NN.child j
  -- the target coloring after `t`
  set τ := (toFin e).symm t with hτ
  have htτ : toFin e τ = t := MulEquiv.apply_symm_apply _ _
  set yv' := encFun fun i => cc ((S.y ∘ τ) (e.symm i)) with hyv'
  have hyv0 : yv = .list ((List.finRange k).map fun i => Val.nat (cc (S.y (e.symm i)))) := hyv
  have hg := gather_spec hga (L := (List.finRange k).map fun i => Val.nat (cc (S.y (e.symm i))))
    (is := (List.finRange k).map fun i => (t i : ℕ)) (by simp)
  have hgy : (((List.finRange k).map fun i => (t i : ℕ)).map fun j =>
      ((List.finRange k).map fun i => Val.nat (cc (S.y (e.symm i)))).getD j (.nat 0)) =
      (List.finRange k).map fun i => Val.nat (cc ((S.y ∘ τ) (e.symm i))) := by
    rw [← htτ]; exact gather_colors e cc S.y τ
  rw [hgy] at hg
  have hy' : ColorVal e cc yv' (S.y ∘ τ) := rfl
  have hyc : ∀ b, cc ((S.y ∘ τ) b) < 2 * k := fun b => (hcan.colors (τ b)).2
  have hcanT := normCanon_child hcan Q nc htr hq hkc hkl j hK
    (by rw [ht]; exact hy') hH
  have hcallT := hcall _ hcanT
  -- weights
  have wv : v.wt < ctx.wt := wt_le_wt_list (by simp)
  have wK : Kv.wt < ctx.wt := wt_le_wt_list (by simp)
  have wH : hv'.wt < ctx.wt := wt_le_wt_list (by simp)
  have wc : ctx.wt < a.wt := wt_le_wt_list (by simp)
  have wx : x.wt < a.wt := wt_le_wt_list (by simp)
  have wt : (encPerm t).wt = x.wt := rfl
  have wlv : lv.wt < ctx.wt := wt_le_wt_list (by simp)
  have wy : yv.wt < v.wt := wt_le_wt_list (by simp)
  have wyv' : yv'.wt ≤ 4 * (2 * k + 1) ^ 2 := by
    have := wt_encFun_le (fun i => cc ((S.y ∘ τ) (e.symm i))) (B := 2 * k)
      fun i => (hyc _).le
    nlinarith
  have ea : (Val.list [ctx, x]).wt = a.wt := rfl
  have ev : (Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]).wt = v.wt := rfl
  have ec : (Val.list [v, Kv, hv', lv, boolVal b]).wt = ctx.wt := rfl
  have ex : (encPerm t).wt = x.wt := rfl
  -- the entries of the state value
  have dctx : ∀ rest, Det Pg (a :: rest) (.get (arg 0) (.nat 0)) v (3 * a.wt + 10) := fun rest =>
    (Det.get' (Det.arg' (vs := [ctx, x]) (rest := rest) (j := 0) rfl) (Det.nat 0)
      (show [v, Kv, hv', lv, boolVal b][0]? = some v from rfl)).mono (by omega)
  have dent : ∀ rest j (hj : j < 10), Det Pg (a :: rest) (ctxV j)
      [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N][j] (5 * a.wt + 30) := fun rest j hj => by
    have := wt_getElem_lt [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] j (by simpa using hj)
    exact (Det.get' (dctx rest) (Det.nat j) (List.getElem?_eq_getElem (by simpa using hj))).mono
      (by omega)
  have dt : ∀ rest, Det Pg (a :: rest) (arg 1) (encPerm t) (3 * a.wt + 10) :=
    fun rest => (Det.arg' (vs := [ctx, x]) (rest := rest) (j := 1) rfl).mono (by omega)
  -- gather
  have hgath := Det.call (Det.mk2 (dent [] 4 (by omega)) (dt [])) (by
    rw [hyv0, encPerm_eq_natList]; exact hg)
  refine FunAll.intro hf (EvalAll.letE hgath fun yw cy hyw => ?_)
  obtain ⟨rfl, hcy⟩ := hyw
  have hyw : Val.list ((List.finRange k).map fun i => Val.nat (cc ((S.y ∘ τ) (e.symm i)))) = yv' :=
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
          (show [v, Kv, hv', lv, boolVal b][1]? = some Kv from rfl)).mono (by omega)
      · exact (dent [yv'] 2 (by omega)).mono (by omega)
      · exact (dent [yv'] 3 (by omega)).mono (by omega)
      · exact (Det.var' (i := 1) rfl).mono (by nlinarith)
      · exact (Det.get' (Det.arg' (vs := [ctx, x]) (rest := [yv']) (j := 0) rfl) (Det.nat 2)
          (show [v, Kv, hv', lv, boolVal b][2]? = some hv' from rfl)).mono (by omega)
      · exact (dent [yv'] 6 (by omega)).mono (by omega)
      · exact (dent [yv'] 7 (by omega)).mono (by omega)
      · exact (dent [yv'] 8 (by omega)).mono (by omega)
      · exact (dent [yv'] 9 (by omega)).mono (by omega))
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hval
  have dl : Det Pg [a, yv'] (.get (arg 0) (.nat 3)) lv (4 * a.wt + 30) :=
    (Det.get' (Det.arg' (vs := [ctx, x]) (rest := [yv']) (j := 0) rfl) (Det.nat 3)
      (show [v, Kv, hv', lv, boolVal b][3]? = some lv from rfl)).mono (by omega)
  have db : Det Pg [a, yv'] (.get (arg 0) (.nat 4)) (boolVal b) (4 * a.wt + 30) := by
    have wb : (boolVal b).wt < ctx.wt := wt_le_wt_list (by simp)
    exact (Det.get' (Det.arg' (vs := [ctx, x]) (rest := [yv']) (j := 0) rfl) (Det.nat 4)
      (show [v, Kv, hv', lv, boolVal b][4]? = some (boolVal b) from rfl)).mono (by omega)
  have hcl := normModeCall_specD hval dl db hcallT
  refine (EvalAll.snoc_det (Det.mk1 (dt [yv'])) hcl).mono ?_
  rintro w cw ⟨u, cu, ⟨cb, hA, hcb, hcu⟩, rfl, hcw⟩
  refine ⟨⟨u, rfl, hA⟩, cb, hcb, ?_⟩
  have wu := hA.wt_le
  set Z := 5 * a.wt + ansW k + 20 * (k + 1) ^ 2 + 10 with hZ
  have hZ1 : Z + 1 ≤ (Z + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hX : (Val.list [Val.list ((List.finRange k).map fun i => Val.nat (cc (S.y (e.symm i)))),
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
  have hZ34 : (Z + 1) ^ 3 ≤ (Z + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hZ14 : Z + 1 ≤ (Z + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  unfold normChildB
  have hgK : gatherK * (Z + 1) ^ 3 ≤ 100000 * (Z + 1) ^ 3 := by simp [gatherK]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hcy
  clear hval hcl hgath hcallT hcanT hcall
  have hq := wt_list2_le yv (encPerm t)
  have hfin : cy + cw + (Val.list ([encPerm t] ++ [u])).wt + 1 ≤
      10000 * (Z + 1) + gatherK * (Z + 1) ^ 3 + cb := by omega
  omega

noncomputable def normTailCost (hm : Membership) (k W : ℕ) : ℕ :=
  W * normChildB (10 * W + ansW k + 20 * (k + 1) ^ 2 + 40) +
    mapQK * (W + 1) * (W + piecesW k W + 1) + combCost k (combInW k W) +
    cosetNFCost hm k (combOutW k W) + 6 * combInW k W + 2 * combOutW k W + 2 * ansW k + 100

set_option maxHeartbeats 3000000 in
/-- The tail returns the canonical answer of `Run.normalize`, charging each recursive call
only to that run's children. -/
theorem normTail_specD (hm : Membership) {Pg : Program} {F : Funs}
    {f bm fch bg bc g comp inv app bn jm : ℕ}
    (hf : Pg.funs[f]? = some (tailF bm bc bn))
    (hbm : Pg.HasAt bm (mapFuns bm fch)) (hch : Pg.funs[fch]? = some (normChildF F bg))
    (hga : Pg.HasAt bg (gatherFuns bg))
    (hbc : Pg.HasAt bc (foldlFuns bc g)) (hg : Pg.funs[g]? = some (combStep comp inv app))
    (hcomp : Pg.HasAt comp (composeFuns comp)) (hinv : Pg.HasAt inv (invFuns inv))
    (happ : Pg.HasAt app (appendFuns app))
    (hbn : Pg.HasAt bn (cosetNFFuns bn jm)) (hjm : Pg.prims[jm]? = some (membershipPrim hm))
    {Ω C : Type} [Finite Ω] {k : ℕ} {e : Ω ≃ Fin k} {cc : C → ℕ}
    {gv dv xv yv hv rv fv hh : Val} {sz : ℕ} {S : State Ω C} {Bc : State Ω C → ℝ}
    (hcan : Canon e cc (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz]) S)
    (htr : S.Transitive) (Q : PrimitiveQuotient S)
    (nc : Q.NormChoice) (hq : P₀.q₀ < (Q.normalizationOf nc).q)
    (hkc : Q.KillsCols) (hkl : Q.KeepsLevels) (b : Bool)
    (hmode : ∀ j, (normMode b = .cont ∧ ¬ ((Q.normAboveOf nc htr hq hkc hkl).child j).Transitive) ∨
      (normMode b = .giant ∧ ((Q.normAboveOf nc htr hq hkc hkl).child j).Transitive))
    {Kv hv' lv : Val} (hK : GroupValC k Kv (groupFin e (Q.normGroup nc.e nc.hS)))
    (hH : HierValC e hv' (Q.pre ++ Q.top :: Q.post))
    (ts : List (Perm (Fin k))) (hlen : ts.length = (Q.normAboveOf nc htr hq hkc hkl).I.k)
    (hτ : ∀ j : Fin (Q.normAboveOf nc htr hq hkc hkl).I.k, nc.τ j = (toFin e).symm (ts.getD j 1))
    (hcall : ∀ j val, Canon e cc val ((Q.normAboveOf nc htr hq hkc hkl).child j) →
      FunAll Pg (F.get (normMode b)) (if b then .list [val, lv] else val)
        (ChildPost Bc ((Q.normAboveOf nc htr hq hkc hkl).child j) e)) :
    FunAll Pg f (.list [.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz],
        Kv, hv', lv, boolVal b], .list (ts.map encPerm)])
      (fun u cost => AnsC e u S.answer ∧ (cost : ℝ) ≤ normTailCost hm k (Val.list [.list
          [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz], Kv, hv', lv, boolVal b],
          .list (ts.map encPerm)]).wt +
          ∑ j : Fin (Q.normAboveOf nc htr hq hkc hkl).I.k,
            Bc ((Q.normAboveOf nc htr hq hkc hkl).child j)) := by
  let xs := ts.map encPerm
  set v := Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz] with hvdef
  set ctx := Val.list [v, Kv, hv', lv, boolVal b] with hctx
  set a := Val.list [ctx, .list xs] with ha
  set W := a.wt with hW
  set n := xs.length with hn
  let NN := Q.normAboveOf nc htr hq hkc hkl
  have hnD : n = NN.I.k := by simpa only [n, xs, List.length_map] using hlen
  have hsumW := sum_wt_lt_wt_list [ctx, .list xs]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsumW
  have ea : (Val.list [ctx, .list xs]).wt = W := rfl
  have hnW : n < W := (length_lt_wt_list xs).trans (by omega)
  -- the calls on the cosets
  have hmap := mapQ_spec hbm (c := ctx) (xs := xs)
    (R := fun i w => ∀ hi : i < NN.I.k, ∃ u,
      w = .list [encPerm (ts.getD i 1), u] ∧ AnsC e u (NN.child ⟨i, hi⟩).answer)
    (Q := fun i cb => ∀ hi : i < NN.I.k, (cb : ℝ) ≤ Bc (NN.child ⟨i, hi⟩))
    (B := fun _ => normChildB (10 * W + ansW k + 20 * (k + 1) ^ 2 + 40)) (fun i hi => by
      have hiN : i < NN.I.k := by change i < n at hi; omega
      have hiT : i < ts.length := by simpa only [xs, List.length_map] using hi
      have hxi : xs[i] = encPerm (ts.getD i 1) := by
        simp only [xs, List.getElem_map, List.getD_eq_getElem _ _ hiT]
      have hxiW := wt_getElem_lt xs i hi
      rw [hxi] at hxiW ⊢
      refine (normChild_specD hch hga hcan Q nc htr hq hkc hkl ⟨i, hiN⟩
        (ts.getD i 1) (hτ ⟨i, hiN⟩) b hK hH (hcall ⟨i, hiN⟩)).mono ?_
      rintro w cost ⟨hR, cb, hQ, hcost⟩
      refine ⟨fun _ => hR, cb, fun _ => hQ, ?_⟩
      change cost ≤ normChildB (5 * (Val.list [ctx, encPerm (ts.getD i 1)]).wt +
        ansW k + 20 * (k + 1) ^ 2 + 10) + cb at hcost
      have h2 := wt_list2_le ctx (encPerm (ts.getD i 1))
      exact hcost.trans (Nat.add_le_add_right (normChildB_mono (by omega)) _))
  set Bo := normChildB (10 * W + ansW k + 20 * (k + 1) ^ 2 + 40) with hBo
  have hcm : EvalAll Pg [a] (.call bm (.var 0)) (fun w cm => ∃ ws, w = .list ws ∧
      ws.length = n ∧ (∀ i (hi : i < ws.length), ∀ hiN : i < NN.I.k, ∃ u,
        ws[i] = .list [encPerm (ts.getD i 1), u] ∧ AnsC e u (NN.child ⟨i, hiN⟩).answer) ∧
      ∃ cs : ℕ → ℕ, (∀ i, i < n → ∀ hiN : i < NN.I.k, (cs i : ℝ) ≤ Bc (NN.child ⟨i, hiN⟩)) ∧
        cm ≤ ∑ i ∈ Finset.range n, (Bo + cs i) + mapQK * (n + 1) * (W + w.wt + 1) + W + w.wt + 2) :=
    EvalAll.call_funAll (Det.var' (i := 0) (v := a) rfl) fun v0 ca h0 => by
      obtain ⟨rfl, hca⟩ := h0
      exact hmap.mono fun w cost hw => by
        obtain ⟨ws, rfl, hwl, hR, cs, hQ, hc⟩ := hw
        have hc' : cost ≤ ∑ i ∈ Finset.range n, (Bo + cs i) +
            mapQK * (n + 1) * (W + (Val.list ws).wt + 1) := by rw [ea] at hc; exact hc
        exact ⟨ws, rfl, hwl, hR, cs, hQ, by omega⟩
  refine FunAll.intro hf (EvalAll.letE hcm fun wsv cm hwsv => ?_)
  obtain ⟨ws, rfl, hwl, hR, cs, hQ, hcmb⟩ := hwsv
  -- the pieces
  have hpc : ∀ i : Fin ws.length, ∃ q : Acc k, ws[i] = encPiece (ts.getD i 1, q) ∧
      accSet q = toFin e '' (NN.child ⟨i, by omega⟩).answer := fun i => by
    obtain ⟨u, hu, hA⟩ := hR i i.2 (by omega)
    obtain ⟨q, rfl, hq⟩ := hA.acc
    exact ⟨q, hu, hq⟩
  choose qs hqs using hpc
  set ps : List (Perm (Fin k) × Acc k) := List.ofFn fun i : Fin ws.length => (ts.getD i 1, qs i)
    with hps
  have hws : ws = ps.map encPiece := List.ext_getElem (by simp [hps]) fun i h1 h2 => by
    simp only [hps, List.getElem_map, List.getElem_ofFn]
    exact (hqs ⟨i, h1⟩).1
  have hτNN : ∀ j : Fin NN.I.k, NN.I.τ j = (toFin e).symm (ts.getD j 1) := hτ
  -- the answer
  have hans := step_cosets NN.I.τ NN.I.τ_mem NN.I.le NN.I.cover NN.child
    (fun _ => ⟨rfl, rfl, rfl, rfl⟩) (fun j => (NN.child j).answer) (fun _ => rfl)
  have hU : unionSet ps = toFin e '' ⋃ j : Fin NN.I.k, NN.I.τ j • (NN.child j).answer := by
    ext g
    rw [Set.image_iUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨q, hq, hg⟩
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      refine ⟨⟨i, by omega⟩, ?_⟩
      rw [image_toFin_smul, hτNN, MulEquiv.apply_symm_apply]
      have := (hqs i).2
      simp only at hg this ⊢
      rw [← this]; exact hg
    · rintro ⟨j, hg⟩
      refine ⟨(ts.getD j 1, qs ⟨j, by omega⟩), List.mem_ofFn.mpr ⟨⟨j, by omega⟩, rfl⟩, ?_⟩
      rw [image_toFin_smul, hτNN, MulEquiv.apply_symm_apply] at hg
      have := (hqs ⟨j, by omega⟩).2
      simp only at hg this ⊢
      rw [this]; exact hg
  have hCE := combine_cosetOrEmpty ps (by rw [hU, hans]; exact image_answer_cases e S)
  -- the combination and the normal form
  have hmk := Det.mk3 (P := Pg) (env := [a, .list ws]) (Det.nat 0) (Det.var' (i := 1) rfl) Det.nil
  have hcomb := Det.call hmk (by
    rw [hws]; exact comb_spec hbc hg hcomp hinv happ (.nat 0) ps)
  refine EvalAll.call_funAll hcomb fun w0 ca h0 => ?_
  obtain ⟨rfl, hca⟩ := h0
  refine (cosetNF_spec hm hbn hjm hCE).mono fun u cb hu => ?_
  obtain ⟨hC, hcb⟩ := hu
  rw [hU] at hC
  rw [hans] at hC
  refine ⟨CosetC.ansC hC, ?_⟩
  -- weights
  have hwu := (CosetC.ansC hC).wt_le
  have hpw : ∀ x ∈ ws, x.wt ≤ pieceW k := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨u', hu', hA'⟩ := hR i hi (by omega)
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
  have hsum : ∑ i ∈ Finset.range n, (Bo + cs i) = n * Bo + ∑ i ∈ Finset.range n, cs i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hnB : n * Bo ≤ W * Bo := Nat.mul_le_mul_right _ hnW.le
  have hpieces : W ≤ piecesW k W := by
    unfold piecesW
    have : W ≤ W * (2 * pieceW k + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have key : cm + (ca + cb + u.wt + 1) + u.wt + 1 ≤
      normTailCost hm k W + ∑ i ∈ Finset.range n, cs i := by
    unfold normTailCost
    rw [← hBo]
    have hci : combInW k W = 2 * piecesW k W + 30 := rfl
    omega
  have hcs : (∑ i ∈ Finset.range n, (cs i : ℝ)) ≤ ∑ j : Fin NN.I.k, Bc (NN.child j) := by
    rw [hnD, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_le_sum fun j _ => hQ j (by omega) j.2
  have := (Nat.cast_le (α := ℝ)).mpr key
  push_cast at this ⊢
  linarith

attribute [local irreducible] normGrow normPrepCost in
open Classical in
set_option maxHeartbeats 2000000 in
/-- The normalization branch computes a canonical answer of `Run.normalize`. Its own work
is polynomial, and all recursive work is charged to the children actually called. -/
theorem normStep_specD (hp : Preimage) (hst : PointwiseStab) (hm : Membership)
    {Pg : Program} {F : Funs} (o : normOps Pg hp hst hm) (t : normTailAt Pg F hm)
    {f prep : ℕ} (hf : Pg.funs[f]? = some (normStepF prep t.tail))
    (hprep : Pg.funs[prep]? = some (normPrepF o))
    {Ω C : Type} [Finite Ω] {n m k sz : ℕ} (en : Ω ≃ Fin n) (cc : C → ℕ) {S : State Ω C}
    (Bg : Bool → State Ω C → ℝ) {gv dv xv yv hv rv fv hh rep hv' : Val}
    (hcan : Canon en cc (.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz]) S)
    (hne : S.dom.Nonempty) (htr : S.Transitive) (Q : PrimitiveQuotient S)
    (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e)
    (hq : P₀.q₀ < m) (hkc : Q.KillsCols) (hkl : Q.KeepsLevels)
    (hrep : normNumbered en Q rep) (hH : HierValC en hv' (Q.pre ++ Q.top :: Q.post))
    (hcall : ∀ (D : normCosetData Q e hS) (b : Bool),
      (∀ j, (normMode b = .cont ∧ ¬ ((Q.normAboveOf D.choice htr hq hkc hkl).child j).Transitive) ∨
        (normMode b = .giant ∧ ((Q.normAboveOf D.choice htr hq hkc hkl).child j).Transitive)) →
      ∀ (lv : Val), (∀ j, LabValStd en ((Q.normAboveOf D.choice htr hq hkc hkl).child j) lv
        ((Q.normAboveOf D.choice htr hq hkc hkl).childLabels j)) →
      ∀ j val, Canon en cc val ((Q.normAboveOf D.choice htr hq hkc hkl).child j) →
        FunAll Pg (F.get (normMode b)) (if b then .list [val, lv] else val)
          (ChildPost (Bg b) ((Q.normAboveOf D.choice htr hq hkc hkl).child j) en)) :
    FunAll Pg f (.list [.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz], rep, hv',
      .nat m, .nat k, encKSetTuples e]) (fun u cost =>
      AnsC en u S.answer ∧ ∃ (D : normCosetData Q e hS) (b : Bool),
        (∀ j, (normMode b = .cont ∧ ¬ ((Q.normAboveOf D.choice htr hq hkc hkl).child j).Transitive) ∨
          (normMode b = .giant ∧ ((Q.normAboveOf D.choice htr hq hkc hkl).child j).Transitive)) ∧
        (cost : ℝ) ≤ normStepCost hp hst hm n m (Val.list
          [.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz], rep, hv',
            .nat m, .nat k, encKSetTuples e]).wt +
          ∑ j : Fin (Q.normAboveOf D.choice htr hq hkc hkl).I.k,
            Bg b ((Q.normAboveOf D.choice htr hq hkc hkl).child j)) := by
  let sv := Val.list [.nat n, gv, dv, xv, yv, hv, rv, fv, hh, .nat sz]
  let input := Val.list [sv, rep, hv', .nat m, .nat k, encKSetTuples e]
  let K := normPrepCost hp hst hm n m input.wt
  have hpr := normPrep_spec hp hst hm o hprep en cc hcan Q htr hne
    e hS hq hkc hkl hrep hH
  have hpre := normBound_call (Det.var' (P := Pg) (env := [input]) (i := 0) rfl) hpr
  refine FunAll.intro hf (EvalAll.letE hpre fun pv cp hpv => ?_)
  obtain ⟨⟨D, Kv, lv, b, ts, rfl, hK, hL, hlen, hτ, hmode⟩, wp, cpr⟩ := hpv
  have hts := normTail_specD (Bc := Bg b) hm t.htail t.hmap t.hchild t.hgather t.hcombine t.hstep
    t.hcompose t.hinverse t.happend t.hnf t.hmembership hcan htr Q
    D.choice hq hkc hkl b hmode hK hH ts hlen hτ (hcall D b hmode lv hL)
  refine EvalAll.call_funAll (Det.var' (i := 1) rfl) fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine hts.mono fun u cost hu => ?_
  obtain ⟨hA, hc⟩ := hu
  refine ⟨hA, D, b, hmode, ?_⟩
  have hu := hA.wt_le
  have ht := normTailCost_mono hm n wp
  have hown : cp + (ca + u.wt + 1) + u.wt + 1 +
      normTailCost hm n (Val.list [.list [sv, Kv, hv', lv, boolVal b],
        .list (ts.map encPerm)]).wt ≤ normStepCost hp hst hm n m input.wt := by
    change _ ≤ input.wt + 4 * K + normTailCost hm n K + 10 * ansW n + 100
    change (Val.list [.list [sv, Kv, hv', lv, boolVal b], .list (ts.map encPerm)]).wt ≤ K at wp
    change ca ≤ (Val.list [.list [sv, Kv, hv', lv, boolVal b], .list (ts.map encPerm)]).wt + 1 at hca
    change normTailCost hm n (Val.list [.list [sv, Kv, hv', lv, boolVal b],
      .list (ts.map encPerm)]).wt ≤ normTailCost hm n K at ht
    change cp ≤ input.wt + 1 + 2 * K + 1 at cpr
    omega
  have hown' := (Nat.cast_le (α := ℝ)).mpr hown
  push_cast at hown' ⊢
  linarith

end GI.Degree
