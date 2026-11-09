module

public import Workspace.Impl.GenEnum

@[expose] public section

/-!
# The enumeration step of the degree algorithm

The text of `Workspace/Impl/GenEnum.lean`, with three changes. A child call meets `ChildPost`, the
exact answer at a cost of at most `Bc T`, in place of `Iface.Post`. The step works from `StepData`,
so it does not ask that the quotient passes the small test of the general algorithm. The result of a
step is the exact answer, and no `Run` is built.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens Membership Preimage)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-- What a child call returns: the exact answer, at a cost of at most `Bc T`. -/
def ChildPost (Bc : State Ω C → ℝ) (T : State Ω C) (e : Ω ≃ Fin k) : Val → ℕ → Prop :=
  fun u cost => AnsC e u T.answer ∧ (cost : ℝ) ≤ Bc T

theorem call_childD {Bc : State Ω C → ℝ} {Pg : Program} {F : Funs} {env : List Val} {a : Expr}
    {val : Val} {cArg : ℕ} {T : State Ω C} {e : Ω ≃ Fin k} (ha : Det Pg env a val cArg)
    (hcall : FunAll Pg F.cont val (ChildPost Bc T e)) :
    EvalAll Pg env (.call F.cont a) (fun u cu => ∃ cb : ℕ, AnsC e u T.answer ∧ (cb : ℝ) ≤ Bc T ∧
      cu ≤ cArg + cb + u.wt + 1) :=
  EvalAll.call_funAll ha fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    exact hcall.mono fun u cb ⟨hA, hcb⟩ => ⟨cb, hA, hcb, by omega⟩

/-- The data of a step on cosets of a subgroup: the subgroup, the coset representatives, and the
hierarchy of the children. -/
structure StepData (S : State Ω C) where
  K : Subgroup (Perm Ω)
  K_le : K ≤ S.G
  n : ℕ
  τ : Fin n → Perm Ω
  τ_mem : ∀ j, τ j ∈ S.G
  cover : (S.G : Set (Perm Ω)) ⊆ ⋃ j, τ j • (K : Set (Perm Ω))
  hier' : List (Interval Ω)
  keeps : CarrierOK K S.dom S.rows hier'
  intervals : ∀ {N : ℕ}, IntervalsOK N S.hier → IntervalsOK N hier'
  rho_le : rhoNat hier' ≤ rhoNat S.hier

/-- The data of a step of the general algorithm. -/
noncomputable def _root_.GI.Algorithm.DispatchStep.toData {P : Params} {S : State Ω C}
    (I : DispatchStep P S) : StepData S :=
  ⟨I.K, I.K_le, I.n, I.τ, I.τ_mem, I.cover, I.hier', I.keeps, I.intervalsOK, I.rhoNat_le⟩

/-- **A child of a step has a canonical value**: the input with the kernel's group value, the
recolored target and the new hierarchy. As `canon_dispChild` of the general algorithm. -/
theorem canon_stepChild {e : Ω ≃ Fin k} {c : C → ℕ}
    {gv dv xv yv hv rv fv hh : Val} {N : ℕ} {S : State Ω C}
    (hcan : Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S)
    (I : StepData S) {T : State Ω C} {y' : Ω → C} (hT : T.Inst I.K S.dom S.x y')
    (hN : T.N = S.N) (hh' : T.hier = I.hier') (hbk : T.book = S.book)
    {gv' yv' hv' : Val} (hg : GroupValC k gv' (groupFin e I.K)) (hy : ColorVal e c yv' y')
    (hyc : ∀ a, c (y' a) < 2 * k) (hhv : HierValC e hv' I.hier') :
    Canon e c (dispChildVal k gv' dv xv yv' hv' rv fv hh N) T := by
  obtain ⟨gv0, dv0, xv0, yv0, hv0, rv0, -, hd, hx, -, -, hr, heq⟩ := hcan.val
  simp only [Val.list.injEq, List.cons.injEq] at heq
  obtain ⟨-, -, rfl, rfl, -, -, rfl, rfl, rfl, hNe, -⟩ := heq
  obtain ⟨hG, hD, hX, hY⟩ := hT
  have hrows : T.rows = S.rows := congrArg Prod.fst hbk
  have hfl : T.floor = S.floor := congrArg (fun b => b.2.1) hbk
  have hhT : T.h = S.h := congrArg (fun b => b.2.2) hbk
  refine ⟨⟨gv', dv, xv, yv', hv', rv, hG ▸ hg, hD ▸ hd, hX ▸ hx, hY ▸ hy, hh' ▸ hhv,
    hrows ▸ hr, ?_⟩, fun a => ⟨hX ▸ (hcan.colors a).1, hY ▸ hyc a⟩, ?_, ?_⟩
  · simp only [dispChildVal, hfl, hhT, hN, hNe]
  · rw [hN]; exact hcan.fits
  · have h := hcan.small
    refine h.of_rho_le hN ?_ (by rw [hh']; exact I.rho_le) ?_
    · rw [hh', hN]; exact I.intervals h.1
    · rw [hrows, hN]; exact h.2.2

/-- **The call on one coset meets its specification.** -/
theorem enumChild_spec (Bc : State Ω C → ℝ) {Pg : Program} {F : Funs} {f bg : ℕ}
    (hf : Pg.funs[f]? = some (enumChildF F bg)) (hga : Pg.HasAt bg (gatherFuns bg))
    {e : Ω ≃ Fin k} {c : C → ℕ} {gv dv xv yv hv rv fv hh : Val} {N : ℕ} {S : State Ω C}
    (hcan : Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S)
    (Ds : StepData S) (t : Perm (Fin k)) {T : State Ω C}
    (hT : T.Inst Ds.K S.dom S.x (S.y ∘ (toFin e).symm t)) (hN : T.N = S.N)
    (hh' : T.hier = Ds.hier') (hbk : T.book = S.book) {Kv hv' : Val}
    (hK : GroupValC k Kv (groupFin e Ds.K)) (hH : HierValC e hv' Ds.hier')
    (hcall : ∀ val, Canon e c val T → FunAll Pg F.cont val (ChildPost Bc T e)) (key : Val) :
    FunAll Pg f (.list [.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N], Kv, hv'],
        .list [key, encPerm t]])
      (fun w cost => (∃ u, w = .list [encPerm t, u] ∧ AnsC e u T.answer) ∧
        ∃ cb : ℕ, (cb : ℝ) ≤ Bc T ∧
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
  have hcanT := canon_stepChild (k := k) hcan Ds hT hN hh' hbk hK hy' hyc hH
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
  have hcl := call_childD hval hcallT
  refine (EvalAll.snoc_det (Det.mk1 (dt [yv'])) hcl).mono ?_
  rintro w cw ⟨u, cu, ⟨cb, hA, hcb, hcu⟩, rfl, hcw⟩
  refine ⟨⟨u, rfl, hA⟩, cb, hcb, ?_⟩
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

/-- The child of a dispatcher step on the coset of `(toFin e).symm t`. -/
noncomputable def tailChild (S : State Ω C) (Ds : StepData S) (e : Ω ≃ Fin k)
    (t : Perm (Fin k)) : State Ω C :=
  S.restrict Ds.K Ds.K_le S.x (S.y ∘ (toFin e).symm t) Ds.hier'

theorem tailChild_book (S : State Ω C) (Ds : StepData S) (e : Ω ≃ Fin k)
    (t : Perm (Fin k)) : (tailChild S Ds e t).book = S.book := by
  simp only [tailChild, State.book, State.restrict_rows_of _ _ _ _ _ _ Ds.keeps,
    State.restrict_floor_of _ _ _ _ _ _ Ds.keeps, State.restrict_h_of _ _ _ _ _ _ Ds.keeps]

/-- **The tail of a dispatcher step meets its specification**: for coset representatives `ts`
of the step (as permutations of `Fin k`), the tail returns a canonical answer of the run
`Run.dispatch` of the step, at a cost of at most `tailCost` plus the cost of the children. -/
theorem tail_spec (Bc : State Ω C → ℝ) (hm : Membership) {Pg : Program} {F : Funs}
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
    (Ds : StepData S) {Kv hv' : Val}
    (hK : GroupValC k Kv (groupFin e Ds.K)) (hH : HierValC e hv' Ds.hier')
    (ts : List (Perm (Fin k))) (hlen : ts.length = Ds.n)
    (hτ : ∀ j : Fin Ds.n, Ds.τ j = (toFin e).symm (ts.getD j 1))
    (xs : List Val) (hxl : xs.length = ts.length)
    (hxs : ∀ i (hi : i < xs.length), ∃ key, xs[i] = .list [key, encPerm (ts.getD i 1)])
    (hcall : ∀ (t : Perm (Fin k)) (val : Val), Canon e c val (tailChild S Ds e t) →
      FunAll Pg F.cont val (ChildPost Bc (tailChild S Ds e t) e)) :
    FunAll Pg f (.list [.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N], Kv, hv'],
        .list xs])
      (fun u cost => AnsC e u S.answer ∧ (cost : ℝ) ≤ tailCost hm k (Val.list [.list [.list [.nat k,
          gv, dv, xv, yv, hv, rv, fv, hh, .nat N], Kv, hv'], .list xs]).wt +
          ∑ i ∈ Finset.range Ds.n, Bc (tailChild S Ds e (ts.getD i 1))) := by
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
    (Q := fun i cb => (cb : ℝ) ≤ Bc (T i))
    (B := fun _ => enumChildB (10 * W + ansW k + 20 * (k + 1) ^ 2 + 40)) (fun i hi => by
      obtain ⟨key, hkey⟩ := hxs i hi
      have hxi := wt_getElem_lt xs i hi
      rw [hkey] at hxi ⊢
      have hTi : (T i).Inst Ds.K S.dom S.x (S.y ∘ (toFin e).symm (ts.getD i 1)) :=
        ⟨rfl, rfl, rfl, rfl⟩
      refine (enumChild_spec Bc hch hga hcan Ds (ts.getD i 1) hTi rfl rfl
        (tailChild_book S Ds e _) hK hH (hcall _) key).mono ?_
      rintro w cost ⟨hR, cb, hQ, hcost⟩
      refine ⟨hR, cb, hQ, ?_⟩
      change cost ≤ enumChildB (5 * (Val.list [ctx, .list [key, encPerm (ts.getD i 1)]]).wt +
        ansW k + 20 * (k + 1) ^ 2 + 10) + cb at hcost
      have h2 := wt_list2_le ctx (.list [key, encPerm (ts.getD i 1)])
      exact hcost.trans (Nat.add_le_add_right (enumChildB_mono (by omega)) _))
  set Bo := enumChildB (10 * W + ansW k + 20 * (k + 1) ^ 2 + 40) with hBo
  have hcm : EvalAll Pg [a] (.call bm (.var 0)) (fun w cm => ∃ ws, w = .list ws ∧
      ws.length = n ∧ (∀ i (hi : i < ws.length), ∃ u, ws[i] = .list [encPerm (ts.getD i 1), u] ∧
        AnsC e u (T i).answer) ∧ ∃ cs : ℕ → ℕ, (∀ i, i < n → (cs i : ℝ) ≤ Bc (T i)) ∧
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
  -- the answer of each child
  have hnD : n = Ds.n := hxl.trans hlen
  have hchild : ∀ j : Fin Ds.n, (T j).Inst Ds.K S.dom S.x (S.y ∘ Ds.τ j) := fun j => by
    rw [hτ j]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hans := step_cosets Ds.τ Ds.τ_mem Ds.K_le Ds.cover (fun j : Fin Ds.n => T j) hchild
    (fun j => (T j).answer) (fun _ => rfl)
  have hU : unionSet ps = toFin e '' ⋃ j : Fin Ds.n, Ds.τ j • (T j).answer := by
    ext g
    rw [Set.image_iUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨q, hq, hg⟩
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      refine ⟨⟨i, by omega⟩, ?_⟩
      rw [image_toFin_smul, hτ, MulEquiv.apply_symm_apply]
      have := (hqs i).2
      simp only at hg this ⊢
      rw [← this]; exact hg
    · rintro ⟨j, hg⟩
      refine ⟨(ts.getD j 1, qs ⟨j, by omega⟩), List.mem_ofFn.mpr ⟨⟨j, by omega⟩, rfl⟩, ?_⟩
      rw [image_toFin_smul, hτ, MulEquiv.apply_symm_apply] at hg
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
  have hsum : ∑ i ∈ Finset.range n, (Bo + cs i) = n * Bo + ∑ i ∈ Finset.range n, cs i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hnB : n * Bo ≤ W * Bo := Nat.mul_le_mul_right _ hnW.le
  have hpieces : W ≤ piecesW k W := by
    unfold piecesW
    have : W ≤ W * (2 * pieceW k + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have key : cm + (ca + cb + u.wt + 1) + u.wt + 1 ≤
      tailCost hm k W + ∑ i ∈ Finset.range n, cs i := by
    unfold tailCost
    rw [← hBo]
    have hci : combInW k W = 2 * piecesW k W + 30 := rfl
    omega
  have hcs : (∑ i ∈ Finset.range n, (cs i : ℝ)) ≤
      ∑ i ∈ Finset.range Ds.n, Bc (tailChild S Ds e (ts.getD i 1)) := by
    rw [hnD]
    exact Finset.sum_le_sum fun i hi => hQ i (by rw [hnD]; exact Finset.mem_range.1 hi)
  have := (Nat.cast_le (α := ℝ)).mpr key
  push_cast at this ⊢
  linarith

/-! ### The enumeration step -/

theorem sum_range_getD : ∀ (ts : List (Perm (Fin k))) (f : Perm (Fin k) → ℝ),
    ∑ i ∈ Finset.range ts.length, f (ts.getD i 1) = (ts.map f).sum
  | [], _ => by simp
  | t :: ts, f => by
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
    rw [sum_range_getD ts f, add_comm]

theorem rhoNat_le_ofQ {S : State Ω C} (Q : PrimitiveQuotient S) :
    rhoNat (Q.pre ++ Q.top :: Q.post) ≤ rhoNat S.hier := by
  have h : (rhoNat (Q.pre ++ Q.top :: Q.post) : ℝ) ≤ rhoNat S.hier := by
    rw [rhoNat_cast, rhoNat_cast]
    exact Q.rho_le
  exact_mod_cast h

/-- The data of an enumeration: the block kernel with its cosets, and the exposed hierarchy. -/
noncomputable def _root_.GI.Algorithm.PrimitiveQuotient.enumData {S : State Ω C}
    (Q : PrimitiveQuotient S) (reps : CosetReps S.G Q.kernel)
    (hkeep : CarrierOK Q.kernel S.dom S.rows (Q.pre ++ Q.top :: Q.post)) : StepData S :=
  ⟨Q.kernel, Q.kernel_le, _, reps.τ, reps.mem, reps.cover, _, hkeep, Q.intervalsOK, rhoNat_le_ofQ Q⟩

/-- The child of an enumeration on the coset of `(toFin e).symm t`. -/
noncomputable def enumChild (S : State Ω C) (Q : PrimitiveQuotient S) (e : Ω ≃ Fin k)
    (t : Perm (Fin k)) : State Ω C :=
  S.restrict Q.kernel Q.kernel_le S.x (S.y ∘ (toFin e).symm t) (Q.pre ++ Q.top :: Q.post)

/-- **The enumeration step meets its specification.** On a canonical value of a transitive state
with a small primitive quotient `Q`, the block numbering `lv` of `Q`, the exposed hierarchy `hv'`
and a bound `B ≥ |ρ(G)|`, the step returns a canonical answer of the run `Run.dispatch` of the
enumeration of `Q`, at a cost of at most `enumCost` plus the cost of the children. -/
theorem enum_spec (Bc : State Ω C → ℝ) (hp : Preimage) (hm : Membership) {Pg : Program} {F : Funs}
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
    (Q : PrimitiveQuotient S)
    (hkeep : CarrierOK Q.kernel S.dom S.rows (Q.pre ++ Q.top :: Q.post))
    {lv hv' : Val} (hR : ReprVal k lv fun i j => Q.labFin e i = Q.labFin e j)
    (hH : HierValC e hv' (Q.pre ++ Q.top :: Q.post)) {B : ℕ} (hB : Nat.card Q.ρ.range ≤ B)
    (hcall : ∀ (t : Perm (Fin k)) (val : Val), Canon e c val (enumChild S Q e t) →
      FunAll Pg F.cont val (ChildPost Bc (enumChild S Q e t) e)) :
    FunAll Pg f (.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N], lv, hv', .nat B])
      (fun u cost => AnsC e u S.answer ∧ ∃ L : List (Perm (Fin k)), L.length ≤ B ∧
        (cost : ℝ) ≤ enumCost hp hm k (Val.list [.list [.nat k, gv, dv, xv, yv, hv,
          rv, fv, hh, .nat N], lv, hv', .nat B]).wt B +
          (L.map fun t => Bc (enumChild S Q e t)).sum) := by
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
  let Ds : StepData S := Q.enumData reps hkeep
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
  have hpw : ∀ x ∈ L.map (Lang.encPair labKey), x.wt ≤ 16 * (k + 1) ^ 2 + 6 := by
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
    show (Val.list (L.map (Lang.encPair labKey))).wt ≤ _
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
  have hxs : ∀ i (hi : i < (L.map (Lang.encPair labKey)).length), ∃ key,
      (L.map (Lang.encPair labKey))[i] = .list [key, encPerm ((L.map Prod.snd).getD i 1)] := by
    intro i hi
    rw [List.length_map] at hi
    exact ⟨natList (labKey L[i].1), by simp [Lang.encPair, List.getElem?_eq_getElem hi]⟩
  refine EvalAll.call_funAll (Det.mk2 (Det.mk3 (dv0 _) (Det.var' (i := 2) rfl) (dhv _))
    (Det.var' (i := 1) rfl)) fun v0 ca h0 => ?_
  obtain ⟨rfl, hca⟩ := h0
  refine (tail_spec Bc hm hbt hbm hch hga hbc hg hcomp hinv happ hbn hjm hcan Ds hKv hH
    (L.map Prod.snd) hlen hτ (L.map (Lang.encPair labKey)) (by simp) hxs hcall).mono ?_
  rintro u cost ⟨hA, hc⟩
  refine ⟨hA, L.map Prod.snd, ?_⟩
  have hu := hA.wt_le
  have hc' : (cost : ℝ) ≤ (tailCost hm k (Val.list [.list [v, Kv, hv'],
      encPairs labKey L]).wt : ℕ) +
          ∑ i ∈ Finset.range Ds.n, Bc (tailChild S Ds e ((L.map Prod.snd).getD i 1)) := hc
  have key : cL + (cK + (ca + u.wt + 1) + u.wt + 1) + u.wt + 1 +
      tailCost hm k (Val.list [.list [v, Kv, hv'], encPairs labKey L]).wt ≤ enumCost hp hm k W B := by
    unfold enumCost
    have : (Val.list [v, Kv, hv']).wt ≤ tailInW k W B := by unfold tailInW; omega
    omega
  refine ⟨by simpa using hLB, ?_⟩
  have hsum : ∑ i ∈ Finset.range Ds.n, Bc (tailChild S Ds e ((L.map Prod.snd).getD i 1)) =
      ((L.map Prod.snd).map fun t => Bc (enumChild S Q e t)).sum := by
    rw [← hlen]
    exact sum_range_getD _ fun t => Bc (enumChild S Q e t)
  rw [hsum] at hc'
  have key' := (Nat.cast_le (α := ℝ)).mpr key
  push_cast at key' ⊢
  linarith

end GI.Degree
