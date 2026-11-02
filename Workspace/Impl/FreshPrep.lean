import Workspace.Impl.FreshColor

/-!
# The value of a fresh state, in `GI.Lang`

`prepF` on a state value `v` of `S` (with `N₀ < |dom|`) returns
`[encGroup gs₀, domCtx, s, v']`:

* `gs₀`: at most `k²` generators of `G` (`redFuns`, with the cited **PointwiseStab**), for the
  lift at the end of the fresh step;
* `domCtx`: the domain positions and their table, for the restriction and the lift;
* `s = |dom|`;
* `v'`: a canonical value of the fresh state `S.freshOn (freshHier G|_dom M)` (`canon_fresh`),
  with the color code `freshCode`. Its group: the restrictions of `1 :: gs₀` to the domain
  (`restrList_spec`), cut to at most `s²` generators by `redFuns` again. Its colors:
  `colorF`. Its hierarchy: `hierF`.

`prep_spec`: cost at most `prepCost (wt v + 1)`, a polynomial plus two calls of
**PointwiseStab** on inputs of weight at most `10⁶ (wt v + 1)⁶`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens PointwiseStab)

variable {Ω C : Type} {k : ℕ}

/-- The body of `prepF` on a state value `[k, gv, dv, xv, yv, hv, rv, fl, h, N]`. -/
def prepBody (red dom col hier : ℕ) : Expr :=
  .letE (.call red (mk2 (arg 0) (arg 1)))
  (.letE (.call dom (arg 2))
  (.letE (mk2 (.var 2) (.call (dom + 8) (mk2 (.var 2) (arg 0))))
  (.letE (.length (.var 2))
  (.letE (.call red (mk2 (.var 4) (mk2 (.var 4) (.call (dom + 22) (mk2 (.var 3)
    (.get (.var 1) (.nat 1)))))))
  (.letE (.call col (mk3 (arg 3) (arg 4) (.var 2)))
  (.letE (.call hier (mk2 (.var 4) (.var 5)))
  (mk4 (.var 1) (.var 3) (.var 4)
    (Expr.mkList [.var 4, .var 5, .get (.var 7) (.nat 0), .get (.var 6) (.nat 0),
      .get (.var 6) (.nat 1), .get (.var 7) (.nat 1), .nil, .nat 0, .nat 2, .var 4]))))))))

/-- Where the pieces of `prepF` sit. -/
structure PrepAt (P : Program) (f red dom col hier ap rep lo cnt ob jst : ℕ) : Prop where
  entry : P.funs[f]? = some (prepBody red dom col hier)
  redAt : P.HasAt red (redFuns red jst)
  domAt : DomAt P dom
  colAt : P.funs[col]? = some (colorBody (dom + 18) ap (dom + 9))
  apAt : P.HasAt ap (appendFuns ap)
  hierAt : P.funs[hier]? = some (hierBody rep lo cnt ob)
  repAt : P.HasAt rep (replicateFuns rep)
  loAt : P.HasAt lo (loFuns lo)
  cntAt : P.HasAt cnt (countFuns cnt)
  obAt : P.HasAt ob (orbitFuns ob)

/-- The cost of `prepF`, in `X = wt v + 1`. -/
def prepCost (pst : Prim) (X : ℕ) : ℕ :=
  10 ^ 22 * X ^ 21 + 2 * (pst.c * (10 ^ 6 * X ^ 6 + 2) ^ pst.k)

/-- **What `prepF` returns** (see the module docstring). -/
def PrepOut (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (w : Val) : Prop :=
  ∃ (gs₀ : List (Perm (Fin k))) (hs : List (Perm (Fin (domFin e S.dom).length)))
    (lab : Fin (domFin e S.dom).length → ℕ) (a : S.dom),
    gens gs₀ = groupFin e S.G ∧ gs₀.length ≤ k ^ 2 ∧
    (∀ b, Nat.card (orb S.domGroup b) ≤ Nat.card (orb S.domGroup a)) ∧
    Canon (domEquiv e S.dom) (freshCode e c S)
      (freshVal (domFin e S.dom).length (encGroup hs) (natList (cmpCodes e c S S.x))
        (natList (cmpCodes e c S S.y)) (fhierVal (encFun lab) (Nat.card (orb S.domGroup a))))
      (S.freshOn (freshHier S.domGroup (Nat.card (orb S.domGroup a)))) ∧
    w = .list [encGroup gs₀, domCtx e S.dom, .nat (domFin e S.dom).length,
      freshVal (domFin e S.dom).length (encGroup hs) (natList (cmpCodes e c S S.x))
        (natList (cmpCodes e c S S.y)) (fhierVal (encFun lab) (Nat.card (orb S.domGroup a)))] ∧
    w.wt ≤ 10 ^ 5 * (k + 1) ^ 6

/-- A call whose function meets a specification, on a known argument. -/
theorem EvalAll.call_spec {P : Program} {env : List Val} {f : ℕ} {a : Expr} {v : Val} {ca : ℕ}
    {R : Val → ℕ → Prop} (ha : Det P env a v ca) (hf : FunAll P f v R) :
    EvalAll P env (.call f a) (fun w c => ∃ cb, R w cb ∧ c ≤ ca + cb + w.wt + 1) :=
  EvalAll.call_funAll ha fun _ _ ⟨h1, h2⟩ => by
    subst h1
    exact hf.mono fun w cb hR => ⟨cb, hR, by omega⟩

/-- The restricted generators, with the identity first, form a group value. -/
theorem restr_groupVal (e : Ω ≃ Fin k) (S : State Ω C) {gs₀ : List (Perm (Fin k))}
    (hgs : gens gs₀ = groupFin e S.G) :
    GroupVal (domFin e S.dom).length (.list [.nat (domFin e S.dom).length,
      .list ((1 :: gs₀).map fun g => encPerm (restrP e S.G S.dom S.dom_inv g))])
      (groupFin (domEquiv e S.dom) S.domGroup) := by
  refine ⟨gs₀.map (restrP e S.G S.dom S.dom_inv), ?_, gens_restrP e S.G S.dom S.dom_inv hgs⟩
  simp only [encGroup, encPerms, List.map_cons, List.map_map, restrP_one]
  rfl

theorem kk_le (k : ℕ) : k * (2 * (2 * k) + 5) ≤ 9 * (k + 1) ^ 2 := by nlinarith

/-- **The value of a fresh state.** -/
theorem prep_spec (hst : PointwiseStab) {P : Program}
    {f red dom col hier ap rep lo cnt ob jst : ℕ}
    (h : PrepAt P f red dom col hier ap rep lo cnt ob jst)
    (hj : P.prims[jst]? = some (pointwiseStabPrim hst))
    (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C) (hsz : 0 < S.size) {v : Val}
    (hv : StateVal e c v S) :
    FunAll P f v (fun w cost => PrepOut e c S w ∧
      cost ≤ prepCost (pointwiseStabPrim hst) (v.wt + 1)) := by
  have hkv := StateVal.k_le_wt hv
  obtain ⟨gv, dv, xv, yv, hv0, rv, hg, hd, hx, hy, -, -, rfl⟩ := hv
  have hd' : dv = indVal e S.dom := hd
  subst hd'
  have hx' : xv = colVal e c S.x := hx
  have hy' : yv = colVal e c S.y := hy
  subst hx' hy'
  set s := (domFin e S.dom).length with hsdef
  set vs := [Val.nat k, gv, indVal e S.dom, colVal e c S.x, colVal e c S.y, hv0, rv,
    boolVal S.floor, .nat S.h, .nat S.N] with hvs
  set inp := Val.list vs with hinp
  refine FunAll.intro h.entry ?_
  have hsum := sum_wt_lt_wt_list vs
  simp only [hvs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
  have ga : ∀ rest (j : ℕ) (u : Val), vs[j]? = some u →
      Det P (inp :: rest) (arg j) u (2 * inp.wt + j + 5) := fun rest j u hu => Det.arg' hu
  -- 1. at most `k²` generators of `G`
  have r1 := red_spec hst h.redAt hj hg
  refine EvalAll.letE (EvalAll.call_spec (Det.mk2 (ga [] 0 _ rfl) (ga [] 1 _ rfl)) r1) ?_
  rintro w1 c1 ⟨cb1, ⟨gs₀, rfl, hgs₀, hl₀, hcb1⟩, hc1⟩
  -- 2. the domain positions
  have d2 := Det.call (ga [encGroup gs₀] 2 _ rfl) (domList_spec h.domAt e S.dom)
  refine EvalAll.letE d2 ?_
  rintro _ c2 ⟨rfl, hc2⟩
  set Pv := natList (domNat e S.dom) with hPv
  -- 3. the context of the restriction
  have d3 := Det.mk2 (Det.var' (P := P) (env := [inp, encGroup gs₀, Pv]) (i := 2) rfl)
    (Det.call (Det.mk2 (Det.var' (P := P) (env := [inp, encGroup gs₀, Pv]) (i := 2) rfl)
      (ga [encGroup gs₀, Pv] 0 _ rfl)) (posTab_spec h.domAt e S.dom))
  refine EvalAll.letE d3 ?_
  rintro _ c3 ⟨rfl, hc3⟩
  -- 4. `s`
  have d4 := Det.length (Det.var' (P := P) (env := [inp, encGroup gs₀, Pv, domCtx e S.dom])
    (i := 2) (v := Pv) rfl)
  simp only [hPv, natList, List.length_map, length_domNat] at d4
  refine EvalAll.letE d4 ?_
  rintro _ c4 ⟨rfl, hc4⟩
  -- 5. the group of the fresh state
  set env5 := [inp, encGroup gs₀, Pv, domCtx e S.dom, Val.nat s] with henv5
  have d5a := Det.call (Det.mk2 (Det.var' (P := P) (env := env5) (i := 3) rfl)
    (Det.get' (Det.var' (P := P) (env := env5) (i := 1) rfl) (Det.nat 1) rfl))
    (restrList_spec e S.G S.dom S.dom_inv h.domAt (hs := 1 :: gs₀) (mem_one_cons e S.G hgs₀))
  have d5 := Det.mk2 (Det.var' (P := P) (env := env5) (i := 4) rfl)
    (Det.mk2 (Det.var' (P := P) (env := env5) (i := 4) rfl) d5a)
  have r5 := red_spec hst h.redAt hj (restr_groupVal e S hgs₀)
  refine EvalAll.letE (EvalAll.call_spec d5 r5) ?_
  rintro w5 c5 ⟨cb5, ⟨hs, rfl, hgs, hls, hcb5⟩, hc5⟩
  -- 6. the colors
  set env6 := env5 ++ [encGroup hs] with henv6
  have d6 := Det.call (Det.mk3 (ga (env6.drop 1) 3 _ rfl) (ga (env6.drop 1) 4 _ rfl)
    (Det.var' (P := P) (env := env6) (i := 2) rfl)) (color_spec h.colAt h.domAt h.apAt e c S)
  refine EvalAll.letE d6 ?_
  rintro _ c6 ⟨rfl, hc6⟩
  -- 7. the hierarchy
  have hne : Nonempty S.dom := by
    have := hsz
    unfold State.size at this
    exact (Nat.card_pos_iff.1 this).1
  obtain ⟨lab, a, hlab, hlab', hmax, hhier⟩ := hier_spec h.hierAt h.repAt h.loAt h.cntAt h.obAt
    (domEquiv e S.dom) S.domGroup hne hgs hls
  set cols := Val.list [natList (cmpCodes e c S S.x), natList (cmpCodes e c S S.y)] with hcols
  set env7 := env6 ++ [cols] with henv7
  have d7 := Det.call (Det.mk2 (Det.var' (P := P) (env := env7) (i := 4) rfl)
    (Det.var' (P := P) (env := env7) (i := 5) rfl)) hhier
  refine EvalAll.letE d7 ?_
  rintro _ c7 ⟨rfl, hc7⟩
  -- 8. the result
  set M := Nat.card (orb S.domGroup a) with hMdef
  set ones := Val.list (List.replicate s (.nat 1)) with hones
  set hv' := fhierVal (encFun lab) M with hhv'
  set hout := Val.list [ones, hv'] with hhout
  set env8 := env7 ++ [hout] with henv8
  set W8 := hout.wt + cols.wt + (encGroup hs).wt + s + 2 with hW8
  have hcolsx : (natList (cmpCodes e c S S.x)).wt < cols.wt := wt_le_wt_list (by simp)
  have hcolsy : (natList (cmpCodes e c S S.y)).wt < cols.wt := wt_le_wt_list (by simp)
  have hones' : ones.wt < hout.wt := wt_le_wt_list (by simp)
  have hhv'' : hv'.wt < hout.wt := wt_le_wt_list (by simp)
  have wns := wt_nat_le s
  have e8 : ∀ (i : ℕ) (u : Val), env8[i]? = some u → u.wt ≤ W8 →
      Det P env8 (.var i) u (3 * W8 + 30) := fun i u hu hw =>
    (Det.var' hu).mono (by omega)
  have e8g : ∀ (i j : ℕ) (us : List Val) (u : Val), env8[i]? = some (.list us) → us[j]? = some u →
      (Val.list us).wt ≤ W8 → j ≤ 2 → Det P env8 (.get (.var i) (.nat j)) u (3 * W8 + 30) :=
    fun i j us u hi hj hw hj2 => (Det.get' (Det.var' hi) (Det.nat j) hj).mono (by
      obtain ⟨hjl, rfl⟩ := List.getElem?_eq_some_iff.mp hj
      have := wt_getElem_lt us j hjl
      omega)
  have hW4 : (Val.nat s).wt ≤ W8 := by rw [hW8]; omega
  have hW5 : (encGroup hs).wt ≤ W8 := by rw [hW8]; omega
  have hW7 : hout.wt ≤ W8 := by rw [hW8]; omega
  have hW6 : cols.wt ≤ W8 := by rw [hW8]; omega
  have dl := Det.mkList (P := P) (env := env8) (c := 3 * W8 + 30)
    [(.var 4, .nat s), (.var 5, encGroup hs), (.get (.var 7) (.nat 0), ones),
      (.get (.var 6) (.nat 0), natList (cmpCodes e c S S.x)),
      (.get (.var 6) (.nat 1), natList (cmpCodes e c S S.y)), (.get (.var 7) (.nat 1), hv'),
      (.nil, .list []), (.nat 0, .nat 0), (.nat 2, .nat 2), (.var 4, .nat s)] (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact e8 4 _ rfl hW4
      · exact e8 5 _ rfl hW5
      · exact e8g 7 0 [ones, hv'] _ rfl rfl hW7 (by norm_num)
      · exact e8g 6 0 _ _ rfl rfl hW6 (by norm_num)
      · exact e8g 6 1 _ _ rfl rfl hW6 (by norm_num)
      · exact e8g 7 1 [ones, hv'] _ rfl rfl hW7 (by norm_num)
      · exact Det.nil.mono (by omega)
      · exact (Det.nat 0).mono (by omega)
      · exact (Det.nat 2).mono (by omega)
      · exact e8 4 _ rfl hW4)
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at dl
  have d8 := Det.mk4 (Det.var' (P := P) (env := env8) (i := 1) rfl)
    (Det.var' (P := P) (env := env8) (i := 3) rfl) (Det.var' (P := P) (env := env8) (i := 4) rfl) dl
  refine d8.post fun c8 hc8 => ?_
  haveI : Finite S.dom := Finite.of_equiv _ (domEquiv e S.dom).symm
  have hMs : M ≤ s := by
    have := Nat.card_le_card_of_injective (fun w : orb S.domGroup a => (w : S.dom))
      Subtype.val_injective
    rw [card_dom_eq e S.dom] at this
    exact this
  have hs_k : s ≤ k := length_domFin_le
  -- weights of the result
  set X := inp.wt + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have hkX : k + 1 ≤ X := by omega
  have p12 : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX1 (by omega)
  have p34 : X ^ 3 ≤ X ^ 4 := Nat.pow_le_pow_right hX1 (by omega)
  have p46 : X ^ 4 ≤ X ^ 6 := Nat.pow_le_pow_right hX1 (by omega)
  have p69 : X ^ 6 ≤ X ^ 9 := Nat.pow_le_pow_right hX1 (by omega)
  have p915 : X ^ 9 ≤ X ^ 15 := Nat.pow_le_pow_right hX1 (by omega)
  have p1521 : X ^ 15 ≤ X ^ 21 := Nat.pow_le_pow_right hX1 (by omega)
  have k2 : (k + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hkX 2
  have k3 : (k + 1) ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left hkX 3
  have k4 : (k + 1) ^ 4 ≤ X ^ 4 := Nat.pow_le_pow_left hkX 4
  have k6 : (k + 1) ^ 6 ≤ X ^ 6 := Nat.pow_le_pow_left hkX 6
  have k9 : (k + 1) ^ 9 ≤ X ^ 9 := Nat.pow_le_pow_left hkX 9
  have s6 : (s + 1) ^ 6 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have s9 : (s + 1) ^ 9 ≤ X ^ 9 := Nat.pow_le_pow_left (by omega) 9
  have s15 : (s + 1) ^ 15 ≤ X ^ 15 := Nat.pow_le_pow_left (by omega) 15
  have s3 : (s + 1) ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have wg0 : (encGroup gs₀).wt ≤ 320 * (k + 1) ^ 6 := wt_encGroup_le_sq hl₀
  have whs : (encGroup hs).wt ≤ 320 * (s + 1) ^ 6 := wt_encGroup_le_sq hls
  have wdc := wt_domCtx_le e S.dom
  have wPv : Pv.wt ≤ 5 * (k + 1) ^ 2 := wt_domNat_le e S.dom
  have wpos := wt_posVal_le e S.dom
  have wones : ones.wt ≤ 7 * (s + 1) := wt_replicate_one_le s
  have wlab : (encFun lab).wt ≤ 4 * (s + 1) ^ 2 := wt_encFun_le_sq lab fun i => (hlab' i).le
  have wM := wt_nat_le M
  have h0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
  have h2 : (Val.nat 2).wt ≤ 4 := wt_nat_le 2
  have hnil : (Val.list []).wt ≤ 5 := by decide
  have wl4 := wt_list4_le (encFun lab) (.nat M) (.nat M) (.nat 0)
  have wl1 := wt_list1_le (Val.list [encFun lab, .nat M, .nat M, .nat 0])
  have whv : hv'.wt ≤ 2 * (Val.list [encFun lab, .nat M, .nat M, .nat 0]).wt + 5 :=
    (wt_fhierVal_le _ _).trans wl1
  have whout := wt_list2_le ones hv'
  have hcl : (codeList e c S).length ≤ 2 * k := by
    simp only [codeList, domCodes, List.length_append, List.length_map]
    have := length_domFin_le (e := e) (D := S.dom); omega
  have wcx : (natList (cmpCodes e c S S.x)).wt ≤ k * (2 * (2 * k) + 5) + 4 := by
    refine (wt_natList_le (B := 2 * k) fun y hy => ?_).trans ?_
    · obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy; exact (posOf_le _ z).trans hcl
    · simp only [cmpCodes, domCodes, List.length_map]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ length_domFin_le) _
  have wcy : (natList (cmpCodes e c S S.y)).wt ≤ k * (2 * (2 * k) + 5) + 4 := by
    refine (wt_natList_le (B := 2 * k) fun y hy => ?_).trans ?_
    · obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy; exact (posOf_le _ z).trans hcl
    · simp only [cmpCodes, domCodes, List.length_map]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ length_domFin_le) _
  have hkk : k * (2 * (2 * k) + 5) ≤ 9 * (k + 1) ^ 2 := kk_le k
  have wcols := wt_list2_le (natList (cmpCodes e c S S.x)) (natList (cmpCodes e c S S.y))
  have s2 : (s + 1) ^ 2 ≤ (k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have kk26 : (k + 1) ^ 2 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have kk16 : k + 1 ≤ (k + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have wfv := wt_list_le [Val.nat s, encGroup hs, ones, natList (cmpCodes e c S S.x),
    natList (cmpCodes e c S S.y), hv', .list [], .nat 0, .nat 2, .nat s]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wfv
  set fv := Val.list [Val.nat s, encGroup hs, ones, natList (cmpCodes e c S S.x),
    natList (cmpCodes e c S S.y), hv', .list [], .nat 0, .nat 2, .nat s] with hfv
  have wfv' : fv.wt ≤ 2000 * (k + 1) ^ 6 := by omega
  have wres := wt_list4_le (encGroup gs₀) (domCtx e S.dom) (.nat s) fv
  have wres' : (Val.list [encGroup gs₀, domCtx e S.dom, .nat s, fv]).wt ≤ 10 ^ 5 * (k + 1) ^ 6 := by
    omega
  refine ⟨⟨gs₀, hs, lab, a, hgs₀, hl₀, hmax, canon_fresh e c S hs hgs hls lab hlab hlab' M
      (Nat.card_pos_iff.2 ⟨⟨a, 1, S.domGroup.one_mem, rfl⟩, Subtype.finite⟩)
      (by unfold State.size; rw [card_dom_eq e S.dom]; exact hMs),
    rfl, wres'⟩, ?_⟩
  -- the cost
  set pst := pointwiseStabPrim hst
  have einp : (Val.list [Val.nat k, gv, indVal e S.dom, colVal e c S.x, colVal e c S.y, hv0, rv,
    boolVal S.floor, Val.nat S.h, Val.nat S.N]).wt = inp.wt := rfl
  have hgvX : gv.wt + 1 ≤ X := by omega
  have hxX : (colVal e c S.x).wt + 1 ≤ X := by omega
  have hyX : (colVal e c S.y).wt + 1 ≤ X := by omega
  have q0 := wt_list2_le (.nat k) gv
  have wnk := wt_nat_le k
  have hnil' : (Val.list []).wt ≤ 5 := by decide
  -- the two calls of PointwiseStab
  have B1 : pst.bound (.list [gv, .list []]) ≤ pst.c * (10 ^ 6 * X ^ 6 + 2) ^ pst.k := by
    refine Prim.bound_le pst ?_
    have := wt_list2_le gv (.list [])
    omega
  set R := Val.list ((1 :: gs₀).map fun g => encPerm (restrP e S.G S.dom S.dom_inv g)) with hR
  have hl1 : (1 :: gs₀).length + 1 = gs₀.length + 2 := by simp
  have hm := measure_le_of_sq hl₀
  have hm' : ((1 :: gs₀).length + 1) * (k + 1) ≤ 2 * X ^ 3 := by
    rw [hl1]; exact hm.trans (Nat.mul_le_mul_left 2 k3)
  have wR : R.wt ≤ 160 * X ^ 6 := by
    have h1 : R.wt ≤ 40 * (((1 :: gs₀).length + 1) * (k + 1)) ^ 2 :=
      wt_gensList_le (n := s) (by omega) (1 :: gs₀) (restrP e S.G S.dom S.dom_inv)
    have h2 : (((1 :: gs₀).length + 1) * (k + 1)) ^ 2 ≤ (2 * X ^ 3) ^ 2 := Nat.pow_le_pow_left hm' 2
    have h3 : (2 * X ^ 3) ^ 2 = 4 * X ^ 6 := by ring
    omega
  have wsR := wt_list2_le (.nat s) R
  have wsR2 := wt_list2_le (.nat s) (.list [.nat s, R])
  have wsR3 := wt_list2_le (.list [.nat s, R]) (.list [])
  have B2 : pst.bound (.list [.list [.nat s, R], .list []]) ≤
      pst.c * (10 ^ 6 * X ^ 6 + 2) ^ pst.k := by
    refine Prim.bound_le pst ?_
    omega
  have hrl : restrListK * (((1 :: gs₀).length + 1) * (k + 1)) ^ 7 ≤ restrListK * (128 * X ^ 21) := by
    refine Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hm' 7).trans ?_)
    rw [mul_pow, ← pow_mul]; norm_num
  -- the colors
  have wcin := wt_list3_le (colVal e c S.x) (colVal e c S.y) Pv
  have hcin : (Val.list [colVal e c S.x, colVal e c S.y, Pv]).wt + 1 ≤ 21 * X ^ 2 := by omega
  have hcol : colorK * ((Val.list [colVal e c S.x, colVal e c S.y, Pv]).wt + 1) ^ 3 ≤
      colorK * (9261 * X ^ 6) := by
    refine Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hcin 3).trans ?_)
    rw [mul_pow, ← pow_mul]; norm_num
  have ePv : natList (domNat e S.dom) = Pv := rfl
  have ePv' : (Val.list ((domNat e S.dom).map Val.nat)).wt = Pv.wt := rfl
  have hsX : (domFin e S.dom).length + 1 ≤ X := by omega
  have s9' : ((domFin e S.dom).length + 1) ^ 9 ≤ X ^ 9 := Nat.pow_le_pow_left hsX 9
  have s15' : ((domFin e S.dom).length + 1) ^ 15 ≤ X ^ 15 := Nat.pow_le_pow_left hsX 15
  -- the rest
  have q1 := wt_list2_le Pv (.nat k)
  have q2 := wt_list2_le Pv (posVal e S.dom)
  have q3 := wt_list2_le (domCtx e S.dom) (.list ((1 :: gs₀).map encPerm))
  have q4 := wt_list2_le (.nat k) (.list ((1 :: gs₀).map encPerm))
  have q5 : (Val.list ((1 :: gs₀).map encPerm)).wt ≤ 40 * (((1 :: gs₀).length + 1) * (k + 1)) ^ 2 := by
    have := wt_gensList_le (n := k) (by omega) (1 :: gs₀) id
    simpa using this
  have q5' : (((1 :: gs₀).length + 1) * (k + 1)) ^ 2 ≤ 4 * X ^ 6 := by
    have := Nat.pow_le_pow_left hm' 2
    have e2 : (2 * X ^ 3) ^ 2 = 4 * X ^ 6 := by ring
    omega
  have q6 := wt_list2_le (.nat s) (encGroup hs)
  have wsX : (Val.nat s).wt ≤ 2 * X := by omega
  have ws15 : s + 1 ≤ X := by omega
  have whs' : (encGroup hs).wt ≤ 320 * X ^ 6 := whs.trans (Nat.mul_le_mul_left _
    ((Nat.pow_le_pow_left (by omega) 6).trans (Nat.pow_le_pow_left ws15 6)))
  have wres'' : (Val.list [encGroup gs₀, domCtx e S.dom, .nat s, fv]).wt ≤ 10 ^ 5 * X ^ 6 :=
    wres'.trans (Nat.mul_le_mul_left _ k6)
  have hfvX : fv.wt ≤ 2000 * X ^ 6 := wfv'.trans (Nat.mul_le_mul_left _ k6)
  have hdcX : (domCtx e S.dom).wt ≤ 30 * X ^ 2 := wdc.trans (Nat.mul_le_mul_left _ k2)
  have hg0X : (encGroup gs₀).wt ≤ 320 * X ^ 6 := wg0.trans (Nat.mul_le_mul_left _ k6)
  have ecols : (Val.list [natList (cmpCodes e c S S.x), natList (cmpCodes e c S S.y)]).wt =
    cols.wt := rfl
  have ehout : (Val.list [ones, hv']).wt = hout.wt := rfl
  have ehv : hv'.wt ≤ (Val.list [Val.list [encFun lab, Val.nat M, Val.nat M, Val.nat 0]]).wt :=
    wt_fhierVal_le _ _
  have hcolsX : cols.wt ≤ 100 * X ^ 2 := by
    have := Nat.mul_le_mul_left 9 k2
    omega
  have houtX : hout.wt ≤ 1000 * X ^ 2 := by
    have := Nat.mul_le_mul_left 4 s2
    have := Nat.mul_le_mul_left 4 k2
    omega
  have hPvX : Pv.wt ≤ 5 * X ^ 2 := wPv.trans (Nat.mul_le_mul_left _ k2)
  have hW8' : W8 ≤ 10 ^ 5 * X ^ 6 := by omega
  have hposX : (posVal e S.dom).wt ≤ 5 * X ^ 2 := wpos.trans (Nat.mul_le_mul_left _ k2)
  have hinpX : inp.wt + 1 = X := rfl
  have hinpX' : inp.wt ≤ X := by omega
  have m2 : domListK * (k + 1) ^ 3 ≤ domListK * X ^ 3 := Nat.mul_le_mul_left _ k3
  have m3 : posTabK * (k + 1) ^ 4 ≤ posTabK * X ^ 4 := Nat.mul_le_mul_left _ k4
  have m7 : hierK * ((domFin e S.dom).length + 1) ^ 15 ≤ hierK * X ^ 15 :=
    Nat.mul_le_mul_left _ s15'
  have C1 : c1 ≤ pst.c * (10 ^ 6 * X ^ 6 + 2) ^ pst.k + 10 ^ 8 * X ^ 9 := by
    clear hc2 hc3 hc4 hc5 hc6 hc7 hc8
    omega
  have C2 : c2 ≤ domListK * X ^ 3 + 10 * X ^ 2 := by
    clear hc1 hc3 hc4 hc5 hc6 hc7 hc8
    omega
  have C3 : c3 ≤ posTabK * X ^ 4 + 100 * X ^ 2 := by
    clear hc1 hc2 hc4 hc5 hc6 hc7 hc8
    omega
  have C4 : c4 ≤ 10 * X ^ 2 := by
    clear hc1 hc2 hc3 hc5 hc6 hc7 hc8
    omega
  have C5 : c5 ≤ pst.c * (10 ^ 6 * X ^ 6 + 2) ^ pst.k + restrListK * (128 * X ^ 21) +
      10 ^ 8 * X ^ 9 := by
    clear hc1 hc2 hc3 hc4 hc6 hc7 hc8
    have eB : pst.bound (.list [.list [.nat (domFin e S.dom).length, R], .list []]) =
      pst.bound (.list [.list [.nat s, R], .list []]) := by rw [hsdef]
    have eB' : (Val.list [.nat (domFin e S.dom).length, R]).wt = (Val.list [.nat s, R]).wt := by
      rw [hsdef]
    rw [eB, eB'] at hcb5
    try simp only [← hR] at hc5
    try simp only [← hR] at hcb5
    have eS : ((domFin e S.dom).length + 1) ^ 9 = (s + 1) ^ 9 := by rw [hsdef]
    rw [eS] at hcb5
    have s9'' : (s + 1) ^ 9 ≤ X ^ 9 := by rw [← eS]; exact s9'
    clear * - hc5 hcb5 B2 wR wsR wsR2 wsR3 hrl wsX hdcX q3 q4 q5 q5' s9'' p69 p12 p23 p34 p46 wnk hkX whs'
    clear_value R pst
    omega
  have hcol' : colorK * ((Val.list [colVal e c S.x, colVal e c S.y,
      natList (domNat e S.dom)]).wt + 1) ^ 3 ≤ colorK * (9261 * X ^ 6) := hcol
  have C6 : c6 ≤ colorK * (9261 * X ^ 6) + 1000 * X ^ 2 := by
    clear hc1 hc2 hc3 hc4 hc5 hc7 hc8
    omega
  have C7 : c7 ≤ hierK * X ^ 15 + 10 ^ 4 * X ^ 6 := by
    clear hc1 hc2 hc3 hc4 hc5 hc6 hc8
    omega
  have C8 : c8 ≤ 10 ^ 7 * X ^ 6 := by
    clear hc1 hc2 hc3 hc4 hc5 hc6 hc7
    omega
  clear hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8
  unfold prepCost
  simp only [colorK, hierK, restrListK, posTabK, domListK] at C2 C3 C5 C6 C7
  omega

end GI.Impl
