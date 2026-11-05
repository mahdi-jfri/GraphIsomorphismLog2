module

public import Workspace.Impl.GenSpecCost
public import Workspace.Impl.Cases

@[expose] public section

/-!
# The general dispatcher: the outer step

Algorithm 5, `Continue` above the threshold, transitive and off the floor. The general step on
the canonical value `v` of the state

1. exposes a primitive quotient `Q` (`expose_spec`): `x = [ρ(G), blocks, hierarchy, labels, t]`;
2. computes `B = |ρ(G)|` with the cited **GroupOrder**;
3. decides the case on `[d, ρ(G)]` (`case_spec`): `w = [0]` (small) or a Maróti structure;
4. runs the branch on `[v, x, w, B]` (`branch_spec`): enumeration, product step or normalization.

The parts enter as the predicates `ExposeAt`, `CaseAt` and `BranchAt`, the conclusions of their
specifications at a function index (`exposeAt_of`, `caseAt_of`, `branchAt_of`).

`gs_general_spec`: the step meets `Iface.GeneralSpec` for every interface whose work at a
dispatcher or normalization node is at least `gsOwn k (stateW k S)` (`GenSpecCost.lean`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encGroup gens GroupOrder CameronRecognition MinimalBlocks Preimage Membership)

/-- The exposure at the function `f`: the conclusion of `expose_spec`. -/
def ExposeAt (hmb : MinimalBlocks) (Pg : Program) (f : ℕ) : Prop :=
  ∀ {Ω C : Type} [Finite Ω] {k : ℕ} {S : State Ω C} {e : Ω ≃ Fin k}, S.Transitive → S.HierInv →
    ¬ UnivOn S.dom ⊥ → ∀ {gs : List (Perm (Fin k))}, gens gs = groupFin e S.G →
    gs.length ≤ k ^ 2 → ∀ {vs : List Val}, HierValC e (.list vs) S.hier → ∀ {rv : Val},
    OptVal (RowValC e) rv S.rows → ∀ (xv yv fv hh nN : Val),
    FunAll Pg f (.list [.nat k, encGroup gs, encFun (indF e S.dom), xv, yv, .list vs, rv, fv, hh,
      nN]) (fun w c => ∃ Q : PrimitiveQuotient S, Q.KillsCols ∧ Q.KeepsLevels ∧ ExposeOut e Q w ∧
        c ≤ gsX hmb (Val.list [.nat k, encGroup gs, encFun (indF e S.dom), xv, yv, .list vs, rv,
          fv, hh, nN]).wt)

theorem exposeAt_of (hmb : MinimalBlocks) {P : Program}
    {f bprep jmb bgather bcls bact bhier bsplit brange bbase : ℕ}
    (hf : P.funs[f]? = some (exposeE bprep jmb bgather bcls bact bhier))
    (hprep : P.funs[bprep]? = some (prepE bsplit brange bcls bbase bact))
    (hsplit : P.HasAt bsplit (hsplitFuns bsplit bcls)) (hrange : P.HasAt brange (rangeFuns brange))
    (hcls : P.HasAt bcls (clsFuns bcls)) (hbase : P.HasAt bbase (baseFuns bbase))
    (hact : P.HasAt bact (actFuns bact)) (hgather : P.HasAt bgather (gatherFuns bgather))
    (hhier : P.HasAt bhier (hierFuns bhier)) (hj : P.prims[jmb]? = some (minimalBlocksPrim hmb)) :
    ExposeAt hmb P f :=
  fun htr hinv h2 _ hgs hgsl _ hH _ hrv xv yv fv hh nN =>
    expose_spec hmb hf hprep hsplit hrange hcls hbase hact hgather hhier hj htr hinv h2 hgs hgsl
      hH hrv xv yv fv hh nN

/-- The case decision at the function `f`: the conclusion of `case_spec`. -/
def CaseAt (hO : GroupOrder) (hC : CameronRecognition) (Pg : Program) (f : ℕ) : Prop :=
  ∀ {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S) {gv : Val},
    GroupVal Q.d gv Q.ρ.range →
    FunAll Pg f (.list [.nat Q.d, gv]) (fun w c => CaseOut Q w ∧
      c ≤ caseCost hO hC gv Q.d + 10 * w.wt)

theorem caseAt_of (hO : GroupOrder) (hC : CameronRecognition) {P : Program} {f sz jo jc : ℕ}
    (hf : P.funs[f]? = some (caseBody sz jo jc)) (hsz : P.HasAt sz (smallZFuns sz 24953))
    (hjo : P.prims[jo]? = some (groupOrderPrim hO))
    (hjc : P.prims[jc]? = some (cameronRecognitionPrim hC)) : CaseAt hO hC P f :=
  fun Q _ hgv => case_spec hO hC hf hsz hjo hjc Q hgv

/-- The branch at the function `f`: the conclusion of `branch_spec`. -/
def BranchAt (I : Iface) (hp : Preimage) (hm : Membership) (Cn : ℕ → ℕ → ℕ) (Pg : Program)
    (F : Funs) (f : ℕ) : Prop :=
  ∀ {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ}, Function.Injective c →
    ∀ {gv dv xv yv hv rv fv hh : Val} {N : ℕ} {S : State Ω C},
    Canon e c (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]) S → Good P₀ .cont S →
    (S.N : ℝ) ^ P₀.γ < S.size → S.Transitive → ¬ S.FloorEntered → I.IH Pg F .cont S →
    ∀ (Q : PrimitiveQuotient S), Q.KillsCols → Q.KeepsLevels →
    ∀ {x w : Val}, ExposeOut e Q x → CaseOut Q w → ∀ {B : ℕ}, Nat.card Q.ρ.range ≤ B →
    FunAll Pg f (.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N], x, w, .nat B])
      (fun u cost => ∃ (A : Set (Perm Ω)) (rn : Run P₀ .cont S none A),
        rn.kind ∈ [CallKind.dispatch, CallKind.normalize] ∧ AnsC e u A ∧
        (cost : ℝ) ≤ brCost hp hm Cn k (Val.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh,
          .nat N], x, w, .nat B]).wt B (caseR w) + I.childCost rn)

theorem branchAt_of (I : Iface) (hp : Preimage) (hm : Membership) {Pg : Program} {F : Funs}
    {f fen fpr fno : ℕ} (hf : Pg.funs[f]? = some (branchE fen fpr fno))
    (hen : EnumAt I hp hm Pg F fen) (hpr : ProdAt I hp hm Pg F fpr)
    {Cn : ℕ → ℕ → ℕ} (hno : NormSpec I Pg F fno Cn)
    (hCn : ∀ {k W W' : ℕ}, W ≤ W' → Cn k W ≤ Cn k W') : BranchAt I hp hm Cn Pg F f :=
  fun hc _ _ _ _ _ _ _ _ _ _ hcan hgood hs htr hfl hIH Q hkc hkl _ _ hx hw _ hB =>
    branch_spec I hp hm hf hen hpr hno hCn hc hcan hgood hs htr hfl hIH Q hkc hkl hx hw hB

/-- **The general step** on the state value `v`, in the environments `[v]`, `[v, x]`,
`[v, x, B]`, `[v, x, B, w]`. -/
def gsGenE (fexp jo fcase fbr : ℕ) : Expr :=
  .letE (.call fexp (.var 0))
  (.letE (.prim jo (.get (.var 1) (.nat 0)))
  (.letE (.call fcase (mk2 (.get (.get (.var 1) (.nat 0)) (.nat 0)) (.get (.var 1) (.nat 0))))
  (.call fbr (mk4 (.var 0) (.var 1) (.var 3) (.var 2)))))

variable {Ω C : Type} {S : State Ω C}

/-- What `caseR` of a case output gives: the order bound when it is `0` (the small case), the
factorial bound otherwise (a Maróti structure with `r ≥ 1` coordinates). -/
theorem gs_caseR_bounds (Q : PrimitiveQuotient S) {k : ℕ} (hd : Q.d ≤ k) {w : Val}
    (hw : CaseOut Q w) :
    (caseR w = 0 → Nat.card Q.ρ.range ≤ gsBk k) ∧
      (caseR w ≠ 0 → (caseR w).factorial ≤ gsBk k) := by
  rcases hw with ⟨rfl, hs⟩ | ⟨m, l, r, E, rfl, -, -, -⟩
  · exact ⟨fun _ => gs_card_le_Bk Q hd hs, fun h => absurd rfl h⟩
  · exact ⟨fun h => absurd h (by have := Q.one_le_r E; show r ≠ 0; omega),
      fun _ => gs_fact_le_Bk Q E hd⟩

theorem gs_encGroup_eq {n : ℕ} (gs : List (Perm (Fin n))) :
    encGroup gs = .list [.nat n, .list ((1 :: gs).map GI.Cited.encPerm)] := rfl

theorem gs_get_deg {P : Program} {env : List Val} {l : Expr} {n c : ℕ}
    {gs : List (Perm (Fin n))} (h : Det P env l (encGroup gs) c) :
    Det P env (.get l (.nat 0)) (.nat n) (c + (0 + 3) + (Val.nat n).wt + 1) :=
  Det.get' (vs := [.nat n, .list ((1 :: gs).map GI.Cited.encPerm)]) h (Det.nat 0) rfl

/-- **The general dispatcher meets its step specification** for every interface whose work at
the nodes of kind `dispatch` and `normalize` is at least `gsOwn k (stateW k S)`. -/
theorem gs_general_spec (I : Iface) (hmb : MinimalBlocks) (hO : GroupOrder)
    (hC : CameronRecognition) (hp : Preimage) (hm : Membership) {Cn : ℕ → ℕ → ℕ}
    (hCn : ∀ {k W W' : ℕ}, W ≤ W' → Cn k W ≤ Cn k W') {Pg : Program} {F : Funs}
    {f fexp jo fcase fbr : ℕ} (hf : Pg.funs[f]? = some (gsGenE fexp jo fcase fbr))
    (hexp : ExposeAt hmb Pg fexp) (hjo : Pg.prims[jo]? = some (groupOrderPrim hO))
    (hcase : CaseAt hO hC Pg fcase) (hbr : BranchAt I hp hm Cn Pg F fbr)
    (hW : ∀ nd : Node P₀, nd.run.kind = .dispatch ∨ nd.run.kind = .normalize →
      (gsOwn hmb hO hC hp hm Cn (Nat.card nd.Ω) (stateW (Nat.card nd.Ω) nd.S) : ℝ) ≤ I.W nd) :
    I.GeneralSpec Pg F f := by
  intro Ω C S k e c hc v hv hgood hP hIH
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  have hcan : Canon e c v S := hv
  obtain ⟨hs, htr, hfl⟩ := hP
  obtain ⟨gv, dv, xv, yv, hv0, rv, hg, hd, -, -, hh, hr, rfl⟩ := hcan.val
  obtain ⟨gs, rfl, hgs, hgsl⟩ := hg
  have hd' : dv = encFun (indF e S.dom) := hd
  subst hd'
  obtain ⟨vs, rfl, hF⟩ := hh
  set v := Val.list [.nat k, encGroup gs, encFun (indF e S.dom), xv, yv, .list vs, rv,
    boolVal S.floor, .nat S.h, .nat S.N] with hvdef
  have hinv : S.HierInv := hgood.2.2
  have h2 : ¬ UnivOn S.dom ⊥ := not_univOn_bot_of_large P₀_terminating P₀_γ hgood.1 hs
  have hk := Iface.card_eq e
  have hWs : v.wt ≤ stateW k S := hcan.wt_le
  set X := gsX hmb v.wt with hXdef
  clear_value X
  refine FunAll.intro hf ?_
  -- 1. the exposure
  have hx := (hexp htr hinv h2 hgs hgsl ⟨vs, rfl, hF⟩ hr xv yv (boolVal S.floor) (.nat S.h)
    (.nat S.N)).wt_lt
  have d1 : EvalAll Pg [v] (.call fexp (.var 0)) (fun x c1 => ∃ Q : PrimitiveQuotient S,
      Q.KillsCols ∧ Q.KeepsLevels ∧ ExposeOut e Q x ∧ c1 ≤ v.wt + 1 + X + x.wt + 1 ∧
      x.wt < X) :=
    EvalAll.call_funAll (Det.var' (i := 0) rfl) fun v0 ca h0 => by
      obtain ⟨rfl, hca⟩ := h0
      exact hx.mono fun w cb ⟨⟨Q, q1, q2, q3, q4⟩, q5⟩ => by
        have q4' : cb ≤ X := by rw [hXdef]; exact q4
        exact ⟨Q, q1, q2, q3, by omega, by omega⟩
  refine EvalAll.letE d1 fun x c1 hx1 => ?_
  obtain ⟨Q, hkc, hkl, hxo, hc1, hxw⟩ := hx1
  have hxo' := hxo
  obtain ⟨gv', rep, hv', rfl, hgv', hrep, hH⟩ := hxo'
  obtain ⟨gs', rfl, hgg⟩ := hgv'
  have hgv' : GroupVal Q.d (encGroup gs') Q.ρ.range := ⟨gs', rfl, hgg⟩
  set gv' := encGroup gs' with hgvdef
  set x := Val.list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length] with hxdef
  have hdk : Q.d ≤ k := Q.d_le_card e
  have wgx : gv'.wt < x.wt := wt_le_wt_list (by simp)
  -- 2. the order of `ρ(G)`
  have dgv : ∀ rest : List Val, Det Pg ([v, x] ++ rest) (.get (.var 1) (.nat 0)) gv'
      (x.wt + 1 + (0 + 3) + gv'.wt + 1) := fun rest =>
    Det.get' (Det.var' (i := 1) rfl) (Det.nat 0) rfl
  have d2 := groupOrder_call hO hjo (dgv []) hgv'
  refine EvalAll.letE d2 fun o c2 ho => ?_
  obtain ⟨rfl, hc2⟩ := ho
  set B := Nat.card Q.ρ.range with hBdef
  have wB : (Val.nat B).wt ≤ Q.d ^ 2 + 3 := wt_card_le _
  -- 3. the case decision
  have dd : Det Pg ([v, x] ++ [.nat B]) (.get (.get (.var 1) (.nat 0)) (.nat 0)) (.nat Q.d)
      (x.wt + 1 + (0 + 3) + gv'.wt + 1 + (0 + 3) + (Val.nat Q.d).wt + 1) :=
    gs_get_deg (dgv [.nat B])
  have d3a := Det.mk2 dd (dgv [.nat B])
  have hcs := hcase Q hgv'
  have d3 : EvalAll Pg ([v, x] ++ [.nat B]) (.call fcase (mk2 (.get (.get (.var 1) (.nat 0))
      (.nat 0)) (.get (.var 1) (.nat 0)))) (fun w c3 => CaseOut Q w ∧
        c3 ≤ (x.wt + 1 + (0 + 3) + gv'.wt + 1 + (0 + 3) + (Val.nat Q.d).wt + 1) +
          (x.wt + 1 + (0 + 3) + gv'.wt + 1) + 2 * (Val.list [.nat Q.d, gv']).wt + 7 +
          (caseCost hO hC gv' Q.d + 10 * w.wt) + w.wt + 1) :=
    EvalAll.call_funAll d3a fun a ca h => by
      obtain ⟨rfl, hca⟩ := h
      exact hcs.mono fun w cb ⟨q1, q2⟩ => ⟨q1, by omega⟩
  refine EvalAll.letE d3 fun w c3 hw3 => ?_
  obtain ⟨hw, hc3⟩ := hw3
  have wW : w.wt ≤ gsWc k := gs_caseOut_wt_le Q hdk hw
  obtain ⟨hR0, hR1⟩ := gs_caseR_bounds Q hdk hw
  -- 4. the branch
  have d4 := Det.mk4 (Det.var' (P := Pg) (env := [v, x] ++ [.nat B] ++ [w]) (i := 0) rfl)
    (Det.var' (i := 1) rfl) (Det.var' (i := 3) rfl) (Det.var' (i := 2) rfl)
  refine EvalAll.call_funAll d4 fun a ca h => ?_
  obtain ⟨rfl, hca⟩ := h
  refine (hbr hc hcan hgood hs htr hfl hIH Q hkc hkl hxo hw (le_refl B)).mono ?_
  rintro u cb ⟨A, rn, hkind, hAu, hcb⟩
  refine ⟨A, none, rn, rfl, hkind, hAu, ?_⟩
  -- the cost
  have hu := hAu.wt_le
  have hXe : X = gsX hmb v.wt := hXdef
  set Wa := (Val.list [v, x, w, .nat B]).wt with hWa
  have hWa' : Wa ≤ gsWb k v.wt X := by
    have := wt_list4_le v x w (.nat B)
    have := Nat.pow_le_pow_left hdk 2
    unfold gsWb; omega
  have hbrc := gs_brCost_le hp hm (Cn := Cn) hCn (k := k) (W := Wa) (B := B) (r := caseR w) hWa' hR0 hR1
  have hcc := gs_caseCost_le hO hC (gv := gv') (X := X) hdk (by omega)
  have hOb := mb_bound_le (groupOrderPrim hO) (v := gv') (W := X) (by omega)
  have hd2 := Nat.pow_le_pow_left hdk 2
  have hk2 : k ^ 2 ≤ (k + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hk1 : k + 2 ≤ (k + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have wd := wt_nat_le Q.d
  have wl2 := wt_list2_le (.nat Q.d) gv'
  have hown : gsOwn hmb hO hC hp hm Cn k v.wt ≤ gsOwn hmb hO hC hp hm Cn k (stateW k S) :=
    gsOwn_mono hmb hO hC hp hm hCn k hWs
  have hWn := hW rn.node (by simpa [Run.node] using hkind)
  simp only [Run.node] at hWn
  rw [hk] at hWn
  have hown' : ((gsOwn hmb hO hC hp hm Cn k v.wt : ℕ) : ℝ) ≤ I.own .cont rn v := by
    simp only [Iface.own, reduceCtorEq, if_false]
    exact (Nat.cast_le.mpr hown).trans (hWn.trans (le_max_right _ _))
  have key : c1 + (c2 + (c3 + (ca + brCost hp hm Cn k Wa B (caseR w) + u.wt + 1) + u.wt + 1) +
      u.wt + 1) + u.wt + 1 ≤ gsOwn hmb hO hC hp hm Cn k v.wt := by
    unfold gsOwn
    rw [← hXdef]
    have h2c : 2 * (groupOrderPrim hO).c * (X + 2) ^ (groupOrderPrim hO).k =
        2 * ((groupOrderPrim hO).c * (X + 2) ^ (groupOrderPrim hO).k) := by ring
    omega
  have key' := (Nat.cast_le (α := ℝ)).mpr key
  push_cast at key' hcb ⊢
  linarith

end GI.Impl
