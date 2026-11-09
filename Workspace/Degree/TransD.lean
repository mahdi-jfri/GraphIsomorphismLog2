module

public import Workspace.Degree.CaseD
public import Workspace.Impl.GenSpecNorm
public import Workspace.Impl.ContSel

@[expose] public section

/-!
# The step at a transitive state

The text of `gsGenE` of the general algorithm, with the order passed to the case decision. A step on
`v`

1. exposes a primitive quotient `Q` (`ExposeAt`);
2. computes its order with `GroupOrder`;
3. calls the case decision of `Degree/CaseD.lean`;
4. runs `branchE` of the general algorithm, whose three branches are functions of the program.

`branchD_spec` and `trans_spec` are control flow only, for any postcondition `Post` of the branches.
So they carry no mathematics, and their cost is the own cost of these steps.
-/

namespace GI.Degree

open GI.Algorithm GI.Assembly GI.Impl GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encGroup gens GroupOrder MinimalBlocks encKSetTuples MarotiStructure)

variable {Ω C : Type} {S : State Ω C}

/-- **The step at a transitive state.** -/
def transE (fexp jo fcase fbr : ℕ) : Expr :=
  .letE (.call fexp (.var 0))
  (.letE (.prim jo (.get (.var 1) (.nat 0)))
  (.letE (.call fcase (mk3 (.get (.get (.var 1) (.nat 0)) (.nat 0)) (.get (.var 1) (.nat 0))
      (.var 2)))
  (.call fbr (mk4 (.var 0) (.var 1) (.var 3) (.var 2)))))

/-- **The branch**, for any postcondition. -/
theorem branchD_spec {Pg : Program} {f fen fpr fno : ℕ}
    (hf : Pg.funs[f]? = some (branchE fen fpr fno)) {v gv rep hv lab t w : Val} {B : ℕ}
    {Post : Val → ℕ → Prop}
    (hw : w = .list [.nat 0] ∨ ∃ (m l r : ℕ) (E : Val), w = .list [.nat 1, .nat m, .nat l, .nat r, E])
    (hen : w = .list [.nat 0] → FunAll Pg fen (.list [v, rep, hv, .nat B]) Post)
    (hpr : ∀ (m l r : ℕ) (E : Val), w = .list [.nat 1, .nat m, .nat l, .nat r, E] → 2 ≤ r →
      FunAll Pg fpr (.list [v, .list [gv, rep, hv, lab, t], w]) Post)
    (hno : ∀ (m l r : ℕ) (E : Val), w = .list [.nat 1, .nat m, .nat l, .nat r, E] → ¬ 2 ≤ r →
      FunAll Pg fno (.list [v, .list [gv, rep, hv, lab, t], w]) Post) :
    FunAll Pg f (.list [v, .list [gv, rep, hv, lab, t], w, .nat B]) fun u cost =>
      ∃ c₀, Post u c₀ ∧ cost ≤ c₀ + 60 * (Val.list [v, .list [gv, rep, hv, lab, t], w, .nat B]).wt +
        100 + 3 * (u.wt + 1) := by
  set x := Val.list [gv, rep, hv, lab, t] with hx
  set a := Val.list [v, x, w, .nat B] with ha
  obtain ⟨W, hW⟩ : ∃ W, W = a.wt := ⟨_, rfl⟩
  rw [← hW]
  have hA : ∀ (j : ℕ) (w' : Val), [v, x, w, .nat B][j]? = some w' → ∀ rest : List Val,
      Det Pg (a :: rest) (arg j) w' (2 * W + j + 5) := fun j w' hj rest => by
    rw [hW]; exact Det.arg' hj
  have wa := sum_wt_lt_wt_list [v, x, w, .nat B]
  have wx := sum_wt_lt_wt_list [gv, rep, hv, lab, t]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at wa wx
  have ea : (Val.list [v, x, w, .nat B]).wt = W := by rw [hW]
  have ex : (Val.list [gv, rep, hv, lab, t]).wt = x.wt := rfl
  have hWx : (Val.list [v, x, w]).wt ≤ W := by
    rw [← ea]; exact wt_list_mono ⟨[.nat B], rfl⟩
  have w1 := wt_nat_le 1
  have w0 := wt_nat_le 0
  have w2 := wt_nat_le 2
  have w3 := wt_nat_le 3
  refine FunAll.intro hf ?_
  rcases hw with rfl | ⟨m, l, r, E, rfl⟩
  · have dc : Det Pg [a] (.get (arg 2) (.nat 0)) (.nat 0) (3 * W + 20) :=
      (Det.get' (hA 2 _ rfl []) (Det.nat 0) (show [Val.nat 0][0]? = some (.nat 0) from rfl)).mono
        (by omega)
    refine EvalAll.ite dc (fun _ _ h => ⟨0, h.1⟩) fun y cc h => ?_
    obtain ⟨h1, hcc⟩ := h
    cases h1
    rw [if_pos rfl]
    have dargs := Det.mk4 (hA 0 v rfl []) (Det.get' (hA 1 x rfl []) (Det.nat 1)
      (show [gv, rep, hv, lab, t][1]? = some rep from rfl))
      (Det.get' (hA 1 x rfl []) (Det.nat 2)
        (show [gv, rep, hv, lab, t][2]? = some hv from rfl))
      (hA 3 (.nat B) rfl [])
    refine EvalAll.call_funAll dargs fun v0 ca h0 => ?_
    obtain ⟨rfl, hca⟩ := h0
    refine (hen rfl).mono fun u cost hP => ⟨cost, hP, ?_⟩
    have w4 := Lang.wt_list4_le v rep hv (.nat B)
    omega
  · set z := Val.list [.nat 1, .nat m, .nat l, .nat r, E] with hzdef
    have wz := sum_wt_lt_wt_list [Val.nat 1, .nat m, .nat l, .nat r, E]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at wz
    have ez : (Val.list [Val.nat 1, .nat m, .nat l, .nat r, E]).wt = z.wt := rfl
    have dc : Det Pg [a] (.get (arg 2) (.nat 0)) (.nat 1) (3 * W + 20) :=
      (Det.get' (hA 2 _ rfl []) (Det.nat 0)
        (show [Val.nat 1, .nat m, .nat l, .nat r, E][0]? = some (.nat 1) from rfl)).mono (by omega)
    refine EvalAll.ite dc (fun _ _ h => ⟨1, h.1⟩) fun y cc h => ?_
    obtain ⟨h1, hcc⟩ := h
    cases h1
    rw [if_neg one_ne_zero]
    have dr : Det Pg [a] (.get (arg 2) (.nat 3)) (.nat r) (3 * W + 20) :=
      (Det.get' (hA 2 _ rfl []) (Det.nat 3)
        (show [Val.nat 1, .nat m, .nat l, .nat r, E][3]? = some (.nat r) from rfl)).mono (by omega)
    have dlt := Det.arith' (op := .lt) (Det.nat (P := Pg) (env := [a]) 1) dr rfl
    have dargs := Det.mk3 (hA 0 v rfl []) (hA 1 x rfl []) (hA 2 z rfl [])
    have hW3 : (Val.list [v, x, z]).wt ≤ W := hWx
    refine EvalAll.ite dlt (fun _ _ h => ⟨_, h.1⟩) fun y c2 h => ?_
    obtain ⟨h1, hc2⟩ := h
    cases h1
    have hlt : BinOp.eval .lt 1 r ≤ 1 := by
      simp only [BinOp.eval]; split <;> omega
    by_cases hr2 : 2 ≤ r
    · have h1 : BinOp.eval .lt 1 r = 1 := by
        show (if 1 < r then 1 else 0) = 1; rw [if_pos (by omega)]
      rw [h1, if_neg one_ne_zero]
      refine EvalAll.call_funAll dargs fun v0 ca h0 => ?_
      obtain ⟨rfl, hca⟩ := h0
      refine (hpr m l r E rfl hr2).mono fun u cost hP => ⟨cost, hP, ?_⟩
      rw [h1] at hc2
      omega
    · have h1 : BinOp.eval .lt 1 r = 0 := by
        show (if 1 < r then 1 else 0) = 0; rw [if_neg (by omega)]
      rw [h1, if_pos rfl]
      refine EvalAll.call_funAll dargs fun v0 ca h0 => ?_
      obtain ⟨rfl, hca⟩ := h0
      refine (hno m l r E rfl hr2).mono fun u cost hP => ⟨cost, hP, ?_⟩
      rw [h1] at hc2
      omega

/-- A structure from recognition has weight at most `gsWc k`. -/
theorem caseOutD_wt_le (Q : PrimitiveQuotient S) {T k : ℕ} (hd : Q.d ≤ k) {w : Val}
    (hw : CaseOutD Q T w) : w.wt ≤ gsWc k := by
  have hK : 1 ≤ (k + 2) ^ 4 := Nat.one_le_pow _ _ (by omega)
  rcases hw with ⟨rfl, -⟩ | ⟨-, m, l, r, e, -, -, -, rfl⟩
  · have := wt_list1_le (.nat 0); have := wt_nat_le 0; unfold gsWc; omega
  · obtain ⟨-, hlm, hmd, h2r⟩ := gs_kset_bounds Q e
    have hrk : r ≤ k := (Nat.lt_two_pow_self).le.trans (h2r.trans hd)
    have hE := gs_encKSet_wt_le Q e hd
    have h := wt_list_le [.nat 1, .nat m, .nat l, .nat r, encKSetTuples e]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at h
    have w1 := wt_nat_le 1
    have w2 := wt_nat_le m
    have w3 := wt_nat_le l
    have w4 := wt_nat_le r
    have h2 : k + 2 ≤ (k + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
    have h3 : 2 ^ 4 ≤ (k + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    unfold gsWc
    omega

/-- **The own work of the step**, for an input of weight `W`, besides the branch. -/
noncomputable def transOwn (hmb : MinimalBlocks) (hO : GroupOrder) (h : JohnsonRecognition)
    (E D k W : ℕ) : ℕ :=
  degTestC E D (2 * (k ^ 2 + k + D + 20)) +
    (groupOrderPrim hO).c * (gsX hmb W + 2) ^ (groupOrderPrim hO).k +
    (recognitionPrim h).c * (gsX hmb W + 2) ^ (recognitionPrim h).k +
    1000 * (W + gsX hmb W + gsWc k + k ^ 2 + k + D + 100)

set_option maxHeartbeats 2000000 in
/-- **The step at a transitive state**, for any postcondition of the three branches. -/
theorem trans_spec (hmb : MinimalBlocks) (hO : GroupOrder) (h : JohnsonRecognition) {Pg : Program}
    {f fexp jo fcase tst jr fbr fen fpr fno E D : ℕ}
    (hf : Pg.funs[f]? = some (transE fexp jo fcase fbr)) (hexp : ExposeAt hmb Pg fexp)
    (hjo : Pg.prims[jo]? = some (groupOrderPrim hO))
    (hc : Pg.funs[fcase]? = some (caseDE tst jr D)) (htst : Pg.HasAt tst (degTestFuns tst E))
    (hjr : Pg.prims[jr]? = some (recognitionPrim h))
    (hbr : Pg.funs[fbr]? = some (branchE fen fpr fno)) {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ} {v : Val}
    (hcan : Canon e c v S) (htr : S.Transitive) (hinv : S.HierInv) (h2 : ¬ UnivOn S.dom ⊥)
    (hp : ∀ Q : PrimitiveQuotient S, ¬ Nat.card Q.ρ.range ≤ Q.d ^ degExp E D → 25 ≤ Q.d ∧
      ∃ (m l r : ℕ) (E' : Fin Q.d ≃ (Fin r → {A : Finset (Fin m) // A.card = l})),
        RecogRange m l ∧ 1 ≤ r ∧ MarotiStructure Q.ρ.range E')
    {Post : Val → ℕ → Prop}
    (hen : ∀ (Q : PrimitiveQuotient S), Q.KillsCols → Q.KeepsLevels → ∀ {gv rep hv : Val},
      (Val.list [gv, rep, hv, encFun (Q.labFin e), .nat Q.pre.length]).wt < gsX hmb v.wt →
      ReprVal k rep (fun i j => Q.labFin e i = Q.labFin e j) →
      HierValC e hv (Q.pre ++ Q.top :: Q.post) → Nat.card Q.ρ.range ≤ Q.d ^ degExp E D →
      FunAll Pg fen (.list [v, rep, hv, .nat (Nat.card Q.ρ.range)]) Post)
    (hpr : ∀ (Q : PrimitiveQuotient S), Q.KillsCols → Q.KeepsLevels → ∀ {gv rep hv : Val},
      (Val.list [gv, rep, hv, encFun (Q.labFin e), .nat Q.pre.length]).wt < gsX hmb v.wt →
      GroupVal Q.d gv Q.ρ.range → normNumbered e Q rep → ReprVal k rep (fun i j => Q.labFin e i = Q.labFin e j) →
      HierValC e hv (Q.pre ++ Q.top :: Q.post) →
      ¬ Nat.card Q.ρ.range ≤ Q.d ^ degExp E D →
      ∀ (m l r : ℕ) (E' : Fin Q.d ≃ (Fin r → {A : Finset (Fin m) // A.card = l})),
        RecogRange m l → MarotiStructure Q.ρ.range E' → 2 ≤ r →
        (Val.list [.nat 1, .nat m, .nat l, .nat r, encKSetTuples E']).wt ≤ gsWc k →
      FunAll Pg fpr (.list [v, .list [gv, rep, hv, encFun (Q.labFin e), .nat Q.pre.length],
        .list [.nat 1, .nat m, .nat l, .nat r, encKSetTuples E']]) Post)
    (hno : ∀ (Q : PrimitiveQuotient S), Q.KillsCols → Q.KeepsLevels → ∀ {gv rep hv : Val},
      (Val.list [gv, rep, hv, encFun (Q.labFin e), .nat Q.pre.length]).wt < gsX hmb v.wt →
      GroupVal Q.d gv Q.ρ.range → normNumbered e Q rep →
      HierValC e hv (Q.pre ++ Q.top :: Q.post) →
      ¬ Nat.card Q.ρ.range ≤ Q.d ^ degExp E D →
      ∀ (m l r : ℕ) (E' : Fin Q.d ≃ (Fin r → {A : Finset (Fin m) // A.card = l})),
        RecogRange m l → MarotiStructure Q.ρ.range E' → 1 ≤ r → ¬ 2 ≤ r →
        (Val.list [.nat 1, .nat m, .nat l, .nat r, encKSetTuples E']).wt ≤ gsWc k →
      FunAll Pg fno (.list [v, .list [gv, rep, hv, encFun (Q.labFin e), .nat Q.pre.length],
        .list [.nat 1, .nat m, .nat l, .nat r, encKSetTuples E']]) Post) :
    FunAll Pg f v fun u cost => ∃ c₀, Post u c₀ ∧
      cost ≤ c₀ + transOwn hmb hO h E D k v.wt + 8 * (u.wt + 2) := by
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  obtain ⟨gv, dv, xv, yv, hv0, rv, hg, hd, -, -, hh, hr, rfl⟩ := hcan.val
  obtain ⟨gs, rfl, hgs, hgsl⟩ := hg
  have hd' : dv = encFun (indF e S.dom) := hd
  subst hd'
  obtain ⟨vs, rfl, hF⟩ := hh
  set v := Val.list [.nat k, encGroup gs, encFun (indF e S.dom), xv, yv, .list vs, rv,
    boolVal S.floor, .nat S.h, .nat S.N] with hvdef
  set X := gsX hmb v.wt with hXdef
  clear_value X
  refine FunAll.intro hf ?_
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
  obtain ⟨gv', rep, hv', rfl, hgv', hrep, hnum, hH⟩ := hxo
  obtain ⟨gs', rfl, hgg⟩ := hgv'
  have hgv' : GroupVal Q.d (encGroup gs') Q.ρ.range := ⟨gs', rfl, hgg⟩
  set gv' := encGroup gs' with hgvdef
  set x := Val.list [gv', rep, hv', encFun (Q.labFin e), .nat Q.pre.length] with hxdef
  have hdk : Q.d ≤ k := Q.d_le_card e
  have wgx : gv'.wt < x.wt := wt_le_wt_list (by simp)
  have dgv : ∀ rest : List Val, Det Pg ([v, x] ++ rest) (.get (.var 1) (.nat 0)) gv'
      (x.wt + 1 + (0 + 3) + gv'.wt + 1) := fun rest =>
    Det.get' (Det.var' (i := 1) rfl) (Det.nat 0) rfl
  have d2 := groupOrder_call hO hjo (dgv []) hgv'
  refine EvalAll.letE d2 fun o c2 ho => ?_
  obtain ⟨rfl, hc2⟩ := ho
  set B := Nat.card Q.ρ.range with hBdef
  have wB : (Val.nat B).wt ≤ Q.d ^ 2 + 3 := wt_card_le _
  have dd : Det Pg ([v, x] ++ [.nat B]) (.get (.get (.var 1) (.nat 0)) (.nat 0)) (.nat Q.d)
      (x.wt + 1 + (0 + 3) + gv'.wt + 1 + (0 + 3) + (Val.nat Q.d).wt + 1) :=
    gs_get_deg (dgv [.nat B])
  have dB := Det.var' (P := Pg) (env := [v, x] ++ [.nat B]) (i := 2) (v := .nat B) rfl
  have d3a := Det.mk3 dd (dgv [.nat B]) dB
  have hcs := caseD_spec h hc htst hjr Q hgv' (o := B) hBdef (hp Q)
  have d3 : EvalAll Pg ([v, x] ++ [.nat B]) (.call fcase (mk3 (.get (.get (.var 1) (.nat 0))
      (.nat 0)) (.get (.var 1) (.nat 0)) (.var 2))) (fun w c3 => CaseOutD Q (degExp E D) w ∧
        c3 ≤ (x.wt + 1 + (0 + 3) + gv'.wt + 1 + (0 + 3) + (Val.nat Q.d).wt + 1) +
          (x.wt + 1 + (0 + 3) + gv'.wt + 1) + ((Val.nat B).wt + 1) +
          3 * (Val.list [.nat Q.d, gv', .nat B]).wt + 8 +
          (caseDCost h E D gv' Q.d B + 10 * w.wt) + w.wt + 1) :=
    EvalAll.call_funAll d3a fun a ca h => by
      obtain ⟨rfl, hca⟩ := h
      exact hcs.mono fun w cb ⟨q1, q2⟩ => ⟨q1, by omega⟩
  refine EvalAll.letE d3 fun w c3 hw3 => ?_
  obtain ⟨hw, hc3⟩ := hw3
  have wW : w.wt ≤ gsWc k := caseOutD_wt_le Q hdk hw
  have d4 := Det.mk4 (Det.var' (P := Pg) (env := [v, x] ++ [.nat B] ++ [w]) (i := 0) rfl)
    (Det.var' (i := 1) rfl) (Det.var' (i := 3) rfl) (Det.var' (i := 2) rfl)
  refine EvalAll.call_funAll d4 fun a ca h' => ?_
  obtain ⟨rfl, hca⟩ := h'
  have hw' : w = .list [.nat 0] ∨ ∃ (m l r : ℕ) (E' : Val),
      w = .list [.nat 1, .nat m, .nat l, .nat r, E'] := by
    rcases hw with ⟨rfl, -⟩ | ⟨-, m, l, r, E', -, -, -, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨m, l, r, _, rfl⟩
  refine (branchD_spec (Post := Post) hbr hw' (fun hz => ?_) (fun m l r Ev hz h2r => ?_)
    (fun m l r Ev hz hr2 => ?_)).mono ?_
  · rcases hw with ⟨-, hs⟩ | ⟨-, m, l, r, E', -, -, -, hz'⟩
    · exact hen Q hkc hkl (gv := gv') hxw hrep hH hs
    · rw [hz'] at hz; cases hz
  · rcases hw with ⟨hz', -⟩ | ⟨hns, m', l', r', E', hR, hr1, hM, hz'⟩
    · rw [hz'] at hz; cases hz
    · rw [hz'] at hz
      simp only [Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at hz
      obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hz
      rw [hz'] at wW ⊢
      exact hpr Q hkc hkl hxw hgv' hnum hrep hH hns _ _ _ E' hR hM h2r wW
  · rcases hw with ⟨hz', -⟩ | ⟨hns, m', l', r', E', hR, hr1, hM, hz'⟩
    · rw [hz'] at hz; cases hz
    · rw [hz'] at hz
      simp only [Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at hz
      obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hz
      rw [hz'] at wW ⊢
      exact hno Q hkc hkl hxw hgv' hnum hH hns _ _ _ E' hR hM hr1 hr2 wW
  · rintro u cb ⟨c₀, hP, hcb⟩
    refine ⟨c₀, hP, ?_⟩
    have hW4 := Lang.wt_list4_le v x w (.nat B)
    have hW3 := Lang.wt_list3_le (.nat Q.d) gv' (.nat B)
    have wd := wt_nat_le Q.d
    have hdk2 : Q.d ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left hdk 2
    have ht := degTestC_mono E D (W := 2 * ((Val.nat B).wt + Q.d + D + 10))
      (W' := 2 * (k ^ 2 + k + D + 20)) (by omega)
    have hb1 := mb_bound_le (groupOrderPrim hO) (v := gv') (W := X) (by omega)
    have hb2 := mb_bound_le (recognitionPrim h) (v := gv') (W := X) (by omega)
    have ea : (Val.list [v, Val.list [gv', rep, hv', encFun (Q.labFin e), Val.nat Q.pre.length], w,
      Val.nat B]).wt = (Val.list [v, x, w, Val.nat B]).wt := rfl
    unfold caseDCost at hc3
    unfold transOwn
    rw [← hXdef]
    omega

/-- The test before a normalization, on `[v, x, z]`: if `q⁵ < N²`, the call goes on to the
normalization at `fad`. Otherwise the general solver at `fs` takes the state. A state after a reset
has `N = s`, so the second case is a state with `s² ≤ q⁵`. -/
def normGateE (fs fad : ℕ) : Expr :=
  .ite (.arith .lt (powE (.get (arg 2) (.nat 1)) 5) (powE (.get (arg 0) (.nat 9)) 2))
    (.call fad (.var 0)) (.call fs (arg 0))

/-- The own cost of the test. -/
def gateOwn (W N m : ℕ) : ℕ := 40 * (W + N + m + 40 + (N + 1) ^ 2 + (m + 1) ^ 5)

/-- **The test before a normalization.** -/
theorem normGate_spec {Pg : Program} {f fs fad : ℕ} (hf : Pg.funs[f]? = some (normGateE fs fad))
    {k N m l r : ℕ} {gv dv xv yv hv rv fv hh x E' : Val} {Post : Val → ℕ → Prop}
    (h1 : m ^ 5 < N ^ 2 → FunAll Pg fad (.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh,
      .nat N], x, .list [.nat 1, .nat m, .nat l, .nat r, E']]) Post)
    (h2 : ¬ m ^ 5 < N ^ 2 → FunAll Pg fs (.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N])
      Post) :
    FunAll Pg f (.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N], x,
      .list [.nat 1, .nat m, .nat l, .nat r, E']]) fun u cost => ∃ c₀, Post u c₀ ∧
        cost ≤ c₀ + gateOwn (Val.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N], x,
          .list [.nat 1, .nat m, .nat l, .nat r, E']]).wt N m + 3 * (u.wt + 1) := by
  set v := Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] with hv'
  set z := Val.list [.nat 1, .nat m, .nat l, .nat r, E'] with hz
  set a := Val.list [v, x, z] with ha
  have wv : v.wt < a.wt := wt_le_wt_list (by simp [ha])
  have wz : z.wt < a.wt := wt_le_wt_list (by simp [ha])
  have dN := Det.get' (Det.arg' (P := Pg) (vs := [v, x, z]) (rest := []) (j := 0) rfl) (Det.nat 9)
    (show [Val.nat k, gv, dv, xv, yv, hv, rv, fv, hh, Val.nat N][9]? = some (.nat N) from rfl)
  have dm := Det.get' (Det.arg' (P := Pg) (vs := [v, x, z]) (rest := []) (j := 2) rfl) (Det.nat 1)
    (show [Val.nat 1, Val.nat m, Val.nat l, Val.nat r, E'][1]? = some (.nat m) from rfl)
  have wN : (Val.nat N).wt < v.wt := wt_le_wt_list (by simp [hv'])
  have wm : (Val.nat m).wt < z.wt := wt_le_wt_list (by simp [hz])
  have ea : (Val.list [v, x, z]).wt = a.wt := rfl
  have dN' := dN.mono (show _ ≤ 3 * a.wt + 30 by omega)
  have dm' := dm.mono (show _ ≤ 3 * a.wt + 30 by omega)
  have pN := Det.powE dN' 2
  have pm := Det.powE dm' 5
  have dt := Det.arith (op := .lt) pm pN
  have hwlt : (Val.nat (BinOp.eval .lt (m ^ 5) (N ^ 2))).wt ≤ 3 := by
    simp only [BinOp.eval]; split <;> decide
  refine FunAll.intro hf (EvalAll.ite dt (fun _ _ h => ⟨_, h.1⟩) fun y cc h => ?_)
  obtain ⟨hy, hcc⟩ := h
  injection hy with hy
  subst hy
  by_cases hlt : m ^ 5 < N ^ 2
  · have e1 : BinOp.eval .lt (m ^ 5) (N ^ 2) = 1 := by
      change (if _ then 1 else 0) = 1; rw [if_pos hlt]
    rw [e1] at hcc hwlt ⊢
    rw [if_neg one_ne_zero]
    refine EvalAll.call_funAll (Det.var' (i := 0) rfl) fun v0 ca h0 => ?_
    obtain ⟨rfl, hca⟩ := h0
    refine (h1 hlt).mono fun u cost hP => ⟨cost, hP, ?_⟩
    unfold gateOwn
    omega
  · have e1 : BinOp.eval .lt (m ^ 5) (N ^ 2) = 0 := by
      change (if _ then 1 else 0) = 0; rw [if_neg hlt]
    rw [e1] at hcc hwlt ⊢
    rw [if_pos rfl]
    refine EvalAll.call_funAll (Det.arg' (P := Pg) (vs := [v, x, z]) (rest := []) (j := 0) rfl)
      fun v0 ca h0 => ?_
    obtain ⟨rfl, hca⟩ := h0
    refine (h2 hlt).mono fun u cost hP => ⟨cost, hP, ?_⟩
    unfold gateOwn
    omega

/-- **The adapter of the general algorithm before the normalization**, for any postcondition. -/
theorem normAd_spec {Pg : Program} {f fn : ℕ} (hf : Pg.funs[f]? = some (gsNormE fn))
    {v gv rep hv lab t E' : Val} {m l r : ℕ} {Post : Val → ℕ → Prop}
    (h : FunAll Pg fn (.list [v, rep, hv, .nat m, .nat l, E']) Post) :
    FunAll Pg f (.list [v, .list [gv, rep, hv, lab, t], .list [.nat 1, .nat m, .nat l, .nat r, E']])
      fun u cost => ∃ c₀, Post u c₀ ∧ cost ≤ c₀ + 100 * (Val.list [v, .list [gv, rep, hv, lab, t],
        .list [.nat 1, .nat m, .nat l, .nat r, E']]).wt + 100 + u.wt := by
  set x := Val.list [gv, rep, hv, lab, t] with hx
  set z := Val.list [.nat 1, .nat m, .nat l, .nat r, E'] with hz
  set a := Val.list [v, x, z] with ha
  have wa := sum_wt_lt_wt_list [v, x, z]
  have wx := sum_wt_lt_wt_list [gv, rep, hv, lab, t]
  have wz := sum_wt_lt_wt_list [Val.nat 1, .nat m, .nat l, .nat r, E']
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at wa wx wz
  have ex : (Val.list [gv, rep, hv, lab, t]).wt = x.wt := rfl
  have ez : (Val.list [Val.nat 1, .nat m, .nat l, .nat r, E']).wt = z.wt := rfl
  have ea : (Val.list [v, x, z]).wt = a.wt := rfl
  have d0 : Det Pg [a] (arg 0) v (2 * a.wt + 0 + 5) := Det.arg' rfl
  have d1 : Det Pg [a] (.get (arg 1) (.nat 1)) rep (2 * a.wt + 1 + 5 + (1 + 3) + rep.wt + 1) :=
    Det.get' (Det.arg' (j := 1) rfl) (Det.nat 1) rfl
  have d2 : Det Pg [a] (.get (arg 1) (.nat 2)) hv (2 * a.wt + 1 + 5 + (2 + 3) + hv.wt + 1) :=
    Det.get' (Det.arg' (j := 1) rfl) (Det.nat 2) rfl
  have d3 : Det Pg [a] (.get (arg 2) (.nat 1)) (.nat m)
      (2 * a.wt + 2 + 5 + (1 + 3) + (Val.nat m).wt + 1) :=
    Det.get' (Det.arg' (j := 2) rfl) (Det.nat 1) rfl
  have d4 : Det Pg [a] (.get (arg 2) (.nat 2)) (.nat l)
      (2 * a.wt + 2 + 5 + (2 + 3) + (Val.nat l).wt + 1) :=
    Det.get' (Det.arg' (j := 2) rfl) (Det.nat 2) rfl
  have d5 : Det Pg [a] (.get (arg 2) (.nat 4)) E'
      (2 * a.wt + 2 + 5 + (4 + 3) + E'.wt + 1) :=
    Det.get' (Det.arg' (j := 2) rfl) (Det.nat 4) rfl
  have dargs := Det.snoc (Det.snoc (Det.mk4 d0 d1 d2 d3) d4) d5
  have winp : (Val.list [v, rep, hv, .nat m, .nat l, E']).wt ≤ 2 * a.wt + 8 := by
    have := wt_list_le [v, rep, hv, .nat m, .nat l, E']
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    omega
  have w4 : (Val.list [v, rep, hv, .nat m]).wt ≤
      (Val.list [v, rep, hv, .nat m, .nat l, E']).wt := wt_list_mono ⟨[.nat l, E'], rfl⟩
  have w5 : (Val.list ([v, rep, hv, .nat m] ++ [.nat l])).wt ≤
      (Val.list [v, rep, hv, .nat m, .nat l, E']).wt := wt_list_mono ⟨[E'], rfl⟩
  have w6 : (Val.list ([v, rep, hv, .nat m] ++ [.nat l] ++ [E'])).wt =
      (Val.list [v, rep, hv, .nat m, .nat l, E']).wt := rfl
  refine FunAll.intro hf (EvalAll.call_funAll dargs fun a' ca h' => ?_)
  obtain ⟨rfl, hca⟩ := h'
  refine h.mono fun u cost hP => ⟨cost, hP, ?_⟩
  omega

end GI.Degree
