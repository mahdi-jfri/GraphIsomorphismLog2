import Workspace.Impl.AggItemStepMv
import Workspace.Impl.AggItemTs

/-!
# The items after the structure step

On the output `K.v` of the structure step, the program `itSRunF fts di0 drun` lists the branch
tuples (`it_ts_spec`, at `fts`), runs the init program of the case (through the dispatcher `di0`),
and then runs the script runner `drun` (`runBody`) from the first state of `itSRep`, with the step
function `cpLoopBody dloop mv` of `AggItemStepMv.lean`.

`itS_run`: at a context `K` of a call where the case meets `ItSCaseAt` with bound `B`, the
program returns the pieces and overcosets of a run of the items' script of a round of `K.Cs`,
with output weight at most `itSStepB` and cost at most `itSRunX W₀ B` plus the cost of the calls.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm gens encGroup encKColoring)

variable {Ω C : Type} {k : ℕ}

/-- **The items after the structure step**, on `v = [st, [d, d'], code, src]`. -/
def itSRunF (fts di0 drun : ℕ) : Expr :=
  .letE (.call fts (mk2 (.get (.get (.get (.var 0) (.nat 0)) (.nat 1)) (.nat 1)) (.nat 65)))
  (.letE (.call di0 (mk2 (.get (.var 0) (.nat 2)) (.var 0)))
    (.call drun (mk2 (itSMk6 (.nat 0) (.var 0) (.var 1) (.nat 0) (mk2 .nil .nil) (.var 2))
      (.nat 0))))

/-- The bound of the number of branches. -/
def itSNb (W₀ : ℕ) : ℕ := (2 * W₀ + 3) ^ 65

/-- The weight bound of the list of the branch tuples. -/
def itSTvB (W₀ : ℕ) : ℕ := itSNb W₀ * (2 * (5 * (2 * W₀ + 3 + 1) ^ 2) + 1) + 4

/-- The bound of the step function of the items, for the case bound `B`. -/
def itSStB (W₀ B : ℕ) : ℕ := itSStepB (itSVB W₀) (itSTvB W₀) (itSNb W₀) B

/-- The cost bound of `itSRunF` besides the calls of the run. -/
noncomputable def itSRunX (W₀ B : ℕ) : ℕ :=
  itTsC (itSNb W₀ + (2 * W₀ + 3) + 75) + 4 * B + itSDispC (2 * itSVB W₀ + 16) +
    40 * (itSVB W₀ + itSTvB W₀ + B + itSBw (itSVB W₀) (itSTvB W₀) (itSNb W₀) B) + 1000 +
    4 * (itSStB W₀ B + 1) + (itSNb W₀ * B + 1) * (runK * (itSStB W₀ B + 1))

theorem itS_tsC_mono {Y Y' : ℕ} (h : Y ≤ Y') : itTsC Y ≤ itTsC Y' := by
  unfold itTsC itTvC itTvW
  gcongr

/-- The number of branches is at most `itSNb W₀`. -/
theorem itS_n_le (I : Iface) (Pg : Program) (F : Funs) {e : Ω ≃ Fin k} {c : C → ℕ}
    {S : State Ω C} {sv lv : Val} {L : SuppliedLabels S} (hc : AsCall I Pg F e c S sv lv L) :
    (itSTups L.q).length ≤ itSNb (I.inW .giant S) ∧ L.q ^ 65 ≤ itSNb (I.inW .giant S) := by
  obtain ⟨hkq, -, -, -, -, -⟩ := itS_size I Pg F hc
  have h : L.q ^ 65 ≤ itSNb (I.inW .giant S) := Nat.pow_le_pow_left (by omega) 65
  refine ⟨?_, h⟩
  rw [itSTups, stTs_length]
  exact h

/-- The list of the branch tuples weighs at most `itSTvB W₀`. -/
theorem itS_tv_wt (I : Iface) (Pg : Program) (F : Funs) {e : Ω ≃ Fin k} {c : C → ℕ}
    {S : State Ω C} {sv lv : Val} {L : SuppliedLabels S} (hc : AsCall I Pg F e c S sv lv L) :
    (itSTv L.q).wt ≤ itSTvB (I.inW .giant S) := by
  obtain ⟨hkq, hκ, -, -, -, -⟩ := itS_size I Pg F hc
  have hn := (itS_n_le I Pg F hc).1
  have h := wt_list_le_of ((itSTups L.q).map stTv) (c := 5 * (2 * I.inW .giant S + 3 + 1) ^ 2)
    fun v hv => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hv
      exact wt_stTv_le t (by omega) (by omega)
  rw [List.length_map] at h
  have : (itSTups L.q).length * (2 * (5 * (2 * I.inW .giant S + 3 + 1) ^ 2) + 1) ≤
      itSNb (I.inW .giant S) * (2 * (5 * (2 * I.inW .giant S + 3 + 1) ^ 2) + 1) :=
    Nat.mul_le_mul_right _ hn
  unfold itSTvB
  exact h.trans (by omega)

/-- **The programs of the items after the structure step**, at their indices: `itSRunF` at
`frun`, the branch tuples at `fts`, the dispatchers `di0` (init) and `db` (branch step) of the
case programs `i₁, i₂, i₃` and `b₁, b₂, b₃`, the runner at `drun`, the loop of moves at `dloop`,
and the moves (`ItSProgAt`). -/
structure ItSRunAt (Pg : Program) (F : Funs) (frun fts di0 drun dloop mv m0 m1 m3 db fac app
    i₁ i₂ i₃ b₁ b₂ b₃ : ℕ) : Prop where
  hf : Pg.funs[frun]? = some (itSRunF fts di0 drun)
  hts : ∀ q, 0 < q → FunDet Pg fts (.list [.nat q, .nat 65]) (itSTv q) (itTsC (q ^ 65 + q + 65 + 10))
  hdi0 : Pg.funs[di0]? = some (itSDispF i₁ i₂ i₃)
  hdb : Pg.funs[db]? = some (itSDispF b₁ b₂ b₃)
  hrun : Pg.funs[drun]? = some (runBody F drun dloop)
  hloop : Pg.funs[dloop]? = some (cpLoopBody dloop mv)
  hmv : ItSProgAt Pg mv m0 m1 m3 db fac app

/-- **The branch tuples from `it_ts_spec`.** -/
theorem itS_ts_of {P : Program} {f pw rb mp tv dc : ℕ} (hf : P.funs[f]? = some (itTsF pw rb mp))
    (hpw : P.HasAt pw (stDPowFuns pw)) (hrb : P.HasAt rb (rangeFuns rb))
    (hmp : P.HasAt mp (mapFuns mp tv)) (htv : P.funs[tv]? = some (itTvF dc))
    (hdc : P.HasAt dc (stDDecFuns dc)) :
    ∀ q, 0 < q → FunDet P f (.list [.nat q, .nat 65]) (itSTv q) (itTsC (q ^ 65 + q + 65 + 10)) :=
  fun _ hq => it_ts_spec hf hpw hrb hmp htv hdc hq

section Run

variable (I : Iface) (Pg : Program) (F : Funs) {e : Ω ≃ Fin k} {c : C → ℕ} {S : State Ω C}
  {sv lv : Val} {L : SuppliedLabels S}

set_option maxHeartbeats 1000000 in
/-- **The items after the structure step.** -/
theorem itS_run {frun fts di0 drun dloop mv m0 m1 m3 db fac app i₁ i₂ i₃ b₁ b₂ b₃ : ℕ}
    (hP : ItSRunAt Pg F frun fts di0 drun dloop mv m0 m1 m3 db fac app i₁ i₂ i₃ b₁ b₂ b₃)
    (hc : AsCall I Pg F e c S sv lv L) {K : ItSCtx k S L} (hK : K.OK e c) {R : ItSCaseRel}
    {B : ℕ} (hA : ItSCaseAt Pg R (itSCaseF i₁ i₂ i₃ K.case) (itSCaseF b₁ b₂ b₃ K.case) e c S L K B) :
    FunAll Pg frun K.v (fun w cost => ∃ Ag ∈ K.Cs, ∃ (a : Branches Ω) (ex : Exec P₀ Ag.itemsScript a),
      ItSFin e L.toGiantLabels a w ∧ w.wt ≤ itSStB (I.inW .giant S) B ∧
      (cost : ℝ) ≤ itSRunX (I.inW .giant S) B + I.execCost ex) := by
  obtain ⟨hkq, hκ, -, hq0, -, -⟩ := itS_size I Pg F hc
  obtain ⟨hn, hq65⟩ := itS_n_le I Pg F hc
  have hV := itS_vW I Pg F hc hK
  have hT := itS_tv_wt I Pg F hc
  have hs := itS_stepOKC hP.hmv hA hV hT hn hP.hloop
    (fun bst Q h => itS_disp_spec hP.hdb K.case bst h)
  have eV : K.v = .list [K.st, .list [encKColoring K.d, encKColoring K.d'],
      .nat (AggCase.code K.case), natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ))] := rfl
  have eS : K.st = .list [K.sv, .list [.nat k, .nat L.q], .list (K.ps.map pairV),
      .list (K.fx.map pairV), .list (K.fy.map pairV),
      stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ)] := rfl
  have eVw : (Val.list [K.st, .list [encKColoring K.d, encKColoring K.d'],
      .nat (AggCase.code K.case), natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ))]).wt = K.v.wt := rfl
  have eSw : (Val.list [K.sv, .list [.nat k, .nat L.q], .list (K.ps.map pairV),
      .list (K.fx.map pairV), .list (K.fy.map pairV),
      stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ)]).wt = K.st.wt := rfl
  have wst : K.st.wt < K.v.wt := by rw [eV]; exact wt_le_wt_list (by simp)
  have wkq : (Val.list [.nat k, .nat L.q]).wt < K.st.wt := by rw [eS]; exact wt_le_wt_list (by simp)
  have wq : (Val.nat L.q).wt < (Val.list [.nat k, .nat L.q]).wt := wt_le_wt_list (by simp)
  have wcode : (Val.nat (AggCase.code K.case)).wt ≤ 5 :=
    (wt_nat_le _).trans (by have := it_code_le K.case; omega)
  refine FunAll.intro hP.hf ?_
  unfold itSRunF
  -- the branch tuples
  have dv : Det Pg [K.v] (.var 0) (.list [K.st, .list [encKColoring K.d, encKColoring K.d'],
      .nat (AggCase.code K.case), natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ))]) _ :=
    Det.var' (i := 0) rfl
  have dst : Det Pg [K.v] (.get (.var 0) (.nat 0)) (.list [K.sv, .list [.nat k, .nat L.q],
      .list (K.ps.map pairV), .list (K.fx.map pairV), .list (K.fy.map pairV),
      stCv K.O.tuples (itCr K.Ag₀.fin S K.Ag₀.πd P₀.κ)]) _ := Det.get' dv (Det.nat 0) rfl
  have dkq := Det.get' dst (Det.nat 1) (v := .list [.nat k, .nat L.q]) rfl
  have dq := Det.get' dkq (Det.nat 1) (v := .nat L.q) rfl
  have dts := Det.call (Det.mk2 dq (Det.nat 65)) (hP.hts L.q hq0)
  refine EvalAll.letE dts fun tv ct ⟨htv, hct⟩ => ?_
  subst htv
  -- the init program of the case
  have dcode : Det Pg ([K.v] ++ [itSTv L.q]) (.get (.var 0) (.nat 2)) (.nat (AggCase.code K.case)) _ :=
    Det.get' (Det.var' (i := 0) (v := .list [K.st, .list [encKColoring K.d, encKColoring K.d'],
      .nat (AggCase.code K.case), natList (stL fun i => (itSrc K.Ag₀ K.J i : ℕ))]) rfl) (Det.nat 2) rfl
  have dv0 : Det Pg ([K.v] ++ [itSTv L.q]) (.var 0) K.v _ := Det.var' (i := 0) rfl
  have hinit := itS_disp_spec hP.hdi0 K.case K.v (FunAll.wt_lt hA.init)
  have w2 := wt_list2_le (.nat (AggCase.code K.case)) K.v
  have hdc : itSDispC (Val.list [.nat (AggCase.code K.case), K.v]).wt ≤
      itSDispC (2 * itSVB (I.inW .giant S) + 16) := by unfold itSDispC; omega
  refine EvalAll.letE (Ra := fun w cw => ∃ D, D ⊆ itSBase K ∧ R.Kc e c S L K w D ∧
      cw ≤ 5 * B + itSDispC (2 * itSVB (I.inW .giant S) + 16) + 20 * itSVB (I.inW .giant S) + 200)
    (EvalAll.call_funAll (Det.mk2 dcode dv0) fun v ca hv => ?_) fun w0 ci hw0 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine FunAll.mono hinit fun w cst h => ?_
    obtain ⟨c', ⟨⟨D, h1, h2, h3⟩, hwc⟩, hcst⟩ := h
    have := hA.wtK w D h2
    exact ⟨D, h1, h2, by omega⟩
  obtain ⟨D0, hD0, hK0, hci⟩ := hw0
  have hw0B := hA.wtK w0 D0 hK0
  -- the runner
  have dH := Det.itSMk6 (Det.nat 0) (Det.var' (i := 0) (v := K.v) rfl)
    (Det.var' (i := 1) (v := itSTv L.q) rfl) (Det.nat 0) (Det.mk2 Det.nil Det.nil)
    (Det.var' (i := 2) (v := w0) rfl) (P := Pg) (env := [K.v] ++ [itSTv L.q] ++ [w0])
  have dst0 := Det.mk2 dH (Det.nat 0)
  refine EvalAll.call_funAll dst0 fun st0 ca hst0 => ?_
  obtain ⟨rfl, hca⟩ := hst0
  have hSs : (fun Ag => itSW Ag [] ((itSTups L.q).drop 0)) '' D0 =
      (fun Ag => Ag.itemsScript) '' D0 := by
    refine Set.image_congr fun Ag hAg => ?_
    rw [List.drop_zero, itSW_start, (hD0 hAg).2.1]
  have hrep : itSRep R e c S L K B (3 * ((itSTups L.q).length - 0) + 1)
      (.list [itSH 0 K.v 0 [] [] w0, .nat 0]) ((fun Ag => Ag.itemsScript) '' D0)
      ((itSTups L.q).length * B) :=
    Or.inl ⟨0, [], [], [], w0, D0, rfl, Nat.zero_le _, hK0, hD0, hSs.symm,
      itSOut_nil e L.toGiantLabels, ⟨by simp, by simp, by simp, by simp⟩, by simp, rfl⟩
  have hBw := itS_rep_wt hA hV hT hn hrep
  refine (I.run_specC Pg F hP.hrun hs hc.ih.below _ _ _ ⟨_, hrep⟩).mono ?_
  rintro out cr ⟨s, ⟨Ag, hAg, rfl⟩, a, ex, hout, hwt, hlen, hcr⟩
  refine ⟨Ag, itSBase_sub (hD0 hAg), a, ex, hout, hwt, ?_⟩
  have eB : itSStepB (itSVB (I.inW .giant S)) (itSTvB (I.inW .giant S)) (itSNb (I.inW .giant S)) B =
    itSStB (I.inW .giant S) B := rfl
  rw [eB] at hcr hwt
  -- the calls
  have hcl : ex.calls.length + 1 ≤ itSNb (I.inW .giant S) * B + 1 := by
    have := Nat.mul_le_mul_right B hn
    omega
  have hcalls : ((ex.calls.length : ℝ) + 1) * (runK * ((itSStB (I.inW .giant S) B : ℝ) + 1)) ≤
      ((itSNb (I.inW .giant S) * B + 1 : ℕ) : ℝ) * (runK * ((itSStB (I.inW .giant S) B : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right (by rw [← Nat.cast_one, ← Nat.cast_add]; exact Nat.cast_le.mpr hcl)
      (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _) zero_le_one))
  -- the costs before the run
  have hts : itTsC (L.q ^ 65 + L.q + 65 + 10) ≤
      itTsC (itSNb (I.inW .giant S) + (2 * I.inW .giant S + 3) + 75) :=
    itS_tsC_mono (by omega)
  have h2q := wt_list2_le (.nat L.q) (.nat 65)
  have := wt_nat_le 65
  have := wt_nat_le 0
  have := wt_nat_le 2
  have hnil := wt_list2_le (.list []) (.list [])
  have enil : (Val.list []).wt = 4 := rfl
  have hHs := wt_list6_lt (.nat 0) K.v (itSTv L.q) (.nat 0) (.list [.list [], .list []]) w0
  have eH0 : (itSH (k := k) (q := L.q) 0 K.v 0 [] [] w0).wt =
    (Val.list [.nat 0, K.v, itSTv L.q, .nat 0, .list [.list [], .list []], w0]).wt := rfl
  have hH0 : (itSH (k := k) (q := L.q) 0 K.v 0 [] [] w0).wt < (Val.list [itSH (k := k) (q := L.q) 0 K.v 0 [] [] w0, .nat 0]).wt :=
    wt_le_wt_list (by simp)
  have eH1 : (Val.list [Val.list [.nat 0, K.v, itSTv L.q, .nat 0, .list [.list [], .list []], w0],
    .nat 0]).wt = (Val.list [itSH (k := k) (q := L.q) 0 K.v 0 [] [] w0, .nat 0]).wt := rfl
  have hBV : itSVB (I.inW .giant S) + itSTvB (I.inW .giant S) + B ≤
      itSBw (itSVB (I.inW .giant S)) (itSTvB (I.inW .giant S)) (itSNb (I.inW .giant S)) B := by
    unfold itSBw; omega
  have hnat : ct + ci + ca + 3 * out.wt + 3 +
      (itSNb (I.inW .giant S) * B + 1) * (runK * (itSStB (I.inW .giant S) B + 1)) ≤
      itSRunX (I.inW .giant S) B := by
    unfold itSRunX
    omega
  have hnatR : ((ct + ci + ca + 3 * out.wt + 3 +
      (itSNb (I.inW .giant S) * B + 1) * (runK * (itSStB (I.inW .giant S) B + 1)) : ℕ) : ℝ) ≤
      (itSRunX (I.inW .giant S) B : ℝ) := Nat.cast_le.mpr hnat
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hnatR hcalls ⊢
  linarith

end Run

end GI.Impl
