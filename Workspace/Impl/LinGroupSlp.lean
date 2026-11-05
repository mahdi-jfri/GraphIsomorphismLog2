module

public import Workspace.Impl.LinGroupSlpStep
public import Workspace.Impl.LinIntSlpValue

@[expose] public section

/-! Evaluate an SLP in a bounded encoded group, retaining shared entries.
The encoding need not be faithful. In particular, the cover can act through
a nonfaithful full affine representation. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linGroupSlpFuns (b mul inv : ℕ) : List Expr :=
  [linSlpValueF (b + 2), linGroupSlpStepF mul inv] ++ linSlpFuns (b + 2) (b + 1)

theorem linGroupSlpFuns_length (b mul inv : ℕ) : (linGroupSlpFuns b mul inv).length = 5 := rfl

structure linGroupSlpAt (P : Program) (b mul inv : ℕ) : Prop where
  entry : P.funs[b]? = some (linSlpValueF (b + 2))
  step : P.funs[b + 1]? = some (linGroupSlpStepF mul inv)
  loop : P.HasAt (b + 2) (linSlpFuns (b + 2) (b + 1))

theorem linGroupSlpAt_of {P : Program} {b mul inv : ℕ}
    (h : P.HasAt b (linGroupSlpFuns b mul inv)) : linGroupSlpAt P b mul inv where
  entry := (h.block (gs := [linSlpValueF (b + 2)]) 0 rfl).single
  step := (h.block (gs := [linGroupSlpStepF mul inv]) 1 rfl).single
  loop := h.block 2 rfl

def linGroupSlpArg (W L B : ℕ) : ℕ := 10 * (W + linVectorAccWt L B + 1)
def linGroupSlpLoopStepCost (W L B C : ℕ) : ℕ :=
  10000 * (W + L + B + linVectorAccWt L B + linGroupSlpStepCost (linGroupSlpArg W L B) B C + 1)
def linGroupSlpLoopCost (W L B C : ℕ) : ℕ :=
  L * linGroupSlpLoopStepCost W L B C +
    loopModK * (L + 1) * (W + L + linVectorAccWt L B + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linGroupSlp_loop_spec {G : Type*} [Group G] {P : Program} {b step mul inv B C : ℕ}
    (hp : P.HasAt b (linSlpFuns b step)) (hstep : P.funs[step]? = some (linGroupSlpStepF mul inv))
    (enc : G → Val) (hB : ∀ x, (enc x).wt ≤ B)
    (hm : ∀ x y, FunDet P mul (.list [enc x, enc y]) (enc (x * y)) C)
    (hi : ∀ x, FunDet P inv (enc x) (enc x⁻¹) C)
    (gs : List G) (prog : List SlpInstr) (es : List G)
    (hprog : linSlpEntries gs prog [] = some es) :
    FunDet P b (.list [linGroupSlpTable enc gs, .list (prog.map encSlpInstr)]) (linGroupSlpTable enc es)
      (linGroupSlpLoopCost (Val.list [linGroupSlpTable enc gs, .list (prog.map encSlpInstr)]).wt
        prog.length B C) := by
  let a := Val.list [linGroupSlpTable enc gs, .list (prog.map encSlpInstr)]
  let W := a.wt
  let M := linVectorAccWt prog.length B
  have wg : (linGroupSlpTable enc gs).wt < W := wt_le_wt_list (by simp [W, a])
  have wp : (Val.list (prog.map encSlpInstr)).wt < W := wt_le_wt_list (by simp [W, a])
  have hacc (k : ℕ) : (linGroupSlpTable enc (linSlpPrefix gs prog k)).wt ≤ M := by
    have hh := linWtList (vs := (linSlpPrefix gs prog k).map enc) (B := B)
      (by intro v hv; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv; exact hB x)
    have hl := linSlpEntries_length gs (prog.take k) [] _ (linSlpPrefix_valid gs prog es hprog k)
    simp only [List.length_nil, zero_add, List.length_take] at hl
    simp only [List.length_map, hl] at hh
    change (Val.list ((linSlpPrefix gs prog k).map enc)).wt ≤ linVectorAccWt prog.length B
    unfold linVectorAccWt
    have hmin : min k prog.length ≤ prog.length := Nat.min_le_right _ _
    have hmul : min k prog.length * B ≤ prog.length * B := Nat.mul_le_mul_right B hmin
    omega
  have hlast : linSlpPrefix gs prog prog.length = es := by simp [linSlpPrefix, hprog]
  have dl := Det.length (Det.arg' (P := P)
    (vs := [linGroupSlpTable enc gs, .list (prog.map encSlpInstr)]) (rest := []) (j := 1) rfl)
  simp only [List.length_map] at dl
  have hl := loopBdd_spec hp dl Det.nil (by
      have hw := a.two_le_size.trans a.size_le_wt
      change 2 * a.wt + 1 + 5 + prog.length + 3 + 5 ≤ 10 * (a.wt + prog.length + 1)
      omega)
    (Inv := fun k acc => acc = linGroupSlpTable enc (linSlpPrefix gs prog k)) (M := M)
    (D := fun _ => linGroupSlpLoopStepCost W prog.length B C) rfl
    (fun k acc _ he => he ▸ hacc k) (fun k acc hk he => ?_)
  · refine hl.mono fun out cost ho => ⟨by simpa only [hlast] using ho.1, ?_⟩
    simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul, linGroupSlpLoopCost] using ho.2
  · subst acc
    obtain ⟨x, hx, hnext⟩ := linSlpPrefix_step gs prog es hprog k hk
    let prev := linSlpPrefix gs prog k
    have wprev := hacc k
    have wnext := hacc (k + 1)
    have wins : (encSlpInstr prog[k]).wt < W :=
      (wt_le_wt_list (List.mem_map.mpr ⟨prog[k], List.getElem_mem hk, rfl⟩)).trans wp
    have wi := wt_list3_le (linGroupSlpTable enc gs) (linGroupSlpTable enc prev) (encSlpInstr prog[k])
    have warg : (Val.list [linGroupSlpTable enc gs, linGroupSlpTable enc prev, encSlpInstr prog[k]]).wt ≤
        linGroupSlpArg W prog.length B := by
      unfold linGroupSlpArg
      dsimp only [prev, M] at *
      omega
    have hs := linGroupSlpStep_spec hstep enc hB hm hi gs prev prog[k] x hx
    have hs' := hs.mono (show linGroupSlpStepCost _ B C ≤ linGroupSlpStepCost (linGroupSlpArg W prog.length B) B C by
      unfold linGroupSlpStepCost; omega)
    have da := Det.arg' (P := P) (vs := [a, .nat k, linGroupSlpTable enc prev]) (rest := []) (j := 0) rfl
    have dg := Det.get' da (Det.nat 0) rfl
    have dp := Det.get' da (Det.nat 1) rfl
    have di := Det.arg' (P := P) (vs := [a, .nat k, linGroupSlpTable enc prev]) (rest := []) (j := 1) rfl
    have dins := Det.get' dp di (by simpa using congrArg (Option.map encSlpInstr) (List.getElem?_eq_getElem hk))
    have dacc := Det.arg' (P := P) (vs := [a, .nat k, linGroupSlpTable enc prev]) (rest := []) (j := 2) rfl
    have dd := Det.snoc dacc (Det.call (Det.mk3 dg dacc dins) hs')
    refine dd.post fun cost hc => ⟨?_, ?_⟩
    · rw [hnext]
      simp only [linGroupSlpTable, List.map_append, List.map_singleton]
      rfl
    · have wx := hB x
      have wk := wt_nat_le k
      have wenv := wt_list3_le a (.nat k) (linGroupSlpTable enc prev)
      have wsa := wt_list3_le (linGroupSlpTable enc gs) (linGroupSlpTable enc prev) (encSlpInstr prog[k])
      have w0 : (Val.nat 0).wt = 2 := by decide
      have w1 : (Val.nat 1).wt = 3 := by decide
      rw [hnext] at wnext
      change cost ≤ linGroupSlpLoopStepCost W prog.length B C + 100 * (W + prog.length + M + 1)
      unfold linGroupSlpLoopStepCost
      dsimp only [W, a, M, prev, linGroupSlpTable] at *
      simp only [List.map_append, List.map_singleton] at *
      omega

theorem linGroupSlpLoopCost_mono {W V L B C : ℕ} (hW : W ≤ V) :
    linGroupSlpLoopCost W L B C ≤ linGroupSlpLoopCost V L B C := by
  unfold linGroupSlpLoopCost linGroupSlpLoopStepCost linGroupSlpStepCost linGroupSlpArg
  gcongr

def linGroupSlpCost (W L B C : ℕ) : ℕ :=
  10000 * (W + L + B + linVectorAccWt L B + linGroupSlpLoopCost (10 * (W + 1)) L B C + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linGroupSlp_spec {G : Type*} [Group G] {P : Program} {b mul inv B C : ℕ}
    (hp : linGroupSlpAt P b mul inv) (enc : G → Val) (hB : ∀ x, (enc x).wt ≤ B)
    (hm : ∀ x y, FunDet P mul (.list [enc x, enc y]) (enc (x * y)) C)
    (hi : ∀ x, FunDet P inv (enc x) (enc x⁻¹) C)
    (gs : List G) (prog : List SlpInstr) (es : List G)
    (hprog : linSlpEntries gs prog [] = some es) :
    FunDet P b (.list [linGroupSlpTable enc gs, .list (prog.map encSlpInstr), enc 1])
      (enc (es.getLast?.getD 1))
      (linGroupSlpCost (Val.list [linGroupSlpTable enc gs, .list (prog.map encSlpInstr), enc 1]).wt
        prog.length B C) := by
  let a := Val.list [linGroupSlpTable enc gs, .list (prog.map encSlpInstr), enc 1]
  let W := a.wt
  have wg : (linGroupSlpTable enc gs).wt < W := wt_le_wt_list (by simp [W, a])
  have wp : (Val.list (prog.map encSlpInstr)).wt < W := wt_le_wt_list (by simp [W, a])
  have wo := hB 1
  have wi := wt_list2_le (linGroupSlpTable enc gs) (.list (prog.map encSlpInstr))
  have ww : (Val.list [linGroupSlpTable enc gs, .list (prog.map encSlpInstr)]).wt ≤ 10 * (W + 1) := by omega
  have hs := (linGroupSlp_loop_spec hp.loop hp.step enc hB hm hi gs prog es hprog).mono
    (linGroupSlpLoopCost_mono ww)
  have wt := hs.wt_lt.le
  have hl := linSlpEntries_length gs prog [] es hprog
  simp only [List.length_nil, zero_add] at hl
  have wm : (linGroupSlpTable enc es).wt ≤ linVectorAccWt prog.length B := by
    have hh := linWtList (vs := es.map enc) (B := B) (by
      intro v hv; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv; exact hB x)
    simpa only [linGroupSlpTable, List.length_map, hl, linVectorAccWt] using hh
  have da (j : ℕ) (rest : List Val) {v : Val}
      (hv : [linGroupSlpTable enc gs, .list (prog.map encSlpInstr), enc 1][j]? = some v) :=
    Det.arg' (P := P) (vs := [linGroupSlpTable enc gs, .list (prog.map encSlpInstr), enc 1])
      (rest := rest) (j := j) hv
  have dc := Det.call (Det.mk2 (da 0 [] rfl) (da 1 [] rfl)) hs
  have dv := Det.var' (P := P) (env := [a, linGroupSlpTable enc es]) (i := 1) rfl
  have dl := Det.length dv
  simp only [List.length_map] at dl
  cases es using List.reverseRecOn with
  | nil =>
    have dd := Det.ite_zero (t := .get (.var 1) (.arith .sub (.length (.var 1)) (.nat 1))) dl
      (da 2 [linGroupSlpTable enc []] rfl)
    apply FunDet.intro hp.entry
    refine (Det.letE dc dd).mono ?_
    unfold linGroupSlpCost
    dsimp only [W, a, linGroupSlpTable] at *
    simp only [List.map_nil, List.getLast?_nil, Option.getD_none] at *
    omega
  | append_singleton es x =>
    have dlen := Det.length dv
    simp only [List.length_map, List.length_append, List.length_singleton] at dlen
    have didx := Det.arith (op := .sub) dlen (Det.nat 1)
    have he : GI.Machine.BinOp.eval .sub (es.length + 1) 1 = es.length := by simp
    rw [he] at didx
    have dg := Det.get' dv didx (show ((es ++ [x]).map enc)[es.length]? = some (enc x) by simp)
    have dd := Det.ite_pos (e := arg 2) dlen (by omega : es.length + 1 ≠ 0) dg
    have wx := hB x
    have wn := wt_nat_le (es.length + 1)
    have wi := wt_nat_le es.length
    have w0 : (Val.nat 1).wt = 3 := by decide
    simp only [List.getLast?_concat, Option.getD_some]
    apply FunDet.intro hp.entry
    refine (Det.letE dc dd).mono ?_
    unfold linGroupSlpCost
    dsimp only [W, a, linGroupSlpTable] at *
    simp only [List.length_append, List.length_singleton] at *
    omega

theorem linGroupSlpCost_poly : PBU (fun L W U => linGroupSlpCost W L U U) := by
  unfold linGroupSlpCost linGroupSlpLoopCost linGroupSlpLoopStepCost linGroupSlpStepCost
    linGroupSlpArg linVectorAccWt
  norm_poly

end GI.Impl
