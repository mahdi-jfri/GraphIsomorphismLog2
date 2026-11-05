module

public import Workspace.Impl.GiantSelMath
public import Workspace.Impl.Lift
public import Workspace.Impl.ColsSplit
public import Workspace.Lang.Lib.Orbit
public import Workspace.Lang.Prims.Blocks

@[expose] public section

/-!
# The natural-map test of `GiantStep`, in `GI.Lang`

`natFuns b jpre` (72 functions at base `b`, the cited preimage primitive at `jpre`) decides the
second part of the row case: whether the kernel-orbit map of the supplied labels is natural
(`natural_iff`, `Workspace/Impl/GiantSelMath.lean`). It runs on the input `[sv, lv]` of
`GiantStep`, where `sv` is the state value and `lv` the label value
`[q, pairs, sel, h, f, blocks]` (`LabValStd`), and is called only when `h = 1`.

1. The graph generators `g ⊕ π g` on `Fin (k + q)`, for the pairs `[g, π g]` of `lv`
   (`shiftApp`, a `map`), as a group value (`mkGroup`).
2. **Preimage** (cited, [LM, Theorem 3.1(vi)(b)]) of the trivial group: generators `hs` of the
   kernel `K = ker π` on the `k` positions (`mem_kerInst`). Its preconditions: the graph
   generators preserve `Fin k` (they are `g ⊕ π g`), and there are no generators of the image
   subgroup.
3. The orbit labels `lab` of `⟨hs⟩` (`orbitFuns`, no cited task).
4. For each position `i`: `lbl i = a + 1` if the position lies in the domain and its block is
   `{a}`, and `lbl i = 0` off the domain (the block entry is `[]` there). The label `a` is the
   first index of the indicator with value `1` (`findEq`).
5. For each position `i` in the domain, the first position `r` with `lbl r = lbl i`, and the
   number `[lab i ≠ lab r]`; the answer is the maximum of these numbers (`chk`, `max`).

`natTest_spec`: the answer is `0` exactly when the kernel is transitive on each block fiber,
which together with `h = 1` is the natural case (`natural_iff`). The cost is at most the bound
of one preimage call on at most `natPB T` cells plus `natCostK * T ^ 16`, where
`T = wt [sv, lv] + k + q + 2` (with `k` positions and `q` labels).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encPerms encGroup gens sumToFin)

variable {Ω C : Type} {k : ℕ}

/-! ### The step functions -/

/-- On `[k, [g, σ]]`: `g ⊕ σ` (with `shiftApp` at `sa`). -/
def graphStepF (sa : ℕ) : Expr :=
  .call sa (mk3 (.get (arg 1) (.nat 0)) (.get (arg 1) (.nat 1)) (arg 0))

/-- On `[c, B]`: `0` if `B = []`, else one plus the first index of `B` with value `1`. -/
def lblStepF (fe : ℕ) : Expr :=
  .ite (.length (arg 1)) (.arith .add (.call fe (mk2 (.nat 1) (arg 1))) (.nat 1)) (.nat 0)

/-- On `[[lbl, lab], i]`: `0` if `lbl i = 0`; else, with `r` the first position with
`lbl r = lbl i`, the number `[lab i ≠ lab r]`. -/
def chkStepF (fe : ℕ) : Expr :=
  .ite (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.ite (.arith .eq (.get (.get (arg 0) (.nat 1)) (arg 1))
        (.get (.get (arg 0) (.nat 1))
          (.call fe (mk2 (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 0))))))
      (.nat 0) (.nat 1))
    (.nat 0)

/-- The constant of the step functions. -/
def natStepK : ℕ := 10 ^ 9

theorem graphStep_spec {P : Program} {b : ℕ}
    (hsa : P.funs[b + 1]? = some (shiftAppF (b + 2) (b + 5)))
    (hap : P.HasAt (b + 2) (appendFuns (b + 2))) (ham : P.HasAt (b + 5) (mapFuns (b + 5) (b + 8)))
    (hadd : P.funs[b + 8]? = some addKF) (hf : P.funs[b + 9]? = some (graphStepF (b + 1)))
    {q : ℕ} (g : Perm (Fin k)) (σ : Perm (Fin q)) :
    FunDet P (b + 9) (.list [.nat k, .list [encPerm g, encPerm σ]])
      (encPerm (sumToFin (Perm.sumCongr g σ))) (natStepK * (k + q + 1) ^ 3) := by
  set A : Val := .list [.nat k, .list [encPerm g, encPerm σ]] with hA
  have g0 := Det.arg' (P := P) (vs := [.nat k, .list [encPerm g, encPerm σ]]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [.nat k, .list [encPerm g, encPerm σ]]) (rest := []) (j := 1) rfl
  have da := Det.get' g1 (Det.nat 0) (v := encPerm g) rfl
  have dc := Det.get' g1 (Det.nat 1) (v := encPerm σ) rfl
  have ds := Det.call (Det.mk3 da dc g0) (shiftApp_spec hsa hap ham hadd g σ)
  refine FunDet.intro hf (ds.mono ?_)
  set N := k + q + 1 with hN
  have w1 : (encPerm g).wt ≤ 4 * N ^ 2 :=
    (wt_encPerm_le g).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have w2 : (encPerm σ).wt ≤ 4 * N ^ 2 :=
    (wt_encPerm_le σ).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have w3 : (encPerm (sumToFin (Perm.sumCongr g σ))).wt ≤ 4 * N ^ 2 :=
    (wt_encPerm_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have w4 := wt_list2_le (encPerm g) (encPerm σ)
  have w5 := wt_list2_le (.nat k) (.list [encPerm g, encPerm σ])
  have w6 := wt_list3_le (encPerm g) (encPerm σ) (.nat k)
  have w7 := wt_nat_le k
  have p12 : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [natStepK, shiftK] at *
  omega

theorem encFun_eq_natList {n : ℕ} (f : Fin n → ℕ) : encFun f = natList ((List.finRange n).map f) := by
  simp [encFun, natList, List.map_map, Function.comp_def]

/-- The label step on a block `{a}`, given by its indicator. -/
theorem lblStep_some {P : Program} {b : ℕ} (hf : P.funs[b + 52]? = some (lblStepF (b + 53)))
    (hfe : P.HasAt (b + 53) (findEqFuns (b + 53))) {q : ℕ} (hq : 1 ≤ q) (ind : Fin q → ℕ)
    (hind : ∀ t, ind t ≤ 1) :
    FunDet P (b + 52) (.list [.nat 0, encFun ind])
      (.nat (((List.finRange q).map ind).findIdx (fun x => decide (x = 1)) + 1))
      (natStepK * (q + 2) ^ 3) := by
  have g1 := Det.arg' (P := P) (vs := [.nat 0, encFun ind]) (rest := []) (j := 1) rfl
  have hlen := Det.length (P := P) (env := [.list [.nat 0, encFun ind]]) (l := arg 1)
      (vs := (List.finRange q).map fun i => .nat (ind i)) g1
  simp only [List.length_map, List.length_finRange] at hlen
  have hfind := findEq_spec hfe (xs := (List.finRange q).map ind) (j := 1) (B := q + 1)
    (by simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index,
      forall_apply_eq_imp_iff]; intro t; have := hind t; omega) (by omega) (by simp)
  rw [← encFun_eq_natList] at hfind
  have dc := Det.call (Det.mk2 (Det.nat (P := P) (env := [.list [.nat 0, encFun ind]]) 1) g1) hfind
  have dadd := Det.arith' (op := .add) dc (Det.nat 1)
    (z := ((List.finRange q).map ind).findIdx (fun x => decide (x = 1)) + 1) rfl
  refine FunDet.intro hf ((Det.ite_pos hlen (by omega) dadd).mono ?_)
  have hfl : ((List.finRange q).map ind).findIdx (fun x => decide (x = 1)) ≤ q := by
    have := List.findIdx_le_length (p := fun x => decide (x = 1)) (xs := (List.finRange q).map ind)
    simpa using this
  have w1 := wt_encFun_le ind (B := 1) hind
  have w2 := wt_list2_le (.nat 0) (encFun ind)
  have w3 := wt_list2_le (.nat 1) (encFun ind)
  have w4 := wt_nat_le (((List.finRange q).map ind).findIdx (fun x => decide (x = 1)) + 1)
  have w5 := wt_nat_le 0
  have w6 := wt_nat_le 1
  have w7 := wt_nat_le (((List.finRange q).map ind).findIdx (fun x => decide (x = 1)))
  have p13 : q + 2 ≤ (q + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  have p23 : (q + 2) ^ 2 ≤ (q + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have pq : (q + 1 + 1) ^ 3 = (q + 2) ^ 3 := by ring
  rw [pq] at *
  simp only [natStepK, findEqK] at *
  omega

/-- The label step off the domain. -/
theorem lblStep_none {P : Program} {b : ℕ} (hf : P.funs[b + 52]? = some (lblStepF (b + 53))) :
    FunDet P (b + 52) (.list [.nat 0, .list []]) (.nat 0) 100 := by
  have g1 := Det.arg' (P := P) (vs := [.nat 0, .list []]) (rest := []) (j := 1) rfl
  have hlen := Det.length (P := P) (env := [.list [.nat 0, .list []]]) (l := arg 1) (vs := []) g1
  refine FunDet.intro hf ((Det.ite_zero hlen (Det.nat 0)).mono ?_)
  simp [wt_nat, GI.Machine.len_zero]
  decide

/-- The first position whose label equals that of `i`. -/
def repOf (lbl : Fin k → ℕ) (i : Fin k) : ℕ :=
  ((List.finRange k).map lbl).findIdx fun x => decide (x = lbl i)

theorem repOf_lt (lbl : Fin k → ℕ) (i : Fin k) : repOf lbl i < k := by
  have h : ∃ x ∈ (List.finRange k).map lbl, decide (x = lbl i) = true :=
    ⟨lbl i, List.mem_map_of_mem (List.mem_finRange i), by simp⟩
  have := List.findIdx_lt_length_of_exists h
  simpa [repOf] using this

theorem lbl_repOf (lbl : Fin k → ℕ) (i : Fin k) : lbl ⟨repOf lbl i, repOf_lt lbl i⟩ = lbl i := by
  have h : ∃ x ∈ (List.finRange k).map lbl, decide (x = lbl i) = true :=
    ⟨lbl i, List.mem_map_of_mem (List.mem_finRange i), by simp⟩
  have hl := List.findIdx_lt_length_of_exists h
  have := List.findIdx_getElem (w := hl)
  simp only [List.getElem_map, List.getElem_finRange, decide_eq_true_eq] at this
  convert this using 2
  apply Fin.ext
  simp [repOf, Fin.cast]

/-- The value of the check step at `i`. -/
def chkVal (lbl lab : Fin k → ℕ) (i : Fin k) : ℕ :=
  if lbl i = 0 then 0 else if lab i = lab ⟨repOf lbl i, repOf_lt lbl i⟩ then 0 else 1

theorem chkVal_le_one (lbl lab : Fin k → ℕ) (i : Fin k) : chkVal lbl lab i ≤ 1 := by
  unfold chkVal; split_ifs <;> omega

theorem chkStep_spec {P : Program} {b : ℕ} (hf : P.funs[b + 60]? = some (chkStepF (b + 53)))
    (hfe : P.HasAt (b + 53) (findEqFuns (b + 53))) (lbl lab : Fin k → ℕ) {B : ℕ}
    (hlbl : ∀ i, lbl i ≤ B) (hlab : ∀ i, lab i ≤ B) (hk : k ≤ B) (i : Fin k) :
    FunDet P (b + 60) (.list [.list [encFun lbl, encFun lab], .nat i]) (.nat (chkVal lbl lab i))
      (natStepK * (B + 2) ^ 3) := by
  have h0 := Det.arg' (P := P) (vs := [(Val.list [encFun lbl, encFun lab]), .nat i]) (rest := []) (j := 0) rfl
  have h1 := Det.arg' (P := P) (vs := [(Val.list [encFun lbl, encFun lab]), .nat i]) (rest := []) (j := 1) rfl
  have dL := Det.get' h0 (Det.nat 0) (v := encFun lbl) rfl
  have dA := Det.get' h0 (Det.nat 1) (v := encFun lab) rfl
  have dli := Det.get' dL h1 (encFun_getElem? lbl i)
  have wL := wt_encFun_le' lbl hlbl hk
  have wA := wt_encFun_le' lab hlab hk
  have wC := wt_list2_le (encFun lbl) (encFun lab)
  have wa := wt_list2_le (Val.list [encFun lbl, encFun lab]) (.nat i)
  have wi := wt_nat_le (i : ℕ)
  have wli := wt_nat_le (lbl i)
  have wlai := wt_nat_le (lab i)
  have hi := i.isLt
  have hli := hlbl i
  have hlai := hlab i
  have w0 : (Val.nat 0).wt ≤ 3 := by simp [wt_nat, GI.Machine.len_zero]
  have w1 : (Val.nat 1).wt ≤ 3 := by simp [wt_nat, GI.Machine.len_zero]
  have p12 : B + 2 ≤ (B + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : (B + 2) ^ 2 ≤ (B + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have p1 : (B + 1) ^ 2 ≤ (B + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have p3 : (B + 1) ^ 3 ≤ (B + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  by_cases h0' : lbl i = 0
  · have hv : chkVal lbl lab i = 0 := by simp [chkVal, h0']
    rw [hv]
    rw [h0'] at dli
    refine FunDet.intro hf ((Det.ite_zero dli (Det.nat 0)).mono ?_)
    simp only [natStepK] at *
    omega
  · -- the representative
    have hfind := findEq_spec hfe (xs := (List.finRange k).map lbl) (j := lbl i) (B := B)
      (by simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index,
        forall_apply_eq_imp_iff]; exact hlbl) (hlbl i) (by simp [hk])
    rw [← encFun_eq_natList] at hfind
    have dr := Det.call (Det.mk2 dli dL) hfind
    have hr := repOf_lt lbl i
    have dlr := Det.get' dA dr (encFun_getElem? lab ⟨repOf lbl i, hr⟩)
    have dlai := Det.get' dA h1 (encFun_getElem? lab i)
    have deq := Det.arith' (op := .eq) dlai dlr
      (z := if lab i = lab ⟨repOf lbl i, hr⟩ then 1 else 0) (by simp [BinOp.eval])
    have din := Det.ite' deq (Det.nat (P := P) 0) (Det.nat 1)
    refine FunDet.intro hf ((Det.ite_pos dli h0' din).post fun c hc => ⟨?_, ?_⟩)
    · simp only [chkVal, h0', if_false]
      split_ifs <;> simp_all
    · have wr := wt_nat_le (repOf lbl i)
      have wlr := wt_nat_le (lab ⟨repOf lbl i, hr⟩)
      have hlr := hlab ⟨repOf lbl i, hr⟩
      have wm := wt_list2_le (.nat (lbl i)) (encFun lbl)
      have hb : ∀ p : Prop, [Decidable p] → (if p then 1 else 0 : ℕ) ≤ 1 := fun p _ => by
        split_ifs <;> omega
      have := hb (lab i = lab ⟨repOf lbl i, hr⟩)
      have wo : (if (if lab i = lab ⟨repOf lbl i, hr⟩ then 1 else 0) = 0 then Val.nat 1
          else Val.nat 0).wt ≤ 3 := by split_ifs <;> assumption
      unfold repOf at *
      simp only [natStepK, findEqK] at *
      omega

/-! ### What the checks compute -/

/-- The first index of the indicator of `{a}` with value `1` is `a`. -/
theorem findIdx_indicator {q : ℕ} (a : Fin q) (ind : Fin q → ℕ)
    (hind : ∀ t, ind t = if t = a then 1 else 0) :
    ((List.finRange q).map ind).findIdx (fun x => decide (x = 1)) = a := by
  rw [List.findIdx_eq (by simp)]
  simp only [List.getElem_map, List.getElem_finRange, hind, decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨by simp, fun j hj => ?_⟩
  rw [if_neg]
  · omega
  · intro h
    have := congrArg Fin.val h
    simp at this
    omega

/-- The checks pass exactly when equal nonzero labels mean equal orbit labels. -/
theorem chk_iff (lbl lab : Fin k → ℕ) :
    (∀ i, chkVal lbl lab i = 0) ↔ ∀ i j, lbl i ≠ 0 → lbl i = lbl j → lab i = lab j := by
  constructor
  · intro h i j hi hij
    have hci := h i
    have hcj := h j
    simp only [chkVal, hi, if_false] at hci
    have hj0 : lbl j ≠ 0 := hij ▸ hi
    simp only [chkVal, hj0, if_false] at hcj
    have hrep : repOf lbl i = repOf lbl j := by simp [repOf, hij]
    have e1 : lab i = lab ⟨repOf lbl i, repOf_lt lbl i⟩ := by by_contra hc; simp [hc] at hci
    have e2 : lab j = lab ⟨repOf lbl j, repOf_lt lbl j⟩ := by by_contra hc; simp [hc] at hcj
    rw [e1, e2]
    congr 2
  · intro h i
    unfold chkVal
    by_cases hi : lbl i = 0
    · simp [hi]
    · rw [if_neg hi, if_pos (h i _ hi (lbl_repOf lbl i).symm)]

/-- **The checks decide the fiber condition**, for labels `a + 1` on the domain (with block
`{a}`), `0` off the domain, and orbit labels of the kernel. -/
theorem chk_iff_fibers (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S} (J : JohnsonBlocks S L)
    (lbl lab : Fin k → ℕ)
    (hon : ∀ i (h : e.symm i ∈ S.dom), ∃ a, J.p ⟨_, h⟩ = {a} ∧ lbl i = a + 1)
    (hoff : ∀ i, e.symm i ∉ S.dom → lbl i = 0)
    (hlab : ∀ v w, lab (e v) = lab (e w) ↔ KerRel S L v w) :
    (∀ i, chkVal lbl lab i = 0) ↔ ∀ v w : S.dom, J.p v = J.p w → KerRel S L v w := by
  rw [chk_iff]
  constructor
  · intro h v w hvw
    obtain ⟨a, ha, hla⟩ := hon (e v) (by simpa using v.2)
    obtain ⟨b, hb, hlb⟩ := hon (e w) (by simpa using w.2)
    simp only [Equiv.symm_apply_apply] at ha hb
    rw [← hlab]
    refine h _ _ (by omega) ?_
    rw [hla, hlb]
    have : ({a} : Finset (Fin L.q)) = {b} := ha.symm.trans (hvw.trans hb)
    rw [Finset.singleton_inj.mp this]
  · intro h i j hi hij
    have hdi : e.symm i ∈ S.dom := by by_contra hc; exact hi (hoff i hc)
    have hdj : e.symm j ∈ S.dom := by by_contra hc; exact hi (hij.trans (hoff j hc))
    obtain ⟨a, ha, hla⟩ := hon i hdi
    obtain ⟨b, hb, hlb⟩ := hon j hdj
    have hab : a = b := by
      have : (a : ℕ) = b := by omega
      exact Fin.ext this
    have := h ⟨_, hdi⟩ ⟨_, hdj⟩ (by rw [ha, hb, hab])
    rw [← hlab] at this
    simpa using this

/-! ### The module -/

/-- Reading the state value, the label value, `k` and `q` from the argument `[sv, lv]`. -/
def natSV : Expr := .get (.var 0) (.nat 0)
def natLV : Expr := .get (.var 0) (.nat 1)
def natK' : Expr := .get natSV (.nat 0)
def natQ : Expr := .get natLV (.nat 0)

/-- The tail of the test, in the environment `[a, graph list, graph group, kernel]`. -/
def natTailE (b : ℕ) : Expr :=
  .letE (.call (b + 20) (mk2 natK' (.var 3)))
  (.letE (.call (b + 57) (mk2 (.nat 0) (.get natLV (.nat 5))))
  (.call (b + 67) (.call (b + 61) (mk2 (mk2 (.var 5) (.var 4)) (.call (b + 64) natK')))))

/-- **The entry of the test** on `[sv, lv]`. -/
def natEntry (b jpre : ℕ) : Expr :=
  .letE (.call (b + 10) (mk2 natK' (.get natLV (.nat 1))))
  (.letE (.call (b + 13) (mk2 (.arith .add natK' natQ) (.var 1)))
  (.letE (.prim jpre (mk3 natK' (.var 2) (.call (b + 13) (mk2 natQ .nil))))
  (natTailE b)))

/-- The first twenty functions of the test. -/
def natFunsA (b jpre : ℕ) : List Expr :=
  [natEntry b jpre] ++ [shiftAppF (b + 2) (b + 5)] ++ appendFuns (b + 2) ++
    mapFuns (b + 5) (b + 8) ++ [addKF] ++ [graphStepF (b + 1)] ++ mapFuns (b + 10) (b + 9) ++
    mkGroupFuns (b + 13)

/-- The last twenty functions of the test. -/
def natFunsB (b : ℕ) : List Expr :=
  [lblStepF (b + 53)] ++ findEqFuns (b + 53) ++
    mapFuns (b + 57) (b + 52) ++ [chkStepF (b + 53)] ++ mapFuns (b + 61) (b + 60) ++
    rangeFuns (b + 64) ++ maxFuns (b + 67)

/-- **The natural-map test** at base `b` (72 functions). -/
def natFuns (b jpre : ℕ) : List Expr := natFunsA b jpre ++ orbitFuns (b + 20) ++ natFunsB b

theorem length_natFunsA (b jpre : ℕ) : (natFunsA b jpre).length = 20 := by
  simp [natFunsA, appendFuns, mapFuns, loopFuns, mkGroupFuns, rangeFuns]

theorem length_natFuns (b jpre : ℕ) : (natFuns b jpre).length = 72 := by
  rw [natFuns, List.length_append, List.length_append, length_natFunsA, length_orbitFuns]
  simp [natFunsB, mapFuns, loopFuns, rangeFuns, findEqFuns, findFuns, maxFuns, foldlFuns]

/-- The blocks of the test module. -/
structure NatAt (P : Program) (b jpre : ℕ) : Prop where
  entry : P.funs[b]? = some (natEntry b jpre)
  shiftApp : P.funs[b + 1]? = some (shiftAppF (b + 2) (b + 5))
  append : P.HasAt (b + 2) (appendFuns (b + 2))
  addMap : P.HasAt (b + 5) (mapFuns (b + 5) (b + 8))
  addK : P.funs[b + 8]? = some addKF
  graphStep : P.funs[b + 9]? = some (graphStepF (b + 1))
  graphMap : P.HasAt (b + 10) (mapFuns (b + 10) (b + 9))
  mkGroup : P.HasAt (b + 13) (mkGroupFuns (b + 13))
  orbit : P.HasAt (b + 20) (orbitFuns (b + 20))
  lblStep : P.funs[b + 52]? = some (lblStepF (b + 53))
  findEq : P.HasAt (b + 53) (findEqFuns (b + 53))
  lblMap : P.HasAt (b + 57) (mapFuns (b + 57) (b + 52))
  chkStep : P.funs[b + 60]? = some (chkStepF (b + 53))
  chkMap : P.HasAt (b + 61) (mapFuns (b + 61) (b + 60))
  range : P.HasAt (b + 64) (rangeFuns (b + 64))
  max : P.HasAt (b + 67) (maxFuns (b + 67))

theorem natAt_of_hasAt {P : Program} {b jpre : ℕ} (h : P.HasAt b (natFuns b jpre)) :
    NatAt P b jpre := by
  have hA : P.HasAt b (natFunsA b jpre) := h.left.left
  have hO : P.HasAt (b + 20) (orbitFuns (b + 20)) := by
    have := h.left.right; rwa [length_natFunsA] at this
  have hB : P.HasAt (b + 52) (natFunsB b) := by
    have := h.right
    rwa [List.length_append, length_natFunsA, length_orbitFuns] at this
  exact {
    entry := by simpa using (hA.block 0 (gs := [natEntry b jpre]) (by rfl)).single
    shiftApp := by simpa using (hA.block 1 (gs := [shiftAppF (b + 2) (b + 5)]) (by rfl)).single
    append := hA.block 2 (by rfl)
    addMap := hA.block 5 (by rfl)
    addK := by simpa using (hA.block 8 (gs := [addKF]) (by rfl)).single
    graphStep := by simpa using (hA.block 9 (gs := [graphStepF (b + 1)]) (by rfl)).single
    graphMap := hA.block 10 (by rfl)
    mkGroup := hA.block 13 (by rfl)
    orbit := hO
    lblStep := by simpa using (hB.block 0 (gs := [lblStepF (b + 53)]) (by rfl)).single
    findEq := by simpa using hB.block 1 (gs := findEqFuns (b + 53)) (by rfl)
    lblMap := by simpa using hB.block 5 (gs := mapFuns (b + 57) (b + 52)) (by rfl)
    chkStep := by simpa using (hB.block 8 (gs := [chkStepF (b + 53)]) (by rfl)).single
    chkMap := by simpa using hB.block 9 (gs := mapFuns (b + 61) (b + 60)) (by rfl)
    range := by simpa using hB.block 12 (gs := rangeFuns (b + 64)) (by rfl)
    max := by simpa using hB.block 15 (gs := maxFuns (b + 67)) (by rfl) }

/-! ### Reading the input -/

section Read

variable {P : Program} {sv lv : Val} {svs lvs : List Val} (rest : List Val)

theorem natSV_det (hsv : sv = .list svs) :
    Det P (.list [sv, lv] :: rest) natSV sv (2 * (Val.list [sv, lv]).wt + 5) := by
  have h := Det.get' (P := P) (Det.var' (env := .list [sv, lv] :: rest) (i := 0) rfl) (Det.nat 0)
    (vs := [sv, lv]) (v := sv) rfl
  refine h.mono ?_
  have := wt_le_wt_list (vs := [sv, lv]) (v := sv) (by simp)
  have := wt_nat_le 0
  omega

theorem natLV_det :
    Det P (.list [sv, lv] :: rest) natLV lv (2 * (Val.list [sv, lv]).wt + 6) := by
  have h := Det.get' (P := P) (Det.var' (env := .list [sv, lv] :: rest) (i := 0) rfl) (Det.nat 1)
    (vs := [sv, lv]) (v := lv) rfl
  refine h.mono ?_
  have := wt_le_wt_list (vs := [sv, lv]) (v := lv) (by simp)
  have := wt_nat_le 1
  omega

theorem natK_det (hsv : sv = .list svs) (hk : svs[0]? = some (.nat k)) :
    Det P (.list [sv, lv] :: rest) natK' (.nat k) (3 * (Val.list [sv, lv]).wt + 10) := by
  subst hsv
  have h := Det.get' (natSV_det rest (P := P) (lv := lv) rfl) (Det.nat 0) hk
  refine h.mono ?_
  have h1 := wt_le_wt_list (vs := [Val.list svs, lv]) (v := .list svs) (by simp)
  have h2 := wt_le_wt_list (vs := svs) (v := .nat k) (List.mem_of_getElem? hk)
  omega

theorem natLVget_det (hlv : lv = .list lvs) {i : ℕ} {u : Val} (hi : lvs[i]? = some u) :
    Det P (.list [sv, lv] :: rest) (.get natLV (.nat i)) u (3 * (Val.list [sv, lv]).wt + i + 10) := by
  subst hlv
  have h := Det.get' (natLV_det rest (P := P) (sv := sv)) (Det.nat i) hi
  refine h.mono ?_
  have h1 := wt_le_wt_list (vs := [sv, Val.list lvs]) (v := .list lvs) (by simp)
  have h2 := wt_le_wt_list (vs := lvs) (v := u) (List.mem_of_getElem? hi)
  omega

end Read

/-! ### The tail: orbits, labels and checks -/

open Classical in
/-- The label number of position `i`: `a + 1` for a domain position whose block indicator first
has value `1` at `a`, and `0` off the domain. -/
noncomputable def lblOf (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S}
    (J : JohnsonBlocks S L) (i : Fin k) : ℕ :=
  if h : e.symm i ∈ S.dom then
    ((List.finRange L.q).map fun j => if j ∈ J.p ⟨e.symm i, h⟩ then 1 else 0).findIdx
      (fun x => decide (x = 1)) + 1
  else 0

theorem lblOf_le (e : Ω ≃ Fin k) {S : State Ω C} {L : GiantLabels S} (J : JohnsonBlocks S L)
    (i : Fin k) : lblOf e J i ≤ L.q + 1 := by
  unfold lblOf
  split_ifs
  · have := List.findIdx_le_length (p := fun x => decide (x = 1))
      (xs := (List.finRange L.q).map fun j => if j ∈ J.p ⟨e.symm i, ‹_›⟩ then 1 else 0)
    simp only [List.length_map, List.length_finRange] at this
    omega
  · omega

theorem mul_le_c_pow {a x T c i : ℕ} (ha : a ≤ T) (hx : x ≤ c * T ^ i) :
    a * x ≤ c * T ^ (i + 1) := by
  calc a * x ≤ T * (c * T ^ i) := Nat.mul_le_mul ha hx
    _ = c * T ^ (i + 1) := by ring

theorem pow_le_pow16 {T j : ℕ} (hT : 1 ≤ T) (hj : j ≤ 16) : T ^ j ≤ T ^ 16 :=
  Nat.pow_le_pow_right hT hj

/-- The constant of the tail. -/
def natTailK : ℕ := 10 ^ 16

theorem natTail_det {P : Program} {b jpre : ℕ} (hb : NatAt P b jpre) (e : Ω ≃ Fin k)
    {S : State Ω C} (L : SuppliedLabels S) {sv lv : Val} {svs : List Val} (hsv : sv = .list svs)
    (hk : svs[0]? = some (.nat k)) (hlv : LabValStd e S lv L) (hh : L.con.blocks.h = 1)
    (hq : 1 ≤ L.q) {hs : List (Perm (Fin k))} (hhs : hs.length ≤ k ^ 2)
    (hK : ∀ g, g ∈ gens hs ↔ ∃ h : (toFin e).symm g ∈ S.G, L.π ⟨_, h⟩ = 1) (gl gg : Val) :
    ∃ t, t ≤ 1 ∧ (t = 0 ↔ ∀ v w : S.dom, L.con.blocks.p v = L.con.blocks.p w →
        KerRel S L.toGiantLabels v w) ∧
      Det P [.list [sv, lv], gl, gg, .list (hs.map encPerm)] (natTailE b) (.nat t)
        (natTailK * ((Val.list [sv, lv]).wt + k + L.q + 2) ^ 16) := by
  classical
  set J := L.con.blocks with hJ
  obtain ⟨ps, hlvE, hlen, hgen, hπ⟩ := hlv
  set A := Val.list [sv, lv] with hA
  set E : List Val := [A, gl, gg, .list (hs.map encPerm)] with hE
  -- the orbit labels of the kernel
  obtain ⟨lab, hO, hlabO, hlabB⟩ := orbits_spec hb.orbit hs
  have dK := natK_det (P := P) (lv := lv) [gl, gg, .list (hs.map encPerm)] hsv hk
  have dV3 := Det.var' (P := P) (env := E) (i := 3) (v := .list (hs.map encPerm)) rfl
  have d1 := Det.call (Det.mk2 dK dV3) hO
  -- the labels of the blocks
  set E2 := E ++ [encFun lab] with hE2
  have dblk := natLVget_det (P := P) (sv := sv) [gl, gg, .list (hs.map encPerm), encFun lab]
    hlvE (i := 5) (u := blkMapVal e J) rfl
  have hmap := mapList_spec hb.lblMap (List.finRange k)
    (fun i => if h : e.symm i ∈ S.dom then
      encFun (fun j : Fin L.q => if j ∈ J.p ⟨e.symm i, h⟩ then 1 else 0) else .list [])
    (fun i => .nat (lblOf e J i)) (c := .nat 0) (B := natStepK * (L.q + 2) ^ 3)
    (fun i _ i' _ he => by
      simp only [Val.nat.injEq]
      unfold lblOf
      by_cases hi : e.symm i ∈ S.dom <;> by_cases hi' : e.symm i' ∈ S.dom <;>
        simp only [hi, hi', dite_true, dite_false] at he ⊢
      · rw [encFun_injective he]
      · have := congrArg (fun v : Val => match v with | .list l => l.length | .nat _ => 0) he
        simp [encFun] at this; omega
      · have := congrArg (fun v : Val => match v with | .list l => l.length | .nat _ => 0) he
        simp [encFun] at this; omega)
    (fun i _ => by
      by_cases hi : e.symm i ∈ S.dom
      · simp only [hi, dite_true]
        have := lblStep_some hb.lblStep hb.findEq hq
          (fun j : Fin L.q => if j ∈ J.p ⟨e.symm i, hi⟩ then 1 else 0)
          (fun t => by split_ifs <;> omega)
        unfold lblOf; simp only [hi, dite_true]
        exact this
      · simp only [hi, dite_false]
        have := lblStep_none hb.lblStep
        unfold lblOf; simp only [hi, dite_false]
        refine this.mono ?_
        have : 1 ≤ (L.q + 2) ^ 3 := Nat.one_le_pow _ _ (by omega)
        simp only [natStepK]; omega)
  have hblk : blkMapVal e J = .list ((List.finRange k).map fun i => if h : e.symm i ∈ S.dom then
      encFun (fun j : Fin L.q => if j ∈ J.p ⟨e.symm i, h⟩ then 1 else 0) else .list []) := rfl
  rw [hblk] at dblk
  have d2 := Det.call (Det.mk2 (Det.nat (P := P) (env := E2) 0) dblk) hmap
  have hlblV : Val.list ((List.finRange k).map fun i => Val.nat (lblOf e J i)) =
    encFun (lblOf e J) := rfl
  rw [hlblV] at d2
  -- the checks
  set E3 := E2 ++ [encFun (lblOf e J)] with hE3
  set T := A.wt + k + L.q + 2 with hT
  have hlabk : ∀ i, lab i < k := fun i => (hlabB i).1
  have dK3 := natK_det (P := P) (lv := lv)
    [gl, gg, .list (hs.map encPerm), encFun lab, encFun (lblOf e J)] hsv hk
  have drange := Det.call dK3 (range_det hb.range k)
  have hone : encPerm (1 : Perm (Fin k)) = .list ((List.finRange k).map fun i : Fin k => Val.nat (i : ℕ)) := rfl
  rw [hone] at drange
  have dV5 := Det.var' (P := P) (env := E3) (i := 5) (v := encFun (lblOf e J)) rfl
  have dV4 := Det.var' (P := P) (env := E3) (i := 4) (v := encFun lab) rfl
  have hchk := mapList_spec hb.chkMap (List.finRange k) (fun i => .nat i)
    (fun i => .nat (chkVal (lblOf e J) lab i)) (c := .list [encFun (lblOf e J), encFun lab])
    (B := natStepK * (T + 2) ^ 3)
    (fun i _ i' _ he => by simp only [Val.nat.injEq] at he; rw [Fin.ext he])
    (fun i _ => chkStep_spec hb.chkStep hb.findEq (lblOf e J) lab (B := T)
      (fun i => by have := lblOf_le e J i; omega) (fun i => by have := hlabk i; omega)
      (by omega) i)
  have d3a := Det.call (Det.mk2 (Det.mk2 dV5 dV4) drange) hchk
  have hmax := max_spec hb.max (xs := (List.finRange k).map (chkVal (lblOf e J) lab)) (B := k + 1)
    (by simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index,
      forall_apply_eq_imp_iff]; intro i; have := chkVal_le_one (lblOf e J) lab i; omega)
    (by simp)
  have hnl : natList ((List.finRange k).map (chkVal (lblOf e J) lab)) =
      .list ((List.finRange k).map fun i => Val.nat (chkVal (lblOf e J) lab i)) := by
    simp [natList, List.map_map, Function.comp_def]
  rw [hnl] at hmax
  have d3 := Det.call d3a hmax
  have dtail := Det.letE d1 (Det.letE d2 d3)
  refine ⟨_, ?_, ?_, dtail.mono ?_⟩
  · rw [foldl_max_01 _ 0 (by omega) (fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact chkVal_le_one _ _ i)]
    split_ifs <;> omega
  · rw [foldl_max_01 _ 0 (by omega) (fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact chkVal_le_one _ _ i)]
    have hall : (¬ (0 = 1 ∨ 1 ∈ (List.finRange k).map (chkVal (lblOf e J) lab))) ↔
        ∀ i, chkVal (lblOf e J) lab i = 0 := by
      simp only [List.mem_map, List.mem_finRange, true_and, not_or, not_exists]
      constructor
      · rintro ⟨-, h⟩ i; have := h i; have := chkVal_le_one (lblOf e J) lab i; omega
      · intro h; exact ⟨by omega, fun i => by rw [h i]; omega⟩
    have hite : ((if 0 = 1 ∨ 1 ∈ (List.finRange k).map (chkVal (lblOf e J) lab) then 1 else 0) = 0)
        ↔ ¬ (0 = 1 ∨ 1 ∈ (List.finRange k).map (chkVal (lblOf e J) lab)) := by
      by_cases hc : (0 = 1 ∨ 1 ∈ (List.finRange k).map (chkVal (lblOf e J) lab))
      · rw [if_pos hc]; exact ⟨fun h => absurd h one_ne_zero, fun h => absurd hc h⟩
      · rw [if_neg hc]; exact ⟨fun _ => hc, fun _ => rfl⟩
    rw [hite, hall]
    refine chk_iff_fibers e J (lblOf e J) lab (fun i hi => ?_) (fun i hi => ?_) (fun v w => ?_)
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp ((J.card ⟨_, hi⟩).trans hh)
      refine ⟨a, ha, ?_⟩
      unfold lblOf
      rw [dif_pos hi, findIdx_indicator a _ (fun t => by simp [ha])]
    · unfold lblOf; rw [dif_neg hi]
    · exact (hlabO (e v) (e w)).trans (kerRel_iff_orbit e L.toGiantLabels hK v w).symm
  · -- bounds on the pieces, in terms of `T`
    clear dtail d1 d2 d3 d3a hchk hmax hmap drange dblk dK dV3 dK3 dV5 dV4 hO hlabO hK hπ hgen
    have hAw : (Val.list [sv, lv]).wt = A.wt := rfl
    clear_value T E3 E2 E
    have hAk : 2 ≤ T := by omega
    have hkT : k + 2 ≤ T := by omega
    have hqT : L.q + 2 ≤ T := by omega
    have hwA : A.wt + 2 ≤ T := by omega
    have hlenT : hs.length + 1 ≤ T ^ 2 := by
      have : k ^ 2 + 1 ≤ T ^ 2 := by nlinarith
      omega
    have hp1 : (hs.length + 1) * (k + 1) ≤ T ^ 3 := by
      calc (hs.length + 1) * (k + 1) ≤ T ^ 2 * T := Nat.mul_le_mul hlenT (by omega)
        _ = T ^ 3 := by ring
    have a1 : (Val.list (hs.map encPerm)).wt ≤ 13 * T ^ 6 := by
      have := wt_list_encPerms_le hs
      have h2 : ((hs.length + 1) * (k + 1)) ^ 2 ≤ (T ^ 3) ^ 2 := Nat.pow_le_pow_left hp1 2
      rw [show (T ^ 3) ^ 2 = T ^ 6 by ring] at h2
      omega
    have a2 : ((hs.length + 1) * (k + 1)) ^ 5 ≤ T ^ 15 := by
      have h2 : ((hs.length + 1) * (k + 1)) ^ 5 ≤ (T ^ 3) ^ 5 := Nat.pow_le_pow_left hp1 5
      rwa [show (T ^ 3) ^ 5 = T ^ 15 by ring] at h2
    have hT1 : T + 1 ≤ 2 * T := by omega
    have hsq : (T + 1) ^ 2 ≤ 4 * T ^ 2 := by
      have : (T + 1) ^ 2 ≤ (2 * T) ^ 2 := Nat.pow_le_pow_left hT1 2
      rwa [show (2 * T) ^ 2 = 4 * T ^ 2 by ring] at this
    have a3 : (encFun lab).wt ≤ 20 * T ^ 2 := by
      have := wt_encFun_le' lab (B := T) (fun i => by have := hlabk i; omega) (by omega)
      omega
    have a5 : (encFun (lblOf e J)).wt ≤ 20 * T ^ 2 := by
      have := wt_encFun_le' (lblOf e J) (B := T) (fun i => by have := lblOf_le e J i; omega)
        (by omega)
      omega
    have a4 : (blkMapVal e J).wt + 2 ≤ T := by
      have h1 : lv.wt < A.wt := wt_le_wt_list (vs := [sv, lv]) (by simp)
      have h2 : (blkMapVal e J).wt < lv.wt := by
        rw [hlvE, hJ]; exact wt_le_wt_list (by simp)
      omega
    rw [← hblk] at *
    have a7 : (Val.list ((List.finRange k).map fun i : Fin k => Val.nat (i : ℕ))).wt ≤ 4 * T ^ 2 := by
      have := wt_encPerm_le (1 : Perm (Fin k))
      rw [hone] at this
      have : (k + 1) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have a8 : (Val.list ((List.finRange k).map fun i => Val.nat (chkVal (lblOf e J) lab i))).wt ≤
        7 * T := by
      have := wt_encFun_le (chkVal (lblOf e J) lab) (B := 1) (chkVal_le_one _ _)
      have e8 : encFun (chkVal (lblOf e J) lab) =
        .list ((List.finRange k).map fun i => Val.nat (chkVal (lblOf e J) lab i)) := rfl
      rw [e8] at this
      omega
    have a9 : (Val.nat (List.foldl max 0 (List.map (chkVal (lblOf e J) lab)
        (List.finRange k)))).wt ≤ 3 := by
      rw [foldl_max_01 _ 0 (by omega) (fun x hx => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact chkVal_le_one _ _ i)]
      split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
    have hp2 : T ≤ T ^ 2 := Nat.le_self_pow (by norm_num) _
    -- the list weights
    have w1 := wt_list2_le (.nat k) (.list (hs.map encPerm))
    have w2 := wt_list2_le (.nat 0) (blkMapVal e J)
    have w3 := wt_list2_le (encFun (lblOf e J)) (encFun lab)
    have w4 := wt_list2_le (.list [encFun (lblOf e J), encFun lab])
      (.list ((List.finRange k).map fun i : Fin k => Val.nat (i : ℕ)))
    have wk := wt_nat_le k
    have w0 : (Val.nat 0).wt ≤ 3 := by simp [wt_nat, GI.Machine.len_zero]
    -- the products
    have m1 : (k + 1) * ((Val.list [Val.nat 0, blkMapVal e J]).wt + (encFun (lblOf e J)).wt + 1)
        ≤ 30 * T ^ 3 := mul_le_c_pow (i := 2) (by omega) (by omega)
    have m2 : k * (natStepK * (L.q + 2) ^ 3) ≤ natStepK * T ^ 4 := by
      have : (L.q + 2) ^ 3 ≤ T ^ 3 := Nat.pow_le_pow_left hqT 3
      have := mul_le_c_pow (a := k) (x := natStepK * (L.q + 2) ^ 3) (T := T) (c := natStepK)
        (i := 3) (by omega) (Nat.mul_le_mul_left _ this)
      exact this
    have m3 : (k + 1) * ((Val.list [Val.list [encFun (lblOf e J), encFun lab],
        Val.list ((List.finRange k).map fun i : Fin k => Val.nat (i : ℕ))]).wt +
        (Val.list ((List.finRange k).map fun i => Val.nat (chkVal (lblOf e J) lab i))).wt + 1)
        ≤ 300 * T ^ 3 := mul_le_c_pow (i := 2) (by omega) (by omega)
    have m4 : k * (natStepK * (T + 2) ^ 3) ≤ 8 * natStepK * T ^ 4 := by
      have h8 : (T + 2) ^ 3 ≤ 8 * T ^ 3 := by
        have : (T + 2) ^ 3 ≤ (2 * T) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        rwa [show (2 * T) ^ 3 = 8 * T ^ 3 by ring] at this
      have hx : natStepK * (T + 2) ^ 3 ≤ 8 * natStepK * T ^ 3 := by
        rw [show 8 * natStepK * T ^ 3 = natStepK * (8 * T ^ 3) by ring]
        exact Nat.mul_le_mul_left _ h8
      exact mul_le_c_pow (a := k) (i := 3) (by omega) hx
    have c1 : (k + 1) ^ 3 ≤ T ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have c2 : (k + 1 + 1) ^ 3 ≤ T ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have p3 : T ^ 2 ≤ T ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have p4 : T ^ 3 ≤ T ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have p6 : T ^ 4 ≤ T ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have p15 : T ^ 6 ≤ T ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
    have p16 : T ^ 15 ≤ T ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
    have x1 := Nat.mul_le_mul_left mapK m1
    have x3 := Nat.mul_le_mul_left mapK m3
    have x2 := Nat.mul_le_mul_left orbitK a2
    clear hlabB hlvE
    simp only [List.length_finRange] at *
    rw [Nat.mul_assoc mapK, Nat.mul_assoc mapK]
    simp only [natTailK, mapK, orbitK, natStepK, maxK] at *
    omega

/-! ### The whole test -/

theorem wt_q_nil_le {q T : ℕ} (hqT : q + 2 ≤ T) : (Val.list [Val.nat q, Val.list []]).wt ≤ 2 * T + 20 := by
  have h1 := wt_list2_le (.nat q) (.list [])
  have h2 : (Val.list []).wt ≤ 5 := by have := wt_list_le ([] : List Val); simpa using this
  have h3 := wt_nat_le q
  omega

/-- The cell bound of the preimage call. -/
def natPB (T : ℕ) : ℕ := 1000 * T ^ 6

/-- The constant of the test besides the preimage call. -/
def natCostK : ℕ := 2 * 10 ^ 16

set_option maxHeartbeats 1600000 in
/-- **The natural-map test.** On `[sv, lv]`, with `sv` a list starting with `k` and `lv` the value
of the supplied labels with block size `h = 1`, every run returns a number `t` that is `0`
exactly when the kernel of `π` is transitive on each block fiber, at cost at most one preimage
bound plus `natCostK * T ^ 16`, `T = wt [sv, lv] + k + q + 2`. -/
theorem natTest_spec (hpre : GI.Cited.Preimage) {P : Program} {b jpre : ℕ} (hb : NatAt P b jpre)
    (hj : P.prims[jpre]? = some (preimagePrim hpre)) (e : Ω ≃ Fin k) {S : State Ω C}
    (L : SuppliedLabels S) {sv lv : Val} {svs : List Val} (hsv : sv = .list svs)
    (hk : svs[0]? = some (.nat k)) (hlv : LabValStd e S lv L) (hh : L.con.blocks.h = 1)
    (hq : 1 ≤ L.q) :
    FunAll P b (.list [sv, lv]) (fun w c => ∃ t, w = .nat t ∧ t ≤ 1 ∧
      (t = 0 ↔ ∀ v w : S.dom, L.con.blocks.p v = L.con.blocks.p w →
        KerRel S L.toGiantLabels v w) ∧
      c ≤ (preimagePrim hpre).boundSize (natPB ((Val.list [sv, lv]).wt + k + L.q + 2)) +
        natCostK * ((Val.list [sv, lv]).wt + k + L.q + 2) ^ 16) := by
  have hlv' := hlv
  obtain ⟨ps, hlvE, hlen, hgen, hπ⟩ := hlv
  set A := Val.list [sv, lv] with hA
  set T := A.wt + k + L.q + 2 with hT
  refine FunAll.intro hb.entry ?_
  unfold natEntry
  -- the graph generators
  have hmap := mapList_spec hb.graphMap ps (fun p => .list [encPerm p.1, encPerm p.2])
    (fun p => encPerm (sumToFin (Perm.sumCongr p.1 p.2))) (c := .nat k)
    (B := natStepK * (k + L.q + 1) ^ 3)
    (fun p _ p' _ he => by rw [pairVal_injective he])
    (fun p _ => graphStep_spec hb.shiftApp hb.append hb.addMap hb.addK hb.graphStep p.1 p.2)
  have dpairs := natLVget_det (P := P) (sv := sv) [] hlvE (i := 1)
    (u := .list (ps.map fun p => .list [encPerm p.1, encPerm p.2])) rfl
  have dG1 := Det.call (Det.mk2 (natK_det (P := P) (lv := lv) [] hsv hk) dpairs) hmap
  set gl := Val.list (ps.map fun p => encPerm (sumToFin (Perm.sumCongr p.1 p.2))) with hgl
  have hgl' : gl = .list (((kerInst ps).ds.map sumToFin).map encPerm) := by
    simp [hgl, kerInst, List.map_map, Function.comp_def]
  refine EvalAll.letE dG1 fun v1 c1 h1 => ?_
  obtain ⟨rfl, hc1⟩ := h1
  -- the graph group
  have dQ1 := natLVget_det (P := P) (sv := sv) [gl] hlvE (i := 0) (u := .nat L.q) rfl
  have dadd := Det.arith' (op := .add) (natK_det (P := P) (lv := lv) [gl] hsv hk) dQ1
    (z := k + L.q) rfl
  have dV1 := Det.var' (P := P) (env := [A, gl]) (i := 1)
    (v := .list (((kerInst ps).ds.map sumToFin).map encPerm)) (by rw [← hgl']; rfl)
  have dG2 := Det.call (Det.mk2 dadd dV1)
    (mkGroup_spec (n := k + L.q) hb.mkGroup ((kerInst ps).ds.map sumToFin))
  refine EvalAll.letE dG2 fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  -- the preimage call
  set gg := encGroup ((kerInst ps).ds.map sumToFin) with hgg
  have dK2 := natK_det (P := P) (lv := lv) [gl, gg] hsv hk
  have dV2 := Det.var' (P := P) (env := [A, gl, gg]) (i := 2) (v := gg) rfl
  have dQ2 := natLVget_det (P := P) (sv := sv) [gl, gg] hlvE (i := 0) (u := .nat L.q) rfl
  have dE := Det.call (Det.mk2 dQ2 (Det.nil (P := P) (env := [A, gl, gg])))
    (mkGroup_spec (n := L.q) hb.mkGroup [])
  have darg := Det.mk3 dK2 dV2 dE
  have hI : Val.list [.nat k, gg, encGroup ([] : List (Perm (Fin L.q)))] =
      preimageEnc (kerInst ps) := rfl
  rw [hI] at darg
  refine EvalAll.letE (preimage_call hpre (kerInst ps) hj darg) fun w cw hw => ?_
  obtain ⟨⟨hs, rfl, hlen', hgens⟩, hcw⟩ := hw
  have hK : ∀ g, g ∈ gens hs ↔ ∃ h : (toFin e).symm g ∈ S.G, L.π ⟨_, h⟩ = 1 := fun g => by
    rw [hgens]; exact mem_kerInst e L.toGiantLabels hgen hπ g
  obtain ⟨t, ht1, ht, dT⟩ := natTail_det hb e L hsv hk hlv' hh hq hlen' hK gl gg
  refine dT.post fun c hc => ⟨t, rfl, ht1, ht, ?_⟩
  -- the cost
  have hAw : (Val.list [sv, lv]).wt = A.wt := rfl
  rw [hAw] at hc hc1 hc2 hcw
  rw [← hT] at hc
  clear dT dG1 dG2 darg dE dV2 dK2 dQ2 dV1 dadd dQ1 dpairs hmap hK
  clear_value T gg gl
  have hkT : k + 2 ≤ T := by omega
  have hqT : L.q + 2 ≤ T := by omega
  have hwT : A.wt + 2 ≤ T := by omega
  have hp2 : T ≤ T ^ 2 := Nat.le_self_pow (by norm_num) _
  have hlenT : ps.length + 2 ≤ T ^ 2 := by
    have : k ^ 2 + 2 ≤ T ^ 2 := by nlinarith
    omega
  have hds : (kerInst ps).ds.length = ps.length := by simp [kerInst]
  have hds' : ((kerInst ps).ds : List (Perm (Fin k ⊕ Fin L.q))).length = ps.length := hds
  rw [← hgl'] at hc2
  set_option backward.isDefEq.respectTransparency false in
    rw [List.length_map] at hc2
  erw [hds'] at hc2
  have wt0 : (Val.nat t).wt ≤ 3 := by have := wt_nat_le t; omega
  have wpairs : (Val.list (ps.map fun p => Val.list [encPerm p.1, encPerm p.2])).wt + 2 ≤ T := by
    have h1 : lv.wt < A.wt := wt_le_wt_list (vs := [sv, lv]) (by simp)
    have h2 : (Val.list (ps.map fun p => Val.list [encPerm p.1, encPerm p.2])).wt < lv.wt := by
      rw [hlvE]; exact wt_le_wt_list (by simp)
    omega
  have hT1 : (k + L.q + 1) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have wgl : gl.wt ≤ 10 * T ^ 4 := by
    rw [hgl]
    have := wt_list_map_le ps (fun p => encPerm (sumToFin (Perm.sumCongr p.1 p.2)))
      (W := 4 * T ^ 2) (fun p _ => (wt_encPerm_le _).trans (by omega))
    have h4 : ps.length * (2 * (4 * T ^ 2) + 1) ≤ T ^ 2 * (9 * T ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have : T ^ 2 * (9 * T ^ 2) = 9 * T ^ 4 := by ring
    have : 2 ^ 4 ≤ T ^ 4 := Nat.pow_le_pow_left (by omega) 4
    omega
  have hp3 : (ps.length + 2) * (k + L.q + 1) ≤ T ^ 3 := by
    calc (ps.length + 2) * (k + L.q + 1) ≤ T ^ 2 * T := Nat.mul_le_mul hlenT (by omega)
      _ = T ^ 3 := by ring
  have h6 : ((ps.length + 2) * (k + L.q + 1)) ^ 2 ≤ T ^ 6 := by
    have h2 : ((ps.length + 2) * (k + L.q + 1)) ^ 2 ≤ (T ^ 3) ^ 2 := Nat.pow_le_pow_left hp3 2
    rwa [show (T ^ 3) ^ 2 = T ^ 6 by ring] at h2
  have wgg' : (encGroup (n := k + L.q) ((kerInst ps).ds.map sumToFin)).wt ≤ 40 * T ^ 6 := by
    have := wt_encGroup_le (n := k + L.q) ((kerInst ps).ds.map sumToFin)
    set_option backward.isDefEq.respectTransparency false in
      rw [List.length_map] at this
    erw [hds'] at this
    omega
  have wgg : gg.wt ≤ 40 * T ^ 6 := by
    rw [hgg]
    have := wt_encGroup_le ((kerInst ps).ds.map sumToFin)
    set_option backward.isDefEq.respectTransparency false in
      rw [List.length_map] at this
    erw [hds'] at this
    exact this.trans (Nat.mul_le_mul_left _ h6)
  have hm9 : ((ps.length + 2) * (k + L.q + 1)) ^ 3 ≤ T ^ 9 := by
    have h2 := Nat.pow_le_pow_left hp3 3
    rwa [show (T ^ 3) ^ 3 = T ^ 9 by ring] at h2
  have h2T : ((([] : List (Perm (Fin L.q))).length + 2) * (L.q + 1)) ≤ 2 * T := by
    simp only [List.length_nil, zero_add]; omega
  have we0 : (encGroup ([] : List (Perm (Fin L.q)))).wt ≤ 160 * T ^ 2 := by
    have := wt_encGroup_le ([] : List (Perm (Fin L.q)))
    have h2 := Nat.pow_le_pow_left h2T 2
    rw [show (2 * T) ^ 2 = 4 * T ^ 2 by ring] at h2
    omega
  have hm3 : ((([] : List (Perm (Fin L.q))).length + 2) * (L.q + 1)) ^ 3 ≤ 8 * T ^ 3 := by
    have h2 := Nat.pow_le_pow_left h2T 3
    rwa [show (2 * T) ^ 3 = 8 * T ^ 3 by ring] at h2
  have wk := wt_nat_le k
  have wq := wt_nat_le L.q
  have wkq := wt_nat_le (k + L.q)
  have w1 := wt_list2_le (.nat k) (.list (ps.map fun p => Val.list [encPerm p.1, encPerm p.2]))
  have w2 := wt_list2_le (.nat (k + L.q)) gl
  have w3 := wt_q_nil_le hqT
  have p6 : T ^ 2 ≤ T ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p46 : T ^ 4 ≤ T ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p36 : T ^ 3 ≤ T ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p69 : T ^ 6 ≤ T ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  have p916 : T ^ 9 ≤ T ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
  have p5 : T ^ 5 ≤ T ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p14 : T ≤ T ^ 4 := Nat.le_self_pow (by norm_num) _
  -- the preimage argument
  have wpe : (preimageEnc (kerInst ps)).wt ≤ natPB T := by
    have := wt_list3_le (.nat k) gg (encGroup ([] : List (Perm (Fin L.q))))
    have he : preimageEnc (kerInst ps) =
        .list [.nat k, gg, encGroup ([] : List (Perm (Fin L.q)))] := by rw [hgg]; rfl
    rw [he]; unfold natPB; omega
  have hbd := (preimagePrim hpre).bound_le ((preimageEnc (kerInst ps)).size_le_wt.trans wpe)
  have hn : (kerInst ps).n = k := rfl
  rw [hn] at hcw
  have hk6 : (k + 1) ^ 6 ≤ T ^ 6 := Nat.pow_le_pow_left (by omega) 6
  -- the products
  have m1 : ps.length * (natStepK * (k + L.q + 1) ^ 3) ≤ natStepK * T ^ 5 := by
    have h3 : (k + L.q + 1) ^ 3 ≤ T ^ 3 := Nat.pow_le_pow_left (by omega) 3
    calc ps.length * (natStepK * (k + L.q + 1) ^ 3) ≤ T ^ 2 * (natStepK * T ^ 3) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ h3)
      _ = natStepK * T ^ 5 := by ring
  have m2 : (ps.length + 1) * ((Val.list [Val.nat k,
      Val.list (ps.map fun p => Val.list [encPerm p.1, encPerm p.2])]).wt + gl.wt + 1) ≤
      20 * T ^ 6 := by
    calc _ ≤ T ^ 2 * (20 * T ^ 4) := Nat.mul_le_mul (by omega) (by omega)
      _ = 20 * T ^ 6 := by ring
  have x2 := Nat.mul_le_mul_left mapK m2
  have x3 := Nat.mul_le_mul_left mkGroupK hm9
  have x4 := Nat.mul_le_mul_left mkGroupK hm3
  rw [Nat.mul_assoc mapK] at hc1
  clear hlvE hgen hπ hlv' ht hgl hgg hgl'
  simp only [natCostK, natTailK, mapK, mkGroupK, natStepK, natPB] at *
  omega

end GI.Impl
