module

public import Workspace.Impl.TermJVecMath

@[expose] public section

/-!
# The coordinate vector of one element of `A = N / N*` (program)

`tmJVVecF`: on `[encGroup ns, encGroup as, encPerm x]` with `x ∈ ⟨as⟩`, return an integer vector
`z` whose image under the coordinate map of `LinPermCertificate.lean` is the class of `x`.

The program has three steps.
1. Build the generator list `ns ++ as` (the prefix program `linPrefixF` with prefix length
   `as.length`).
2. Build the table of zero vectors for `ns` and unit vectors for `as` (`linAssignF`).
3. Run constructive membership of `x` in `⟨ns ++ as⟩` and interpret the returned straight-line
   program on the table (`linCoordinateWitnessF`).
By `tmJV_class` the resulting vector is correct. The cost is polynomial in the input weight
(`tmJV_vec_spec_poly`). The only primitive used is constructive membership, at index `jm`.
-/

namespace GI.Impl
open GI.Cited GI.Lang
open scoped IsMulCommutative

/-! ### The program -/

/-- The main function: prefix, table, witness, and the vector part of the witness output. -/
def tmJVVecF (pref assign wit : ℕ) : Expr :=
  .letE (.call pref (mk3 (arg 0) (arg 1) (linPrepCountE 1)))
    (.letE (.call assign (mk3 (linPrepCountE 1) (linPrepCountE 0) (linPrepCountE 1)))
      (.letE (.call wit (mk3 (mk2 (.var 1) (arg 2)) (.var 2) (.nat 0)))
        (.get (.var 3) (.nat 1))))

/-- The functions, in order: main, prefix, table, the library modules of the prefix and of
the table, and the witness block. They sit at `b, …, b + 51`. -/
def tmJVVecFuns (b jm : ℕ) : List Expr :=
  [tmJVVecF (b + 1) (b + 2) (b + 21), linPrefixF (b + 3) (b + 6) (b + 9),
    linAssignF (b + 12) (b + 15)] ++
    linTailFuns (b + 3) ++ linTakeFuns (b + 6) ++ appendFuns (b + 9) ++
    replicateFuns (b + 12) ++ linAssignUnitFuns (b + 15) (b + 18) ++ linBasisFuns (b + 18) ++
    linCoordinateWitnessFuns (b + 21) jm

theorem tmJVVecFuns_length (b jm : ℕ) : (tmJVVecFuns b jm).length = 52 := rfl

/-- Where the pieces sit. -/
structure TmJVVecAt (P : Program) (b jm : ℕ) (hm : ConstructiveMembership) : Prop where
  main : P.funs[b]? = some (tmJVVecF (b + 1) (b + 2) (b + 21))
  pref : P.funs[b + 1]? = some (linPrefixF (b + 3) (b + 6) (b + 9))
  assign : P.funs[b + 2]? = some (linAssignF (b + 12) (b + 15))
  tail : P.HasAt (b + 3) (linTailFuns (b + 3))
  take : P.HasAt (b + 6) (linTakeFuns (b + 6))
  append : P.HasAt (b + 9) (appendFuns (b + 9))
  rep : P.HasAt (b + 12) (replicateFuns (b + 12))
  units : P.HasAt (b + 15) (linAssignUnitFuns (b + 15) (b + 18))
  basis : P.HasAt (b + 18) (linBasisFuns (b + 18))
  wit : linWitnessAt P (b + 21) jm hm

/-- The functions at `b` and the membership primitive at `jm` give `TmJVVecAt`. -/
theorem TmJVVecAt.of_hasAt {P : Program} {b jm : ℕ} {hm : ConstructiveMembership}
    (h : P.HasAt b (tmJVVecFuns b jm)) (hj : P.prims[jm]? = some (linMembershipPrim hm)) :
    TmJVVecAt P b jm hm where
  main := (h.block (gs := [tmJVVecF (b + 1) (b + 2) (b + 21)]) 0 rfl).single
  pref := (h.block (gs := [linPrefixF (b + 3) (b + 6) (b + 9)]) 1 rfl).single
  assign := (h.block (gs := [linAssignF (b + 12) (b + 15)]) 2 rfl).single
  tail := h.block 3 rfl
  take := h.block 6 rfl
  append := h.block 9 rfl
  rep := h.block 12 rfl
  units := h.block 15 rfl
  basis := h.block 18 rfl
  wit := linCoordinateWitnessAt_of (h.block 21 rfl) hj

/-! ### Cost bounds, all in the input weight `W` -/

/-- A bound on the cost of the prefix step, and on the weight of its output. -/
def tmJVPrefCost (W : ℕ) : ℕ := linPrefixCost (10 * (W + 1))

/-- A bound on the cost of the table step, and on the weight of its output. -/
def tmJVAssignCost (W : ℕ) : ℕ := linAssignCost (10 * (W + 1)) W W W

/-- A bound on the weight of the membership input `[encGroup (ns ++ as), encPerm x]`. -/
def tmJVMemberWt (W : ℕ) : ℕ := 10 * (tmJVPrefCost W + W + 1)

/-- A bound on the weight of the witness input. -/
def tmJVWitArg (W : ℕ) : ℕ := 100 * (tmJVPrefCost W + tmJVAssignCost W + W + 1)

/-- A bound on the weight of the membership output. -/
noncomputable def tmJVMemberOut (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  400 * (tmJVMemberWt W ^ linMembershipDegree hm + 1) *
    (2 * W + tmJVMemberWt W ^ linMembershipDegree hm + 2) + 100

/-- A bound on the cost of the witness step. -/
noncomputable def tmJVWitCost (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  1000 * (tmJVWitArg W + W + ((linMembershipPrim hm).boundSize (tmJVMemberWt W) +
    tmJVMemberWt W + tmJVMemberOut hm W + 2) + tmJVMemberOut hm W +
    linSlpValueCost (10 * (tmJVWitArg W + tmJVMemberOut hm W + 1))
      (tmJVMemberWt W ^ linMembershipDegree hm) W + 1)

/-- The cost bound of `tmJVVecF`. -/
noncomputable def tmJVVecCost (hm : ConstructiveMembership) (W : ℕ) : ℕ :=
  1000 * (W + tmJVPrefCost W + tmJVAssignCost W + tmJVWitCost hm W + 1)

theorem tmJV_prefixCost_mono {W V : ℕ} (h : W ≤ V) : linPrefixCost W ≤ linPrefixCost V := by
  unfold linPrefixCost; gcongr

theorem tmJV_assignCost_mono {W V t s ns ms i j : ℕ} (hW : W ≤ V) (ht : t ≤ s) (hn : ns ≤ ms)
    (hi : i ≤ j) : linAssignCost W t ns i ≤ linAssignCost V s ms j := by
  simp only [linAssignCost, linAssignRepCost, linAssignZeroWt, linAssignInitWt,
    linAssignUnitsArg, linAssignUnitCost, linAssignUnitStepCost, linAssignUnitAccWt,
    linAssignUnitBasisCost, linAssignUnitBasisArg, linBasisCost, linVectorAccWt]
  gcongr

/-- The witness cost for a membership instance of bounded size. -/
theorem tmJV_witCost_le (hm : ConstructiveMembership) (I : MemberInst) {W C t : ℕ}
    (hI : (memberInput I).wt ≤ tmJVMemberWt W) (hg : I.gs.length ≤ 2 * W) (ht : t ≤ W)
    (hC : C ≤ tmJVWitArg W) :
    linCoordinateWitnessCost hm I C t ≤ tmJVWitCost hm W := by
  have hs : (memberInput I).cells.length ≤ tmJVMemberWt W := (memberInput I).size_le_wt.trans hI
  have hout : linMembershipWt (linMembershipDegree hm) I ≤ tmJVMemberOut hm W := by
    change 400 * (((memberInput I).cells.length ^ linMembershipDegree hm) + 1) *
      (I.gs.length + (memberInput I).cells.length ^ linMembershipDegree hm + 2) + 100 ≤
      400 * (tmJVMemberWt W ^ linMembershipDegree hm + 1) *
        (2 * W + tmJVMemberWt W ^ linMembershipDegree hm + 2) + 100
    have hp := Nat.pow_le_pow_left hs (linMembershipDegree hm)
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hp 1)
    · omega
  have hcall : linMembershipCost hm I ≤ (linMembershipPrim hm).boundSize (tmJVMemberWt W) +
      tmJVMemberWt W + tmJVMemberOut hm W + 2 := by
    have hp := (linMembershipPrim hm).bound_le hs
    unfold linMembershipCost
    omega
  have he := linSlpValueCost_mono_all
    (by omega : 10 * (C + linMembershipWt (linMembershipDegree hm) I + 1) ≤
      10 * (tmJVWitArg W + tmJVMemberOut hm W + 1))
    (Nat.pow_le_pow_left hs (linMembershipDegree hm)) ht
  unfold linCoordinateWitnessCost tmJVWitCost
  omega

/-- The degree and the two generator counts are bounded by the input weight. -/
theorem tmJV_source_bounds {n : ℕ} (ns as : List (Equiv.Perm (Fin n))) (x : Equiv.Perm (Fin n)) :
    n + 1 ≤ (Val.list [encGroup ns, encGroup as, encPerm x]).wt ∧
      ns.length + 2 ≤ (Val.list [encGroup ns, encGroup as, encPerm x]).wt ∧
      as.length + 2 ≤ (Val.list [encGroup ns, encGroup as, encPerm x]).wt := by
  have wn := S_le_wt_encGroup ns
  have wa := S_le_wt_encGroup as
  have wns : (encGroup ns).wt < (Val.list [encGroup ns, encGroup as, encPerm x]).wt :=
    wt_le_wt_list (by simp)
  have was : (encGroup as).wt < (Val.list [encGroup ns, encGroup as, encPerm x]).wt :=
    wt_le_wt_list (by simp)
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- The count `gs.length` read from `encGroup gs` at position `j` of the argument. -/
theorem tmJV_count {P : Program} {vs rest : List Val} (j : ℕ) {n : ℕ}
    (gs : List (Equiv.Perm (Fin n))) (hj : vs[j]? = some (encGroup gs)) :
    Det P (.list vs :: rest) (linPrepCountE j) (.nat gs.length) (6 * (Val.list vs).wt + j + 30) := by
  have da : Det P (.list vs :: rest) (arg j) (.list [.nat n, .list ((1 :: gs).map encPerm)])
      (2 * (Val.list vs).wt + j + 5) := Det.arg' hj
  have dl := Det.length (Det.get' da (Det.nat 1)
    (show [Val.nat n, .list ((1 :: gs).map encPerm)][1]? = some (.list ((1 :: gs).map encPerm))
      from rfl))
  have d := Det.arith' (op := .sub) dl (Det.nat 1)
    (show GI.Machine.BinOp.eval .sub ((1 :: gs).map encPerm).length 1 = gs.length by simp)
  refine d.mono ?_
  have w1 : (encGroup gs).wt < (Val.list vs).wt := wt_le_wt_list (List.mem_of_getElem? hj)
  have w2 : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
    wt_le_wt_list (by simp)
  have w3 := length_lt_wt_list ((1 :: gs).map encPerm)
  simp only [List.length_map, List.length_cons] at w3 ⊢
  omega

/-! ### The specification -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- **The coordinate vector of one element.** On `[encGroup ns, encGroup as, encPerm x]` with
`x ∈ ⟨as⟩`, every run returns `linVecVal z` for a vector `z` whose image under the coordinate
map is the class of `x` in `⟨as⟩ / ⟨ns⟩`. -/
theorem tmJV_vec_spec (hm : ConstructiveMembership) {P : Program} {b jm n : ℕ}
    (h : TmJVVecAt P b jm hm) (ns as : List (Equiv.Perm (Fin n))) (hle : gens ns ≤ gens as)
    [((gens ns).subgroupOf (gens as)).Normal]
    [IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as))]
    (x : Equiv.Perm (Fin n)) (hx : x ∈ gens as) :
    FunAll P b (.list [encGroup ns, encGroup as, encPerm x]) (fun out cost =>
      (∃ z : Fin as.length → ℤ, out = linVecVal z ∧
        Additive.ofMul (QuotientGroup.mk' ((gens ns).subgroupOf (gens as)) ⟨x, hx⟩) =
          linCoordMap (fun i : Fin as.length => QuotientGroup.mk' ((gens ns).subgroupOf (gens as))
            (linIntoSubgroup (gens as) as[i.val])) z) ∧
      cost ≤ tmJVVecCost hm (Val.list [encGroup ns, encGroup as, encPerm x]).wt) := by
  let vs := [encGroup ns, encGroup as, encPerm x]
  let a := Val.list vs
  let W := a.wt
  let t := as.length
  let s := ns.length
  let g := encGroup (ns ++ as)
  let vecs := linPrefixVectors t s t
  let tab := Val.list [.list (vecs.map linVecVal), linVecVal (0 : Fin t → ℤ)]
  let I : MemberInst := ⟨n, ns ++ as, x⟩
  obtain ⟨hn, hs, ht⟩ := tmJV_source_bounds ns as x
  change n + 1 ≤ W at hn
  change s + 2 ≤ W at hs
  change t + 2 ≤ W at ht
  have wS : (encGroup ns).wt < W := wt_le_wt_list (by simp [vs])
  have wN : (encGroup as).wt < W := wt_le_wt_list (by simp [vs])
  have wX : (encPerm x).wt < W := wt_le_wt_list (by simp [vs])
  -- the prefix step
  have hg := linPrefix_spec h.pref h.tail h.take h.append ns as t le_rfl
  rw [List.take_length] at hg
  have wpa := wt_list3_le (encGroup ns) (encGroup as) (.nat t)
  have wt' := wt_nat_le t
  have hg' := hg.mono (tmJV_prefixCost_mono (show (Val.list [encGroup ns, encGroup as, .nat t]).wt ≤
    10 * (W + 1) by omega))
  have wg : g.wt ≤ tmJVPrefCost W := hg'.wt_lt.le
  -- the table step
  have hA := linAssign_spec h.assign h.rep h.units h.basis t s t le_rfl
  have waa := wt_list3_le (.nat t) (.nat s) (.nat t)
  have ws' := wt_nat_le s
  have hA' := hA.mono (tmJV_assignCost_mono (show (Val.list [.nat t, .nat s, .nat t]).wt ≤
    10 * (W + 1) by omega) (show t ≤ W by omega) (show s ≤ W by omega) (show t ≤ W by omega))
  have wtab : tab.wt ≤ tmJVAssignCost W := hA'.wt_lt.le
  -- the witness step
  have hmem : I.x ∈ gens I.gs :=
    Subgroup.closure_mono (fun y (hy : y ∈ as) => List.mem_append_right ns hy) hx
  have hlen : I.gs.length = vecs.length := by
    simp [I, vecs, linPrefixVectors, t, s]
  have hw := linCoordinateWitness_spec hm h.wit.entry h.wit.member h.wit.prim h.wit.exponent
    h.wit.table h.wit.step h.wit.ints h.wit.add h.wit.scale I hmem vecs hlen
    (linPrefixVectors_bound _ _ _) (.nat 0)
  have wmi := wt_list2_le g (encPerm x)
  have hmw : (memberInput I).wt ≤ tmJVMemberWt W := by
    change (Val.list [g, encPerm x]).wt ≤ _
    unfold tmJVMemberWt; omega
  have hgl : I.gs.length ≤ 2 * W := by
    simp only [I, List.length_append]; omega
  have wwa := wt_list3_le (memberInput I) tab (.nat 0)
  have w0 : (Val.nat 0).wt = 2 := rfl
  have hwarg : (Val.list [memberInput I, tab, .nat 0]).wt ≤ tmJVWitArg W := by
    unfold tmJVWitArg tmJVMemberWt at *; omega
  have hwc := (linCoordinateWitnessCost_mono hm I hwarg t).trans
    (tmJV_witCost_le hm I hmw hgl (by omega) le_rfl)
  -- the program
  have darg (j : ℕ) (rest : List Val) {v : Val} (hv : vs[j]? = some v) :=
    Det.arg' (P := P) (vs := vs) (rest := rest) (j := j) hv
  have d1 := Det.call (Det.mk3 (darg 0 [] rfl) (darg 1 [] rfl)
    (tmJV_count (P := P) (vs := vs) (rest := []) 1 as rfl)) hg'
  have d2 := Det.call (Det.mk3 (tmJV_count (P := P) (vs := vs) (rest := [g]) 1 as rfl)
    (tmJV_count (P := P) (vs := vs) (rest := [g]) 0 ns rfl)
    (tmJV_count (P := P) (vs := vs) (rest := [g]) 1 as rfl)) hA'
  have dwa : Det P [a, g, tab] (mk3 (mk2 (.var 1) (arg 2)) (.var 2) (.nat 0))
      (.list [memberInput I, tab, .nat 0]) _ :=
    Det.mk3 (Det.mk2 (Det.var' (P := P) (env := [a, g, tab]) (i := 1) rfl) (darg 2 [g, tab] rfl))
      (Det.var' (P := P) (env := [a, g, tab]) (i := 2) rfl) (Det.nat 0)
  apply FunAll.intro h.main
  apply EvalAll.letE d1
  rintro gv c1 ⟨rfl, hc1⟩
  apply EvalAll.letE d2
  rintro tv c2 ⟨rfl, hc2⟩
  apply EvalAll.letE (EvalAll.call_funAll dwa (Q := fun wv cw =>
      (∃ (prog : List SlpInstr) (z : Fin t → ℤ), wv = .list [.nat 0, linVecVal z] ∧
        SlpReaches I.gs prog I.x ∧ linExponentValue vecs prog = some z) ∧
      wv.wt ≤ tmJVWitCost hm W ∧ cw ≤ (2 * W + 10) * 100 + 6 * (Val.list [memberInput I, tab, .nat 0]).wt + 2 * g.wt +
        2 * tab.wt + 3 * tmJVWitCost hm W + 100) (fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    refine hw.wt_lt.mono fun out cost ho => ?_
    obtain ⟨⟨hres, hcost⟩, hwt⟩ := ho
    refine ⟨hres, ?_⟩
    have hmk := wt_list2_le (memberInput I) tab
    have hmk2 := wt_list2_le g (encPerm x)
    have hmlt : (memberInput I).wt < (Val.list [memberInput I, tab, .nat 0]).wt :=
      wt_le_wt_list (by simp)
    simp only [W, a, vs, t, s, g, vecs, tab, I, memberInput] at *
    constructor <;> omega))
  rintro wv c3 ⟨⟨prog, z, rfl, hreach, hz⟩, hwv, hc3⟩
  have dget := Det.get' (Det.var' (P := P) (env := [a, g, tab, .list [.nat 0, linVecVal z]])
    (i := 3) rfl) (Det.nat 1) (show [Val.nat 0, linVecVal z][1]? = some (linVecVal z) from rfl)
  refine dget.post fun c4 hc4 => ⟨⟨z, rfl, tmJV_class ns as hle x hx prog hreach z hz⟩, ?_⟩
  have wz : (linVecVal z).wt < (Val.list [.nat 0, linVecVal z]).wt := wt_le_wt_list (by simp)
  have wo := wt_list2_le (.nat 0) (linVecVal z)
  have wmk := wt_list2_le (memberInput I) tab
  change (Val.list [g, encPerm x]).wt ≤ _ at hmw
  have wenv1 := wt_list3_le (.nat t) (.nat s) (.nat t)
  unfold tmJVVecCost
  simp only [W, a, vs, t, s, g, vecs, tab, I, memberInput, tmJVPrefCost, tmJVAssignCost] at *
  omega

/-! ### Polynomial cost -/

theorem tmJVVecCost_poly (hm : ConstructiveMembership) :
    PBU (fun _ W _ => tmJVVecCost hm W) := by
  have hPC : PBU (fun _ W _ => tmJVPrefCost W) := by
    unfold tmJVPrefCost linPrefixCost; norm_poly
  have hAC : PBU (fun _ W _ => tmJVAssignCost W) := by
    simp only [tmJVAssignCost, linAssignCost, linAssignRepCost, linAssignZeroWt, linAssignInitWt,
      linAssignUnitsArg, linAssignUnitCost, linAssignUnitStepCost, linAssignUnitAccWt,
      linAssignUnitBasisCost, linAssignUnitBasisArg, linBasisCost, linVectorAccWt]
    norm_poly
  have hJ : PBU (fun _ W _ => tmJVMemberWt W) := PBU.smul 10 (PBU.addc (PBU.add hPC PBU.W) 1)
  have hC : PBU (fun _ W _ => tmJVWitArg W) :=
    PBU.smul 100 (PBU.addc (PBU.add (PBU.add hPC hAC) PBU.W) 1)
  have hMW : PBU (fun _ W _ => tmJVMemberOut hm W) :=
    PBU.addc (PBU.mul (PBU.smul 400 (PBU.addc (PBU.pow hJ (linMembershipDegree hm)) 1))
      (PBU.addc (PBU.add (PBU.smul 2 PBU.W) (PBU.pow hJ (linMembershipDegree hm))) 2)) 100
  have hB : PBU (fun _ W _ => (linMembershipPrim hm).boundSize (tmJVMemberWt W)) := by
    unfold Prim.boundSize
    exact PBU.smul _ (PBU.pow (PBU.addc hJ 2) _)
  have hslp := linPoly_subst linSlpValueCost_poly PBU.W
    (PBU.smul 10 (PBU.addc (PBU.add hC hMW) 1)) (PBU.pow hJ (linMembershipDegree hm))
  have hWC : PBU (fun _ W _ => tmJVWitCost hm W) :=
    PBU.smul 1000 (PBU.addc (PBU.add (PBU.add (PBU.add (PBU.add hC PBU.W)
      (PBU.addc (PBU.add (PBU.add hB hJ) hMW) 2)) hMW) hslp) 1)
  exact PBU.smul 1000 (PBU.addc (PBU.add (PBU.add (PBU.add PBU.W hPC) hAC) hWC) 1)

/-- A uniform bound `K * (W + 1) ^ D` from a `PBU` bound in `W` alone. -/
theorem tmJV_pbu_bound {f : ℕ → ℕ} (hf : PBU (fun _ W _ => f W)) :
    ∃ K D : ℕ, ∀ W, f W ≤ K * (W + 1) ^ D := by
  obtain ⟨K, D, hp⟩ := hf
  refine ⟨K * 2 ^ D, D, fun W => ?_⟩
  have hb := hp 0 W 0
  change f W ≤ K * (W + 0 + 0 + 2) ^ D at hb
  calc
    f W ≤ K * (W + 2) ^ D := by simpa using hb
    _ ≤ K * (2 * (W + 1)) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) D)
    _ = (K * 2 ^ D) * (W + 1) ^ D := by rw [mul_pow]; ring

/-- **The coordinate vector of one element, with a polynomial cost.** The constants depend only
on the cited membership algorithm. -/
theorem tmJV_vec_spec_poly (hm : ConstructiveMembership) :
    ∃ K D : ℕ, ∀ {P : Program} {b jm n : ℕ},
      P.HasAt b (tmJVVecFuns b jm) → P.prims[jm]? = some (linMembershipPrim hm) →
      ∀ (ns as : List (Equiv.Perm (Fin n))), gens ns ≤ gens as →
      ∀ [((gens ns).subgroupOf (gens as)).Normal]
        [IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as))]
        (x : Equiv.Perm (Fin n)) (hx : x ∈ gens as),
        FunAll P b (.list [encGroup ns, encGroup as, encPerm x]) (fun out cost =>
          (∃ z : Fin as.length → ℤ, out = linVecVal z ∧
            Additive.ofMul (QuotientGroup.mk' ((gens ns).subgroupOf (gens as)) ⟨x, hx⟩) =
              linCoordMap (fun i : Fin as.length =>
                QuotientGroup.mk' ((gens ns).subgroupOf (gens as))
                  (linIntoSubgroup (gens as) as[i.val])) z) ∧
          cost ≤ K * ((Val.list [encGroup ns, encGroup as, encPerm x]).wt + 1) ^ D) := by
  obtain ⟨K, D, hb⟩ := tmJV_pbu_bound (tmJVVecCost_poly hm)
  refine ⟨K, D, fun hl hj ns as hle _ _ x hx => ?_⟩
  exact (tmJV_vec_spec hm (TmJVVecAt.of_hasAt hl hj) ns as hle x hx).mono
    fun out cost ho => ⟨ho.1, ho.2.trans (hb _)⟩

end GI.Impl
