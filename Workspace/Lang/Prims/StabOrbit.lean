/-
**Example: the stabilizer and the orbit of a point.**

Given a group `G ≤ Sym(n)` by generators (`GroupVal`) and a point `α`, the program `stabOrbitFuns`
returns a pair: the group value of the stabilizer `G_α` and the list of the points of the orbit
`α^G`, in increasing order.
* The orbit is computed inside the language: `orbitFuns` labels each point by the least point of
  its orbit, and `filterFuns` keeps the points whose label is the label of `α`.
* The stabilizer is computed by the pointwise-stabilizer task (`pstabFuns`).

The result weighs at most `700 (n + 1)⁶`. The cost is at most one call of the
pointwise-stabilizer task on at most `T + 3` cells, where `T` is the weight of the argument, plus
`stabOrbitK * T ^ 9`. Both bounds depend on the input alone, because the task bounds its output:
at most `n²` generators (`GI.Cited.GensOf`). The large constant comes from
`pstabK * (20 T) ^ 9`.
-/
module

public import Workspace.Lang.Prims.Blocks

@[expose] public section

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited
open Equiv

variable {n : ℕ}

/-! ### Comparing labels -/

/-- On `[[labels, k], x]`: whether the label of `x` is `k`. -/
def eqLabF : Expr := .arith .eq (.get (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1))

/-- The test used by the filter: the value is a point whose label is `k`. -/
noncomputable def labTest (lab : Fin n → ℕ) (k : ℕ) (v : Val) : Bool :=
  @decide (∃ i : Fin n, v = .nat i ∧ lab i = k) (Classical.dec _)

theorem labTest_nat (lab : Fin n → ℕ) (k : ℕ) (i : Fin n) :
    labTest lab k (.nat i) = decide (lab i = k) := by
  unfold labTest
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simp only [Val.nat.injEq] at hj
    rw [Fin.ext hj]
  · exact fun h => ⟨i, rfl, h⟩

theorem eqLab_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some eqLabF) (lab : Fin n → ℕ)
    (hlab : ∀ x, lab x ≤ n) (k : ℕ) (i : Fin n) :
    FunDet P f (.list [.list [encFun lab, .nat k], .nat i])
      (boolVal (labTest lab k (.nat i))) (300 * (n + k + 1) ^ 2) := by
  have d0 := Det.arg' (P := P) (vs := [.list [encFun lab, .nat k], .nat i]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [encFun lab, .nat k], .nat i]) (rest := []) (j := 1) rfl
  have dL := Det.get' d0 (Det.nat 0) (show [encFun lab, Val.nat k][0]? = some (encFun lab) from rfl)
  have dK := Det.get' d0 (Det.nat 1) (show [encFun lab, Val.nat k][1]? = some (.nat k) from rfl)
  have dX := Det.get' dL d1 (encFun_getElem?_nat lab i i.isLt)
  have dE := Det.arith' (op := .eq) dX dK (z := (decide (lab i = k)).toNat)
    (by simp only [BinOp.eval_eq, Fin.eta]; split_ifs <;> simp_all)
  rw [labTest_nat]
  refine FunDet.intro hf (dE.mono ?_)
  have w1 : (encFun lab).wt ≤ 4 * (n + 1) ^ 2 := wt_encFun_le_sq lab hlab
  have w2 := wt_list2_le (.list [encFun lab, .nat k]) (.nat i)
  have w3 := wt_list2_le (encFun lab) (.nat k)
  have w4 := wt_nat_le k
  have w5 := wt_nat_le (i : ℕ)
  have w6 := wt_nat_le (lab ⟨i, i.isLt⟩)
  have w7 := wt_boolVal_le (decide (lab i = k))
  have w8 := hlab ⟨i, i.isLt⟩
  have w9 : (decide (lab i = k)).toNat ≤ 1 := Bool.toNat_le _
  have hi := i.isLt
  have h1 : (n + 1) ^ 2 ≤ (n + k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : n + k + 1 ≤ (n + k + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have e : (Val.nat (decide (lab i = k)).toNat).wt = (boolVal (decide (lab i = k))).wt := rfl
  omega

/-! ### The program -/

/-- On `[gv, α]`: the stabilizer of `α` and the orbit of `α`. -/
def stabOrbitEntry (b : ℕ) : Expr :=
  .letE (.call (b + 1) (arg 0))
    (.letE (.call (b + 33) (.get (arg 0) (.nat 0)))
      (.letE (.call (b + 36) (mk2 (mk2 (.var 1) (.get (.var 1) (arg 1))) (.var 2)))
        (.letE (.call (b + 40) (mk2 (arg 0) (mk1 (arg 1))))
          (mk2 (.var 4) (.var 3)))))

/-- The program, at base `b` (48 functions), with the pointwise-stabilizer primitive at `jps`. -/
def stabOrbitFuns (b jps : ℕ) : List Expr :=
  [stabOrbitEntry b] ++ orbitFuns (b + 1) ++ rangeFuns (b + 33) ++ filterFuns (b + 36) (b + 39) ++
    [eqLabF] ++ pstabFuns (b + 40) jps

/-- The constant of the program. -/
def stabOrbitK : ℕ := 600000000000000000

theorem sum_map_const' {β : Type*} (L : List β) (C : ℕ) : (L.map fun _ => C).sum = L.length * C := by
  induction L with
  | nil => simp
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; ring

theorem size_list2_nat_le (gv : Val) (x : ℕ) (S : List (Fin n)) (hS : S.length = 1) :
    (Val.list [gv, encPts S]).size ≤ (Val.list [gv, .nat x]).size + 3 := by
  match S, hS with
  | [i], _ =>
    rw [size_list2, size_list2, encPts_eq]
    simp only [List.map_cons, List.map_nil, size_list, length_cellsList, List.sum_cons,
      List.sum_nil, size_nat]
    omega

/-- **The stabilizer and the orbit of a point.** The result is a pair: the group value of `G_α`,
and the points of the orbit of `α` without repeats. -/
theorem stabOrbit_spec (hps : PointwiseStab) {P : Program} {b jps : ℕ}
    (hb : P.HasAt b (stabOrbitFuns b jps)) (hj : P.prims[jps]? = some (pointwiseStabPrim hps))
    {gv : Val} {G : Subgroup (Perm (Fin n))} (hG : GroupVal n gv G) (α : Fin n) :
    FunAll P b (.list [gv, .nat α]) (fun w c =>
      (∃ v1 v2, w = .list [v1, v2] ∧ GroupVal n v1 (pointwiseStab G [α]) ∧
        ∃ O : List (Fin n), v2 = encPts O ∧ O.Nodup ∧ ∀ y, y ∈ O ↔ ∃ g ∈ G, g α = y) ∧
      w.wt ≤ 700 * (n + 1) ^ 6 ∧
      c ≤ (pointwiseStabPrim hps).boundSize ((Val.list [gv, .nat α]).wt + 3) +
        stabOrbitK * (Val.list [gv, .nat α]).wt ^ 9) := by
  simp only [stabOrbitFuns] at hb
  have hentry : P.funs[b]? = some (stabOrbitEntry b) := hb.left.left.left.left.left.single
  have horb : P.HasAt (b + 1) (orbitFuns (b + 1)) := by simpa using hb.left.left.left.left.right
  have hrg : P.HasAt (b + 33) (rangeFuns (b + 33)) := by
    simpa [length_orbitFuns, Nat.add_assoc] using hb.left.left.left.right
  have hflt : P.HasAt (b + 36) (filterFuns (b + 36) (b + 39)) := by
    simpa [length_orbitFuns, rangeFuns, loopFuns, Nat.add_assoc] using hb.left.left.right
  have heq : P.funs[b + 39]? = some eqLabF := by
    simpa [length_orbitFuns, rangeFuns, filterFuns, loopFuns, Nat.add_assoc] using
      hb.left.right.single
  have hps' : P.HasAt (b + 40) (pstabFuns (b + 40) jps) := by
    simpa [length_orbitFuns, rangeFuns, filterFuns, loopFuns, Nat.add_assoc] using hb.right
  obtain ⟨gs, rfl, rfl⟩ := hG
  obtain ⟨lab, hO, hlabO, hlab⟩ := orbits_spec horb (1 :: gs)
  have hlab' : ∀ x, lab x ≤ n := fun x => (hlab x).1.le
  -- the orbit labels
  have dLab := Det.call (Det.arg' (P := P) (vs := [encGroup gs, .nat α]) (rest := [])
    (j := 0) rfl) hO
  refine FunAll.intro hentry (EvalAll.letE dLab fun v1 c1 h1 => ?_)
  obtain ⟨rfl, hc1⟩ := h1
  -- the points
  have dIds := Det.call (Det.get' (Det.arg' (P := P) (vs := [encGroup gs, .nat α])
    (rest := [encFun lab]) (j := 0) rfl) (Det.nat 0)
    (show [Val.nat n, Val.list ((1 :: gs).map encPerm)][0]? = some (.nat n) from rfl)) (range_det hrg n)
  refine EvalAll.letE dIds fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  -- the orbit of `α`
  have dC := Det.mk2 (Det.mk2 (Det.var' (P := P) (env := [Val.list [encGroup gs, .nat α],
      encFun lab, encPerm (1 : Perm (Fin n))]) (i := 1) rfl)
    (Det.get' (Det.var' (P := P) (env := [Val.list [encGroup gs, .nat α],
      encFun lab, encPerm (1 : Perm (Fin n))]) (i := 1) rfl)
      (Det.arg' (P := P) (vs := [encGroup gs, .nat α]) (rest := [encFun lab,
        encPerm (1 : Perm (Fin n))]) (j := 1) rfl) (encFun_getElem?_nat lab α α.isLt)))
    (Det.var' (P := P) (env := [Val.list [encGroup gs, .nat α],
      encFun lab, encPerm (1 : Perm (Fin n))]) (i := 2) rfl)
  have hF := filter_spec hflt (c := .list [encFun lab, .nat (lab ⟨α, α.isLt⟩)])
    (xs := (List.finRange n).map fun i : Fin n => Val.nat (i : ℕ))
    (q := labTest lab (lab ⟨α, α.isLt⟩)) (B := fun _ => 300 * (n + n + 1) ^ 2) (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact (eqLab_spec heq lab hlab' _ i).mono (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by have := hlab' ⟨α, α.isLt⟩; omega) 2)))
  have hCall : EvalAll P [Val.list [encGroup gs, .nat α], encFun lab, encPerm (1 : Perm (Fin n))]
      (.call (b + 36) (mk2 (mk2 (.var 1) (.get (.var 1) (arg 1))) (.var 2)))
      (fun w c => w = .list (((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)).filter
          (labTest lab (lab ⟨α, α.isLt⟩))) ∧
        ∃ ca cb, ca ≤ _ ∧ cb ≤ (((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)).map
          fun _ => 300 * (n + n + 1) ^ 2).sum + loopModK * (((List.finRange n).map
            fun i : Fin n => Val.nat (i : ℕ)).length + 1) *
            ((Val.list [.list [encFun lab, .nat (lab ⟨α, α.isLt⟩)],
              .list ((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ))]).wt +
              ((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)).length + w.wt + 1) ∧
          c = ca + cb + w.wt + 1) :=
    EvalAll.call_funAll dC fun v ca hv => by
      obtain ⟨rfl, hca⟩ := hv
      exact hF.mono fun w c hw => ⟨hw.1, ca, c, hca, hw.2, rfl⟩
  refine EvalAll.letE hCall fun v3 c3 h3 => ?_
  obtain ⟨rfl, ca3, cb3, hca3, hcb3, rfl⟩ := h3
  -- the stabilizer
  have dS := Det.mk2 (Det.arg' (P := P) (vs := [encGroup gs, .nat α]) (rest := [encFun lab,
      encPerm (1 : Perm (Fin n)), .list (((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)).filter
          (labTest lab (lab ⟨α, α.isLt⟩)))]) (j := 0) rfl)
    (Det.mk1 (Det.arg' (P := P) (vs := [encGroup gs, .nat α]) (rest := [encFun lab,
      encPerm (1 : Perm (Fin n)), .list (((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)).filter
          (labTest lab (lab ⟨α, α.isLt⟩)))]) (j := 1) rfl))
  have hpts : Val.list [Val.nat (α : ℕ)] = encPts [α] := by rw [encPts_eq]; rfl
  have hpts' := hpts
  rw [hpts] at dS
  have hP := pstab_spec hps hps' hj ⟨gs, rfl, rfl⟩ [α]
  have hCall2 : EvalAll P [Val.list [encGroup gs, .nat α], encFun lab, encPerm (1 : Perm (Fin n)),
      .list (((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)).filter
          (labTest lab (lab ⟨α, α.isLt⟩)))]
      (.call (b + 40) (mk2 (arg 0) (mk1 (arg 1))))
      (fun w c => GroupVal n w (pointwiseStab (gens gs) [α]) ∧ w.wt ≤ 320 * (n + 1) ^ 6 ∧
        ∃ ca cb, ca ≤ _ ∧ cb ≤ (pointwiseStabPrim hps).bound (.list [encGroup gs, encPts [α]]) +
          pstabK * (Val.list [encGroup gs, encPts [α]]).wt ^ 9 ∧
          c = ca + cb + w.wt + 1) :=
    EvalAll.call_funAll dS fun v ca hv => by
      obtain ⟨rfl, hca⟩ := hv
      exact hP.mono fun w c hw => ⟨hw.1, hw.2.1, ca, c, hca, hw.2.2, rfl⟩
  refine EvalAll.letE hCall2 fun v4 c4 h4 => ?_
  obtain ⟨hv4, hv4w, ca4, cb4, hca4, hcb4, rfl⟩ := h4
  -- the orbit, as a list of points
  have hvO : Val.list (((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)).filter
      (labTest lab (lab ⟨α, α.isLt⟩))) =
      encPts ((List.finRange n).filter (fun y => decide (lab y = lab α))) := by
    rw [encPts_eq, List.filter_map]
    congr 2
    apply List.filter_congr
    intro i _
    simp only [Function.comp_apply, labTest_nat, Fin.eta]
  -- the weight of the result
  have hOr7 : (Val.list (((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)).filter
      (labTest lab (lab ⟨α, α.isLt⟩)))).wt ≤ 7 * (n + 1) ^ 2 := by
    rw [hvO]
    have h1 := wt_encPts_le ((List.finRange n).filter (fun y => decide (lab y = lab α)))
    have h2 := List.length_filter_le (fun y => decide (lab y = lab α)) (List.finRange n)
    rw [List.length_finRange] at h2
    have h3 : 3 * ((List.finRange n).filter (fun y => decide (lab y = lab α))).length * (n + 2) ≤
        3 * n * (n + 2) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
    nlinarith
  have hO7 : (Val.list [v4, .list (((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)).filter
      (labTest lab (lab ⟨α, α.isLt⟩)))]).wt ≤ 700 * (n + 1) ^ 6 := by
    have h1 := wt_list2_le v4 (.list (((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)).filter
      (labTest lab (lab ⟨α, α.isLt⟩))))
    have h2 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have dOut := Det.mk2 (Det.var' (P := P) (env := [Val.list [encGroup gs, .nat α], encFun lab,
      encPerm (1 : Perm (Fin n)), .list (((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)).filter
          (labTest lab (lab ⟨α, α.isLt⟩))), v4]) (i := 4) rfl)
    (Det.var' (P := P) (env := [Val.list [encGroup gs, .nat α], encFun lab,
      encPerm (1 : Perm (Fin n)), .list (((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)).filter
          (labTest lab (lab ⟨α, α.isLt⟩))), v4]) (i := 3) rfl)
  refine dOut.post fun c hc => ⟨⟨_, _, rfl, hv4,
    (List.finRange n).filter (fun y => decide (lab y = lab α)), hvO, ?_, fun y => ?_⟩, hO7, ?_⟩
  · exact (List.nodup_finRange n).filter _
  · have h1 := (hlabO α y).trans mem_genOrbit
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    rw [eq_comm, h1, show genGroup (1 :: gs) = gens (1 :: gs) from rfl, gens_one_cons]
  · clear dLab dIds dC hF hCall dS hP hCall2 dOut hO hvO
    -- weights
    have w1 : (encFun lab).wt ≤ 4 * (n + 1) ^ 2 := wt_encFun_le_sq lab hlab'
    have e1 : (Val.list ((List.finRange n).map fun i => Val.nat (lab i))).wt = (encFun lab).wt :=
      congrArg Val.wt rfl
    have w2 : (encPerm (1 : Perm (Fin n))).wt ≤ 4 * (n + 1) ^ 2 := wt_encPerm_le _
    have e2 : (Val.list ((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ))).wt =
        (encPerm (1 : Perm (Fin n))).wt := congrArg Val.wt rfl
    have e3 : (Val.list [Val.list [encFun lab, Val.nat (lab ⟨α, α.isLt⟩)],
        Val.list ((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ))]).wt =
        (Val.list [Val.list [encFun lab, Val.nat (lab ⟨α, α.isLt⟩)],
          encPerm (1 : Perm (Fin n))]).wt := congrArg Val.wt rfl
    have w3 := wt_nat_le (lab ⟨α, α.isLt⟩)
    have w4 := hlab' ⟨α, α.isLt⟩
    have w5 := wt_list2_le (encFun lab) (.nat (lab ⟨α, α.isLt⟩))
    have w6 := wt_list2_le (.list [encFun lab, .nat (lab ⟨α, α.isLt⟩)]) (encPerm (1 : Perm (Fin n)))
    have w7 := wt_nat_le n
    have w8 := wt_nat_le (α : ℕ)
    have w9 : (encPts [α]).wt ≤ 2 * (Val.nat (α : ℕ)).wt + 5 := by
      rw [← hpts']; exact wt_list1_le _
    have w10 := wt_list2_le (encGroup gs) (encPts [α])
    have w11 : (encGroup gs).wt + (Val.nat (α : ℕ)).wt < (Val.list [encGroup gs, .nat α]).wt := by
      have := sum_wt_lt_wt_list [encGroup gs, .nat α]
      simpa using this
    have w12 := S_le_wt_encGroup gs
    have w13 : v4.wt < (Val.list [v4, .list (((List.finRange n).map fun i : Fin n =>
        Val.nat (i : ℕ)).filter (labTest lab (lab ⟨α, α.isLt⟩)))]).wt := wt_le_wt_list (by simp)
    have w14 : (Val.list (((List.finRange n).map fun i : Fin n =>
        Val.nat (i : ℕ)).filter (labTest lab (lab ⟨α, α.isLt⟩)))).wt <
        (Val.list [v4, .list (((List.finRange n).map fun i : Fin n =>
        Val.nat (i : ℕ)).filter (labTest lab (lab ⟨α, α.isLt⟩)))]).wt := wt_le_wt_list (by simp)
    have hα := α.isLt
    -- the size of the argument of the primitive call
    have hsz : (Val.list [encGroup gs, encPts [α]]).size ≤ (Val.list [encGroup gs, .nat α]).wt + 3 := by
      have h1 := size_list2_nat_le (encGroup gs) (α : ℕ) [α] rfl
      have h2 := (Val.list [encGroup gs, .nat α]).size_le_wt
      exact le_trans h1 (Nat.add_le_add_right h2 3)
    have hbd := (pointwiseStabPrim hps).bound_le hsz
    simp only [List.length_cons] at hc1
    have l1 : ((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)).length = n := by simp
    have s1 : (((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)).map
        fun _ => 300 * (n + n + 1) ^ 2).sum = n * (300 * (n + n + 1) ^ 2) := by
      rw [sum_map_const', l1]
    rw [s1, l1, e3] at hcb3
    rw [e1] at hca3
    clear hsz hpts hpts' e1 e2 e3
    generalize hT : (Val.list [encGroup gs, .nat α]).wt = T at *
    generalize hO : (Val.list [v4, .list (((List.finRange n).map fun i : Fin n =>
        Val.nat (i : ℕ)).filter (labTest lab (lab ⟨α, α.isLt⟩)))]).wt = O at *
    generalize hOr : (Val.list (((List.finRange n).map fun i : Fin n =>
        Val.nat (i : ℕ)).filter (labTest lab (lab ⟨α, α.isLt⟩)))).wt = Or at *
    have hS : (gs.length + 2) * (n + 1) ≤ T := by omega
    have hn : n + 1 ≤ T := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hS
    have hT1 : 1 ≤ T := by omega
    have h9 : T ≤ T ^ 9 := Nat.le_self_pow (by omega) _
    have hN3 : (n + 1) ^ 3 ≤ T ^ 9 :=
      (Nat.pow_le_pow_left hn 3).trans (Nat.pow_le_pow_right hT1 (by omega))
    have hN6 : (n + 1) ^ 6 ≤ T ^ 9 :=
      (Nat.pow_le_pow_left hn 6).trans (Nat.pow_le_pow_right hT1 (by omega))
    have hN2 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : orbitK * ((gs.length + 1 + 1) * (n + 1)) ^ 5 ≤ 1000000 * T ^ 9 :=
      Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left
        (by rw [show gs.length + 1 + 1 = gs.length + 2 from rfl]; omega) 5).trans
        (Nat.pow_le_pow_right hT1 (by omega)))
    have h2 : n * (300 * (n + n + 1) ^ 2) ≤ 1200 * (n + 1) ^ 3 := by
      calc n * (300 * (n + n + 1) ^ 2) ≤ (n + 1) * (300 * (4 * (n + 1) ^ 2)) :=
            Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (sq_nn_le n))
        _ = 1200 * (n + 1) ^ 3 := by ring
    have h3 : loopModK * (n + 1) * ((Val.list [Val.list [encFun lab, Val.nat (lab ⟨α, α.isLt⟩)],
        encPerm (1 : Perm (Fin n))]).wt + n + Or + 1) ≤ loopModK * (n + 1) * (80 * (n + 1) ^ 2) := by
      refine Nat.mul_le_mul_left _ ?_
      have e : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      omega
    have e4 : loopModK * (n + 1) * (80 * (n + 1) ^ 2) = 80000 * (n + 1) ^ 3 := by
      simp only [loopModK]; ring
    have h4 : pstabK * (Val.list [encGroup gs, encPts [α]]).wt ^ 9 ≤
        512000000000000000 * T ^ 9 := by
      have : (Val.list [encGroup gs, encPts [α]]).wt ≤ 20 * T := by omega
      calc pstabK * (Val.list [encGroup gs, encPts [α]]).wt ^ 9
          ≤ pstabK * (20 * T) ^ 9 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 9)
        _ = 512000000000000000 * T ^ 9 := by simp only [pstabK]; ring
    have k : stabOrbitK = 600000000000000000 := rfl
    rw [k]
    omega

end GI.Lang
