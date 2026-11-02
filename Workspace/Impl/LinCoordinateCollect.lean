import Workspace.Impl.LinCoordinateRow
import Workspace.Impl.LinPermCertificate

/-! Collect all cyclic-order and exponent-vector pairs, allowing each cited
constructive-membership call to choose any valid straight-line program. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linCoordinateCollectStep (row : ℕ) : Expr :=
  .snoc (arg 2) (.call row (mk3 (.get (arg 0) (.nat 0))
    (.get (arg 0) (.nat 1)) (arg 1)))

def linCoordinateCollectFuns (b row : ℕ) : List Expr :=
  loopFuns b (linPrepCountE 1) .nil (linCoordinateCollectStep row)

noncomputable def linCoordinateRecord {n : ℕ} (ns as : List (Equiv.Perm (Fin n)))
    (i : Fin as.length) (v : Val) : Prop :=
  ∃ (prog : List SlpInstr) (z : Fin as.length → ℤ),
    v = .list [encInt (linCyclicOrders (gens ns) as i), linVecVal z] ∧
    SlpReaches (ns ++ as.take i.val) prog (as[i.val] ^ linCyclicOrders (gens ns) as i) ∧
    linExponentValue (linPrefixVectors as.length ns.length i.val) prog = some z

def linCoordinateCollectCost (W t D : ℕ) : ℕ :=
  t * (10 * (D + 1)) + loopModK * (t + 1) * (W + t + linVectorAccWt t D + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linCoordinateCollect_spec (ho : GroupOrder) (hm : ConstructiveMembership)
    {P : Program} {b row jo jm n D : ℕ}
    (hp : P.HasAt b (linCoordinateCollectFuns b row))
    (hr : P.HasAt row (linCoordinateRowFuns row jo jm))
    (hjo : P.prims[jo]? = some (groupOrderPrim ho))
    (hjm : P.prims[jm]? = some (linMembershipPrim hm))
    (ns as : List (Equiv.Perm (Fin n))) (hle : gens ns ≤ gens as)
    (hc : ∀ x ∈ gens as, ∀ y ∈ gens as, x * y * x⁻¹ * y⁻¹ ∈ gens ns)
    (hD : ∀ i, linCoordinateRowCost ho hm ns as i ≤ D) :
    FunAll P b (.list [encGroup ns, encGroup as]) (fun out cost =>
      (∃ ws, out = .list ws ∧ List.Forall₂ (linCoordinateRecord ns as) (List.finRange as.length) ws) ∧
      cost ≤ linCoordinateCollectCost (Val.list [encGroup ns, encGroup as]).wt as.length D) := by
  let a := Val.list [encGroup ns, encGroup as]
  let W := a.wt
  let t := as.length
  let R (i : Fin t) (v : Val) := linCoordinateRecord ns as i v ∧ v.wt ≤ D
  let Inv (k : ℕ) (v : Val) := ∃ ws, v = .list ws ∧ List.Forall₂ R ((List.finRange t).take k) ws
  have wm (k : ℕ) (v : Val) (hk : k ≤ t) (hv : Inv k v) : v.wt ≤ linVectorAccWt t D := by
    obtain ⟨ws, rfl, hws⟩ := hv
    have hh := linWtList (vs := ws) (B := D) (by
      intro w hw
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
      have hx : j < ((List.finRange t).take k).length := by rw [hws.length_eq]; exact hj
      exact (hws.get hx hj).2)
    have hl : ws.length ≤ t := by
      have hh := hws.length_eq
      simp only [List.length_take, List.length_finRange] at hh
      omega
    exact hh.trans (by unfold linVectorAccWt; nlinarith [Nat.mul_le_mul_right D hl])
  have dk := Det.arith' (op := .sub)
    (Det.length (Det.get' (Det.arg' (P := P) (vs := [encGroup ns, encGroup as])
      (rest := []) (j := 1) rfl) (Det.nat 1) rfl)) (Det.nat 1)
    (show ((1 :: as).map encPerm).length - 1 = t by simp [t])
  have hl := loopBdd_spec hp dk Det.nil (by
      have := wt_nat_le t
      have wg : (encGroup as).wt < W := wt_le_wt_list (by simp [W, a])
      have wx : (Val.list ((1 :: as).map encPerm)).wt < (encGroup as).wt := wt_le_wt_list (by simp [encGroup, encPerms])
      have hsum := sum_wt_lt_wt_list [encGroup ns, encGroup as]
      have hn := (encGroup ns).two_le_size.trans (encGroup ns).size_le_wt
      have ha := (encGroup as).two_le_size.trans (encGroup as).size_le_wt
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
      have := a.two_le_size
      have := a.size_le_wt
      simp only [List.length_map, List.length_cons] at *
      dsimp only [W, a, t] at *
      omega)
    (Inv := Inv) (M := linVectorAccWt t D) (D := fun _ => 10 * (D + 1))
    ⟨[], rfl, by simp⟩ wm (fun k acc hk hv => ?_)
  · refine hl.mono fun out cost hout => ?_
    obtain ⟨⟨ws, rfl, hws⟩, hcost⟩ := hout
    refine ⟨⟨ws, rfl, ?_⟩, ?_⟩
    · have hh := hws.imp (fun _ _ h => h.1)
      simpa only [← (List.length_finRange (n := t)), List.take_length] using hh
    · simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul, linCoordinateCollectCost] using hcost
  · obtain ⟨ws, rfl, hws⟩ := hv
    let i : Fin t := ⟨k, hk⟩
    have dr := linCoordinateRow_spec ho hm hr hjo hjm ns as hle hc i
    have dw := dr.wt_lt
    have d0 := Det.arg' (P := P) (vs := [a, .nat k, .list ws]) (rest := []) (j := 0) rfl
    have da := Det.mk3 (Det.get' d0 (Det.nat 0) rfl) (Det.get' d0 (Det.nat 1) rfl)
      (Det.arg' (P := P) (vs := [a, .nat k, .list ws]) (rest := []) (j := 1) rfl)
    have call := EvalAll.call_funAll da (f := row) (Q := fun v cost =>
      R i v ∧ cost ≤ 60 * (W + t + (Val.list ws).wt + 1) + D + v.wt + 1) (fun v ca hv => by
        obtain ⟨rfl, hca⟩ := hv
        exact dw.mono fun v cost hv => by
          obtain ⟨⟨⟨p, z, he, hp, hz, _⟩, hcost⟩, hwt⟩ := hv
          have hd := hD i
          have wa := wt_list3_le a (.nat k) (.list ws)
          have wr := wt_list3_le (encGroup ns) (encGroup as) (.nat k)
          have hmin := sum_wt_lt_wt_list [encGroup ns, encGroup as]
          have hnmin := (encGroup ns).two_le_size.trans (encGroup ns).size_le_wt
          have hamin := (encGroup as).two_le_size.trans (encGroup as).size_le_wt
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hmin
          have wi := wt_nat_le k
          have wn : (encGroup ns).wt < W := wt_le_wt_list (by simp [W, a])
          have was : (encGroup as).wt < W := wt_le_wt_list (by simp [W, a])
          refine ⟨⟨⟨p, z, he, hp, hz⟩, hwt.le.trans (hcost.trans hd)⟩, ?_⟩
          dsimp only [W, a, t] at *
          omega)
    refine (EvalAll.snoc_det (Det.arg' (P := P) (vs := [a, .nat k, .list ws])
      (rest := []) (j := 2) rfl) call).mono ?_
    rintro v cost ⟨w, cw, hw, rfl, hcost⟩
    have hnew : Inv (k + 1) (.list (ws ++ [w])) := by
      refine ⟨ws ++ [w], rfl, ?_⟩
      rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hk)]
      simpa only [List.getElem_finRange] using List.rel_append hws (List.Forall₂.cons hw.1 List.Forall₂.nil)
    refine ⟨hnew, ?_⟩
    have wa := wt_list3_le a (.nat k) (.list ws)
    have wi := wt_nat_le k
    have wold := wm k (.list ws) hk.le ⟨ws, rfl, hws⟩
    have wnew := wm (k + 1) (.list (ws ++ [w])) hk hnew
    have winput := wt_list3_le (encGroup ns) (encGroup as) (.nat k)
    have wn : (encGroup ns).wt < W := wt_le_wt_list (by simp [W, a])
    have was : (encGroup as).wt < W := wt_le_wt_list (by simp [W, a])
    dsimp only [W, a, R, i] at *
    omega

end GI.Impl

namespace GI.Impl
open GI.Cited GI.Lang

/-- The collected data satisfy all the hypotheses of the presentation theorem,
with the quotient map induced by the original permutation generators. -/
theorem linCoordinateCollect_presentation (ho : GroupOrder) (hm : ConstructiveMembership)
    {P : Program} {b row jo jm n D : ℕ}
    (hp : P.HasAt b (linCoordinateCollectFuns b row))
    (hr : P.HasAt row (linCoordinateRowFuns row jo jm))
    (hjo : P.prims[jo]? = some (groupOrderPrim ho))
    (hjm : P.prims[jm]? = some (linMembershipPrim hm))
    (ns as : List (Equiv.Perm (Fin n))) (hle : gens ns ≤ gens as)
    (hc : ∀ x ∈ gens as, ∀ y ∈ gens as, x * y * x⁻¹ * y⁻¹ ∈ gens ns)
    (hD : ∀ i, linCoordinateRowCost ho hm ns as i ≤ D) :
    FunAll P b (.list [encGroup ns, encGroup as]) (fun out cost =>
      (∃ C : Matrix (Fin as.length) (Fin as.length) ℤ,
        out = .list ((List.finRange as.length).map (fun i =>
          .list [encInt (linCyclicOrders (gens ns) as i), linVecVal (C i)])) ∧
        linPermPresentation ns as (linRelationMatrix (linCyclicOrders (gens ns) as) C)) ∧
      cost ≤ linCoordinateCollectCost (Val.list [encGroup ns, encGroup as]).wt as.length D) := by
  classical
  refine (linCoordinateCollect_spec ho hm hp hr hjo hjm ns as hle hc hD).mono ?_
  rintro out cost ⟨⟨ws, rfl, hw⟩, hcost⟩
  have hlen : ws.length = as.length := by simpa using hw.length_eq.symm
  have hrow (i : Fin as.length) : linCoordinateRecord ns as i ws[i.val] := by
    have hh := hw.get (i := i.val) (by simpa using i.isLt) (by omega)
    simpa using hh
  choose prog C he hp hC using hrow
  refine ⟨⟨C, ?_, linPermCertificate ns as hle hc prog C hp hC⟩, hcost⟩
  apply congrArg Val.list
  apply List.ext_getElem (by simp [hlen])
  intro j hj hj'
  simpa using he ⟨j, by omega⟩

end GI.Impl
