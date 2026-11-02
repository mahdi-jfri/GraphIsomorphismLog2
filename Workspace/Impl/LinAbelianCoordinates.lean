import Workspace.Impl.LinCoordinateUniform
import Workspace.Impl.LinCoordinateSplit

/-! End-to-end assembly of the integer presentation of A/N, from permutation inputs. -/
namespace GI.Impl
open GI.Cited GI.Lang
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

def linAbelianCoordinatesF (collect split relations : ℕ) : Expr :=
  .letE (.call collect (.var 0))
    (.letE (.call split (.var 1)) (.call relations (.var 2)))

def linAbelianCoordinatesFuns (b jo jm : ℕ) : List Expr :=
  [linAbelianCoordinatesF (b + 1) (b + 66) (b + 69)] ++
    linCoordinateCollectFuns (b + 1) (b + 4) ++ linCoordinateRowFuns (b + 4) jo jm ++
    linCoordinateSplitFuns (b + 66) ++ linRelationsFuns (b + 69) (b + 72) (b + 75) ++
    linBasisFuns (b + 72) ++ linVectorBinaryFuns (b + 75) ((b + 78) + 12) ++ linIntFuns (b + 78)

theorem linAbelianCoordinatesFuns_length (b jo jm : ℕ) :
    (linAbelianCoordinatesFuns b jo jm).length = 96 := rfl

structure linAbelianCoordinatesAt (P : Program) (b jo jm : ℕ) : Prop where
  entry : P.funs[b]? = some (linAbelianCoordinatesF (b + 1) (b + 66) (b + 69))
  collect : P.HasAt (b + 1) (linCoordinateCollectFuns (b + 1) (b + 4))
  row : P.HasAt (b + 4) (linCoordinateRowFuns (b + 4) jo jm)
  split : P.HasAt (b + 66) (linCoordinateSplitFuns (b + 66))
  relations : P.HasAt (b + 69) (linRelationsFuns (b + 69) (b + 72) (b + 75))
  basis : P.HasAt (b + 72) (linBasisFuns (b + 72))
  sub : P.HasAt (b + 75) (linVectorBinaryFuns (b + 75) ((b + 78) + 12))
  ints : linIntSpec P (b + 78)

theorem linAbelianCoordinatesAt_of {P : Program} {b jo jm : ℕ}
    (h : P.HasAt b (linAbelianCoordinatesFuns b jo jm)) : linAbelianCoordinatesAt P b jo jm where
  entry := (h.block (gs := [linAbelianCoordinatesF (b + 1) (b + 66) (b + 69)]) 0 rfl).single
  collect := h.block 1 rfl
  row := h.block 4 rfl
  split := h.block 66 rfl
  relations := h.block 69 rfl
  basis := h.block 72 rfl
  sub := h.block 75 rfl
  ints := linInt_spec (h.block 78 rfl)

noncomputable def linAbelianCoordinatesCost (ho : GroupOrder) (hm : ConstructiveMembership) (W t : ℕ) : ℕ :=
  let C := linCoordinateCollectCost W t (linCoordinateRowBudget ho hm W)
  let S := linCoordinateSplitCost C t
  let R := linRelationsCost S t
  1000 * (W + C + S + R + 1)

theorem linCoordinateSplitCost_mono {W V t s : ℕ} (hW : W ≤ V) (ht : t ≤ s) :
    linCoordinateSplitCost W t ≤ linCoordinateSplitCost V s := by
  simp only [linCoordinateSplitCost, linCoordinateSplitAcc]; gcongr

theorem linRelationsCost_mono {W V t s : ℕ} (hW : W ≤ V) (ht : t ≤ s) :
    linRelationsCost W t ≤ linRelationsCost V s := by
  simp only [linRelationsCost, linRelationsStepCost, linRelationsAccWt,
    linRelationsRowCost, linRelationsSubArg, linRelationsBasisCost, linRelationsBasisArg,
    linBasisCost, linVectorBinaryCost, linVectorAccWt]
  gcongr

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
theorem linAbelianCoordinates_spec (ho : GroupOrder) (hm : ConstructiveMembership)
    {P : Program} {b jo jm n : ℕ} (h : linAbelianCoordinatesAt P b jo jm)
    (hjo : P.prims[jo]? = some (groupOrderPrim ho))
    (hjm : P.prims[jm]? = some (linMembershipPrim hm))
    (ns as : List (Equiv.Perm (Fin n))) (hle : gens ns ≤ gens as)
    (hc : ∀ x ∈ gens as, ∀ y ∈ gens as, x * y * x⁻¹ * y⁻¹ ∈ gens ns) :
    FunAll P b (.list [encGroup ns, encGroup as]) (fun out cost =>
      (∃ M : Matrix (Fin as.length) (Fin as.length) ℤ,
        out = encIntMatrix M ∧ linPermPresentation ns as M) ∧
      cost ≤ linAbelianCoordinatesCost ho hm (Val.list [encGroup ns, encGroup as]).wt as.length) := by
  let a := Val.list [encGroup ns, encGroup as]
  let W := a.wt
  let t := as.length
  let CC := linCoordinateCollectCost W t (linCoordinateRowBudget ho hm W)
  let SC := linCoordinateSplitCost CC t
  let RC := linRelationsCost SC t
  have col := linCoordinateCollect_presentation ho hm h.collect h.row hjo hjm ns as hle hc
    (linCoordinateRowCost_le ho hm ns as)
  have call : EvalAll P [a] (.call (b + 1) (.var 0)) (fun rows cost =>
      (∃ C : Matrix (Fin t) (Fin t) ℤ,
        rows = .list ((List.finRange t).map (fun i =>
          .list [encInt (linCyclicOrders (gens ns) as i), linVecVal (C i)])) ∧
        linPermPresentation ns as (linRelationMatrix (linCyclicOrders (gens ns) as) C)) ∧
      cost ≤ 10 * (W + CC + 1) ∧ rows.wt ≤ CC) := by
    apply EvalAll.call_funAll (Det.var' (P := P) (env := [a]) (i := 0) rfl)
    intro v ca hv
    obtain ⟨rfl, hca⟩ := hv
    refine col.wt_lt.mono fun rows cost hr => ?_
    obtain ⟨⟨hcert, hcost⟩, hwt⟩ := hr
    exact ⟨hcert, by change _ ≤ 10 * (a.wt + CC + 1); change cost ≤ CC at hcost; omega,
      hwt.le.trans hcost⟩
  apply FunAll.intro h.entry
  apply EvalAll.letE call
  intro rows cr hr
  obtain ⟨⟨C, rfl, hC⟩, hcr, wr⟩ := hr
  let rv := Val.list ((List.finRange t).map fun i =>
    Val.list [encInt (linCyclicOrders (gens ns) as i), linVecVal (C i)])
  have split := (linCoordinateSplit_spec h.split (linCyclicOrders (gens ns) as) C).mono
    (linCoordinateSplitCost_mono wr le_rfl)
  have ds := Det.call (Det.var' (P := P) (env := [a, rv]) (i := 1) rfl) split
  apply EvalAll.letE ds
  intro data cs hdata
  obtain ⟨rfl, hcs⟩ := hdata
  have wd := split.wt_lt.le
  have rel := (linRelations_spec h.relations h.basis h.ints h.sub
    (linCyclicOrders (gens ns) as) C).mono (linRelationsCost_mono wd le_rfl)
  have dr := Det.call (Det.var' (P := P) (env := [a, rv, _]) (i := 2) rfl) rel
  refine dr.post fun cost hcost => ⟨⟨_, rfl, hC⟩, ?_⟩
  have wm := rel.wt_lt.le
  change _ ≤ linAbelianCoordinatesCost ho hm W t
  unfold linAbelianCoordinatesCost
  change _ ≤ 1000 * (W + CC + SC + RC + 1)
  dsimp only [W, a, CC, SC, RC, t, rv] at *
  omega

end GI.Impl

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

theorem linCoordinateSplitCost_poly : PBU (fun t W _ => linCoordinateSplitCost W t) := by
  unfold linCoordinateSplitCost linCoordinateSplitAcc
  norm_poly

theorem linRelationsCost_poly : PBU (fun t W _ => linRelationsCost W t) := by
  simp only [linRelationsCost, linRelationsStepCost, linRelationsAccWt,
    linRelationsRowCost, linRelationsSubArg, linRelationsBasisCost, linRelationsBasisArg,
    linBasisCost, linVectorBinaryCost, linVectorAccWt, linIntBinaryCost,
    linIntCoreBudget, linIntPartsCost, linIntCodecCost]
  norm_poly

theorem linAbelianCoordinatesBudget_poly (ho : GroupOrder) (hm : ConstructiveMembership) :
    PBU (fun _ W _ => linAbelianCoordinatesCost ho hm W W) := by
  have hcol := linCoordinateBudget_poly ho hm
  have hsplit := linPoly_subst linCoordinateSplitCost_poly PBU.W hcol (PBU.const 0)
  have hrel := linPoly_subst linRelationsCost_poly PBU.W hsplit (PBU.const 0)
  exact PBU.smul 1000 (PBU.addc (PBU.add (PBU.add (PBU.add PBU.W hcol) hsplit) hrel) 1)

theorem linAbelianCoordinatesCost_mono_t (ho : GroupOrder) (hm : ConstructiveMembership)
    (W : ℕ) {t s : ℕ} (ht : t ≤ s) :
    linAbelianCoordinatesCost ho hm W t ≤ linAbelianCoordinatesCost ho hm W s := by
  have hcol : linCoordinateCollectCost W t (linCoordinateRowBudget ho hm W) ≤
      linCoordinateCollectCost W s (linCoordinateRowBudget ho hm W) := by
    exact linCoordinateCollectCost_mono le_rfl ht le_rfl
  have hsplit := linCoordinateSplitCost_mono hcol ht
  have hrel := linRelationsCost_mono hsplit ht
  simp only [linAbelianCoordinatesCost]
  omega

/-- A concrete 96-function program computes a complete presentation of A/N in
uniform polynomial bit time. No presentation or coordinate oracle is assumed. -/
theorem linAbelianCoordinates_spec_poly (ho : GroupOrder) (hm : ConstructiveMembership) :
    ∃ K D : ℕ, ∀ {P : Program} {b jo jm n : ℕ},
      P.HasAt b (linAbelianCoordinatesFuns b jo jm) →
      P.prims[jo]? = some (groupOrderPrim ho) →
      P.prims[jm]? = some (linMembershipPrim hm) →
      ∀ (ns as : List (Equiv.Perm (Fin n))), gens ns ≤ gens as →
        (∀ x ∈ gens as, ∀ y ∈ gens as, x * y * x⁻¹ * y⁻¹ ∈ gens ns) →
        FunAll P b (.list [encGroup ns, encGroup as]) (fun out cost =>
          (∃ M : Matrix (Fin as.length) (Fin as.length) ℤ,
            out = encIntMatrix M ∧ linPermPresentation ns as M) ∧
          cost ≤ K * ((Val.list [encGroup ns, encGroup as]).wt + 1) ^ D) := by
  obtain ⟨K, D, hp⟩ := linAbelianCoordinatesBudget_poly ho hm
  refine ⟨K * 2 ^ D, D, fun hl hjo hjm ns as hle hc => ?_⟩
  refine (linAbelianCoordinates_spec ho hm (linAbelianCoordinatesAt_of hl) hjo hjm ns as hle hc).mono
    fun out cost ho' => ⟨ho'.1, ho'.2.trans ?_⟩
  let W := (Val.list [encGroup ns, encGroup as]).wt
  have ht := (linCoordinateSource_bounds ns as).2.2
  have hcost := linAbelianCoordinatesCost_mono_t ho hm W ht
  have hb := hp 0 W 0
  change linAbelianCoordinatesCost ho hm W W ≤ K * (W + 0 + 0 + 2) ^ D at hb
  calc
    _ ≤ linAbelianCoordinatesCost ho hm W W := hcost
    _ ≤ K * (W + 2) ^ D := by simpa using hb
    _ ≤ K * (2 * (W + 1)) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) D)
    _ = (K * 2 ^ D) * (W + 1) ^ D := by rw [mul_pow]; ring

end GI.Impl
