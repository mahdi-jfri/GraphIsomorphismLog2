module

public import Workspace.Impl.LinCoordinateLayout
public import Workspace.Impl.LinWitnessLayout

@[expose] public section

/-! One complete cyclic relation row from permutation-group inputs. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linCoordinateRowF (prep witness : ℕ) : Expr :=
  .letE (.call prep (.var 0)) (.call witness (.var 1))

def linCoordinateRowFuns (b jo jm : ℕ) : List Expr :=
  [linCoordinateRowF (b + 1) (b + 31)] ++
    linCoordinatePrepFuns (b + 1) jo ++ linCoordinateWitnessFuns (b + 31) jm

theorem linCoordinateRowFuns_length (b jo jm : ℕ) : (linCoordinateRowFuns b jo jm).length = 62 := rfl

theorem linCoordinateWitnessCost_mono (h : ConstructiveMembership) (I : MemberInst)
    {W V : ℕ} (hW : W ≤ V) (t : ℕ) :
    linCoordinateWitnessCost h I W t ≤ linCoordinateWitnessCost h I V t := by
  have he := linSlpValueCost_mono_all
    (show 10 * (W + linMembershipWt (linMembershipDegree h) I + 1) ≤
      10 * (V + linMembershipWt (linMembershipDegree h) I + 1) by omega)
    (le_refl ((memberInput I).cells.length ^ linMembershipDegree h)) (le_refl t)
  unfold linCoordinateWitnessCost
  omega

noncomputable def linCoordinateRowCost (ho : GroupOrder) (hm : ConstructiveMembership)
    {n : ℕ} (ns as : List (Equiv.Perm (Fin n))) (i : Fin as.length) : ℕ :=
  let W := (Val.list [encGroup ns, encGroup as, .nat i.val]).wt
  let C := linCoordinatePrepCost ho W n ns.length as.length i.val
  1000 * (W + C + linCoordinateWitnessCost hm (linCoordinateMemberInst ns as i) C as.length + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linCoordinateRow_spec (ho : GroupOrder) (hm : ConstructiveMembership)
    {P : Program} {b jo jm n : ℕ}
    (h : P.HasAt b (linCoordinateRowFuns b jo jm))
    (hjo : P.prims[jo]? = some (groupOrderPrim ho))
    (hjm : P.prims[jm]? = some (linMembershipPrim hm))
    (ns as : List (Equiv.Perm (Fin n))) (hle : gens ns ≤ gens as)
    (hc : ∀ x ∈ gens as, ∀ y ∈ gens as, x * y * x⁻¹ * y⁻¹ ∈ gens ns) (i : Fin as.length) :
    FunAll P b (.list [encGroup ns, encGroup as, .nat i.val]) (fun out cost =>
      (∃ (prog : List SlpInstr) (z : Fin as.length → ℤ),
        out = .list [encInt (linCyclicOrders (gens ns) as i), linVecVal z] ∧
        SlpReaches (ns ++ as.take i.val) prog (as[i.val] ^ linCyclicOrders (gens ns) as i) ∧
        linExponentValue (linPrefixVectors as.length ns.length i.val) prog = some z ∧
        (∀ j, i ≤ j → z j = 0)) ∧ cost ≤ linCoordinateRowCost ho hm ns as i) := by
  have hprep : P.HasAt (b + 1) (linCoordinatePrepFuns (b + 1) jo) := h.block 1 rfl
  have hwit : P.HasAt (b + 31) (linCoordinateWitnessFuns (b + 31) jm) := h.block 31 rfl
  have pa := linCoordinatePrepAt_of hprep hjo
  have wa := linCoordinateWitnessAt_of hwit hjm
  let a := Val.list [encGroup ns, encGroup as, .nat i.val]
  let C := linCoordinatePrepCost ho a.wt n ns.length as.length i.val
  let WI := linCoordinateMemberInst ns as i
  let CW := linCoordinateWitnessCost hm WI C as.length
  have hp := linCoordinatePrep_spec ho pa (linCoordinatePrep_entry hprep) ns as i
  have wp : (linCoordinatePrepVal ns as i).wt ≤ C := hp.wt_lt.le
  have hmember : WI.x ∈ gens WI.gs := linPermChain_power (gens as) ns as hle
    (fun x hx => Subgroup.subset_closure hx) (fun x y => hc x x.property y y.property) i.val i.isLt
  have hlen : WI.gs.length = (linPrefixVectors as.length ns.length i.val).length := by
    simp only [WI, linCoordinateMemberInst, linPrefixVectors, List.length_append,
      List.length_replicate, List.length_map, List.length_take, List.length_finRange]
  have hw := linCoordinateWitness_spec hm wa.entry wa.member wa.prim wa.exponent wa.table wa.step
    wa.ints wa.add wa.scale WI hmember _ hlen (linPrefixVectors_bound _ _ _)
    (encInt (linCyclicOrders (gens ns) as i))
  have hw' : FunAll P (b + 31) (linCoordinatePrepVal ns as i) (fun out cost =>
      (∃ (prog : List SlpInstr) (z : Fin as.length → ℤ),
        out = .list [encInt (linCyclicOrders (gens ns) as i), linVecVal z] ∧
        SlpReaches WI.gs prog WI.x ∧
        linExponentValue (linPrefixVectors as.length ns.length i.val) prog = some z) ∧ cost ≤ CW) :=
    FunAll.mono hw fun out cost ho' =>
      ⟨ho'.1, ho'.2.trans (linCoordinateWitnessCost_mono hm WI wp as.length)⟩
  have he := (h.block (gs := [linCoordinateRowF (b + 1) (b + 31)]) 0 rfl).single
  apply FunAll.intro he
  have dp := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hp
  apply EvalAll.letE dp
  intro pv cp hpv
  obtain ⟨rfl, hcp⟩ := hpv
  have da := Det.var' (P := P) (env := [a, linCoordinatePrepVal ns as i]) (i := 1) rfl
  apply EvalAll.call_funAll da
  intro v ca hv
  obtain ⟨rfl, hca⟩ := hv
  refine hw'.wt_lt.mono fun out cost ho' => ?_
  obtain ⟨⟨⟨prog, z, hout, hreach, hz⟩, hcost⟩, wout⟩ := ho'
  refine ⟨⟨prog, z, hout, hreach, hz, ?_⟩, ?_⟩
  · intro j hij
    exact linExponentValue_zero _ j (linPrefixVectors_zero _ _ _ j hij) _ _ hz
  · change _ ≤ linCoordinateRowCost ho hm ns as i
    unfold linCoordinateRowCost
    dsimp only [C, CW, a, WI] at hcp hca hcost wout wp ⊢
    clear * - hcp hca hcost wout wp
    generalize (Val.list [encGroup ns, encGroup as, .nat i.val]).wt = Wp at *
    generalize linCoordinatePrepCost ho Wp n ns.length as.length i.val = CP at *
    generalize linCoordinateWitnessCost hm (linCoordinateMemberInst ns as i) CP as.length = WP at *
    nlinarith only [hcp, hca, hcost, wout, wp]

end GI.Impl
