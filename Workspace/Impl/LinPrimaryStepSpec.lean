module

public import Workspace.Impl.LinPrimaryStepCost

@[expose] public section

/-! A complete primary iteration, with both answer branches and the full
restricted dictionary, point and accumulated representative. -/
namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 18000

noncomputable def linPrimaryNextTarget {n p d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (hp : p.Prime) (hpn : p ≤ n) (ν : Fin d → ℕ) (level : ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (hs : IsSolvable ρ.range)
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν))
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (hf : ∀ g, linPrimaryFiber p ν level (c g)) (x : linFiniteVec (linPrimaryOrders p ν)) :
    Subgroup (Equiv.Perm (Fin n)) :=
  linAffineTargetSub (linPrimaryLayerInst gs hp hpn ν level ρ hs x)
    (fun g => linPrimaryCoord p ν level (c g))
    (linPrimaryLayer_cocycle gs hp hpn ν level ρ hs c hc hf x) 0

theorem linPrimaryNextTarget_le {n p d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (hp : p.Prime) (hpn : p ≤ n) (ν : Fin d → ℕ) (level : ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (hs : IsSolvable ρ.range)
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν))
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (hf : ∀ g, linPrimaryFiber p ν level (c g)) (x : linFiniteVec (linPrimaryOrders p ν)) :
    linPrimaryNextTarget gs hp hpn ν level ρ hs c hc hf x ≤ gens gs := by
  intro z hz
  obtain ⟨g, _, rfl⟩ := Subgroup.mem_map.mp hz
  exact g.property

noncomputable def linPrimaryStepOut {n p d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (hp : p.Prime) (hpn : p ≤ n) (ν : Fin d → ℕ) (level : ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (hs : IsSolvable ρ.range)
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν))
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (hf : ∀ g, linPrimaryFiber p ν level (c g)) (x : linFiniteVec (linPrimaryOrders p ν))
    (acc : Equiv.Perm (Fin n)) (out : Val) : Prop :=
  (out = .list [] ∧ ¬∃ g : gens gs, linPrimaryFiber p ν (level + 1) (ρ g x + c g)) ∨
  ∃ (g : gens gs) (newgs : List (Equiv.Perm (Fin n))) (hle : gens newgs ≤ gens gs),
    newgs.length ≤ n ^ 2 ∧ gens newgs = linPrimaryNextTarget gs hp hpn ν level ρ hs c hc hf x ∧
    out = .list [linActionContext newgs (linPrimaryOrders p ν) (ρ.comp (Subgroup.inclusion hle))
      (c ∘ Subgroup.inclusion hle), linFinitePointVal (linPrimaryOrders p ν) (ρ g x + c g), encPerm (g.val * acc)] ∧
    linPrimaryFiber p ν (level + 1) (ρ g x + c g)

private theorem linPrimaryWholeCost {W Z A L T ca cl cb wo : ℕ}
    (hz : ca ≤ 100 * (W + Z + 1)) (hl : cl ≤ A + 2 * L + 1)
    (hb : cb ≤ L + 2 * T + 100) (hw : wo ≤ T + 4) :
    ca + (cl + cb + wo + 1) + wo + 1 ≤ 100000 * (W + Z + A + L + T + 1) := by omega

private theorem linPrimaryFailGuard (L T : ℕ) :
    4 + 1 + 0 + 3 + 5 + 4 + 1 ≤ L + 2 * T + 100 := by omega

private theorem linPrimarySuccessGuard {a w L T : ℕ} (ha : a ≤ L) (hw : w ≤ T) :
    a + 1 + 2 + 3 + T + w + 1 ≤ L + 2 * T + 100 := by omega

private theorem linPrimaryTailInput {a z ans W Z L : ℕ} (ha : a ≤ W) (hz : z ≤ Z) (hans : ans ≤ L) :
    a + z + ans ≤ 100 * (W + Z + L + 1) := by omega

set_option maxHeartbeats 3000000 in
theorem linPrimaryStep_spec (hm : ConstructiveMembership) (hv : VectorStabilizer)
    {P : Program} {b jm jv n p d : ℕ} (hat : linPrimaryStepAt P b jm jv hm hv)
    (gs : List (Equiv.Perm (Fin n))) (hp : p.Prime) (hpn : p ≤ n)
    [NeZero n] (ν : Fin d → ℕ) (level : ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (hs : IsSolvable ρ.range)
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν))
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (hf : ∀ g, linPrimaryFiber p ν level (c g)) (x : linFiniteVec (linPrimaryOrders p ν))
    (hx : linPrimaryFiber p ν level x) (acc : Equiv.Perm (Fin n)) :
    let a := linPrimaryIterationVal gs (linPrimaryOrders p ν) ρ c x acc p ν level
    FunAll P b a (fun out cost => linPrimaryStepOut gs hp hpn ν level ρ hs c hc hf x acc out ∧
      cost ≤ linPrimaryStepCost hm hv a.wt level) := by
  let m := linPrimaryOrders p ν
  let a := linPrimaryIterationVal gs m ρ c x acc p ν level
  let W := a.wt
  let zero := encVec (0 : Fin d → ZMod p)
  let I := linPrimaryLayerInst gs hp hpn ν level ρ hs x
  let c' : gens I.gs → Fin I.d → ZMod I.p := fun g => linPrimaryCoord p ν level (c g)
  let hc' := linPrimaryLayer_cocycle gs hp hpn ν level ρ hs c hc hf x
  let layerArg := Val.list [linPrimaryInputVal gs ν level ρ c x, zero]
  let Z := linPrimaryStepZeroBudget W
  let A := linPrimaryStepArgBudget W
  let L := linPrimaryStepLayerBudget hv W level
  let T := linPrimaryStepTailBudget hm hv W level
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => Val.nat (ν i))
    simp only [List.length_map, List.length_finRange] at hh
    have ww : (encFun ν).wt < W := wt_le_wt_list (by simp [W, a, linPrimaryIterationVal])
    change d < (encFun ν).wt at hh
    omega
  have hz := (linPrimaryZero_spec (p := p) (d := d) hat.replicate).mono
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hd 1) 3))
  have wz : zero.wt ≤ Z := hz.wt_lt.le
  have dz := linPrimaryStep_zero_det (p := p) hat.replicate gs m ρ c x acc ν level
  have da0 := linPrimaryStepLayerArg_spec (P := P) gs ν level ρ c x acc zero
  have ha : 100000 * (W + zero.wt + 1) ≤ A :=
    Nat.mul_le_mul (by decide : 100000 ≤ 1000000) (Nat.add_le_add_right (Nat.add_le_add_left wz W) 1)
  have da : Det P [a, zero] linPrimaryStepLayerArgE layerArg A := da0.mono ha
  have warg : layerArg.wt ≤ A := linDet_wt_le da
  have hlayer : FunAll P (b + 4) layerArg (fun out cost => linAffineTransportOut I c' hc' 0 out ∧ cost ≤ L) :=
    FunAll.mono (linPrimaryTransport_spec hv hat.layer gs hp hpn ν level ρ hs c hc hf x 0)
      (fun out cost ho => ⟨ho.1, ho.2.trans (linPrimaryTransportCost_mono hv warg le_rfl)⟩)
  have call := normBound_call da hlayer
  apply FunAll.intro hat.entry
  apply EvalAll.letE dz
  intro z cz hzpost
  obtain ⟨rfl, hcz⟩ := hzpost
  apply EvalAll.letE call
  intro ans cl ho
  have hcl := ho.2.2
  have wans := ho.2.1
  have hnext := linPrimaryTransportOut_next gs hp hpn ν level ρ hs c hc hf x hx ans ho.1
  rcases hnext with ⟨rfl, hno⟩ | ⟨g, sv, hans, hg, hgens⟩
  · have dlen := Det.length (Det.var' (P := P) (env := [a, zero, .list []]) (i := 2) rfl)
    have de := Det.ite_zero (t := linPrimaryStepTailF (b + 233) (b + 300) (b + 347) (b + 425)) dlen (Det.nil (P := P) (env := [a, zero, .list []]))
    refine de.post fun outCost hout => ⟨Or.inl ⟨rfl, hno⟩, ?_⟩
    have hb : (Val.list []).wt + 1 + 0 + 3 + 5 + (Val.list []).wt + 1 ≤ L + 2 * T + 100 := by
      exact linPrimaryFailGuard L T
    have hw : (Val.list []).wt ≤ T + 4 := Nat.le_add_left 4 T
    have hb' := hout.trans hb
    have htotal := linPrimaryWholeCost (T := T) hcz hcl hb' hw
    change _ ≤ linPrimaryStepCost hm hv W level
    exact htotal
  · subst ans
    obtain ⟨newgs, hraw, hlen, heq⟩ := hgens
    have hle : gens newgs ≤ gens gs := by
      rw [heq]
      exact linPrimaryNextTarget_le gs hp hpn ν level ρ hs c hc hf x
    subst sv
    let result := Val.list [linActionContext newgs m (ρ.comp (Subgroup.inclusion hle)) (c ∘ Subgroup.inclusion hle),
      linFinitePointVal m (ρ g x + c g), encPerm (g.val * acc)]
    have wtarg : a.wt + zero.wt + (Val.list [encPerm g.val, .list (newgs.map encPerm)]).wt ≤
        linPrimaryStepTailArg hv W level := by
      exact linPrimaryTailInput (show a.wt ≤ W from le_rfl) wz wans
    have dt := (linPrimaryStep_success_spec hm hv hat gs newgs hle m (fun i => Nat.pow_pos hp.pos)
      ρ c hc g x acc p ν level zero).mono (linPrimarySuccessCost_mono hm wtarg)
    change Det P [a, zero, .list [encPerm g.val, .list (newgs.map encPerm)]]
      (linPrimaryStepTailF (b + 233) (b + 300) (b + 347) (b + 425)) result T at dt
    have wr := linDet_wt_le dt
    have dlen := Det.length (Det.var' (P := P)
      (env := [a, zero, .list [encPerm g.val, .list (newgs.map encPerm)]]) (i := 2) rfl)
    have di := Det.ite_pos (e := .nil) dlen (by change (2 : ℕ) ≠ 0; decide) dt
    refine di.post fun outCost hout => ⟨Or.inr ⟨g, newgs, hle, hlen, heq, rfl, hg⟩, ?_⟩
    have hb : (Val.list [encPerm g.val, .list (newgs.map encPerm)]).wt + 1 + 2 + 3 + T + result.wt + 1 ≤
        L + 2 * T + 100 := linPrimarySuccessGuard wans wr
    have hb' := hout.trans hb
    have hw : result.wt ≤ T + 4 := wr.trans (Nat.le_add_right T 4)
    have htotal := linPrimaryWholeCost hcz hcl hb' hw
    change _ ≤ linPrimaryStepCost hm hv W level
    exact htotal

end GI.Impl
