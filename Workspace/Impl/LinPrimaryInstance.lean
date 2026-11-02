import Workspace.Impl.LinPrimaryInput
import Workspace.Impl.LinPrimaryLayerTransport

/-! Identify the executable primary input with the cited field task on the
original solvable permutation cover. No faithful quotient action is required. -/
namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linPrimaryLayerInst {n p d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (hs : IsSolvable (gens gs)) (hp : p.Prime) (hpn : p ≤ n) (ν : Fin d → ℕ) (level : ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (x : linFiniteVec (linPrimaryOrders p ν)) : VecStabInst where
  n := n
  gs := gs
  solvable := hs
  p := p
  prime := hp
  p_le := hpn
  d := d
  φ := linPrimaryFieldRep p hp.pos ν level ρ
  v := linPrimaryCoord p ν level x

noncomputable def linPrimaryGeneratorList {n : ℕ} (gs : List (Equiv.Perm (Fin n))) : List (gens gs) :=
  gs.attach.map fun g => ⟨g.val, Subgroup.subset_closure g.property⟩

noncomputable def linPrimaryInputVal {n p d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (ν : Fin d → ℕ) (level : ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν))
    (x : linFiniteVec (linPrimaryOrders p ν)) : Val :=
  .list [encGroup gs, .nat p, encFun ν, .nat level,
    .list ((linPrimaryGeneratorList gs).map (linFiniteAffineVal (linPrimaryOrders p ν) ρ c)),
    linFinitePointVal (linPrimaryOrders p ν) x]

theorem linPrimaryInput_layer_spec {P : Program} {b n p d : ℕ} (h : linPrimaryInputAt P b)
    (gs : List (Equiv.Perm (Fin n))) (hs : IsSolvable (gens gs)) (hp : p.Prime) (hpn : p ≤ n)
    (ν : Fin d → ℕ) (level : ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν))
    (x : linFiniteVec (linPrimaryOrders p ν)) :
    FunDet P b (linPrimaryInputVal gs ν level ρ c x)
      (linAffineLayerInput (linPrimaryLayerInst gs hs hp hpn ν level ρ x)
        (fun g => linPrimaryCoord p ν level (c g)))
      (linPrimaryInputCost (linPrimaryInputVal gs ν level ρ c x).wt level) := by
  simpa only [linPrimaryInputVal, linAffineLayerInput, linPrimaryLayerInst,
    linPrimaryGeneratorList, List.map_map, Function.comp_def] using
    linPrimaryInput_spec h hp (encGroup gs) ν level ρ c (linPrimaryGeneratorList gs) x

theorem linPrimaryLayer_cocycle {n p d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (hs : IsSolvable (gens gs)) (hp : p.Prime) (hpn : p ≤ n) (ν : Fin d → ℕ) (level : ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν))
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g)
    (hf : ∀ g, linPrimaryFiber p ν level (c g)) (x : linFiniteVec (linPrimaryOrders p ν)) :
    let I := linPrimaryLayerInst gs hs hp hpn ν level ρ x
    let c' : gens I.gs → Fin I.d → ZMod I.p := fun g => linPrimaryCoord p ν level (c g)
    ∀ g k, c' (g * k) = (I.φ g).val.mulVec (c' k) + c' g :=
  fun g k => linPrimaryCoord_cocycle p hp.pos ν level ρ c hc hf g k

end GI.Impl
