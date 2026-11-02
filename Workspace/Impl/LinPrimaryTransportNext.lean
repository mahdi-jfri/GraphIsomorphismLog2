import Workspace.Impl.LinPrimaryTransport

/-! The executable field answer has precisely the next-fiber meaning needed
by the primary loop, including a proved failure branch. -/
namespace GI.Impl
open GI.Cited GI.Lang

theorem linPrimaryLayerTarget_mem {n p d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (hs : IsSolvable (gens gs)) (hp : p.Prime) (hpn : p ≤ n) (ν : Fin d → ℕ) (level : ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν))
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (hf : ∀ g, linPrimaryFiber p ν level (c g)) (x : linFiniteVec (linPrimaryOrders p ν))
    (g : gens gs) :
    let I := linPrimaryLayerInst gs hs hp hpn ν level ρ x
    let c' : gens I.gs → Fin I.d → ZMod I.p := fun g => linPrimaryCoord p ν level (c g)
    let hc' := linPrimaryLayer_cocycle gs hs hp hpn ν level ρ c hc hf x
    g.val ∈ linAffineTargetSub I c' hc' 0 ↔ linPrimaryFiber p ν (level + 1) (c g) := by
  let I := linPrimaryLayerInst gs hs hp hpn ν level ρ x
  let c' : gens I.gs → Fin I.d → ZMod I.p := fun g => linPrimaryCoord p ν level (c g)
  let hc' := linPrimaryLayer_cocycle gs hs hp hpn ν level ρ c hc hf x
  have hh := linAffineTargetSub_mem I c' hc' 0 (g : gens I.gs)
  change g.val ∈ linAffineTargetSub I c' hc' 0 ↔ _
  refine hh.trans ?_
  simp only [Matrix.mulVec_zero, zero_add]
  exact linPrimaryCoord_zero_iff p hp.pos ν level (c g) (hf g)

theorem linPrimaryTransportOut_next {n p d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (hs : IsSolvable (gens gs)) (hp : p.Prime) (hpn : p ≤ n) (ν : Fin d → ℕ) (level : ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν))
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (hf : ∀ g, linPrimaryFiber p ν level (c g))
    (x : linFiniteVec (linPrimaryOrders p ν)) (hx : linPrimaryFiber p ν level x) (out : Val) :
    let I := linPrimaryLayerInst gs hs hp hpn ν level ρ x
    let c' : gens I.gs → Fin I.d → ZMod I.p := fun g => linPrimaryCoord p ν level (c g)
    let hc' := linPrimaryLayer_cocycle gs hs hp hpn ν level ρ c hc hf x
    linAffineTransportOut I c' hc' 0 out →
      (out = .list [] ∧ ¬∃ g : gens gs, linPrimaryFiber p ν (level + 1) (ρ g x + c g)) ∨
      ∃ (g : gens gs) (sv : Val), out = .list [encPerm g.val, sv] ∧
        linPrimaryFiber p ν (level + 1) (ρ g x + c g) ∧
        GensVal n sv (linAffineTargetSub I c' hc' 0) := by
  dsimp only
  intro ho
  have he (g : gens gs) :
      (linPrimaryFieldRep p hp.pos ν level ρ g).val.mulVec
        (linPrimaryCoord p ν level x) + linPrimaryCoord p ν level (c g) = 0 ↔
      linPrimaryFiber p ν (level + 1) (ρ g x + c g) :=
    linPrimaryTransport_next p hp.pos ν level (ρ g).toAddMonoidHom x (c g) hx (hf g)
  rcases ho with ⟨hout, hno⟩ | ⟨g, sv, hout, hg, hgens⟩
  · exact Or.inl ⟨hout, fun ⟨g, hg⟩ => hno ⟨g, (he g).mpr hg⟩⟩
  · exact Or.inr ⟨g, sv, hout, (he g).mp hg, hgens⟩

end GI.Impl
