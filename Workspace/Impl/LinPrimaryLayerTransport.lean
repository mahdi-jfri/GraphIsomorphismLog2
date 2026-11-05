module

public import Workspace.Impl.LinPrimaryCoordinateKernel
public import Workspace.Impl.LinAffineTransport

@[expose] public section

/-! The field transporter and stabilizer tests are exactly the next primary
fiber tests for the retained full affine action. -/
namespace GI.Impl

/-- Every full affine transformation whose offset is in the current fiber
preserves that fiber. -/
theorem linPrimaryFiber_affine {d : ℕ} (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (f : linFiniteVec (linPrimaryOrders p ν) →+ linFiniteVec (linPrimaryOrders p ν))
    (x u : linFiniteVec (linPrimaryOrders p ν))
    (hx : linPrimaryFiber p ν j x) (hu : linPrimaryFiber p ν j u) :
    linPrimaryFiber p ν j (f x + u) := by
  rw [linPrimaryFiber_powerLayer p hp ν j] at hx hu ⊢
  obtain ⟨y, hy⟩ := (linPowerLayer_mem p j x).mp hx
  obtain ⟨z, hz⟩ := (linPowerLayer_mem p j u).mp hu
  apply (linPowerLayer_mem p j _).mpr
  refine ⟨f y + z, ?_⟩
  rw [smul_add, ← map_zsmul, hy, hz]

/-- Solving the field equation with zero target moves the full point into the
next layer. This is why the target origin can remain zero throughout. -/
theorem linPrimaryTransport_next {d : ℕ} (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (f : linFiniteVec (linPrimaryOrders p ν) →+ linFiniteVec (linPrimaryOrders p ν))
    (x u : linFiniteVec (linPrimaryOrders p ν))
    (hx : linPrimaryFiber p ν j x) (hu : linPrimaryFiber p ν j u) :
    (linPrimaryFieldMatrix p ν j f).mulVec (linPrimaryCoord p ν j x) + linPrimaryCoord p ν j u = 0 ↔
      linPrimaryFiber p ν (j + 1) (f x + u) := by
  rw [← linPrimaryCoord_affine p hp ν j f x u hx hu]
  exact linPrimaryCoord_zero_iff p hp ν j (f x + u) (linPrimaryFiber_affine p hp ν j f x u hx hu)

/-- The target field stabilizer is precisely the subgroup whose full offsets
belong to the next layer. -/
theorem linPrimaryStabilizer_next {d : ℕ} (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (f : linFiniteVec (linPrimaryOrders p ν) →+ linFiniteVec (linPrimaryOrders p ν))
    (u : linFiniteVec (linPrimaryOrders p ν)) (hu : linPrimaryFiber p ν j u) :
    (linPrimaryFieldMatrix p ν j f).mulVec 0 + linPrimaryCoord p ν j u = 0 ↔
      linPrimaryFiber p ν (j + 1) u := by
  rw [Matrix.mulVec_zero, zero_add]
  exact linPrimaryCoord_zero_iff p hp ν j u hu

/-- Restricting the full cover to the target stabilizer supplies the invariant
needed for the next invocation. -/
theorem linPrimaryRestriction_next {G : Type*} [Group G] {d : ℕ}
    (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (ρ : G →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : G → linFiniteVec (linPrimaryOrders p ν))
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g)
    (hmem : ∀ g, linPrimaryFiber p ν j (c g)) :
    ∀ g : G, (linPrimaryFieldRep p hp ν j ρ g).val.mulVec 0 + linPrimaryCoord p ν j (c g) = 0 ↔
      linPrimaryFiber p ν (j + 1) (c g) := by
  intro g
  exact linPrimaryStabilizer_next p hp ν j (ρ g).toAddMonoidHom (c g) (hmem g)

end GI.Impl
