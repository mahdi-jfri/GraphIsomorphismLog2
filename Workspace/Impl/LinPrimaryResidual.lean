module

public import Workspace.Impl.LinPrimaryLoopInput

@[expose] public section

/-! The full-action facts used when the loop replaces its cover by a layer
stabilizer and multiplies its accumulated representative. -/
namespace GI.Impl

theorem linPrimaryFiber_zero {d : ℕ} (p : ℕ) (ν : Fin d → ℕ) (j : ℕ) :
    linPrimaryFiber p ν j (0 : linFiniteVec (linPrimaryOrders p ν)) := by
  intro i
  simp

theorem linPrimaryFiber_neg {d : ℕ} (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (x : linFiniteVec (linPrimaryOrders p ν)) (hx : linPrimaryFiber p ν j x) :
    linPrimaryFiber p ν j (-x) := by
  rw [linPrimaryFiber_powerLayer p hp ν j] at hx ⊢
  exact (linPowerLayer p j).neg_mem hx

theorem linPrimaryFiber_linear {d : ℕ} (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (f : linFiniteVec (linPrimaryOrders p ν) →+ linFiniteVec (linPrimaryOrders p ν))
    (x : linFiniteVec (linPrimaryOrders p ν)) (hx : linPrimaryFiber p ν j x) :
    linPrimaryFiber p ν j (f x) := by
  simpa only [add_zero] using linPrimaryFiber_affine p hp ν j f x 0 hx (linPrimaryFiber_zero p ν j)

theorem linPrimaryZero_forces_offset {d : ℕ} (p : ℕ) (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (f : linFiniteVec (linPrimaryOrders p ν) →+ linFiniteVec (linPrimaryOrders p ν))
    (x u : linFiniteVec (linPrimaryOrders p ν)) (hx : linPrimaryFiber p ν j x) (he : f x + u = 0) :
    linPrimaryFiber p ν j u := by
  have hu : u = -(f x) := eq_neg_of_add_eq_zero_right he
  rw [hu]
  exact linPrimaryFiber_neg p hp ν j (f x) (linPrimaryFiber_linear p hp ν j f x hx)

theorem linFiniteEval_residual {G V : Type*} [Group G] [AddCommGroup V]
    (ρ : G →* (V ≃+ V)) (c : G → V) (hc : ∀ g h, c (g * h) = ρ g (c h) + c g)
    (h r : G) (x : V) :
    linFiniteEval ρ c (h * r⁻¹) (linFiniteEval ρ c r x) = linFiniteEval ρ c h x := by
  rw [← linFiniteEval_mul ρ c hc]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

theorem linPrimaryResidual_factor {G : Type*} [Group G] {p d : ℕ}
    (hp : 0 < p) (ν : Fin d → ℕ) (j : ℕ)
    (ρ : G →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : G → linFiniteVec (linPrimaryOrders p ν)) (hc : ∀ g h, c (g * h) = ρ g (c h) + c g)
    (x : linFiniteVec (linPrimaryOrders p ν)) (h r : G)
    (hh : linFiniteEval ρ c h x = 0) (hr : linPrimaryFiber p ν j (linFiniteEval ρ c r x)) :
    linPrimaryFiber p ν j (c (h * r⁻¹)) := by
  have he := (linFiniteEval_residual ρ c hc h r x).trans hh
  exact linPrimaryZero_forces_offset p hp ν j (ρ (h * r⁻¹)).toAddMonoidHom
    (linFiniteEval ρ c r x) (c (h * r⁻¹)) hr he

end GI.Impl
