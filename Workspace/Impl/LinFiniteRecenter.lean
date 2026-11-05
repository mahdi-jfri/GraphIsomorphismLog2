module

public import Workspace.Impl.LinAffineResidual

@[expose] public section

/-! Translate the target point to zero before processing its characteristic
primary components. The cover and its multiplication convention do not change. -/
namespace GI.Impl

variable {G V : Type*} [Group G] [AddCommGroup V]

def linFiniteRecenter (ρ : G →* (V ≃+ V)) (c : G → V) (w : V) (g : G) : V :=
  ρ g w + c g - w

theorem linFiniteRecenter_cocycle (ρ : G →* (V ≃+ V)) (c : G → V)
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (w : V) (g h : G) :
    linFiniteRecenter ρ c w (g * h) =
      ρ g (linFiniteRecenter ρ c w h) + linFiniteRecenter ρ c w g := by
  simp only [linFiniteRecenter, hc, map_add, map_sub, map_mul]
  change ρ g (ρ h w) + (ρ g (c h) + c g) - w = _
  abel

theorem linFiniteRecenter_eval (ρ : G →* (V ≃+ V)) (c : G → V)
    (w v : V) (g : G) :
    linFiniteEval ρ (linFiniteRecenter ρ c w) g (v - w) =
      linFiniteEval ρ c g v - w := by
  simp only [linFiniteEval, linFiniteRecenter, map_sub]
  abel

theorem linFiniteRecenter_transport (ρ : G →* (V ≃+ V)) (c : G → V)
    (w v : V) (g : G) :
    linFiniteEval ρ (linFiniteRecenter ρ c w) g (v - w) = 0 ↔
      linFiniteEval ρ c g v = w := by
  rw [linFiniteRecenter_eval, sub_eq_zero]

theorem linFiniteRecenter_stabilizer (ρ : G →* (V ≃+ V)) (c : G → V)
    (w : V) (g : G) :
    linFiniteRecenter ρ c w g = 0 ↔ linFiniteEval ρ c g w = w := by
  exact sub_eq_zero

end GI.Impl
