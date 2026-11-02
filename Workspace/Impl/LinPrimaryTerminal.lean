import Workspace.Impl.LinPrimaryHeight
import Workspace.Impl.LinAffineResidual

/-! At the computed height the primary fiber is zero. A completed transporter
is therefore a coset of the target stabilizer, as required before changing to
canonical left-coset output. -/
namespace GI.Impl

theorem linPrimaryFiber_height_iff {p d : ℕ} (hp : p.Prime) (ν : Fin d → ℕ)
    (x : linFiniteVec (linPrimaryOrders p ν)) :
    linPrimaryFiber p ν (linPrimaryHeight ν) x ↔ x = 0 := by
  constructor
  · exact linPrimaryFiber_terminal p hp.pos ν _ (linPrimaryHeight_ge ν) x
  · rintro rfl
    intro i
    simp

theorem linPrimaryTerminal_offsets {G : Type*} [Group G] {p d : ℕ}
    (hp : p.Prime) (ν : Fin d → ℕ) (c : G → linFiniteVec (linPrimaryOrders p ν))
    (hf : ∀ g, linPrimaryFiber p ν (linPrimaryHeight ν) (c g)) : ∀ g, c g = 0 :=
  fun g => (linPrimaryFiber_height_iff hp ν (c g)).mp (hf g)

theorem linFiniteAffineTransport_coset {G V : Type*} [Group G] [AddCommGroup V]
    (ρ : G →* (V ≃+ V)) (c : G → V)
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (x : V) (g : G)
    (hg : linFiniteEval ρ c g x = 0) :
    {h : G | linFiniteEval ρ c h x = 0} = (fun k : G => k * g) '' {k | c k = 0} := by
  have he := linFiniteAffineResidual ρ c hc (⊥ : AddSubgroup V)
    (fun h y hy => by
      change y = 0 at hy
      change ρ h y = 0
      simpa only [hy] using (ρ h).map_zero) x g
    (show linFiniteEval ρ c g x ∈ (⊥ : AddSubgroup V) by simpa using hg)
  rw [hg] at he
  change {h : G | linFiniteEval ρ c h x = 0} =
    (fun k : G => k * g) '' {k | c k ∈ (⊥ : AddSubgroup V) ∧ linFiniteEval ρ c k 0 = 0} at he
  simpa only [AddSubgroup.mem_bot, linFiniteEval, map_zero, zero_add, and_self] using he

end GI.Impl
