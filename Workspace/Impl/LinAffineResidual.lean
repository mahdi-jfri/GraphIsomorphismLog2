module

public import Workspace.Impl.LinPrimaryLayerTransport

@[expose] public section

/-! After choosing a representative for one quotient layer, full transport
continues inside the target-fiber subgroup. This is the coset invariant of the
primary loop. -/
namespace GI.Impl

variable {G V : Type*} [Group G] [AddCommGroup V]

noncomputable def linFiniteEval (ρ : G →* (V ≃+ V)) (c : G → V) (g : G) (x : V) : V := ρ g x + c g

theorem linFiniteCocycle_one (ρ : G →* (V ≃+ V)) (c : G → V)
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) : c 1 = 0 := by
  have hh := hc 1 1
  rw [one_mul, map_one] at hh
  change c 1 = c 1 + c 1 at hh
  exact (add_left_cancel (show c 1 + 0 = c 1 + c 1 by simpa using hh)).symm

theorem linFiniteEval_mul (ρ : G →* (V ≃+ V)) (c : G → V)
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (g h : G) (x : V) :
    linFiniteEval ρ c (g * h) x = linFiniteEval ρ c g (linFiniteEval ρ c h x) := by
  unfold linFiniteEval
  rw [hc, map_mul]
  change ρ g (ρ h x) + (ρ g (c h) + c g) = ρ g (ρ h x + c h) + c g
  rw [map_add, add_assoc]

theorem linFiniteCocycle_inv (ρ : G →* (V ≃+ V)) (c : G → V)
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (g : G) :
    c g⁻¹ = -(ρ g⁻¹ (c g)) := by
  have hh := hc g⁻¹ g
  rw [inv_mul_cancel, linFiniteCocycle_one ρ c hc] at hh
  exact eq_neg_of_add_eq_zero_right hh.symm

/-- The cover subgroup preserving the chosen target fiber. -/
noncomputable def linAffineFiberSubgroup (ρ : G →* (V ≃+ V)) (c : G → V)
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (S : AddSubgroup V)
    (hρ : ∀ g x, x ∈ S → ρ g x ∈ S) : Subgroup G where
  carrier := {g | c g ∈ S}
  one_mem' := by simpa only [Set.mem_setOf_eq, linFiniteCocycle_one ρ c hc] using S.zero_mem
  mul_mem' := by
    intro g h hg hh
    change c (g * h) ∈ S
    rw [hc]
    exact S.add_mem (hρ g (c h) hh) hg
  inv_mem' := by
    intro g hg
    change c g⁻¹ ∈ S
    rw [linFiniteCocycle_inv ρ c hc]
    exact S.neg_mem (hρ g⁻¹ (c g) hg)

/-- Choosing one layer representative replaces the transporter by a residual
transporter in the target-fiber subgroup, multiplied on the right by that representative. -/
theorem linFiniteAffineResidual (ρ : G →* (V ≃+ V)) (c : G → V)
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (S : AddSubgroup V)
    (hρ : ∀ g x, x ∈ S → ρ g x ∈ S) (x : V) (g : G)
    (hg : linFiniteEval ρ c g x ∈ S) :
    {h : G | linFiniteEval ρ c h x = 0} =
      (fun k : G => k * g) '' {k | k ∈ linAffineFiberSubgroup ρ c hc S hρ ∧
        linFiniteEval ρ c k (linFiniteEval ρ c g x) = 0} := by
  ext h
  constructor
  · intro hh
    let k := h * g⁻¹
    have he : linFiniteEval ρ c k (linFiniteEval ρ c g x) = 0 := by
      rw [← linFiniteEval_mul ρ c hc]
      simpa only [Set.mem_setOf_eq, k, mul_assoc, inv_mul_cancel, mul_one] using hh
    have hk : c k ∈ S := by
      have hs := hρ k (linFiniteEval ρ c g x) hg
      have hn : c k = -(ρ k (linFiniteEval ρ c g x)) :=
        eq_neg_of_add_eq_zero_right he
      rw [hn]
      exact S.neg_mem hs
    exact ⟨k, ⟨hk, he⟩, by simp [k, mul_assoc]⟩
  · rintro ⟨k, ⟨_, he⟩, rfl⟩
    exact (linFiniteEval_mul ρ c hc k g x).trans he

end GI.Impl
