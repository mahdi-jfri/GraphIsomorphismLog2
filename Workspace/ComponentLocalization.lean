import Workspace.CartesianCover

open scoped commutatorElement

namespace GI.CartesianCover

variable {I D S : Type*} [Group S]
variable {H : Subgroup (Equiv.Perm (I → D))}

/-- A visible simple quotient surjecting from the position kernel is killed
by the active-orbit kernel in at least one actual component action. -/
theorem exists_component_kernel_killed [Fintype I] [Fintype D] [IsSimpleGroup S]
    (c : CartesianCover H) (φ : H →* S)
    (onto : Function.Surjective (φ.comp c.positions.ker.subtype))
    (nonabelian : ∃ s t : S, s * t ≠ t * s) (v : I → D)
    (transitive : ∀ h : H, ∃ n : H, φ n = 1 ∧ n • v = h • v)
    (visible : ∀ h : H, (∀ g : H, h • (g • v) = g • v) → φ h = 1) :
    ∃ i : I, ∀ k : c.positions.ker,
      k ∈ actionOrbitKernel (c.kernelComponent i) (v i) → φ k = 1 := by
  classical
  let K := c.positions.ker
  let ψ := φ.comp K.subtype
  let indices := (Finset.univ : Finset I).toList
  let kernels := indices.map (fun i => actionOrbitKernel (c.kernelComponent i) (v i))
  have hn : ∀ Q ∈ kernels, Q.Normal := by
    intro Q hQ
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hQ
    exact actionOrbitKernel_normal _ _
  have hkilled : commonKernel kernels ≤ ψ.ker := by
    intro k hk
    apply every_active_orbit_kernel_killed K φ onto nonabelian v transitive visible k
    intro g
    apply funext
    intro i
    have hmem : actionOrbitKernel (c.kernelComponent i) (v i) ∈ kernels := by
      apply List.mem_map.mpr
      exact ⟨i, by simp [indices], rfl⟩
    have hi := (mem_commonKernel_iff kernels k).mp hk _ hmem
    have hfix := (mem_actionOrbitKernel_iff (c.kernelComponent i) (v i) k).mp hi g
    rw [c.kernelComponent_apply i g v,
      c.kernelComponent_apply i k ((g.val : Equiv.Perm (I → D)) v)] at hfix
    exact hfix
  obtain ⟨Q, hQ, hbot⟩ := simple_quotient_localization ψ onto nonabelian kernels hn hkilled
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hQ
  refine ⟨i, ?_⟩
  intro k hk
  have hm := Subgroup.mem_map_of_mem ψ hk
  simpa only [hbot, Subgroup.mem_bot] using hm

/-- Centerlessness promotes visibility in a position-kernel component to
visibility in the full stabilizer of that coordinate. -/
theorem component_visible_of_kernel [IsSimpleGroup S]
    (c : CartesianCover H) (φ : H →* S)
    (onto : Function.Surjective (φ.comp c.positions.ker.subtype))
    (nonabelian : ∃ s t : S, s * t ≠ t * s) (v : I → D) (i : I)
    (killed : ∀ k : c.positions.ker,
      k ∈ actionOrbitKernel (c.kernelComponent i) (v i) → φ k = 1)
    (t : coordinateStabilizer c.positions i)
    (fixed : ∀ g : coordinateStabilizer c.positions i,
      c.component i t (c.component i g (v i)) = c.component i g (v i)) : φ t.val = 1 := by
  apply killed_commutators_force_killed φ c.positions.ker onto nonabelian t.val
  intro u
  let z : c.positions.ker := ⟨⁅u.val, t.val⁆,
    Subgroup.commutator_le_left c.positions.ker ⊤
      (Subgroup.commutator_mem_commutator u.property (Subgroup.mem_top t.val))⟩
  apply killed z
  apply (mem_actionOrbitKernel_iff _ _ z).mpr
  intro g
  have hz : c.kernelComponent i z = ⁅c.kernelComponent i u, c.component i t⁆ := by
    change c.component i (c.kernelCoordinate i z) =
      ⁅c.component i (c.kernelCoordinate i u), c.component i t⁆
    rw [← map_commutatorElement]
    congr 1
  have hg : c.component i t (c.kernelComponent i g (v i)) =
      c.kernelComponent i g (v i) := fixed (c.kernelCoordinate i g)
  have hginv : (c.component i t)⁻¹ (c.kernelComponent i g (v i)) =
      c.kernelComponent i g (v i) := by
    have he := congrArg (fun x => (c.component i t)⁻¹ x) hg
    simpa using he.symm
  have hug : c.component i t ((c.kernelComponent i u)⁻¹ (c.kernelComponent i g (v i))) =
      (c.kernelComponent i u)⁻¹ (c.kernelComponent i g (v i)) := by
    have hh := fixed (c.kernelCoordinate i (u⁻¹ * g))
    change c.component i t (c.kernelComponent i (u⁻¹ * g) (v i)) =
      c.kernelComponent i (u⁻¹ * g) (v i) at hh
    simpa only [map_mul, map_inv, Equiv.Perm.mul_apply] using hh
  rw [hz]
  simp only [commutatorElement_def, Equiv.Perm.mul_apply]
  rw [hginv, hug]
  exact (c.kernelComponent i u).apply_symm_apply _

end GI.CartesianCover
