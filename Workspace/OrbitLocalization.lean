module

public import Workspace.Localization
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Fintype.List

@[expose] public section

namespace GI

variable {H S D : Type*} [Group H] [Group S] [MulAction H D]

/-- The pointwise kernel on the U-orbit of a, as an actual subgroup of U. -/
def orbitKernel (U : Subgroup H) (a : D) : Subgroup U where
  carrier := {k | ∀ v : U, (k : H) • ((v : H) • a) = (v : H) • a}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro k l hk hl v
    change ((k : H) * (l : H)) • ((v : H) • a) = _
    rw [mul_smul, hl v, hk v]
  inv_mem' := by
    intro k hk v
    have hh := congrArg (fun z : D => (k : H)⁻¹ • z) (hk v)
    simpa using hh.symm

theorem orbitKernel_normal (U : Subgroup H) (a : D) : (orbitKernel U a).Normal := by
  constructor
  intro k hk g v
  have hh := hk (g⁻¹ * v)
  change (k : H) • (((g : H)⁻¹ * (v : H)) • a) = ((g : H)⁻¹ * (v : H)) • a at hh
  change ((g : H) * (k : H) * (g : H)⁻¹) • ((v : H) • a) = _
  simpa only [mul_smul, smul_inv_smul] using congrArg (fun z : D => (g : H) • z) hh

theorem mem_commonKernel_iff (Ks : List (Subgroup H)) (h : H) :
    h ∈ commonKernel Ks ↔ ∀ K ∈ Ks, h ∈ K := by
  induction Ks with
  | nil => simp [commonKernel]
  | cons K Ks ih => simp [commonKernel, ih]

/-- Conjugation transports the orbit kernel of a normal subgroup to the image orbit. -/
theorem orbitKernel_conjugate (U : Subgroup H) [U.Normal] {a b : D}
    (h : H) (hab : h • a = b) (k : U) (hk : k ∈ orbitKernel U a) :
    ∀ v : U, (h * (k : H) * h⁻¹) • ((v : H) • b) = (v : H) • b := by
  intro v
  let w : U := ⟨h⁻¹ * (v : H) * h, by
    simpa only [inv_inv] using (inferInstance : U.Normal).conj_mem _ v.property h⁻¹⟩
  have hh := hk w
  change (k : H) • ((h⁻¹ * (v : H) * h) • a) = (h⁻¹ * (v : H) * h) • a at hh
  rw [← hab]
  simpa only [mul_smul, smul_inv_smul] using congrArg (fun z : D => h • z) hh

/-- Lemma A.4's orbit assertion, with actual orbit kernels and the extended homomorphism.
No orbit-kernel conjugacy or localization premise is assumed here. -/
theorem every_orbit_kernel_killed [Fintype D] [IsSimpleGroup S]
    (U : Subgroup H) [U.Normal] (ψ : H →* S)
    (onto : Function.Surjective (ψ.comp U.subtype))
    (nonabelian : ∃ a b : S, a * b ≠ b * a)
    (transitive : ∀ a b : D, ∃ h : H, h • a = b)
    (wholeKilled : ∀ k : U, (∀ d : D, (k : H) • d = d) → ψ k = 1)
    (a : D) (k : U) (hk : k ∈ orbitKernel U a) : ψ k = 1 := by
  classical
  let points := (Finset.univ : Finset D).toList
  let kernels := points.map (orbitKernel U)
  let φ := ψ.comp U.subtype
  have hnormal : ∀ K ∈ kernels, K.Normal := by
    intro K hK
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hK
    exact orbitKernel_normal U b
  have hkilled : commonKernel kernels ≤ φ.ker := by
    intro u hu
    apply wholeKilled u
    intro d
    have hmem : orbitKernel U d ∈ kernels := by
      apply List.mem_map.mpr
      exact ⟨d, by simp [points], rfl⟩
    have hfix := (mem_commonKernel_iff kernels u).1 hu _ hmem
    simpa using hfix (1 : U)
  obtain ⟨K, hK, hbot⟩ := simple_quotient_localization φ onto nonabelian kernels hnormal hkilled
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hK
  obtain ⟨h, hab⟩ := transitive a b
  let c : U := ⟨h * (k : H) * h⁻¹, (inferInstance : U.Normal).conj_mem _ k.property h⟩
  have hc : c ∈ orbitKernel U b := orbitKernel_conjugate U h hab k hk
  have himage : φ c ∈ (orbitKernel U b).map φ := Subgroup.mem_map_of_mem φ hc
  rw [hbot, Subgroup.mem_bot] at himage
  have heq : ψ h * ψ k * (ψ h)⁻¹ = 1 := by
    simpa [φ, c] using himage
  have heq' := congrArg (fun s : S => (ψ h)⁻¹ * s * ψ h) heq
  simpa only [mul_assoc, inv_mul_cancel_left, one_mul, inv_mul_cancel, mul_one] using heq'

end GI
