import Workspace.OrbitLocalization
import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.Subgroup.Center

open scoped commutatorElement

namespace GI

variable {H S X B : Type*} [Group H] [Group S]

theorem simple_central_eq_one [IsSimpleGroup S]
    (nonabelian : ∃ a b : S, a * b ≠ b * a) {z : S}
    (hz : ∀ s : S, s * z = z * s) : z = 1 := by
  have hn : (Subgroup.center S).Normal := inferInstance
  rcases hn.eq_bot_or_eq_top with hbot | htop
  · have hm : z ∈ Subgroup.center S := Subgroup.mem_center_iff.mpr hz
    simpa only [hbot, Subgroup.mem_bot] using hm
  · obtain ⟨a, b, hab⟩ := nonabelian
    have hb : b ∈ Subgroup.center S := by rw [htop]; exact Subgroup.mem_top b
    exact False.elim (hab (Subgroup.mem_center_iff.mp hb a))

/-- If all commutators with a surjecting subgroup are killed, the other element is killed.
This is the centerlessness argument used at a local block stabilizer. -/
theorem killed_commutators_force_killed [IsSimpleGroup S]
    (φ : H →* S) (U : Subgroup H)
    (onto : Function.Surjective (φ.comp U.subtype))
    (nonabelian : ∃ a b : S, a * b ≠ b * a) (t : H)
    (hcomm : ∀ u : U, φ ⁅(u : H), t⁆ = 1) : φ t = 1 := by
  apply simple_central_eq_one nonabelian
  intro s
  obtain ⟨u, hu⟩ := onto s
  have hc := hcomm u
  rw [map_commutatorElement] at hc
  have hmul := commutatorElement_eq_one_iff_mul_comm.mp hc
  change φ (u : H) = s at hu
  simpa only [hu] using hmul

variable [MulAction H X] [MulAction H B]

/-- Kernel of the actual action on block labels. -/
def blockActionKernel : Subgroup H := (MulAction.toPermHom H B).ker

theorem mem_blockActionKernel_iff (h : H) :
    h ∈ blockActionKernel (H := H) (B := B) ↔ ∀ b : B, h • b = b := by
  constructor
  · intro hh b
    have heq := congrArg (fun p : Equiv.Perm B => p b) hh
    exact heq
  · intro hh
    apply Equiv.ext
    exact hh

instance blockActionKernel_normal : (blockActionKernel (H := H) (B := B)).Normal :=
  MonoidHom.normal_ker _

/-- The full one-mark block dichotomy underlying Lemma A.5.

The block map and both actions are actual supplied maps. A physically visible simple
quotient with transitive kernel either factors through the block action, or is visible
and onto in the stabilizer action on the fiber through `a`. In each case the induced
kernel is transitive on that new domain. This theorem does not assume a localization
or chain-transfer conclusion. The cumulative inequality for sigma is a separate theorem.
-/
theorem visible_block_dichotomy [Fintype X] [IsSimpleGroup S]
    (φ : H →* S) (onto : Function.Surjective φ)
    (nonabelian : ∃ s t : S, s * t ≠ t * s)
    (f : X → B) (surjective : Function.Surjective f)
    (equivariant : ∀ h : H, ∀ x : X, f (h • x) = h • f x)
    (visible : ∀ h : H, (∀ x : X, h • x = x) → φ h = 1)
    (kernel_transitive : ∀ x y : X, ∃ n : H, φ n = 1 ∧ n • x = y)
    (a : X) :
    ((∀ h : H, (∀ b : B, h • b = b) → φ h = 1) ∧
      (∀ b c : B, ∃ n : H, φ n = 1 ∧ n • b = c)) ∨
    ((∀ s : S, ∃ h : H, h • f a = f a ∧ φ h = s) ∧
      (∀ t : H, t • f a = f a →
        (∀ x : X, f x = f a → t • x = x) → φ t = 1) ∧
      (∀ x y : X, f x = f a → f y = f a →
        ∃ n : H, φ n = 1 ∧ n • f a = f a ∧ n • x = y)) := by
  let U := blockActionKernel (H := H) (B := B)
  haveI : U.Normal := blockActionKernel_normal
  rcases ((inferInstance : U.Normal).map φ onto).eq_bot_or_eq_top with hbot | htop
  · left
    constructor
    · intro h hh
      have hU : h ∈ U := (mem_blockActionKernel_iff h).2 hh
      have himage := Subgroup.mem_map_of_mem φ hU
      simpa only [hbot, Subgroup.mem_bot] using himage
    · intro b c
      obtain ⟨x, rfl⟩ := surjective b
      obtain ⟨y, rfl⟩ := surjective c
      obtain ⟨n, hn, hxy⟩ := kernel_transitive x y
      exact ⟨n, hn, (equivariant n x).symm.trans (congrArg f hxy)⟩
  · right
    have honto : Function.Surjective (φ.comp U.subtype) := by
      intro s
      have hs : s ∈ U.map φ := by rw [htop]; exact Subgroup.mem_top s
      obtain ⟨u, hu, hus⟩ := hs
      exact ⟨⟨u, hu⟩, hus⟩
    have htrans : ∀ x y : X, ∃ h : H, h • x = y := by
      intro x y
      obtain ⟨n, _, hxy⟩ := kernel_transitive x y
      exact ⟨n, hxy⟩
    have hlocal_visible : ∀ t : H, t • f a = f a →
        (∀ x : X, f x = f a → t • x = x) → φ t = 1 := by
      intro t _ hfix
      apply killed_commutators_force_killed φ U honto nonabelian t
      intro u
      let c : U := ⟨⁅(u : H), t⁆,
        Subgroup.commutator_le_left U ⊤
          (Subgroup.commutator_mem_commutator u.property (Subgroup.mem_top t))⟩
      have hc : c ∈ orbitKernel U a := by
        intro v
        have hvfix := (mem_blockActionKernel_iff (v : H)).1 v.property
        have hufix := (mem_blockActionKernel_iff (u : H)⁻¹).1 (U.inv_mem u.property)
        have hv : f ((v : H) • a) = f a := (equivariant _ _).trans (hvfix _)
        have huv : f ((u : H)⁻¹ • ((v : H) • a)) = f a := by
          rw [equivariant, hv, hufix]
        have htfix := hfix _ hv
        have htinv : t⁻¹ • ((v : H) • a) = (v : H) • a := by
          have hh := congrArg (fun z : X => t⁻¹ • z) htfix
          simpa using hh.symm
        change ⁅(u : H), t⁆ • ((v : H) • a) = (v : H) • a
        simp only [commutatorElement_def, mul_smul]
        rw [htinv, hfix _ huv]
        exact smul_inv_smul _ _
      exact every_orbit_kernel_killed U φ honto nonabelian htrans
        (fun k hk => visible k hk) a c hc
    refine ⟨?_, hlocal_visible, ?_⟩
    · intro s
      obtain ⟨u, hu⟩ := honto s
      exact ⟨u, (mem_blockActionKernel_iff (u : H)).1 u.property (f a), hu⟩
    · intro x y hx hy
      obtain ⟨n, hn, hxy⟩ := kernel_transitive x y
      refine ⟨n, hn, ?_, hxy⟩
      calc
        n • f a = n • f x := by rw [hx]
        _ = f (n • x) := (equivariant n x).symm
        _ = f y := congrArg f hxy
        _ = f a := hy

end GI
