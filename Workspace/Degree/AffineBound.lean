module

public import Workspace.Degree.LinearBound
public import Workspace.PrimitiveAbelianNormal
public import Workspace.PrimitiveSolvableNormal

/-!
# The affine case

A faithful primitive group `G` in `Γ̂_D` with an abelian minimal normal subgroup `N` has
`log |G| ≤ (C log D + 1) log n` (`GI.Degree.log_card_affine_le`). This is the argument of
`GI.Proved.palfy_primitive_aux`, with `GI.Degree.log_card_linear_le` as the linear input: `N` is
regular and elementary abelian, the kernel of the conjugation action on `N` lies in `N`, and the
image is irreducible on `N`.
-/

@[expose] public section

namespace GI.Degree

open MulAction GI.Proved GI.RadicalSocle GI.PrimitiveStructure

/-- **The linear core.** If `N` is an elementary abelian `p`-group and `Hg ≤ Aut(N)` is in the
class, with no invariant subgroups besides `1` and `N`, then `log |Hg| ≤ C log D log |N|`. -/
theorem deg_affine_core {D : ℕ} (hD : 6 ≤ D) {N : Type} [CommGroup N] [Finite N] [Nontrivial N]
    (p : ℕ) [Fact p.Prime] [Module (ZMod p) (Additive N)] (Hg : Subgroup (MulAut N))
    (hcl : GammaHat D Hg)
    (hirr0 : ∀ W : Subgroup N, (∀ σ ∈ Hg, ∀ w ∈ W, σ w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Real.log (Nat.card Hg) ≤ linC * Real.log D * Real.log (Nat.card N) := by
  classical
  let L : MulAut N → Module.End (ZMod p) (Additive N) := fun σ =>
    AddMonoidHom.toZModLinearMap p (MonoidHom.toAdditive (σ : N →* N))
  have hL : ∀ σ : MulAut N, ∀ y : N, (L σ : Additive N →ₗ[ZMod p] Additive N) (Additive.ofMul y) = Additive.ofMul (σ y) :=
    fun _ _ => rfl
  let ψ : MulAut N →* (Module.End (ZMod p) (Additive N))ˣ :=
    { toFun := fun σ =>
        { val := L σ
          inv := L σ⁻¹
          val_inv := LinearMap.ext fun v => by
            change Additive.ofMul (σ (σ⁻¹ (Additive.toMul v))) = v
            rw [MulAut.apply_inv_self]
            rfl
          inv_val := LinearMap.ext fun v => by
            change Additive.ofMul (σ⁻¹ (σ (Additive.toMul v))) = v
            rw [MulAut.inv_apply_self]
            rfl }
      map_one' := Units.ext (LinearMap.ext fun v => rfl)
      map_mul' := fun σ τ => Units.ext (LinearMap.ext fun v => rfl) }
  have hψ : Function.Injective ψ := by
    intro σ τ h
    ext y
    have := congrArg (fun u : (Module.End (ZMod p) (Additive N))ˣ =>
      Additive.toMul ((u : Module.End (ZMod p) (Additive N)) (Additive.ofMul y))) h
    exact this
  set H := Hg.map ψ
  have hHcl : GammaHat D H := hcl.of_surjective _ (ψ.subgroupMap_surjective Hg)
  have hHcard : Nat.card H = Nat.card Hg := Subgroup.card_map_of_injective hψ
  -- irreducibility
  have hirr : palfyIrr H := by
    intro W hW
    let S0 : Subgroup N :=
      { carrier := {y | Additive.ofMul y ∈ W}
        mul_mem' := fun {y z} hy hz => by
          change Additive.ofMul y + Additive.ofMul z ∈ W
          exact W.add_mem hy hz
        one_mem' := by
          change (0 : Additive N) ∈ W
          exact W.zero_mem
        inv_mem' := fun {y} hy => by
          change -Additive.ofMul y ∈ W
          exact W.neg_mem hy }
    have hinv : ∀ σ ∈ Hg, ∀ w ∈ S0, σ w ∈ S0 := by
      intro σ hσ y hy
      change Additive.ofMul (σ y) ∈ W
      exact hW _ ⟨σ, hσ, rfl⟩ _ hy
    rcases hirr0 S0 hinv with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      have hy : (Additive.toMul v : N) ∈ S0 := hv
      rw [h, Subgroup.mem_bot] at hy
      rw [Submodule.mem_bot]
      have h1 : Additive.toMul v = 1 := hy
      change Additive.ofMul (Additive.toMul v) = Additive.ofMul 1
      rw [h1]
    · right
      rw [eq_top_iff]
      intro v _
      have hv : (Additive.toMul v : N) ∈ S0 := by rw [h]; exact Subgroup.mem_top _
      exact hv
  haveI : Finite (Additive N) := inferInstanceAs (Finite N)
  haveI : Nontrivial (Additive N) := inferInstanceAs (Nontrivial N)
  have hlin := log_card_linear_le hD (ZMod p) (Additive N) H hHcl (palfyCR_of_irr hirr)
  have hVN : Nat.card (Additive N) = Nat.card N := rfl
  rwa [hVN, hHcard] at hlin

/-- **The affine case.** A faithful primitive group in the class with an abelian minimal normal
subgroup has `log |G| ≤ (C log D + 1) log n`. -/
theorem log_card_affine_le {D : ℕ} (hD : 6 ≤ D) {G α : Type} [Group G] [Finite G] [MulAction G α]
    [FaithfulSMul G α] [Finite α] [Nontrivial G] [IsPreprimitive G α] (hcl : GammaHat D G)
    {N : Subgroup G} (hN : MinimalNormal N) (hc : ∀ x y : N, x * y = y * x) :
    Real.log (Nat.card G) ≤ (linC * Real.log D + 1) * Real.log (Nat.card α) := by
  classical
  haveI := hN.1
  haveI := normal_pretransitive (V := α) N hN.2.1
  have hα : Nonempty α := by
    by_contra hα
    rw [not_nonempty_iff] at hα
    obtain ⟨g, h, hgh⟩ := exists_pair_ne G
    exact hgh (eq_of_smul_eq_smul (α := α) (fun v => isEmptyElim v))
  obtain ⟨a⟩ := hα
  have hcard : Nat.card N = Nat.card α := abelian_normal_card N hN.2.1 hc a
  haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN.2.1
  letI : CommGroup N := { (inferInstance : Group N) with mul_comm := hc }
  let ρ : G →* MulAut N := MulAut.conjNormal
  -- the kernel of `ρ` lies in `N`
  have hker : ρ.ker ≤ N := by
    intro g hg1
    rw [MonoidHom.mem_ker] at hg1
    obtain ⟨y, hy⟩ := MulAction.exists_smul_eq N a (g • a)
    have hcent : (y : G)⁻¹ * g ∈ solvCent a N := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [mem_stabilizer_iff, mul_smul, ← hy]
        exact inv_smul_smul (y : G) a
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hx' : g * x * g⁻¹ = x := by
          have := MulAut.conjNormal_apply g ⟨x, hx⟩
          rw [← this]
          change ((ρ g) ⟨x, hx⟩ : G) = x
          rw [hg1]
          rfl
        have hyx : Commute x (y : G) := congrArg Subtype.val (hc ⟨x, hx⟩ y)
        have hxg : Commute x g := (mul_inv_eq_iff_eq_mul.mp hx').symm
        exact hyx.inv_right.mul_right hxg
    rw [solvCent_top_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hcent
    rw [← hcent]
    exact y.2
  have hG : Nat.card G ≤ Nat.card N * Nat.card ρ.range := by
    rw [← Subgroup.card_mul_index ρ.ker, Subgroup.index_ker]
    exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hker)
  -- `N` is elementary abelian
  have h1N : Nat.card N ≠ 1 := (Finite.one_lt_card (α := N)).ne'
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1N
  haveI := Fact.mk hp
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) p hpd
  let P : Subgroup G :=
    { carrier := {g | g ∈ N ∧ g ^ p = 1}
      mul_mem' := by
        rintro g h ⟨hg, hgp⟩ ⟨hh, hhp⟩
        refine ⟨N.mul_mem hg hh, ?_⟩
        have hcomm : Commute g h := congrArg Subtype.val (hc ⟨g, hg⟩ ⟨h, hh⟩)
        rw [hcomm.mul_pow, hgp, hhp, one_mul]
      one_mem' := ⟨N.one_mem, one_pow p⟩
      inv_mem' := by
        rintro g ⟨hg, hgp⟩
        exact ⟨N.inv_mem hg, by rw [inv_pow, hgp, inv_one]⟩ }
  have hPN : P ≤ N := fun g hg => hg.1
  have hPnorm : P.Normal := by
    constructor
    rintro g ⟨hg, hgp⟩ h
    exact ⟨hN.1.conj_mem g hg h, by rw [conj_pow, hgp, mul_one, mul_inv_cancel]⟩
  have hxP : (x : G) ∈ P := ⟨x.2, by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this⟩
  have hPne : P ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.mem_bot] at hxP
    have : x = 1 := Subtype.ext hxP
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hexp : ∀ y : N, y ^ p = 1 := by
    rcases hN.2.2 P hPnorm hPN with h | h
    · exact absurd h hPne
    · intro y
      have : (y : G) ∈ P := by rw [h]; exact y.2
      exact Subtype.ext this.2
  -- the linear core
  have hirr0 : ∀ W : Subgroup N, (∀ σ ∈ ρ.range, ∀ w ∈ W, σ w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hnorm : (W.map N.subtype).Normal := by
      constructor
      rintro _ ⟨w, hw, rfl⟩ g
      exact ⟨(ρ g) w, hW _ ⟨g, rfl⟩ w hw, MulAut.conjNormal_apply g w⟩
    rcases hN.2.2 _ hnorm (Subgroup.map_subtype_le W) with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp h
    · right
      rw [eq_top_iff]
      intro y _
      have hy : (y : G) ∈ W.map N.subtype := by rw [h]; exact y.2
      obtain ⟨w, hw, hwy⟩ := hy
      rwa [← Subtype.ext hwy]
  have h3 : Real.log (Nat.card ρ.range) ≤ linC * Real.log D * Real.log (Nat.card N) :=
    @deg_affine_core D hD N _ _ _ p _ (AddCommGroup.zmodModule (fun v => by
      change Additive.ofMul ((Additive.toMul v) ^ p) = Additive.ofMul 1
      rw [hexp])) ρ.range (hcl.of_surjective _ ρ.rangeRestrict_surjective) hirr0
  rw [hcard] at h3
  rw [hcard] at hG
  have hR : (0 : ℝ) < Nat.card ρ.range := by exact_mod_cast Nat.card_pos
  haveI : Nonempty α := ⟨a⟩
  have hαpos : (0 : ℝ) < Nat.card α := by exact_mod_cast Nat.card_pos
  have h4 : (Nat.card G : ℝ) ≤ Nat.card α * Nat.card ρ.range := by exact_mod_cast hG
  have h5 := Real.log_le_log (by exact_mod_cast Nat.card_pos) h4
  rw [Real.log_mul hαpos.ne' hR.ne'] at h5
  calc _ ≤ _ := h5
    _ ≤ _ := by linarith

end GI.Degree
