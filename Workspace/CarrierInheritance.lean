module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! "Inheritance of the retained row action" (`subsec:carrier-inheritance`,
the faithful-image assertion) and eq. `promotion-product` of
"Why a row action is enlarged at most once" (Section 6).

The paper: "write the covering group of the largest first orbit as
`H/M = Alt(m) × Q'` and let `T = H_{(Ω')}` be the kernel of its physical
action. Every pointwise-fixing element fixes every row label, since the orbit
contains all rows above its column orbit. Consequently `TM/M = 1 × Z` for a
normal subgroup `Z ◁ Q'`, and `(H/T)/(TM/T) ≅ Alt(m) × (Q'/Z)`."

The identification `H/M = Alt(m) × Q'` is a surjection `π : H → A × Q'` with
kernel `M`; `A` plays the role of `Alt(m)`. `TM` is `T ⊔ M`. -/

namespace GI.CarrierInheritance

variable {H A Q : Type*} [Group H] [Group A] [Group Q]

/-- "Every pointwise-fixing element fixes every row label, since the orbit
contains all rows": an element fixing pointwise a set that meets every row acts
trivially on the rows. -/
theorem row_action_trivial_of_fixes {X I : Type*} [MulAction H X] (φ : H →* Equiv.Perm I)
    (label : X → I) (hlabel : ∀ (h : H) (x : X), label (h • x) = φ h (label x))
    (Ω' : Set X) (hrows : ∀ i, ∃ x ∈ Ω', label x = i) (t : H) (ht : ∀ x ∈ Ω', t • x = x) :
    φ t = 1 := by
  ext i
  obtain ⟨x, hx, rfl⟩ := hrows i
  rw [← hlabel, ht x hx]
  rfl

/-- The faithful-image assertion: if every element of `T` has trivial
`Alt(m)`-component, then `TM/M = 1 × Z` for a normal `Z ◁ Q'`, and
`(H/T)/(TM/T) ≅ Alt(m) × (Q'/Z)`. -/
theorem faithful_image (M T : Subgroup H) [T.Normal] (π : H →* A × Q)
    (hπ : Function.Surjective π) (hker : π.ker = M) (hT : ∀ t ∈ T, (π t).1 = 1) :
    ∃ (Z : Subgroup Q) (_ : Z.Normal), (T ⊔ M).map π = (⊥ : Subgroup A).prod Z ∧
      ∃ (_ : ((T ⊔ M).map (QuotientGroup.mk' T)).Normal),
        Nonempty ((H ⧸ T) ⧸ ((T ⊔ M).map (QuotientGroup.mk' T)) ≃* A × (Q ⧸ Z)) := by
  let σ : H →* Q := (MonoidHom.snd A Q).comp π
  have hσ : Function.Surjective σ := fun q => by
    obtain ⟨h, hh⟩ := hπ (1, q)
    exact ⟨h, by simp [σ, hh]⟩
  let Z : Subgroup Q := T.map σ
  haveI hZ : Z.Normal := (inferInstance : T.Normal).map σ hσ
  -- `TM/M = 1 × Z`.
  have hmapM : M.map π = ⊥ := by
    rw [← hker]
    exact (Subgroup.map_eq_bot_iff _).mpr le_rfl
  have hmap : (T ⊔ M).map π = (⊥ : Subgroup A).prod Z := by
    rw [Subgroup.map_sup, hmapM, sup_bot_eq]
    ext ⟨a, q⟩
    constructor
    · rintro ⟨t, ht, hπt⟩
      have h1 := hT t ht
      rw [hπt] at h1
      refine ⟨Subgroup.mem_bot.mpr h1, t, ht, ?_⟩
      simp [σ, hπt]
    · rintro ⟨ha, t, ht, hσt⟩
      refine ⟨t, ht, ?_⟩
      have h1 := hT t ht
      have ha' : a = 1 := Subgroup.mem_bot.mp ha
      exact Prod.ext (h1.trans ha'.symm) hσt
  refine ⟨Z, hZ, hmap, ?_⟩
  have hTM : T ≤ T ⊔ M := le_sup_left
  let ρ : H →* A × (Q ⧸ Z) := (MonoidHom.prodMap (MonoidHom.id A) (QuotientGroup.mk' Z)).comp π
  have hρ : Function.Surjective ρ := by
    rintro ⟨a, qz⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective Z qz
    obtain ⟨h, hh⟩ := hπ (a, q)
    exact ⟨h, by simp [ρ, hh]⟩
  have hρker : ρ.ker = T ⊔ M := by
    ext h
    rw [MonoidHom.mem_ker]
    constructor
    · intro hh
      have h1 : (π h).1 = 1 := congrArg Prod.fst hh
      have h2 : (π h).2 ∈ Z := (QuotientGroup.eq_one_iff _).mp (congrArg Prod.snd hh)
      have hmem : π h ∈ (T ⊔ M).map π := by
        rw [hmap]
        exact ⟨Subgroup.mem_bot.mpr h1, h2⟩
      obtain ⟨x, hx, hxh⟩ := hmem
      have hd : x⁻¹ * h ∈ M := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hxh, inv_mul_cancel]
      have := (T ⊔ M).mul_mem hx (Subgroup.mem_sup_right hd)
      simpa using this
    · intro hh
      have hmem : π h ∈ (⊥ : Subgroup A).prod Z := hmap ▸ ⟨h, hh, rfl⟩
      exact Prod.ext (Subgroup.mem_bot.mp hmem.1)
        ((QuotientGroup.eq_one_iff _).mpr hmem.2)
  haveI hTMn : (T ⊔ M).Normal := by
    rw [← hρker]
    infer_instance
  haveI hmapn : ((T ⊔ M).map (QuotientGroup.mk' T)).Normal :=
    hTMn.map _ (QuotientGroup.mk'_surjective T)
  refine ⟨hmapn, ⟨?_⟩⟩
  exact (QuotientGroup.quotientQuotientEquivQuotient T (T ⊔ M) hTM).trans
    ((QuotientGroup.quotientMulEquivOfEq hρker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρ))

/-- Eq. `promotion-product`: for `1/3 < α`, `λ = N^α`, and two exposed ratios
`m, q > λ`, the remaining ratios have product at most
`N/(mq) < N^{1-2α} < N^α = λ`. -/
theorem promotion_product {N α m q : ℝ} (hN : 1 < N) (hα : 1 / 3 < α)
    (hm : N ^ α < m) (hq : N ^ α < q) :
    N / (m * q) < N ^ (1 - 2 * α) ∧ N ^ (1 - 2 * α) < N ^ α := by
  have hN0 : 0 < N := by linarith
  have hlam : 0 < N ^ α := Real.rpow_pos_of_pos hN0 α
  have hmq : N ^ α * N ^ α < m * q := mul_lt_mul'' hm hq hlam.le hlam.le
  have hsq : N ^ α * N ^ α = N ^ (2 * α) := by
    rw [← Real.rpow_add hN0]
    ring_nf
  constructor
  · rw [hsq] at hmq
    have hpos : 0 < N ^ (2 * α) := Real.rpow_pos_of_pos hN0 _
    have h1 : N / (m * q) < N / N ^ (2 * α) := div_lt_div_of_pos_left hN0 hpos hmq
    have h2 : N / N ^ (2 * α) = N ^ (1 - 2 * α) := by
      rw [Real.rpow_sub hN0, Real.rpow_one]
    rwa [h2] at h1
  · exact Real.rpow_lt_rpow_of_exponent_lt hN (by linarith)

end GI.CarrierInheritance
