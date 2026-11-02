import Workspace.Proved.VsMBasic

/-!
# The goodness test

With `q = |L| = p^(dim L)` and `|S| = q - 1` (`VsMGoodTestStmt`), an element `y` is good
(`y^r = l^r`, `l ∈ S`) iff `y^r ∈ S` and, when `r ∣ q - 1`, `y^(q-1) = 1` (`vsH_good_iff`).
Goodness does not change modulo `S` for `y` commuting with `S` (`vsH_good_mul`).
-/

namespace GI.Proved

open Module

variable {p : ℕ} [hp : Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem vsH_card_scal [FiniteDimensional (ZMod p) V] [Nontrivial V]
    {A : Subgroup (End (ZMod p) V)ˣ} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hdom : vsTDom (vsTAlg A)) :
    Nat.card (vsMScal A) + 1 = p ^ finrank (ZMod p) (vsTAlg A) := by
  classical
  rw [(vsM_good_test (p := p) (V := V) A hA hdom).1]
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  haveI : Finite (End (ZMod p) V) := Module.finite_of_finite (ZMod p)
  haveI : Fintype (vsTAlg A) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p) (V := vsTAlg A),
    ZMod.card]

/-- **The goodness test.** -/
theorem vsH_good_iff [FiniteDimensional (ZMod p) V] [Nontrivial V]
    {A : Subgroup (End (ZMod p) V)ˣ} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hdom : vsTDom (vsTAlg A)) {r : ℕ} (hr : r.Prime) (y : (End (ZMod p) V)ˣ) :
    vsMGood A r y ↔ y ^ r ∈ vsMScal A ∧
      (r ∣ p ^ finrank (ZMod p) (vsTAlg A) - 1 → y ^ (p ^ finrank (ZMod p) (vsTAlg A) - 1) = 1) := by
  have hcard := vsH_card_scal (V := V) hA hdom
  set q := p ^ finrank (ZMod p) (vsTAlg A)
  have hS : Nat.card (vsMScal A) = q - 1 := by omega
  have hT := (vsM_good_test (p := p) (V := V) A hA hdom).2 r (y ^ r) hr
  constructor
  · rintro ⟨l, hl, e⟩
    have hyS : y ^ r ∈ vsMScal A := by rw [e]; exact pow_mem hl r
    refine ⟨hyS, fun hdvd => ?_⟩
    have := (hT (by rw [hS]; exact hdvd) hyS).1 ⟨l, hl, e⟩
    rw [← pow_mul, hS, Nat.mul_div_cancel' hdvd] at this
    exact this
  · rintro ⟨hyS, h1⟩
    by_cases hdvd : r ∣ q - 1
    · obtain ⟨l, hl, e⟩ := (hT (by rw [hS]; exact hdvd) hyS).2
        (by rw [← pow_mul, hS, Nat.mul_div_cancel' hdvd]; exact h1 hdvd)
      exact ⟨l, hl, e⟩
    · have hcop : (Nat.card (vsMScal A)).Coprime r := by
        rw [hS, Nat.coprime_comm]
        exact (Nat.Prime.coprime_iff_not_dvd hr).2 hdvd
      set c : vsMScal A := ⟨y ^ r, hyS⟩
      refine ⟨((powCoprime hcop).symm c : vsMScal A), ((powCoprime hcop).symm c).2, ?_⟩
      have := (powCoprime hcop).apply_symm_apply c
      have e2 := congrArg Subtype.val this
      simp only [powCoprime_apply, SubgroupClass.coe_pow] at e2
      exact e2.symm

/-- Goodness does not change modulo `S`. -/
theorem vsH_good_mul {A : Subgroup (End (ZMod p) V)ˣ} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {r : ℕ} {y s : (End (ZMod p) V)ˣ} (hs : s ∈ vsMScal A) (hys : y * s = s * y)
    (h : vsMGood A r (y * s)) : vsMGood A r y := by
  obtain ⟨l, hl, e⟩ := h
  refine ⟨l * s⁻¹, mul_mem hl (inv_mem hs), ?_⟩
  have hc : Commute y s := hys
  rw [hc.mul_pow] at e
  have hls : Commute l s⁻¹ := vsM_scal_comm hA hl (inv_mem hs)
  rw [hls.mul_pow, ← e, inv_pow, mul_inv_cancel_right]

end GI.Proved
