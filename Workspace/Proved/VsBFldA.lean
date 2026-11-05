module

public import Workspace.Proved.VsBFldMath
public import Workspace.Impl.VsBDesc

@[expose] public section

/-!
# The λ-chain as a descent

The λ-chain of the field line fits the descent of `Impl/VsBDesc.lean`. The group `M` is
`vsBU s`, the invertible matrices `u` with `u, u⁻¹ ∈ L`; it is commutative because `L` is.
The map `ψ` sends `h ∈ H` to `Λ(h)`. Stage `p` of the chain is `q = p + 2`, for
`p < max n 2 - 1`, and sees `u` through the vector `u^{F_q} e₀`.

* `vsBU`, `vsBPsi`, `vsBTq`, `vsBAp`, `vsBPs`.
* `vsB_descHyp`: the hypotheses `VsBDescHyp` of the descent hold.
-/

open Matrix

namespace GI.Proved

open GI.Impl GI.Cited GI.Lang Equiv

variable {I : VecStabInst}

/-- The local matrices of a state. -/
abbrev vsBMt (s : VsQSt I) : Type := Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)

/-- The units of `L` (as matrices). -/
noncomputable def vsBU (s : VsQSt I) : Subgroup (vsBMt s)ˣ where
  carrier := {u | (u : vsBMt s) ∈ vsBLamA s ∧ ((u⁻¹ : (vsBMt s)ˣ) : vsBMt s) ∈ vsBLamA s}
  one_mem' := ⟨one_mem _, by simp [one_mem]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, ?_⟩
    · simp only [Units.val_mul]; exact mul_mem ha hb
    · simp only [_root_.mul_inv_rev, Units.val_mul]; exact mul_mem hb' ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by simpa using ha⟩

/-- The stages: `p < max n 2 - 1`, standing for `q = p + 2`. -/
def vsBPs (n : ℕ) : List ℕ := List.range (max n 2 - 1)

/-- The action of stage `p`. -/
noncomputable def vsBAp (s : VsQSt I) (p : ℕ) : Perm (Fin I.n) → (Fin (vsQD s) → ZMod I.p) →
    Fin (vsQD s) → ZMod I.p :=
  vsBAq s (p + 2)

/-- The point of stage `p` seen by a unit. -/
noncomputable def vsBTq (s : VsQSt I) (hD : 1 ≤ vsQD s) (p : ℕ) (u : vsBU s) :
    Fin (vsQD s) → ZMod I.p :=
  (((u : (vsBMt s)ˣ) : vsBMt s) ^ vsBF I.n (p + 2)) *ᵥ vsBe0 s hD

section

variable {s : VsQSt I} (hs : VsQStOK s)
include hs

theorem vsB_lam_inv {h : Perm (Fin I.n)} (hh : h ∈ gens s.hs) :
    vsQLam s h * vsQLam s h⁻¹ = 1 := by
  rw [← vsQLam_mul hs hh (inv_mem hh), mul_inv_cancel, vsQLam_one hs]

theorem vsB_lam_inv' {h : Perm (Fin I.n)} (hh : h ∈ gens s.hs) :
    vsQLam s h⁻¹ * vsQLam s h = 1 := by
  rw [← vsQLam_mul hs (inv_mem hh) hh, inv_mul_cancel, vsQLam_one hs]

end

open Classical in
/-- The map `ψ`: `h ↦ Λ(h)` on `H`. -/
noncomputable def vsBPsi {s : VsQSt I} (hs : VsQStOK s) (h : Perm (Fin I.n)) : vsBU s :=
  if hh : h ∈ gens s.hs then
    ⟨⟨vsQLam s h, vsQLam s h⁻¹, vsB_lam_inv hs hh, vsB_lam_inv' hs hh⟩,
      vsB_lam_mem hs hh, vsB_lam_mem hs (inv_mem hh)⟩
  else 1

section

variable {s : VsQSt I} (hs : VsQStOK s)
include hs

theorem vsBPsi_val {h : Perm (Fin I.n)} (hh : h ∈ gens s.hs) :
    (((vsBPsi hs h : vsBU s) : (vsBMt s)ˣ) : vsBMt s) = vsQLam s h := by
  simp [vsBPsi, hh]

theorem vsB_U_comm (hab : s.Ab) {X Y : Matrix (Fin (vsQD s)) (Fin (vsQD s)) (ZMod I.p)}
    (hX : X ∈ vsBLamA s) (hY : Y ∈ vsBLamA s) : Commute X Y := by
  have hc : ∀ a ∈ {X | ∃ g ∈ s.hs, vsQLam s g = X}, ∀ b ∈ {X | ∃ g ∈ s.hs, vsQLam s g = X},
      Commute a b := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    exact vsB_comm hs hab (Subgroup.subset_closure hg) (Subgroup.subset_closure hh)
  exact Algebra.commute_of_mem_adjoin_of_forall_mem_commute hY fun b hb =>
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hX fun a ha => (hc b hb a ha)).symm

/-- **The λ-chain is a descent.** -/
theorem vsB_descHyp (hab : s.Ab) (hD : 1 ≤ vsQD s) (hdom : VsBDom s) :
    VsBDescHyp (vsBAp s) (vsBe0 s hD) (gens s.hs) (vsBPsi hs) (vsBTq s hD) (vsBPs I.n) where
  act p _ := vsBAq_act hs hab (p + 2)
  hom g hg h hh := by
    apply Subtype.ext; apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, vsBPsi_val hs (mul_mem hg hh), vsBPsi_val hs hg,
      vsBPsi_val hs hh, vsQLam_mul hs hg hh]
  aT p _ h hh := by
    simp only [vsBAp, vsBAq, vsBTq, vsBPsi_val hs hh]
  kerT p _ a b := by
    have hab' : Commute (((b⁻¹ : vsBU s) : (vsBMt s)ˣ) : vsBMt s)
        (((a : vsBU s) : (vsBMt s)ˣ) : vsBMt s) :=
      vsB_U_comm hs hab (b⁻¹).2.1 a.2.1
    simp only [vsBTq, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one, one_pow,
      one_mulVec, hab'.mul_pow, ← mulVec_mulVec]
    set F := vsBF I.n (p + 2)
    have hbb : (((b⁻¹ : vsBU s) : (vsBMt s)ˣ) : vsBMt s) ^ F *
        (((b : vsBU s) : (vsBMt s)ˣ) : vsBMt s) ^ F = 1 := by
      rw [← (vsB_U_comm hs hab (b⁻¹).2.1 b.2.1).mul_pow]
      simp
    have hbb' : (((b : vsBU s) : (vsBMt s)ˣ) : vsBMt s) ^ F *
        (((b⁻¹ : vsBU s) : (vsBMt s)ˣ) : vsBMt s) ^ F = 1 := by
      rw [← (vsB_U_comm hs hab b.2.1 (b⁻¹).2.1).mul_pow]
      simp
    constructor
    · intro h
      rw [h, mulVec_mulVec, hbb, one_mulVec]
    · intro h
      have := congrArg (fun v => (((b : vsBU s) : (vsBMt s)ˣ) : vsBMt s) ^ F *ᵥ v) h
      simp only [mulVec_mulVec, ← mul_assoc, hbb', one_mul] at this
      exact this
  fin a ha := by
    have hF : ∀ q, 2 ≤ q → q ≤ max I.n 2 → a ^ vsBF I.n q = 1 := by
      intro q hq2 hqN
      have hp : q - 2 ∈ vsBPs I.n := List.mem_range.mpr (by omega)
      have h1 := ha (q - 2) hp
      have e : q - 2 + 2 = q := by omega
      simp only [vsBTq, e, Subgroup.coe_one, Units.val_one, one_pow, one_mulVec] at h1
      have hm : (((a : vsBU s) : (vsBMt s)ˣ) : vsBMt s) ^ vsBF I.n q - 1 ∈ vsBLamA s :=
        sub_mem (pow_mem a.2.1 _) (one_mem _)
      have h0 := vsB_dom_eq_zero hdom hm (vsB_e0_ne hD) (by rw [sub_mulVec, one_mulVec, h1, sub_self])
      apply Subtype.ext; apply Units.ext
      simpa [sub_eq_zero] using h0
    exact vsB_eq_one hF

end

end GI.Proved
