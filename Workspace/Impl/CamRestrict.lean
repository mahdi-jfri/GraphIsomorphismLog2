module

public import Workspace.Cited.AlgoPermGroups

@[expose] public section

/-!
# Restricting a group to a numbered invariant set

The program restricts the generators of one factor to one of its orbits, numbered by an injection
`ν : Fin n' → Fin n`. Restricting each generator `t` gives a permutation `g` of `Fin n'` with
`ν (g w) = t (ν w)`. `cam_restrict_gens` says that the restricted generators generate exactly the
restrictions of the elements of the group. This is the hypothesis `hH` of `cam_combine`.
-/

namespace GI.Impl

open Equiv GI.Cited

/-- `g` is the restriction of `t` along `ν`. -/
def CamRestricts {n n' : ℕ} (ν : Fin n' → Fin n) (g : Perm (Fin n')) (t : Perm (Fin n)) : Prop :=
  ∀ w, ν (g w) = t (ν w)

theorem cam_restricts_one {n n' : ℕ} (ν : Fin n' → Fin n) : CamRestricts ν 1 1 := fun _ => rfl

theorem cam_restricts_mul {n n' : ℕ} {ν : Fin n' → Fin n} {g₁ g₂ : Perm (Fin n')}
    {t₁ t₂ : Perm (Fin n)} (h₁ : CamRestricts ν g₁ t₁) (h₂ : CamRestricts ν g₂ t₂) :
    CamRestricts ν (g₁ * g₂) (t₁ * t₂) := fun w => by
  simp only [Equiv.Perm.mul_apply, h₁ (g₂ w), h₂ w]

theorem cam_restricts_inv {n n' : ℕ} {ν : Fin n' → Fin n} {g : Perm (Fin n')}
    {t : Perm (Fin n)} (h : CamRestricts ν g t) : CamRestricts ν g⁻¹ t⁻¹ := fun w => by
  have := h (g⁻¹ w)
  rw [show g (g⁻¹ w) = w from g.apply_symm_apply w] at this
  rw [this]
  exact (t.symm_apply_apply _).symm

/-- **Restricted generators generate the restricted group.** -/
theorem cam_restrict_gens {n n' : ℕ} (ν : Fin n' → Fin n) (hν : Function.Injective ν)
    (ts : List (Perm (Fin n))) (ts' : List (Perm (Fin n')))
    (h1 : ∀ t ∈ ts, ∃ g ∈ ts', CamRestricts ν g t)
    (h2 : ∀ g ∈ ts', ∃ t ∈ ts, CamRestricts ν g t) (g : Perm (Fin n')) :
    g ∈ gens ts' ↔ ∃ t ∈ gens ts, CamRestricts ν g t := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨t, ht, hgt⟩ := h2 g hg
      exact ⟨t, Subgroup.subset_closure ht, hgt⟩
    | one => exact ⟨1, Subgroup.one_mem _, cam_restricts_one ν⟩
    | mul a b _ _ ha hb =>
      obtain ⟨ta, hta, ha⟩ := ha
      obtain ⟨tb, htb, hb⟩ := hb
      exact ⟨ta * tb, Subgroup.mul_mem _ hta htb, cam_restricts_mul ha hb⟩
    | inv a _ ha =>
      obtain ⟨ta, hta, ha⟩ := ha
      exact ⟨ta⁻¹, Subgroup.inv_mem _ hta, cam_restricts_inv ha⟩
  · rintro ⟨t, ht, hgt⟩
    have key : ∃ g' ∈ gens ts', CamRestricts ν g' t := by
      clear hgt
      induction ht using Subgroup.closure_induction with
      | mem t ht =>
        obtain ⟨g', hg', h⟩ := h1 t ht
        exact ⟨g', Subgroup.subset_closure hg', h⟩
      | one => exact ⟨1, Subgroup.one_mem _, cam_restricts_one ν⟩
      | mul a b _ _ ha hb =>
        obtain ⟨ga, hga, ha⟩ := ha
        obtain ⟨gb, hgb, hb⟩ := hb
        exact ⟨ga * gb, Subgroup.mul_mem _ hga hgb, cam_restricts_mul ha hb⟩
      | inv a _ ha =>
        obtain ⟨ga, hga, ha⟩ := ha
        exact ⟨ga⁻¹, Subgroup.inv_mem _ hga, cam_restricts_inv ha⟩
    obtain ⟨g', hg', h⟩ := key
    have : g' = g := Equiv.ext fun w => hν (by rw [h w, hgt w])
    exact this ▸ hg'

end GI.Impl
