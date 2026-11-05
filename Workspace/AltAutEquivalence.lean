module

public import Workspace.AltAutConjugation
public import Mathlib.GroupTheory.GroupAction.ConjAct

@[expose] public section

/-! The natural symmetric-group realization of alternating-group automorphisms.
Surjectivity uses the fully proved small pinned conjugation branch; injectivity
is established by the action on all three-point supports. -/

namespace GI.AlternatingAutomorphism
open Equiv Equiv.Perm
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem conjugation_injective (hα : 4 ≤ Fintype.card α) :
    Function.Injective (MulAut.conjNormal (H := alternatingGroup α) :
      Perm α →* MulAut (alternatingGroup α)) := by
  intro σ τ hστ
  apply eq_of_forall_map_eq hα
  intro s hs
  obtain ⟨g, hg, hgs⟩ := exists_alternatingGroup_isThreeCycle_support_eq hs
  have he : σ * (g : Perm α) * σ⁻¹ = τ * (g : Perm α) * τ⁻¹ := by
    simpa only [MulAut.conjNormal_apply] using
      congrArg (fun f : MulAut (alternatingGroup α) => (f g : Perm α)) hστ
  have hsup := congrArg Perm.support he
  simpa only [support_conj, hgs] using hsup

theorem conjugation_surjective (hα : Fintype.card α = 5 ∨ 7 ≤ Fintype.card α) :
    Function.Surjective (MulAut.conjNormal (H := alternatingGroup α) :
      Perm α →* MulAut (alternatingGroup α)) := by
  intro f
  obtain ⟨σ, hσ⟩ := exists_perm_conj hα f
  refine ⟨σ, ?_⟩
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  exact (MulAut.conjNormal_apply σ g).trans (hσ g).symm

noncomputable def conjugationEquiv (hα : Fintype.card α = 5 ∨ 7 ≤ Fintype.card α) :
    Perm α ≃* MulAut (alternatingGroup α) :=
  MulEquiv.ofBijective MulAut.conjNormal
    ⟨conjugation_injective (by omega), conjugation_surjective hα⟩

@[simp] theorem conjugationEquiv_apply
    (hα : Fintype.card α = 5 ∨ 7 ≤ Fintype.card α) (σ : Perm α) :
    conjugationEquiv hα σ = MulAut.conjNormal σ := rfl

@[simp] theorem conjugationEquiv_apply_coe
    (hα : Fintype.card α = 5 ∨ 7 ≤ Fintype.card α) (σ : Perm α)
    (g : alternatingGroup α) :
    (conjugationEquiv hα σ g : Perm α) = σ * g * σ⁻¹ :=
  MulAut.conjNormal_apply σ g

@[simp] theorem conjugationEquiv_apply_val
    (hα : Fintype.card α = 5 ∨ 7 ≤ Fintype.card α) (g : alternatingGroup α) :
    conjugationEquiv hα (g : Perm α) = MulAut.conj g := MulAut.conjNormal_val

@[simp] theorem conjugationEquiv_symm_conj
    (hα : Fintype.card α = 5 ∨ 7 ≤ Fintype.card α) (g : alternatingGroup α) :
    (conjugationEquiv hα).symm (MulAut.conj g) = (g : Perm α) := by
  rw [← conjugationEquiv_apply_val hα g]
  exact (conjugationEquiv hα).symm_apply_apply g.val

theorem existsUnique_perm_conj
    (hα : Fintype.card α = 5 ∨ 7 ≤ Fintype.card α)
    (f : MulAut (alternatingGroup α)) :
    ∃! σ : Perm α, ∀ g : alternatingGroup α, (f g : Perm α) = σ * g * σ⁻¹ := by
  obtain ⟨σ, hσ⟩ := exists_perm_conj hα f
  refine ⟨σ, hσ, fun τ hτ => conjugation_injective (by omega) ?_⟩
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  exact (MulAut.conjNormal_apply τ g).trans
    ((hτ g).symm.trans ((hσ g).trans (MulAut.conjNormal_apply σ g).symm))

noncomputable def finConjugationEquiv {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) :
    Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
  conjugationEquiv (by simpa using hn)

@[simp] theorem finConjugationEquiv_apply_val {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    (g : alternatingGroup (Fin n)) :
    finConjugationEquiv hn (g : Perm (Fin n)) = MulAut.conj g :=
  conjugationEquiv_apply_val _ g

@[simp] theorem finConjugationEquiv_symm_conj {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    (g : alternatingGroup (Fin n)) :
    (finConjugationEquiv hn).symm (MulAut.conj g) = (g : Perm (Fin n)) :=
  conjugationEquiv_symm_conj _ g

end GI.AlternatingAutomorphism
