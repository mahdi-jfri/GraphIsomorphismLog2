import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Simple

open scoped commutatorElement

namespace GI

variable {U S : Type*} [Group U] [Group S]

def commonKernel : List (Subgroup U) → Subgroup U
  | [] => ⊤
  | K :: Ks => K ⊓ commonKernel Ks

theorem commonKernel_normal (Ks : List (Subgroup U))
    (hn : ∀ K ∈ Ks, K.Normal) : (commonKernel Ks).Normal := by
  induction Ks with
  | nil => exact inferInstanceAs (⊤ : Subgroup U).Normal
  | cons K Ks ih =>
    haveI : K.Normal := hn K (by simp)
    haveI : (commonKernel Ks).Normal := ih (fun L hL => hn L (by simp [hL]))
    exact inferInstanceAs (K ⊓ commonKernel Ks).Normal

theorem simple_nonabelian_perfect [IsSimpleGroup S]
    (nonabelian : ∃ a b : S, a * b ≠ b * a) :
    ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = (⊤ : Subgroup S) := by
  rcases (inferInstance : (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆).Normal).eq_bot_or_eq_top with h | h
  · obtain ⟨a, b, hab⟩ := nonabelian
    have hm := Subgroup.commutator_mem_commutator
      (show a ∈ (⊤ : Subgroup S) from Subgroup.mem_top a)
      (show b ∈ (⊤ : Subgroup S) from Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hm
    exact False.elim (hab (commutatorElement_eq_one_iff_mul_comm.mp hm))
  · exact h

/-- Normal subgroups surjecting onto a perfect group have a surjecting intersection. -/
theorem intersection_surjects (φ : U →* S) (hφ : Function.Surjective φ)
    (perfect : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = (⊤ : Subgroup S)) (Ks : List (Subgroup U))
    (hn : ∀ K ∈ Ks, K.Normal) (hm : ∀ K ∈ Ks, K.map φ = ⊤) :
    (commonKernel Ks).map φ = ⊤ := by
  induction Ks with
  | nil => exact Subgroup.map_top_of_surjective φ hφ
  | cons K Ks ih =>
    haveI : K.Normal := hn K (by simp)
    haveI : (commonKernel Ks).Normal :=
      commonKernel_normal Ks (fun L hL => hn L (by simp [hL]))
    have hi := ih (fun L hL => hn L (by simp [hL]))
      (fun L hL => hm L (by simp [hL]))
    apply top_le_iff.mp
    calc
      (⊤ : Subgroup S) = (⁅K, commonKernel Ks⁆).map φ := by
        rw [Subgroup.map_commutator, hm K (by simp), hi, perfect]
      _ ≤ (K ⊓ commonKernel Ks).map φ :=
        Subgroup.map_mono (Subgroup.commutator_le_inf K (commonKernel Ks))

/-- Lemma A.4, first assertion: a nonabelian simple quotient is visible in at least
one component whenever the intersection of the component kernels is killed. -/
theorem simple_quotient_localization [IsSimpleGroup S]
    (φ : U →* S) (hφ : Function.Surjective φ)
    (nonabelian : ∃ a b : S, a * b ≠ b * a)
    (Ks : List (Subgroup U)) (hn : ∀ K ∈ Ks, K.Normal)
    (hk : commonKernel Ks ≤ φ.ker) :
    ∃ K ∈ Ks, K.map φ = ⊥ := by
  apply Classical.byContradiction
  intro h
  have hm : ∀ K ∈ Ks, K.map φ = ⊤ := by
    intro K hK
    rcases ((hn K hK).map φ hφ).eq_bot_or_eq_top with hbot | htop
    · exact False.elim (h ⟨K, hK, hbot⟩)
    · exact htop
  have hi := intersection_surjects φ hφ (simple_nonabelian_perfect nonabelian) Ks hn hm
  have hbot : (commonKernel Ks).map φ ≤ ⊥ := by
    rintro s ⟨u, hu, rfl⟩
    exact hk hu
  rw [hi] at hbot
  exact top_ne_bot (le_antisymm hbot bot_le)

end GI
