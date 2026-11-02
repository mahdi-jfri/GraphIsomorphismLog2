import Workspace.MulticosetPieces
import Workspace.MulticosetTransport

/-! Local stabilizers in the abelian layer contain the kernel and are
normal in `A`. This justifies the quotients used in the object glue. -/
namespace GI.Impl

open GI.Multicoset
open scoped commutatorElement

variable {G Ω : Type*} [Group G] [RAct G Ω]

theorem linObjectKernel_le_aut {N A : Subgroup G} {T : Multiset Ω}
    (hNA : N ≤ A) (hfix : Fixes N T) : N ≤ Aut A T := by
  intro n hn
  exact ⟨hNA hn, hfix.act_eq hn⟩

theorem linObjectAut_normalizes {N A : Subgroup G} {T : Multiset Ω}
    (hNA : N ≤ A) (hcomm : ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ N)
    (hfix : Fixes N T) : Normalizes A (Aut A T) := by
  intro a ha b hb
  have hc : ⁅a, b⁆ ∈ Aut A T :=
    linObjectKernel_le_aut hNA hfix (hcomm a ha b hb.1)
  have he : a * b * a⁻¹ = ⁅a, b⁆ * b := by
    rw [commutatorElement_def]
    group
  rw [he]
  exact (Aut A T).mul_mem hc hb

theorem linObjectPieceKernel_le_aut {N A : Subgroup G} {X T : Multiset Ω}
    (hNA : N ≤ A) (hfix : Fixes N X) (hT : T ∈ pieces A X) : N ≤ Aut A T :=
  linObjectKernel_le_aut hNA (hfix.of_le (piece_le hT))

theorem linObjectPieceAut_normalizes {N A : Subgroup G} {X T : Multiset Ω}
    (hNA : N ≤ A) (hcomm : ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ N)
    (hfix : Fixes N X) (hT : T ∈ pieces A X) : Normalizes A (Aut A T) :=
  linObjectAut_normalizes hNA hcomm (hfix.of_le (piece_le hT))

end GI.Impl
