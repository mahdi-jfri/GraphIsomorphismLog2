module

public import Workspace.Cited.Facts
public import Workspace.Degree.JohnsonWreath
import Maroti.Main
import Workspace.Degree.MarotiWreath
import Maroti.Assembly.Classification
import Maroti.Alternating.AutBound
import Maroti.Linear.OrderAut
import Maroti.Classical.AutBound
import Maroti.Exceptional.AutBound
import Maroti.Sporadic.AutBound
import CFSG.Sporadic.Bridge.M11
import CFSG.Sporadic.Bridge.M12
import CFSG.Sporadic.Presentation.M23
import CFSG.Sporadic.Presentation.M24Exact

/-!
# Maróti's theorem for all degrees, and `|Aut T| ≤ |T|²`

Two cited results in the form that the degree-sensitive group theory uses. Like
`Workspace/Cited/Facts.lean`, this file imports the formalization of Maróti's theorem privately,
so a file that imports it sees only these statements.
-/

@[expose] public section

namespace GI.Degree

open Equiv

/-- **Maróti's Theorem 1.1**, for all degrees at least 2. A primitive group of degree `n` is a
Johnson product, or a Mathieu group of degree at least 11 (with order at most `n^7`), or has order below `n^(1 + ⌊log₂ n⌋)`. -/
theorem marotiFull {α : Type} [Finite α] [Nontrivial α] (G : Subgroup (Perm α))
    (hG : MulAction.IsPreprimitive G α) :
    (∃ (m k r : ℕ) (e : α ≃ JohnsonTuple m k r), 5 ≤ m ∧ 1 ≤ k ∧ 2 * k < m ∧ 1 ≤ r ∧
      WreathStructure G e) ∨
    (Nat.card G ≤ Nat.card α ^ 7 ∧ 11 ≤ Nat.card α) ∨
    Nat.card G < Nat.card α ^ (1 + Nat.log 2 (Nat.card α)) := by
  rcases Maroti.theorem_1_1_of_classification GI.Cited.cfsg G with
    ⟨m, k, r, e, hm, hk, hkm, hr, hwr, halt⟩ | ⟨s, hs, hcard, -, ⟨eG⟩⟩ | ⟨hle, hlt⟩
  · exact Or.inl (wreathStructure_of_productAction G ⟨m, k, r, e, hm, hk, hkm, hr, hwr, halt⟩)
  · refine Or.inr (Or.inl ?_)
    have hc : Nat.card G = Nat.card s.1.Group := Nat.card_congr eG.toEquiv
    simp only [Maroti.fourTransitiveMathieu, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · rw [hcard]
      exact ⟨hc ▸ CFSG.Sporadic.Bridge.M11.tauCeti_finite_card_le.2.trans (by norm_num),
        by norm_num⟩
    · rw [hcard]
      exact ⟨hc ▸ CFSG.Sporadic.Bridge.M12.tauCeti_finite_card_le.2.trans (by norm_num),
        by norm_num⟩
    · rw [hcard]
      exact ⟨hc ▸ CFSG.Sporadic.Presentation.M23.finite_card_le.2.trans (by norm_num),
        by norm_num⟩
    · rw [hcard]
      exact ⟨hc ▸ CFSG.Sporadic.Presentation.M24.finite_card_le.2.trans (by norm_num),
        by norm_num⟩
  · exact Or.inr (Or.inr (hle.trans_lt hlt))

/-- **`|Aut T| ≤ |T|²`** for every finite nonabelian simple group. -/
theorem autBound {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hT : ∃ a b : T, a * b ≠ b * a) : Nat.card (MulAut T) ≤ Nat.card T ^ 2 :=
  Maroti.autBound_of_families GI.Cited.cfsg Maroti.autBound_alternating Maroti.autBound_linear
    Maroti.autBound_otherClassical Maroti.autBound_exceptional Maroti.autBound_sporadic T
    ⟨inferInstance, hT⟩

end GI.Degree
