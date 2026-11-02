import Workspace.Impl.TermJOLink
import Workspace.Impl.TermJTabMath

/-!
# The table `O` of the `N`-tests (mathematics)

For the stored answers `us` of the `N`-tests `tmTestState S E σN ac`, the table `tmJOOf us q`
has the three properties that `tmJTab_aut` asks for (`tmJO_props`): every diagonal entry is
`(r, gs)` with `⟨gs⟩ = Aut_N(x_a)`, a nonempty entry `(b, _)` of `(a, a')` is an
`N`-transporter `x_a → x_{a'}`, and an empty entry means that there is none.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly Equiv
open GI.Cited (Val encPerm encGroup gens)
open scoped Pointwise

variable {Ω C : Type}

attribute [local instance] stringRAct

theorem tmJO_test_answer {S : State Ω C} {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    (σN : List (Perm (Fin m))) (a a' : Fin q) (g : Perm (Fin m)) :
    g ∈ (tmTestState S E σN (.inl a, .inl a')).answer ↔
      g ∈ gens σN ∧ tmRowStr S E (.inl a) ∘ g = tmRowStr S E (.inl a') := by
  unfold tmTestState
  rw [rowState_answer]
  rfl

/-- **The three facts of the table.** -/
theorem tmJO_props {S : State Ω C} {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    (σN : List (Perm (Fin m))) {us : List Val}
    (hus : List.Forall₂ (fun u ac => AnsC (Equiv.refl (Fin m)) u
      (tmTestState S E σN ac).answer) us (tmTests q)) :
    (∀ a, ∃ r gs, tmJOOf us q a a = some (r, gs) ∧
      Subgroup.closure {s | s ∈ gs} = tmJRowAut (gens σN) (tmRowStr S E (.inl a))) ∧
    (∀ a a' b gs, tmJOOf us q a a' = some (b, gs) →
      b ∈ gens σN ∧ tmRowStr S E (.inl a) ∘ b = tmRowStr S E (.inl a')) ∧
    (∀ a a', tmJOOf (m := m) us q a a' = none →
      ∀ b ∈ gens σN, tmRowStr S E (.inl a) ∘ b ≠ tmRowStr S E (.inl a')) := by
  refine ⟨fun a => ?_, fun a a' b gs h => ?_, fun a a' h b hb hx => ?_⟩
  · have hK : (tmTestState S E σN (.inl a, .inl a)).answer =
        ((tmJRowAut (gens σN) (tmRowStr S E (.inl a)) : Subgroup (Perm (Fin m))) :
          Set (Perm (Fin m))) := by
      ext g
      rw [tmJO_test_answer]
      rfl
    obtain ⟨r, gs, hO, hg, -, -⟩ := tmJO_diag hus a hK
    exact ⟨r, gs, hO, hg⟩
  · obtain ⟨hT, -⟩ := tmJO_some hus h
    have hb : b ∈ (tmTestState S E σN (.inl a, .inl a')).answer := by
      rw [hT]; exact ⟨1, Subgroup.one_mem _, mul_one b⟩
    exact (tmJO_test_answer E σN a a' b).1 hb
  · have hT := tmJO_none hus h
    have hb' : b ∈ (tmTestState S E σN (.inl a, .inl a')).answer :=
      (tmJO_test_answer E σN a a' b).2 ⟨hb, hx⟩
    rw [hT] at hb'
    exact hb'

end GI.Impl
