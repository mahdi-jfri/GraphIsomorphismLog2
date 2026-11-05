module

public import Workspace.Impl.AggItemCiTest

@[expose] public section

/-!
# Cases 2b and 3, the configuration query: mathematics

The item `cfgItem X Y` (`AuxConfig.lean`) asks `Solve` on the pair structures of the fibers of
`X` and `Y`, and reads from the answer an even permutation `σ` of the labels that agrees on the
fiber of `X` with an element of the answer; the item is the overcoset `σ · autE X`. This file
has the facts the program needs.

* `itci_schreier`: Schreier's lemma for index two with any odd element `t` of the group (not
  only an involution): the list `itciSch t S` generates the even part.
* `itciFl s`: the points of `s` in increasing order, the order of `PairCfg.emb`
  (`itci_emb_eq`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm Finset

variable {q : ℕ}

/-! ### Schreier's lemma for index two -/

/-- The Schreier generators for the transversal `{1, t}` of the even part: for even `s`, `s` and
`t s t⁻¹`; for odd `s`, `s t⁻¹` and `t s`. -/
def itciSch (t : Perm (Fin q)) (S : List (Perm (Fin q))) : List (Perm (Fin q)) :=
  S.flatMap fun s => if sign s = 1 then [s, t * s * t⁻¹] else [s * t⁻¹, t * s]

theorem itci_mem_sch {t g : Perm (Fin q)} {S : List (Perm (Fin q))} :
    g ∈ itciSch t S ↔ ∃ s ∈ S, (sign s = 1 ∧ (g = s ∨ g = t * s * t⁻¹)) ∨
      (sign s ≠ 1 ∧ (g = s * t⁻¹ ∨ g = t * s)) := by
  simp only [itciSch, List.mem_flatMap]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  split_ifs with h <;> simp [h]

/-- **Schreier's lemma for index two**, with an odd element `t` of the group. -/
theorem itci_schreier {t : Perm (Fin q)} {S : List (Perm (Fin q))}
    (ht : t ∈ Subgroup.closure {s | s ∈ S}) (hst : sign t = -1) :
    Subgroup.closure {g | g ∈ itciSch t S} =
      Subgroup.closure {s | s ∈ S} ⊓ alternatingGroup (Fin q) := by
  set K := Subgroup.closure {g | g ∈ itciSch t S}
  have hti : sign t⁻¹ = -1 := by rw [Perm.sign_inv, hst]
  refine le_antisymm ((Subgroup.closure_le _).2 fun g hg => ?_) fun g ⟨hg, hgA⟩ => ?_
  · obtain ⟨s, hs, h⟩ := itci_mem_sch.1 hg
    have hsG : s ∈ Subgroup.closure {s | s ∈ S} := Subgroup.subset_closure hs
    have hss := itp_sign_cases s
    have hti' := Subgroup.inv_mem _ ht
    rcases h with ⟨h1, rfl | rfl⟩ | ⟨h1, rfl | rfl⟩
    · exact ⟨hsG, h1⟩
    · refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ ht hsG) hti', ?_⟩
      show sign _ = 1
      rw [Perm.sign_mul, Perm.sign_mul, h1, hst, hti]; decide
    · refine ⟨Subgroup.mul_mem _ hsG hti', ?_⟩
      show sign _ = 1
      rw [Perm.sign_mul, hss.resolve_left h1, hti]; decide
    · refine ⟨Subgroup.mul_mem _ ht hsG, ?_⟩
      show sign _ = 1
      rw [Perm.sign_mul, hss.resolve_left h1, hst]; decide
  · have mem : ∀ g, g ∈ itciSch t S → g ∈ K := fun g h => Subgroup.subset_closure h
    have hK1 : ∀ s ∈ S, sign s = 1 → s ∈ K ∧ t * s * t⁻¹ ∈ K := fun s hs h1 =>
      ⟨mem _ (itci_mem_sch.2 ⟨s, hs, Or.inl ⟨h1, Or.inl rfl⟩⟩),
        mem _ (itci_mem_sch.2 ⟨s, hs, Or.inl ⟨h1, Or.inr rfl⟩⟩)⟩
    have hK2 : ∀ s ∈ S, sign s = -1 → s * t⁻¹ ∈ K ∧ t * s ∈ K := fun s hs h1 => by
      have h1' : sign s ≠ 1 := by rw [h1]; decide
      exact ⟨mem _ (itci_mem_sch.2 ⟨s, hs, Or.inr ⟨h1', Or.inl rfl⟩⟩),
        mem _ (itci_mem_sch.2 ⟨s, hs, Or.inr ⟨h1', Or.inr rfl⟩⟩)⟩
    -- the invariant along words in `S`: `x` is in `K` if even, `x t⁻¹` is if odd
    have key : ∀ x ∈ Subgroup.closure {s | s ∈ S},
        (sign x = 1 → x ∈ K) ∧ (sign x = -1 → x * t⁻¹ ∈ K) := by
      intro x hx
      induction hx using Subgroup.closure_induction_right with
      | one => exact ⟨fun _ => K.one_mem, fun h => by rw [Perm.sign_one] at h; exact absurd h (by decide)⟩
      | mul_right x _ s hs ih =>
        rcases itp_sign_cases x with hx | hx <;> rcases itp_sign_cases s with h | h
        · refine ⟨fun _ => K.mul_mem (ih.1 hx) (hK1 s hs h).1, fun h' => ?_⟩
          rw [Perm.sign_mul, hx, h] at h'; exact absurd h' (by decide)
        · refine ⟨fun h' => ?_, fun _ => ?_⟩
          · rw [Perm.sign_mul, hx, h] at h'; exact absurd h' (by decide)
          · rw [mul_assoc]; exact K.mul_mem (ih.1 hx) (hK2 s hs h).1
        · refine ⟨fun h' => ?_, fun _ => ?_⟩
          · rw [Perm.sign_mul, hx, h] at h'; exact absurd h' (by decide)
          · rw [show x * s * t⁻¹ = x * t⁻¹ * (t * s * t⁻¹) by group]
            exact K.mul_mem (ih.2 hx) (hK1 s hs h).2
        · refine ⟨fun _ => ?_, fun h' => ?_⟩
          · rw [show x * s = x * t⁻¹ * (t * s) by group]
            exact K.mul_mem (ih.2 hx) (hK2 s hs h).2
          · rw [Perm.sign_mul, hx, h] at h'; exact absurd h' (by decide)
      | mul_inv_cancel x _ s hs ih =>
        rcases itp_sign_cases x with hx | hx <;> rcases itp_sign_cases s with h | h
        · refine ⟨fun _ => K.mul_mem (ih.1 hx) (K.inv_mem (hK1 s hs h).1), fun h' => ?_⟩
          rw [Perm.sign_mul, Perm.sign_inv, hx, h] at h'; exact absurd h' (by decide)
        · refine ⟨fun h' => ?_, fun _ => ?_⟩
          · rw [Perm.sign_mul, Perm.sign_inv, hx, h] at h'; exact absurd h' (by decide)
          · rw [show x * s⁻¹ * t⁻¹ = x * (t * s)⁻¹ by group]
            exact K.mul_mem (ih.1 hx) (K.inv_mem (hK2 s hs h).2)
        · refine ⟨fun h' => ?_, fun _ => ?_⟩
          · rw [Perm.sign_mul, Perm.sign_inv, hx, h] at h'; exact absurd h' (by decide)
          · rw [show x * s⁻¹ * t⁻¹ = x * t⁻¹ * (t * s * t⁻¹)⁻¹ by group]
            exact K.mul_mem (ih.2 hx) (K.inv_mem (hK1 s hs h).2)
        · refine ⟨fun _ => ?_, fun h' => ?_⟩
          · rw [show x * s⁻¹ = x * t⁻¹ * (s * t⁻¹)⁻¹ by group]
            exact K.mul_mem (ih.2 hx) (K.inv_mem (hK2 s hs h).1)
          · rw [Perm.sign_mul, Perm.sign_inv, hx, h] at h'; exact absurd h' (by decide)
    exact (key g hg).1 hgA

/-! ### Points of a set in increasing order -/

/-- The points of `s` in increasing order. -/
def itciFl (s : Finset (Fin q)) : List (Fin q) := (List.finRange q).filter (· ∈ s)

theorem itci_sort_eq (s : Finset (Fin q)) : s.sort = itciFl s := by
  refine s.sortedLT_sort.eq_of_mem_iff ?_ (fun a => by simp [itciFl])
  rw [List.sortedLT_iff_pairwise]
  exact ((List.sortedLT_iff_pairwise).1 (List.sortedLT_finRange q)).filter _

theorem itciFl_length (s : Finset (Fin q)) : (itciFl s).length = s.card := by
  rw [← itci_sort_eq, Finset.length_sort]

theorem itciFl_nodup (s : Finset (Fin q)) : (itciFl s).Nodup :=
  (List.nodup_finRange q).filter _

theorem itci_mem_fl {s : Finset (Fin q)} {a : Fin q} : a ∈ itciFl s ↔ a ∈ s := by
  simp [itciFl]

/-- **The numbering of the fiber is by the list**: `emb h i` is entry `i` of `itciFl`. -/
theorem itci_emb_eq (X : PairCfg q) {n : ℕ} (h : X.fiber.card = n) (i : Fin n) :
    X.emb h i = (itciFl X.fiber)[i.1]'(by rw [itciFl_length, h]; exact i.2) := by
  change (X.fiber.orderEmbOfFin h i) = _
  rw [Finset.orderEmbOfFin_apply]
  simp only [itci_sort_eq]; rfl

end GI.Impl
