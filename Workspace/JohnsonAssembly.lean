module

public import Workspace.JohnsonForestExtra
public import Workspace.JohnsonForestMerge
public import Mathlib.Data.Finset.Max

@[expose] public section

namespace GI.Johnson

open RefinementTree

variable {α I : Type*} [DecidableEq α] [DecidableEq I]

omit [DecidableEq α] [DecidableEq I] in
theorem pairwise_regions_of_nodup (f : I → RefinementTree α) {l : List I} (hn : l.Nodup)
    (hd : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → Disjoint (f i).region (f j).region) :
    (l.map f).Pairwise (fun t u => Disjoint t.region u.region) := by
  induction l with
  | nil => simp
  | cons i is ih =>
      obtain ⟨hi, his⟩ := List.nodup_cons.mp hn
      apply List.pairwise_cons.mpr
      constructor
      · intro t ht
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
        apply hd i (List.mem_cons_self ..) j (List.mem_cons_of_mem _ hj)
        intro he
        exact hi (he ▸ hj)
      · exact ih his (fun j hj k hk => hd j (List.mem_cons_of_mem _ hj) k (List.mem_cons_of_mem _ hk))

/-- Assemble actual child forests after an orbit split. A largest child keeps
the inherited remaining budget; each other child's root uses its natural bound. -/
theorem assemble_forests (C B oldBudget : ℝ) (T E : Finset α) (s : Finset I)
    (hne : s.Nonempty) (trees : I → RefinementTree α) (charge budget : I → ℝ)
    (hv : ∀ i ∈ s, (trees i).Valid T)
    (hsub : ∀ i ∈ s, (trees i).region ⊆ E)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (trees i).region (trees j).region)
    (hcharge : ∀ i ∈ s, charge i ≤ budget i + (trees i).extraAllowance C B)
    (hinherit : ∀ i ∈ s, budget i ≤ oldBudget)
    (hfresh : ∀ i ∈ s, budget i ≤ C * Real.log ((trees i).region.card : ℝ) - B) :
    ∃ t : RefinementTree α, t.Valid T ∧ t.region = E ∧
      (∑ i ∈ s, charge i) ≤ oldBudget + t.extraAllowance C B := by
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun j => (trees j).region.card) hne
  let fresh := (s.erase i).toList.map trees
  let t := mergeAt E (trees i) fresh
  have hfmem : ∀ u ∈ fresh, ∃ j ∈ s.erase i, trees j = u := by
    intro u hu
    obtain ⟨j, hj, hju⟩ := List.mem_map.mp hu
    exact ⟨j, Finset.mem_toList.mp hj, hju⟩
  have hpair : (trees i :: fresh).Pairwise (fun a b => Disjoint a.region b.region) := by
    change ((i :: (s.erase i).toList).map trees).Pairwise _
    apply pairwise_regions_of_nodup trees
    · exact List.nodup_cons.mpr ⟨by simp, Finset.nodup_toList _⟩
    · intro j hj k hk hjk
      have hs : ∀ x ∈ i :: (s.erase i).toList, x ∈ s := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hi
        · exact Finset.mem_of_mem_erase (Finset.mem_toList.mp hx)
      exact hdis j (hs j hj) k (hs k hk) hjk
  have hvalid : t.Valid T := by
    apply mergeAt_valid (trees i) fresh (hv i hi)
    · intro u hu
      obtain ⟨j, hj, rfl⟩ := hfmem u hu
      exact hv j (Finset.mem_of_mem_erase hj)
    · exact hpair
    · intro u hu
      obtain ⟨j, hj, rfl⟩ := hfmem u hu
      exact hmax j (Finset.mem_of_mem_erase hj)
    · exact hsub i hi
    · intro u hu
      obtain ⟨j, hj, rfl⟩ := hfmem u hu
      exact hsub j (Finset.mem_of_mem_erase hj)
  refine ⟨t, hvalid, rfl, ?_⟩
  have hex : t.extraAllowance C B = (trees i).extraAllowance C B +
      ∑ j ∈ s.erase i, ((C * Real.log ((trees j).region.card : ℝ) - B) + (trees j).extraAllowance C B) := by
    change ((mergeAt E (trees i) fresh).extraStarts.map
      (fun (n : ℕ) => C * Real.log (n : ℝ) - B)).sum = _
    rw [mergeAt_extraStarts, List.map_append, List.sum_append, startAllowance_flatMap]
    simp only [extraAllowance, fresh, List.map_map, Function.comp_def, Finset.sum_map_toList]
  have hsum : (∑ j ∈ s, charge j) = charge i + ∑ j ∈ s.erase i, charge j := by
    calc
      (∑ j ∈ s, charge j) = ∑ j ∈ insert i (s.erase i), charge j := by rw [Finset.insert_erase hi]
      _ = _ := Finset.sum_insert (Finset.notMem_erase _ _)
  have hm := (hcharge i hi).trans (add_le_add_left (hinherit i hi) _)
  have hs : (∑ j ∈ s.erase i, charge j) ≤
      ∑ j ∈ s.erase i, ((C * Real.log ((trees j).region.card : ℝ) - B) + (trees j).extraAllowance C B) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hcharge j (Finset.mem_of_mem_erase hj)).trans
      (add_le_add_left (hfresh j (Finset.mem_of_mem_erase hj)) _)
  rw [hsum, hex]
  linarith

end GI.Johnson
