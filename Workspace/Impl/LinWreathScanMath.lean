module

public import Workspace.Impl.LinWreathReturned

@[expose] public section

namespace GI.Impl
open GI.Cited Equiv

/-- Lift a listed permutation through the faithful numbered cover. -/
theorem linWreathReturned_lift (I : VecStabInst) [Nonempty (Fin I.n)]
    (w : Fin I.d → ZMod I.p) (hs : List (Perm (Fin (I.n + I.n))))
    (hh : gens hs = (vecStab (linWreathVecInst I w)).map
      (gens (linWreathCoverGenerators I.gs)).subtype)
    {σ : Perm (Fin (I.n + I.n))} (hσ : σ ∈ hs) :
    ∃ a ∈ linWreathReturned I hs, linWreathFinCover (n := I.n) (gens I.gs) a = σ := by
  have he := linWreathReturned_map I w hs hh
  rw [← he] at hσ
  exact List.mem_map.mp hσ

/-- The point-image predicate scanned by the program detects every nonempty
original vector transporter. -/
theorem linWreathReturned_perms (I : VecStabInst) [NeZero I.n]
    (w : Fin I.d → ZMod I.p) (hs : List (Perm (Fin (I.n + I.n))))
    (hh : gens hs = (vecStab (linWreathVecInst I w)).map
      (gens (linWreathCoverGenerators I.gs)).subtype) :
    (∃ σ ∈ hs, I.n ≤ (σ (0 : Fin (I.n + I.n)) : ℕ)) ↔
      ∃ g : gens I.gs, (I.φ g).val.mulVec I.v = w := by
  constructor
  · rintro ⟨σ, hσ, ht⟩
    obtain ⟨a, ha, rfl⟩ := linWreathReturned_lift I w hs hh hσ
    have hswap := (linWreathCover_first_swap_test I.gs a).mp ht
    exact (linWreathReturned_transport I w hs hh).mp ⟨a, ha, hswap⟩
  · intro hg
    obtain ⟨a, ha, hswap⟩ := (linWreathReturned_transport I w hs hh).mpr hg
    refine ⟨linWreathFinCover (gens I.gs) a, ?_,
      (linWreathCover_first_swap_test I.gs a).mpr hswap⟩
    rw [← linWreathReturned_map I w hs hh]
    exact List.mem_map_of_mem ha

/-- Every selected swapping table gives both a transporter and its exact
restriction table, as used by the extraction program. -/
theorem linWreathReturned_selected (I : VecStabInst) [NeZero I.n]
    (w : Fin I.d → ZMod I.p) (hs : List (Perm (Fin (I.n + I.n))))
    (hh : gens hs = (vecStab (linWreathVecInst I w)).map
      (gens (linWreathCoverGenerators I.gs)).subtype)
    {σ : Perm (Fin (I.n + I.n))} (hσ : σ ∈ hs)
    (ht : I.n ≤ (σ (0 : Fin (I.n + I.n)) : ℕ)) :
    ∃ a ∈ linWreathReturned I hs,
      linWreathFinCover (n := I.n) (gens I.gs) a = σ ∧ a.right = linTwoSwap ∧
      (I.φ (a.left linTwoSwap)).val.mulVec I.v = w := by
  obtain ⟨a, ha, rfl⟩ := linWreathReturned_lift I w hs hh hσ
  have hswap := (linWreathCover_first_swap_test I.gs a).mp ht
  exact ⟨a, ha, rfl, hswap, linWreathReturned_extract I w hs hh ha hswap⟩

end GI.Impl
