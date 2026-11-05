module

public import Workspace.Impl.LinWreathVector

@[expose] public section

/-! Correctness of scanning the generating list returned by VectorStabilizer.
Both success and failure are justified in the original permutation cover. -/
namespace GI.Impl
open GI.Cited Equiv

noncomputable def linWreathReturned (I : VecStabInst) [Nonempty (Fin I.n)]
    (hs : List (Perm (Fin (I.n + I.n)))) : List (gens I.gs ≀ᵣ linTwo) :=
  hs.map (fun x => (linWreathCoverEquiv I.gs).symm
    (linIntoSubgroup (gens (linWreathCoverGenerators I.gs)) x))

/-- A returned stabilizer generator belongs to the cover before it is lifted. -/
theorem linWreathReturned_map (I : VecStabInst) [Nonempty (Fin I.n)]
    (w : Fin I.d → ZMod I.p) (hs : List (Perm (Fin (I.n + I.n))))
    (hh : gens hs = (vecStab (linWreathVecInst I w)).map
      (gens (linWreathCoverGenerators I.gs)).subtype) :
    (linWreathReturned I hs).map (linWreathFinCover (gens I.gs)) = hs := by
  have hle : gens hs ≤ gens (linWreathCoverGenerators I.gs) := by
    rw [hh]
    exact Subgroup.map_subtype_le _
  have he := linIntoSubgroup_map (gens (linWreathCoverGenerators I.gs)) hs
    (fun x hx => hle (Subgroup.subset_closure hx))
  simpa only [linWreathReturned, List.map_map, Function.comp_def,
    ← linWreathCoverEquiv_val, MulEquiv.apply_symm_apply, Subgroup.subtype_apply] using he

/-- Every lifted generator fixes the pair, because the primitive returns the
whole vector stabilizer, not only a subgroup of it. -/
theorem linWreathReturned_mem (I : VecStabInst) [Nonempty (Fin I.n)]
    (w : Fin I.d → ZMod I.p) (hs : List (Perm (Fin (I.n + I.n))))
    (hh : gens hs = (vecStab (linWreathVecInst I w)).map
      (gens (linWreathCoverGenerators I.gs)).subtype)
    {a : gens I.gs ≀ᵣ linTwo} (ha : a ∈ linWreathReturned I hs) :
    linWreathCoverEquiv I.gs a ∈ vecStab (linWreathVecInst I w) := by
  have hm := linWreathReturned_map I w hs hh
  have hp : linWreathFinCover (gens I.gs) a ∈ gens hs :=
    Subgroup.subset_closure (by rw [← hm]; exact List.mem_map_of_mem ha)
  rw [hh] at hp
  obtain ⟨b, hb, he⟩ := hp
  have he' : b = linWreathCoverEquiv I.gs a := by
    apply Subtype.ext
    exact he
  exact he' ▸ hb

/-- Checking the returned generators for a swap is a complete transporter
nonemptiness test. No enumeration of the stabilizer is needed. -/
theorem linWreathReturned_transport (I : VecStabInst) [Nonempty (Fin I.n)]
    (w : Fin I.d → ZMod I.p) (hs : List (Perm (Fin (I.n + I.n))))
    (hh : gens hs = (vecStab (linWreathVecInst I w)).map
      (gens (linWreathCoverGenerators I.gs)).subtype) :
    (∃ a ∈ linWreathReturned I hs, a.right = linTwoSwap) ↔
      ∃ g : gens I.gs, (I.φ g).val.mulVec I.v = w := by
  constructor
  · rintro ⟨a, ha, hs⟩
    exact (linWreathVecInst_transport I w).mp
      ⟨a, hs, linWreathReturned_mem I w _ hh ha⟩
  · intro hg
    obtain ⟨a, hswap, ha⟩ := (linWreathVecInst_transport I w).mpr hg
    apply (linWreath_swap_generator_iff (linWreathReturned I hs)).mp
    refine ⟨a, ?_, hswap⟩
    let f := linWreathFinCover (n := I.n) (gens I.gs)
    have hm : (Subgroup.closure {a | a ∈ linWreathReturned I hs}).map f = gens hs := by
      rw [MonoidHom.map_closure]
      have he : f '' {a | a ∈ linWreathReturned I hs} = {x | x ∈ hs} := by
        calc f '' {a | a ∈ linWreathReturned I hs} =
            {x | x ∈ (linWreathReturned I hs).map f} := by
              ext x
              simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_map]
          _ = {x | x ∈ hs} := by rw [linWreathReturned_map I w hs hh]
      rw [he]
      rfl
    have hp : f a ∈ (Subgroup.closure {a | a ∈ linWreathReturned I hs}).map f := by
      rw [hm, hh]
      exact ⟨linWreathCoverEquiv I.gs a, ha, rfl⟩
    obtain ⟨b, hb, he⟩ := hp
    have he' : b = a := linWreathFinCover_injective he
    exact he' ▸ hb

/-- A swapping returned generator yields the required original-cover element. -/
theorem linWreathReturned_extract (I : VecStabInst) [Nonempty (Fin I.n)]
    (w : Fin I.d → ZMod I.p) (hs : List (Perm (Fin (I.n + I.n))))
    (hh : gens hs = (vecStab (linWreathVecInst I w)).map
      (gens (linWreathCoverGenerators I.gs)).subtype)
    {a : gens I.gs ≀ᵣ linTwo} (ha : a ∈ linWreathReturned I hs)
    (hswap : a.right = linTwoSwap) :
    (I.φ (a.left linTwoSwap)).val.mulVec I.v = w := by
  exact linWreath_extract (R := ZMod I.p) (linMatrixLinearEquiv.toMonoidHom.comp I.φ)
    I.v w a hswap ((linWreathVecInst_mem I w a).mp (linWreathReturned_mem I w hs hh ha))

end GI.Impl
