module

public import Workspace.Lang.Prims.BlockMath

@[expose] public section

/-! # Kernels of generator-defined actions as preimage instances -/

namespace GI.Proved

open GI.Cited GI.Lang Equiv

variable {n m : ℕ} (H : Subgroup (Perm (Fin n)))
  (φ : H →* Perm (Fin m))

open Classical in
/-- Outside the acting group the extension is arbitrary and is never used. -/
noncomputable def gmpGraphPerm (g : Perm (Fin n)) : Perm (Fin n ⊕ Fin m) :=
  if hg : g ∈ H then sumCongr g (φ ⟨g, hg⟩) else 1

theorem gmpGraphPerm_of_mem {g : Perm (Fin n)} (hg : g ∈ H) :
    gmpGraphPerm H φ g = sumCongr g (φ ⟨g, hg⟩) := dif_pos hg

theorem gmpGraphPerm_mul {g h : Perm (Fin n)} (hg : g ∈ H) (hh : h ∈ H) :
    gmpGraphPerm H φ (g * h) = gmpGraphPerm H φ g * gmpGraphPerm H φ h := by
  rw [gmpGraphPerm_of_mem H φ (H.mul_mem hg hh), gmpGraphPerm_of_mem H φ hg,
    gmpGraphPerm_of_mem H φ hh]
  change sumCongr (g * h) (φ (⟨g, hg⟩ * ⟨h, hh⟩)) = _
  rw [map_mul, Perm.sumCongr_mul]

noncomputable def gmpGraphKernelInst (gs : List (Perm (Fin n)))
    (hgs : ∀ g ∈ gs, g ∈ H) : PreimageInst where
  n := n
  n' := m
  ds := gs.map (gmpGraphPerm H φ)
  ms := []
  preserves := by
    intro d hd i
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hd
    rw [gmpGraphPerm_of_mem H φ (hgs g hg)]
    exact ⟨g i, rfl⟩
  ms_le := by simp

theorem gmpGraphKernelInst_mem (gs : List (Perm (Fin n)))
    (hgs : ∀ g ∈ gs, g ∈ H) (g : Perm (Fin n)) :
    g ∈ GI.CitedChecks.preimageSubgroup (gmpGraphKernelInst H φ gs hgs) ↔
      ∃ hg : g ∈ gens gs, φ ⟨g, (show gens gs ≤ H from
        (by rw [gens, Subgroup.closure_le]; exact hgs)) hg⟩ = 1 := by
  have hle : gens gs ≤ H := (by rw [gens, Subgroup.closure_le]; exact hgs)
  have hgraph : ∀ x : Perm (Fin n ⊕ Fin m),
      x ∈ Subgroup.closure {d | d ∈ gs.map (gmpGraphPerm H φ)} ↔
        ∃ g ∈ gens gs, gmpGraphPerm H φ g = x := by
    intro x
    have he : {d | d ∈ gs.map (gmpGraphPerm H φ)} =
        {d | ∃ g ∈ gs, gmpGraphPerm H φ g = d} := by ext d; simp
    rw [he]
    exact mem_closure_image_of_mul H (gmpGraphPerm H φ)
      (fun _ hg _ hh => gmpGraphPerm_mul H φ hg hh) hgs x
  change (∃ k ∈ Subgroup.closure {k | k ∈ ([] : List (Perm (Fin m)))},
    sumCongr g k ∈ Subgroup.closure {d | d ∈ gs.map (gmpGraphPerm H φ)}) ↔ _
  simp only [List.not_mem_nil, Set.setOf_false, Subgroup.closure_empty,
    Subgroup.mem_bot, exists_eq_left, hgraph]
  constructor
  · rintro ⟨a, ha, he⟩
    rw [gmpGraphPerm_of_mem H φ (hle ha)] at he
    have hag : a = g := by
      apply Equiv.ext
      intro i
      exact Sum.inl.inj (congrArg (fun p => p (Sum.inl i)) he)
    subst a
    have hk : φ ⟨g, hle ha⟩ = 1 := by
      apply Equiv.ext
      intro i
      exact Sum.inr.inj (congrArg (fun p => p (Sum.inr i)) he)
    exact ⟨ha, hk⟩
  · rintro ⟨hg, hk⟩
    exact ⟨g, hg, by rw [gmpGraphPerm_of_mem H φ (hle hg), hk]⟩

end GI.Proved
