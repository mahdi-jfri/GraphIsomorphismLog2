import Workspace.Impl.LinObjectAffineFiber

namespace GI.Impl
open GI.Cited GI.Lang

/-- Decode the subgroup of a nonempty affine answer: its permutations are
exactly the zero-cocycle cover elements, with no faithfulness assumption. -/
theorem linObjectAffineCoset_group {n d : ℕ} (gs : List (Equiv.Perm (Fin n))) (m : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (t : linFiniteVec m)
    (r : Equiv.Perm (Fin n)) (ls : List (Equiv.Perm (Fin n)))
    (hT : tmGLAffTrans gs ρ c 0 t = (fun l => r * l) '' (gens ls : Set (Equiv.Perm (Fin n)))) :
    ∃ a : gens gs, a.val = r ∧ c a = t ∧ gens ls ≤ gens gs ∧
      ∀ l : gens gs, l.val ∈ gens ls ↔ c l = 0 := by
  have hr : r ∈ tmGLAffTrans gs ρ c 0 t := by
    rw [hT]
    exact ⟨1,(gens ls).one_mem,by simp⟩
  obtain ⟨a,ha,har⟩ := hr
  have hL : gens ls ≤ gens gs := by
    intro l hl
    have hrl : r * l ∈ tmGLAffTrans gs ρ c 0 t := by rw [hT]; exact ⟨l,hl,rfl⟩
    obtain ⟨k,hk,hek⟩ := hrl
    have hrH : r ∈ gens gs := har ▸ a.property
    have hrlH : r * l ∈ gens gs := hek ▸ k.property
    have hh := (gens gs).mul_mem ((gens gs).inv_mem hrH) hrlH
    simpa using hh
  let L := (gens ls).subgroupOf (gens gs)
  have hSet : {k : gens gs | c k = t} = (fun l => a * l) '' (L : Set (gens gs)) := by
    ext k
    constructor
    · intro hk
      have hkm : k.val ∈ tmGLAffTrans gs ρ c 0 t := (linObjectAffineTrans_zero_mem gs m ρ c t k).mpr hk
      rw [hT] at hkm
      obtain ⟨l,hl,he⟩ := hkm
      refine ⟨⟨l,hL hl⟩,hl,Subtype.ext ?_⟩
      change a.val * l = k.val
      rw [har]
      exact he
    · rintro ⟨l,hl,he⟩
      apply (linObjectAffineTrans_zero_mem gs m ρ c t k).mp
      rw [hT]
      refine ⟨l.val,hl,?_⟩
      have hv := congrArg Subtype.val he
      change a.val * l.val = k.val at hv
      rwa [har] at hv
  have hkernel := linObjectAffineFiber_kernel ρ c hc t a L hSet
  exact ⟨a,har,hkernel.1,hL,hkernel.2⟩

end GI.Impl
