module

public import Workspace.Impl.LinObjectCallerSpec

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

/-- A left coset describing a cocycle fiber carries the zero fiber as its
subgroup. Thus the transporter call already computes the generators to lift. -/
theorem linObjectAffineFiber_kernel {G V : Type*} [Group G] [AddCommGroup V]
    (ρ : G →* (V ≃+ V)) (c : G → V)
    (hc : ∀ g h, c (g * h) = ρ g (c h) + c g) (t : V) (r : G) (L : Subgroup G)
    (hT : {g | c g = t} = (fun l => r * l) '' (L : Set G)) :
    c r = t ∧ ∀ l, l ∈ L ↔ c l = 0 := by
  have hcr : c r = t := by
    change r ∈ {g | c g = t}
    rw [hT]
    exact ⟨1,L.one_mem,by simp⟩
  refine ⟨hcr,?_⟩
  intro l
  constructor
  · intro hl
    have hrl : c (r * l) = t := by
      change r * l ∈ {g | c g = t}
      rw [hT]
      exact ⟨l,hl,rfl⟩
    have he : ρ r (c l) + c r = 0 + c r := by
      rw [← hc,hrl,hcr,zero_add]
    have hz := add_right_cancel he
    apply (ρ r).injective
    simpa only [map_zero] using hz
  · intro hl
    have hrl : r * l ∈ {g | c g = t} := by
      change c (r * l) = t
      rw [hc,hl,map_zero,zero_add,hcr]
    rw [hT] at hrl
    obtain ⟨k,hk,he⟩ := hrl
    exact mul_left_cancel he ▸ hk

theorem linObjectAffineTrans_zero_mem {n d : ℕ} (gs : List (Equiv.Perm (Fin n))) (m : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (t : linFiniteVec m) (g : gens gs) :
    g.val ∈ tmGLAffTrans gs ρ c 0 t ↔ c g = t := by
  constructor
  · rintro ⟨h,hh,he⟩
    have hg : h = g := Subtype.ext he
    subst h
    simpa only [Set.mem_setOf_eq, map_zero, zero_add] using hh
  · intro hg
    exact ⟨g, by simpa only [Set.mem_setOf_eq, map_zero, zero_add] using hg, rfl⟩

end GI.Impl
