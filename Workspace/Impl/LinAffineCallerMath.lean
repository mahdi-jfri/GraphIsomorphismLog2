module

public import Workspace.Impl.LinAffineCaller

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang
open scoped Pointwise

theorem linFiniteIntVec_zero_iff {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (x : linFiniteVec m) : (fun i => ((x i).val : ℤ)) = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    haveI : NeZero (m i) := ⟨Nat.ne_of_gt (hm i)⟩
    apply ZMod.val_injective
    have hi := congrFun h i
    simpa only [Pi.zero_apply, ZMod.val_zero, Int.natCast_eq_zero] using hi
  · rintro rfl
    funext i
    simp

theorem linAffineTrivial_trans {n d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (m : Fin d → ℕ) (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m))
    (c : gens gs → linFiniteVec m) (hc : ∀ g h, c (g * h) = ρ g (c h) + c g)
    (hgs : gens gs = ⊥) (v w : linFiniteVec m) :
    tmGLAffTrans gs ρ c v w = if v = w then {1} else ∅ := by
  have hg1 (g : gens gs) : g = 1 := by
    apply Subtype.ext
    exact (show gens gs ≤ ⊥ from hgs.le) g.property
  have hc1 := linFiniteCocycle_one ρ c hc
  ext t
  by_cases hvw : v = w
  · simp only [hvw, if_true, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [hg1 g]
      rfl
    · rintro rfl
      refine ⟨1, ?_, rfl⟩
      change ρ 1 w + c 1 = w
      simp [hc1]
  · simp only [hvw, if_false, Set.mem_empty_iff_false, iff_false]
    rintro ⟨g, hg, ht⟩
    change ρ g v + c g = w at hg
    rw [hg1 g, map_one, hc1] at hg
    exact hvw (by simpa using hg)

theorem linAffineTrivial_out {n d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (m : Fin d → ℕ) (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m))
    (c : gens gs → linFiniteVec m) (hc : ∀ g h, c (g * h) = ρ g (c h) + c g)
    (hgs : gens gs = ⊥) (v w : linFiniteVec m) :
    TmGLAffOut n (if v = w then .list [encPerm (1 : Equiv.Perm (Fin n)), encGroup ([] : List (Equiv.Perm (Fin n))) ] else .list [])
      (tmGLAffTrans gs ρ c v w) := by
  rw [linAffineTrivial_trans gs m ρ c hc hgs]
  by_cases hvw : v = w
  · simp only [hvw, if_true]
    refine Or.inr ⟨1, [], rfl, ?_⟩
    simp [gens]
  · exact Or.inl ⟨by simp [hvw], by simp [hvw]⟩

theorem linAffineTrivial_coset {n d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (m : Fin d → ℕ) (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m))
    (c : gens gs → linFiniteVec m) (hc : ∀ g h, c (g * h) = ρ g (c h) + c g)
    (hgs : gens gs = ⊥) (v w : linFiniteVec m) :
    CosetC n (if v = w then .list [encPerm (1 : Equiv.Perm (Fin n)),
      encGroup ([] : List (Equiv.Perm (Fin n)))] else .list []) (tmGLAffTrans gs ρ c v w) := by
  rw [linAffineTrivial_trans gs m ρ c hc hgs]
  by_cases h : v = w
  · simp only [if_pos h]
    exact Or.inr ⟨1, [], rfl, by simp, by simp [gens]⟩
  · exact Or.inl ⟨by simp [h], by simp [h]⟩

end GI.Impl
