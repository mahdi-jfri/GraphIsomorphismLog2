module

public import Workspace.CleanComplementInputs
public import Workspace.SmallDegreeBudget
public import Workspace.AlternatingSimple
public import Workspace.Localization

@[expose] public section

/-! Unconditional localization from the elementary linear degree obstruction.
These bounds use k > f and do not establish the paper's logarithmic A.15 bound. -/
namespace GI

theorem small_degree_kernel_surjects {U B : Type*} [Group U] [Fintype B]
    {k : ℕ} (hk : 5 ≤ k) (hdegree : Fintype.card B < k)
    (q : U →* alternatingGroup (Fin k)) (hq : Function.Surjective q)
    (f : U →* Equiv.Perm B) : f.ker.map q = ⊤ := by
  classical
  letI : IsSimpleGroup (alternatingGroup (Fin k)) := AlternatingSimple.isSimple_fin hk
  haveI : (f.ker.map q).Normal := (inferInstance : f.ker.Normal).map q hq
  rcases (inferInstance : (f.ker.map q).Normal).eq_bot_or_eq_top with hbot | htop
  · have hkern : f.rangeRestrict.ker ≤ q.ker := by
      intro x hx
      have hfx : f x = 1 := congrArg Subtype.val hx
      have hm : q x ∈ f.ker.map q := ⟨x, hfx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hm
      exact hm
    have hf : Function.Surjective f.rangeRestrict := by
      rintro ⟨y, x, hxy⟩
      exact ⟨x, Subtype.ext hxy⟩
    let r := HomDescent.factor f.rangeRestrict hf q hkern
    have hr : Function.Surjective r := HomDescent.factor_surjective _ hf q hkern hq
    exact False.elim ((no_alternating_surjection_of_small_order hk hdegree
      (permutation_subgroup_card_le_factorial f.range) r) hr)
  · exact htop

/-- The image on a small block already comes entirely from the top kernel. -/
theorem small_degree_kernel_image_eq {U B : Type*} [Group U] [Fintype B]
    {k : ℕ} (hk : 5 ≤ k) (hdegree : Fintype.card B < k)
    (q : U →* alternatingGroup (Fin k)) (hq : Function.Surjective q)
    (f : U →* Equiv.Perm B) : q.ker.map f = f.range := by
  apply le_antisymm
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    have hm : q x ∈ f.ker.map q := by
      rw [small_degree_kernel_surjects hk hdegree q hq f]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hqn⟩ := hm
    refine ⟨x * n⁻¹, ?_, ?_⟩
    · change q (x * n⁻¹) = 1
      rw [map_mul, map_inv, hqn]
      exact mul_inv_cancel _
    · change f n = 1 at hn
      simp [map_mul, map_inv, hn]

theorem mem_localization_commonKernel_iff {U : Type*} [Group U] (Ks : List (Subgroup U)) (x : U) :
    x ∈ commonKernel Ks ↔ ∀ K ∈ Ks, x ∈ K := by
  induction Ks with
  | nil => simp [commonKernel]
  | cons K Ks ih => simp [commonKernel, ih]

/-- Intersect the actual action kernels on all small components. Every prescribed
alternating top element still has a lift acting trivially in every component. -/
theorem small_degree_simultaneous_lift {U J : Type*} [Group U] [Fintype J]
    (B : J → Type*) [∀ j, Fintype (B j)] {k : ℕ} (hk : 5 ≤ k)
    (hdegree : ∀ j, Fintype.card (B j) < k)
    (q : U →* alternatingGroup (Fin k)) (hq : Function.Surjective q)
    (f : ∀ j, U →* Equiv.Perm (B j)) (p : alternatingGroup (Fin k)) :
    ∃ g : U, q g = p ∧ ∀ j, f j g = 1 := by
  classical
  let Ks := Finset.univ.toList.map (fun j => (f j).ker)
  have hn : ∀ K ∈ Ks, K.Normal := by
    intro K hK
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hK
    infer_instance
  have hm : ∀ K ∈ Ks, K.map q = ⊤ := by
    intro K hK
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hK
    exact small_degree_kernel_surjects hk (hdegree j) q hq (f j)
  letI : IsSimpleGroup (alternatingGroup (Fin k)) := AlternatingSimple.isSimple_fin hk
  have hmap := intersection_surjects q hq
    (simple_nonabelian_perfect (AlternatingSimple.nonabelian_fin hk)) Ks hn hm
  have hp : p ∈ (commonKernel Ks).map q := by rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨g, hg, hgp⟩ := hp
  refine ⟨g, hgp, ?_⟩
  intro j
  exact (mem_localization_commonKernel_iff Ks g).mp hg (f j).ker
    (List.mem_map.mpr ⟨j, by simp, rfl⟩)

end GI
