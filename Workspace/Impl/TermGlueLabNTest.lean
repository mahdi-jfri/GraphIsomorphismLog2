import Workspace.Impl.TermGlueLabPRep

/-!
# The label driver: which case of step 5

Proof of Theorem A.23, step 5. The paper adds the orientation coordinate exactly
when all types of `x` are distinct. The driver must decide this from data it has: the labels of
`x` (`tmGLPXLab_spec`) give for each row `k` the first row `J_k` of its type. All types are
distinct exactly when every row is the first row of its type (`tmGLN_nodup_iff`).
-/

namespace GI.Impl

open GI.Multicoset Equiv

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω]

/-- **All types are distinct exactly when `J_k = k` for every row.** -/
theorem tmGLN_nodup_iff {N : Subgroup (Perm (Fin n))} {q : ℕ} {X : Fin q → Ω}
    {J : Fin q → Fin q} (hJ : ∀ k, TmGLPFirst N X (X k) (J k)) :
    (types N X).Nodup ↔ ∀ k, J k = k := by
  have hinj : (types N X).Nodup ↔ Function.Injective fun i => orbitN N (X i) := by
    rw [types, Multiset.nodup_map_iff_inj_on Finset.univ.nodup]
    exact ⟨fun h i j e => h i (by simp) j (by simp) e, fun h i _ j _ e => h e⟩
  rw [hinj]
  constructor
  · -- `x_k` lies in the orbit of `x_{J_k}`, so the two rows have the same type
    intro h k
    exact h (tmGLP_orbit_eq (hJ k).1).symm
  · -- a row with a smaller row of the same type would not be the first row of its type
    intro h i j e
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have hj := (hJ j).2 i (by rw [h j]; exact hlt)
      exact hj (by simp only at e; rw [e]; exact tmGLP_self_mem N (X j))
    · have hi := (hJ i).2 j (by rw [h i]; exact hlt)
      exact hi (by simp only at e; rw [← e]; exact tmGLP_self_mem N (X i))

end GI.Impl
