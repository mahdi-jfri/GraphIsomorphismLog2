module

public import Workspace.Impl.CamDefs

@[expose] public section

/-!
# Renumbering the coordinates

The program finds the simple factors in some order `j ↦ τ j`. Reading the coordinates in that
order is the identification `camReindex e τ`, with `(camReindex e τ x) j = e x (τ j)`. It keeps the
Maróti structure (`cam_maroti_reindex`), and its factors are those of `e`, renumbered
(`camProd_reindex`).
-/

namespace GI.Impl

open Equiv GI.Cited

variable {n m k r : ℕ}

/-- The coordinates of `e`, read in the order `τ`. -/
def camReindex (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})) (τ : Perm (Fin r)) :
    Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k}) :=
  e.trans
    { toFun := fun f j => f (τ j)
      invFun := fun f i => f (τ.symm i)
      left_inv := fun f => by funext i; simp
      right_inv := fun f => by funext j; simp }

@[simp] theorem camReindex_apply (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k}))
    (τ : Perm (Fin r)) (x : Fin n) (j : Fin r) : camReindex e τ x j = e x (τ j) := rfl

theorem camHom_reindex (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k}))
    (τ : Perm (Fin r)) (h : Fin r → Perm (Fin m)) :
    camHom (camReindex e τ) h = camHom e fun i => h (τ.symm i) := by
  refine Equiv.ext fun x => (camReindex e τ).injective ?_
  rw [camHom_apply]
  funext j
  simp only [camReindex_apply]
  rw [camHom_apply]
  simp

/-- **Renumbering keeps the Maróti structure.** -/
theorem cam_maroti_reindex {G : Subgroup (Perm (Fin n))}
    {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})} (τ : Perm (Fin r))
    (hM : MarotiStructure G e) : MarotiStructure G (camReindex e τ) := by
  refine ⟨fun g hg => ?_, fun h hh => ?_⟩
  · obtain ⟨σ, h, hgh⟩ := hM.1 g hg
    refine ⟨τ⁻¹ * σ * τ, fun j => h (τ j), fun x => ?_⟩
    funext j
    simp [hgh x]
  · have := hM.2 (fun i => h (τ.symm i)) fun i => hh _
    have e1 : (camReindex e τ).trans
        ((Equiv.piCongrRight fun i => kSetPerm (h i)).trans (camReindex e τ).symm) =
        camHom (camReindex e τ) h := rfl
    have e2 : e.trans ((Equiv.piCongrRight fun i => kSetPerm (h (τ.symm i))).trans e.symm) =
        camHom e (fun i => h (τ.symm i)) := rfl
    rw [e1, camHom_reindex, ← e2]
    exact this

/-- **The factors of the renumbered identification.** -/
theorem camProd_reindex (e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k}))
    (τ : Perm (Fin r)) (S : Finset (Fin r)) :
    camProd (camReindex e τ) S = camProd e (S.map τ.toEmbedding) := by
  ext g
  simp only [camProd, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨fun i => h (τ.symm i), ?_, (camHom_reindex e τ h).symm⟩
    rw [Subgroup.mem_pi] at hh ⊢
    intro i _
    have := hh (τ.symm i) (Set.mem_univ _)
    simpa [Finset.mem_map_equiv] using this
  · rintro ⟨h, hh, rfl⟩
    refine ⟨fun j => h (τ j), ?_, ?_⟩
    · rw [Subgroup.mem_pi] at hh ⊢
      intro j _
      have := hh (τ j) (Set.mem_univ _)
      simpa [Finset.mem_map_equiv] using this
    · rw [camHom_reindex]
      simp

end GI.Impl
