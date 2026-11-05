module

public import Workspace.Impl.LinObjectData
public import Workspace.Impl.LinObjectGroupImage

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

theorem linPermPresentation_det {n : ℕ} {as ns : List (Equiv.Perm (Fin n))}
    {M : Matrix (Fin as.length) (Fin as.length) ℤ} (hM : linPermPresentation ns as M) : M.det ≠ 0 := by
  obtain ⟨hN, hQ, hCert⟩ := hM
  exact hCert.1

theorem linObjectPresentation_mulVec_injective {d : ℕ} (M : Matrix (Fin d) (Fin d) ℤ)
    (hM : M.det ≠ 0) : Function.Injective M.mulVec := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_mulVec_eq_zero hM
  rw [Matrix.mulVec_sub, hxy, sub_self]

theorem linList_finRange_get {α : Type*} (xs : List α) :
    (List.finRange xs.length).map xs.get = xs := by
  rw [← List.ofFn_eq_map]
  exact List.ofFn_get xs

def linObjectDataOut {n : ℕ} {Q : Type*} [CommGroup Q]
    (as ns : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n)) (π : gens as →* Q) (out : Val) : Prop :=
  let refs := tmRiPcsO (gens as) Y
  ∃ (M : Matrix (Fin as.length) (Fin as.length) ℤ) (groups : List Val)
      (L : Fin refs.length → Matrix (Fin (as.length + (n ^ 2 + 1))) (Fin as.length) ℤ) (wn vn : Val),
    out = .list [.list [.list (refs.map tmGlObjsVal), .list groups], encIntMatrix M,
      linObjectBlockInput L, wn, vn] ∧ linPermPresentation ns as M ∧
      List.Forall₂ (fun S v => GroupValC n v (Aut (gens as) (tmGlMs S))) refs groups ∧
      (∀ i : Fin refs.length, ∃ C : Matrix (Fin (n ^ 2 + 1)) (Fin as.length) ℤ,
        L i = linRowStack M C ∧ (linRelations C).map (linObjectLiftCoord as π) =
          linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs (refs.get i)))) ∧
      (∀ i, Function.Injective (L i).mulVec) ∧
      TmGLQOut (linObjectBlockMatrix L) wn ∧ TmGLQOut (linObjectQuotientMatrix L) vn

theorem linObjectData_local_cert {n : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (refs : List (List (TmRiO n))) (bss : List (List (Equiv.Perm (Fin n))))
    (M : Matrix (Fin as.length) (Fin as.length) ℤ)
    (hB : List.Forall₂ (fun S bs => gens bs = Aut (gens as) (tmGlMs S) ∧ bs.length ≤ n ^ 2) refs bss)
    (Ms : List (Matrix (Fin (as.length + (n ^ 2 + 1))) (Fin as.length) ℤ))
    (hMs : List.Forall₂ (fun bs L => ∃ C : Matrix (Fin (n ^ 2 + 1)) (Fin as.length) ℤ,
      L = linRowStack M C ∧ (linRelations C).map (linObjectLiftCoord as π) =
        Submodule.span ℤ (Set.range fun i : Fin (1 :: bs).length =>
          Additive.ofMul (π (linIntoSubgroup (gens as) ((1 :: bs).get i))))) bss Ms) :
    List.Forall₂ (fun S L => ∃ C : Matrix (Fin (n ^ 2 + 1)) (Fin as.length) ℤ,
      L = linRowStack M C ∧ (linRelations C).map (linObjectLiftCoord as π) =
        linObjectGroupImage (gens as) π (Aut (gens as) (tmGlMs S))) refs Ms := by
  apply linForall₂_comp hB hMs
  intro S bs L hgroup hlocal
  obtain ⟨C, hLC, hC⟩ := hlocal
  refine ⟨C, hLC, ?_⟩
  have hBA : gens bs ≤ gens as := by rw [hgroup.1]; exact aut_le _ _
  rw [← hgroup.1, linObjectGroupImage_identityGenerators (gens as) π bs hBA]
  exact hC

end GI.Impl
