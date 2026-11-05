module

public import Workspace.Impl.LinObjectLiftCost

@[expose] public section

/-! The observable answer of the common-translation lift. Failure rules
out every common abelian translation; success supplies an actual cover
permutation whose image cancels all local residues. -/
namespace GI.Impl
open GI.Cited GI.Lang

noncomputable def linObjectLiftCoord {n : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q) :
    (Fin as.length → ℤ) →ₗ[ℤ] Additive Q :=
  linCoordMap (fun i => π (linIntoSubgroup (gens as) (as.get i)))

def linObjectLiftAnswer {n p : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (B : Fin p → Submodule ℤ (Additive Q)) (w : Fin (as.length * p) → ℤ) (out : Val) : Prop :=
  (out = .nat 0 ∧ ¬ ∃ a : Additive Q, ∀ i,
    linObjectLiftCoord as π (linObjectUnflatten p as.length w i) + a ∈ B i) ∨
  ∃ a : Equiv.Perm (Fin n), ∃ ha : a ∈ gens as, out = .list [.nat 1, encPerm a] ∧
    ∀ i, linObjectLiftCoord as π (linObjectUnflatten p as.length w i) +
      Additive.ofMul (π ⟨a, ha⟩) ∈ B i

theorem linObjectLift_row_answer {n p r : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (B : Fin p → Submodule ℤ (Additive Q))
    (L : Fin p → Matrix (Fin r) (Fin as.length) ℤ)
    (hL : ∀ i, LinearMap.ker ((B i).mkQ.comp (linObjectLiftCoord as π)) = linRelations (L i))
    (w : Fin (as.length * p) → ℤ) (z : Fin (r * p + as.length) → ℤ)
    (hz : Matrix.vecMul z (linObjectQuotientMatrix L) = -w) :
    let common := fun j => z (Fin.natAdd (r * p) j)
    linObjectLiftAnswer as π B w
      (.list [.nat 1, encPerm (linGroupWord (fun i => as.get i) common)]) := by
  let common := fun j : Fin as.length => z (Fin.natAdd (r * p) j)
  refine Or.inr ⟨_, linPermWord_mem as common, rfl, ?_⟩
  intro i
  rw [← linPermWord_coordinates as π common]
  exact linObjectCorrection_rows B (linObjectLiftCoord as π) L hL w z hz i

theorem linObjectLift_failure {n p r : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (B : Fin p → Submodule ℤ (Additive Q)) (hf : Function.Surjective (linObjectLiftCoord as π))
    (L : Fin p → Matrix (Fin r) (Fin as.length) ℤ)
    (hL : ∀ i, LinearMap.ker ((B i).mkQ.comp (linObjectLiftCoord as π)) = linRelations (L i))
    (w : Fin (as.length * p) → ℤ)
    (hno : ¬ ∃ z, Matrix.vecMul z (linObjectQuotientMatrix L) = -w) :
    linObjectLiftAnswer as π B w (.nat 0) :=
  Or.inl ⟨rfl, fun ha => hno ((linObjectLiftable_iff B (linObjectLiftCoord as π) hf L hL w).mpr ha)⟩

theorem linObjectLift_empty {n p : ℕ} {Q : Type*} [CommGroup Q]
    (as : List (Equiv.Perm (Fin n))) (π : gens as →* Q)
    (B : Fin p → Submodule ℤ (Additive Q)) (w : Fin (as.length * p) → ℤ)
    (hzero : as.length * p = 0) : linObjectLiftAnswer as π B w
      (.list [.nat 1, encPerm (1 : Equiv.Perm (Fin n))]) := by
  refine Or.inr ⟨1, (gens as).one_mem, rfl, ?_⟩
  intro i
  rcases Nat.mul_eq_zero.mp hzero with ht | hp
  · have hw : linObjectUnflatten p as.length w i = 0 := by
      ext j
      have := j.isLt
      omega
    rw [hw, map_zero]
    change (0 : Additive Q) + Additive.ofMul (π 1) ∈ B i
    rw [map_one]
    change (0 : Additive Q) + 0 ∈ B i
    simpa only [add_zero] using (B i).zero_mem
  · have := i.isLt
    omega

end GI.Impl
