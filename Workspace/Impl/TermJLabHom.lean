import Workspace.Impl.TermJLabMath

/-!
# The label and the top as homomorphisms on `N ≀ Sym(q)`

For `B` nonempty a pair is determined by its permutation (`tmJP_injective`), so the label
`tmJLab` and the top permutation are homomorphisms on `tmJW N` (`tmJLabHom`, `tmJTopHom`).
`tmJLabHom_tmJP`, `tmJTopHom_tmJP` compute them on a pair.
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Multicoset

variable {B : Type} [Nonempty B] {q : ℕ} {N : Subgroup (Perm B)} {A : Type*} [CommGroup A]
  (φ : N →* A)

/-- The pair of an element of `N ≀ Sym(q)`. -/
noncomputable def tmJPairOf (σ : tmJW (q := q) N) : (Fin q → Perm B) × Perm (Fin q) :=
  Classical.choose σ.2

omit [Nonempty B] in
theorem tmJPairOf_spec (σ : tmJW (q := q) N) :
    (∀ i, (tmJPairOf σ).1 i ∈ N) ∧ tmJP (tmJPairOf σ) = σ :=
  Classical.choose_spec σ.2

theorem tmJPairOf_eq {σ : tmJW (q := q) N} {p : (Fin q → Perm B) × Perm (Fin q)}
    (hp : tmJP p = σ) : tmJPairOf σ = p :=
  tmJP_injective ((tmJPairOf_spec σ).2.trans hp.symm)

theorem tmJPairOf_mul (σ τ : tmJW (q := q) N) :
    tmJPairOf (σ * τ) = (fun i => (tmJPairOf τ).1 i * (tmJPairOf σ).1 ((tmJPairOf τ).2 i),
      (tmJPairOf σ).2 * (tmJPairOf τ).2) := by
  apply tmJPairOf_eq
  rw [← tmJP_mul, (tmJPairOf_spec σ).2, (tmJPairOf_spec τ).2]
  rfl

/-- The label as a homomorphism on `N ≀ Sym(q)`. -/
noncomputable def tmJLabHom : tmJW (q := q) N →* A where
  toFun σ := tmJLab N φ (tmJPairOf σ).1
  map_one' := by
    rw [tmJPairOf_eq (p := (1, 1)) tmJP_one]
    exact tmJLab_one
  map_mul' σ τ := by
    rw [tmJPairOf_mul, tmJLab_mul _ (tmJPairOf_spec σ).1 (tmJPairOf_spec τ).1, mul_comm]

/-- The top permutation as a homomorphism on `N ≀ Sym(q)`. -/
noncomputable def tmJTopHom : tmJW (q := q) N →* Perm (Fin q) where
  toFun σ := (tmJPairOf σ).2
  map_one' := by rw [tmJPairOf_eq (p := (1, 1)) tmJP_one]
  map_mul' σ τ := by rw [tmJPairOf_mul]

theorem tmJLabHom_tmJP {p : (Fin q → Perm B) × Perm (Fin q)} (hp : ∀ i, p.1 i ∈ N) :
    tmJLabHom φ ⟨tmJP p, p, hp, rfl⟩ = tmJLab N φ p.1 := by
  change tmJLab N φ (tmJPairOf _).1 = _
  rw [tmJPairOf_eq rfl]

theorem tmJTopHom_tmJP {p : (Fin q → Perm B) × Perm (Fin q)} (hp : ∀ i, p.1 i ∈ N) :
    tmJTopHom (N := N) ⟨tmJP p, p, hp, rfl⟩ = p.2 := by
  change (tmJPairOf _).2 = _
  rw [tmJPairOf_eq rfl]

end GI.Impl
