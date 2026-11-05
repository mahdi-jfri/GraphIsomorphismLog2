module

public import Workspace.Impl.VsPFin

@[expose] public section

namespace GI.Impl

open GI.Cited GI.Proved Equiv

/-- A fold preserves any property preserved by each step. -/
theorem vsH_fold_all {α β : Type*} (f : α → β → α) (Q : α → Prop)
    (xs : List β) (h : ∀ a, Q a → ∀ b ∈ xs, Q (f a b)) (a : α) (ha : Q a) :
    Q (xs.foldl f a) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons b bs ih =>
    exact ih (fun a ha b hb => h a ha b (by simp [hb])) _ (h a ha b (by simp))

/-- Orbit insertion only adds the supplied element. -/
theorem vsH_ins_mem {n : ℕ} (kf : Perm (Fin n) → List ℕ) (cap : ℕ)
    (T : Set (Perm (Fin n))) (O : List (Perm (Fin n) × List ℕ))
    (hO : ∀ p ∈ O, p.1 ∈ T) (c : Perm (Fin n)) (hc : c ∈ T) :
    ∀ p ∈ vsPOIns kf cap O c, p.1 ∈ T := by
  unfold vsPOIns
  split_ifs
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hO p hp
    · simp only [List.mem_singleton] at hp
      simpa [hp] using hc
  · exact hO

/-- The orbit computation stays in a set closed under the listed conjugations. -/
theorem vsH_orbit_mem {n : ℕ} (kf : Perm (Fin n) → List ℕ) (cap : ℕ)
    (hs : List (Perm (Fin n))) (T : Set (Perm (Fin n)))
    (hT : ∀ h ∈ hs, ∀ z ∈ T, h * z * h⁻¹ ∈ T) (F : ℕ)
    (y : Perm (Fin n)) (hy : y ∈ T) : ∀ p ∈ vsPOrbit kf cap hs F y, p.1 ∈ T := by
  have hi : ∀ z ∈ T, ∀ O, (∀ p ∈ O, p.1 ∈ T) →
      ∀ p ∈ vsPOInner kf cap hs z O, p.1 ∈ T := by
    intro z hz O hO
    exact vsH_fold_all _ (fun L => ∀ p ∈ L, p.1 ∈ T) hs
      (fun a ha b hb => vsH_ins_mem kf cap T a ha _ (hT b hb z hz)) O hO
  have hp : ∀ O, (∀ p ∈ O, p.1 ∈ T) → ∀ p ∈ vsPOPass kf cap hs O, p.1 ∈ T := by
    intro O hO
    exact vsH_fold_all _ (fun L => ∀ p ∈ L, p.1 ∈ T) O
      (fun a ha b hb => hi b.1 (hO b hb) a ha) O hO
  induction F with
  | zero => simpa [vsPOrbit] using hy
  | succ F ih =>
    simpa only [vsPOrbit, Function.iterate_succ_apply'] using hp _ ih

/-- The selected basis stays in the same set as its orbit. -/
theorem vsH_dim_mem {I : VecStabInst} (ws' cs : List (List ℕ)) (Zp : List (List (List ℕ)))
    (gs : List (Perm (Fin I.n))) (cap : ℕ) (hs : List (Perm (Fin I.n)))
    (T : Set (Perm (Fin I.n))) (hT : ∀ h ∈ hs, ∀ z ∈ T, h * z * h⁻¹ ∈ T)
    (F r : ℕ) (y : Perm (Fin I.n)) (hy : y ∈ T) :
    ∀ b ∈ vsPDim I ws' cs Zp gs cap hs F r y, b ∈ T := by
  intro b hb
  obtain ⟨p, hp, rfl⟩ := vsPBasis_sub _ b hb
  exact vsH_orbit_mem _ cap hs T hT F y hy p hp

end GI.Impl
