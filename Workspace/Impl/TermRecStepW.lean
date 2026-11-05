module

public import Workspace.Impl.TermRecBase

@[expose] public section

/-!
# T5, the weights and small facts of one level of the recursion

The step `tmRiStepE` keeps in its environment the input, the pieces, the table, the profiles
and the answer of the recursive call. Every one of these values has weight at most
`tmRiVs n M = 10⁸ (M + 1)² (n⁶ … + M + 1)` (`tmRiB`, `tmRiVs`). This file proves these weight
bounds, the fuel of the profile call (`tmRi_fuel`), and two monotonicity facts of the cost
bounds.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset GI.Algorithm GI.Assembly Equiv
open GI.Cited (Val encPerm encGroup gens SolvableCosetIntersection DerivedSubgroup Membership)

variable {n : ℕ}

/-- **The fuel of the profile call.** For `A = relDerived H N ℓ`, also
`relDerived H A ℓ ≤ A`: the derived series of `H/A` reaches `A` after `ℓ` steps. -/
theorem tmRi_fuel {G : Type} [Group G] {H N : Subgroup G} (hNH : N ≤ H) (ℓ : ℕ) :
    relDerived H (relDerived H N ℓ) ℓ ≤ relDerived H N ℓ :=
  relDerived_mono hNH le_rfl le_rfl ℓ le_rfl

/-- The trivial renaming. -/
theorem tmRi_toFin_refl (A : Set (Perm (Fin n))) : toFin (Equiv.refl (Fin n)) '' A = A := by
  have h : ∀ a : Perm (Fin n), toFin (Equiv.refl (Fin n)) a = a := fun a => by
    ext i; simp [toFin, Equiv.permCongrHom]
  ext a
  simp [h]

theorem tmRi_ansC_iff {u : Val} {A : Set (Perm (Fin n))} :
    AnsC (Equiv.refl (Fin n)) u A ↔ CosetC n u A := by
  rw [ansC_iff_cosetC, tmRi_toFin_refl]

/-! ### The weight bound -/

/-- `(M + 1) ((n + 1)⁶ + M + 1)`. -/
def tmRiB (n M : ℕ) : ℕ := (M + 1) * ((n + 1) ^ 6 + M + 1)

/-- The weight bound of every value of one level. -/
def tmRiVs (n M : ℕ) : ℕ := 10 ^ 8 * ((M + 1) * tmRiB n M)

theorem tmRiB_facts (n M : ℕ) :
    (n + 1) ^ 6 ≤ tmRiB n M ∧ M + 1 ≤ tmRiB n M ∧ M * (n + 1) ^ 6 ≤ tmRiB n M ∧
      M * M ≤ tmRiB n M ∧ tmRiB n M ≤ (M + 1) * tmRiB n M := by
  have e : tmRiB n M = M * (n + 1) ^ 6 + M * M + 2 * M + (n + 1) ^ 6 + 1 := by
    unfold tmRiB; ring
  refine ⟨by omega, by omega, by omega, by omega, Nat.le_mul_of_pos_left _ (by omega)⟩

/-- The weight of a list of at most `M` objects with colors below `2M`. -/
theorem tmRi_wt_side {M : ℕ} {X : List (TmRiO n)} (hX : X.length ≤ M) (hok : TmRiOK (2 * M) X) :
    (tmGlObjsVal X).wt ≤ 2020 * tmRiB n M := by
  have h1 := tmRi_wt_objs hok
  have h2 : X.length * (2 * (1000 * (n + 1) ^ 6 + 2 * (2 * M)) + 1) ≤
      M * (2 * (1000 * (n + 1) ^ 6 + 2 * (2 * M)) + 1) := Nat.mul_le_mul_right _ hX
  have e : M * (2 * (1000 * (n + 1) ^ 6 + 2 * (2 * M)) + 1) =
      2000 * (M * (n + 1) ^ 6) + 8 * (M * M) + M := by ring
  obtain ⟨f1, f2, f3, f4, -⟩ := tmRiB_facts n M
  omega

/-- The weight of a list of at most `2M` lists of weight at most `c`. -/
theorem tmRi_wt_lists {Ps : List (List (TmRiO n))} {M c : ℕ} (hl : Ps.length ≤ 2 * M)
    (h : ∀ S ∈ Ps, (tmGlObjsVal S).wt ≤ c) :
    (Val.list (Ps.map tmGlObjsVal)).wt ≤ 2 * M * (2 * c + 1) + 4 := by
  have h1 := tmRi_wt_list_le (Ps.map tmGlObjsVal) (c := c) (by
    intro v hv
    obtain ⟨S, hS, rfl⟩ := List.mem_map.1 hv
    exact h S hS)
  rw [List.length_map] at h1
  have := Nat.mul_le_mul_right (2 * c + 1) hl
  omega

/-- The weight of the table. -/
theorem tmRi_wt_tab {m M : ℕ} (hm : m ≤ 2 * M) :
    m * (2 * (m * (1400 * (n + 1) ^ 6 + 1) + 4) + 1) + 4 ≤ 12000 * ((M + 1) * tmRiB n M) := by
  have h1 : m * (2 * (m * (1400 * (n + 1) ^ 6 + 1) + 4) + 1) ≤
      (2 * M) * (2 * ((2 * M) * (1400 * (n + 1) ^ 6 + 1) + 4) + 1) :=
    Nat.mul_le_mul hm (by have := Nat.mul_le_mul_right (1400 * (n + 1) ^ 6 + 1) hm; omega)
  have e1 : (2 * M) * (2 * ((2 * M) * (1400 * (n + 1) ^ 6 + 1) + 4) + 1) =
      11200 * (M * (M * (n + 1) ^ 6)) + 8 * (M * M) + 18 * M := by ring
  have e2 : (M + 1) * tmRiB n M = M * (M * (n + 1) ^ 6) + M * (M * M) + 3 * (M * M) +
      2 * (M * (n + 1) ^ 6) + 3 * M + (n + 1) ^ 6 + 1 := by unfold tmRiB; ring
  omega

/-- The weight of the profiles of one side. -/
theorem tmRi_wt_profs {m M L : ℕ} (hm : m ≤ M) (hL : L ≤ 2 * M) :
    m * (2 * (2 * L + 700 * (n + 1) ^ 6) + 1) + 4 ≤ 2000 * tmRiB n M := by
  have h1 : m * (2 * (2 * L + 700 * (n + 1) ^ 6) + 1) ≤
      M * (2 * (2 * (2 * M) + 700 * (n + 1) ^ 6) + 1) := Nat.mul_le_mul hm (by omega)
  have e : M * (2 * (2 * (2 * M) + 700 * (n + 1) ^ 6) + 1) =
      8 * (M * M) + 1400 * (M * (n + 1) ^ 6) + M := by ring
  obtain ⟨f1, f2, f3, f4, -⟩ := tmRiB_facts n M
  omega

/-- The weight of a list of at most `2M` pieces, each a sublist of a side. -/
theorem tmRi_wt_pcsL {Ps : List (List (TmRiO n))} {M : ℕ} (hl : Ps.length ≤ 2 * M)
    (h : ∀ S ∈ Ps, (tmGlObjsVal S).wt ≤ 2020 * tmRiB n M) :
    (Val.list (Ps.map tmGlObjsVal)).wt ≤ 9000 * ((M + 1) * tmRiB n M) := by
  have h1 := tmRi_wt_lists hl h
  have e : 2 * M * (2 * (2020 * tmRiB n M) + 1) = 8080 * (M * tmRiB n M) + 2 * M := by ring
  have e2 : (M + 1) * tmRiB n M = M * tmRiB n M + tmRiB n M := by ring
  obtain ⟨f1, f2, -, -, -⟩ := tmRiB_facts n M
  omega

/-- A sublist of objects is lighter. -/
theorem tmRi_wt_objs_sub {S X : List (TmRiO n)} (h : S.Sublist X) :
    (tmGlObjsVal S).wt ≤ (tmGlObjsVal X).wt :=
  wt_list_sublist (h.map _)

theorem tmRiVs_facts (n M : ℕ) :
    10 ^ 8 * tmRiB n M ≤ tmRiVs n M ∧ 10 ^ 8 * (M + 1) ≤ tmRiVs n M ∧
      10 ^ 8 * (n + 1) ^ 6 ≤ tmRiVs n M ∧ tmRiVs n M = 10 ^ 8 * ((M + 1) * tmRiB n M) := by
  obtain ⟨f1, f2, -, -, f5⟩ := tmRiB_facts n M
  unfold tmRiVs
  omega

end GI.Impl
