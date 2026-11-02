import Workspace.Impl.TermGlueLabPFind
import Workspace.Impl.TermCosetFirst
import Workspace.Impl.TermStep
import Workspace.Impl.TermGlueLabTorsor

/-!
# Representatives of the types and the labels of `x`

Step 2 of the label program. Proof of Theorem A.23: "fix one representative
`z_a` of every type `a` of `x`, and for every row `z_i` of type `a` an element `n_i ∈ N` with
`z_a^{n_i} = z_i`. The total `s(z) = Σ_i [n_i]` is well defined."

The representative of a type is its **first row**: `x_j` with `j` least among the rows of that
type (`tmGLPRep`, `TmGLPFirst`). The program finds it from the `N`-test table `us`, whose entry
`(x_j, x_i)` is `Iso_N(x_j, x_i)`. For a row `x_i` the first `j` with a nonempty entry is the
first row of its type, and the stored coset gives `n_i` (`tmGLPXLab_spec`). For any other row
`z` the search of `TermGlueLabPFind` returns the same kind of data.

`tmGLP_lab_of_first` turns such data into the label `s(z)`.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens)

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω]

/-! ### The first row of a type -/

/-- `j` is the first row of `x` whose `N`-orbit holds `z`. -/
def TmGLPFirst (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω) (z : Ω) (j : Fin q) :
    Prop :=
  z ∈ orbitN N (X j) ∧ ∀ j' : Fin q, j'.1 < j.1 → z ∉ orbitN N (X j')

theorem tmGLP_first_unique {N : Subgroup (Perm (Fin n))} {q : ℕ} {X : Fin q → Ω} {z : Ω}
    {j j' : Fin q} (h : TmGLPFirst N X z j) (h' : TmGLPFirst N X z j') : j = j' := by
  rcases lt_trichotomy j.1 j'.1 with hl | he | hl
  · exact absurd h.1 (h'.2 j hl)
  · exact Fin.ext he
  · exact absurd h'.1 (h.2 j' hl)

theorem tmGLP_first_exists {N : Subgroup (Perm (Fin n))} {q : ℕ} {X : Fin q → Ω} {z : Ω}
    {j : Fin q} (hz : z ∈ orbitN N (X j)) : ∃ j', TmGLPFirst N X z j' := by
  classical
  have hex : ∃ k, ∃ hk : k < q, z ∈ orbitN N (X ⟨k, hk⟩) := ⟨j.1, j.2, hz⟩
  refine ⟨⟨Nat.find hex, (Nat.find_spec hex).1⟩, (Nat.find_spec hex).2, fun j' hj' hj'z => ?_⟩
  exact Nat.find_min hex hj' ⟨j'.2, hj'z⟩

theorem tmGLP_orbit_eq {N : Subgroup (Perm (Fin n))} {Y z : Ω} (hz : z ∈ orbitN N Y) :
    orbitN N z = orbitN N Y := by
  obtain ⟨c, hc, rfl⟩ := hz
  exact orbitN_kernel hc

theorem tmGLP_self_mem (N : Subgroup (Perm (Fin n))) (z : Ω) : z ∈ orbitN N z :=
  ⟨1, N.one_mem, act_one z⟩

/-- `a` is an `N`-type whose first row is `j`. -/
def TmGLPFirstT (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω) (a : Set Ω) (j : Fin q) :
    Prop :=
  a = orbitN N (X j) ∧ ∀ j' : Fin q, j'.1 < j.1 → a ≠ orbitN N (X j')

open Classical in
/-- **The representatives**: the first row of each type (`X j0` off the types). -/
noncomputable def tmGLPRep (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω) (j0 : Fin q)
    (a : Set Ω) : Ω :=
  if h : ∃ j, TmGLPFirstT N X a j then X h.choose else X j0

theorem tmGLP_firstT_of {N : Subgroup (Perm (Fin n))} {q : ℕ} {X : Fin q → Ω} {z : Ω}
    {j : Fin q} (h : TmGLPFirst N X z j) : TmGLPFirstT N X (orbitN N z) j := by
  refine ⟨tmGLP_orbit_eq h.1, fun j' hj' he => h.2 j' hj' ?_⟩
  rw [← he]; exact tmGLP_self_mem N z

/-- **The representative of the type of `z` is the first row of that type.** -/
theorem tmGLP_rep_eq {N : Subgroup (Perm (Fin n))} {q : ℕ} {X : Fin q → Ω} (j0 : Fin q)
    {z : Ω} {j : Fin q} (h : TmGLPFirst N X z j) : tmGLPRep N X j0 (orbitN N z) = X j := by
  classical
  have hT := tmGLP_firstT_of h
  have hex : ∃ j, TmGLPFirstT N X (orbitN N z) j := ⟨j, hT⟩
  unfold tmGLPRep
  rw [dif_pos hex]
  congr 1
  have hc := hex.choose_spec
  rcases lt_trichotomy hex.choose.1 j.1 with hl | he | hl
  · exact absurd hc.1 (hT.2 _ hl)
  · exact Fin.ext he
  · exact absurd hT.1 (hc.2 _ hl)

/-- The representatives are rows of their types. -/
theorem tmGLP_rep_ok (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω) (j0 : Fin q) :
    TmGLRep N X (tmGLPRep N X j0) := by
  intro i
  obtain ⟨j, hj⟩ := tmGLP_first_exists (tmGLP_self_mem N (X i))
  rw [tmGLP_rep_eq j0 hj]
  rw [tmGLP_orbit_eq hj.1]
  exact tmGLP_self_mem N (X j)

/-- **The label from first rows.** If every row `z_i` is `x_{j_i}^{n_i}` with `n_i ∈ N` and
`j_i` the first row of the type of `z_i`, then `s(z) = Π_i [n_i]`. -/
theorem tmGLP_lab_of_first {A : Type*} [CommGroup A] {N : Subgroup (Perm (Fin n))}
    {φ : N →* A} {q : ℕ} {X : Fin q → Ω} (j0 : Fin q) {z : Fin q → Ω}
    (hz : types N z = types N X) {J : Fin q → Fin q} {a : Fin q → Perm (Fin n)}
    (ha : ∀ i, a i ∈ N) (hJ : ∀ i, TmGLPFirst N X (z i) (J i)) (haz : ∀ i, X (J i) ↼ a i = z i) :
    tmGLLab N φ X (tmGLPRep N X j0) z = ∏ i, tmGLc N φ X (a i) :=
  tmGLLab_eq (tmGLP_rep_ok N X j0) hz ha fun i => by rw [tmGLP_rep_eq j0 (hJ i)]; exact haz i

/-- The search of `TermGlueLabPFind` gives first rows. -/
theorem tmGLP_first_of_find {N : Subgroup (Perm (Fin n))} {q : ℕ} {X : Fin q → Ω} {Z : Ω}
    {j : Fin q} {x : Perm (Fin n)} (hx : x ∈ N) (hxZ : X j ↼ x = Z)
    (hmin : ∀ j' : Fin q, j'.1 < j.1 → ∀ x ∈ N, X j' ↼ x ≠ Z) : TmGLPFirst N X Z j :=
  ⟨⟨x, hx, hxZ⟩, fun j' hj' ⟨y, hy, hyZ⟩ => hmin j' hj' y hy hyZ⟩

end GI.Impl
