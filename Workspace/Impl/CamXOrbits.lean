module

public import Workspace.Impl.CamXParams
public import Workspace.AlternatingSubsetTransitive

@[expose] public section

/-!
# The orbits of the factors of the socle

Read through `e`, the factor `camProd e {i}` moves only coordinate `i`, and there it is the
alternating group on `k`-sets, which is transitive for `m ≥ 3`. So its orbit of a point is the
set of points that agree with it outside coordinate `i` (`camX_orbit_factor`). Likewise the
product of the other factors has as orbits the fibers of coordinate `i` (`camX_orbit_others`).
-/

namespace GI.Impl

open Equiv GI.Cited

variable {n m k r : ℕ} {e : Fin n ≃ (Fin r → {A : Finset (Fin m) // A.card = k})}

/-- Membership in the coordinate product: alternating in `S`, trivial outside. -/
theorem camX_mem_pi {S : Finset (Fin r)} {h : Fin r → Perm (Fin m)} :
    h ∈ Subgroup.pi Set.univ (fun i => if i ∈ S then alternatingGroup (Fin m) else ⊥) ↔
      ∀ i, (i ∈ S → h i ∈ alternatingGroup (Fin m)) ∧ (i ∉ S → h i = 1) := by
  refine ⟨fun hh i => ?_, fun hh i _ => ?_⟩
  · have := hh i trivial
    by_cases hi : i ∈ S
    · simp only [hi, if_true] at this
      exact ⟨fun _ => this, fun h' => absurd hi h'⟩
    · simp only [hi, if_false] at this
      exact ⟨fun h' => absurd h' hi, fun _ => this⟩
  · by_cases hi : i ∈ S
    · simp only [hi, if_true]
      exact (hh i).1 hi
    · simp only [hi, if_false]
      exact (hh i).2 hi

theorem camX_mem_prod {S : Finset (Fin r)} {g : Perm (Fin n)} :
    g ∈ camProd e S ↔ ∃ h : Fin r → Perm (Fin m),
      (∀ i, (i ∈ S → h i ∈ alternatingGroup (Fin m)) ∧ (i ∉ S → h i = 1)) ∧ camHom e h = g := by
  unfold camProd
  rw [Subgroup.mem_map]
  simp only [camX_mem_pi]

/-- `Alt(m)` is transitive on `k`-sets for `m ≥ 3`. -/
theorem camX_exists_alt (hm : 3 ≤ m) (A B : {A : Finset (Fin m) // A.card = k}) :
    ∃ a ∈ alternatingGroup (Fin m), kSetPerm a A = B := by
  obtain ⟨p, hp⟩ := GI.AlternatingActions.exists_alternating_finset_eq
    (by simpa using hm) A.1 B.1 (A.2.trans B.2.symm)
  refine ⟨p, p.2, Subtype.ext ?_⟩
  rw [cam_kSetPerm_apply, ← hp, Finset.map_eq_image, Finset.smul_finset_def]
  rfl

/-- The orbits of `camProd e S` on points: a point moves exactly in the coordinates of `S`. -/
private theorem camX_orbit_prod (hm : 3 ≤ m) (S : Finset (Fin r)) (x y : Fin n) :
    y ∈ MulAction.orbit (camProd e S) x ↔ ∀ j, j ∉ S → e y j = e x j := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩ j hj
    obtain ⟨h, hh, rfl⟩ := camX_mem_prod.mp hg
    change e (camHom e h x) j = e x j
    rw [camHom_apply]
    change kSetPerm (h j) (e x j) = e x j
    rw [(hh j).2 hj, cam_kSetPerm_one]
    rfl
  · intro hy
    choose a ha hax using fun j => camX_exists_alt hm (e x j) (e y j)
    classical
    let h : Fin r → Perm (Fin m) := fun j => if j ∈ S then a j else 1
    have hmem : camHom e h ∈ camProd e S := camX_mem_prod.mpr ⟨h, fun j =>
      ⟨fun hj => by simp only [h, hj, if_true]; exact ha j,
       fun hj => by simp only [h, hj, if_false]⟩, rfl⟩
    refine ⟨⟨camHom e h, hmem⟩, ?_⟩
    change camHom e h x = y
    apply e.injective
    rw [camHom_apply]
    funext j
    by_cases hj : j ∈ S
    · simp only [h, hj, if_true]
      exact hax j
    · simp only [h, hj, if_false, cam_kSetPerm_one]
      exact (hy j hj).symm

set_option linter.unusedVariables false in
/-- The hypothesis `k ≤ m` is not needed; it is kept to match the planned statement. -/
theorem camX_orbit_factor (hm : 3 ≤ m) (hkm : k ≤ m) (i : Fin r) (x₀ y : Fin n) :
    y ∈ MulAction.orbit (camProd e {i}) x₀ ↔ ∀ j, j ≠ i → e y j = e x₀ j := by
  rw [camX_orbit_prod hm]
  simp only [Finset.mem_singleton]

set_option linter.unusedVariables false in
theorem camX_orbit_others (hm : 3 ≤ m) (hkm : k ≤ m) (i : Fin r) (x y : Fin n) :
    y ∈ MulAction.orbit (camProd e {i}ᶜ) x ↔ e y i = e x i := by
  rw [camX_orbit_prod hm]
  simp only [Finset.mem_compl, Finset.mem_singleton, not_not]
  exact ⟨fun h => h i rfl, fun h j hj => hj ▸ h⟩

end GI.Impl
