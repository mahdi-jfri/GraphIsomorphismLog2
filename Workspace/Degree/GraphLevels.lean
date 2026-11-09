module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Layers and balls

Section 9.1 of the paper, with both graphs relabeled so that their layers are the same sets. Fix a
level function `ℓ` on the vertices.

* `HasLevels X ℓ R`: the graph `X` has levels `ℓ` up to `R`.
* `Ball ℓ r X Y`: the set `C_r(X, Y)`, the permutations that keep levels, fix all points above level
  `r`, and are isomorphisms of the balls of radius `r`.
* `ballGroup ℓ r X`: the group `A_r = C_r(X, X)`.
* `Ball.inv_mul`, `Ball.mul`, `Ball.pull`, `Ball.cut`: the facts on balls of Section 9.1.
-/

@[expose] public section

namespace GI.Degree

open Equiv

variable {V : Type*}

/-- The graph `X` has levels `ℓ` up to `R`. -/
structure HasLevels (X : SimpleGraph V) (ℓ : V → ℕ) (R : ℕ) : Prop where
  /-- The root is the only point of level `0`. -/
  root : ∃ o, ∀ u, ℓ u = 0 ↔ u = o
  /-- An edge goes up at most one level. -/
  step : ∀ u v, X.Adj u v → ℓ u ≤ R → ℓ v ≤ ℓ u + 1
  /-- A point of positive level has a neighbour one level below. -/
  back : ∀ w, 1 ≤ ℓ w → ℓ w ≤ R → ∃ u, X.Adj u w ∧ ℓ u + 1 = ℓ w

/-- The graph `Y^T`: `u, v` are adjacent if `T u, T v` are adjacent in `Y`. -/
def pull (T : Perm V) (Y : SimpleGraph V) : SimpleGraph V where
  Adj u v := Y.Adj (T u) (T v)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => Y.loopless.irrefl _ h⟩

@[simp] theorem pull_adj {T : Perm V} {Y : SimpleGraph V} {u v : V} :
    (pull T Y).Adj u v ↔ Y.Adj (T u) (T v) := Iff.rfl

/-- `C_r(X, Y)`. -/
def Ball (ℓ : V → ℕ) (r : ℕ) (X Y : SimpleGraph V) : Set (Perm V) :=
  {g | (∀ u, ℓ (g u) = ℓ u) ∧ (∀ u, r < ℓ u → g u = u) ∧
    ∀ u v, ℓ u ≤ r → ℓ v ≤ r → (X.Adj u v ↔ Y.Adj (g u) (g v))}

variable {ℓ : V → ℕ} {r s : ℕ} {X Y : SimpleGraph V}

theorem one_mem_ball_self : (1 : Perm V) ∈ Ball ℓ r X X :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => Iff.rfl⟩

/-- `g ∈ C_r(X, Y)` and `f ∈ A_r` give `g f ∈ C_r(X, Y)`. -/
theorem Ball.mul {g f : Perm V} (hg : g ∈ Ball ℓ r X Y) (hf : f ∈ Ball ℓ r X X) :
    g * f ∈ Ball ℓ r X Y := by
  obtain ⟨g1, g2, g3⟩ := hg
  obtain ⟨f1, f2, f3⟩ := hf
  refine ⟨fun u => ?_, fun u hu => ?_, fun u v hu hv => ?_⟩
  · simp [Perm.mul_apply, g1, f1]
  · simp [Perm.mul_apply, f2 u hu, g2 u hu]
  · rw [f3 u v hu hv, Perm.mul_apply, Perm.mul_apply]
    exact g3 _ _ (by rwa [f1]) (by rwa [f1])

/-- The inverse of an element of `C_r(X, Y)` lies in `C_r(Y, X)`. -/
theorem Ball.inv {g : Perm V} (hg : g ∈ Ball ℓ r X Y) : g⁻¹ ∈ Ball ℓ r Y X := by
  obtain ⟨g1, g2, g3⟩ := hg
  have hl : ∀ u, ℓ (g⁻¹ u) = ℓ u := fun u => by
    have := g1 (g⁻¹ u)
    simpa using this.symm
  refine ⟨hl, fun u hu => ?_, fun u v hu hv => ?_⟩
  · have := g2 u hu
    exact (Perm.inv_eq_iff_eq.2 this.symm)
  · have := g3 (g⁻¹ u) (g⁻¹ v) (by rwa [hl]) (by rwa [hl])
    simpa using this.symm

/-- The group `A_r = C_r(X, X)`. -/
def ballGroup (ℓ : V → ℕ) (r : ℕ) (X : SimpleGraph V) : Subgroup (Perm V) where
  carrier := Ball ℓ r X X
  mul_mem' := Ball.mul
  one_mem' := one_mem_ball_self
  inv_mem' := Ball.inv

theorem mem_ballGroup {g : Perm V} : g ∈ ballGroup ℓ r X ↔ g ∈ Ball ℓ r X X := Iff.rfl

/-- Two elements of `C_r(X, Y)` differ by an element of `A_r`. -/
theorem Ball.inv_mul {g h : Perm V} (hg : g ∈ Ball ℓ r X Y) (hh : h ∈ Ball ℓ r X Y) :
    g⁻¹ * h ∈ ballGroup ℓ r X := by
  obtain ⟨g1, g2, g3⟩ := hg
  obtain ⟨h1, h2, h3⟩ := hh
  obtain ⟨i1, i2, i3⟩ := Ball.inv (⟨g1, g2, g3⟩ : g ∈ Ball ℓ r X Y)
  refine ⟨fun u => ?_, fun u hu => ?_, fun u v hu hv => ?_⟩
  · rw [Perm.mul_apply, i1, h1]
  · rw [Perm.mul_apply, h2 u hu, i2 u hu]
  · rw [h3 u v hu hv, Perm.mul_apply, Perm.mul_apply]
    exact i3 _ _ (by rwa [h1]) (by rwa [h1])

/-- **Relabeling.** Let `T` keep levels. Then `g ∈ C_s(X, Y^T)` if and only if `T g ∈ C_s(X, Y)`,
when `T` fixes all points above level `s`. -/
theorem mem_ball_pull {T g : Perm V} (hT : ∀ u, ℓ (T u) = ℓ u) (hT' : ∀ u, s < ℓ u → T u = u)
    : g ∈ Ball ℓ s X (pull T Y) ↔ T * g ∈ Ball ℓ s X Y := by
  constructor
  · rintro ⟨g1, g2, g3⟩
    refine ⟨fun u => by simp [Perm.mul_apply, hT, g1], fun u hu => ?_, fun u v hu hv => ?_⟩
    · simp [Perm.mul_apply, g2 u hu, hT' u hu]
    · simpa using g3 u v hu hv
  · rintro ⟨g1, g2, g3⟩
    refine ⟨fun u => ?_, fun u hu => ?_, fun u v hu hv => ?_⟩
    · simpa [Perm.mul_apply, hT] using g1 u
    · have := g2 u hu
      rw [Perm.mul_apply] at this
      exact T.injective (this.trans (hT' u hu).symm)
    · simpa using g3 u v hu hv

theorem one_mem_ball_pull {T : Perm V} (h : T ∈ Ball ℓ r X Y) : (1 : Perm V) ∈ Ball ℓ r X (pull T Y) :=
  (mem_ball_pull h.1 h.2.1).2 (by simpa using h)

/-- The cut of `g`: `g` on levels at most `r`, the identity above. -/
def ballCut (ℓ : V → ℕ) (r : ℕ) (g : Perm V) (hg : ∀ u, ℓ (g u) = ℓ u) : Perm V :=
  g.subtypePerm (p := fun u => ℓ u ≤ r) (fun u => by simp only [hg]) |>.ofSubtype

open Classical in
theorem ballCut_apply_of_le {g : Perm V} (hg : ∀ u, ℓ (g u) = ℓ u) {u : V} (hu : ℓ u ≤ r) :
    ballCut ℓ r g hg u = g u := by
  exact Perm.ofSubtype_apply_of_mem (p := fun u => ℓ u ≤ r) _ hu

open Classical in
theorem ballCut_apply_of_lt {g : Perm V} (hg : ∀ u, ℓ (g u) = ℓ u) {u : V} (hu : r < ℓ u) :
    ballCut ℓ r g hg u = u := by
  exact Perm.ofSubtype_apply_of_not_mem (p := fun u => ℓ u ≤ r) _ (by simpa using hu)

/-- **Restriction to a smaller ball** (fact (i) of Section 9.1). -/
theorem Ball.cut {g : Perm V} (hg : g ∈ Ball ℓ (r + 1) X Y) :
    ballCut ℓ r g hg.1 ∈ Ball ℓ r X Y := by
  obtain ⟨g1, g2, g3⟩ := hg
  have hl : ∀ u, ℓ (ballCut ℓ r g g1 u) = ℓ u := fun u => by
    rcases le_or_gt (ℓ u) r with h | h
    · rw [ballCut_apply_of_le g1 h, g1]
    · rw [ballCut_apply_of_lt g1 h]
  refine ⟨hl, fun u hu => ballCut_apply_of_lt g1 hu, fun u v hu hv => ?_⟩
  rw [ballCut_apply_of_le g1 hu, ballCut_apply_of_le g1 hv]
  exact g3 u v (by omega) (by omega)

/-- If `C_{r+1}` is empty for a pair, so is `C_s` for each `s ≥ r + 1`. -/
theorem Ball.down {g : Perm V} (hsr : r ≤ s) (hg : g ∈ Ball ℓ s X Y) :
    ∃ g' : Perm V, g' ∈ Ball ℓ r X Y := by
  induction s, hsr using Nat.le_induction generalizing g with
  | base => exact ⟨g, hg⟩
  | succ s _ ih => exact ih (Ball.cut hg)

end GI.Degree
