import Workspace.Impl.AggStructCase
import Workspace.Lang.Lib.OrbitMath

/-!
# The case of a branch from orbit labels: the list form

The case test of the items (`aggCase` of `π(F_x)`, Section A.3) is computed by a program from
generators `gs` of `H`: orbit labels `lab` (`orbits_spec`:
`lab x = lab y` exactly when `y` is in the orbit of `x`), the orbit size of `b` as the number of
points with the label of `b`, the dominant points `D` (orbit size above `q/2`) as an increasing
list, the count of points in nontrivial orbits, and, if `D` is not empty, the giant test
`|D|! · |H_(D)| ≤ 2 |H|` (one pointwise stabilizer and two group orders, `st_aggCase_eq`).

This file gives the list form of that computation and proves it equal to `aggCase H`
(`ac_aggCase_eq`). The stabilizer of the list `D` is that of `(domSet H).toList`, since a
pointwise stabilizer depends only on the members of the list (`ac_pstab_congr`).
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm

variable {q : ℕ}

/-- **A pointwise stabilizer depends only on the members of the list.** -/
theorem ac_pstab_congr (H : Subgroup (Perm (Fin q))) {l l' : List (Fin q)}
    (h : ∀ i, i ∈ l ↔ i ∈ l') : GI.Cited.pointwiseStab H l = GI.Cited.pointwiseStab H l' := by
  ext g
  change (g ∈ H ∧ ∀ i ∈ l, g i = i) ↔ (g ∈ H ∧ ∀ i ∈ l', g i = i)
  simp only [h]

/-- The orbit size of `b` from the labels: the number of points with the label of `b`. -/
def acSize (lab : Fin q → ℕ) (b : Fin q) : ℕ := ((List.finRange q).map lab).count (lab b)

/-- The dominant points, in increasing order. -/
def acDom (lab : Fin q → ℕ) : List (Fin q) :=
  (List.finRange q).filter fun b => q < 2 * acSize lab b

/-- The number of points in nontrivial orbits. -/
def acSupp (lab : Fin q → ℕ) : ℕ :=
  ((List.finRange q).filter fun b => acSize lab b ≠ 1).length

/-- The case code: `0` Case 1, `1` Case 2a, `2` Case 2b, `3` Case 3. -/
def AggCase.code : AggCase → ℕ
  | .one => 0
  | .twoA => 1
  | .twoB => 2
  | .three => 3

/-- **The case from labels and two group orders**: `oH = |H|`, `oD = |H_(D)|`. -/
def acCaseL (lab : Fin q → ℕ) (oH oD : ℕ) : AggCase :=
  if acDom lab ≠ [] then (if (acDom lab).length.factorial * oD ≤ 2 * oH then .twoA else .twoB)
  else if q ≤ 2 * acSupp lab then .one else .three

theorem ac_card_filter (p : Fin q → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ((List.finRange q).filter fun b => decide (p b)).length := by
  have : Finset.univ.filter p = ((List.finRange q).filter fun b => decide (p b)).toFinset := by
    ext; simp
  rw [this, List.toFinset_card_of_nodup ((List.nodup_finRange q).filter _)]

variable {gs : List (Perm (Fin q))} {H : Subgroup (Perm (Fin q))} {lab : Fin q → ℕ}

/-- **The orbit size from the labels.** -/
theorem ac_lorb_card (hH : GI.Cited.gens gs = H)
    (hlab : ∀ x y, lab x = lab y ↔ y ∈ genOrbit gs x) (b : Fin q) :
    (lorb H b).card = acSize lab b := by
  classical
  have h1 : lorb H b = Finset.univ.filter fun y => lab y = lab b := by
    ext y
    simp only [lorb, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [eq_comm, hlab, mem_genOrbit]
    change (∃ h ∈ H, h b = y) ↔ ∃ g ∈ GI.Cited.gens gs, g b = y
    rw [hH]
  rw [h1, ac_card_filter, acSize, List.count, List.countP_map, List.countP_eq_length_filter]
  congr 1

theorem ac_domSet (hH : GI.Cited.gens gs = H)
    (hlab : ∀ x y, lab x = lab y ↔ y ∈ genOrbit gs x) :
    domSet H = (acDom lab).toFinset := by
  ext b
  simp [mem_domSet, acDom, ac_lorb_card hH hlab]

theorem ac_suppSet_card (hH : GI.Cited.gens gs = H)
    (hlab : ∀ x y, lab x = lab y ↔ y ∈ genOrbit gs x) :
    (suppSet H).card = acSupp lab := by
  classical
  have : suppSet H = Finset.univ.filter fun b => acSize lab b ≠ 1 := by
    ext b; simp [mem_suppSet, ac_lorb_card hH hlab]
  rw [this, ac_card_filter, acSupp]

/-- **The list form of the case is the case.** -/
theorem ac_aggCase_eq (hH : GI.Cited.gens gs = H)
    (hlab : ∀ x y, lab x = lab y ↔ y ∈ genOrbit gs x) :
    aggCase H = acCaseL lab (Nat.card H) (Nat.card (GI.Cited.pointwiseStab H (acDom lab))) := by
  classical
  have hD := ac_domSet hH hlab
  have hnd : (acDom lab).Nodup := (List.nodup_finRange q).filter _
  rw [st_aggCase_eq, acCaseL, hD, ac_suppSet_card hH hlab,
    ac_pstab_congr H (l := (acDom lab).toFinset.toList) (l' := acDom lab) (by simp),
    List.toFinset_card_of_nodup hnd]
  have hne : (acDom lab).toFinset.Nonempty ↔ acDom lab ≠ [] := by
    rw [List.toFinset_nonempty_iff, ne_eq]
  by_cases h : acDom lab ≠ []
  · rw [if_pos (hne.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hne.1 h')), if_neg h]

end GI.Impl
