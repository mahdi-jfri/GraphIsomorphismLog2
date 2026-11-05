module

public import Workspace.Proved.VStabLinKer
public import Workspace.Impl.VStabLinUnit

@[expose] public section

/-!
# Kernels and coordinates with unit tags

Insert the pairs `(v_i, e_i)` for `i < m`, where `m` is the number of vectors. A pair `(x, t)`
in their span has `t` supported below `m` and `x = ∑ t_i v_i` (`vsUnitPairs_span`). So:

* `vsUnitPairs_ker`: the relations span the kernel of `a ↦ ∑_{i < m} a_i v_i` (on `a`
  supported below `m`).
* `vsUnitPairs_solve`: if sifting `(u, 0)` gives main part `0`, then `u = ∑ c_i v_i`, where
  `c` is the negated sifted tag.
-/

namespace GI.Proved

open GI.Impl

variable {p : ℕ}

theorem vsF_vsUnit {m i : ℕ} (hi : i < m) : vsF p (vsUnit m i) = Pi.single i 1 := by
  funext j
  rw [vsF_apply, Pi.single_apply]
  by_cases hj : j < m
  · rw [List.getD_eq_getElem _ _ (by rw [vsUnit_length]; exact hj)]
    simp only [vsUnit, List.getElem_map, List.getElem_range]
    split_ifs <;> simp
  · rw [List.getD_eq_default _ _ (by rw [vsUnit_length]; omega)]
    have : j ≠ i := by omega
    simp [this]

/-- The combination `∑_{i < m} t_i v_i`. -/
noncomputable def vsComb (p : ℕ) (vs : List (List ℕ)) (t : ℕ → ZMod p) : ℕ → ZMod p :=
  ∑ i ∈ Finset.range vs.length, t i • vsF p (vs.getD i [])

/-- **The span of the unit-tag pairs.** -/
theorem vsUnitPairs_span (vs : List (List ℕ)) (x t : ℕ → ZMod p) :
    (x, t) ∈ vsPairSpan p (vsUnitPairs vs.length vs) ↔
      (∀ j, vs.length ≤ j → t j = 0) ∧ x = vsComb p vs t := by
  constructor
  · intro h
    suffices H : ∀ v ∈ vsPairSpan p (vsUnitPairs vs.length vs),
        (∀ j, vs.length ≤ j → v.2 j = 0) ∧ v.1 = vsComb p vs v.2 from H _ h
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      simp only [Set.mem_setOf_eq, List.mem_map, vsUnitPairs, List.mem_range] at hv
      obtain ⟨_, ⟨i, hi, rfl⟩, rfl⟩ := hv
      simp only [vsP, vsF_vsUnit hi]
      refine ⟨fun j hj => by rw [Pi.single_apply, if_neg (by omega)], ?_⟩
      unfold vsComb
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · intro h'; exact absurd (Finset.mem_range.mpr hi) h'
    | zero => exact ⟨fun _ _ => rfl, by simp [vsComb]⟩
    | add u w _ _ hu hw =>
      refine ⟨fun j hj => by simp [hu.1 j hj, hw.1 j hj], ?_⟩
      simp only [Prod.fst_add, Prod.snd_add, hu.2, hw.2, vsComb, Pi.add_apply, add_smul,
        Finset.sum_add_distrib]
    | smul a u _ hu =>
      refine ⟨fun j hj => by simp [hu.1 j hj], ?_⟩
      simp only [Prod.smul_fst, Prod.smul_snd, hu.2, vsComb, Finset.smul_sum, Pi.smul_apply,
        smul_eq_mul, mul_smul]
  · rintro ⟨ht, rfl⟩
    have e : (vsComb p vs t, t) = ∑ i ∈ Finset.range vs.length, t i • vsP p (vs.getD i [],
        vsUnit vs.length i) := by
      ext j
      · simp only [vsComb, vsP, Prod.fst_sum, Prod.smul_fst]
      · simp only [vsP, Prod.snd_sum, Prod.smul_snd]
        rw [Finset.sum_apply]
        by_cases hj : j < vs.length
        · rw [Finset.sum_eq_single j]
          · simp [vsF_vsUnit hj]
          · intro b hb hbj
            simp [vsF_vsUnit (Finset.mem_range.mp hb), Ne.symm hbj]
          · intro h'; exact absurd (Finset.mem_range.mpr hj) h'
        · rw [ht j (by omega)]
          refine (Finset.sum_eq_zero fun b hb => ?_).symm
          have hbj : j ≠ b := by have := Finset.mem_range.mp hb; omega
          simp [vsF_vsUnit (Finset.mem_range.mp hb), hbj]
    rw [e]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    simp only [Set.mem_setOf_eq, List.mem_map, vsUnitPairs, List.mem_range]
    exact ⟨_, ⟨i, Finset.mem_range.mp hi, rfl⟩, rfl⟩

theorem vsUnitPairs_fit {vs : List (List ℕ)} {lx : ℕ}
    (hvs : ∀ v ∈ vs, (∀ y ∈ v, y < p) ∧ v.length = lx) :
    ∀ xt ∈ vsUnitPairs vs.length vs, VsBelow p xt ∧ xt.1.length = lx ∧ xt.2.length = vs.length := by
  intro xt hxt
  simp only [vsUnitPairs, List.mem_map, List.mem_range] at hxt
  obtain ⟨i, hi, rfl⟩ := hxt
  have hm := List.getD_eq_getElem vs [] hi ▸ hvs _ (List.getElem_mem hi)
  exact ⟨hm.1, hm.2, vsUnit_length _ _⟩

/-- **The relations span the kernel.** For `a` supported below `m = |vs|`, `∑ a_i v_i = 0`
exactly when `a` is in the span of the relations of the unit-tag insertion. -/
theorem vsUnitPairs_ker (hp : p.Prime) {vs : List (List ℕ)} {lx : ℕ}
    (hvs : ∀ v ∈ vs, (∀ y ∈ v, y < p) ∧ v.length = lx) {a : ℕ → ZMod p}
    (ha : ∀ j, vs.length ≤ j → a j = 0) :
    vsComb p vs a = 0 ↔ a ∈ Submodule.span (ZMod p)
      {w | w ∈ (vsInsertAll p (vsUnitPairs vs.length vs)).2.map (vsF p)} := by
  rw [← vsInsertAll_ker hp (vsUnitPairs_fit hvs), vsUnitPairs_span]
  exact ⟨fun h => ⟨ha, h.symm⟩, fun h => h.2.symm⟩

/-- **Coordinates.** If sifting `(u, z)` (with `z` reading as `0`) through the rows of the
unit-tag insertion gives main part `0`, then `u = ∑ c_i v_i` for the negated sifted tag `c`. -/
theorem vsUnitPairs_solve (hp : p.Prime) {vs : List (List ℕ)} {lx : ℕ}
    (hvs : ∀ v ∈ vs, (∀ y ∈ v, y < p) ∧ v.length = lx) {u z : List ℕ}
    (hu : ∀ y ∈ u, y < p) (hul : u.length = lx) (hzl : z.length = vs.length) (hz : vsF p z = 0)
    (h0 : vsF p (vsSift p (vsInsertAll p (vsUnitPairs vs.length vs)).1 (u, z)).1 = 0) :
    vsF p u = vsComb p vs (-vsF p (vsSift p (vsInsertAll p (vsUnitPairs vs.length vs)).1 (u, z)).2) :=
  ((vsUnitPairs_span vs _ _).mp ((vsSolve hp (vsUnitPairs_fit hvs) hu hul hzl hz).2 h0)).2

end GI.Proved
