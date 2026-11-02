import Workspace.Impl.SmallInv
import Workspace.Algorithm.DispatchKeep

/-!
# The children of a dispatcher step keep `SmallInv`

A child of `Run.dispatch` has the parent's `N`, the parent's row record (`hbk`) and the
hierarchy `I.hier'` of the step: the exposed hierarchy (enumeration) or the exposed hierarchy
with `top` split into the coordinate intervals (product refinement). Every new interval is
nontrivial with numbers at most those of an old interval (`PrimitiveQuotient.from_old`; a
coordinate interval has ratio `binom(m,k) ≥ 2`, at most `binom(m,k)^r = d`, the ratio of `top`),
and `ρ` does not increase (`DispatchStep.facts`). So the child keeps `SmallInv`
(`DispatchStep.smallInv_child`).
-/

namespace GI.Impl

open GI.Algorithm

variable {Ω C : Type} {S : State Ω C}

/-- The exposed hierarchy keeps the interval bounds of `SmallInv`. -/
theorem _root_.GI.Algorithm.PrimitiveQuotient.intervalsOK (Q : PrimitiveQuotient S) {N : ℕ}
    (h : IntervalsOK N S.hier) : IntervalsOK N (Q.pre ++ Q.top :: Q.post) := by
  intro I hI
  rcases Q.from_old I hI with hI' | ⟨J, hJ, h2, hr, hc, ho⟩
  · exact h I hI'
  · obtain ⟨-, hJr, hJc, hJo⟩ := h J hJ
    exact ⟨h2, hr.trans hJr, hc.trans hJc, ho ▸ hJo⟩

/-- **The hierarchy of a dispatcher step keeps the interval bounds.** -/
theorem _root_.GI.Algorithm.DispatchStep.intervalsOK {P : Params} (I : DispatchStep P S) {N : ℕ}
    (h : IntervalsOK N S.hier) : IntervalsOK N I.hier' := by
  rcases I.K_hier'_eq with ⟨Q, -, -, -, -, -, -, -, hh⟩ |
    ⟨Q, -, -, -, -, -, m, k, r, e, hS, hb, hr, -, hh⟩
  · rw [hh]; exact Q.intervalsOK h
  · rw [hh]
    have hQ := Q.intervalsOK h
    have htop := hQ Q.top (by simp)
    intro J hJ
    simp only [List.mem_append] at hJ
    rcases hJ with (hJ | hJ) | hJ
    · exact hQ J (by simp [hJ])
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hJ
      have hd := Q.card_kset_pow e
      have hle : m.choose k ≤ Q.top.ratio := by
        rw [Q.ratio_eq, hd]
        calc m.choose k = m.choose k ^ 1 := (pow_one _).symm
          _ ≤ m.choose k ^ r := Nat.pow_le_pow_right (by omega) (by omega)
      exact ⟨hb, hle.trans htop.2.1, (min_le_left _ _).trans htop.2.2.1, htop.2.2.2⟩
    · exact hQ J (by simp [hJ])

/-- `ρ` does not increase at a dispatcher step. -/
theorem _root_.GI.Algorithm.DispatchStep.rhoNat_le {P : Params} (I : DispatchStep P S) :
    rhoNat I.hier' ≤ rhoNat S.hier := by
  have hf := I.facts
  have h : (rhoNat I.hier' : ℝ) ≤ rhoNat S.hier := by
    rw [rhoNat_cast, rhoNat_cast]
    cases hk : I.kind with
    | enumeration d => rw [hk] at hf; exact hf.2.2.2.1
    | product r =>
      rw [hk] at hf
      have : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by have := hf.1; omega)
      linarith [hf.2.2.2]
  exact_mod_cast h

/-- **A child of a dispatcher step keeps `SmallInv`**: it has the parent's `N` and row
record and the step's hierarchy. -/
theorem _root_.GI.Algorithm.DispatchStep.smallInv_child {P : Params} (I : DispatchStep P S)
    (h : SmallInv S)
    {T : State Ω C} (hN : T.N = S.N) (hh : T.hier = I.hier') (hbk : T.book = S.book) :
    SmallInv T := by
  have hrows : T.rows = S.rows := congrArg Prod.fst hbk
  refine h.of_rho_le hN ?_ (by rw [hh]; exact I.rhoNat_le) ?_
  · rw [hh, hN]; exact I.intervalsOK h.1
  · rw [hrows, hN]; exact h.2.2

end GI.Impl
