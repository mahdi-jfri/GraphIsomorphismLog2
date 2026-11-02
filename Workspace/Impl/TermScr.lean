import Workspace.Impl.TermStep

/-!
# The terminal script after `j` exact answers (T1)

The terminal asks `(2q)² = 4q²` `N`-tests and then `q²` coset calls (`tm_script_unrolled`).
Since every recursive run returns the exact answer (`Run.exact`), the rest of the script after
`j` answers is fixed: `tmScr I j`. The step function of the terminal (`TermLoop.lean`) keeps `j`
and the answers so far, and asks call number `j`.

* `tmScr_zero`: the script of the terminal with the program's order is `tmScr I 0`;
* `tmScr_test`: for `j < 4q²`, `tmScr I j` asks `N`-test number `j`, and continues with
  `tmScr I (j + 1)` on the exact answer;
* `tmScr_coset`: the same for the coset calls, `4q² ≤ j < 5q²`;
* `tmScr_done`: `tmScr I (5q²)` is finished with the answer of the state (Theorem A.23 through
  `tm_assemble_exact`).
-/

namespace GI.Impl

open GI.Algorithm Equiv Equiv.Perm

variable {Ω C : Type} {P : Params} {S : State Ω C} {L : GiantLabels S} (I : RowTerminal P S L)

/-- The rest of the terminal script after `j` exact answers, with the program's order. -/
noncomputable def tmScr (j : ℕ) : Script (Set (Perm Ω)) :=
  if j < 4 * L.q ^ 2 then
    tmTabFrom I.typeCall ((tmTests L.q).drop j)
      (((tmTests L.q).take j).map fun ac => (ac, (I.typeCall ac).answer))
      fun TN => tmTabFrom I.cosetCall (tmCosets L.q) [] fun TH => .done (I.assemble TN TH)
  else
    tmTabFrom I.cosetCall ((tmCosets L.q).drop (j - 4 * L.q ^ 2))
      (((tmCosets L.q).take (j - 4 * L.q ^ 2)).map fun ij => (ij, (I.cosetCall ij).answer))
      fun TH => .done (I.assemble (fun ac => (I.typeCall ac).answer) TH)

/-- **The start.** -/
theorem tmScr_zero (hq : 0 < L.q) : (tmWithOrder I).script = tmScr I 0 := by
  rw [tm_script_unrolled]
  have h : 0 < 4 * L.q ^ 2 := by positivity
  simp only [tmScr, if_pos h, List.drop_zero, List.take_zero, List.map_nil]

theorem tm_take_succ {α : Type} (l : List α) (j : ℕ) (h : j < l.length) :
    l.take (j + 1) = l.take j ++ [l[j]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  rfl

theorem tm_drop_eq {α : Type} (l : List α) (j : ℕ) (h : j < l.length) :
    l.drop j = l[j] :: l.drop (j + 1) := (List.drop_eq_getElem_cons h)

/-- **An `N`-test.** -/
theorem tmScr_test (j : ℕ) (hj : j < 4 * L.q ^ 2) :
    ∃ k, tmScr I j = .ask .solve (I.typeCall ((tmTests L.q)[j]'(by rw [length_tmTests]; exact hj)))
      k ∧ k (I.typeCall ((tmTests L.q)[j]'(by rw [length_tmTests]; exact hj))).answer =
        tmScr I (j + 1) := by
  have hl : j < (tmTests L.q).length := by rw [length_tmTests]; exact hj
  unfold tmScr
  rw [if_pos hj, tm_drop_eq _ j hl, tmTabFrom_cons]
  refine ⟨_, rfl, ?_⟩
  by_cases hj1 : j + 1 < 4 * L.q ^ 2
  · rw [if_pos hj1, tm_take_succ _ j hl, List.map_append]
    rfl
  · rw [if_neg hj1]
    have he : j + 1 = (tmTests L.q).length := by rw [length_tmTests]; omega
    have hd : (tmTests L.q).drop (j + 1) = [] := by rw [he]; exact List.drop_length
    have ht : (tmTests L.q).take j ++ [(tmTests L.q)[j]] = tmTests L.q := by
      rw [← tm_take_succ _ j hl, he, List.take_length]
    have h0 : j + 1 - 4 * L.q ^ 2 = 0 := by omega
    rw [hd, h0, tmTabFrom_nil, List.drop_zero, List.take_zero, List.map_nil]
    have hm : ((tmTests L.q).take j).map (fun ac => (ac, (I.typeCall ac).answer)) ++
        [((tmTests L.q)[j], (I.typeCall (tmTests L.q)[j]).answer)] =
        (tmTests L.q).map (fun ac => (ac, (I.typeCall ac).answer)) := by
      calc _ = ((tmTests L.q).take j ++ [(tmTests L.q)[j]]).map
            (fun ac => (ac, (I.typeCall ac).answer)) := by rw [List.map_append]; rfl
        _ = _ := by rw [ht]
    rw [hm, tmUpd_exact _ _ _ mem_tmTests]

/-- **A coset call.** -/
theorem tmScr_coset (j : ℕ) (hj1 : 4 * L.q ^ 2 ≤ j) (hj : j < 5 * L.q ^ 2) :
    ∃ k, tmScr I j = .ask .solve (I.cosetCall ((tmCosets L.q)[j - 4 * L.q ^ 2]'(by
        rw [length_tmCosets]; omega))) k ∧
      k (I.cosetCall ((tmCosets L.q)[j - 4 * L.q ^ 2]'(by rw [length_tmCosets]; omega))).answer =
        tmScr I (j + 1) := by
  have hl : j - 4 * L.q ^ 2 < (tmCosets L.q).length := by rw [length_tmCosets]; omega
  unfold tmScr
  rw [if_neg (by omega), tm_drop_eq _ _ hl, tmTabFrom_cons]
  refine ⟨_, rfl, ?_⟩
  rw [if_neg (by omega), show j + 1 - 4 * L.q ^ 2 = j - 4 * L.q ^ 2 + 1 by omega,
    tm_take_succ _ _ hl, List.map_append]
  rfl

/-- **The end**: the answer of the state. -/
theorem tmScr_done : tmScr I (5 * L.q ^ 2) = .done S.answer := by
  unfold tmScr
  rw [if_neg (by omega), show 5 * L.q ^ 2 - 4 * L.q ^ 2 = (tmCosets L.q).length by
    rw [length_tmCosets]; omega, List.drop_length, List.take_length, tmTabFrom_nil,
    tmUpd_exact _ _ _ mem_tmCosets, tm_assemble_exact]

end GI.Impl
