/-
Bounding the number of memory cells changed by a run, and hence the number of generators in a
correct output.

A run of cost `c` executes at most `c` `store` instructions, so it changes at most `c` memory
cells (`GI.Turing.Runs.changed_cells_le`). When `n ≥ 2`, every permutation of `Fin n` has at least
one nonzero image value, so each generator in `CorrectOutput` uses a distinct nonzero cell. Since
an `InputLayout` has at most `2 * n * n + 1` nonzero cells, a program of cost `T` can output at
most `T + 2 * n * n + 1` generators (`GI.Turing.run_gens_length_le`).
-/
module

public import Workspace.Machine.Link
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace GI.Turing

open GI.Machine GI.Statement

/-- A run of cost `c` changes at most `c` memory cells. -/
theorem exec_changed_cells_le {p : Program} {fuel : ℕ} {s : Stmt} {st st' : State} {o : Outcome}
    {c : ℕ} (h : exec p fuel s st = some (o, st', c)) :
    ∃ S : Finset ℕ, S.card ≤ c ∧ ∀ a, a ∉ S → st'.mem a = st.mem a := by
  induction fuel generalizing s st st' o c with
  | zero => simp [exec] at h
  | succ f ih =>
    cases s with
    | nop =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl, rfl⟩ := h
      exact ⟨∅, by simp, fun _ _ => rfl⟩
    | assign r e =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl, rfl⟩ := h
      exact ⟨∅, by simp, fun _ _ => rfl⟩
    | ret e =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl, rfl⟩ := h
      exact ⟨∅, by simp, fun _ _ => rfl⟩
    | store a e =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl, rfl⟩ := h
      refine ⟨{(evalExpr st a).1}, ?_, fun x hx => ?_⟩
      · simp only [Finset.card_singleton]; omega
      · simp only [Finset.mem_singleton] at hx
        exact Function.update_of_ne hx _ _
    | seq s t =>
      simp only [exec] at h
      cases h1 : exec p f s st with
      | none => simp [h1] at h
      | some r1 =>
        rw [h1] at h
        obtain ⟨o1, st1, c1⟩ := r1
        cases o1 with
        | returned v =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl, rfl⟩ := h
          obtain ⟨S1, hcard1, hmem1⟩ := ih h1
          exact ⟨S1, by omega, hmem1⟩
        | normal =>
          simp only at h
          cases h2 : exec p f t st1 with
          | none => simp [h2] at h
          | some r2 =>
            rw [h2] at h
            obtain ⟨o2, st2, c2⟩ := r2
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl, rfl⟩ := h
            obtain ⟨S1, hcard1, hmem1⟩ := ih h1
            obtain ⟨S2, hcard2, hmem2⟩ := ih h2
            refine ⟨S1 ∪ S2, ?_, fun x hx => ?_⟩
            · have := Finset.card_union_le S1 S2; omega
            · rw [Finset.mem_union, not_or] at hx
              rw [hmem2 x hx.2, hmem1 x hx.1]
    | cond e s t =>
      simp only [exec] at h
      cases h1 : exec p f (if (evalExpr st e).1 = 0 then t else s) st with
      | none => simp [h1] at h
      | some r1 =>
        rw [h1] at h
        obtain ⟨o1, st1, c1⟩ := r1
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, rfl⟩ := h
        obtain ⟨S1, hcard1, hmem1⟩ := ih h1
        exact ⟨S1, by omega, hmem1⟩
    | loop e body =>
      simp only [exec] at h
      split_ifs at h with hv
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, rfl⟩ := h
        exact ⟨∅, by simp, fun _ _ => rfl⟩
      · cases h1 : exec p f body st with
        | none => simp [h1] at h
        | some r1 =>
          rw [h1] at h
          obtain ⟨o1, st1, c1⟩ := r1
          cases o1 with
          | returned w =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl, rfl⟩ := h
            obtain ⟨S1, hcard1, hmem1⟩ := ih h1
            exact ⟨S1, by omega, hmem1⟩
          | normal =>
            simp only at h
            cases h2 : exec p f (.loop e body) st1 with
            | none => simp [h2] at h
            | some r2 =>
              rw [h2] at h
              obtain ⟨o2, st2, c2⟩ := r2
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨_, rfl, rfl⟩ := h
              obtain ⟨S1, hcard1, hmem1⟩ := ih h1
              obtain ⟨S2, hcard2, hmem2⟩ := ih h2
              refine ⟨S1 ∪ S2, ?_, fun x hx => ?_⟩
              · have := Finset.card_union_le S1 S2; omega
              · rw [Finset.mem_union, not_or] at hx
                rw [hmem2 x hx.2, hmem1 x hx.1]
    | call r g args =>
      simp only [exec] at h
      cases hb : p.procs[g]? with
      | none => simp [hb] at h
      | some body =>
        rw [hb] at h
        simp only at h
        cases h1 : exec p f body
            { mem := st.mem, regs := fun i => (evalArgs st args).1.getD i 0 } with
        | none => rw [h1] at h; simp at h
        | some r1 =>
          rw [h1] at h
          obtain ⟨o1, st1, c1⟩ := r1
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl, rfl⟩ := h
          obtain ⟨S1, hcard1, hmem1⟩ := ih h1
          exact ⟨S1, by omega, hmem1⟩

/-- Fuel-free version of `exec_changed_cells_le`. -/
theorem Runs.changed_cells_le {p : Program} {s : Stmt} {st st' : State} {o : Outcome} {c : ℕ}
    (h : Runs p s st o st' c) :
    ∃ S : Finset ℕ, S.card ≤ c ∧ ∀ a, a ∉ S → st'.mem a = st.mem a := by
  obtain ⟨fuel, hf⟩ := h
  exact exec_changed_cells_le hf

/-- Extracting the underlying `Runs` from `GI.Machine.run`, together with `len r ≤ T` and `1 ≤ T`. -/
theorem run_spec {p : Program} {mem mem' : ℕ → ℕ} {fuel r T : ℕ}
    (h : run p mem fuel = some (mem', r, T)) :
    ∃ body o st'' c', p.procs[0]? = some body ∧
      Runs p body { mem := mem, regs := fun _ => 0 } o st'' c' ∧
      st''.mem = mem' ∧ o.retVal = r ∧ T = c' + 1 ∧ len r ≤ T ∧ 1 ≤ T := by
  unfold run at h
  cases he : exec p fuel (.call 0 0 []) { mem := mem, regs := fun _ => 0 } with
  | none => rw [he] at h; simp at h
  | some res =>
    rw [he] at h
    obtain ⟨o0, st0, c0⟩ := res
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨body, o', st'', c', hbody, hr, rfl, rfl, hc⟩ := Runs.call_inv ⟨fuel, he⟩
    simp only [evalArgs_nil, Nat.zero_add, Function.update_self] at hc ⊢
    subst hc
    have hlen : len o'.retVal ≤ c' + 1 := by
      cases o' with
      | normal => simp [len_zero]
      | returned w => have := hr.len_returned_le; simp only [Outcome.retVal_returned]; omega
    exact ⟨body, o', st'', c', hbody, hr, rfl, rfl, rfl, hlen, by omega⟩

/-- For `n ≥ 2`, a program of cost `T` started on an `InputLayout` outputs at most
`T + 2 * n * n + 1` generators. -/
theorem run_gens_length_le {n : ℕ} {G H : SimpleGraph (Fin n)} {p : Program}
    {mem mem' : ℕ → ℕ} {fuel r T : ℕ} (hn : 2 ≤ n) (hin : InputLayout G H mem)
    (hrun : run p mem fuel = some (mem', r, T)) (gens : List (Equiv.Perm (Fin n)))
    (hgens : ∀ (t : Fin gens.length) (i : Fin n),
      mem' (r + 2 + n + n * t + i) = gens.get t i) :
    gens.length ≤ T + 2 * n * n + 1 := by
  obtain ⟨body, o, st'', c', _, hr, rfl, _, hT, _, _⟩ := run_spec hrun
  obtain ⟨S, hScard, hSmem⟩ := Runs.changed_cells_le hr
  set Z : Finset ℕ := S ∪ Finset.range (2 * n * n + 1)
  have hZcard : Z.card ≤ T + 2 * n * n + 1 := by
    have := Finset.card_union_le S (Finset.range (2 * n * n + 1))
    rw [Finset.card_range] at this
    dsimp only [Z]
    omega
  -- Every nonzero cell of `st''.mem` lies in `Z`.
  have hmemZ : ∀ a, st''.mem a ≠ 0 → a ∈ Z := by
    intro a ha
    rw [Finset.mem_union]
    by_cases haS : a ∈ S
    · exact Or.inl haS
    · right
      rw [Finset.mem_range]
      have hma : mem a ≠ 0 := by
        have hEq := hSmem a haS
        dsimp only at hEq
        rwa [← hEq]
      by_contra hle
      exact hma (hin.rest a (by omega))
  -- For each generator `t`, pick a vertex `idx t` whose image is nonzero.
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let idx : Fin gens.length → Fin n := fun t =>
    if (gens.get t i0 : ℕ) ≠ 0 then i0 else i1
  have hidx_ne : ∀ t : Fin gens.length, (gens.get t (idx t) : ℕ) ≠ 0 := by
    intro t
    dsimp only [idx]
    split_ifs with h0
    · exact h0
    · push Not at h0
      intro h1
      have heq : gens.get t i0 = gens.get t i1 := Fin.ext (by omega)
      have hi01 : i0 = i1 := (gens.get t).injective heq
      have : (0 : ℕ) = 1 := congrArg Fin.val hi01
      omega
  -- Map each generator `t` to its nonzero cell in `Z`.
  let φ : Fin gens.length → ℕ := fun t => r + 2 + n + n * t + idx t
  have hφ_mem : ∀ t : Fin gens.length, φ t ∈ Z := fun t => by
    apply hmemZ
    rw [hgens t (idx t)]
    exact hidx_ne t
  have hφ_inj : Function.Injective φ := by
    intro t₁ t₂ heq
    have h1 : n * (t₁ : ℕ) + (idx t₁ : ℕ) = n * (t₂ : ℕ) + (idx t₂ : ℕ) := by
      dsimp only [φ] at heq; omega
    have hdiv := congrArg (· / n) h1
    rw [cell_div (idx t₁).isLt, cell_div (idx t₂).isLt] at hdiv
    exact Fin.ext hdiv
  have hcard : gens.length ≤ Z.card := by
    have h1 : (Finset.univ.image φ).card ≤ Z.card :=
      Finset.card_le_card (Finset.image_subset_iff.mpr fun t _ => hφ_mem t)
    rw [Finset.card_image_of_injective _ hφ_inj, Finset.card_univ, Fintype.card_fin] at h1
    exact h1
  exact hcard.trans hZcard

end GI.Turing
