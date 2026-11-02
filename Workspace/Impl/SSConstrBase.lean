import Workspace.Impl.SSMember

/-!
# Facts for the constructive membership wrapper

The instructions of `ssConstrProg` name small indices (`ss_constr_insMax`), so its encoding is
small, and its length is bounded by a power of the number of input cells
(`ss_constr_len_cells`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {n : ℕ}

theorem ss_chain_insMax (N M : ℕ) :
    ∀ (used : List ℕ) (loc : List SlpInstr), (∀ ins ∈ loc, ssInsMax ins ≤ M) →
      (∀ u ∈ used, u ≤ M) → N + loc.length + 2 * used.length ≤ M →
      ∀ ins ∈ used.foldl (ssChain N) loc, ssInsMax ins ≤ M := by
  intro used
  induction used with
  | nil => intro loc h _ _; simpa using h
  | cons u used ih =>
    intro loc hl hu hM
    simp only [List.foldl_cons]
    refine ih _ (fun ins hins => ?_) (fun v hv => hu v (List.mem_cons_of_mem _ hv)) ?_
    · unfold ssChain at hins
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hins
      rcases hins with h | rfl | rfl
      · exact hl ins h
      · exact hu u (by simp)
      · simp only [ssInsMax, List.length_cons] at hM ⊢; omega
    · simp only [ssChain, List.length_append, List.length_cons, List.length_nil,
        List.length_cons] at hM ⊢
      omega

/-- The instructions of the program for a member name small indices. -/
theorem ss_constr_insMax (prog : List SlpInstr) (used : List ℕ) {M : ℕ}
    (hp : ∀ ins ∈ prog, ssInsMax ins ≤ M) (hu : ∀ u ∈ used, u ≤ M)
    (hM : prog.length + 4 + 2 * used.length ≤ M) :
    ∀ ins ∈ ssConstrProg prog used, ssInsMax ins ≤ M := by
  have hloc := ss_chain_insMax prog.length M used [.gen 0, .inv prog.length,
    .mul (prog.length + 1) prog.length] (fun ins h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> simp only [ssInsMax] <;> omega) hu
    (by simp only [List.length_cons, List.length_nil]; omega)
  intro ins h
  unfold ssConstrProg at h
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with (h | h) | rfl
  · exact hp ins h
  · exact hloc ins h
  · simp only [ssInsMax]
    have := length_ssConstrLoc prog.length used
    omega

end GI.Impl
