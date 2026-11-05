module

public import Workspace.Impl.AggRectCertP

@[expose] public section

/-!
# The certificate search as a program: the lists it computes

The search program reads the input `[col table, j, x₀]` and computes three lists. This file
shows that they are the lists of `AggRectCertMath.lean`:

* `rc_colVal_eq`: the col table is the value `rcTV (rcTab X.col)`;
* `rc_fib_eq`: the fiber filtered from the diagonal is `rcFib X` (both are sorted, with the same
  members);
* `rc_fib_find`: the position of `x₀` in it is `X.idx hx`;
* `rc_dtab_eq`: the table of the fiber rows is `rcTab (rcDm X)`.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val)

variable {q : ℕ} (X : PairCfg q)

theorem rc_colVal_eq : rcColVal X = rcTV (rcTab X.col) := by
  simp [rcColVal, rcTV, rcTab, encFun, natList, List.map_map, Function.comp_def]

theorem rc_emb_lt {i i' : Fin X.fiber.card} (h : i < i') :
    (X.emb rfl i : ℕ) < (X.emb rfl i' : ℕ) := by
  have := (X.fiber.orderIsoOfFin rfl).strictMono h
  exact this

theorem rc_fib_sorted : (rcFib X).SortedLT := by
  refine List.sortedLT_iff_pairwise.2 ?_
  rw [rcFib, List.pairwise_map]
  exact (List.sortedLT_iff_pairwise.1 (List.sortedLT_finRange _)).imp fun h => rc_emb_lt X h

theorem rc_mem_fib {y : ℕ} : y ∈ rcFib X ↔ ∃ hy : y < q, (⟨y, hy⟩ : Fin q) ∈ X.fiber := by
  constructor
  · intro h
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
    exact ⟨(X.emb rfl i).isLt, X.emb_mem rfl i⟩
  · rintro ⟨hy, hm⟩
    refine List.mem_map.2 ⟨X.idx hm, List.mem_finRange _, ?_⟩
    rw [X.emb_idx hm]

/-- **The fiber from the diagonal.** -/
theorem rc_fib_eq :
    (List.range q).filter (fun y => decide (rcAt (rcTab X.col) y y = X.j)) = rcFib X := by
  have hs : ((List.range q).filter fun y => decide (rcAt (rcTab X.col) y y = X.j)).SortedLT :=
    List.sortedLT_iff_pairwise.2 (List.pairwise_lt_range.filter _)
  refine hs.eq_of_mem_iff (rc_fib_sorted X) fun y => ?_
  rw [rc_mem_fib, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hy, he⟩
    refine ⟨hy, PairCfg.mem_fiber.2 ?_⟩
    have := rcAt_tab X.col ⟨y, hy⟩ ⟨y, hy⟩
    simp only at this
    rw [← this]; simpa using he
  · rintro ⟨hy, hm⟩
    refine ⟨hy, ?_⟩
    have := rcAt_tab X.col ⟨y, hy⟩ ⟨y, hy⟩
    simp only at this
    rw [this]; simpa using PairCfg.mem_fiber.1 hm

theorem rc_fib_length : (rcFib X).length = X.fiber.card := by simp [rcFib]

/-- **The position of `x₀` in the fiber.** -/
theorem rc_fib_find {x₀ : Fin q} (hx : x₀ ∈ X.fiber) :
    (rcFib X).findIdx (fun y => decide (y = (x₀ : ℕ))) = X.idx hx := by
  have hl : (X.idx hx : ℕ) < (rcFib X).length := by rw [rc_fib_length]; exact (X.idx hx).isLt
  have hget : ∀ (k : ℕ) (hk : k < (rcFib X).length),
      (rcFib X)[k] = (X.emb rfl ⟨k, by rw [rc_fib_length] at hk; exact hk⟩ : ℕ) := by
    intro k hk; simp [rcFib]
  rw [List.findIdx_eq hl]
  refine ⟨?_, fun k hk => ?_⟩
  · rw [hget]; simp [X.emb_idx hx]
  · rw [hget]
    simp only [decide_eq_false_iff_not]
    intro he
    have hk' : k < X.fiber.card := lt_trans hk (X.idx hx).isLt
    have h1 : X.emb rfl ⟨k, hk'⟩ = X.emb rfl (X.idx hx) := by rw [X.emb_idx hx]; exact Fin.ext he
    have := congrArg Fin.val ((X.emb rfl).injective h1)
    simp at this
    omega

/-- **The table of the fiber rows.** -/
theorem rc_dtab_eq :
    (rcFib X).map (fun a => (rcFib X).map (rcAt (rcTab X.col) a)) = rcTab (rcDm X) := by
  simp only [rcFib, rcTab, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, rcDm]
  exact rcAt_tab X.col (X.emb rfl i) (X.emb rfl k)

end GI.Impl
