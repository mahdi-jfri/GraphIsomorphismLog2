module

public import Workspace.Impl.TermJProgTl
public import Workspace.Impl.TermJHMath

@[expose] public section

/-!
# The table lists generate the wreath stabilizer (mathematics)

The per-label program and `Aut_J(X)` use the pairs `lg = tmJLgList O` (the stored generators of
`Aut_N(x_a)`, with `1`, at row `a`) and the triples `Tl = tmJTlList O` (one `N`-transporter
`x_a → x_{a'}` for every pair of different rows of the same `N`-type). `tmJTab_aut` says that
their local elements and lifted transpositions generate `Aut_{N ≀ Sym(q)}(X)`; it is
`tmJ_young_eq` with the diagonal triples `(a, a, 1)` added, whose lifted transpositions are `1`.
`tmJTab_lg_mem`, `tmJTab_lg_row` and `tmJTab_tl_mem` give the other facts used by
`tmJH_corr` and `tmJ_autJ_gens`.
-/

namespace GI.Impl

open Equiv Equiv.Perm

variable {m q : ℕ} {C : Type} (N : Subgroup (Perm (Fin m))) (x : Fin q → Fin m → C)
  (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m))))

theorem tmJSw_self (a : Fin q) : tmJSw a a (1 : Perm (Fin m)) = 1 := by
  unfold tmJSw tmJSwD
  rw [swap_self, Pi.mulSingle_one, inv_one]
  have : Function.update (1 : Fin q → Perm (Fin m)) a 1 = 1 := by
    funext i; by_cases h : i = a <;> simp [Function.update, h]
  rw [this]
  exact tmJP_one

/-- The pairs of the list at row `a`. -/
theorem tmJTab_lg_iff {a : Fin q} {r : Perm (Fin m)} {gs : List (Perm (Fin m))}
    (hO : O a a = some (r, gs)) (b : Fin q) (g : Perm (Fin m)) :
    (b, g) ∈ tmJLgList O ↔ (b = a ∧ g ∈ 1 :: gs) ∨ (b ≠ a ∧ ∃ r' gs', O b b = some (r', gs') ∧
      g ∈ 1 :: gs') := by
  simp only [tmJLgList, List.mem_flatten, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨l, ⟨b', rfl⟩, hl⟩
    unfold tmJLgOf at hl
    cases hb : O b' b' with
    | none => rw [hb] at hl; simp at hl
    | some p =>
      obtain ⟨r', gs'⟩ := p
      rw [hb] at hl
      simp only [List.mem_map, Prod.mk.injEq] at hl
      obtain ⟨g', hg', rfl, rfl⟩ := hl
      by_cases hba : b' = a
      · subst hba
        rw [hO] at hb
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨-, rfl⟩ := hb
        exact Or.inl ⟨rfl, hg'⟩
      · exact Or.inr ⟨hba, r', gs', hb, hg'⟩
  · rintro (⟨rfl, hg⟩ | ⟨-, r', gs', hb, hg⟩)
    · refine ⟨tmJLgOf O b, ⟨b, rfl⟩, ?_⟩
      unfold tmJLgOf; rw [hO]
      exact List.mem_map.2 ⟨g, hg, rfl⟩
    · refine ⟨tmJLgOf O b, ⟨b, rfl⟩, ?_⟩
      unfold tmJLgOf; rw [hb]
      exact List.mem_map.2 ⟨g, hg, rfl⟩

/-- The triples of the list. -/
theorem tmJTab_tl_iff (a a' : Fin q) (b : Perm (Fin m)) :
    (a, a', b) ∈ tmJTlList O ↔ a ≠ a' ∧ ∃ gs, O a a' = some (b, gs) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact a.elim0)
  simp only [tmJTlList, List.mem_flatten, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨l, ⟨t, rfl⟩, hl⟩
    unfold tmJTlOf at hl
    split_ifs at hl with he
    · simp at hl
    · cases ho : O (tmJFst t) (tmJSnd t) with
      | none => rw [ho] at hl; simp at hl
      | some p =>
        obtain ⟨b', gs'⟩ := p
        rw [ho] at hl
        simp only [List.mem_singleton, Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl, rfl⟩ := hl
        exact ⟨he, gs', ho⟩
  · rintro ⟨hne, gs, ho⟩
    let t : Fin (q * q) := ⟨a * q + a', by
      have : (a : ℕ) * q + a' < (a + 1) * q := by rw [Nat.add_mul, one_mul]; omega
      exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ a.2)⟩
    have h1 : tmJFst t = a := Fin.ext (by
      simp only [tmJFst, t]
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt a'.2, zero_add])
    have h2 : tmJSnd t = a' := Fin.ext (by
      simp only [tmJSnd, t]
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a'.2])
    refine ⟨tmJTlOf O t, ⟨t, rfl⟩, ?_⟩
    unfold tmJTlOf
    rw [h1, h2, if_neg hne, ho]
    exact List.mem_singleton_self _

variable {N x O}

/-- **The table lists generate `Aut_{N ≀ Sym(q)}(X)`.** -/
theorem tmJTab_aut
    (hloc : ∀ a, ∃ r gs, O a a = some (r, gs) ∧
      Subgroup.closure {s | s ∈ gs} = tmJRowAut N (x a))
    (hsome : ∀ a a' b gs, O a a' = some (b, gs) → b ∈ N ∧ x a ∘ b = x a')
    (hnone : ∀ a a', O a a' = none → ∀ b ∈ N, x a ∘ b ≠ x a') :
    Subgroup.closure (tmJHLocs (tmJLgList O) ∪ tmJHSws (tmJTlList O)) =
      tmJW N ⊓ tmJStab (tmJStr x) := by
  choose r gs hO hgs using hloc
  set ls : Fin q → List (Perm (Fin m)) := fun a => 1 :: gs a with hls
  have hls' : ∀ a, Subgroup.closure {s | s ∈ ls a} = tmJRowAut N (x a) := by
    intro a
    rw [← hgs a]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro s hs
      simp only [hls, List.mem_cons, Set.mem_setOf_eq] at hs
      rcases hs with rfl | hs
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure hs
    · exact Subgroup.closure_mono fun s hs => List.mem_cons_of_mem _ hs
  set trs := tmJTlList O ++ (List.finRange q).map fun a => (a, a, (1 : Perm (Fin m))) with htrs
  have hY := tmJ_young_eq N x ls hls' trs
    (by
      rintro ⟨a, a', b⟩ ht
      rcases List.mem_append.1 ht with ht | ht
      · obtain ⟨-, gs', h⟩ := (tmJTab_tl_iff O a a' b).1 ht
        exact hsome a a' b gs' h
      · obtain ⟨a'', -, he⟩ := List.mem_map.1 ht
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact ⟨N.one_mem, rfl⟩)
    (by
      intro a a' b hb hx
      by_cases haa : a = a'
      · subst haa
        exact ⟨1, List.mem_append_right _ (List.mem_map.2 ⟨a, List.mem_finRange a, rfl⟩)⟩
      · cases h : O a a' with
        | none => exact absurd hx (hnone a a' h b hb)
        | some p =>
          exact ⟨p.1, List.mem_append_left _ ((tmJTab_tl_iff O a a' p.1).2 ⟨haa, p.2, by rw [h]⟩)⟩)
  rw [← hY]
  -- the two generating sets differ by identities
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro σ (⟨⟨a, g⟩, hag, rfl⟩ | ⟨⟨a, a', b⟩, ht, rfl⟩)
    · rcases (tmJTab_lg_iff O (hO a) a g).1 hag with ⟨-, hg⟩ | ⟨-, r', gs', hb, hg⟩
      · exact Subgroup.subset_closure (Or.inl ⟨a, g, hg, rfl⟩)
      · rw [hO a] at hb
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨-, rfl⟩ := hb
        exact Subgroup.subset_closure (Or.inl ⟨a, g, hg, rfl⟩)
    · exact Subgroup.subset_closure (Or.inr ⟨(a, a', b), List.mem_append_left _ ht, rfl⟩)
  · rw [Subgroup.closure_le]
    rintro σ (⟨a, g, hg, rfl⟩ | ⟨⟨a, a', b⟩, ht, rfl⟩)
    · exact Subgroup.subset_closure (Or.inl ⟨(a, g), (tmJTab_lg_iff O (hO a) a g).2
        (Or.inl ⟨rfl, hg⟩), rfl⟩)
    · rcases List.mem_append.1 ht with ht | ht
      · exact Subgroup.subset_closure (Or.inr ⟨(a, a', b), ht, rfl⟩)
      · obtain ⟨a'', -, he⟩ := List.mem_map.1 ht
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        show tmJSw _ _ (1 : Perm (Fin m)) ∈ _
        rw [tmJSw_self]
        exact Subgroup.one_mem _

/-- **The generators at row `a`** generate `Aut_N(x_a)`. -/
theorem tmJTab_lg_row
    (hloc : ∀ a, ∃ r gs, O a a = some (r, gs) ∧
      Subgroup.closure {s | s ∈ gs} = tmJRowAut N (x a)) (a : Fin q) :
    Subgroup.closure {g | (a, g) ∈ tmJLgList O} = tmJRowAut N (x a) := by
  obtain ⟨r, gs, hO, hgs⟩ := hloc a
  rw [← hgs]
  have : {g | (a, g) ∈ tmJLgList O} = {g | g ∈ 1 :: gs} := by
    ext g
    simp only [Set.mem_setOf_eq, tmJTab_lg_iff O hO a g, ne_eq, not_true_eq_false, false_and,
      or_false, true_and]
  rw [this]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro s hs
    simp only [List.mem_cons, Set.mem_setOf_eq] at hs
    rcases hs with rfl | hs
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure hs
  · exact Subgroup.closure_mono fun s hs => List.mem_cons_of_mem _ hs

/-- **Every pair of the list is a local stabilizer.** -/
theorem tmJTab_lg_mem
    (hloc : ∀ a, ∃ r gs, O a a = some (r, gs) ∧
      Subgroup.closure {s | s ∈ gs} = tmJRowAut N (x a))
    (k : Fin (tmJLgList O).length) :
    ((tmJLgList O).get k).2 ∈ tmJRowAut N (x ((tmJLgList O).get k).1) := by
  rw [← tmJTab_lg_row hloc]
  exact Subgroup.subset_closure (List.getElem_mem k.2)

/-- **Every triple of the list is a transporter between different rows.** -/
theorem tmJTab_tl_mem (hsome : ∀ a a' b gs, O a a' = some (b, gs) → b ∈ N ∧ x a ∘ b = x a')
    (t : Fin q × Fin q × Perm (Fin m)) (ht : t ∈ tmJTlList O) :
    t.1 ≠ t.2.1 ∧ t.2.2 ∈ N ∧ x t.1 ∘ t.2.2 = x t.2.1 := by
  obtain ⟨a, a', b⟩ := t
  obtain ⟨hne, gs, h⟩ := (tmJTab_tl_iff O a a' b).1 ht
  exact ⟨hne, hsome a a' b gs h⟩

end GI.Impl
